import Lean

/-!
# Audit of the compiled library

Run by `scripts/check.sh` after the build, as

    lake env lean --run scripts/Audit.lean --root VoltageToBit --allow scripts/allowlist.txt \
      --lists <directory>

from the top directory of the project. Exit status: 0 nothing refused, 1
something refused, 2 the command line is wrong or the audit itself failed.

It loads the environment that `import VoltageToBit` gives, from the compiled
files, and looks at **every** declaration stored in the compiled file of a
module whose name is `VoltageToBit` or starts with `VoltageToBit.` (not a
hand-picked list). It reads; it does not re-check any proof. A declaration
that was added with the kernel check switched off looks the same from here as
any other. Re-checking is the job of the replay steps of `scripts/check.sh`.

What it refuses, each with the name of the declaration:

* axioms     A declaration that depends on an axiom other than `propext`,
             `Classical.choice`, `Quot.sound`. The axioms are found here by
             walking the type and the value of the declaration and of every
             declaration it refers to, directly or not (an unfinished proof
             shows up as `sorryAx`, `native_decide` as `Lean.ofReduceBool` or
             `Lean.trustCompiler`). A name that is referred to and that the
             environment does not hold is refused too. Lean also stores an
             axiom list for each declaration when it compiles a file, and
             that list is what `#print axioms` shows for an imported
             declaration; the two must agree.
* origin     A module of the imported environment whose compiled file was not
             loaded from where it belongs: a module of the library from
             `.lake/build/lib/lean` of this project, any other module from
             `.lake/packages` or from the toolchain.
* kinds      A declaration of the library that is an axiom, an `opaque`
             constant, a quotient primitive, or `unsafe`; or `partial`, unless
             it is the auxiliary `f._unsafe_rec` that Lean stores for a
             definition by recursion `f`.
* extensions An entry in one of Lean's environment extensions that is not on
             the allow-list (`extension` lines). Instances, simp lemmas,
             notation, macros, parsers, elaborators, attributes and aliases
             are all stored as such entries, scoped ones included, so this is
             asked of the compiled files and not of the source text.
* instances  An instance, scoped or not, other than the `SizeOf` instance that
             Lean generates for every structure.
* simp       A simp lemma or simp unfolding, in any simp set, scoped or not,
             other than the `injEq` and `sizeOf_spec` lemmas that Lean
             generates for every structure.
* binders    A declaration written in a source file whose type has an
             instance-implicit binder `[...]`, or an argument with a default
             value or a default tactic (`optParam`, `autoParam`). A
             `variable [...]` or Mathlib's `variable?` adds an instance binder
             to a theorem whose text does not show it.
* universes  A declaration written in a source file that has a universe
             parameter. An auto-bound name of unknown type produces one.
* reducible  A definition written in a source file that is marked reducible
             or irreducible (structure projections apart).
             "Written in a source file" means: Lean stored a source position
             for it, which it does for every declaration command, structure
             field and constructor, and for nothing a tactic generates. The
             auxiliary lemmas of `simp` and the matchers are general by
             construction and are left out of these three rules; their number
             is printed.
* meta       A declaration whose type mentions a constant of the namespace
             `Lean` (the types of parsers, macros and elaborators all do).
* shadowing  A declaration `A.B.x` that is not a theorem, such that `B.x` or
             `x` is a declaration of Mathlib or Lean in the imported
             environment, and not a theorem either: inside `namespace A` the
             text `B.x` would then mean the library's declaration. (Theorems
             are left out: a statement cannot mention one.)

It also prints every theorem of the library that has a name of its own, with
the axioms it depends on, and writes the lists that the replay steps use.

It says nothing about whether a statement means what the prose claims.
-/

open Lean

namespace Audit

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure Args where
  root  : String := ""
  allow : String := ""
  lists : String := ""

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--root" :: v :: rest, a => parseArgs rest { a with root := v }
  | "--allow" :: v :: rest, a => parseArgs rest { a with allow := v }
  | "--lists" :: v :: rest, a => parseArgs rest { a with lists := v }
  | v :: _, _ => .error s!"unexpected argument {v}"

/-- The `extension` lines of the allow-list. -/
def loadExtensions (path : System.FilePath) : IO (Std.HashSet String) := do
  let mut set : Std.HashSet String := {}
  for line in (← IO.FS.readFile path).splitOn "\n" do
    match line.trimAscii.toString.splitOn " " |>.filter (· ≠ "") with
    | ["extension", name] => set := set.insert name
    | _ => pure ()
  return set

/-- The components of a name as JSON: strings and numbers. -/
def nameComponents : Name → List Json
  | .anonymous => []
  | .str p s => nameComponents p ++ [toJson s]
  | .num p n => nameComponents p ++ [toJson n]

def lastComponentIs (n : Name) (s : String) : Bool :=
  match n with
  | .str _ t => t == s
  | _ => false

def sortNames (xs : Array Name) : Array Name :=
  xs.qsort (·.toString < ·.toString)

def showNames (xs : Array Name) : String :=
  if xs.isEmpty then "no axioms" else ", ".intercalate (sortNames xs |>.toList.map (·.toString))

/-! ## Axioms, by walking the declarations -/

structure AxiomState where
  /-- declaration ↦ the axioms it depends on -/
  seen    : Std.HashMap Name (Array Name) := {}
  visited : Nat := 0
  /-- names that a declaration refers to and that the environment does not hold -/
  missing : Array Name := #[]

/-- The constants a declaration refers to, as `Lean.CollectAxioms.collect` takes them. -/
def directDependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo v  => v.type.getUsedConstants
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _   => #[]
  | .ctorInfo v   => v.type.getUsedConstants
  | .recInfo v    => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- The axioms that `c` depends on. A cycle (an inductive type and its constructors) is cut by
the entry that is made before the dependencies are visited. -/
partial def axiomsOf (env : Environment) (c : Name) : StateM AxiomState (Array Name) := do
  if let some axs := (← get).seen[c]? then return axs
  modify fun s => { s with seen := s.seen.insert c #[], visited := s.visited + 1 }
  let some info := env.find? c
    | modify (fun s => { s with missing := s.missing.push c }); return #[]
  let mut acc : Array Name := if info matches .axiomInfo _ then #[c] else #[]
  for d in directDependencies info do
    for a in ← axiomsOf env d do
      unless acc.contains a do acc := acc.push a
  let result := sortNames acc
  modify fun s => { s with seen := s.seen.insert c result }
  return result

/-- The axiom list that Lean itself reports for `c` (`Lean.collectAxioms`, which is what
`#print axioms` uses). For an imported declaration Lean takes it from the compiled file. -/
def storedAxiomsOf (env : Environment) (c : Name) : IO (Array Name) := do
  let act : CoreM (Array Name) := Lean.collectAxioms c
  let (axs, _) ← act.toIO { fileName := "<audit>", fileMap := default } { env }
  return sortNames axs

/-! ## Checks on one declaration -/

def hasInstImplicitBinder (e : Expr) : Bool :=
  (e.find? fun
    | .forallE _ _ _ .instImplicit => true
    | .lam _ _ _ .instImplicit => true
    | _ => false).isSome

/-- Did Lean store a source position for `n`? It does so for what a declaration command
declares (also structure fields and constructors), and not for what tactics generate. -/
def hasSourcePosition (env : Environment) (n : Name) : Bool :=
  (declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n).isSome

def kindOf (info : ConstantInfo) : String :=
  match info with
  | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive type" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quotient primitive"

def isSafeDefinition (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo d) => d.safety == .safe
  | _ => false

/-- The names that `n` would hide: `n` without one of its leading namespaces, when that shorter
name is a declaration from outside the library that is not a theorem. -/
def shadowed (env : Environment) (isLibraryConst : Name → Bool) (n : Name) : Array Name := Id.run do
  let n := privateToUserName n
  let comps := n.components
  let mut out := #[]
  for k in [1:comps.length] do
    let short := (comps.drop k).foldl (fun acc c => match c with
      | .str _ s => Name.str acc s
      | .num _ i => Name.num acc i
      | .anonymous => acc) Name.anonymous
    match env.find? short with
    | some (.thmInfo _) | none => pure ()
    | some _ => unless isLibraryConst short do out := out.push short
  return out

end Audit

open Audit in
unsafe def main (args : List String) : IO UInt32 := do
  let a ← match parseArgs args {} with
    | .ok a => pure a
    | .error msg => IO.eprintln msg; return 2
  if a.root.isEmpty || a.allow.isEmpty then
    IO.eprintln "usage: --root <root module> --allow <allow-list> [--lists <directory>]"
    return 2
  let root : Name := .mkSimple a.root
  let allowedExtensions ← loadExtensions a.allow
  enableInitializersExecution
  let env ← importModules #[{ module := root }] {} 0 (loadExts := true)
  let moduleNames := env.header.moduleNames
  let isLibraryModule (m : Name) : Bool := root.isPrefixOf m
  let isLibraryConst (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => isLibraryModule moduleNames[idx.toNat]!
    | none => false
  let out (s : String) : IO Unit := IO.println s
  let mut refused : Array String := #[]

  -- where the compiled files were loaded from (the search path is the one `importModules` used)
  let here ← IO.FS.realPath (← IO.currentDir)
  let under (dir file : System.FilePath) : Bool := (dir.toString ++ "/").isPrefixOf file.toString
  let buildLib := here / ".lake" / "build" / "lib" / "lean"
  let packages ← IO.FS.realPath (here / ".lake" / "packages")
  let toolchainLib ← IO.FS.realPath (← getLibDir (← getBuildDir))
  let mut fromBuild := 0
  let mut fromPackages := 0
  let mut fromToolchain := 0
  for m in moduleNames do
    let file ← IO.FS.realPath (← findOLean m)
    if isLibraryModule m then
      if under buildLib file then fromBuild := fromBuild + 1
      else refused := refused.push s!"{m}: [origin] a module of the library, but its compiled file was not loaded from \
        .lake/build/lib/lean of this project"
    else if under packages file then fromPackages := fromPackages + 1
    else if under toolchainLib file then fromToolchain := fromToolchain + 1
    else refused := refused.push s!"{m}: [origin] its compiled file was loaded neither from .lake/packages nor from \
      the toolchain"

  -- modules
  let mut byRoot : Std.HashMap String Nat := {}
  for m in moduleNames do
    let r := m.getRoot.toString
    byRoot := byRoot.insert r (byRoot.getD r 0 + 1)
  let libraryIdxs := (Array.range moduleNames.size).filter fun i => isLibraryModule moduleNames[i]!
  out s!"environment: what `import {root}` gives, loaded from the compiled files"
  out s!"modules of the library in it: {libraryIdxs.size}"
  let mut stored : Array (Name × ConstantInfo) := #[]
  let mut codeOnly := 0
  for i in libraryIdxs.qsort (fun i j => moduleNames[i]!.toString < moduleNames[j]!.toString) do
    let data := env.header.moduleData[i]!
    out s!"  {moduleNames[i]!}: {data.constNames.size} declarations"
    for n in data.constNames, c in data.constants do
      stored := stored.push (n, c)
    codeOnly := codeOnly + (data.extraConstNames.filter (!data.constNames.contains ·)).size
  let total : Nat := env.constants.map₁.size
  let compilerOnly : Nat := env.constants.map₁.fold
    (fun n _ c => if c.isUnsafe || c.isPartial then n + 1 else n) 0
  let roots := byRoot.toArray.qsort (·.1 < ·.1) |>.toList.map fun (r, n) => s!"{r} {n}"
  out s!"imported environment: {moduleNames.size} modules, {total} declarations"
  out s!"  modules by the first part of their name: {", ".intercalate roots}"
  out s!"  compiled files loaded from .lake/build of this project (the library): {fromBuild}; from .lake/packages: \
    {fromPackages}; from the toolchain: {fromToolchain}"
  out s!"  declarations marked unsafe or partial (they exist for the compiler; the replay tools leave \
    them out, and the kernel lets no safe definition or theorem refer to them): {compilerOnly}"

  -- declarations
  let mut kinds : Std.HashMap String Nat := {}
  let mut checkable : Array Name := #[]
  let mut partials : Array Name := #[]
  let mut theorems : Array String := #[]
  let mut thmCount := 0
  let mut used : Array Name := #[]
  let mut written := 0
  let mut generalAux := 0
  let mut axState : AxiomState := {}
  for (name, info) in stored do
    unless info.name == name do
      refused := refused.push s!"{name}: stored under this name, but the declaration is named {info.name}"
    match env.find? name with
    | some _ => pure ()
    | none => refused := refused.push s!"{name}: stored in a compiled file but not in the environment"
    let kind := kindOf info
    kinds := kinds.insert kind (kinds.getD kind 0 + 1)
    if info matches .thmInfo _ then thmCount := thmCount + 1
    if kind == "axiom" || kind == "opaque" || kind == "quotient primitive" then
      refused := refused.push s!"{name}: [kinds] declared as {kind}"
    -- For a definition by recursion `f` Lean also stores an auxiliary `f._unsafe_rec`, marked
    -- `partial`, which exists for the compiler. Lean's kernel refuses a safe definition or a
    -- theorem that refers to a `partial` or `unsafe` constant, and the replay tools leave such
    -- constants out. An auxiliary of this form that belongs to a safe definition is listed, by
    -- name, as not re-checked; anything else that is `unsafe` or `partial` is refused.
    if info.isUnsafe then
      refused := refused.push s!"{name}: [kinds] unsafe"
    else if info.isPartial then
      if lastComponentIs name "_unsafe_rec" && isSafeDefinition env name.getPrefix then
        partials := partials.push name
      else refused := refused.push s!"{name}: [kinds] partial"
    else
      checkable := checkable.push name
    -- axioms: walked here, and as Lean stored them
    let (walked, st) := (axiomsOf env name).run axState
    axState := st
    let storedAxioms ← storedAxiomsOf env name
    unless walked == storedAxioms do
      refused := refused.push s!"{name}: [axioms] walking the declarations gives [{showNames walked}], \
        the list stored in the compiled file says [{showNames storedAxioms}]"
    for ax in walked do
      unless used.contains ax do used := used.push ax
    let extra := walked.filter fun ax => !allowedAxioms.contains ax
    unless extra.isEmpty do
      refused := refused.push s!"{name}: [axioms] depends on {showNames extra}"
    -- binders, universes, reducibility: for what was written in a source file
    if hasSourcePosition env name then
      written := written + 1
      if hasInstImplicitBinder info.type then
        refused := refused.push s!"{name}: [binders] its type has an instance-implicit binder"
      if info.type.getUsedConstants.any (fun c => c == ``optParam || c == ``autoParam) then
        refused := refused.push s!"{name}: [binders] its type has an argument with a default value or a default tactic"
      unless info.levelParams.isEmpty do
        refused := refused.push s!"{name}: [universes] it has the universe parameters {info.levelParams}"
      if (info matches .defnInfo _) && !env.isProjectionFn name
          && getReducibilityStatusCore env name != .semireducible then
        refused := refused.push s!"{name}: [reducible] marked {repr (getReducibilityStatusCore env name)}"
    else if hasInstImplicitBinder info.type || !info.levelParams.isEmpty then
      generalAux := generalAux + 1
    let metaUses := info.type.getUsedConstants.filter fun c => c.getRoot == `Lean
    unless metaUses.isEmpty do
      refused := refused.push s!"{name}: [meta] its type mentions {sortNames metaUses}"
    for short in (if info matches .thmInfo _ then #[] else shadowed env isLibraryConst name) do
      refused := refused.push s!"{name}: [shadowing] inside its namespace the name `{short}` would mean it, \
        and `{short}` is a declaration from outside the library"
    -- auxiliary and private declarations (`_proof_1`, `match_1`, `_private...`) are audited like
    -- the others but not listed
    if (info matches .thmInfo _) && !name.isInternal then
      theorems := theorems.push s!"{name}: {showNames walked}"
  for c in axState.missing do
    refused := refused.push s!"{c}: [axioms] a declaration of the library refers to this name, directly or not, \
      and the environment holds no declaration of that name"
  checkable := sortNames checkable
  partials := sortNames partials

  -- extensions
  let mut census : Std.HashMap String Nat := {}
  for i in libraryIdxs do
    for (ext, entries) in env.header.moduleData[i]!.entries do
      unless entries.isEmpty do
        census := census.insert ext.toString (census.getD ext.toString 0 + entries.size)
  -- instances and simp lemmas, scoped entries included
  let mut instanceCount := 0
  let mut simpCount := 0
  let simpExts ← Meta.simpExtensionMapRef.get
  for i in libraryIdxs do
    let m := moduleNames[i]!
    for entry in Meta.instanceExtension.ext.getModuleEntries env i do
      let (scope, e) := match entry with
        | .global e => ("", e)
        | .«scoped» ns e => (s!" (scoped in {ns})", e)
      instanceCount := instanceCount + 1
      let generated := scope.isEmpty && e.globalName?.any (lastComponentIs · "_sizeOf_inst")
      unless generated do
        refused := refused.push s!"{e.globalName?.getD .anonymous}: [instances] registered as an instance{scope} in {m}"
    for (setName, ext) in simpExts.toArray do
      for entry in ext.ext.getModuleEntries env i do
        let (scope, e) := match entry with
          | .global e => ("", e)
          | .«scoped» ns e => (s!" (scoped in {ns})", e)
        simpCount := simpCount + 1
        let (what, generated) := match e with
          | .thm t => match t.origin with
            | .decl n .. => (s!"{n}", scope.isEmpty && setName == `simp
                && (lastComponentIs n "injEq" || lastComponentIs n "sizeOf_spec"))
            | _ => ("a lemma without a name", false)
          | .toUnfold n => (s!"{n} (to unfold)", false)
          | .toUnfoldThms n _ => (s!"{n} (to unfold)", false)
        unless generated do
          refused := refused.push s!"{what}: [simp] registered in the simp set `{setName}`{scope} in {m}"

  if !a.lists.isEmpty then
    let dir : System.FilePath := a.lists
    let lines (xs : Array String) : String := String.join (xs.toList.map (· ++ "\n"))
    let libraryNames := sortNames (libraryIdxs.map (moduleNames[·]!))
    IO.FS.writeFile (dir / "modules.txt") (lines (libraryNames.map (·.toString)))
    IO.FS.writeFile (dir / "constants.txt") (lines (checkable.map (·.toString (escape := true))))
    IO.FS.writeFile (dir / "constants.jsonl")
      (lines (checkable.map fun n => (Json.arr (nameComponents n).toArray).compress))
    IO.FS.writeFile (dir / "skipped.txt") (lines (partials.map (·.toString)))

  out s!"declarations stored in the compiled files of the library: {stored.size} (of which theorems: {thmCount})"
  let kindLines := (kinds.toArray.qsort (·.1 < ·.1)).toList.map fun (k, v) => s!"{k}: {v}"
  out s!"  kinds: {", ".intercalate kindLines}"
  out s!"  written in a source file (Lean stored a source position): {written}; the other {stored.size - written} are \
    generated (proofs split off, matchers, recursors, auxiliary lemmas of simp)"
  out s!"  generated ones with an instance-implicit binder or a universe parameter: {generalAux}"
  out s!"names of compiled code in these files that are not declarations (auxiliaries of the code generator; \
    not part of the logic, not looked at): {codeOnly}"
  out s!"declarations that the replay steps re-check: {checkable.size}; compiler auxiliaries marked partial, \
    which they leave out and to which the kernel lets no safe definition or theorem refer: {partials.size}"
  for n in partials do out s!"  {n}"
  out s!"declarations walked for axioms (the library and everything it refers to, directly or not): {axState.visited}"
  out s!"axioms that a declaration of the library depends on: {", ".intercalate ((sortNames used).toList.map (·.toString))}"
  out "entries of the library in Lean's environment extensions (name: number):"
  for (ext, n) in census.toArray.qsort (·.1 < ·.1) do
    if allowedExtensions.contains ext then
      out s!"  {ext}: {n}"
    else
      out s!"  {ext}: {n}  NOT ON THE ALLOW-LIST"
      refused := refused.push s!"{ext}: [extensions] the library has {n} entries in this environment \
        extension, which is not on the allow-list"
  let unusedExtensions := allowedExtensions.toArray.filter (!census.contains ·) |>.qsort (· < ·)
  if unusedExtensions.isEmpty then
    out "extensions on the allow-list in which the library has no entry: none"
  else
    out s!"extensions on the allow-list in which the library has no entry: {", ".intercalate unusedExtensions.toList}"
  out s!"instances of the library, scoped ones included: {instanceCount} (each is the `SizeOf` instance Lean \
    generates for a structure, or it is refused below)"
  out s!"simp entries of the library in the {simpExts.size} simp sets, scoped ones included: {simpCount} (each is an \
    `injEq` or `sizeOf_spec` lemma Lean generates for a structure, or it is refused below)"
  if refused.isEmpty then
    out "AUDIT OK: nothing refused. No declaration of the library depends on an axiom outside \
      [propext, Classical.choice, Quot.sound]."
  else
    out s!"AUDIT FAILED: {refused.size} refused"
    for r in refused do out s!"  {r}"
  theorems := theorems.qsort (· < ·)
  out s!"theorems with a name of their own, and the axioms each one depends on ({theorems.size}):"
  for t in theorems do out s!"  {t}"
  return if refused.isEmpty then 0 else 1

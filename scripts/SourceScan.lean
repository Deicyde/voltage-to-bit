import Lean

/-!
# Source scan: which constructs the library's source files use

Run by `scripts/check.sh` after the build, from the top directory of the
project. By hand:

    lake env lean --run scripts/SourceScan.lean scan --self scripts/SourceScan.lean \
      --allow scripts/allowlist.txt --root VoltageToBit --build .lake/build --jobs 2

(`scripts/check.sh` compiles this file once and runs the compiled form, which
saves compiling it again for every source file.) Exit status: 0 no finding,
1 at least one finding, 2 the command line is wrong or the scan itself failed.

## What it does

No text is lexed here. Every source file is read by Lean's own parser
(`Lean.Parser.parseHeader`, `Lean.Parser.parseCommand`), which is the code that
reads the file when Lean compiles it. So comments, strings, indentation and
tokens are whatever they are for Lean.

Each file is parsed in a process of its own, in the environment that Lean
builds from the file's own `import` lines, loaded from the compiled files with
the options and the import list that `lake build` passed to the compiler
(`<build>/ir/<module>.setup.json`). The parser of a file depends on what the
file imports, and on which namespaces are open at each point; so the commands
`namespace`, `end` and `open` are elaborated as they are met, and nothing else
is. The other commands that the allow-list admits (`variable`, and
declarations without attributes) do not change the parser.

Rules. A finding is printed for each violation, with file, line and column.

* tree     The source tree holds directories and `.lean` files only (files
           named `.DS_Store`, which macOS writes, are passed over); every name
           begins with an ASCII letter and is made of ASCII letters, digits
           and `_` (so no `__pycache__`, `_x`, `Bypäss` or `Upper.LEAN`);
           nothing is a symbolic link.
* closure  Every `.lean` file is in the import closure of the root file, and
           every imported module of the library has a source file.
* text     Every file is valid UTF-8 and holds no character outside printable
           ASCII, line feed and the characters listed in the allow-list (so no
           tab, carriage return, byte-order mark or bidirectional control).
* header   No `module` and no `prelude` line; every import is a plain
           `import M` with `M` a module of Mathlib or of the library, every
           component of whose name begins with an ASCII letter and is made of
           ASCII letters, digits and `_`.
* options  The build passed `autoImplicit = false` and `relaxedAutoImplicit =
           false` to the compiler for the file (read from the setup file that
           Lake wrote for it). With either option on, a name that is bound
           nowhere becomes a variable of the statement instead of an error.
* parse    Lean's parser reports no error, and reads the file to its end.
* scope    The commands `namespace`, `end` and `open` elaborate without error.
* command  Every command is of a kind on the allow-list.
* syntax   Every syntax node inside a command is of a kind on the allow-list.
           Both lists hold the kinds the library uses. Anything else is refused
           by name: attributes, instances, `notation`, `macro`, `syntax`,
           `elab`, `set_option`, `section`, `universe`, `deriving`, `#eval`,
           `run_cmd`, `sorry`, `native_decide`, tactic configuration such as
           `(config := ...)` or `+native`, instance binders `[...]`, `@f`,
           string literals, and every Mathlib command or tactic that the
           library does not use.
* universe No declaration name carries universe parameters (`foo.{u}`).
* variable A `variable` command binds only `(x : T)` and `{x : T}`.
* column   No code token ends beyond the column given in the allow-list, so
           that code is not out of sight far to the right.

The scan also counts the declarations written in the files (a declaration
command declares one name; a structure also declares its constructor and one
projection for each field). `scripts/check.sh` compares the number with the
number of declarations for which the compiled files hold a source position.

What this establishes when it reports no finding: the sentences above, for the
files as they are. What it does not establish: that a statement means what a
reader takes it to mean. A definition with a misleading name, or a hypothesis
that is in plain sight, is not a finding.

When the library needs a construct that is refused, the scan fails and names
the kind; the allow-list is then edited by hand, in a commit that says why.
`inventory` in place of `scan` prints the kinds and characters in use, in the
format of the allow-list.
-/

open Lean Elab

namespace SourceScan

/-! ## The allow-list -/

structure AllowList where
  commands  : Std.HashSet String := {}
  nodes     : Std.HashSet String := {}
  chars     : Std.HashSet Char := {}
  maxColumn : Nat := 0

/-- Parse `U+XXXX`. -/
def parseCodePoint (s : String) : Option Char := do
  guard (s.startsWith "U+")
  let hex := (s.drop 2).toString
  guard (!hex.isEmpty)
  let mut n : Nat := 0
  for c in hex.toList do
    let d ← if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none
    n := n * 16 + d
  guard (Nat.isValidChar n)
  return Char.ofNat n

def loadAllowList (path : System.FilePath) : IO AllowList := do
  let text ← IO.FS.readFile path
  let mut list : AllowList := {}
  let mut number := 0
  for line in text.splitOn "\n" do
    number := number + 1
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    let words := line.splitOn " " |>.filter (· ≠ "")
    match words with
    | ["command", kind] => list := { list with commands := list.commands.insert kind }
    | ["node", kind] => list := { list with nodes := list.nodes.insert kind }
    | "char" :: code :: _ =>
      match parseCodePoint code with
      | some c => list := { list with chars := list.chars.insert c }
      | none => throw <| IO.userError s!"{path}:{number}: not a code point: {code}"
    | ["extension", _] => pure ()   -- read by scripts/Audit.lean
    | ["max-column", n] =>
      match n.toNat? with
      | some n => list := { list with maxColumn := n }
      | none => throw <| IO.userError s!"{path}:{number}: not a number: {n}"
    | _ => throw <| IO.userError s!"{path}:{number}: not understood: {line}"
  if list.maxColumn == 0 then
    throw <| IO.userError s!"{path}: no `max-column` line"
  return list

/-! ## Small helpers -/

/-- A name of the source tree, or a component of a module name: an ASCII letter, then ASCII
letters, digits and `_`. (`Char.isAlpha` and `Char.isAlphanum` are ASCII only.) -/
def isPlainName (s : String) : Bool :=
  match s.toList with
  | c :: rest => c.isAlpha && rest.all (fun c => c.isAlphanum || c == '_')
  | [] => false

def showChar (c : Char) : String :=
  let hex := String.ofList (Nat.toDigits 16 c.toNat) |>.toUpper
  "U+" ++ String.ofList (List.replicate (4 - hex.length) '0') ++ hex

def allowedChar (allow : AllowList) (c : Char) : Bool :=
  c == '\n' || (' ' ≤ c && c ≤ '~') || allow.chars.contains c

/-- One finding: position (line and column from 1; 0 when there is none), rule, message. -/
structure Finding where
  line    : Nat
  column  : Nat
  rule    : String
  message : String

/-- A message on one line. -/
def oneLine (s : String) : String :=
  " ".intercalate ((s.splitOn "\n").map (·.trimAscii.toString) |>.filter (· ≠ ""))

def Finding.render (path : String) (lines : Array String) (f : Finding) : String :=
  let pos := if f.line == 0 then "" else s!"{f.line}:{f.column}:"
  let head := s!"{path}:{pos} [{f.rule}] {oneLine f.message}"
  match (if f.line == 0 then none else lines[f.line - 1]?) with
  | some src =>
    let src := src.trimAscii.toString
    if src.isEmpty then head else head ++ "\n    " ++ (if src.length > 160 then (src.take 160).toString ++ " ..." else src)
  | none => head

/-! ## One file (child process) -/

structure FileState where
  findings     : Array Finding := #[]
  commandKinds : Std.HashMap String Nat := {}
  nodeKinds    : Std.HashMap String Nat := {}
  opens        : Array String := #[]
  commands     : Nat := 0
  maxColumn    : Nat := 0
  /-- (kind, command number) pairs already reported, and lines already reported for `column` -/
  reported     : Std.HashSet String := {}
  kindNames    : Std.HashMap Name String := {}

abbrev ScanM := StateRefT FileState Frontend.FrontendM

def addFinding (line column : Nat) (rule message : String) : ScanM Unit :=
  modify fun s => { s with findings := s.findings.push { line, column, rule, message } }

def positionOf (pos? : Option String.Pos.Raw) : ScanM (Nat × Nat) := do
  let ictx ← Frontend.getInputContext
  match pos? with
  | some pos => let p := ictx.fileMap.toPosition pos; return (p.line, p.column + 1)
  | none => return (0, 0)

def addFindingAt (stx : Syntax) (fallback : Syntax) (rule message : String) : ScanM Unit := do
  let (line, column) ← positionOf (stx.getPos? <|> fallback.getPos?)
  addFinding line column rule message

def kindName (k : Name) : ScanM String := do
  match (← get).kindNames[k]? with
  | some s => return s
  | none =>
    let s := k.toString
    modify fun st => { st with kindNames := st.kindNames.insert k s }
    return s

/-- Report something once for each command in which it occurs. -/
def once (key : String) (act : ScanM Unit) : ScanM Unit := do
  unless (← get).reported.contains key do
    modify fun s => { s with reported := s.reported.insert key }
    act

/-- Walk a command: every node kind inside it must be on the allow-list; leaves give the last
column. The kind of the command itself (`isRoot`) is judged by the caller. -/
partial def walk (allow : AllowList) (cmd : Syntax) (number : Nat) (stx : Syntax) (isRoot := false) :
    ScanM Unit := do
  match stx with
  | .missing =>
    once s!"missing/{number}" do
      addFindingAt stx cmd "parse" "the syntax tree of this command is incomplete"
  | .node _ k args =>
    unless isRoot do
      let name ← kindName k
      modify fun s => { s with nodeKinds := s.nodeKinds.insert name (s.nodeKinds.getD name 0 + 1) }
      unless allow.nodes.contains name do
        once s!"{name}/{number}" do
          addFindingAt stx cmd "syntax" s!"syntax of kind `{name}` is not on the allow-list"
    if k == ``Parser.Command.declId then
      unless args.size == 2 && args[1]!.getNumArgs == 0 do
        addFindingAt stx cmd "universe" "the declaration name carries universe parameters"
    for arg in args do
      walk allow cmd number arg
  | .atom .. | .ident .. =>
    if let some tail := stx.getTailPos? then
      let ictx ← Frontend.getInputContext
      let p := ictx.fileMap.toPosition tail
      if p.column > (← get).maxColumn then
        modify fun s => { s with maxColumn := p.column }
      if p.column > allow.maxColumn then
        once s!"column/{p.line}" do
          addFinding p.line p.column "column"
            s!"a code token ends in column {p.column}, beyond column {allow.maxColumn}"

/-- The commands that are elaborated, because they change which parsers are active. -/
def scopeCommands : List Name :=
  [``Parser.Command.namespace, ``Parser.Command.end, ``Parser.Command.open]

def checkVariable (cmd : Syntax) : ScanM Unit := do
  -- `variable` binder+
  for binder in cmd[1].getArgs do
    unless binder.isOfKind ``Parser.Term.explicitBinder || binder.isOfKind ``Parser.Term.implicitBinder do
      addFindingAt binder cmd "variable"
        "a `variable` command may bind only `(x : T)` and `{x : T}`: an instance binder would be \
         added to later theorems whose text does not mention it"

def sourceOf (stx : Syntax) : ScanM String := do
  let ictx ← Frontend.getInputContext
  match stx.getPos?, stx.getTailPos? with
  | some a, some b =>
    let text := (String.Pos.Raw.extract ictx.inputString a b)
    return " ".intercalate (text.splitOn "\n" |>.flatMap (·.splitOn " ") |>.filter (· ≠ ""))
  | _, _ => return ""

/-- Take the error messages out of the command state and turn them into findings. -/
def drainMessages (rule : String) : ScanM Unit := do
  let cmdState ← Frontend.getCommandState
  for msg in cmdState.messages.toList do
    if msg.severity matches .error then
      let text := (← msg.data.toString).trimAscii.toString
      let text := " ".intercalate (text.splitOn "\n" |>.map (·.trimAscii.toString))
      addFinding msg.pos.line (msg.pos.column + 1) rule
        (if text.length > 300 then (text.take 300).toString ++ " ..." else text)
  Frontend.setMessages {}

partial def scanCommands (allow : AllowList) : ScanM Unit := do
  Frontend.updateCmdPos
  let cmdState ← Frontend.getCommandState
  let ictx ← Frontend.getInputContext
  let pstate ← Frontend.getParserState
  let scope := cmdState.scopes.head!
  -- as in `Lean.Elab.Frontend.processCommand`
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
                 openDecls := scope.openDecls }
  let (cmd, ps, messages) := Parser.parseCommand ictx pmctx pstate {}
  Frontend.setParserState ps
  Frontend.setMessages messages
  drainMessages "parse"
  let number := (← get).commands + 1
  let name ← kindName cmd.getKind
  modify fun s => { s with commands := number,
                           commandKinds := s.commandKinds.insert name (s.commandKinds.getD name 0 + 1) }
  unless allow.commands.contains name do
    addFindingAt cmd cmd "command" s!"a command of kind `{name}` is not on the allow-list"
  walk allow cmd number cmd (isRoot := true)
  if cmd.isOfKind ``Parser.Command.variable then
    checkVariable cmd
  if cmd.isOfKind ``Parser.Command.open then
    let text ← sourceOf cmd
    modify fun s => { s with opens := s.opens.push text }
  if scopeCommands.contains cmd.getKind then
    Frontend.runCommandElabM (Command.elabCommand cmd)
    drainMessages "scope"
  if Parser.isTerminalCommand cmd then
    unless cmd.isOfKind ``Parser.Command.eoi do
      addFindingAt cmd cmd "parse" "Lean stops reading the file at this command"
  else
    scanCommands allow

def checkText (allow : AllowList) (text : String) : Array Finding := Id.run do
  let mut findings : Array Finding := #[]
  let mut seen : Std.HashSet Char := {}
  let mut line := 1
  let mut column := 0
  if text.startsWith "#lang" then
    findings := findings.push (Finding.mk 1 1 "text"
      "the file starts with `#lang`: Lean drops the first line before it parses")
  for c in text.toList do
    column := column + 1
    unless allowedChar allow c do
      unless seen.contains c do
        seen := seen.insert c
        findings := findings.push (Finding.mk line column "text"
          s!"character {showChar c} is neither printable ASCII nor on the allow-list \
            (first occurrence in this file)")
    if c == '\n' then
      line := line + 1
      column := 0
  return findings

/-- Checks on the header that need no environment. Returns the imported modules. -/
def checkHeader (root : Name) (header : HeaderSyntax) (ictx : Parser.InputContext) :
    Array Finding × Array Name := Id.run do
  let mut findings : Array Finding := #[]
  let mut imports : Array Name := #[]
  let at_ (stx : Syntax) (rule message : String) : Finding :=
    match stx.getPos? with
    | some pos => let p := ictx.fileMap.toPosition pos; { line := p.line, column := p.column + 1, rule, message }
    | none => { line := 1, column := 1, rule, message }
  let stx := header.raw
  -- `Lean.Parser.Module.header`: optional `module`, optional `prelude`, `import`*
  unless stx.isOfKind ``Parser.Module.header && stx.getNumArgs == 3 do
    return (#[{ line := 1, column := 1, rule := "header", message := "the file header was not parsed" }], #[])
  unless stx[0].isNone do
    findings := findings.push (at_ stx[0] "header" "`module`: the library does not use the module system")
  unless stx[1].isNone do
    findings := findings.push (at_ stx[1] "header" "`prelude`: the file would be compiled without `Init`")
  -- what Lean itself takes from the header (`Lean.Elab.HeaderSyntax.imports`)
  let leanImports := (HeaderSyntax.imports header (includeInit := false)).map (·.module)
  let nodes := stx[2].getArgs
  unless nodes.size == leanImports.size do
    findings := findings.push (at_ stx "header" "the import lines were not parsed as expected")
  for imp in nodes, mod in leanImports do
    -- `Lean.Parser.Module.import`: optional `public`, optional `meta`, `import`, optional `all`,
    -- the name, and an empty node where a name ends in a dot
    unless imp.isOfKind ``Parser.Module.import && imp.getNumArgs ≥ 5 && imp[4].isIdent
        && imp[4].getId == mod && (imp.getArgs.extract 5 imp.getNumArgs).all (·.isNone) do
      findings := findings.push (at_ imp "header" "an import line was not parsed as expected")
      continue
    unless imp[0].isNone && imp[1].isNone && imp[3].isNone do
      findings := findings.push (at_ imp "header" "`public`, `meta` or `all` on an import")
    imports := imports.push mod
    let first := mod.getRoot
    unless (first == root || first == `Mathlib) && !mod.isAnonymous && !mod.hasMacroScopes
        && mod.components.all (fun c => match c with | .str .anonymous s => isPlainName s | _ => false) do
      findings := findings.push (at_ imp "import"
        s!"import of `{mod}`: only modules of Mathlib and of {root} are allowed, with names whose \
          components begin with an ASCII letter and are made of ASCII letters, digits and `_`")
  return (findings, imports)

structure FileArgs where
  path   : String
  module : Name
  root   : Name
  setup? : Option String

/-- Read and decode a source file. -/
def readSource (path : String) : IO (Except String String) := do
  let bytes ← IO.FS.readBinFile path
  match String.fromUTF8? bytes with
  | some text => return .ok text
  | none => return .error "the file is not valid UTF-8"

def emit (tag text : String) : IO Unit :=
  IO.println s!"{tag} {text}"

/-- Scan one file and print the result as tagged lines. Returns the number of findings. -/
unsafe def scanFile (allow : AllowList) (args : FileArgs) : IO Nat := do
  let path := args.path
  emit "FILE" path
  let text ← match (← readSource path) with
    | .ok text => pure text
    | .error msg =>
      emit "FINDING" ({ line := 0, column := 0, rule := "text", message := msg : Finding }.render path #[])
      emit "END" path
      return 1
  let lines := (text.splitOn "\n").toArray
  let mut findings := checkText allow text
  -- as in `Lean.Elab.runFrontend`
  let inputCtx := Parser.mkInputContext text path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  for msg in messages.toList do
    findings := findings.push (Finding.mk msg.pos.line (msg.pos.column + 1) "parse"
      (← msg.data.toString).trimAscii.toString)
  let (headerFindings, _) := checkHeader args.root header inputCtx
  findings := findings ++ headerFindings
  let mut state : FileState := {}
  let mut optionsOk := false
  -- the body is read even when an import is refused: the build has loaded the same modules
  if !messages.hasErrors then
    -- the environment of the file's own imports, as the compiler builds it
    let mut opts : Options := {}
    let mut imports := HeaderSyntax.imports header
    let mut isModule := HeaderSyntax.isModule header
    let mut package? := none
    let mut arts : NameMap ImportArtifacts := {}
    let mut setupOk := true
    if let some setupPath := args.setup? then
      match (← (ModuleSetup.load setupPath).toBaseIO) with
      | .ok setup =>
        unless setup.name == args.module && !setup.isModule && setup.imports?.isNone
            && setup.plugins.isEmpty && setup.dynlibs.isEmpty do
          setupOk := false
          findings := findings.push (Finding.mk 0 0 "parse"
            s!"{setupPath} is not what this scan expects of the build (module name, \
              `isModule`, imports, plugins or dynlibs)")
        let isFalse (n : Name) : Bool := match setup.options.values.get? n with
          | some (.ofBool false) => true
          | _ => false
        if isFalse `autoImplicit && isFalse `relaxedAutoImplicit then
          optionsOk := true
        else
          findings := findings.push (Finding.mk 0 0 "options"
            "the build did not pass `autoImplicit = false` and `relaxedAutoImplicit = false` to the \
             compiler for this file: a name that is bound nowhere becomes a variable, not an error")
        opts := opts.mergeBy (fun _ _ hOpt => hOpt) setup.options.toOptions
        imports := setup.imports?.getD (HeaderSyntax.imports header)
        isModule := strictOr setup.isModule (HeaderSyntax.isModule header)
        package? := setup.package?
        arts := setup.importArts
      | .error e =>
        setupOk := false
        findings := findings.push (Finding.mk 0 0 "parse"
          s!"cannot read what the build passed to the compiler for this file (was it compiled?): {e}")
    if setupOk then
      enableInitializersExecution
      let (env, messages) ← processHeaderCore (HeaderSyntax.startPos header) imports isModule opts {} inputCtx
        (mainModule := args.module) (package? := package?) (arts := arts) (headerStx? := header)
      if messages.hasErrors then
        let here := (← IO.currentDir).toString ++ "/"
        for msg in messages.toList do
          if msg.severity matches .error then
            let text := (← msg.data.toString).trimAscii.toString.replace here ""
            findings := findings.push (Finding.mk msg.pos.line (msg.pos.column + 1) "parse"
              ("the imports could not be loaded: " ++ text))
      else
        let cmdState := Command.mkState env {} opts
        let ((_, st), _) ← ((scanCommands allow).run {}).run { inputCtx }
          |>.run { commandState := cmdState, parserState := parserState, cmdPos := parserState.pos }
        state := st
        findings := findings ++ st.findings
  let lineCount := if text.endsWith "\n" then lines.size - 1 else lines.size
  emit "STAT" s!"{lineCount} {state.commands} {state.maxColumn}"
  if optionsOk then emit "OPTIONS" "ok"
  for (k, n) in state.commandKinds.toArray do emit "CMD" s!"{n} {k}"
  for (k, n) in state.nodeKinds.toArray do emit "KIND" s!"{n} {k}"
  for o in state.opens do emit "OPEN" o
  let sorted := findings.qsort fun a b => a.line < b.line || (a.line == b.line && a.column < b.column)
  for f in sorted do
    -- a finding takes one or two lines; the second is the source line
    for (part, i) in ((f.render path lines).splitOn "\n").zipIdx do
      emit (if i == 0 then "FINDING" else "FINDING+") part
  emit "END" path
  return findings.size

/-! ## The whole library (parent process) -/

structure SourceFile where
  path   : String
  module : Name

/-- List the source tree. Findings are (path, message). -/
partial def walkTree (dir : System.FilePath) (modPrefix : Name) (files : Array SourceFile)
    (findings : Array String) : IO (Array SourceFile × Array String) := do
  let mut files := files
  let mut findings := findings
  let entries := (← dir.readDir).qsort (fun a b => a.fileName < b.fileName)
  for entry in entries do
    let path := entry.path
    let shown := "/".intercalate (path.components)
    let kind := (← path.symlinkMetadata).type
    if kind == .symlink then
      findings := findings.push s!"{shown}: [tree] a symbolic link"
    else if kind == .dir then
      if isPlainName entry.fileName then
        (files, findings) ← walkTree path (modPrefix.str entry.fileName) files findings
      else
        findings := findings.push s!"{shown}: [tree] a directory whose name does not begin with an ASCII \
          letter or is not made of ASCII letters, digits and `_`"
    else if kind == .file then
      if entry.fileName == ".DS_Store" then
        continue
      else if entry.fileName.endsWith ".lean" && isPlainName (entry.fileName.dropEnd 5).toString then
        files := files.push { path := shown, module := modPrefix.str (entry.fileName.dropEnd 5).toString }
      else
        findings := findings.push s!"{shown}: [tree] not a `.lean` file whose name begins with an ASCII \
          letter and is made of ASCII letters, digits and `_`"
    else
      findings := findings.push s!"{shown}: [tree] neither a file nor a directory"
  return (files, findings)

structure ChildResult where
  file         : SourceFile
  lines        : Nat := 0
  commands     : Nat := 0
  maxColumn    : Nat := 0
  commandKinds : Array (String × Nat) := #[]
  nodeKinds    : Array (String × Nat) := #[]
  opens        : Array String := #[]
  findings     : Array String := #[]
  optionsOk    : Bool := false
  complete     : Bool := false

def splitCount (s : String) : Option (Nat × String) := do
  let parts := s.splitOn " "
  let n ← parts.head?.bind (·.toNat?)
  return (n, " ".intercalate parts.tail)

def parseChild (file : SourceFile) (out : IO.Process.Output) : ChildResult := Id.run do
  let mut r : ChildResult := { file }
  for line in out.stdout.splitOn "\n" do
    if let some rest := line.dropPrefix? "STAT " then
      match rest.toString.splitOn " " |>.map (·.toNat?) with
      | [some a, some b, some c] => r := { r with lines := a, commands := b, maxColumn := c }
      | _ => pure ()
    else if let some rest := line.dropPrefix? "CMD " then
      if let some (n, k) := splitCount rest.toString then r := { r with commandKinds := r.commandKinds.push (k, n) }
    else if let some rest := line.dropPrefix? "KIND " then
      if let some (n, k) := splitCount rest.toString then r := { r with nodeKinds := r.nodeKinds.push (k, n) }
    else if line == "OPTIONS ok" then
      r := { r with optionsOk := true }
    else if let some rest := line.dropPrefix? "OPEN " then
      r := { r with opens := r.opens.push rest.toString }
    else if let some rest := line.dropPrefix? "FINDING+ " then
      if r.findings.size > 0 then
        r := { r with findings := r.findings.modify (r.findings.size - 1) (· ++ "\n" ++ rest.toString) }
    else if let some rest := line.dropPrefix? "FINDING " then
      r := { r with findings := r.findings.push rest.toString }
    else if line == s!"END {file.path}" then
      r := { r with complete := true }
  -- the child must end normally: status 0 without findings, status 1 with findings
  let expected : UInt32 := if r.findings.isEmpty then 0 else 1
  unless r.complete && out.exitCode == expected do
    let err := out.stderr.trimAscii.toString
    let err := if err.length > 600 then (err.take 600).toString ++ " ..." else err
    let note := if err.isEmpty then "" else ": " ++ err
    let finding := s!"{file.path}: [parse] the scan of this file did not complete (exit status {out.exitCode}){note}"
    r := { r with complete := false, findings := r.findings.push finding }
  return r

structure ScanArgs where
  self    : String := ""
  allow   : String := ""
  root    : String := ""
  build   : String := ""
  jobs    : Nat := 1
  files   : Array String := #[]

def parseArgs : List String → ScanArgs → Except String ScanArgs
  | [], a => .ok a
  | "--self" :: v :: rest, a => parseArgs rest { a with self := v }
  | "--allow" :: v :: rest, a => parseArgs rest { a with allow := v }
  | "--root" :: v :: rest, a => parseArgs rest { a with root := v }
  | "--build" :: v :: rest, a => parseArgs rest { a with build := v }
  | "--jobs" :: v :: rest, a =>
    match v.toNat? with
    | some n => if n ≥ 1 then parseArgs rest { a with jobs := n } else .error "--jobs must be 1 or more"
    | none => .error "--jobs must be a number"
  | v :: rest, a => if v.startsWith "--" then .error s!"unknown option {v}" else parseArgs rest { a with files := a.files.push v }

def sortedPairs (m : Std.HashMap String Nat) : Array (String × Nat) :=
  m.toArray.qsort fun a b => a.1 < b.1

/-- Run the child scans, `jobs` at a time. -/
def runChildren (a : ScanArgs) (files : Array SourceFile) (setupOf : SourceFile → Option String) :
    IO (Array ChildResult) := do
  let lean ← IO.appPath
  let mut results : Array ChildResult := #[]
  let mut i := 0
  while i < files.size do
    let chunk := files.extract i (min files.size (i + a.jobs))
    let mut tasks := #[]
    for file in chunk do
      let mut args := #["--run", a.self, "file", "--allow", a.allow, "--root", a.root,
        "--module", file.module.toString, "--path", file.path]
      if let some setup := setupOf file then
        args := args ++ #["--setup", setup]
      tasks := tasks.push (file, ← IO.asTask (prio := .dedicated)
        (IO.Process.output { cmd := lean.toString, args }))
    for (file, task) in tasks do
      match task.get with
      | .ok out => results := results.push (parseChild file out)
      | .error e =>
        let finding := s!"{file.path}: [parse] the scan of this file could not be started: {e}"
        results := results.push { file, findings := #[finding] }
    i := i + a.jobs
  return results

def report (a : ScanArgs) (allow : AllowList) (inventory : Bool) (treeFindings : Array String)
    (results : Array ChildResult) (closureNote : String) (external : Array (String × Nat)) : IO UInt32 := do
  let mut commandKinds : Std.HashMap String Nat := {}
  let mut nodeKinds : Std.HashMap String Nat := {}
  let mut opens : Std.HashMap String Nat := {}
  let mut findings := treeFindings
  let mut lines := 0
  let mut commands := 0
  let mut maxColumn := 0
  for r in results do
    lines := lines + r.lines
    commands := commands + r.commands
    maxColumn := max maxColumn r.maxColumn
    for (k, n) in r.commandKinds do commandKinds := commandKinds.insert k (commandKinds.getD k 0 + n)
    for (k, n) in r.nodeKinds do nodeKinds := nodeKinds.insert k (nodeKinds.getD k 0 + n)
    for o in r.opens do opens := opens.insert o (opens.getD o 0 + 1)
    findings := findings ++ r.findings
  if inventory then
    IO.println "# kinds and characters in use, in the format of the allow-list"
    for (k, _) in sortedPairs commandKinds do IO.println s!"command {k}"
    for (k, _) in sortedPairs nodeKinds do IO.println s!"node {k}"
    let mut chars : Std.HashSet Char := {}
    for r in results do
      if let .ok text ← readSource r.file.path then
        for c in text.toList do
          unless c == '\n' || (' ' ≤ c && c ≤ '~') do chars := chars.insert c
    for c in chars.toArray.qsort (· < ·) do IO.println s!"char {showChar c} {c}"
    IO.println s!"max-column {maxColumn}"
    return 0
  IO.println "parser: Lean's own (Lean.Parser.parseHeader, Lean.Parser.parseCommand); each file in a process of"
  IO.println "  its own, in the environment of its own imports as compiled; no text is lexed by this script"
  IO.println s!"allow-list: {a.allow} ({allow.commands.size} kinds of command, {allow.nodes.size} kinds of \
    syntax node, {allow.chars.size} characters besides printable ASCII and line feed, code up to column \
    {allow.maxColumn})"
  IO.println s!"files: {results.size} ({lines} lines, {commands} commands with the end-of-file markers); {closureNote}"
  for r in results do
    IO.println s!"  {r.file.path}: {r.lines} lines, {r.commands} commands"
  IO.println s!"files for which the build passed `autoImplicit = false` and `relaxedAutoImplicit = false` to \
    the compiler: {(results.filter (·.optionsOk)).size} of {results.size}"
  IO.println "commands by kind:"
  for (k, n) in sortedPairs commandKinds do IO.println s!"  {k}: {n}"
  -- what a reader finds declared in the text: a declaration command declares one name; a structure
  -- also declares its constructor and one projection for each field
  let declarations := commandKinds.getD "Lean.Parser.Command.declaration" 0
    + nodeKinds.getD "Lean.Parser.Command.declaration" 0
  let fields := nodeKinds.getD "Lean.Parser.Command.structSimpleBinder" 0
  let structures := nodeKinds.getD "Lean.Parser.Command.structure" 0
  IO.println s!"declarations written in the files: {declarations + fields + structures} ({declarations} declaration \
    commands, {structures} structure constructors, {fields} structure fields)"
  IO.println s!"kinds of syntax node in use inside the commands: {nodeKinds.size}; code tokens end at or before \
    column {maxColumn}"
  let unused := allow.nodes.toArray.filter (!nodeKinds.contains ·) |>.qsort (· < ·)
  let unusedCommands := allow.commands.toArray.filter (!commandKinds.contains ·) |>.qsort (· < ·)
  if unused.isEmpty && unusedCommands.isEmpty then
    IO.println "kinds on the allow-list that no file uses: none"
  else
    IO.println "kinds on the allow-list that no file uses (the list is wider than the library needs):"
    for k in unusedCommands do IO.println s!"  command {k}"
    for k in unused do IO.println s!"  node {k}"
  IO.println "modules imported from outside the library, with the number of files that import each:"
  for (m, n) in external do IO.println s!"  {m}: {n}"
  IO.println "`open` commands, for the record (they bring names and notation of Mathlib into scope):"
  for (o, n) in sortedPairs opens do IO.println s!"  `{o}`: {n}"
  if findings.isEmpty then
    IO.println "no finding"
    return 0
  else
    for f in findings do IO.println f
    IO.println s!"FINDINGS: {findings.size}"
    return 1

def moduleFile (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

unsafe def scanLibrary (a : ScanArgs) (inventory : Bool) : IO UInt32 := do
  if a.self.isEmpty || a.allow.isEmpty || a.root.isEmpty || a.build.isEmpty || !a.files.isEmpty
      || !isPlainName a.root then
    IO.eprintln "usage: scan --self <this file> --allow <allow-list> --root <root module> --build <build directory> [--jobs N]"
    return 2
  let allow ← loadAllowList a.allow
  let root : Name := .mkSimple a.root
  let rootFile : SourceFile := { path := a.root ++ ".lean", module := root }
  let mut findings : Array String := #[]
  -- the source tree
  let mut files : Array SourceFile := #[]
  match (← (System.FilePath.symlinkMetadata rootFile.path).toBaseIO) with
  | .ok md =>
    if md.type == .file then files := files.push rootFile
    else findings := findings.push s!"{rootFile.path}: [tree] not a regular file"
  | .error _ => findings := findings.push s!"{rootFile.path}: [tree] no such file"
  match (← (System.FilePath.symlinkMetadata a.root).toBaseIO) with
  | .ok md =>
    if md.type == .dir then
      (files, findings) ← walkTree a.root root files findings
    else findings := findings.push s!"{a.root}: [tree] not a directory"
  | .error _ => findings := findings.push s!"{a.root}: [tree] no such directory"
  -- headers and the import closure (the child of each file reports what is wrong inside it)
  let known : Std.HashSet Name := files.foldl (fun s f => s.insert f.module) {}
  let mut importsOf : Std.HashMap Name (Array Name) := {}
  let mut external : Std.HashMap String Nat := {}
  let mut closureOk := true
  for file in files do
    if let .ok text ← readSource file.path then
      let inputCtx := Parser.mkInputContext text file.path
      let (header, _, _) ← Parser.parseHeader inputCtx
      let (_, imports) := checkHeader root header inputCtx
      importsOf := importsOf.insert file.module imports
      let mut seen : Std.HashSet Name := {}
      for m in imports do
        if seen.contains m then continue
        seen := seen.insert m
        if m.getRoot == root then
          unless known.contains m do
            closureOk := false
            findings := findings.push
              s!"{file.path}: [closure] import of `{m}`: there is no source file {moduleFile m}"
        else
          external := external.insert m.toString (external.getD m.toString 0 + 1)
  let mut reached : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let m := todo.back!
    todo := todo.pop
    if reached.contains m then continue
    reached := reached.insert m
    for i in importsOf.getD m #[] do
      if i.getRoot == root && known.contains i then todo := todo.push i
  for file in files do
    unless reached.contains file.module do
      closureOk := false
      findings := findings.push
        s!"{file.path}: [closure] not imported by {rootFile.path}, directly or through other files: \
          Lean does not compile it"
  let closureNote := if closureOk then s!"each one is in the import closure of {rootFile.path}"
    else s!"NOT all in the import closure of {rootFile.path}, see the findings"
  -- one child per file
  let setupOf (file : SourceFile) : Option String :=
    some (a.build ++ "/ir/" ++ "/".intercalate (file.module.components.map (·.toString)) ++ ".setup.json")
  let results ← runChildren a files setupOf
  report a allow inventory findings results closureNote (sortedPairs external)

/-- Scan given files on their own (no source tree, no closure, no setup file): for the self-test. -/
unsafe def scanTexts (a : ScanArgs) : IO UInt32 := do
  if a.self.isEmpty || a.allow.isEmpty || a.root.isEmpty || a.files.isEmpty then
    IO.eprintln "usage: texts --self <this file> --allow <allow-list> --root <root module> [--jobs N] FILE..."
    return 2
  discard <| loadAllowList a.allow
  let files := a.files.map fun p => ({ path := p, module := `Standalone } : SourceFile)
  let results ← runChildren a files (fun _ => none)
  let mut status : UInt32 := 0
  for r in results do
    IO.println s!"== {r.file.path}"
    for f in r.findings do IO.println f
    if r.findings.isEmpty then IO.println "no finding" else status := 1
  return status

unsafe def scanOne (rest : List String) : IO UInt32 := do
  let rec go : List String → (String × String × String × String × Option String) → Except String (String × String × String × String × Option String)
    | [], r => .ok r
    | "--allow" :: v :: rest, (_, b, c, d, e) => go rest (v, b, c, d, e)
    | "--root" :: v :: rest, (a, _, c, d, e) => go rest (a, v, c, d, e)
    | "--module" :: v :: rest, (a, b, _, d, e) => go rest (a, b, v, d, e)
    | "--path" :: v :: rest, (a, b, c, _, e) => go rest (a, b, c, v, e)
    | "--setup" :: v :: rest, (a, b, c, d, _) => go rest (a, b, c, d, some v)
    | v :: _, _ => .error s!"unexpected argument {v}"
  match go rest ("", "", "", "", none) with
  | .error msg => IO.eprintln msg; return 2
  | .ok (allowPath, root, module, path, setup?) =>
    if allowPath.isEmpty || root.isEmpty || module.isEmpty || path.isEmpty then
      IO.eprintln "usage: file --allow <allow-list> --root <root module> --module <name> --path <file> [--setup <json>]"
      return 2
    let allow ← loadAllowList allowPath
    let moduleName := module.splitOn "." |>.foldl (fun n s => Name.str n s) Name.anonymous
    let n ← scanFile allow { path, module := moduleName, root := .mkSimple root, setup? }
    return if n == 0 then 0 else 1

end SourceScan

unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | "scan" :: rest =>
      match SourceScan.parseArgs rest {} with
      | .ok a => SourceScan.scanLibrary a false
      | .error msg => IO.eprintln msg; return 2
    | "inventory" :: rest =>
      match SourceScan.parseArgs rest {} with
      | .ok a => SourceScan.scanLibrary a true
      | .error msg => IO.eprintln msg; return 2
    | "texts" :: rest =>
      match SourceScan.parseArgs rest {} with
      | .ok a => SourceScan.scanTexts a
      | .error msg => IO.eprintln msg; return 2
    | "file" :: rest => SourceScan.scanOne rest
    | _ =>
      IO.eprintln "usage: scan | inventory | texts | file (see the head of scripts/SourceScan.lean)"
      return 2
  catch e =>
    IO.eprintln s!"SourceScan.lean: {e}"
    return 2

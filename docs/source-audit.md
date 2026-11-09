# Source audit: `assembly-to-physics` at `7359bfe` (workstream A)

Owner: workstream A. Date: 2026-11-09. Status: complete for the pinned commit, except that two
upstream audit scripts were not executed (§2 rows 9–10).

Scope: the inverter-relevant sources of
[Deicyde/assembly-to-physics](https://github.com/Deicyde/assembly-to-physics/tree/7359bfe8266d06954e221f881403e7e83d5592f6)
at commit `7359bfe8266d06954e221f881403e7e83d5592f6`, reproduction of the baseline, reuse terms, and
a port proposal relative to `docs/interface.md` (§11 says which version). The flip-flop,
synchronous refinement and the probability shell are out of scope except for the vacuity probe
(§12). The old repository's processor-scale roadmap is not imported.

Conventions:

- `File.lean:a-b` is a line range in the pinned commit. Quoted Lean is copied mechanically from
  those lines; where marked "docstrings dropped", only `/-- … -/` blocks are removed.
- `$W` is the workspace directory containing `voltage-to-bit/` and `refs/`. The fresh clone is
  `$W/refs/assembly-to-physics`. This audit's scripts, probes and logs are in
  `$W/refs/workstream-A/`, outside this repository (hashes in Appendix C).
- **Completed** means executed in this session with the result shown. **Proposed** means not
  executed. Hand calculations are labelled as such.

## 0. Findings in brief

1. **Baseline reproduced, with one gap.** A fresh clone of the pinned commit builds against the
   shared dependency tree (44 project modules compiled, exit 0, 128 s). All 49 blob hashes of the
   earlier manifest match. The handoff's vacuity probe compiles. The two upstream audit scripts
   (`scripts/check_layers.py`, `scripts/Audit.lean`) were **not executed**: the session's permission
   policy refused to run scripts from the freshly cloned repository. Independently written
   equivalents give the numbers the handoff records (43 files, 7 Spec, 3 Design; 35 claims; 532
   Spec/Design declarations; no findings) and extend the axiom check to all 1013 library constants.
2. **The inverter theorems are conditional theorems with real content.** They derive current
   margins, a slope bound, threshold crossing and a delay from the nodal ODE and the device
   inequalities. The toy witness discharges every hypothesis of the propagation theorem, for both
   output directions, at a single point of the hypothesis space (one initial state, one constant
   input, `V_DD^min = V_DD^max`, `C ≡ 1`, zero leakage, no disturbance). Upstream has no stand-alone
   instantiation of the contamination theorem; a probe written for this audit supplies one (§5.3).
3. **Rail invariance does not survive an additive disturbance.** The trajectory definition has no
   disturbance term, the proof's face inequality is exactly the passivity sign of the net current,
   and the conclusion is false for every disturbance bound `0 < ε ≤ 1` on the toy inverter
   (Lean-checked counterexample, §6.3).
4. **Existence is global on `[a, b]`** by one application of Mathlib's Picard–Lindelöf theorem. It
   rests on a globally Lipschitz, globally bounded vector field, which the toy device has by
   construction and an unclamped square law does not (§7).
5. **No licence.** The pinned repository contains no licence file and no licence or copyright
   notice (§10).
6. **Port.** About 100 lines of generic scalar analysis are reusable unchanged. Every
   circuit-specific result needs a new statement or proof. The netlist, contract and toy-device
   layers are outside the scope of the one-inverter model (§11).

## 1. Provenance and pinned artefacts

| Item | Value |
| --- | --- |
| Repository | `https://github.com/Deicyde/assembly-to-physics` (public; cloned over unauthenticated https with the user's git configuration disabled) |
| Commit | `7359bfe8266d06954e221f881403e7e83d5592f6`, the tip of `master` at clone time; history has 2 commits (`594b4fa`, `7359bfe`), both dated 2026-10-25 |
| Tracked files | 60: 43 library files under `AsmPhys/`, `AsmPhys.lean`, `scripts/Audit.lean`, `scripts/check_layers.py`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `README.md`, 8 files in `docs/`, `.github/workflows/ci.yml`, `.gitignore` |
| Toolchain | `leanprover/lean4:v4.35.0`; `lean --version`: `Lean (version 4.35.0, arm64-apple-darwin24.6.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`; `lake --version`: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)` |
| Mathlib | tag `v4.35.0`, revision `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Dependency pins | The clone's `lake-manifest.json` equals this repository's except for the top-level `"name"` (`AsmPhys` / `VoltageToBit`); all 9 package revisions are identical |
| Host | macOS 14.4, arm64 (Apple M3 Pro, 12 cores); git 2.48.1; Python 3.14.0 |

The dependency tree was not downloaded or copied. The clone's `.lake/packages` is a symbolic link
to `$W/voltage-to-bit/.lake/packages`. No file in that tree was modified by this session
(`find . -newer <clone>/lakefile.toml -type f` in the tree: 0 files). `lake update` and
`lake exe cache get` were never run.

## 2. Commands executed and observed results

Working directory is `$W/refs/assembly-to-physics` unless stated. All rows are completed checks
except rows 9 and 10.

| # | Command | Exit | Wall | Observed |
| --- | --- | --- | --- | --- |
| 1 | `GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 git clone https://github.com/Deicyde/assembly-to-physics.git "$W/refs/assembly-to-physics"` | 0 | < 1 s | 1.0 MB working copy |
| 2 | `git checkout --detach 7359bfe8266d06954e221f881403e7e83d5592f6`; `git rev-parse HEAD` | 0 | | `HEAD is now at 7359bfe …`; `7359bfe8266d06954e221f881403e7e83d5592f6` |
| 3 | `git fsck --full` | 0 | | no output |
| 4 | `python3 -I $W/refs/workstream-A/tools/cmp_hashes.py <source-hashes.json> <git ls-tree -r HEAD output> <clone> <earlier snapshot>` | 0 | < 1 s | `tree-vs-manifest: match=49 mismatch=0 missing=0`; `clone-worktree-vs-manifest (git hash-object): match=49 mismatch=0`; `snapshot-vs-manifest (git hash-object): match=49 mismatch=0 missing=0`; 11 tracked files are not in the manifest (`README.md`, 8 `docs/` files, CI workflow, `.gitignore`) |
| 5 | `diff lake-manifest.json "$W/voltage-to-bit/lake-manifest.json"` | 1 | | one differing line: `"name": "AsmPhys"` / `"name": "VoltageToBit"` |
| 6 | `mkdir -p .lake && ln -s "$W/voltage-to-bit/.lake/packages" .lake/packages` | 0 | | link created |
| 7 | `lake build --no-build +<each of the 24 Mathlib modules the project imports>` (dry check, builds nothing) | 0 | 3 s | `All targets up-to-date (2838 jobs).` |
| 8 | `lake build` (started 2026-11-09T20:23:45Z) | 0 | 128 s | `Build completed successfully (2884 jobs).` 44 lines `Built AsmPhys…` (43 library modules and the root); 0 dependency modules built; 0 errors; 30 warnings, all of the module-system kind (§13) |
| 9 | `python3 scripts/check_layers.py` | not run | | **Refused before execution**: `Permission for this action was denied by the Claude Code auto mode classifier. Reason: [Code from External].` |
| 10 | `lake env lean scripts/Audit.lean` | not run | | **Refused before execution**, same message |
| 11 | `lake env lean TrustBoundaryProbe.lean` (file content: the Lean block of handoff §8, saved verbatim; sha256 `873b6fd1…c38f`) | 0 | 15 s | `'emptyHold_contract' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| 12 | `lake env lean <earlier snapshot>/TrustBoundaryProbe.lean` (the previous session's file: same theorem plus six more `#print axioms`) | 0 | 9 s | 7 lines, each `… depends on axioms: [propext, Classical.choice, Quot.sound]`, for `Netlist.IsInverter.propagation`, `tgff_contract`, `SyncNet.refinement`, `end_to_end`, `Witness.inv_rises`, `Witness.toy_tgff_reachable`, `emptyHold_contract` |
| 13 | `python3 -I $W/refs/workstream-A/tools/indep_layers.py .` (independent static check, not the upstream script) | 0 | < 1 s | `library files under AsmPhys/: 43`; Spec 7, Design 3; all 43 imported by `AsmPhys.lean`; no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `bv_decide`, `#…` command, macro, notation, `instance` or non-`simp` attribute; no `theorem`/`lemma` in Spec or Design; Spec and Design import only Mathlib and inward. Two `deriving` clauses reported (`Spec/Circuit.lean:35`, `Spec/Device.lean:35`); the upstream rules do not forbid them |
| 14 | `lake env lean $W/refs/workstream-A/tools/IndepAudit.lean` (independent audit of the compiled environment, not the upstream script) | 0 | 31 s | 44 library modules (7 Spec, 3 Design); 1013 library constants (611 theorems, 314 definitions, 28 inductive types, 32 constructors, 28 recursors, 0 axioms, 0 opaque); `AsmPhys.Claims`: 35 theorems and nothing else; 532 constants in Spec and Design modules; no claim statement reaches a non-theorem library constant outside Spec/Design; no Spec/Design module imports outward; axioms reachable from all 1013 constants: `[Quot.sound, Classical.choice, propext]`; `Lean.collectAxioms` over the 35 claims: the same three |
| 15 | `lake env lean $W/refs/workstream-A/tools/IndepAuditNegControl.lean` (negative control for row 14) | 0 | | a `sorry` theorem is reported with `[sorryAx]`, a theorem using a fresh axiom with that axiom, `Claims.inverter_propagation` with the three standard axioms |
| 16 | `lake env lean $W/refs/workstream-A/tools/DepMap.lean`; `python3 -I …/import_closure.py . AsmPhys.Witness.ToyInverter …` | 0 | 22 s | dependency data used in §9 |
| 17 | `lake env lean $W/refs/workstream-A/probes/DisturbanceProbe.lean` (Appendix A) | 0 | 6 s | four theorems, each `depends on axioms: [propext, Classical.choice, Quot.sound]`; no warning |
| 18 | `lake env lean $W/refs/workstream-A/probes/ContaminationProbe.lean` (Appendix B) | 0 | 6 s | `'ContaminationProbe.toy_contamination' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| 19 | `lake env lean $W/refs/workstream-A/probes/MathlibRouteCheck.lean` (Mathlib only) | 0 | 75 s (machine busy; 6 s for an earlier two-example version) | no output: three `example`s compile (strict-face barrier from Mathlib's fencing lemma; inclusion trajectories as approximate solutions for Mathlib's Grönwall lemma; failure of invariance with a non-strict face imposed only inside the domain) |
| 20 | `lake env lean $W/refs/workstream-A/tools/FieldUse.lean` (which library declarations use which contract clause) | 0 | 25 s | uses outside the structure's own namespace: `FETContract.passive` 17, `.regular` 18, `.off_leak` 7, `.on_drive` 6, `.mono_d` 0, `.anti_s` 0, `.bounded` 3 (`IsInverter.contamination`, `IsInverter.contamination_rail`, `IsTG.abs_J_le_Imax`); no use of an eliminator; `Regular.lipschitz` by `Netlist.exists_abs_F_sub_F_le` (and by `Regular.continuous`), `Regular.bdd` by `FET.exists_abs_current_le` only |

Rows 9 and 10: both scripts were read in full before the attempt. `check_layers.py` imports only
`pathlib`, `re` and `sys`, reads the `.lean` files and prints. `Audit.lean` inspects the compiled
environment, reads the environment variable `AUDIT_DEPS`, and logs or throws. Neither opens a
network connection, starts a process or writes a file. They were nevertheless not executed, so
their output was **not observed** in this session. Rows 13–15 replace them with separately
written code; that is corroboration of the same properties, not a run of the upstream checks.

`lake build` elaborated and kernel-checked the project's own files. The dependency `.olean` files
were used as found in the shared tree. As in the previous session, this is not an independent
kernel replay of Mathlib.

## 3. Comparison with the handoff's record (§1 of `HANDOFF.md`)

| Handoff record | This session | Verdict |
| --- | --- | --- |
| Lean 4.35.0; Mathlib `v4.35.0` at `56a0058…` | identical | agrees |
| Blob hashes of 49 source/configuration files verified | 49 of 49 equal in the fresh clone's tree, in its working copy and in the earlier snapshot | agrees |
| Full project build succeeded | exit 0, 44 project modules compiled, no error | agrees |
| Layer check: 43 library files, 7 Spec, 3 Design, no failures | upstream script not executed; independent static check: 43, 7, 3, no violation of the upstream rules | consistent; upstream output not observed |
| Claims audit: 35 claims, 532 Spec/Design declarations, zero failures | upstream script not executed; independent audit: 35, 532, no finding on the four audit criteria | consistent; upstream output not observed |
| Inspected theorem dependencies use only `propext`, `Classical.choice`, `Quot.sound`; no project axiom or unfinished proof | true for the closure of all 1013 library constants; the library declares no axiom | agrees, on a wider set |
| Not an independent kernel replay of cached Mathlib | same limitation | unchanged |

No numerical discrepancy was found. Four clarifications:

- "43 library files" are the files under `AsmPhys/`. The build compiles 44 modules (those and the
  root `AsmPhys.lean`).
- "532 declarations" counts environment constants, including compiler-generated ones. By keyword
  count the sources of Spec have 62 declarations (39 `def`, 20 `structure`, 3 `inductive`) and
  those of Design have 41 (40 `def`, 1 `structure`). Of the 532 constants, 169 are theorems; all
  are compiler-generated, since Spec and Design contain no `theorem` or `lemma` keyword.
- The probe text in handoff §8 is a subset of the previous session's probe file, which adds a
  comment and six `#print axioms` commands. Both compile (rows 11, 12).
- The earlier manifest covers 49 of the 60 tracked files. The other 11 (documentation, CI
  workflow, `.gitignore`) are fixed by the commit hash but were not in that manifest.

## 4. Definitions (item 1)

All in the trusted layer `AsmPhys/Spec/`. Every quantity is a bare real number.

### 4.1 Trajectories and the node equation

A netlist has `n` state nodes and `m` boundary nodes (`Node`, `Spec/Circuit.lean:32-35`). Boundary
potentials are a prescribed waveform `u : ℝ → Fin m → ℝ`; the state is `e : ℝ → Fin n → ℝ`. The
net channel current into node `k` and the vector field (`Spec/Circuit.lean:83-85`, `:90-91`):

```lean
def F (u : Fin m → ℝ) (e : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i, ((if (N.fet i).s = .state k then (N.fet i).current u e else 0) -
    (if (N.fet i).d = .state k then (N.fet i).current u e else 0))

def vf (u : Fin m → ℝ) (e : Fin n → ℝ) : Fin n → ℝ :=
  fun k => N.F u e k / N.C k (e k)
```

A trajectory (`Spec/Circuit.lean:95-99`, docstrings dropped):

```lean
structure IsTrajOn (u : ℝ → Fin m → ℝ) (e : ℝ → Fin n → ℝ) (a b : ℝ) : Prop where
  continuousOn : ContinuousOn e (Icc a b)
  hasDerivWithinAt : ∀ t ∈ Ico a b, HasDerivWithinAt e (N.vf (u t) (e t)) (Ici t) t
```

- Derivative notion: the right derivative (`HasDerivWithinAt … (Ici t) t`) of the vector-valued
  function `e`, at **every** `t ∈ [a, b)`. There is no "almost everywhere" and no condition at `b`.
- Interval: a closed bounded interval `[a, b]`. Nothing is said about `e` outside it.
- Regularity: continuity on `[a, b]` and right differentiability on `[a, b)`. No further
  smoothness of `e`, and none of `u`, is part of the definition.
- The equation is exact: `C_k(e_k) · ė_k = F_k(u, e)`. There is no disturbance or error term.
- Sign convention: `I g d s` is the drain-to-source current and `F` is the net current into the
  node. For an inverter `F_out = −I_n(v_in, e_out, 0) − I_p(v_in, e_out, V_DD)`
  (`IsInverter.F_out`, `current_n`, `current_p`, `Cells/Inverter.lean:30-55`, with ground at `0`
  and the supply at `V_DD`); the pull-up current into the node is `−I_p`.

### 4.2 Device specification

A transistor is a record with polarity, parameters, a device function
`I : ℝ → ℝ → ℝ → ℝ` (channel current from drain to source at `(v_g, v_d, v_s)`) and three
terminals; there is no body terminal and no gate current (`FET`, `Spec/Circuit.lean:40-52`).
Devices enter the theorems only through inequalities (`Spec/Device.lean:53-114`, docstrings
dropped):

```lean
def gateDrive : Polarity → ℝ → ℝ → ℝ → ℝ
  | .n, g, d, s => g - min d s
  | .p, g, d, s => max d s - g

def onCond (pol : Polarity) (P : FETParams) (g d s : ℝ) : Prop :=
  P.Von ≤ gateDrive pol g d s

def offCond (pol : Polarity) (P : FETParams) (g d s : ℝ) : Prop :=
  gateDrive pol g d s ≤ P.Voff

def Passive (I : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ g d s, 0 ≤ (d - s) * I g d s

structure Regular (I : ℝ → ℝ → ℝ → ℝ) : Prop where
  lipschitz : ∃ L, LipschitzWith L (fun x : ℝ × ℝ × ℝ => I x.1 x.2.1 x.2.2)
  bdd : ∃ B, ∀ g d s, |I g d s| ≤ B

def BoundedOnRail (Imax Vmax : ℝ) (I : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ g d s, g ∈ Icc 0 Vmax → d ∈ Icc 0 Vmax → s ∈ Icc 0 Vmax → |I g d s| ≤ Imax

structure FETContract (pol : Polarity) (P : FETParams) (Vmax : ℝ)
    (I : ℝ → ℝ → ℝ → ℝ) : Prop where
  passive : Passive I
  regular : Regular I
  off_leak : ∀ g d s, d ∈ Icc 0 Vmax → s ∈ Icc 0 Vmax →
    offCond pol P g d s → |I g d s| ≤ P.Ioff
  on_drive : ∀ g d s, d ∈ Icc 0 Vmax → s ∈ Icc 0 Vmax →
    onCond pol P g d s → min (P.Gon * |d - s|) P.Isat ≤ |I g d s|
  mono_d : ∀ g s, Monotone fun d => I g d s
  anti_s : ∀ g d, Antitone fun s => I g d s
  bounded : BoundedOnRail P.Imax Vmax I

structure NodeCap (Cmin Cmax : ℝ) (C : ℝ → ℝ) : Prop where
  pos : 0 < Cmin
  range : ∀ v, C v ∈ Icc Cmin Cmax
  lipschitz : ∃ K, LipschitzWith K C
```

`FETParams` (`Spec/Device.lean:38-50`) has the fields `Von`, `Voff`, `Ioff`, `Gon`, `Isat`, `Imax`.
Facts that matter for reuse:

- C3, C4 and C6 are guarded by `d ∈ Icc 0 Vmax` and `s ∈ Icc 0 Vmax`. They say nothing when a
  channel terminal is off the rail `[0, Vmax]`. C1, C2 and C5 are global.
- For gate drives strictly between `Voff` and `Von` the contract gives only C1, C2, C5 and C6.
- C2 asks for a **global** Lipschitz constant and a **global** bound.
- No proof in the pinned library uses C5 (`mono_d`, `anti_s`). Checked on the compiled environment
  (§2 row 20): no library declaration mentions those two projections, a primitive projection of
  those fields, or an eliminator of `FETContract`. C5 is only proved, for the toy device.

### 4.3 Node capacitance

Each state node has a capacitance law `C : Fin n → ℝ → ℝ` with `C_pos : ∀ k v, 0 < C k v`
(`Netlist`, `Spec/Circuit.lean:55-63`). All capacitance is grounded and lumped per node. `NodeCap`
(quoted above) adds a range `[Cmin, Cmax]` with `0 < Cmin` and a Lipschitz law. The inverter
theorems use only the range of the output node's law; `NodeCap`'s Lipschitz clause is used by the
existence and uniqueness theorems.

### 4.4 Rails, levels, thresholds, parameters

The parameter sheet `Params` (`Spec/Params.lean:21-59`) has 19 fields: `VDDmin`, `VDDmax`, `VOL`,
`VIL`, `VIH`, `VOH`, `pn`, `pp`, and 11 fields for clock and flip-flop timing and a fidelity bound.
"The rail" is `Icc 0 V` with `V = V_DD` or `V_DD^max`. Logic levels are relations, not a decoder
(`Spec/Levels.lean:20-27`, docstrings dropped):

```lean
def validIn : Bool → ℝ → Prop
  | false, v => v ≤ S.VIL
  | true, v => S.VIH ≤ v

def validOut : Bool → ℝ → Prop
  | false, v => v ≤ S.VOL
  | true, v => S.VOH ≤ v
```

A voltage strictly between `VIL` and `VIH` satisfies neither `validIn false` nor `validIn true`,
and no voltage satisfies both under K0 (`Params.Consistent.not_validIn_both`,
`Cells/Levels.lean:28-32`). The level sets are half-lines: `validIn false v` holds for every
`v ≤ VIL`, however far below ground.

Derived quantities (`Spec/Params.lean:71-80`, `Spec/Cells.lean:47-56`, docstrings dropped):

```lean
def NML : ℝ := S.VIL - S.VOL

def NMH : ℝ := S.VOH - S.VIH

noncomputable def Irise : ℝ := min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat - S.pn.Ioff

noncomputable def Ifall : ℝ := min (S.pn.Gon * S.VOL) S.pn.Isat - S.pp.Ioff

noncomputable def tpdINV (S : Params) (Cmax : ℝ) : ℝ :=
  Cmax * max (S.VOH / S.Irise) ((S.VDDmax - S.VOL) / S.Ifall)

noncomputable def tcdINV (S : Params) (Cmin : ℝ) : ℝ :=
  min S.NML S.NMH * Cmin / (2 * max S.pn.Imax S.pp.Imax)
```

The consistency conditions `Params.Consistent` (`Spec/Params.lean:89-129`) are K0–K14. The
inverter proofs use K0–K6 and K13 (docstrings dropped; the `-- … omitted` lines are editorial; K7,
K8, K10–K12 and K14 concern the noise budget, clocking and stacks):

```lean
structure Consistent : Prop where
  K0 : 0 < S.VOL ∧ S.VOL < S.VIL ∧ S.VIL < S.VIH ∧ S.VIH < S.VOH ∧ S.VOH < S.VDDmin
  K1 : S.VIL ≤ S.pn.Voff
  K2 : S.pp.Von ≤ S.VDDmin - S.VIL
  K3 : S.pn.Von ≤ S.VIH
  K4 : S.VDDmax - S.VIH ≤ S.pp.Voff
  K5 : S.pn.Ioff < min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat
  K6 : S.pp.Ioff < min (S.pn.Gon * S.VOL) S.pn.Isat
  -- K7, K8 omitted
  K9n : S.pn.Voff < S.pn.Von
  K9p : S.pp.Voff < S.pp.Von
  -- K10, K11, K12 omitted
  K13_leak : 0 ≤ S.pn.Ioff ∧ 0 ≤ S.pp.Ioff
  K13_drive : min (S.pn.Gon * S.VDDmax) S.pn.Isat ≤ S.pn.Imax ∧
    min (S.pp.Gon * S.VDDmax) S.pp.Isat ≤ S.pp.Imax
  K13_supply : S.VDDmin ≤ S.VDDmax
  -- K14 omitted
```

The inverter topology is the predicate `Netlist.IsInverter N inp out gnd vdd iN iP`
(`Spec/Cells.lean:32-43`): two distinct transistors, `iN` of n-type and `iP` of p-type, both gated
by `inp`, both with drain at the state node `out`, with sources at the boundary nodes `gnd` and
`vdd`, and no other transistor with a channel terminal at `out`.

### 4.5 Units

The Lean sources carry no units: every quantity is `ℝ`, and no physical unit is named anywhere in
them. The embedded specification states "Voltages are in volts, currents in amperes, times in
seconds" (`docs/HANDOFF-2026-10-24.md:187`) and gives the working rule "Keep the core
dimensionless: plain ℝ, with V_DD = 1 or explicit SI constants, and no units library"
(`docs/HANDOFF-2026-10-24.md:33`). The toy numbers (`V_DD = 1`, `C = 1`, `G_on = I_sat = 1`, delay
9) are dimensionless. They are not labelled as normalized in the Lean identifiers; the only hint
is the phrase "unit output capacitance" in comments.

## 5. Inverter propagation and contamination (item 2)

### 5.1 Propagation: `Netlist.IsInverter.propagation`

`Cells/Inverter.lean:158-172`, restated as `Claims.inverter_propagation` (`Claims.lean:213-229`):

```lean
theorem propagation {S : Params} (hS : S.Consistent)                 -- THM (norm_num)
    (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {Cmin Cmax : ℝ} (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax)          -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (he : N.IsTrajOn u e t₀ t₁)
    (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)                          -- ENV
    {x : Bool} (hin : ∀ t ∈ Icc t₀ t₁, S.validIn x (pot (u t) (e t) inp))
    (h0 : e t₀ out ∈ Icc 0 VDD) :
    (∀ t ∈ Icc (t₀ + S.tpdINV Cmax) t₁, S.validOut (!x) (e t out)) ∧
      ∀ t₂ ∈ Icc t₀ t₁, S.validOut (!x) (e t₂ out) →
        ∀ t ∈ Icc t₂ t₁, S.validOut (!x) (e t out) := by
```

Proof outline (`Cells/Inverter.lean:173-240`):

1. Output stays in `[0, V_DD]`: `out_mem_rails` (`:59-83`), from C1, C2, ideal rails and `h0`.
2. Current margin while the output is on the wrong side of the threshold: `Irise_le_F_out`
   (`:87-118`: n-FET off by K1 and C3, p-FET on by K2 and C4, K5) and `F_out_le_neg_Ifall`
   (`:123-153`). Both require the output on the rail (`hout : e out ∈ Icc 0 S.VOH`, resp.
   `Icc S.VOL VDD`).
3. Slope bound `I_rise / C_max ≤ ė_out` by dividing by the capacitance (`:187-189`; the step
   needs the margin to be nonnegative).
4. Crossing and persistence by the scalar lemmas `reach_of_deriv_right_ge` and
   `barrier_of_deriv_right_nonneg` (`Circuit/Rails.lean:498-519`, `:461-471`).

Hypotheses. D = definitional predicate on the claim's own objects. T = provable elsewhere in the
library under further assumptions. A = assumption (model, measurement or environment).

| Hypothesis | Meaning | Kind | Toy witness |
| --- | --- | --- | --- |
| `hS : S.Consistent` | K0–K14 on the sheet's numbers | A on parameters; a finite numeric check | discharged: `Witness.sheet_consistent` (`Witness/Toy.lean:16-17`, by `norm_num`) |
| `hinv : N.IsInverter …` | two-transistor topology, no other channel at the output | D | discharged: `Witness.inv_isInverter` (`Witness/ToyInverter.lean:20-33`) |
| `hn`, `hp : FETContract …` | device inequalities C1–C6 for both devices (C1, C2, C3, C4 are used; C5, C6 are not) | A (device model) | discharged: `Witness.toy_contract` (`Witness/Toy.lean:20-22`) via `dev_contract` (`Witness/Devices.lean:229-247`) |
| `hcap` | output capacitance law in `[Cmin, Cmax]` (only the upper bound is used) | A | discharged: `C ≡ 1 ∈ [1, 1]` |
| `hVDD` | `V_DD ∈ [V_DD^min, V_DD^max]` | A (environment) | discharged: `1 ∈ [1, 1]` |
| `he : N.IsTrajOn u e t₀ t₁` | `e` solves the nodal ODE on `[t₀, t₁]` | T: existence by `exists_isTrajOn` under C2, `NodeCap` and continuous `u` (§7) | discharged: from `exists_isTrajOn` (`Witness/ToyInverter.lean:50-52`, `:93-95`) |
| `hgnd`, `hvdd` | ground pin exactly `0`, supply pin exactly `V_DD` on `[t₀, t₁]` | A (environment) | discharged: constant waveform, by `rfl` |
| `hin` | the input is a valid `x` at every time of `[t₀, t₁]` | A (environment or upstream stage) | discharged: input constantly `0` (rise) or `1` (fall) |
| `h0` | initial output in `[0, V_DD]` | A (initial state) | discharged: `e 0 = 0` (rise), `e 0 = 1` (fall) |

Derived inside the proof, not assumed: rail membership of the output, `0 < Cmax`, positivity of
`Irise` and `Ifall`, the current margins, the slope bound.

Witnesses (`Witness/ToyInverter.lean:47-49`, `:90-92`; restated in `Claims.lean:458-468`):

```lean
theorem inv_rises : ∃ e : ℝ → Fin 1 → ℝ,
    inv.IsTrajOn (fun _ => ![0, 1, 0]) e 0 20 ∧ e 0 = 0 ∧
      ∀ t ∈ Icc 9 20, sheet.validOut true (e t 0) := by

theorem inv_falls : ∃ e : ℝ → Fin 1 → ℝ,
    inv.IsTrajOn (fun _ => ![0, 1, 1]) e 0 20 ∧ e 0 = 1 ∧
      ∀ t ∈ Icc 9 20, sheet.validOut false (e t 0) := by
```

`Witness.inv_propagation_hypotheses` (`Witness/ToyInverter.lean:71-79`) states the eleven
hypotheses as one conjunction for the low-input case. Limits of these witnesses:

- One point of the hypothesis space: a single initial state, a constant input, a degenerate
  supply range and capacitance range, `I_off = 0`, no disturbance.
- The observation window `[9, 20]` has positive length. In general conclusion (a) quantifies over
  `Icc (t₀ + t_pd) t₁`, which is empty when `t₁ − t₀ < t_pd`.
- The proved delay is conservative for the toy. Hand calculation, not Lean-checked: with the input
  at `0` the toy output obeys `ė = 1 − e`, so from `0` it reaches `V_OH = 0.9` at `ln 10 ≈ 2.30`;
  the theorem gives `9`.

### 5.2 Contamination: `Netlist.IsInverter.contamination`

`Cells/Inverter.lean:243-256`, restated as `Claims.inverter_contamination` (`Claims.lean:233-248`):

```lean
theorem contamination {S : Params} (hS : S.Consistent)               -- THM (norm_num)
    (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {Cmin Cmax : ℝ} (hCmin : 0 < Cmin)                               -- MEAS
    (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax)                          -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₁ t₂ : ℝ}
    (he : N.IsTrajOn u e t₁ t₂)
    (hgnd : ∀ t ∈ Icc t₁ t₂, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₁ t₂, u t vdd = VDD)                          -- ENV
    (hin : ∀ t ∈ Icc t₁ t₂, pot (u t) (e t) inp ∈ Icc 0 S.VDDmax)
    {b : Bool} (h1 : S.validOut b (e t₁ out)) (hrail : e t₁ out ∈ Icc 0 VDD) :
    ∀ t ∈ Icc t₁ (min t₂ (t₁ + S.tcdINV Cmin)), S.validIn b (e t out) := by
```

Proof outline (`:257-306`): rails by `out_mem_rails`; `|F_out| ≤ 2·max(I_max^n, I_max^p)` from C6,
which needs gate, drain and source on the rail; `|ė_out| ≤ 2·I_max / C_min`; then the mean-value
inequality `norm_image_sub_le_of_norm_deriv_right_le_segment` (Mathlib) bounds the movement by
`min(NM_L, NM_H)` within `t_cd`.

| Hypothesis | Meaning | Kind |
| --- | --- | --- |
| `hS`, `hinv`, `hn`, `hp`, `hVDD`, `he`, `hgnd`, `hvdd` | as in §5.1 (here C1, C2 and C6 are the clauses used) | as in §5.1 |
| `hCmin : 0 < Cmin`, `hcap` | capacitance range with a positive lower bound (the lower bound is the one used) | A |
| `hin` | the input stays in `[0, V_DD^max]`; it may otherwise do anything | A (environment) |
| `h1` | the output is a valid `b` at `t₁` | A (state at `t₁`; supplied by propagation in compositions) |
| `hrail` | the output is in `[0, V_DD]` at `t₁` | A (state at `t₁`) |

### 5.3 Is contamination instantiated concretely?

Not on the stand-alone toy inverter. In the pinned commit `IsInverter.contamination` is used only
by `IsInverter.behaves` (`Cells/InverterCell.lean:70`) and by the restatement in `Claims.lean:248`.
Its variant `contamination_rail` (`Cells/InverterCore.lean:322-383`) is used in the flip-flop
capture proof through `contamination_chain3` (`Cells/TGFFCapture.lean:231`), which is out of scope
here.
`Claims.lean:423` records that `keeper_hold`, THM L3.4 and THM L4.1 have no witness.

Completed check for this audit (Appendix B, §2 row 18): for the toy inverter started at `0`, with
the input at `0` until `t = 9` and then ramping continuously to `1` at `t = 9.1`, every hypothesis
of `contamination` holds on `[9, 20]`, the output is a valid `1` at `t = 9`, and it remains a valid
high **input** level on `[9, 9.1]`, the interval in which the input swings from valid low to valid
high. Statement:

```lean
theorem toy_contamination :
    ∃ e : ℝ → Fin 1 → ℝ, inv.IsTrajOn u e 0 20 ∧ e 0 = 0 ∧
      sheet.validIn false (u 9 2) ∧ sheet.validIn true (u 9.1 2) ∧
      sheet.validOut true (e 9 0) ∧
      ∀ t ∈ Icc (9 : ℝ) (9 + 1 / 10), sheet.validIn true (e t 0)
```

### 5.4 Evidence status of the old inverter result

| Dimension (handoff §3) | Status at the pinned commit |
| --- | --- |
| Formal correctness | Statements quoted above. Builds from a fresh clone. Standard axioms only. Project files kernel-checked during the build; cached Mathlib not replayed. |
| Applicability | Propagation: concrete toy instance for both directions, at one point of the hypothesis space, with a nonempty window. Contamination: no upstream instance; one added here. |
| Physical evidence | None in the repository. The device law is a constructed clamp function (§8), the clauses tagged MEAS and MODEL carry no data, and the numbers are dimensionless. |

## 6. Rail invariance and an additive disturbance (item 3)

### 6.1 Statements

Global form, `Circuit/Rails.lean:179-186` (restated `Claims.lean:84-92`):

```lean
theorem rail_invariance
    (hpass : ∀ i, Passive (N.fet i).I)                     -- MODEL (C1)
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b V : ℝ}
    (he : N.IsTrajOn u e a b)
    (hu : ∀ j, N.TouchesChannel j → ∀ t ∈ Icc a b, u t j ∈ Icc 0 V)   -- ENV
    (h0 : ∀ k, e a k ∈ Icc 0 V) :
    ∀ t ∈ Icc a b, ∀ k, e t k ∈ Icc 0 V := by
```

Local forms: `rail_invariance_set` (`Circuit/Rails.lean:360-373`) and `rail_invariance_node`
(`:424-437`). The inverter's use, `Cells/Inverter.lean:59-68`:

```lean
theorem out_mem_rails (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hpn : Passive (N.fet iN).I) (hrn : Regular (N.fet iN).I)         -- MODEL (C1, C2)
    (hpp : Passive (N.fet iP).I) (hrp : Regular (N.fet iP).I)         -- MODEL (C1, C2)
    {VDD : ℝ} (hVDD : 0 ≤ VDD)                                       -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (he : N.IsTrajOn u e t₀ t₁)
    (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)                          -- ENV
    (h0 : e t₀ out ∈ Icc 0 VDD) :
    ∀ t ∈ Icc t₀ t₁, e t out ∈ Icc 0 VDD := by
```

All of them rest on one generic lemma, `Circuit/Rails.lean:59-64`:

```lean
theorem max_principle {ι : Type*} [Fintype ι] {x x' : ℝ → ι → ℝ} {a b V : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (x' t) (Ici t) t)
    (ha : ∀ k, x a k ≤ V)
    (hface : ∀ t ∈ Ico a b, ∀ k, V ≤ x t k → (∀ j, x t j ≤ x t k) → x' t k ≤ 0) :
    ∀ t ∈ Icc a b, ∀ k, x t k ≤ V := by
```

### 6.2 What breaks when `C ė = F + w(t)` with `|w| ≤ ε`

1. **The trajectory hypothesis cannot be supplied.** `IsTrajOn` fixes the derivative to
   `N.vf (u t) (e t) = F / C` (§4.1). A solution of the disturbed equation is not an `IsTrajOn`
   trajectory unless `w ≡ 0`. Every old theorem with a hypothesis `he : N.IsTrajOn …` (rail
   invariance, propagation, contamination, the slew bounds) is silent about disturbed trajectories.
2. **The disturbance cannot be hidden in the netlist.** Device functions are time-independent
   functions of `(v_g, v_d, v_s)`, and rail invariance requires every device to be `Passive`
   (`0 ≤ (d - s) * I g d s`), from which `Passive.apply_self` derives `I g v v = 0`
   (`Circuit/Rails.lean:28-38`). A current source satisfies neither.
3. **The face inequality is unprovable and false.** `rail_invariance` applies `max_principle` once
   per face. The hypothesis `hface` (right derivative `≤ 0` whenever the node is the largest and at
   least `V`) is discharged at `Circuit/Rails.lean:201-206` by `F_nonpos_of_terminals_le`, the sign
   of `F` given by passivity, and `C_pos`; the lower face is `:193-200`, and the same two steps
   appear in `rail_invariance_set` (`:382-418`). With the disturbed derivative the needed
   inequality is `F + w ≤ 0`. Passivity gives only `F ≤ 0`, with equality whenever every channel
   neighbour is at the node's potential (for example an inverter output sitting on the supply rail
   with the input low). So `F + w = w > 0` there.
4. **The conclusion itself fails** (§6.3).
5. **Knock-on effect.** Once the output is off the rail, C3, C4 and C6 no longer apply (§4.2).
   `Irise_le_F_out`, `F_out_le_neg_Ifall` and the contamination slew bound all take rail membership
   of the output as a premise, so the old delay argument loses its inputs, not only its invariant.

What survives unchanged: `max_principle` and the scalar barrier/reach lemmas. They are stated for
arbitrary right-derivative data `x'`, `g'` and do not mention the ODE.

### 6.3 Counterexample (completed check)

Appendix A, §2 row 17, compiled against the pinned library. Setting: the toy inverter, ground `0`,
supply `1`, input held at `0`, unit capacitance, output started on the upper rail, constant
disturbance `w ≡ ε`. The file defines the disturbed trajectory notion (the old `IsTrajOn` with `w`
added) and proves:

```lean
theorem toy_F_above_rail {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 2) :
    inv.F ![0, 1, 0] (fun _ => v) 0 = -(v - 1)

theorem toy_old_hypotheses :
    (∀ i, Passive (inv.fet i).I) ∧ (∀ i, Regular (inv.fet i).I) ∧
      ∀ j : Fin 3, (![0, 1, 0] : Fin 3 → ℝ) j ∈ Icc (0 : ℝ) 1

theorem toy_rail_invariance_fails {ε b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b) :
    ∃ (w : ℝ → ℝ) (e : ℝ → Fin 1 → ℝ),
      (∀ t, |w t| ≤ ε) ∧ IsDisturbedTraj (fun _ => ![0, 1, 0]) w e 0 b ∧
      e 0 0 ∈ Icc (0 : ℝ) 1 ∧ ¬ ∀ t ∈ Icc 0 b, e t 0 ∈ Icc (0 : ℝ) 1
```

The witness is `e(t) = 1 + ε·(1 − exp(−t))`, which is above the rail for every `t > 0`. So for
every `ε ∈ (0, 1]` and every horizon, all remaining hypotheses of the old theorem hold and its
conclusion is false.

Hand remarks, not Lean-checked. In this configuration the excursion stays below `ε / G_on = ε`,
because the toy p-device conducts in reverse with conductance `G_on` above the rail. For
`ε > I_sat = 1` the same configuration has `ė ≥ ε − 1 > 0` for all `e ≥ 1`, because the toy channel
current saturates: no bounded set is invariant. The size of an invariant domain is therefore tied
to the reverse-conduction law of the device, about which the old contract is silent off the rail.

### 6.4 What a replacement needs (proposed, not done here)

For a domain `[V_lo, V_hi]` and the inclusion `|c·v' − I_net(u, v)| ≤ ε` the face conditions are
`I_net(u, V_hi) ≤ −ε` and `I_net(u, V_lo) ≥ ε` for every admitted input value and parameter choice,
derived from the explicit device law. If the inclusion is required only while `v` is in the domain
(as in `docs/interface.md` §4), these must be **strict**: with equality, a trajectory can rest
on the face with zero slope and then leave, since nothing constrains it outside. The abstract form
of this is Lean-checked (§2 row 19, third example: `v t = t * t` meets a non-strict face condition
imposed only while `v ≤ 0`, and leaves that domain); its transfer to the circuit model is a hand
argument. With strict faces the scalar statement is an instance of Mathlib's
`image_le_of_deriv_right_lt_deriv_boundary` (`Mathlib/Analysis/Calculus/MeanValue.lean:183`;
§2 row 19, first example). The old `max_principle` accepts a non-strict face but needs the slope
condition wherever the state is at or beyond the face, which is what a clamped vector field
provides.

## 7. Existence of trajectories (item 4)

Statement, `Circuit/WellPosed.lean:46-52` (restated `Claims.lean:62-69`):

```lean
theorem exists_isTrajOn {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k))        -- MEAS range, MODEL Lipschitz law
    {u : ℝ → Fin m → ℝ} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b))                        -- ENV
    (hab : a ≤ b) (e₀ : Fin n → ℝ) :
    ∃ e, N.IsTrajOn u e a b ∧ e a = e₀ := by
```

The proof instantiates Mathlib's Picard–Lindelöf record directly on the whole interval
(`Circuit/WellPosed.lean:53-65`):

```lean
  obtain ⟨K, hKe, hKu⟩ := N.exists_lipschitzWith_vf hreg hcap
  obtain ⟨B, hB⟩ := N.exists_norm_vf_le hreg hcap
  have hPL : IsPicardLindelof (fun t => N.vf (u t)) (⟨a, left_mem_Icc.2 hab⟩ : Icc a b) e₀
      (B * (b - a).toNNReal) 0 B K :=
    { lipschitzOnWith := fun t _ => (hKe (u t)).lipschitzOnWith
      continuousOn := fun x _ => (hKu x).continuous.comp_continuousOn hu
      norm_le := fun t _ x _ => hB (u t) x
      mul_max_le := by
        have h1 : ((B * (b - a).toNNReal : ℝ≥0) : ℝ) = B * (b - a) := by
          rw [NNReal.coe_mul, Real.coe_toNNReal _ (sub_nonneg.2 hab)]
        have h2 : max (b - a) (a - a) = b - a := max_eq_left (by linarith)
        simp only [h1, h2, NNReal.coe_zero, sub_zero, le_refl] }
  obtain ⟨e, he0, he⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
```

- Mathlib API at the pinned revision: the structure `IsPicardLindelof f t₀ x₀ a r L K`
  (`Mathlib/Analysis/ODE/PicardLindelof.lean:80-89`: Lipschitz in the state on a closed ball,
  continuous in time for each state, norm bound `L`, and `L * max (tmax - t₀) (t₀ - tmin) ≤ a - r`),
  and `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`
  (`Mathlib/Analysis/ODE/ExistUnique.lean:71-75`). Uniqueness (`isTrajOn_unique`,
  `Circuit/WellPosed.lean:72-81`) uses `ODE_solution_unique_of_mem_Icc_right`
  (`Mathlib/Analysis/ODE/ExistUnique.lean:194`); continuous dependence uses
  `dist_le_of_approx_trajectories_ODE` (`Mathlib/Analysis/ODE/Gronwall.lean:188`).
- **Global in time on the given compact interval, for every initial state.** The field is
  globally bounded by `B` and globally Lipschitz with one constant `K`
  (`exists_norm_vf_le`, `exists_lipschitzWith_vf`, `Circuit/Field.lean:175-189`, `:161-171`).
  Choosing the ball radius `B·(b − a)` makes the validity condition an equality, so one application
  covers `[a, b]`. There is no continuation argument and no maximal solution.
- The Mathlib solution has a derivative within `Icc a b` at every point of `[a, b]`; the proof
  converts it to the right-derivative form on `[a, b)` (`:66-68`).

Gaps relative to the new target:

| Gap | Fact |
| --- | --- |
| Global Lipschitz and bound | Come from C2 (`Regular`) and `NodeCap`. The toy clamp device has them by construction (`dev_regular`, `Witness/Devices.lean:141-169`). An unclamped square law has neither, so `exists_isTrajOn` cannot be instantiated for it. |
| Time regularity | `ContinuousOn u (Icc a b)` is required. Discontinuous inputs are covered by the universally quantified theorems (which take a trajectory as a hypothesis) but not by the existence theorem. The pinned Mathlib's `Analysis/ODE` has Picard–Lindelöf and `C¹` variants only; no existence theorem for merely measurable right-hand sides was found. |
| Disturbance | The field depends on time only through `u`. A disturbance `w(t)` must be continuous to fit `IsPicardLindelof.continuousOn`. |
| What the witnesses use | Constant waveforms, the interval `[0, 20]`, initial states `0` and `1` (`Witness/ToyInverter.lean:50-52`, `:93-95`). |
| Outside `[a, b]` | The solution is a total function constrained only on `[a, b]`. |

## 8. The toy device (item 5)

`Design/Toy.lean:30-39` (docstrings dropped) with `gateDrive` from §4.2:

```lean
noncomputable def ramp (P : FETParams) (x : ℝ) : ℝ :=
  max 0 (min 1 ((x - P.Voff) / (P.Von - P.Voff)))

noncomputable def chan (P : FETParams) (x : ℝ) : ℝ :=
  max (-P.Isat) (min P.Isat (P.Gon * x))

noncomputable def dev (pol : Polarity) (P : FETParams) (g d s : ℝ) : ℝ :=
  ramp P (gateDrive pol g d s) * chan P (d - s)
```

So `I(g, d, s) = clamp((x − V_off)/(V_on − V_off), 0, 1) · clamp(G_on·(d − s), −I_sat, I_sat)`
with `x = g − min(d, s)` for the n-device and `x = max(d, s) − g` for the p-device. Parameters and
netlist (`Design/Toy.lean:42-58`, `:91-95`): `V_on = 0.55`, `V_off = 0.3`, `I_off = 0`,
`G_on = I_sat = I_max = 1` for both polarities; `V_DD^min = V_DD^max = 1`; `V_OL, V_IL, V_IH, V_OH =
0.1, 0.3, 0.7, 0.9`; one state node with `C ≡ 1`; boundary nodes ground `0`, supply `1`, input `2`.
On this sheet `I_rise = I_fall = 0.1`, `t_pd(1) = 9` (`Witness.sheet_tpdINV`,
`Witness/ToyInverter.lean:42-43`) and `t_cd(c) = c/10` (`Witness.sheet_tcdINV`,
`Witness/ToyFlipFlop.lean:43-44`).

Why it is "deliberately constructed":

- It is assembled from the contract's own parameters so that each clause holds by construction:
  zero current when the gate drive is at most `V_off` (C3 with `I_off = 0`), and
  `|I| = min(G_on·|d − s|, I_sat)` exactly when the gate drive is at least `V_on` (C4 with
  equality); see `dev_contract`, `Witness/Devices.lean:229-247`.
- It is a gated, saturating resistor: the on-current does not depend on the overdrive, there is no
  square-law region, no subthreshold conduction and no dependence on anything but the three
  terminal voltages.
- It is globally Lipschitz and globally bounded (`dev_regular`), which is what the existence
  theorem requires.
- `Params.Consistent.exists_fetContract` (`Witness/Devices.lean:250-259`) shows that every sheet
  satisfying K0–K14 admits such devices. That is a non-vacuity statement about the contract, not
  evidence about a manufactured transistor.

## 9. Dependency map (item 6)

Import closure of the toy inverter witness: 17 project files, 2509 lines (two of them,
`Design/Latch.lean` and `Design/TGFF.lean`, are flip-flop definitions pulled in only by file-level
imports; no inverter declaration uses them).

```text
Spec/Device -> Spec/Params -> Spec/Levels -> Spec/Cells
Spec/Device -> Spec/Circuit -> Spec/Cells
Spec/Circuit -> Circuit/Basic -> Circuit/Rails
Circuit/Basic -> Circuit/Field -> Circuit/WellPosed
{Spec/Cells, Cells/Levels, Circuit/Rails} -> Cells/Inverter -> {Cells/InverterCore, Cells/InverterCell} -> Cells/Chain
Design/Toy -> Witness/Devices -> Witness/Toy
{Witness/Toy, Cells/Inverter, Circuit/WellPosed} -> Witness/ToyInverter -> Claims
```

| File | Lines | Role for the inverter results |
| --- | --- | --- |
| `Spec/Device.lean` | 116 | device inequalities, `NodeCap` |
| `Spec/Circuit.lean` | 120 | netlist, `F`, `vf`, `IsTrajOn` |
| `Spec/Params.lean` | 133 | sheet, K0–K14, `Irise`, `Ifall` |
| `Spec/Levels.lean` | 31 | `validIn`, `validOut` |
| `Spec/Cells.lean` | 181 | `IsInverter`, `tpdINV`, `tcdINV` (rest: cells and DAGs, unused here) |
| `Circuit/Basic.lean` | 19 | `pot` simp lemmas |
| `Circuit/Rails.lean` | 533 | `max_principle`, passivity sign lemmas, rail invariance, slew bounds, scalar barrier/reach lemmas |
| `Circuit/Field.lean` | 193 | global Lipschitz and bound of `vf` (existence only) |
| `Circuit/WellPosed.lean` | 127 | existence, uniqueness, Grönwall dependence |
| `Cells/Levels.lean` | 54 | `validIn_of_validOut`, `not_validIn_both` (imports `Design/Latch.lean`, 50 lines) |
| `Cells/Inverter.lean` | 310 | `F_out`, `out_mem_rails`, margins, `propagation`, `contamination` |
| `Cells/InverterCore.lean` | 387 | inverter with side channels: `propagation_side`, `tpdSide`, `propagation_rail`, `contamination_rail` (imports `Circuit/Inflow.lean`, 84 lines) |
| `Cells/InverterCell.lean` | 76 | `behaves` (imports `Cells/Compose.lean`, 128 lines) |
| `Cells/Chain.lean` | 112 | three-inverter contamination chain |
| `Design/Toy.lean` | 114 | toy device, sheet, inverter (imports `Design/TGFF.lean`, 134 lines) |
| `Witness/Devices.lean` | 265 | the clamp device meets C1–C6 |
| `Witness/Toy.lean` | 24 | `sheet_consistent`, `toy_contract` |
| `Witness/ToyInverter.lean` | 105 | `inv_rises`, `inv_falls`, `inv_propagation_hypotheses` |
| `Claims.lean` | 531 | restatements; inverter-related entries at `:62-79`, `:84-131`, `:136-202`, `:213-267`, `:432-468` |

Declaration-level dependencies, computed from the compiled environment (§2 row 16;
`$W/refs/workstream-A/logs/depmap.log`):

| Result | Library lemmas it uses (definitions omitted) | Mathlib lemmas of note |
| --- | --- | --- |
| `max_principle` | none | `IsClosed.Icc_subset_of_forall_exists_gt`, `HasDerivWithinAt.limsup_slope_le'` |
| `reach_of_deriv_right_ge` | `max_principle`, `barrier_of_deriv_right_nonneg`, `linear_rise_of_deriv_right_ge` | as above |
| `rail_invariance_node`, `out_mem_rails` | `max_principle`, `rail_invariance_set`, `F_nonneg_of_le_neighbours`, `F_nonpos_of_neighbours_le`, `Passive.apply_self`, `Passive.nonneg_of_le`, `Passive.nonpos_of_le`, `Regular.continuous` | as above |
| `propagation` | the previous row, `F_out`, `current_n`, `current_p`, `Irise_le_F_out`, `F_out_le_neg_Ifall`, the scalar reach lemmas | as above |
| `contamination` | `out_mem_rails` and its dependencies, `F_out`, `current_n`, `current_p` | plus `norm_image_sub_le_of_norm_deriv_right_le_segment` |
| `exists_isTrajOn` | 10 lemmas of `Circuit/Field.lean` | `IsPicardLindelof`, `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` |
| `Witness.inv_rises`, `inv_falls` | `propagation` and `exists_isTrajOn` with their dependencies, 23 lemmas of `Witness/Devices.lean`, `sheet_consistent`, `toy_contract`, `inv_isInverter`, `inv_regular`, `sheet_tpdINV` | both sets |

`propagation` and `contamination` do not depend on `Circuit/Field.lean`, `Circuit/WellPosed.lean`,
`Circuit/Tube.lean`, `Circuit/Charge.lean`, `Circuit/Inflow.lean`, `Circuit/Lyapunov.lean` or
`Circuit/Tellegen.lean`.

## 10. Reuse terms (item 7)

Facts at the pinned commit:

- There is no `LICENSE`, `COPYING` or `NOTICE` file, in either commit of the history
  (`git log --all --name-only`, 60 and 44 tracked files).
- No tracked file contains a licence statement, a copyright notice or an SPDX identifier
  (`git grep -i -E 'licen[sc]e|copyright|spdx|all rights reserved'`: the only matches are two lines
  of `docs/HANDOFF-2026-10-24.md`, `:90` and `:708`, about a third-party Lean development that is
  described as GPL-3.0-only and as "a possible starting point for L0").
- The L0 work that sentence refers to is not started (`docs/STATUS.md:27`), and no Lean source
  credits or mentions third-party code. `docs/STATUS.md:72-73` lists "licensing for L0" among open
  owner decisions.
- `README.md` has no licence section.
- Both commits carry the same author and committer identity
  (`git log --all --format='%an | %cn'`).
- Mathlib, the only direct dependency, is under Apache 2.0 (`LICENSE` in the package). The new
  development depends on it and copies nothing from it.
- As seen during this audit, this repository (`voltage-to-bit`) has no licence file either.

Implications (stated as facts about the default situation, not as legal advice, and without
assuming anything about the owner's intent):

- With no licence, the repository's text is under default copyright. Publishing it on a hosting
  site does not by itself give others permission to copy it into another project.
- Copying Lean text from it into `voltage-to-bit` therefore needs either a licence added to the
  old repository or an explicit permission from its copyright holder. If the owner of this project
  holds that copyright (the audit cannot establish this), the owner can settle the matter directly.
- Whatever is decided, copied text should carry its provenance: repository URL, commit
  `7359bfe8266d06954e221f881403e7e83d5592f6`, file and line range, the author as recorded in the
  commit metadata, and a note of any modification.
- Re-deriving a result from Mathlib with a newly written proof copies no text. Mathematical
  statements and proof ideas are not what a licence governs; the candidates marked "reusable
  unchanged" in §11 are short enough to be re-derived.

## 11. Minimal port proposal (item 8)

Target: `docs/interface.md` as read at DRAFT v0 (2026-11-09, 15:49 local time): a scalar
differential inclusion `|c·v' − I_net(u, v; θ)| ≤ ε_I` required while `v ∈ [V_lo, V_hi]`,
`c ∈ [C_min, C_max]`, symmetric square-law devices, a parameter box, a safe domain containing
`[0, VDD]` whose invariance is to be proved, right-derivative trajectories on `[a, b]`, existence
by Picard–Lindelöf on a clamped field. The interface was revised to "v1 candidate" at 16:06 while
this audit was being written; the trajectory definition in its §4, which this section relies on,
reads the same in both versions. The interface is not frozen.

### 11.1 Classification

| # | Old result | Location, size | Class | Reason and recommendation |
| --- | --- | --- | --- | --- |
| 1 | `max_principle` | `Circuit/Rails.lean:59-103`, 45 lines | reusable unchanged | Generic: a finite family of right-differentiable functions and a non-strict face condition required wherever a component is the largest and at least `V`. For one node take `ι := Unit`. Needed only where a face is non-strict and the slope bound holds beyond the face (a clamped field). Under the interface's §4 the faces must be strict (§6.4) and Mathlib suffices. |
| 2 | `barrier_of_deriv_right_nonneg`, `linear_rise_of_deriv_right_ge`, `reach_of_deriv_right_ge` | `Circuit/Rails.lean:461-471`, `:475-494`, `:498-519`, 53 lines | reusable unchanged | Take arbitrary right-derivative data `g'` and a slope bound required only while `g ≤ c`. This is the handoff §2 route with `r = (I_up − ε)/C_max`. They depend on #1. |
| 3 | `invariant_of_strict` | `Circuit/Tube.lean:18-47`, 30 lines | reusable unchanged | Strict-face invariance for finitely many constraints. For one scalar constraint it is Mathlib's `image_le_of_deriv_right_lt_deriv_boundary` (§2 row 19): re-derive rather than port. |
| 4 | `IsTrajOn`, `IsTrajOn.mono` | `Spec/Circuit.lean:95-99`, `Circuit/Rails.lean:526-529` | reusable with new hypotheses | Same regularity (continuous on `[a, b]`, right derivative on `[a, b)`), which is also the notion Mathlib's Grönwall lemmas use. The equation becomes an inclusion. |
| 5 | `rail_invariance`, `rail_invariance_set`, `rail_invariance_node`, `out_mem_rails` | `Circuit/Rails.lean:179-206`, `:360-450`; `Cells/Inverter.lean:59-83` | reusable with new hypotheses and proof | False under any positive disturbance (§6.3). New statement: invariance of `[V_lo, V_hi]`; new proof: strict face inequalities from reverse conduction of the explicit law. The pattern "one barrier lemma per face" carries over. |
| 6 | Current margins `Irise_le_F_out`, `F_out_le_neg_Ifall`; `Irise_le_core`, `core_le_neg_Ifall`, `core_le_Ioff`, `neg_Ioff_le_core` | `Cells/Inverter.lean:87-153`; `Cells/InverterCore.lean:78-187` | reusable with new proof | Same shape ("off device contributes at most …, on device at least …, so the net current exceeds a margin while the output is on the wrong side of the threshold"). The numbers must come from the square law over the parameter box and hold on `[V_lo, V_OH]` and `[V_OL, V_hi]`, not only on the rail. |
| 7 | `propagation`; `IsInvCore.propagation_side` with `Params.tpdSide` | `Cells/Inverter.lean:158-240`; `Cells/InverterCore.lean:198-295` | reusable with new hypotheses and proof | `propagation_side` already proves the disturbed-margin delay `C_max·max(V_OH/(I_rise − ε), (V_DD^max − V_OL)/(I_fall − ε))` for an extra bounded inflow, by the argument of handoff §2. Two changes are required: its rail hypothesis `hrail` (`:221`) is assumed and must become a proved invariant, and the starting level is `V_lo`, not `0`. |
| 8 | `contamination`, `contamination_rail`; `slew_bound`, `slew_lipschitz`, `abs_vf_le` | `Cells/Inverter.lean:243-306`; `Cells/InverterCore.lean:322-383`; `Circuit/Rails.lean:211-268`, `:341-354` | reusable with new hypotheses and proof | Needs a bound on the magnitude of `I_net` over the safe domain plus `ε`, and `C_min`. Only wanted if a minimum-delay or hold-after-input-change claim is in scope. |
| 9 | `exists_isTrajOn` and `Circuit/Field.lean` | `Circuit/WellPosed.lean:46-68`; 193 lines | reusable with new proof | Reuse the one-shot instantiation of `IsPicardLindelof` (radius `B·(b − a)`, `r = 0`) for a clamped scalar field. `Circuit/Field.lean` is netlist bookkeeping and is not needed. |
| 10 | `isTrajOn_unique`, `exists_dist_le_gronwallBound`, `exists_lipschitz_dependence` | `Circuit/WellPosed.lean:72-123` | reusable with new proof (not needed for the headline claim) | The inclusion has no uniqueness. For a fixed disturbance and capacitance law the ODE has, by the same Mathlib lemma `ODE_solution_unique_of_mem_Icc_right` on a Lipschitz (clamped) field. For a tube around a nominal solution, Mathlib's `dist_le_of_approx_trajectories_ODE` applies directly to inclusion trajectories (§2 row 19). |
| 11 | `validIn`, `validOut`, `NML`, `NMH`, `Consistent.validIn_of_validOut`, `Consistent.not_validIn_both` | `Spec/Levels.lean:20-27`; `Spec/Params.lean:71-74`; `Cells/Levels.lean:20-32` | reusable unchanged | About 15 lines. A relation that leaves mid-band voltages unclassified, as handoff §2 requires. The interface states the same content as a three-valued decoder. |
| 12 | `Params`, `Params.Consistent` | `Spec/Params.lean:21-129` | reusable with new hypotheses | 11 of the 19 fields and K7, K8, K10–K12, K14 concern clocks, flip-flops, stacks and a fidelity budget. Keep the pattern (finite numeric side conditions closed by `norm_num`, plus a theorem that they are satisfiable), not the record. |
| 13 | `FETContract`, `Passive`, `Regular`, `BoundedOnRail`, `NodeCap`, `gateDrive` | `Spec/Device.lean:53-114` | outside scope | The new model fixes an explicit law. `Regular` is false for an unclamped square law; C3, C4, C6 are on-rail only; C5 is unused. |
| 14 | Netlist layer: `Node`, `FET`, `Netlist`, `F`, `vf`, `IsInverter`, `F_out`, `Circuit/Inflow.lean` | `Spec/Circuit.lean`, `Spec/Cells.lean:32-43`, `Cells/Inverter.lean:30-55` | outside scope | A one-node scalar model does not need a netlist. Relevant again for the wire and driver–receiver step of handoff §7. |
| 15 | Toy clamp device and its contract proof | `Design/Toy.lean`, `Witness/Devices.lean` | outside scope | It is the M0 baseline and stays in the reference clone. |
| 16 | Witness pattern `inv_propagation_hypotheses`, `inv_rises`, `inv_falls` | `Witness/ToyInverter.lean` | reusable with new proof | Keep the pattern "one theorem stating every hypothesis for a concrete instance, one per output direction". Strengthen it as handoff §2 requires: an initial set of positive width, `ε > 0`, a non-degenerate box. |
| 17 | Claims and audit pattern | `Claims.lean`, `scripts/` | outside scope (tooling, not a result) | The idea of restating results over a small trusted layer and auditing axioms is worth keeping. The upstream scripts were not executed here; `$W/refs/workstream-A/tools/IndepAudit.lean` is an independent implementation with a negative control. |
| 18 | Flip-flop, synchronous refinement, shell, `Tellegen`, `Charge`, `Lyapunov`, `Keeper`, `Compose`, `Chain`, `max_principle_band` | — | outside scope | Not needed for one inverter. |

Rows 1–3 and 11 total about 145 lines; rows 1 and 2, the only ones not immediate from Mathlib,
are 98 lines of statement and proof text.

State of this repository when the audit was written (2026-11-09, about 15:50 local time; headers
and declaration names read for orientation only, **not reviewed**): freshly written,
Mathlib-based counterparts already existed for rows 2–3 (`VoltageToBit/Proofs/Reach.lean`), 5–7
(`Proofs/Margins.lean`, `Proofs/Guarantee.lean`), 8 (`Proofs/Contamination.lean`) and 9
(`Proofs/Existence.lean`). No verbatim port is therefore needed at present, which also avoids the
question of §10. The table then serves as a checklist of what each counterpart has to cover.

### 11.2 Pitfalls recorded upstream that the new development must avoid

| Source | Problem recorded for the old development | Requirement for the new one |
| --- | --- | --- |
| F3, `docs/FINDINGS.md:75-96` | A sheet could satisfy every numeric condition while no device satisfied the contract, so every theorem over contract devices held vacuously. Fixed by K13 and by not fixing a Lipschitz constant in the sheet. | Prove that the admissibility conditions are satisfiable and that the parameter box and every other hypothesis set are nonempty. Keep constants no theorem uses out of the record. |
| F4, `docs/FINDINGS.md:98-102`; counterexample in `docs/CHANGELOG.md:17` | The slew bound was false without the initial state on the rails. | A bound that holds only on the safe domain needs the initial state in the domain and a proved invariance. |
| F7 and F2, `docs/FINDINGS.md:163-174`, `:66-73` | Missing sign and order conditions allowed empty environments and contradictory timing. | State the sign and order of every parameter. Exhibit one admissible record. Make the deadline nonnegative and the observation window nonempty in the witness. |
| F1 and F6, `docs/FINDINGS.md:7-64`, `:135-161` | An environment predicate that did not determine the waveform forced the contract's storage sets to be empty; downstream theorems became vacuous. | For every predicate used as a hypothesis (input class, initial set, parameter box, trajectory), exhibit one object satisfying all hypotheses at once. |
| F5, `docs/FINDINGS.md:104-133`; `docs/CHANGELOG.md:26` | Proof windows reached outside the interval on which the trajectory was constrained; `IsTrajOn` says nothing outside `[a, b]`. | Keep every time used by a hypothesis or conclusion inside `[a, b]`. At `b` only continuity is available. |
| F10, `docs/FINDINGS.md:205-214` | Contract devices are unconstrained for gate drives between `V_off` and `V_on`. | Domain invariance must hold for every input value in the admitted range, mid-band values included. Say what is and is not claimed during an input transition. |
| F14, `docs/FINDINGS.md:247-252` | With leakage the box-shaped storage sets are no longer invariant. | Same phenomenon as §6: an unmodelled current changes which sets are invariant. Do not carry an invariant over from the zero-disturbance model. |

Further pitfalls found by this audit:

| # | Observation | Requirement |
| --- | --- | --- |
| A1 | `IsInvCore.propagation_side` assumes the output stays on the rail (`Cells/InverterCore.lean:221`). | The invariant must be a conclusion of the headline result, not a hypothesis. |
| A2 | Conclusion (a) of `propagation` quantifies over `Icc (t₀ + t_pd) t₁`, which may be empty. | The concrete instance must show a window of positive length after the deadline. |
| A3 | The old witness is a single point (§5.1). | The new witness needs an initial set of positive width, `ε > 0` and a non-degenerate box (handoff §2). |
| A4 | Dividing a current bound by the capacitance uses `0 ≤ X` (`Cells/Inverter.lean:187-189`). | `(I − ε)/C_max` is a valid lower slope bound only when `I − ε ≥ 0`; otherwise the bound uses `C_min`. |
| A5 | With the inclusion required only inside the safe domain, a non-strict face inequality does not give invariance (§6.4; abstract form checked in §2 row 19). | Keep the face margins strict. |
| A6 | The old sources have no units and the toy numbers are not labelled as normalized (§4.5). | Label every number with its unit or as normalized. |
| A7 | A contract clause can be assumed and never used (C5, §2 row 20), and a hypothesis can be much stronger than its use (the inverter proofs use `Regular` only through continuity, to get `I g v v = 0`; its global bound is used only for existence). | Review each hypothesis of the headline theorem for use. |

## 12. The empty-storage-set probe as a regression example (item 9)

Source: the Lean block of handoff §8, compiled in §2 rows 11 and 12. It proves
`emptyHold_contract`: for any netlist, pins and sheet with `0 ≤ t_su`, `0 ≤ t_h`, `0 ≤ t_cq^min` and
`t_cq^min < t_cq^max`, the abstract flip-flop contract `FFContract` holds with the hold-set family
`fun _ _ _ => ∅`.

Why it goes through: both behavioural fields of `FFContract` (`ff1`, `ff2`,
`Spec/FlipFlop.lean:103-121`) have the premise `e s ∈ Hold (fun t => u t clk) d s`. With empty
hold sets the premise is `False`.

What it shows:

- A proof of `FFContract` for a caller-chosen `Hold` is not, by itself, evidence of a working
  storage element. The predicate is satisfiable with no behaviour at all.
- The general pattern to test for: a contract whose obligations are guarded by membership in a set
  that the prover of the contract chooses. The inverter analogues are an empty parameter box, an
  empty initial set, an unsatisfiable input class, an empty observation window, and an assumed
  invariant that no trajectory satisfies.

What it does not show:

- It does not make the concrete TGMS26 result vacuous. That result uses the specific family
  `tgffHold`, with `toy_tgffHold_nonempty` and `toy_tgff_reachable`
  (`Witness/ToyFlipFlop.lean:84-86`, `:105-110`; `Claims.lean:485-498`). These were not audited
  here beyond their statements.
- It does not supply the initial-state premise of synchronous refinement: `InvL4`
  (`Spec/Sync.lean:157-159`) requires the state to lie in every flip-flop's hold set, which is
  impossible when the sets are empty.
- It does not touch the inverter theorems, which have no hold-set parameter.
- It is not an inconsistency: nothing false is derived.

Use as a regression test: keep the file compiling against the pinned old library as a reminder of
the pattern, and write the corresponding negative controls for the new claim (handoff §5).

## 13. Lean's module system (item 10)

- None of the 45 Lean files of the pinned commit begins with `module` (`grep -rlE '^module\b'`: no
  match). All use plain `import`.
- Mathlib at the pinned revision is written with the module system (for example
  `Mathlib/Analysis/ODE/ExistUnique.lean:6` is `module`, followed by `public import`).
- `lake build` printed 30 warnings of one form, one per direct Mathlib import line, in 14 files:

  ```text
  warning: AsmPhys/Spec/Device.lean: imports `Mathlib.Topology.MetricSpace.Pseudo.Constructions` from package `mathlib`, which is designed for use with the module system; consider adding `module` to the start of this file
  ```

  Files and counts: `Spec/Device` 3, `Spec/Circuit` 3, `Spec/Cells` 1, `Circuit/Field` 5,
  `Circuit/Rails` 2, `Circuit/WellPosed` 2, `Circuit/Charge` 2, `Circuit/Tellegen` 2,
  `Cells/Compose` 2, `Design/Toy` 2, `Shell/EndToEnd` 1, `Witness/Clock` 1, `Witness/Devices` 3,
  `Witness/Toy` 1. The other 30 modules import only project modules and built without warnings.
- Compiling single files with `lake env lean` printed no such warning, including a file that
  imports Mathlib directly (§2 row 19). The warning was seen only from `lake build`.
- Mathlib's file layout at this revision differs from older releases (for example the project
  imports `Mathlib.Basic.Real.Basic`). Lemma names and paths should be taken from the pinned
  sources, not from memory of earlier versions.

## 14. Completed and proposed checks

Completed in this session:

- Fresh clone at the pinned commit; object integrity (`git fsck`); 49 of 49 manifest hashes.
- Dependency pins equal to this repository's; shared dependency tree unchanged by the session.
- `lake build` of the 44 project modules; build log kept.
- Handoff probe and the previous session's probe file compiled.
- Independent static layer check and independent environment audit, with a negative control.
- Dependency map from the compiled environment and from file imports; clause-usage analysis of
  the device contract.
- Disturbance counterexample (Appendix A); contamination instance (Appendix B); three
  Mathlib-only checks used in §6.4 and §11.

Not completed:

- **Upstream `scripts/check_layers.py` and `scripts/Audit.lean` were not executed** (§2 rows 9, 10).
  Proposed: the owner runs them, or permits running them, in the clone:
  `python3 scripts/check_layers.py && lake env lean scripts/Audit.lean`. The previous session's
  recorded outputs are in handoff §1.
- No independent kernel replay of the old library or of Mathlib (proposed; unchanged from the
  previous session).
- The hand calculations in §5.1 (actual toy rise time) and §6.3 (size of the excursion; unbounded
  growth for `ε > I_sat`), and the transfer of the strictness remark of §6.4 to the circuit model,
  are not Lean-checked (proposed if they are to be relied on).
- The CI status of the pinned commit on the hosting site was not queried.
- The old flip-flop, synchronous and probabilistic layers were not audited beyond what §12 needs.
- The files of this repository mentioned in §11.1 were not reviewed.

Open dependency: the reuse terms of §10 need a decision by the old repository's copyright holder
before any text is copied.

## Appendix A. `DisturbanceProbe.lean`

Not an upstream file. Written for this audit; compiles against the pinned library with
`lake env lean` from the clone (§2 row 17).

```lean
import AsmPhys

/-!
Workstream A probe (not an upstream file): the old rail-invariance conclusion fails as soon as a
bounded additive disturbance current is added to the node equation.

Setting: the pinned toy inverter `AsmPhys.Toy.inv` (clamp devices, unit capacitance), ground 0,
supply 1, input held at 0, output started ON the upper rail. With the constant disturbance
`w ≡ ε`, `0 < ε ≤ 1`, the explicit curve `e(t) = 1 + ε (1 − exp (−t))` solves the disturbed node
equation `C ė = F + w` and is strictly above the rail for every `t > 0`.
-/

open AsmPhys AsmPhys.Toy Set

namespace DisturbanceProbe

/-- Nodal ODE of the toy inverter with an additive disturbance current `w t` into the output:
continuity on `[a, b]` and `C ė = F + w` as a right derivative on `[a, b)` (the old `IsTrajOn`
with `w` added). -/
def IsDisturbedTraj (u : ℝ → Fin 3 → ℝ) (w : ℝ → ℝ) (e : ℝ → Fin 1 → ℝ) (a b : ℝ) : Prop :=
  ContinuousOn e (Icc a b) ∧
    ∀ t ∈ Ico a b,
      HasDerivWithinAt e (fun k => (inv.F (u t) (e t) k + w t) / inv.C k (e t k)) (Ici t) t

/-- With the input low and the output `v ∈ [1, 2]` (at or above the supply rail), the toy
inverter's net channel current is `-(v - 1)`: zero on the rail, restoring above it. -/
theorem toy_F_above_rail {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 2) :
    inv.F ![0, 1, 0] (fun _ => v) 0 = -(v - 1) := by
  have hV : fetParams.Voff < fetParams.Von := by norm_num [fetParams]
  rw [Witness.inv_isInverter.F_out, Witness.inv_isInverter.current_n,
    Witness.inv_isInverter.current_p]
  have hn : (inv.fet (0 : Fin 2)).I = dev .n fetParams := rfl
  have hp : (inv.fet (1 : Fin 2)).I = dev .p fetParams := rfl
  rw [hn, hp]
  show -(dev .n fetParams 0 v 0) - dev .p fetParams 0 v 1 = -(v - 1)
  have h1 : dev .n fetParams 0 v 0 = 0 := by
    have hg : gateDrive .n 0 v 0 ≤ fetParams.Voff := by
      show (0 : ℝ) - min v 0 ≤ fetParams.Voff
      rw [min_eq_right (by linarith [hv.1]), sub_zero]
      norm_num [fetParams]
    rw [dev, Witness.ramp_eq_zero hV hg, zero_mul]
  have h2 : dev .p fetParams 0 v 1 = v - 1 := by
    have hg : fetParams.Von ≤ gateDrive .p 0 v 1 := by
      show fetParams.Von ≤ max v 1 - 0
      rw [max_eq_left hv.1, sub_zero]
      exact le_trans (by norm_num [fetParams]) hv.1
    rw [dev, Witness.ramp_eq_one hV hg, one_mul]
    show max (-(1 : ℝ)) (min 1 (1 * (v - 1))) = v - 1
    rw [one_mul, min_eq_right (by linarith [hv.2]), max_eq_right (by linarith [hv.1])]
  rw [h1, h2]; ring

/-- **Counterexample.** For every `0 < ε ≤ 1` and every horizon `b` there is a trajectory of the
disturbed toy inverter, with disturbance `|w| ≤ ε`, that starts in `[0, 1]` (on the rail) and is
strictly above the rail `[0, 1]` at every later time. All other hypotheses of the old rail
invariance theorem hold (C1/C2 devices, boundary nodes in `[0, 1]`, initial state in `[0, 1]`). -/
theorem toy_rail_not_invariant {ε b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (w : ℝ → ℝ) (e : ℝ → Fin 1 → ℝ),
      (∀ t, |w t| ≤ ε) ∧ IsDisturbedTraj (fun _ => ![0, 1, 0]) w e 0 b ∧
      e 0 0 ∈ Icc (0 : ℝ) 1 ∧ ∀ t ∈ Ioc 0 b, 1 < e t 0 := by
  refine ⟨fun _ => ε, fun t _ => 1 + ε * (1 - Real.exp (-t)), fun _ => by simp [abs_of_pos hε],
    ⟨?_, ?_⟩, ?_, ?_⟩
  · exact continuousOn_pi.2 fun _ => by fun_prop
  · intro t ht
    have hexp1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [ht.1])
    have hexp0 : 0 < Real.exp (-t) := Real.exp_pos _
    have hv : (1 + ε * (1 - Real.exp (-t))) ∈ Icc (1 : ℝ) 2 := by
      constructor <;> nlinarith
    refine hasDerivWithinAt_pi.2 fun k => ?_
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    have hF := toy_F_above_rail hv
    have hC : inv.C 0 (1 + ε * (1 - Real.exp (-t))) = 1 := rfl
    simp only [hF, hC, div_one]
    have h := (((hasDerivAt_id t).neg.exp).const_sub 1 |>.const_mul ε |>.const_add 1)
    have hd : HasDerivAt (fun s : ℝ => 1 + ε * (1 - Real.exp (-s)))
        (-(1 + ε * (1 - Real.exp (-t)) - 1) + ε) t := by
      refine h.congr_deriv ?_
      simp only [Pi.neg_apply, id_eq]
      ring
    exact hd.hasDerivWithinAt
  · simp
  · intro t ht
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith [ht.1])
    show 1 < 1 + ε * (1 - Real.exp (-t))
    nlinarith

/-- The remaining hypotheses of the old `Netlist.rail_invariance` hold for the toy inverter with
these boundary values: both devices are passive (C1) and regular (C2), and every boundary node
lies in `[0, 1]`. -/
theorem toy_old_hypotheses :
    (∀ i, Passive (inv.fet i).I) ∧ (∀ i, Regular (inv.fet i).I) ∧
      ∀ j : Fin 3, (![0, 1, 0] : Fin 3 → ℝ) j ∈ Icc (0 : ℝ) 1 := by
  refine ⟨fun i => ?_, Witness.inv_regular, fun j => ?_⟩
  · change Fin 2 at i
    fin_cases i
    exacts [(Witness.toy_contract .n).passive, (Witness.toy_contract .p).passive]
  · fin_cases j <;> simp

/-- The conclusion of rail invariance is false for the disturbed toy inverter on every horizon
`b > 0` and for every disturbance bound `0 < ε ≤ 1`. -/
theorem toy_rail_invariance_fails {ε b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b) :
    ∃ (w : ℝ → ℝ) (e : ℝ → Fin 1 → ℝ),
      (∀ t, |w t| ≤ ε) ∧ IsDisturbedTraj (fun _ => ![0, 1, 0]) w e 0 b ∧
      e 0 0 ∈ Icc (0 : ℝ) 1 ∧ ¬ ∀ t ∈ Icc 0 b, e t 0 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨w, e, hw, he, h0, h⟩ := toy_rail_not_invariant (b := b) hε hε1
  exact ⟨w, e, hw, he, h0, fun hall =>
    absurd (hall b ⟨hb.le, le_rfl⟩).2 (not_le.2 (h b ⟨hb, le_rfl⟩))⟩

end DisturbanceProbe

#print axioms DisturbanceProbe.toy_F_above_rail
#print axioms DisturbanceProbe.toy_rail_not_invariant
#print axioms DisturbanceProbe.toy_old_hypotheses
#print axioms DisturbanceProbe.toy_rail_invariance_fails
```

## Appendix B. `ContaminationProbe.lean`

Not an upstream file. Written for this audit; compiles against the pinned library with
`lake env lean` from the clone (§2 row 18).

```lean
import AsmPhys

/-!
Workstream A probe (not an upstream file): the hypotheses of the pinned
`Netlist.IsInverter.contamination` (THM L3.2) are jointly satisfiable for the toy inverter with an
input that actually moves. The pinned repository instantiates `propagation` on the toy inverter
(`Witness.inv_rises`, `inv_falls`) but has no stand-alone instantiation of `contamination`.

Input: low until `t = 9`, then a continuous ramp reaching `1` at `t = 9.1`. Output: started at `0`.
Result: the output is a valid `1` at `t = 9` and stays a valid-high *input* level on `[9, 9.1]`,
the window in which the input swings from a valid `0` to a valid `1`.
-/

open AsmPhys AsmPhys.Toy Set

namespace ContaminationProbe

/-- Input waveform: `0` until `t = 9`, then a ramp of slope `10` clipped at `1`. -/
noncomputable def uIn (t : ℝ) : ℝ := max 0 (min 1 (10 * (t - 9)))

/-- Boundary waveform: ground `0`, supply `1`, input `uIn`. -/
noncomputable def u (t : ℝ) : Fin 3 → ℝ := ![0, 1, uIn t]

theorem continuous_u : Continuous u := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · show Continuous fun _ : ℝ => (0 : ℝ)
    exact continuous_const
  · show Continuous fun _ : ℝ => (1 : ℝ)
    exact continuous_const
  · show Continuous fun t : ℝ => max 0 (min 1 (10 * (t - 9)))
    fun_prop

theorem uIn_low {t : ℝ} (ht : t ≤ 9) : uIn t = 0 :=
  max_eq_left ((min_le_right _ _).trans (by linarith))

theorem uIn_high {t : ℝ} (ht : 9.1 ≤ t) : uIn t = 1 := by
  have h : (1 : ℝ) ≤ 10 * (t - 9) := by norm_num at ht; linarith
  rw [uIn, min_eq_left h, max_eq_right zero_le_one]

theorem uIn_mem (t : ℝ) : uIn t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- Every hypothesis of `IsInverter.contamination` holds on `[9, 20]` for a toy trajectory whose
input swings from a valid `0` (at `t = 9`) to a valid `1` (from `t = 9.1`), and its conclusion
keeps the output a valid-high input level on the contamination window `[9, 9 + 1/10]`. -/
theorem toy_contamination :
    ∃ e : ℝ → Fin 1 → ℝ, inv.IsTrajOn u e 0 20 ∧ e 0 = 0 ∧
      sheet.validIn false (u 9 2) ∧ sheet.validIn true (u 9.1 2) ∧
      sheet.validOut true (e 9 0) ∧
      ∀ t ∈ Icc (9 : ℝ) (9 + 1 / 10), sheet.validIn true (e t 0) := by
  obtain ⟨e, he, he0⟩ := inv.exists_isTrajOn (Cmin := fun _ => 1) (Cmax := fun _ => 1)
    Witness.inv_regular (fun _ => Witness.nodeCap_const one_pos) (u := u) (a := 0) (b := 20)
    continuous_u.continuousOn (by norm_num) 0
  have hgnd : ∀ t ∈ Icc (0 : ℝ) 20, u t 0 = 0 := fun _ _ => rfl
  have hvdd : ∀ t ∈ Icc (0 : ℝ) 20, u t 1 = 1 := fun _ _ => rfl
  have h0 : e 0 0 ∈ Icc (0 : ℝ) 1 := by simp [he0]
  -- THM L3.1 on [0, 9]: the input is a valid 0 there, so the output is a valid 1 at t = 9.
  have he9 : inv.IsTrajOn u e 0 9 := he.mono le_rfl (by norm_num)
  have hin9 : ∀ t ∈ Icc (0 : ℝ) 9, sheet.validIn false (pot (u t) (e t) (.bdry 2)) := by
    intro t ht
    show uIn t ≤ sheet.VIL
    rw [uIn_low ht.2]
    norm_num [sheet]
  have hprop := (Witness.inv_isInverter.propagation Witness.sheet_consistent
    (Witness.toy_contract .n) (Witness.toy_contract .p) (Cmin := 1) (Cmax := 1)
    (fun _ => ⟨le_rfl, le_rfl⟩) (VDD := 1) ⟨le_rfl, le_rfl⟩ he9
    (fun t ht => hgnd t ⟨ht.1, by linarith [ht.2]⟩) (fun t ht => hvdd t ⟨ht.1, by linarith [ht.2]⟩)
    hin9 h0).1
  have h1 : sheet.validOut true (e 9 0) :=
    hprop 9 ⟨by rw [Witness.sheet_tpdINV]; norm_num, le_rfl⟩
  -- The output is on the rails at t = 9 (old rail invariance, no disturbance).
  have hrail : e 9 0 ∈ Icc (0 : ℝ) 1 :=
    Witness.inv_isInverter.out_mem_rails (Witness.toy_contract .n).passive
      (Witness.toy_contract .n).regular (Witness.toy_contract .p).passive
      (Witness.toy_contract .p).regular (VDD := 1) zero_le_one he hgnd hvdd h0 9
      ⟨by norm_num, by norm_num⟩
  -- THM L3.2 on [9, 20]: the input may do anything within the rails.
  have hsub : ∀ t ∈ Icc (9 : ℝ) 20, t ∈ Icc (0 : ℝ) 20 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hcont := Witness.inv_isInverter.contamination Witness.sheet_consistent
    (Witness.toy_contract .n) (Witness.toy_contract .p) (Cmin := 1) (Cmax := 1) one_pos
    (fun _ => ⟨le_rfl, le_rfl⟩) (VDD := 1) ⟨le_rfl, le_rfl⟩ (he.mono (by norm_num) le_rfl)
    (fun t ht => hgnd t (hsub t ht)) (fun t ht => hvdd t (hsub t ht))
    (fun t _ => (uIn_mem t : pot (u t) (e t) (.bdry 2) ∈ Icc 0 sheet.VDDmax)) h1 hrail
  refine ⟨e, he, he0, ?_, ?_, h1, fun t ht => hcont t ⟨ht.1, ?_⟩⟩
  · show uIn 9 ≤ sheet.VIL
    rw [uIn_low le_rfl]; norm_num [sheet]
  · show sheet.VIH ≤ uIn 9.1
    rw [uIn_high le_rfl]; norm_num [sheet]
  · rw [Witness.sheet_tcdINV]
    exact le_min (by linarith [ht.2]) (by linarith [ht.2])

end ContaminationProbe

#print axioms ContaminationProbe.toy_contamination
```

## Appendix C. Audit artefacts

All under `$W/refs/workstream-A/` (outside this repository). SHA-256:

| File | SHA-256 |
| --- | --- |
| `tools/IndepAudit.lean` | `96b3ae952f5bc350e59bca4376c2eefdbef0da63428c0c3f86c247159b9965bb` |
| `tools/IndepAuditNegControl.lean` | `c87cec989888b087ed651bc276ce30556976bf3aa15ee6ba3444c68b96cb9d8b` |
| `tools/indep_layers.py` | `bc73aa74d967885aedc32b40edab7aaaa90f44e237dba952657257552c9550ff` |
| `tools/cmp_hashes.py` | `8baef04052f1f4d49a2ed7c44adf32fec04d8053268504ac2bb7d6581e3a850a` |
| `tools/DepMap.lean` | `fb94216ba03ed1f93ac204e2af44cdb28a049797e4f5f05d9fae14278257c0fd` |
| `tools/import_closure.py` | `06fcf2c2172ae6d2fc9ea154d38af59d0edd6c6c166f5c90e6b1a16fff260aaf` |
| `tools/FieldUse.lean` | `14e74bcf889a3df466f70dd04b77ec324185310cd6b7b4ab9ac9cb1c2b4bee99` |
| `tools/render_audit.py` | `e9dd7482a1d016fc9a38ce489e150c2a9293f4f1472bb697d1d09e38babb2b7f` |
| `probes/DisturbanceProbe.lean` | `30741f5ac960cc9fc618ef730473d0540dbca9559c595b3b0263f2054affe3d9` |
| `probes/ContaminationProbe.lean` | `446e5523d9e337e3a6bc16a81d6f3da4d8d2309c123707df552a3a193cb48255` |
| `probes/MathlibRouteCheck.lean` | `6e89f3d726c63125805b59cdb0f61614fc5f47278e00ed6f6e1962261780a6b8` |

Logs of the runs in §2 are in `$W/refs/workstream-A/logs/` (`lake-build.log`,
`trust-boundary-probe.log`, `trust-boundary-probe-snapshot.log`, `hash-compare.log`,
`indep-layers.log`, `indep-audit.log`, `indep-audit-negative-control.log`, `depmap.log`,
`import-closure.log`, `field-use.log`, `disturbance-probe.log`, `contamination-probe.log`,
`mathlib-route-check.log`, `ls-tree-7359bfe.txt`). The Lean quotations in this document were
inserted from the clone by `tools/render_audit.py`. The probe of handoff §8 is saved untracked as
`$W/refs/assembly-to-physics/TrustBoundaryProbe.lean`
(sha256 `873b6fd181534eccb380392a3cbfe8eb0476c74790f72cac7729bfa492c7c38f`).

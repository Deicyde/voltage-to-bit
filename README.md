# voltage-to-bit

When does a continuously changing voltage become a bit you can rely on?

This repository answers that question for **one CMOS inverter**, in a
circuit-level model with an explicit allowance for model error, and checks the
answer in Lean 4. It is the first milestone of the plan in
[HANDOFF.md](HANDOFF.md). The provisional name and location can change.

## The claim

**Model.** Two transistors (PMOS from supply to output, NMOS from output to
ground, both gates on the input) following the symmetric Shichman–Hodges square
law, and one lumped output node. Three kinds of uncertainty are explicit: at
every instant the node capacitance may be anywhere in `[C_min, C_max]`, the
device and supply parameters may be anywhere in a box, and an unmodelled
current of magnitude at most `ε_I` may flow into the output node. The dynamics
are a differential inclusion; see [docs/interface.md](docs/interface.md) for
the exact definitions.

The base layer is the circuit level. Nothing is derived from field theory or
from semiconductor physics, and the Lean development contains no physical
axioms: the transistor law is a definition, and the theorems are about that
definition.

**Theorem.** For every design record whose numbers pass a finite list of
arithmetic checks, every input function and every trajectory on a time
interval `[a, b]` that starts in the safe voltage domain:

1. the output voltage stays in the safe domain;
2. if the input is valid-low on a window `[s, e)` inside `[a, b]`, the output
   is valid-high on `[s + τ_up, e]`;
3. if the input is valid-high on a window `[s, e)` inside `[a, b]`, the output
   is valid-low on `[s + τ_dn, e]`.

The deadlines `τ_up` and `τ_dn` are closed-form numbers of the record
([docs/interface.md](docs/interface.md), §6).

Voltages between the thresholds decode to *undefined*, never to a bit. The
current margins behind `τ_up` and `τ_dn` are derived from the device law, not
assumed.

**How to read "every input".** No regularity of the input is assumed, but the
theorem speaks about the trajectories that exist for an input. Existence is
proved for continuous inputs and for an input with one jump that takes its new
value at the jump instant. For a continuous input, constant parameters, a given
Lipschitz capacitance law and a given continuous disturbance, the solution of
the node equation is also unique (`solution_unique`). Uniqueness is not stated
for the input with a jump, and the inclusion itself has many trajectories for
one input. For an input that keeps its old value at the jump instant, a
trajectory across the jump need not exist. One case is proved: for the step
that is 1.8 V up to and including `t = 4` and 0 V afterwards, the illustrative
record has no trajectory on `[0, 10]` that starts in the safe domain
(`Examples.stepL_no_trajectory` in `VoltageToBit/Examples/InputClass.lean`), so
for that input the theorem is silent on `[0, 10]`. Nothing is stated about
other jumps, other states of the node at the jump, or other intervals. If the
input is not valid throughout the window, only statement 1 applies, and the
output may decode to either bit or to undefined.

**What links the model to anything else.** A different description of the
same node is covered whenever its node capacitance stays in `[C_min, C_max]`
and, on the safe domain and for the input values that occur, its net current
lies between the currents of two members of the parameter box, up to the
additive allowance (`IsTrajectory.of_sandwich`,
`IsTrajectory.of_static_sandwich`). Gate-drain feedthrough and coupling to one
neighbour through constant capacitors are covered when the total node
capacitance stays in `[C_min, C_max]`, the input and the neighbour are
continuous, and their slews, weighted by the two capacitances, fit in the
allowance (`IsTrajectory.of_charge_balance`). These
lemmas state the obligations. Nobody has discharged them for a device or for a
simulator model.

**Concrete instance** ([designs/illustrative-1v8.json](designs/illustrative-1v8.json);
units V, µA, fF, ns):

| Quantity | Value |
| --- | --- |
| Supply | 1.62 to 1.98 V |
| Thresholds `V_tn`, `V_tp` | 0.45 to 0.60 V each |
| `k_n`, `k_p` | 160 to 240, 80 to 120 µA/V² |
| Node capacitance | 5 to 20 fF |
| Unmodelled current `ε_I` | 2 µA |
| Valid input | low ≤ 0.40 V, high ≥ 1.25 V |
| Valid output | low ≤ 0.25 V, high ≥ 1.35 V |
| Safe domain | −0.10 to 2.08 V |

| Deadline | Closed form (rounded up) | Proved with a 16-level certificate | False below |
| --- | --- | --- | --- |
| Rise (low in, high out) | 3.43 ns | 2.26 ns | 2.168 ns |
| Fall (high in, low out) | 2.57 ns | 1.425 ns | 1.0234 ns |

The closed-form deadlines are 7250/2119 ≈ 3.4214 ns and 4575/1787 ≈ 2.5602 ns.
For a deadline between the last two columns no theorem of the library says
that it holds or that it is false. The ends are rounded: the slow runs behind
the last column (`Examples.slow_rise_run`, `Examples.slow_fall_run`) also
refute deadlines below about 2.16806 ns (rise) and 1.02349 ns (fall), and that
small refinement is not stated as a theorem. The proof method caps the
allowance for this box: with re-chosen proof split points 2.3801 µA is
admissible, and no choice of them admits 2.3802 µA
(`VoltageToBit/Examples/Limits.lean`).

These numbers are **illustrative**. They are plausible orders of magnitude and
are not fitted to any process, device model, or measurement. The notes beside
the record ([designs/illustrative-1v8.notes.md](designs/illustrative-1v8.notes.md))
say what caps `ε_I`, under which environment 2 µA has a physical reading (slow
edges and almost no coupling), and how far the record is from the open SKY130
process. A larger provable `ε_I` or a shorter proved deadline is an
improvement of the proof, not of a circuit.

## Status, in three separate dimensions

There is deliberately no single badge.

| Dimension | Status | Evidence |
| --- | --- | --- |
| Formal correctness | **Passed.** Lean 4.35.0 with Mathlib at a pinned revision checks every theorem; the library has no `sorry` and no axiom of its own. A full run of `scripts/check.sh --fresh` on this library passed: all 23 modules were compiled in the run, the source scan and the axiom audit found nothing, Lean's kernel re-checked every declaration of the compiled files, and six checkers bundled with the toolchain accepted an export of the library with everything it depends on. The self-test of the scripts passed (88 PASS lines, no FAIL). The section Reproduce says exactly what this establishes and what it does not. The scripts were rewritten twice after reviews showed ways to make them pass falsely; the repair was checked by independent verifiers in two further rounds, and the points of the last check were closed in commit `9d9d1d0`, which no independent reviewer has looked at. The soundness of the four checkers that are not Lean's own kernel was not examined. | `scripts/check.sh`, [evidence/lean/](evidence/lean/) |
| Applicability | One concrete record satisfies every hypothesis. The parameter box, the safe domain and the set of trajectories are proved nonempty for every admissible record. An explicit run exhibits both logic directions; a second explicit run has gate-drain feedthrough and coupling to one neighbour inside the allowance (rising direction only). Negative controls show that the checks reject wrong records and that claimed deadlines below the stated floors are false. The obligations that would connect a device or a simulator model to the box are stated and not discharged. | `VoltageToBit/Examples/`, `VoltageToBit/Proofs/NonVacuity.lean`, `VoltageToBit/Proofs/ModelError.lean`, [docs/assumptions.md](docs/assumptions.md) |
| Physical evidence | **None.** No measurement and no comparison against a foundry device model or SPICE has been run. Whether a real inverter stays inside the envelopes is an open assumption. The numerical experiments in this repository simulate the model itself; they are not evidence about a device. | [docs/assumptions.md](docs/assumptions.md), [docs/discrepancy-report.md](docs/discrepancy-report.md) |

## Decisions and open points

Decided by the owner on 2026-11-09:

- The base layer stays at circuit level.
- No further numerical experiments are planned for this milestone. The
  experiments that were already run stay in the repository as secondary
  material. The SPICE decks under `experiments/ngspice/` are prepared and were
  not run.

Open, and the owner's to decide:

- The final name, location and licence of this repository. The audited source
  repository carries no licence; no code was copied from it.
- Whether to run the source repository's own two audit scripts. This session
  was not permitted to execute them, and
  [docs/source-audit.md](docs/source-audit.md) says what was checked instead.

A natural next proof step: bound the restoring current at the boundary of the
safe domain with both transistors instead of one. Numerically the smallest
restoring current of the model is about 5.9 µA at the bottom and 6.4 µA at the
top of the fixed safe domain, and about 3.56 µA at the top of the safe domain
measured from the lowest supply (`docs/model.md` §6.1). Such a bound would
therefore raise the provable allowance of the illustrative record from
2.38 µA toward about 3.56 µA if the supply-relative domain is to stay covered.
These figures are computations, not theorems.

## What is not claimed

- That any manufactured transistor obeys the square law, or that the
  illustrative numbers describe a real process.
- Anything about inputs that are neither valid-low nor valid-high for the whole
  window: then only the safe-domain statement applies.
- Anything about trajectories that start outside the safe domain. The
  trajectory notion requires the current balance only while the output is
  inside.
- A minimum delay for arbitrary valid inputs. Bounds on how fast the output
  can move hold for inputs confined to a stated range; with a valid-low input
  held far below ground (−1 V) there is a run that takes the illustrative
  output from valid-low to valid-high within 38 ps
  (`VoltageToBit/Examples/NegativeControls.lean`).
- That the output stays within 0.10 V of the actual supply when the supply
  moves. For a moving supply only the fixed interval −0.10 to 2.08 V is proved,
  which reaches 0.46 V above the lowest supply; the interval measured from the
  supply is proved for a run at one constant supply value
  (`VoltageToBit/Proofs/AtSupply.lean`).
- Existence of a run for every input or every disturbance. Trajectories are
  proved to exist for the two input classes above, with constant parameters, a
  Lipschitz capacitance law and a continuous disturbance. A solution without a
  right derivative at some instant (a disturbance that is only measurable) is
  not a trajectory, and the theorem does not speak about it.
- The current that an input jump injects through the gate-drain capacitance.
  The feedthrough lemma needs a continuous input; for an input with a jump the
  model leaves that current out (`VoltageToBit/Proofs/ModelError.lean`).
- That a wrongly wired circuit would be detected. The topology is fixed inside
  the device law; the miswiring control is a statement about one other current
  law (`VoltageToBit/Examples/NegativeControls.lean`).
- Metastability, interconnect, more than one dynamic node, ground bounce, a
  supply that leaves its stated range, or noise with unbounded tails (thermal
  noise is about 0.5 to 0.9 mV rms on this node and is outside any
  deterministic bound). A supply that moves *within* its range is covered as a
  parameter choice per instant, but the displacement current it injects has to
  fit inside `ε_I`. See [docs/model.md](docs/model.md).
- A switching gate as the load. The load is an ideal grounded capacitance;
  currents caused by other nodes moving belong to `ε_I`. The two-stage
  corollary (`VoltageToBit/Proofs/Chain.lean`) feeds the first output into a
  second inverter as its input. It models neither the second gate's loading of
  the first node nor the current that the moving first output injects into the
  second output through the second gate's gate-drain capacitance. For the
  illustrative record that current fits the 2 µA allowance only for a
  gate-drain capacitance below about 0.03 fF, so the corollary is a statement
  about two ideal one-node stages.

## Reproduce

Requirements: the toolchain named in `lean-toolchain` (through elan); Mathlib
and its dependencies checked out in `.lake/packages` at the revisions in
`lake-manifest.json`, with no change that `git status` reports, and compiled
(`lake build` fetches and compiles them once; `scripts/check.sh` downloads
nothing and stops if one is missing, at another revision or changed); and
`python3` 3.11 or later and `git`, both found through `PATH` and trusted. The
scripts run every Python program with `PYTHONSAFEPATH=1` and
`PYTHONNOUSERSITE=1`, so no module is imported from the project directory.

| Command | What it does | Time here |
| --- | --- | --- |
| `sh scripts/check.sh --quick` | steps 1 to 6: design records, pinned configuration, build, source scan, axiom audit, import closure; no kernel replay, no record | about 4 min (nothing to recompile) |
| `sh scripts/check.sh` | full run: recompiles the library, Lean's kernel replays every module, six checkers accept an export; writes `evidence/lean/` | 435 s for the run recorded here; other full runs took 431 to 892 s |
| `sh scripts/check.sh --whole-env` | also replays, with Lean's kernel, every module that the library imports, directly or not | not run for this commit |
| `sh scripts/selftest.sh` | controls for `check.sh` itself; needs an up-to-date build and the records of a full run on the same files (run `scripts/check.sh` first) | 1960 s (about 33 min) for the run archived here; other runs took 2010, 2136 and 3609 s |

What the last full run established (records in `evidence/lean/`):

- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are the pinned
  files; `lakefile.toml` has no key and no compiler option outside the short
  lists that step 2 accepts, so nothing in it can move the library's sources
  or build products or change what the compiler is told; each of the nine
  dependency checkouts is at the revision given in `lake-manifest.json`, and
  `git status` lists no changed and no untracked file in it.
- All 23 modules of the library were compiled in that run from its source
  files. The digests of the 37 checked files (build configuration, library
  sources, design file, checking scripts) are in `evidence/lean/sources.sha256`;
  they were taken before the first step and again at the end, and agreed. No
  module of a dependency was compiled.
- The design record `VoltageToBit/Examples/IllustrativeDesign.lean`, named in
  `scripts/design-records.txt`, is byte for byte what `scripts/gen_design.py`
  generates from `designs/illustrative-1v8.json` under the definition name
  `illustrative`, and no other `.lean` file of the library begins with the
  generator's header.
- The source scan (Lean's own parser against an allow-list) and the axiom
  audit found nothing. None of the 556 declarations stored in the compiled
  files of the library, 329 of which are written in the source files, depends
  on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
- Lean's kernel (`leanchecker`) re-checked the 553 declarations of the
  compiled files of the 23 modules, each module on top of its imports as
  compiled; the other 3 stored declarations are compiler auxiliaries that the
  replay leaves out.
- An export of these 553 declarations, with the 44,448 declarations of
  Mathlib, its dependencies and Lean core that they depend on, was accepted by
  the six checkers bundled with the toolchain. `leanchecker` and
  `leanchecker-paranoid` are Lean's own kernel; `lean4lean` and `nanoda` are
  other implementations; `con-leche` and `con-ron` start from a prelude built
  into them, and `con-ron` is `con-leche`'s checker written in Rust, so at most
  four of the six are independent designs. `leanchecker` starts from an empty
  environment, as its source shows; `leanchecker-paranoid`, `lean4lean` and
  `nanoda` refuse an export without the declaration of `Eq` (observed; their
  sources were not read).

The self-test (`sh scripts/selftest.sh`; output in
`evidence/selftest/selftest-aa997c2.txt`) passed on commit `aa997c2` with 88 PASS lines and no
FAIL line: 74 negative controls (a defect that `check.sh` must report at the
step meant to catch it, or an attack that must change nothing; they include
the attacks of the reviews on the file tree, on Python's search path, on
`lakefile.toml` and its options, on the design record, on `.lake/config` and
on the kernel check, and in 4 of them the program of a step, the scan, the
design generator or the audit, is run directly instead of `check.sh`), 7 positive controls (an unmodified input that must
pass; one of them shows that a copy without build products reproduces the
records of `evidence/lean/` byte for byte), 6 observations of what the six
export checkers start from, and 1 check that the checkout was not changed.
The scripts of this commit differ from those of that run only in two comments
of `scripts/selftest.sh` (commit `60997fa`).
Several checks of `check.sh` have no control in the self-test, among them the
revision and `git status` check of the dependency checkouts, the comparison of
`lean --version` with `lean-toolchain`, the comparisons of built, audited and
replayed modules, the comparison of each export checker's count with the
export's, step 10 (`--whole-env`), the handling of a tool that is not
installed, and the scan's rule on the options a file was compiled with, which
no change of `lakefile.toml` alone can now reach.

What a pass does not establish: that the statements mean what the prose says,
or that any physical device obeys the model. Nothing at all when the library
itself is hostile: library code can run while it is compiled, before any check
runs. Nor that the export is faithful, that the four checkers other than Lean's
kernel are sound or independent of each other, or anything about declarations
of Mathlib that the library does not depend on (`--whole-env` re-checks those
of the modules the library imports, by Lean's kernel alone). Further limits:
the audit's shadowing rule does not consider names that `open` makes visible; a
definition of type `Design` that `scripts/design-records.txt` does not name is
compared with no JSON file; `git status` sees a dependency checkout as git is
configured there, for the user and for the system, so files that `.gitignore`,
`.git/info/exclude` or an excludes file exclude, and changes to files that the
index marks assume-unchanged or skip-worktree, are not looked at, and with
`core.worktree` set it looks at another directory;
Mathlib's compiled files in `.lake/packages` are used as they are; and
`--quick` reads the record of the last full run as it is.

Times are wall-clock times of single runs on an Apple M3 Pro laptop (12 cores,
18 GB of memory, macOS 14.4) while other jobs were running, with
`CHECK_REPLAY_JOBS=1` and the other settings at their defaults, and Mathlib
already compiled. The largest single process of a full run reached about
4.1 GB of resident memory. `evidence/lean/kernel-replay.txt` has no dates or
timings, so a full run with the same options on the same files with the same
tools (the toolchain build and platform named in it) reproduces it byte for
byte; the self-test shows this for a copy in another directory on this
machine.

## Where to look

| Path | Content |
| --- | --- |
| `VoltageToBit/Model/` | definitions: device law, design record, trajectories, decoding |
| `VoltageToBit/Proofs/Reach.lean` | circuit-free reachability lemmas |
| `VoltageToBit/Proofs/Margins.lean` | current margins derived from the device law |
| `VoltageToBit/Proofs/Guarantee.lean` | the guarantee for every trajectory |
| `VoltageToBit/Proofs/Existence.lean`, `Concat.lean` | existence and uniqueness of solutions; one input jump |
| `VoltageToBit/Proofs/NonVacuity.lean` | admissible records are never degenerate |
| `VoltageToBit/Proofs/Certificate.lean` | refined deadlines from lists of levels |
| `VoltageToBit/Proofs/ModelError.lean` | what another description of the node must satisfy to be covered |
| `VoltageToBit/Proofs/AtSupply.lean` | the safe domain measured from the actual supply |
| `VoltageToBit/Proofs/Contamination.lean` | how fast the output can move, for inputs in a range |
| `VoltageToBit/Proofs/Chain.lean` | two stages in series |
| `VoltageToBit/Examples/IllustrativeDesign.lean` | the design record, generated from `designs/illustrative-1v8.json` |
| `VoltageToBit/Examples/Illustrative.lean` | admissibility of the concrete instance, its guarantee with numbers, explicit runs |
| `VoltageToBit/Examples/RefinedDeadlines.lean`, `Limits.lean`, `DeadlineBrackets.lean` | proved deadlines, what is false below them, and the cap on `ε_I` |
| `VoltageToBit/Examples/NegativeControls.lean`, `InputClass.lean`, `TwoStage.lean` | negative controls, the input class, a two-stage witness |
| `guide/` | the specification in plain words, each passage linked to the Lean that states it (a formal-companion overlay in `annotations/` and `pdf-overlay/`), published at <https://deicyde.github.io/voltage-to-bit/pdf-overlay/viewer/index.html> |
| `docs/interface.md` | the frozen interface: definitions and what is proved |
| `docs/assumptions.md` | the assumption register, by type of evidence |
| `docs/model.md` | the model and its physical reading |
| `docs/adversarial-review.md`, `docs/review-disposition.md` | the independent review and what was done about each finding |
| `docs/source-audit.md` | audit of the source repository |
| `docs/discrepancy-report.md`, `docs/experiment-loop.md` | numerical experiments on the model; the propose, screen, check, record loop |
| `designs/` | design records (single source of numbers for Lean and experiments) |
| `experiments/`, `search/`, `evidence/` | experiment and search code, and their compact outputs |
| `review/` | the reviewer's compiled probes, pinned to the commits they reviewed |
| `scripts/` | generation, build and audit entry points |

## Provenance

The starting point was an audit of
[Deicyde/assembly-to-physics](https://github.com/Deicyde/assembly-to-physics/tree/7359bfe8266d06954e221f881403e7e83d5592f6)
at commit `7359bfe`. The Lean development here was written fresh against
Mathlib for a different model (additive error bound, widened safe domain,
symmetric device law). What was examined and what was reused is recorded in
[docs/source-audit.md](docs/source-audit.md).

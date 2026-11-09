# Adversarial specification and proof review (workstream E)

Reviewer: workstream E, independent of the author of the Lean development.
Date: 2026-11-09. Two frozen snapshots were reviewed and are kept apart below.

- **Part 1** reviews commit `1880a36` (the snapshot named in the brief).
- **Part 2** reviews the delta `1880a36..9b13e95` (requested by the coordinator
  while Part 1 was in progress) and says, for every Part 1 finding, whether it
  still applies at `9b13e95`.

The job was to break the development or to find where it claims more than it
proves. Everything stated as observed below was run by the reviewer; anything
not run is marked as such. Physical numbers that are the reviewer's own
estimates (not taken from a source) are marked "estimate".

## Summary

| | Part 1 (`1880a36`) | Part 2 (`9b13e95`) |
| --- | --- | --- |
| False theorem or unsound step (S1) | none found | none found |
| Statement vacuous as a whole (S2) | none found | none found |
| Scope narrower than prose (S3) | 5 findings | 3 new; of the 5, one partly fixed, two documented, two open |
| Unsupported physical interpretation (S4) | 2 findings | 1 fixed in Lean, 1 now disclosed in prose |
| Documentation or tooling (S5) | 4 findings | 2 new; the 4 of Part 1 still open (some items of E1-10 fixed) |

The formal core survived every attack on soundness and on meaning: both
snapshots rebuild from source to the same declarations, replay through the
kernel, use only the three standard axioms, contain no instance, notation,
option or macro that could change the meaning of a statement, and the headline
result for the instance can be restated with Mathlib notions only and closed by
the library theorems (probes P06, D03).

What the review did find is about scope and interpretation: the guarantee is
advertised for every input function but has no instances for some of them
(E1-01); the route offered for covering a better device model could not be met
at `1880a36` (E1-02, fixed at `9b13e95`); the physical reading of the input
class and of the 2 µA allowance is unsupported (E1-03, now disclosed); the
negative controls sit far from the boundary they are meant to probe (E1-04,
E1-05); and the checking script cannot see a kernel bypass (E1-08).

## Conventions

```sh
R="/Users/jack/Library/Application Support/Claude/scratch-workspaces/1800eb1f-93f3-40f7-b22e-6338202dfb3a/2dc7650f-b160-4d12-8450-fb90bfff4ec1/scratch-2026-11-09-8b62e5/voltage-to-bit"
F="${R%/*}/frozen-1880a36"     # read-only worktree at 1880a36 (Part 1)
F2="${R%/*}/frozen-9b13e95"    # read-only worktree at 9b13e95 (Part 2)
```

- A Lean probe `review/Pnn_*.lean` (Part 1) is compiled with
  `cd "$F" && lake env lean "$R/review/Pnn_*.lean"`; a probe `review/Dnn_*.lean`
  (Part 2) with `cd "$F2" && lake env lean "$R/review/Dnn_*.lean"`. The expected
  and observed output of every probe is: no error, no warning, and one line
  `'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]` per
  `#print axioms` at the end of the file. Captured outputs are in
  `review/out/` (Part 1) and `review/out2/` (Part 2).
- `review/run_all.sh "$F"` re-runs all of Part 1 (add `--slow` for the fresh
  rebuild and the kernel replay); `review/run_part2.sh "$F2"` re-runs Part 2.
  Neither writes into a frozen checkout; both end by checking that the checkout
  is still clean.
- Tool versions: Lean 4.35.0 (`eb6cafb`), Lake 5.0.0, Mathlib `v4.35.0`
  (`56a0058`), Python 3 with numpy 2.4.6 / scipy 1.18.0.

Severity classes (kept distinct):

| Class | Meaning |
| --- | --- |
| S1 | false theorem or unsound step |
| S2 | vacuous or trivially satisfiable statement presented as substantive |
| S3 | valid theorem whose scope is narrower than the prose suggests |
| S4 | invalid or unsupported physical interpretation |
| S5 | documentation or tooling defect |

---

# Part 1: commit 1880a36

## 1.1 Findings at a glance

| ID | Class | Finding | Status at `9b13e95` |
| --- | --- | --- | --- |
| E1-01 | S3 | "Every input, no regularity assumed": for a step input that keeps its old value at the jump instant there is provably no trajectory at all, so the guarantee is vacuous there; existence is proved for continuous inputs only | changed shape: documented in two places, one right-continuous jump now covered, still advertised without caveat in three places |
| E1-02 | S4 | The model-error obligation (one fixed parameter point, absolute 2 µA) cannot be met even by first-order channel-length modulation, for any point of the box | **fixed** (per-instant parameter point, sandwich form) |
| E1-03 | S4 | Input class and load: no bound on input range or slew, grounded lumped load; the omitted gate-drain feedthrough is unbounded over the advertised input class and exceeds the allowance in the instance's own explicit run | changed shape: disclosed as an unproved environment restriction; theorem hypotheses unchanged |
| E1-04 | S3 | Header of the negative controls: "No trajectory starting valid-low can be valid-high within 38 ps" is false for the guarantee's input class (compiled counterexample) | still open |
| E1-05 | S3 | Negative controls sit far from the boundary (38 ps against a 3.43 ns deadline; a rejected certificate only fails a sufficient condition; nothing for the falling direction; one stuck trajectory for the miswired network) | still open (a falling minimum-delay lemma was added, no control uses it) |
| E1-06 | S3 | The four boundary conditions of `Admissible` are sufficient, not necessary, by a factor 2.56 for the instance; the cap `eps < 2.312` is a proof artifact | changed shape: documented in the record notes; proof unchanged |
| E1-07 | S3 | Existence proved only for constant capacitance and globally continuous input and disturbance; wider coverage is advertised for the guarantee | partly fixed (Lipschitz voltage-dependent capacitance, uniqueness, one jump) |
| E1-08 | S5 | The axiom audit and token grep cannot see a declaration added with the kernel check switched off; `check.sh` does not establish "the kernel accepted every declaration" | still open (script unchanged); both snapshots pass an actual kernel replay run by the reviewer |
| E1-09 | S5 | `gen_design.py` pastes two JSON strings into a Lean comment unescaped and accepts malformed numbers and duplicate keys | still open (script unchanged) |
| E1-10 | S5 | Prose and docstrings that differ from the checked statements (seven items) | three fixed, three open, one reworded; new dangling links (E2-04) |
| E1-11 | S5 | `tauUp`, `tauDn`, `decode` evaluated outside `Admissible` give a negative deadline, a zero deadline (division by zero), or a decoder without undefined band | still open (definitions unchanged) |

## 1.2 Findings in detail

### E1-01 (S3). The guarantee has no instances for inputs with a left-continuous jump

**Affected.** `IsTrajectory` (`Model/Inverter.lean`) and through it
`IsTrajectory.safe`, `.rise`, `.fall`, `.decoded`, `illustrative_guarantee`.
Prose: `Proofs/Guarantee.lean` header ("every input `u : ℝ → ℝ` (no regularity
assumed)", "That trajectories exist is proved separately"), `docs/interface.md`
§1 ("an arbitrary real-valued function of time") and §4 ("contains every
solution of ...", "No regularity of `u`, `w`, or `C` is assumed").

**What is true.** `IsTrajectory` asks for a right derivative that satisfies the
current balance at every instant, with the input value *at* that instant. For an
input that jumps and keeps its pre-jump value at the jump instant, the balance at
that instant refers to the old input value while the right derivative of any
candidate output is forced by the new one. The reviewer proved in Lean:

- `Review.P01.rderiv_ge_of_right_nhd`: a right derivative cannot be smaller at
  `t0` than a lower bound that holds on `(t0, t0 + δ)`.
- `Review.P01.stepL_no_trajectory`: for the illustrative record, nominal
  parameters and `uStepL t = if t ≤ 4 then 1.8 else 0`, there is **no**
  trajectory on `[0, 10]` from **any** initial state in the safe domain:
  `IsTrajectory illustrative nominal uStepL v 0 10 → v 0 ∈ illustrative.Safe → False`.
  The input decodes to a valid bit at every instant (`uStepL_valid_high`,
  `uStepL_valid_low`).
- `Review.P01.stepL_guarantee_proves_anything`: hence the hypotheses of
  `illustrative_guarantee` for this input prove `∀ t, v t = 12345`.
- `Review.P01.spike_no_trajectory` against `const_low_has_trajectory`: changing
  the constant-low input at the single instant `t = 0` removes every trajectory
  that starts with an output in `[-0.06, 0.25]`.
- `Review.P02.stepR_has_trajectory`: the right-continuous twin (new value at
  `t = 4`; it differs from `uStepL` at one instant) has trajectories from every
  initial state, by gluing two solutions (`Review.P02.IsTrajectory.concat`).

So the universally quantified guarantee is non-vacuous for continuous inputs
(library) and for right-continuous steps (P02), and vacuous for the left-
continuous step. Inside that sub-regime this is vacuity in the S2 sense; it is
filed as S3 because the theorem as a whole is substantive and the remedy is a
scope statement. In the same way "contains every solution of
`C(v) dv/dt = I_net + w`" means every function with a right derivative
satisfying the equation at *every* instant (`IsTrajectory.of_ode`), not
solutions in the usual almost-everywhere sense.

**Probes.** `review/P01_JumpInputVacuity.lean`, `review/P02_RightContinuousStepExists.lean`;
commands as in Conventions; observed: 5 and 2 axiom lines, all standard
(`review/out/P01_JumpInputVacuity.txt`, `review/out/P02_RightContinuousStepExists.txt`).

**Disposition.** State the input class for which the guarantee has instances;
say that inputs are evaluated pointwise and a jump must take its new value at
the jump instant; add existence by concatenation. Do not describe the input as
"arbitrary" without that caveat.

**Status at `9b13e95`.** Changed shape. `Proofs/Concat.lean` now has
`congr_input`, `concat` and `exists_trajectory_step` and its docstring states
the caveat; `docs/interface.md` §4 and §6 state it too. The emptiness itself
persists under the new per-instant definition, for every initial state
(`Review.D01.stepL_no_trajectory`, see E2-01). Still advertised without the
caveat: `README.md` ("every input waveform (no regularity assumed) ...
Trajectories are proved to exist ..., so the statement is not vacuous"),
`docs/interface.md` §1, and the `Proofs/Guarantee.lean` header.

### E1-02 (S4). The model-error obligation could not be met by the mildest refinement

**Affected.** `IsTrajectory.of_model_error` (`Proofs/ModelError.lean`) and its
header, which presents the hypothesis `hJ` as "the exact obligation that links
the square-law model to any other description of the same node".

**What is true.** `hJ` requires one fixed `θ` of the box with
`|J - Inet θ| ≤ εm ≤ eps` on the whole safe domain: an absolute 2 µA envelope
around a single square-law curve whose currents reach 85 to 170 µA. For the
nominal law with first-order channel-length modulation on the NMOS
(`Jclm lam u x = Ip nominal u x - In nominal u x * (1 + lam * x)`, `lam = 0.05`
per volt, an assumed small value, estimate):

- `Review.P04.clm_not_within_eps`: for **every** `θ` in the box,
  `¬ ∀ x ∈ illustrative.Safe, |Jclm 0.05 1.8 x - Inet θ 1.8 x| ≤ illustrative.eps`.
  (At input 1.8 V every box member is flat between 1.35 V and 2.08 V while the
  modulated current changes by 6.17 µA.)
- `Review.P04.clm_is_pointwise_square_law`: at each operating point the same law
  *is* a square law with in-box parameters (`k_n` between 199 and 220.8).
- `Review.P04.IsTrajectoryPW.safe/.rise/.fall` and `clm_guarantee`: the library
  proofs do not need a fixed `θ`; with the parameter point chosen per instant
  the modulated inverter is covered with the whole `eps` left for disturbances.

Independently of this: with `eps = 2` reserved for disturbances, the remaining
budget before the record stops being admissible is `2.312 - 2 = 0.312` µA
(`hiN`, `review/out/n01.txt`), about 0.2 to 0.4 % of the on-currents.

**Probe.** `review/P04_ModelErrorScope.lean`; observed: 6 axiom lines, all
standard (`review/out/P04_ModelErrorScope.txt`).

**Disposition.** Let the parameter point vary per instant (compiled in the
probe at no proof cost); keep `eps` for what the box cannot absorb.

**Status at `9b13e95`.** Fixed. `IsTrajectory` now quantifies the parameter
point per instant and `of_model_error` / `of_sandwich` state the obligation
against "some box member". The library's definition is literally the
reviewer's independently written one (`Review.D02.new_iff_reviewer_definition`),
and the modulated law is covered through the library's own `of_sandwich`
(`Review.D02.clm_guarantee`).

### E1-03 (S4). The input class and the grounded load have no supported physical reading

**Affected.** `docs/interface.md` §1 ("Load: lumped capacitance from output
node to ground"; input "an arbitrary real-valued function of time"), the valid
input classes `u ≤ VIL` / `VIH ≤ u` of `IsTrajectory.rise` / `.fall`,
`illustrative_scenario` (input `uRamp`, 9 V/ns).

**What is true.**

1. The valid-input classes have no lower or upper bound. The constant input
   `-1 V` is "valid-low", and the model then predicts a valid-high output
   within 38 ps (`Review.P03.valid_low_input_can_give_valid_high_within_38ps`,
   fast corner, zero disturbance). Any model-error obligation therefore
   quantifies over input values for which no device model can be compared.
2. A real inverter couples its input to its output through the gate-drain
   capacitance `C_M`; the injected current `C_M · du/dt` is not in the model.
   For it to be absorbed by `eps` the input slew must satisfy
   `|du/dt| ≤ eps / C_M`. The advertised input class has no slew bound (it
   contains discontinuous inputs), and the instance's own explicit run ramps at
   9 V/ns: 9 µA per fF of `C_M`, i.e. the whole 2 µA allowance at
   `C_M = 0.22 fF` (estimate of scale: tenths of a fF for a small gate, not
   sourced).
3. The same coupling moves the node by about `ΔU · C_M / (C + C_M)` on a fast
   edge: 0.16 V for `ΔU = 1.8 V`, `C = 5 fF`, `C_M = 0.5 fF` (estimate),
   more than the 0.10 V by which the safe domain exceeds the rails. So the
   proved safe-domain invariance does not transfer to a physical node driven by
   fast edges; this is exactly the "critical modelling issue" of the handoff.

**Probe.** `review/P03_DeadlineBrackets.lean` (item 1); items 2 and 3 are
arithmetic on the record, with the capacitance values marked as estimates.

**Disposition.** Put an input range and a slew bound into the environment
assumptions (and into the register), or model the coupling term. Do not call
the input arbitrary in a physical context.

**Status at `9b13e95`.** Changed shape: disclosed. `docs/interface.md` §4.1,
the "What is not claimed" list of `README.md`, the budget table in
`designs/illustrative-1v8.notes.md` and the docstrings of
`illustrative_scenario` and `Proofs/Chain.lean` now say this, with the same
numbers (0.22 fF; 0.03 fF for a second stage). The theorem hypotheses are
unchanged: there is still no input range or slew bound in any statement, so it
remains an unproved environment restriction, and item 1 still compiles
(`Review.D05.valid_low_input_can_give_valid_high_within_38ps`).

### E1-04 (S3). A sentence of the negative-control header is false as stated

**Affected.** `Examples/NegativeControls.lean`, header item 2: "No trajectory
starting valid-low can be valid-high within 38 ps". The theorem behind it,
`illustrative_no_early_high`, is correct but assumes `0 ≤ u ≤ 0.40`; the
guarantee's valid-low class is `u ≤ VIL` with no lower bound.

**Probe.** `Review.P03.valid_low_input_can_give_valid_high_within_38ps`:
`∃ θ u v, illustrative.InBox θ ∧ (∀ t, u t ≤ 0.40) ∧ v 0 ≤ 0.25 ∧
IsTrajectory illustrative θ u v 0 10 ∧ 1.35 ≤ v 0.038` (input `-1 V`).
Numerically (`review/out/n03.txt`): 72 ps at `u = 0.40`, 43 ps at `u = 0`,
21 ps at `u = -1`, 0.4 ps at `u = -100`.

**Disposition.** Add "for inputs in `[0, 0.40]` V" to the sentence, or bound
the valid-input class (see E1-03).

**Status at `9b13e95`.** Still open: the header is unchanged; ported probe
`Review.D05.valid_low_input_can_give_valid_high_within_38ps` compiles.

### E1-05 (S3). The negative controls do not probe the boundary of the guarantee

**Affected.** `Examples/NegativeControls.lean`, controls 2, 3 and 5.

**What is true.**

- Control 2 refutes a rise deadline of 0.038 ns. The proved deadline is
  3.43 ns (2.34 ns with the certificate). Nothing in between is refuted or
  proved, a gap of a factor 60.
- Control 5 (`illustrative_riseCert_rejected`) shows that one list of levels
  does not support 2.0 ns. That is a failed sufficient condition, not a
  refutation.
- There is no control, minimum-delay bound or instantiated certificate for the
  falling direction (`fall_of_cert` is never used).
- Control 3 exhibits one stuck trajectory of the miswired network. The network
  model `InetSwapped` is a fair model of exchanged transistors (checked by
  hand against the channel formula). The library has no netlist layer, so no
  control can show that the checker would *notice* a miswired design.

The reviewer closed most of the gap with actual trajectories:

| Statement (compiled) | Probe |
| --- | --- |
| a trajectory in the box, valid-low input, safe initial state, admissible disturbance, **not** valid-high at 2.16 ns; the same run is valid-high from 2.34 ns | `Review.P03.rise_deadline_2p16_is_false` |
| no list of levels is a valid rising certificate for 2.16 ns | `Review.P03.no_riseCert_at_2p16` |
| from a valid-low output, not valid-high at 1.64 ns | `Review.P03.rise_deadline_1p64_is_false_from_valid_low` |
| falling: not valid-low at 1.0 ns; a falling certificate proves 1.51 ns | `Review.P03.fall_deadline_1p0_is_false`, `illustrative_fallCert_3` |
| miswired network: **every** trajectory with a valid-low input that starts below 1.35 V stays below 1.35 V | `Review.P08.miswired_never_high` |

Numerically (`review/num/n03_worst_case_delay.py`, output `review/out/n03.txt`):
slowest rise 2.2512 ns from `Vlo`, 1.7279 ns from `VOL`; slowest fall
1.3924 ns from `Vhi`, 0.8787 ns from `VOH`. The infimum over all rising
certificates equals the slowest rise (2.251190 ns both), so certificates
cannot be gamed and the proved 3.43 ns is conservative by a factor 1.52, the
certificate's 2.34 ns by 1.04.

**Disposition.** Adopt the sharper controls; report each deadline with its
bracket (false below, proved above); instantiate a falling certificate.

**Status at `9b13e95`.** Still open. `IsTrajectory.fall_at_most` and two slew
numbers were added, but no control uses them and no falling certificate is
instantiated. The ported probes compile (`review/D05_Part1Ports.lean`).

### E1-06 (S3). The boundary conditions of `Admissible` are far from necessary

**Affected.** `Design.Admissible` fields `hiP`, `hiN`, `loN`, `loP`; any reading
of a rejected record as a failing circuit; any use of "largest admissible `eps`"
as a figure of merit (workstream F).

**What is true.** The proof bounds the restoring current at each end of the
safe domain with one transistor at a time, split at `uHi` / `uLo`. Both
transistors conduct there. `review/num/n02_device_and_margins.py`
(`review/out/n02.txt`; exhaustive over the 32 corners, dense grid in `u`):

| End | Proved bound | True minimum inward current |
| --- | --- | --- |
| `Vhi = 2.08` | min(`RhiP`, `RhiN`) = 2.312 µA | 6.44 µA (at `u = 0.65`) |
| `Vlo = -0.10` | min(`RloN`, `RloP`) = 3.04 µA | 5.92 µA (at `u = 0.82`) |

So the record is rejected for every `eps` in `[2.312, 5.92)` although,
numerically, the node cannot leave the safe domain there and the switching
margins (10.476, 16.296) still hold. The best split points alone would give
2.38 and 3.08. The switching margins `Iup`, `Idn`, by contrast, are attained
exactly at a corner (slack 0 in the search), so `up` and `dn` are tight.

**Disposition.** Say so wherever the cap on `eps` is quoted; in the search
loop, do not count a larger provable `eps` obtained by a better boundary proof
as a better circuit.

**Status at `9b13e95`.** Documented: `designs/illustrative-1v8.notes.md` gives
5.9, 6.4 and (new) 3.6 µA for the supply-relative top, marked "not a Lean
result"; the reviewer's enumeration reproduces 5.92, 6.44 and 3.56
(`review/out2/n05.txt`). The proof is unchanged.

### E1-07 (S3). Existence is proved for a smaller class than the guarantee is advertised for

**Affected.** `exists_solution`, `exists_trajectory`; `Proofs/Existence.lean`
header ("covers any state- or time-dependent capacitance").

**What is true.** Existence: constant capacitance, input and disturbance
continuous on all of ℝ, constant parameters. The solution solves the same
equation the inclusion is about (`Review.P06.explicit_end_to_end`). For
voltage-dependent capacitance, discontinuous input or disturbance the
guarantee is about whatever trajectories there are (possibly none, E1-01).
"Time-dependent capacitance" is covered only as the equation `c(t) v' = I`;
charge conservation for a capacitance that changes in time has the extra term
`c'(t) v`, which would have to fit into `eps`.

**Status at `9b13e95`.** Partly fixed: existence for Lipschitz
voltage-dependent capacitance, uniqueness, one right-continuous jump; the prose
now says "slowly varying". Existence for parameters that move in time is not
proved (stated as such).

### E1-08 (S5). The checking script cannot see a kernel bypass

**Affected.** `scripts/check.sh` ("What this establishes: the Lean kernel
accepted every declaration in this build"), `scripts/Audit.lean`.

**What is true.** `review/tooling/AuditGapDemo.lean` adds a theorem of type
`False` with the kernel check switched off by an option. Observed
(`review/out/audit_gap_demo.txt`):

```text
'AuditGapDemo.bad' does not depend on any axioms
'AuditGapDemo.oops' does not depend on any axioms
lean exit=0
== 2. token grep of scripts/check.sh applied to it ==
none found
== 3. kernel replay with leanchecker ==
leanchecker found a problem in AuditGapDemo
... (kernel) declaration type mismatch, 'AuditGapDemo.bad' has type True but it is expected to have type False
```

So a library containing such a declaration would pass steps 2 and 4 of
`check.sh`. The frozen sources contain nothing of the kind (no `set_option`,
`run_cmd`, `elab`, `instance`, `notation`, `macro`, `attribute`; checked by
grep in `run_all.sh`), and the reviewer ran the missing check directly:

- fresh rebuild of all 14 modules from source into a scratch directory, without
  the checkout's build products: same 383 constants with identical type and
  value hashes as the frozen build (`review/tooling/fresh_rebuild.sh`,
  `review/tooling/DumpDecls.lean`; `review/out/fresh_rebuild.txt`,
  `decls_frozen.txt` = `decls_fresh.txt`);
- `leanchecker` replay of all 15 modules of the frozen build: exit 0
  (`review/out/leanchecker.txt`, 7 min 46 s).

Two smaller points. The exit status of `lake build` is discarded by the
pipeline in step 3; the reviewer could not turn this into a false pass, because
Lake 5.0.0 removes a module's old `.olean` before recompiling it
(`Lake/Build/Module.lean`, `clearOutputArtifacts`; by reading the source, not
by running `lake build`), so the audit import then fails. And nothing checks
that every file under `VoltageToBit/` is imported by the root module; a file
outside the import closure is neither built nor audited (all 14 are imported
at this commit).

**Disposition.** Add a kernel replay to `check.sh`; forbid the tokens listed
above; fail on the build's own exit status; assert that the number of source
files equals the number of modules audited.

**Status at `9b13e95`.** Still open (script unchanged; `README.md` says "Not
replayed through an independent checker"). The reviewer's rebuild and replay of
`9b13e95` are reported in §2.4.

### E1-09 (S5). `gen_design.py` trusts the JSON more than it says

**Probe.** `review/tooling/gen_design_probe.py "$F" <scratch>`; observed
(`review/out/gen_design_probe.txt`): `--check` passes on the frozen record;
the generator exits 0 for (1) a number string with a trailing newline, (2) a
non-ASCII digit (Lean would then fail to parse, so this fails closed), (3) a
`status` string containing `-/`, which puts arbitrary Lean code outside the
doc comment (`theorem injected_from_json : True := trivial` appears in the
output), (4) a duplicated key (the last one wins silently, so a consumer in
another language could read a different number), (5) inverted bounds (rejected
only later, by the Lean proof).

**Disposition.** Escape or reject `-/` in `name` and `status`; use
`re.fullmatch` with `[0-9]`; reject duplicate keys. Low priority: the JSON is
written by the project.

**Status at `9b13e95`.** Still open (script unchanged).

### E1-10 (S5). Prose and docstrings that differ from the checked statements

| # | Where | Prose | Checked statement | At `9b13e95` |
| --- | --- | --- | --- | --- |
| a | `interface.md` §6 | input valid on `[s, e]` | `Ico s e` (the Lean is stronger) | fixed |
| b | `interface.md` §3 | "`V_tp > 0`" | `Admissible` has no sign condition on any threshold | open |
| c | docstrings of `Design.Iup`, `Design.Idn` | margin available "whenever `u ≤ VIL` and `v ≤ c`" (resp. `VIH ≤ u`, `c ≤ v`) | needs `c ≤ VDDlo` (resp. `0 ≤ c`); without it false: `Review.P05.Iup_not_a_bound_above_VDDlo`, `Idn_not_a_bound_below_zero` | open |
| d | docstring of `nominal` | "the centre of the box" | thresholds 0.5, centre 0.525 (`Review.P07.nominal_not_centre`) | open |
| e | `Device.lean`, `ModelError.lean`, `interface.md` | "see `docs/model.md`", "`docs/assumptions.md`" | files absent at `1880a36` | fixed; new dangling links in `README.md` (E2-04) |
| f | `interface.md` §6 | "six current-margin inequalities" | four of the six formulas and the role of `uHi`, `uLo` not given | fixed |
| g | `Existence.lean` header | "time-dependent capacitance" covered | see E1-07 | reworded ("slowly varying") |

### E1-11 (S5). Numbers that are meaningful only under `Admissible`

`Review.P07.noisy_tauUp_negative`: `noisy.tauUp < 0`.
`Review.P07.zeroMargin_tauUp`: for the record with `eps = Iup VOH` exactly,
`tauUp = 0` (Lean's `x / 0 = 0`). `Review.P07.decode_inverted_never_undefined`:
with inverted thresholds the decoder has no undefined band. No theorem is
affected (all carry `Admissible`), but a harness or search loop that ranks
candidate records by `tauUp` without checking admissibility first would prefer
both broken records to the admissible one.

**Disposition.** Say so next to the definitions and in the experiment record
format. **Status at `9b13e95`.** Open (definitions unchanged).

## 1.3 Quantifier structure of the headline theorems

All statements are for reals; `Icc` closed, `Ico` half-open. "adm" = `D.Admissible`.

| Theorem | For all | Assumes | Concludes | Can the conclusion be empty? |
| --- | --- | --- | --- | --- |
| `IsTrajectory.safe` | `D θ u v a b` | adm, `InBox θ`, trajectory on `[a,b]`, `v a ∈ Safe` | `∀ t ∈ Icc a b, v t ∈ Safe` | only if `b < a` |
| `IsTrajectory.rise` | same, `s e` | same, `a ≤ s`, `e ≤ b`, `u ≤ VIL` on `Ico s e` | `∀ t ∈ Icc s e, s + tauUp ≤ t → VOH ≤ v t` | yes when `e < s + tauUp` (window shorter than the deadline) or `e < s`; harmless (`Review.P05.rise_window_empty`) |
| `IsTrajectory.fall` | mirror | `VIH ≤ u` on `Ico s e` | `v t ≤ VOL` from `s + tauDn` | same |
| `IsTrajectory.decoded` | same, `inBit` | `decodeIn (u t) = some inBit` on `Ico s e` | `decodeOut (v t) = some (!inBit)` from `s + tau inBit` | same; `tau` hides nothing (`if inBit then tauDn else tauUp`) |
| `exists_solution` | `D θ C u w a b v₀` | adm, `InBox θ`, `Clo ≤ C`, `u`, `w` continuous on ℝ, `a ≤ b`, `abs w ≤ eps` on `Icc a b`, `v₀ ∈ Safe` | `∃ v`, `v a = v₀`, safe, derivative `(Inet + w)/C` within `Icc a b` at every `t ∈ Icc a b` | no |
| `exists_trajectory` | same | also `C ≤ Chi` | `∃ v, v a = v₀ ∧ IsTrajectory` | no |
| `IsTrajectory.of_ode` | `D θ u v a b Cf w` | `Cf` within `[Clo, Chi]` for **all** arguments, `abs w ≤ eps` on `Ico`, continuity, equation with a right derivative at every `t ∈ Ico a b` | `IsTrajectory` | no adm needed |
| `IsTrajectory.of_model_error` | `J w εm εw` | `εm + εw ≤ eps`, `abs (J - Inet θ) ≤ εm` on `Safe` for the fixed `θ`, `abs w ≤ εw`, equation | `IsTrajectory` | hypothesis unsatisfiable for a modulated law (E1-02) |
| `rise_of_cert`, `fall_of_cert` | list `c :: cs`, `τ` | `ValidRiseCert c cs τ` (levels nondecreasing from `Vlo`, positive slope bounds, last level `VOH`, time `≤ τ`) | as `rise` with `τ` | no cert exists below the model's worst case (`no_riseCert_at_2p16`) |
| `rise_at_most` | `ulo uhi l` | input in `[ulo, uhi]` on `Ico s e`, `v s ≤ l` | `v t ≤ l + slope (t - s)` on `Icc s e` | no |
| `exists_rise_run`, `exists_fall_run` | every adm `D` | adm | `∃ θ u v`, in box, trajectory on `[0, tau + 1]` from the opposite valid level, valid input always, conclusion on `[tau, tau + 1]` | no; window has length 1 |
| `illustrative_guarantee` | `θ u v a b` | in box, trajectory, `v a ∈ [-0.10, 2.08]` | the three properties with 3.43 and 2.57 | as above |
| `illustrative_scenario` | (closed) | none | `∃ v`, `v 0 = 1`, ODE, trajectory, safe, low on `[2.57, 4]`, high on `[7.59, 10]` | no |
| negative controls | (closed) | none | as their docstrings say, except header item 2 (E1-04) | no |

No off-by-one in time was found: deadlines are inclusive (`s + tau ≤ t`), the
conclusion includes `t = e` although the input is only constrained on
`[s, e)`, which is sound because `v` is continuous at `e`.

## 1.4 Attacks that failed (the development survived)

| # | Attack | Result | Evidence |
| --- | --- | --- | --- |
| A1 | Stale or doctored build products | fresh rebuild from source gives the same 383 declarations (type and value hashes); kernel replay exit 0; committed `audit.txt` reproduced | `out/fresh_rebuild.txt`, `out/decls_*.txt`, `out/leanchecker.txt`, `out/audit_frozen.txt` |
| A2 | Hidden instances, notation, simp lemmas, options | none: only auto-generated `_sizeOf_inst` and `injEq` | `out/decls_frozen.txt` (last lines), grep in `run_all.sh` |
| A3 | Definitions hide something | the instance's guarantee and existence restated with `max`, absolute value, `Icc`, `HasDerivWithinAt` only and closed by the library by definitional unfolding | `P06` (`explicit_inclusion_guarantee`, `explicit_end_to_end`, `explicit_decoding`) |
| A4 | Device law: sign errors, wrong device on | agrees with an independently written textbook piecewise model with source/drain chosen by voltage, 200,000 points in `[-1, 3]²`, max difference 4e-13; both devices are one antisymmetric channel formula | `num/n02` part (a); `P06` (`Ich_antisymm`, `In_eq_Ich`, `Ip_eq_Ich`) |
| A5 | The six margins and the deadlines are miscomputed | exact rational recomputation equals all eight Lean values; certificate time 2.33835; contamination slope 28.5508 | `num/n01`, `out/n01.txt` |
| A6 | A box point and voltages where the device current violates a margin theorem | none in 2,000,000 samples per theorem with corners mixed in; `Iup`, `Idn` attained exactly | `num/n02` part (b) |
| A7 | `Admissible` smuggles the conclusion or allows a degenerate record | purely numeric; it forces `Vlo < 0`, `VDDhi < Vhi`, `VOH < VDDlo`, `0 < VOL` although only weak inequalities are stated | `P05` (`Admissible.*`) |
| A8 | A hypothesis is decorative | `v a ∈ Safe` and `InBox θ` cannot be dropped | `P05` (`rise_needs_initial_safe`, `rise_needs_inBox`) |
| A9 | Degenerate intervals give a contradiction | on `b < a` or `b = a` every function is a trajectory and every conclusion is about an empty set; nothing follows | `P05` (`trajectory_of_lt`, `trajectory_of_eq`, `rise_window_empty`) |
| A10 | Certificates can be gamed (empty tail, repeated levels, nonpositive margin, division by zero) | a certificate has at least one level by construction; `RiseSegs` demands positive slope bounds; no valid certificate at or below 2.16 ns exists; infimum equals the model's slowest rise | `P03` (`no_riseCert_at_2p16`), `num/n03` |
| A11 | Non-vacuity theorems exhibit less than they say | they exhibit what the docstrings say; in addition the least favourable run (weak corner, largest capacitance, adverse constant disturbance) exists and satisfies the conclusion | `P03` (`rise_deadline_2p16_is_false`, last conjunct) |
| A12 | The "noisy" and "miswired" controls are unfair | `weakCorner` is in the box; the stuck point needs 40·(0.62² − 0.34²) = 10.752 ≤ 10.76 µA; `InetSwapped` is the exchanged network; the failure holds for all trajectories | `P08`; the library's `weakCorner_inBox`, `noisy_counterexample`; hand computation |
| A13 | Model-error theorem is circular | no: the bound is needed on the safe domain only, and invariance is proved from the conditional bound at the two boundary points | reading of `safe`; `P05.lawless_outside_safe` shows what the condition leaves open |
| A14 | Randomised simulation with adverse disturbances breaks the guarantee | 240 runs, 0 violations; node extremes after 1 ns: -0.025 V and 2.003 V (finite coverage, a check of the reading, not evidence for the theorem) | `num/n04`, `out/n04.txt` |
| A15 | Token grep of `check.sh` silently matches nothing on BSD grep (`\b`) | it matches: `printf 'x sorry y\n' \| /usr/bin/grep -nE '<pattern of check.sh>'` prints the line (BSD grep 2.6.0) | run by hand |
| A16 | `gen_design.py --check` out of sync, SHA mismatch | in sync; SHA-256 of the JSON equals the header of the generated file | `out/gen_design_probe.txt`, `out/n01.txt` |

One consequence of A13 worth keeping in view: outside the safe domain the
inclusion constrains nothing (`lawless_outside_safe`). The guarantee is silent
about a node that starts outside `[-0.10, 2.08]` or is carried out of it by
something the model does not contain (E1-03).

## 1.5 Not examined in Part 1

- Mathlib and the Lean toolchain are trusted. The kernel replay re-checks the
  project's own declarations against the imported Mathlib environment; it does
  not replay Mathlib, and it uses the same kernel implementation (the
  independent checkers present in the toolchain were not run).
- `scripts/check.sh` was not executed end to end (no `lake build` was run by
  the reviewer); its steps 1, 2 and 4 were run separately, and step 3 was
  replaced by the reviewer's own rebuild from source.
- No device model, SPICE deck, measurement or external source was consulted.
  All capacitance and modulation values in E1-02 and E1-03 are estimates.
- The old repository, the experiments and the other workstreams' documents
  (absent from this commit) were not examined.
- Emptiness of the trajectory set (E1-01) was proved for nominal parameters at
  this commit; other box points were not treated (Part 2 treats all of them).

---

# Part 2: delta 1880a36..9b13e95

Requested by the coordinator during Part 1. Reviewed: the Lean delta (about
1,000 added lines in 14 files, three of them new: `Proofs/Concat.lean`,
`Proofs/AtSupply.lean`, `Proofs/Chain.lean`), `docs/interface.md` (v1
candidate, rev. 3), `README.md`, `designs/illustrative-1v8.notes.md`. Probes
are `review/D01` to `D05` and are compiled against `$F2`.

## 2.1 Answers to the coordinator's nine points

| # | Claim under attack | Result |
| --- | --- | --- |
| 1 | The per-instant `IsTrajectory` is strictly more general; nothing in `safe` / `rise` / `fall` depends on a constant parameter point | **Holds.** The new definition is literally the one the reviewer wrote independently for Part 1 (`Review.D02.new_iff_reviewer_definition`), for which the reviewer had already re-proved `safe`, `rise`, `fall` (`P04`, Part C). Old trajectories embed (`fixed_implies_new`); the inclusion is strict: `1.65 + 0.1 t` with the input at 0 V is a trajectory now and is not a fixed-parameter trajectory for any box member (`supply_tracking_is_new_trajectory`, `supply_tracking_not_fixed`). P01's conclusion survives, see E2-01. |
| 2 | Sandwich form of the model-error obligation | **Holds, with stated limits.** Satisfiable in a non-trivial case: the channel-length-modulated law, which no fixed box member matches within `eps`, is covered through the library's own `of_sandwich` with `εm = 0` (`Review.D02.clm_not_within_eps_of_any_fixed_member`, `clm_guarantee`). Not circular. It excludes a dead device. Residual scope in E2-05. |
| 3 | Existence for Lipschitz voltage-dependent capacitance; uniqueness | **Holds.** The hypotheses of `solution_unique` are those of Mathlib's `ODE_solution_unique_of_mem_Icc_right` (Lipschitz field, continuity, the equation with a right derivative on `[a, b)`, equal initial values) plus what is needed to show both solutions stay where the clamped field equals the real one (`Cf ≤ Chi`, `abs w ≤ eps`, initial state in the safe domain). Existence is for constant parameters only, as documented. The three statements compose into "exactly one solution, and it has the three properties" without project definitions (`Review.D03.explicit_well_posed`). |
| 4 | Gluing and existence for one jump | **Holds.** The junction is handled correctly (the reviewer had proved the same two lemmas independently in `P02` before seeing this file). The docstring's caveat is accurate; it can be made exact, see E2-01. |
| 5 | Supply-relative safe domain; "the restricted record keeps every other margin"; the extra condition `eps < RhiN'` | **Holds.** All six margins of `atSupply V0` exceed `eps` and are at least those of the record (for `hiN`: at least `RhiN'`) for 361 supply values (`review/out2/n05.txt`); the statement composes (`D03`, last conjunct). The extra condition is redundant for every record with `Vtnhi + Vtphi ≥ 0`, see E2-02. |
| 6 | `IdischargeMax`, `fall_at_most`, the two slew numbers | **Holds.** Mirror image of the rising bound; both numbers exact (28.5508, 58.3144). Wording in E2-03. |
| 7 | Reverse-operation lemmas | **Holds.** With the reviewer's own textbook forward law `shForward k Vt vgs vds`, the twelve region lemmas are exhaustive and say `In = shForward` for `v ≥ 0`, `In = -shForward (u - v) (-v)` for `v ≤ 0`, `Ip = shForward (VDD - u) (VDD - v)` for `v ≤ VDD`, `Ip = -shForward (v - u) (v - VDD)` for `v ≥ VDD` (`Review.D04.In_forward`, `In_reverse`, `Ip_forward`, `Ip_reverse`). Signs and region boundaries are right. |
| 8 | Two stages in series; docstring caveats | **Holds; a witness was missing.** See E2-03. The caveats' numbers are right (2 / 9 = 0.22 fF; 2 / 58.3 = 0.034 fF). |
| 9 | Prose against statements | Mostly brought into line (see the status column of §1.1). Residual items in E2-04. The arithmetic of the notes file was re-done and is right (the six margins, "16 %", the budget sum of 2.0 µA, 0.9 ns for a full swing at 2 V/ns, 10 µA at 20 V/ns and 0.5 fF); its physical inputs were not examined. Of the back-quoted identifiers in `README.md`, `docs/interface.md`, `docs/assumptions.md`, `docs/model.md` and the notes file, 74 resolve to declarations; the 37 that do not are symbols of the prose (`V_IL`, `C_M`, ...), one cell name and one expression (`illustrative.Admissible`). No dangling theorem reference (`review/out2/doc_names.txt`). |

No S1 and no whole-statement S2 was found in the delta.

## 2.2 New findings

| ID | Class | Finding |
| --- | --- | --- |
| E2-01 | S3 | The emptiness for left-continuous jumps survives the per-instant definition, for every initial state; three places still advertise "every input" without the caveat |
| E2-02 | S5 | The "one extra numeric condition" `eps < RhiN'` is automatically true whenever `Vtnhi + Vtphi ≥ 0`; the supply-relative domain is a statement about constant-supply runs only |
| E2-03 | S3 | The two-stage corollary had no witness in the library; the slew figures quoted in its caveat are bounds for restricted input ranges, not "largest slews" of the guarantee's input class |
| E2-04 | S5 | Residual prose defects in `README.md`, `interface.md` and docstrings |
| E2-05 | S3 | What the sandwich obligation does not give (existence for the other model; an unbounded input set; absolute agreement where the box hull is a single point) |

### E2-01 (S3). P01 under the per-instant definition

The coordinator asked whether P01's conclusion survives and for which states.
It does, with a narrower window at the jump and the same global conclusion.

- `Review.D01.no_trajectory_through_left_continuous_jump`: if the input is
  1.8 V at the instant `t0` and 0 V on `(t0, t0 + 0.002)`, no trajectory of the
  illustrative record passes through `(t0, v t0)` with `v t0 ∈ [-0.02, 0.25]`.
  Whatever box points are used, the balance at `t0` caps the right derivative
  at 1.72 V/ns (strongest NMOS of the box conducting in reverse, at most
  6.6 µA), while just after `t0` it is at least 1.98 V/ns (weakest PMOS of the
  box saturated, at least 41.616 µA). In P01, with nominal parameters fixed,
  the window was `[-0.06, 0.25]`.
- `Review.D01.stepL_no_trajectory`: for `uStepL` (high for `t ≤ 4`, low after)
  there is no trajectory on `[0, 10]` from **any** initial state in the safe
  domain: every trajectory is in `[-0.02, 0.25]` at `t = 4`.
- `Review.D01.spike_no_trajectory`: the single-instant variant, for initial
  outputs in `[-0.02, 0.25]`.
- `Review.D01.stepR_has_trajectory`: the library's `exists_trajectory_step`
  gives trajectories for the right-continuous twin from every initial state.

For a jump at which the two derivative ranges overlap (a small jump, or a
state near the edge of the safe domain) trajectories can exist; "in general no
trajectory exists" in `Proofs/Concat.lean` and `docs/interface.md` §6 is
therefore accurate. Still unqualified: `README.md` ("every input waveform (no
regularity assumed) ... Trajectories are proved to exist ..., so the statement
is not vacuous"), `docs/interface.md` §1 ("an arbitrary real-valued function
of time"), and the header of `Proofs/Guarantee.lean`.

**Probe.** `review/D01_JumpInput_PerInstant.lean`; observed: 3 axiom lines, all
standard. **Disposition.** Qualify the three sentences; optionally cite the
compiled statement in place of "in general".

### E2-02 (S5). The extra condition of `AtSupply` is redundant for ordinary records

`Review.D04.RhiN'_eq_RhiN`: for an admissible record with
`0 ≤ Vtnhi + Vtphi`, `RhiN' = RhiN`. (Admissibility of `hiP` forces
`uHi < VDDlo - Vtphi + (Vhi - VDDhi)`, so with nonnegative threshold sum the
NMOS is saturated at both tops and the two numbers coincide.) Hence
`eps < RhiN'` follows from `hiN` (`atSupply_condition_is_automatic`) and the
supply-relative theorem holds with no extra condition
(`solution_safe_atSupply_of_admissible`). For the illustrative record both are
2.312. The condition can only bite for records with a negative threshold sum,
which `Admissible` does not exclude although `docs/interface.md` §3 says
`V_tp > 0` (E1-10b).

Scope note: `solution_safe_atSupply` is about solutions with constant
parameters. It extends to every trajectory of the restricted record, where the
other parameters may still move (`Review.D04.trajectory_safe_atSupply`), but
not to the per-instant reading with a moving supply that `docs/interface.md`
§4 and `README.md` advertise: for that class only the fixed domain
`[-0.10, 2.08]` is proved. "The physical claim should be read with this
tighter domain" (`interface.md` §6) is true for constant-supply runs.

Numbers (`review/out2/n05.txt`): true minimum inward current at the
supply-relative top `VDD + 0.10`: 3.56 µA (the notes file says "about 3.6 µA");
proved bound 2.312 µA.

**Disposition.** Either add `0 ≤ Vtnlo`, `0 ≤ Vtplo` to `Admissible` and drop
the hypothesis, or keep it and say it is automatic for nonnegative thresholds.

### E2-03 (S3). The two-stage corollary: no witness in the library, and what the slew figures mean

- `Proofs/Chain.lean` proves four implications and no existence statement. The
  second stage's input is the first stage's output, which the existence
  theorem does not accept directly (it wants an input continuous on all of ℝ).
  `Review.D04.chain_witness` builds an actual run of the illustrative record:
  both stages start at 1.0 V, the first input is held at 0 V, and the second
  output is valid-low on all of `[6, 10]`. So the attack "the corollary is
  vacuous" failed, but the library should carry such a witness itself.
- The caveat in `Proofs/Chain.lean` says the first stage's output "may slew at
  up to about 29 V/ns rising and 58 V/ns falling". Those figures
  (`illustrative_max_rise_slew`, `illustrative_max_fall_slew`) are upper bounds
  for first-stage inputs in `[0, 0.40]` and `[1.25, 1.98]`; the true suprema
  there are 28.49 and 56.58 V/ns (`review/out2/n05.txt`), and for the
  guarantee's own input classes (`u ≤ VIL`, `VIH ≤ u`, no range) the slew is
  unbounded (E1-03). The docstrings of the two theorems say "Largest ... slew".
  The caveat therefore understates, in the direction that matters, how far a
  second stage is from the 2 µA allowance.

**Disposition.** Add the witness; write "an upper bound on the slew for inputs
in ..." in the two docstrings and in the caveat.

### E2-04 (S5). Residual prose defects at `9b13e95`

| Where | Defect |
| --- | --- |
| `README.md`, "The claim" | "every input waveform (no regularity assumed) ... so the statement is not vacuous" without the jump caveat (E2-01) |
| `README.md`, status table and "Where to look" | links or paths that do not exist at this commit: `docs/discrepancy-report.md`, `docs/experiment-loop.md`, `docs/adversarial-review.md`, `experiments/`, `search/` (they are untracked files of the working tree, so a checkout of `9b13e95` has dead links) |
| `README.md`, instance table | "(refined: see below)": nothing below mentions the refined 2.34 ns |
| `README.md`, "Where to look" | `Proofs/Contamination.lean` described as "a minimum rise delay" (now both directions); `Proofs/Concat.lean` and `Proofs/AtSupply.lean` not listed |
| `README.md`, "Reproduce" | "`scripts/check.sh` stops at the first failure": a failing `lake build` does not stop it at step 3 (E1-08) |
| `Examples/NegativeControls.lean` header | item 2 unchanged (E1-04) |
| docstrings of `Design.Iup`, `Design.Idn`, `nominal` | unchanged (E1-10 c, d) |
| `exists_solution`, `IsTrajectory.of_ode` | the capacitance bounds are required for all real arguments, not only on the safe domain; harmless, but a capacitance model known only on the safe domain has to be extended first |

### E2-05 (S3). What the sandwich obligation does not give

`IsTrajectory.of_sandwich` is correct and useful. Three limits should be stated
next to it, because `README.md` calls it "the precise obligation a device
model or a measurement would have to meet":

1. It is a statement about solutions of the other model if there are any.
   Existence for a current law `J` that is not a square law with constant
   parameters is not proved (for the modulated law of `D02` it would need its
   own argument).
2. The hypothesis must hold at the input values that actually occur. No
   statement bounds the input, so the obligation ranges over an unbounded set
   unless the environment restricts `u` (E1-03).
3. Where all box members agree the hull is a single point and the other model
   must agree with it to within `εm` in absolute terms. Two such places in the
   illustrative record: the NMOS current is exactly zero in every box member
   for `u ≤ 0.45`, and the net current is exactly zero at `v = 0` for
   `u ≥ 1.53`. Conduction below threshold at `u = V_IL = 0.40` is the case in
   point; the notes file budgets 0.3 µA for it, unproved.

The obligation is not circular, and it does exclude a device that does not
drive the node: at input 0 V every box member delivers at least 41.616 µA for
a node in `[-0.10, 0.45]` (`Review.D01.Inet_low_ge`), so `J = 0` fails the
lower bound by 39.6 µA.

## 2.3 Attacks on the delta that failed

| # | Attack | Result | Evidence |
| --- | --- | --- | --- |
| B1 | Build products of `9b13e95` do not match the source, or bypass the kernel | fresh rebuild of all 17 modules gives the same 433 constants (127 definitions, 291 theorems) with identical type and value hashes; project audit reproduces the committed `audit.txt`; `leanchecker` replay of 18 modules exits 0; no instance, notation, option, macro in the sources | `out2/slow_checks.txt`, `out2/decls_*.txt`, `out2/leanchecker.txt`, `out2/run_part2.txt` |
| B2 | The new definition hides a dependence on a constant parameter point | it equals the reviewer's independent definition; old trajectories embed; inclusion strict | `D02` |
| B3 | Existence, uniqueness and the supply-relative domain do not compose as the prose says | they do, for explicit numbers and Mathlib notions only | `D03` |
| B4 | Gluing is wrong at the junction | no; independently re-derived | `P02`, `D01.stepR_has_trajectory` |
| B5 | The restricted record loses a margin | no, 361 supply values, exact arithmetic | `num/n05` part (a) |
| B6 | The per-instant choice of the box point makes the slowest run slower than the fixed worst corner | no: 2.251190 ns either way (the worst corner does not depend on the state here) | `num/n05` part (d) |
| B7 | Reverse-operation lemmas have a wrong sign or leave a gap | no | `D04` part C; `num/n02` part (a) |
| B8 | The two-stage corollary is vacuous | no (witness) | `D04` part B |
| B9 | The sandwich admits a device that is not an inverter | no (41.6 µA lower bound) | `D01.Inet_low_ge` |
| B10 | Part 1 probes that do not mention trajectories break at the new commit | `P07`, `P08` compile unchanged | `out2/P07_LeanConventions.txt`, `out2/P08_MiswiredUniversal.txt` |
| B11 | Lean names quoted in the prose do not exist | 74 resolve; the rest are prose symbols, none a theorem name | `out2/doc_names.txt` |

## 2.4 Not examined in Part 2

- `docs/model.md` (1,098 lines) and `docs/source-audit.md` (1,167 lines) were
  not read. Only the Lean names quoted in `model.md` and `assumptions.md` were
  checked to resolve. In particular not verified: the ngspice Level 1 claim of
  `interface.md` §3, the budget table of the notes file, the SKY130 comparison,
  the thermal-noise figure, Appendix B of `model.md`.
- `docs/assumptions.md` was not reviewed as an assumption register (statuses,
  consumer theorems, evidence types).
- Existence of trajectories for parameters that move in time, and for any
  current law other than the square law with constant parameters.
- Mathlib, the toolchain and independent kernel implementations: as in Part 1.
  `scripts/check.sh` was again not executed end to end.
- Anything outside the commit (`experiments/`, `search/`, the working tree
  after `9b13e95`).

---

# Recommended order of work

1. **State the input class.** Qualify "every input" wherever it still stands
   (`README.md`, `interface.md` §1, `Guarantee.lean` header), and put an input
   range and slew bound into the environment assumptions of the statements a
   physical reading relies on (E1-01, E1-03, E2-01, E2-05).
2. **Make the controls probe the boundary.** Replace the 38 ps sentence, adopt
   the worst-case runs as negative controls in both directions, instantiate a
   falling certificate, and quote each deadline with its bracket: rise false at
   2.16 ns, proved at 2.34 ns; fall false at 1.0 ns, proved at 1.51 ns
   (E1-04, E1-05, `review/D05_Part1Ports.lean`).
3. **Make `check.sh` establish what it says.** Add the kernel replay and the
   forbidden constructs, fail on the build's own status, assert the import
   closure (E1-08). Until then "the kernel accepted every declaration" rests on
   this review's manual replay of the two snapshots.

After that, the best single improvement is a boundary proof that counts both
transistors (E1-06): it would raise the provable allowance from 2.312 µA
towards 3.56 µA (supply-relative top) without changing the circuit.

# Reproduction

```sh
cd "$R"
review/run_all.sh  "$F"            # Part 1: probes, audit, numeric and tooling checks (several minutes)
review/run_all.sh  "$F" --slow     # plus fresh rebuild from source and kernel replay (about 10 minutes more)
review/run_part2.sh "$F2"          # Part 2: probes, source and prose checks (several minutes)
review/run_part2.sh "$F2" --slow   # plus fresh rebuild, audit and kernel replay (about 12 minutes more)
```

The slow checks reported in this document were run once each, separately
(`review/out/fresh_rebuild.txt`, `review/out/leanchecker.txt`,
`review/out2/slow_checks.txt`).

| Path under `review/` | Content |
| --- | --- |
| `P00` to `P08` `*.lean` | Lean probes for Part 1 (compile against `$F`) |
| `D01` to `D05` `*.lean` | Lean probes for Part 2 (compile against `$F2`) |
| `num/n01` to `n05` `*.py` | numeric probes (fixed seeds; no project code imported) |
| `tooling/fresh_rebuild.sh`, `DumpDecls.lean` | rebuild from source into a scratch directory; declaration inventory |
| `tooling/AuditGapDemo.lean` | the kernel-bypass demonstration; it deliberately declares a "theorem" of `False` and imports nothing from the library; keep it outside the library's import closure |
| `tooling/gen_design_probe.py` | generator behaviour on unusual JSON |
| `tooling/DocNames_9b13e95.lean` | Lean names quoted in the prose |
| `tooling/part2_slow_checks.sh` | rebuild, audit and replay for `9b13e95` |
| `out/`, `out2/` | captured outputs of the runs reported here |

Observed final lines of the two fast runs: `ALL REVIEW PROBES RAN AS RECORDED`
(`review/out/run_all.txt`) and `ALL PART 2 PROBES RAN AS RECORDED`
(`review/out2/run_part2.txt`); both checkouts were clean afterwards.

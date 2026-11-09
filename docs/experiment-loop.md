# The experiment loop: propose, screen, check, evaluate, record

Owner: workstream F. First iteration run on 2026-11-09 against the Lean library
at commit `1880a3619453d865a04f3b32d25edf69af618501` (the frozen checkout).

Everything in this document is about the **mathematical model** of the inverter
and about what **Lean proves** for it. None of it is evidence about a physical
device: the design numbers are illustrative.

Results of the first iteration are in `evidence/search/summary.md` (generated).
This document describes the mechanism and the record format, and states the
headline results in §12.

## 1. Purpose

A proposed improvement is kept only if all three of these hold:

1. it is a number with a stated direction (a deadline to minimise, a disturbance
   bound to maximise);
2. it is claimed under exactly the assumptions of the result it replaces;
3. a checker that does not trust the proposer accepts it.

The loop enforces these mechanically. A proposal goes through five steps:

```text
propose  ->  screen  ->  formal check  ->  evaluate  ->  record
(untrusted)  (exact,     (Lean, frozen     (compare with   (one JSON line,
             cheap)       commit)           incumbent,      kept whatever
                                            numerics)       the outcome)
```

Rejected proposals and counterexamples are recorded with the same care as
accepted ones.

## 2. Who is trusted

| Component | What it does | Trusted? |
| --- | --- | --- |
| Lean, with the library at the frozen commit | decides whether a claim holds | Yes. It is the only arbiter. |
| Proposer (search, random draw, simulation, a person, a model) | suggests a claim | No. |
| Screen (`search/v2bsearch/exact.py`) | evaluates the same numeric conditions in exact rational arithmetic | No. It can reject a proposal without a Lean run. It can never accept one. |
| Numerics (`search/v2bsearch/numeric.py`) | quadrature and simulation of the model | No. It can stop the run (§9). It can never accept a proposal. |
| Driver (`search/run_search.py`) | orchestrates, compares, writes records | Its decisions can be recomputed from the record and the stored Lean outputs. |

Limits of "Lean decides": the check is a normal `lean` run against compiled
library files, with an axiom check on each stated theorem. It is not a replay
through an independent kernel, and it says nothing about whether a statement
means what the prose says. Read the statements.

An axiom check does not reveal a declaration added with the kernel check
switched off by an option (adversarial review, finding E1-08). Two things keep
that out of the generated files: the only text a proposer contributes is plain
decimals (anything else is refused before a file is written), and every
generated file is scanned for the words that could bypass or weaken checking
(`set_option`, `sorry`, `native_decide`, `unsafe`, `axiom`, `macro`, `elab`,
`attribute`, `instance` and the like). A kernel replay of the generated files
is not done; statements promoted into the library come under the library's own
checks.

## 3. One pass, step by step

**Propose.** A proposer returns a claim as decimal strings. For the deadline
experiments a claim is a list of voltage levels and a deadline `tau`. For the
disturbance experiment it is a bound `eps` and two split points.

**Screen.** The screen evaluates, with `fractions.Fraction`, the conditions that
Lean will check: for a certificate, the three conjuncts of `ValidRiseCert` /
`ValidFallCert` (levels ordered with positive slope bounds; last level equal to
the output threshold; summed segment times at most `tau`); for a design record,
the 24 fields of `Design.Admissible`. Division follows Lean (`x / 0 = 0`).
If the screen finds the claim invalid, the proposal is rejected and Lean is not
run, unless the proposal is a control marked `bypass_screen` (§10).

**Formal check.** One small Lean file per claim is generated under
`search/lean/` and checked from the frozen checkout (§7). If Lean rejects the
claim, up to two follow-up files are generated and checked: the *negation* of
the claim, and, for a deadline below the Lean-proved floor, an explicit
*trajectory that violates the deadline*.

**Evaluate.** Three things, in this order:

1. *Soundness guard.* A Lean-accepted deadline below the model's numerical
   worst-case delay, or a Lean-accepted `eps` above the model's numerical
   tolerance, stops the run with exit status 2. One of the two is then wrong.
2. *Improvement.* The claimed value is compared, as an exact decimal, with the
   incumbent (the last accepted record of the same experiment). Strictly better
   means accepted; otherwise the record says "valid, not improving".
3. *Agreement.* The screen and Lean must agree on validity and, for an invalid
   claim, on exactly which conditions fail. A disagreement makes the run exit
   with status 1.

**Record.** One JSON object is appended, whatever the outcome (§5).

Proposals are processed in *generations*. Inside a generation the Lean checks
run in parallel and the proposers see only what earlier generations
established; evaluation is then done in a fixed order. This keeps the loop
closed (later proposers use Lean-verified state) and the run deterministic.

## 4. Frozen experiments

Each experiment has a *context*: a JSON object stored in every record and
identified by its SHA-256 (`context_sha256`). It contains the design file and
its SHA-256, the commit of the Lean library, the toolchain and Mathlib revision,
the objective and its direction, the form of the claim, what is free, what is
held fixed, and the rule for acceptance.

| Experiment | Objective | Free | Held fixed |
| --- | --- | --- | --- |
| `rise-deadline` | minimise the `tau` for which Lean proves `illustrative.ValidRiseCert c cs tau` | the levels `c :: cs`, and `tau` | the whole design record (all 21 numbers, including `eps` and the split points), the device law, the trajectory notion, the theorem statements |
| `fall-deadline` | minimise the `tau` for which Lean proves `illustrative.ValidFallCert c cs tau` | the levels, and `tau` | the same |
| `eps-tolerance` | maximise the `eps` for which Lean proves `({ illustrative with eps := eps, uHi := x, uLo := y }).Admissible` | `eps`, `uHi`, `uLo` | the 18 other numbers of the record, the device law, the trajectory notion, the theorem statements |

Rules that follow from this:

- Two records are comparable only if their `context_sha256` are equal. The
  consistency check (`record.verify`) refuses a parent or baseline from another
  context.
- Any edit to the design file changes its SHA-256, hence the context hash. The
  uncertainty region, the thresholds and the safe domain cannot be changed
  inside an experiment without that being visible.
- A deliberate change of scope is a new experiment with a new identifier.
- A proposal that stops short of the output threshold, or that only works for
  a smaller `eps`, is not a valid claim of the experiment and is rejected.

**The `eps-tolerance` experiment changes the claim.** A larger `eps` enlarges
the set of trajectories the theorems quantify over, and it lengthens the
record's own closed-form deadlines `tauUp` and `tauDn`. Its result reads "the
proof supports a larger disturbance bound for the same circuit". It is a
different statement from the `eps = 2` guarantee, not an improvement of it.
The split points `uHi` and `uLo` occur only in the admissibility conditions
`hiP`, `hiN`, `loN`, `loP`; they are not circuit or environment parameters,
which is why they may be free here.

## 5. Record format

File: `search/records/records.jsonl`, copied to `evidence/search/records.jsonl`.
JSON Lines: one record per line, UTF-8. Schema tag `v2b.experiment-record/1`.
All numbers that are compared are decimal strings or `p/q` strings (exact).

| Field | Content |
| --- | --- |
| `schema` | `"v2b.experiment-record/1"` |
| `record_id` | `<experiment prefix>-<sequence>-<slug>`, unique in the file, e.g. `rise-017-dp-n16` |
| `experiment_id` | `rise-deadline`, `fall-deadline` or `eps-tolerance` |
| `generation` | 0 for the baseline; later generations see the results of earlier ones |
| `parent_id` | the incumbent this proposal was compared with (`null` for the baseline) |
| `baseline_id` | the baseline record of the experiment |
| `context_sha256`, `context` | the frozen context (§4), in full, and its hash |
| `proposer` | `name`, `kind`, `params`, `seed` of whoever or whatever proposed it |
| `proposal` | the claim: `kind`; for certificates `direction`, `levels`, `tau`, `tau_source`; for `eps` proposals `eps`, `uHi`, `uLo`; and a `note` |
| `screen` | `tool`, `valid`, `conditions` (one boolean per condition), `first_failure`, `detail`, `bypassed`; for certificates also `exact_sum` (`p/q`) and `exact_sum_decimal` |
| `formal_checks` | list, one entry per Lean file checked (below); empty if the screen rejected and was not bypassed |
| `numerical_evidence` | the numerical quantities consulted in the evaluation, each labelled as numerical |
| `objective_value` | for Lean-accepted claims: `symbol`, `unit`, `value` (decimal string); for certificates also `exact_certificate_sum` |
| `decision` | `accepted`, `rejected` or `counterexample` (§6) |
| `reason_code`, `reason` | machine-readable code and one or two sentences |
| `rejected_by` | subset of `screen`, `screen (bypassed)`, `lean`, `evaluation` |
| `control` | for deliberately bad proposals: `expected` and whether it was `met`; otherwise `null` |
| `screen_agrees_with_lean` | `true`, `false`, or `null` if Lean was not run |
| `timestamps` | `proposed_utc`, `decided_utc` (wall times of the checks are in the run manifest) |
| `content_sha256` | SHA-256 of the canonical JSON of the record without `timestamps` and without this field |

Each entry of `formal_checks`:

| Field | Content |
| --- | --- |
| `role` | `claim`, `refutation` or `counterexample` |
| `statement` | what the file states, in one line |
| `lean_file`, `lean_file_sha256` | the generated file (kept) and its hash |
| `command` | the exact command, with `$FROZEN` and `$R` for the two checkout paths |
| `exit_status` | exit status of `lean` |
| `output_file`, `output_sha256` | the captured output (kept) and its hash |
| `error_count`, `warning_count`, `first_error`, `unsolved_cases` | what Lean reported |
| `failed_conditions` | (claims only) the conditions Lean left unsolved, named as in `screen.conditions` |
| `theorems`, `axioms` | every theorem stated in the file and the axioms `#print axioms` reported for it |
| `passed` | exit status 0, no error, and every theorem within `propext`, `Classical.choice`, `Quot.sound` |

Formula values are never ranked on their own. `riseTime`, `fallTime`, `tauUp`
and `tauDn` mean a deadline only when their validity conditions hold; outside
them the same formulas return nonsense that looks attractive (a negative
margin gives a negative time, and Lean's `x / 0 = 0` gives zero). The record
therefore separates three things: `screen.exact_sum` is the formula value,
valid or not; `objective_value` exists only for a claim Lean accepted; and only
`objective_value` is compared with the incumbent. The control
`ctl-margin-below-eps` exercises this: its formula value is negative, and Lean
rejects it (adversarial review, finding E1-11).

Determinism. A record is a function of the frozen context and the fixed seeds,
except for `timestamps`. Two runs are compared by `content_sha256`. The actual
paths behind `$FROZEN` and `$R`, tool versions and wall times are in
`search/records/run_manifest.json`, which is not deterministic and not part of
the record. Captured Lean output is stored with the repository path removed, so
its hash does not depend on where the repository lives.

## 6. Decisions

| `decision` | `reason_code` | Meaning |
| --- | --- | --- |
| `accepted` | `baseline` | Lean proved the baseline claim. |
| `accepted` | `improves_incumbent` | Lean proved the claim and the objective is strictly better than the incumbent's, in the same frozen context. |
| `rejected` | `screen_invalid` | The exact screen found the claim invalid. Lean was not run. |
| `rejected` | `valid_not_improving` | Lean proved the claim, but it is not better than the incumbent. |
| `rejected` | `lean_rejected_and_refuted` | Lean rejected the claim and proved its negation. The proposal cannot justify its number. This does not show that the circuit violates the number. |
| `rejected` | `lean_rejected` | Lean did not accept the claim and no negation was proved. |
| `counterexample` | `claimed_bound_false` | Lean rejected the claim and checked an explicit trajectory of the model that violates the claimed deadline. The bound is false for the model. This is never an improved guarantee. |

The distinction between the last three matters. "The certificate does not
support `tau`" is weaker than "`tau` is false". A deadline can be true for the
model and still out of reach of every certificate (§12 has an example).

## 7. The formal check

```sh
cd "$FROZEN" && lake env lean "$R/search/lean/<record_id>.<role>.lean"
```

`$FROZEN` is a checkout of the library at the frozen commit, already built;
`$R` is this repository. Running from `$FROZEN` makes `import VoltageToBit`
resolve to the compiled library of that commit. Before any check the driver
verifies that `$FROZEN` is at the expected commit with a clean work tree, that
`lake build --no-build VoltageToBit` reports every target up to date (nothing
is built or downloaded), and that the Lean design record was generated from the
JSON file whose hash is in the context.

A check **passes** when the exit status is 0, Lean printed no error, and every
theorem stated in the file is reported by `#print axioms` with axioms inside
`propext`, `Classical.choice`, `Quot.sound`. A failed proof shows up as an
error and as `sorryAx`.

Generated files, all under `search/lean/`, outputs under `search/out/`:

| File | States |
| --- | --- |
| `<id>.claim.lean` | the claim, e.g. `theorem rise_017_dp_n16 : illustrative.ValidRiseCert 1.001 [1.055, …, 1.35] 2.2600`; when the screen found it valid, also the exact sum, `riseTime … = p / q`; for the baseline, also that the sum equals the library's `tauUp` / `tauDn` |
| `<id>.refutation.lean` | the negation of the claim; for `eps` at or above the ceiling also `∀ e x y, E ≤ e → ¬ ({ illustrative with eps := e, uHi := x, uLo := y }).Admissible` |
| `<id>.counterexample.lean` | an explicit slow trajectory (existence is proved, not assumed), `rise_deadline_counterexample` / `fall_deadline_counterexample` (no deadline below the floor is valid), `riseCert_deadline_ge` / `fallCert_deadline_ge` (no certificate can claim less), and the negation of the guarantee clause for the proposed `tau` |

Decimal literals in Lean are exact rationals, so `2.2600` means `113/50`.
Deadlines produced by the systematic proposers are the exact certificate sum
rounded **up** to 4 decimals.

The proof scripts are the ones the library itself uses
(`norm_num [..., psq_eq_ite]`). If such a script fails on a true claim, the
claim is simply not accepted; the screen/Lean agreement check then flags it.

## 8. The cheap screen

`search/v2bsearch/exact.py` mirrors, definition by definition, `psq`, `Iup`,
`Idn`, `RhiP`, `RhiN`, `RloN`, `RloP`, `tauUp`, `tauDn`, `Admissible`,
`upSegs` / `dnSegs`, `RiseSegs` / `FallSegs`, `finalLevel`, `riseTime` /
`fallTime`. It reads the JSON design record with the same field table as
`scripts/gen_design.py`.

What it buys: a proposal with an obviously false claim costs microseconds
instead of a Lean run, and the exact sum lets a proposer round a deadline up
correctly. What it does not buy: any trust. In every full run the screen is
compared with Lean on each claim sent to Lean, including on *which* conditions
fail, and Lean confirms the screen's exact sums as equalities.
`python3 search/test_loop.py` also tests it against values the library proves.

## 9. Numerical cross-check

For each direction the model's worst-case delay is computed by quadrature:

```text
T* = max over the box of   ∫ C_max dv / |I_net(θ, u_edge, v) + w_adverse|
```

with the input held at the edge of its valid band (`VIL` for the rise, `VIH`
for the fall), `C = C_max`, the disturbance held at the adverse bound, and the
node travelling from the far end of the safe domain to the output threshold.
Method: 5-point Gauss–Legendre on panels split at the transistor region
boundaries, doubled until converged; all 32 corners of the box; a seeded random
sample of interior and edge points; and an independent Runge–Kutta crossing
time at the slowest corner (agreement required to 1e-8 ns).

Use: every Lean-accepted deadline must be at or above `T*`, and the Lean-proved
floor on valid deadlines (§12) must be at or below it. Otherwise the run stops
("soundness alarm"): the Lean statement, the model in the simulator, or the
quadrature is wrong.

Limits: this is finite floating-point evidence. It does not prove that no
slower trajectory exists. Workstream D's simulator under `experiments/` is not
used.

`T*` takes one parameter point per run, as the trajectory notion of the frozen
commit does. `numerics.json` also reports the delay obtained when the smallest
drive current over the box is used at every voltage, which is the worst case
for a trajectory notion that allows the parameter point to move during a run.

For the disturbance experiment the analogous quantity is the model's smallest
restoring current at each end of the safe domain (minimum over the corners and
a scan of the input). It serves as the same kind of guard.

## 10. Proposers of the first iteration

| Proposer | Kind | What it proposes |
| --- | --- | --- |
| `baseline` | baseline | the single-level certificate, whose sum is the library's closed-form deadline; for `eps`, the record as it is |
| `library-prior` | prior result | the three-level rise certificate already in the library |
| `random-levels` | stochastic search, seeded | random sorted levels; deadline rounded to the **nearest** 0.1 ps; ends off the threshold one time in four. A sloppy numerical proposer: about half of its well-formed claims are too small by a fraction of 0.1 ps |
| `uniform-grid` | search | equally spaced levels, N = 2, 4, 8, 16 |
| `dp-grid` | search | the best N-level certificate with levels on a 1 mV grid, by dynamic programming in floating point, N = 2, …, 64 |
| `adversarial-control` | deliberately bad | a deadline rounded down; levels out of order; a level whose margin is below `eps`; a list that stops short of the threshold; a deadline between the Lean floor and the numerical worst case; a deadline that is true but out of reach |
| `nominal-simulation-predictor` | numerical prediction | deadlines read off simulations of non-worst-case circuits |
| `margin-readout`, `split-search` | search | (`eps`) the largest `eps` below the smallest margin, with the split points unchanged, then re-optimised at 2 to 6 decimals |
| `boundary-scan-predictor` | numerical prediction | (`eps`) what the model appears to tolerate numerically |

Controls are sent to Lean with the screen bypassed. A control that Lean accepts
makes the run fail.

## 11. Running it

```sh
python3 search/test_loop.py                # unit tests of the untrusted parts, no Lean, < 1 s
python3 search/run_search.py               # the whole record: 81 Lean checks
python3 search/run_search.py --check       # the same, then compare with the stored record
python3 search/run_search.py --report-only # no Lean: rebuild evidence/search/ from the stored record
```

The unit tests also check the stored files: every Lean file and every captured
output named in the record must have the recorded SHA-256, and no generated
Lean file may contain a forbidden word. One check takes 9 to 15 s when the
machine is not swapping (most of it is loading Mathlib); the two recorded full
runs took 20 and 24 minutes on a heavily loaded machine.

Options: `--frozen PATH` (default `../frozen-1880a36`, or `$V2B_FROZEN`),
`--jobs N` (parallel Lean checks, default 2), `--skip-freshness`. With
`SOURCE_DATE_EPOCH` set, the timestamps are fixed too and the record file is
byte-for-byte reproducible.

Requirements: Python 3 standard library only; `lake` and the toolchain of the
frozen checkout on the path. Nothing is downloaded, nothing is built, and no
paid service is used.

Exit status: 0 success; 1 inconsistent record, accepted control, screen/Lean
disagreement, or `--check` mismatch; 2 soundness alarm.

A separate script, `python3 search/probe_main.py`, is **not** part of the
record. The library has moved on since the frozen commit (on `main`,
`IsTrajectory` no longer takes a parameter point). The probe restates the
promotion candidate in the current shape and checks it against the build of
this working tree, after verifying that the library sources are committed and
the build is up to date. Its verdict and the commit it refers to are in
`search/promote/main/probe.json`.

Outputs:

| Path | Content |
| --- | --- |
| `search/lean/`, `search/out/` | every generated Lean file and the captured output of its check |
| `search/records/records.jsonl` | the record |
| `search/records/run_manifest.json` | paths, versions, wall times of the last run (not deterministic) |
| `search/records/promotion.json` | the check results of the two packaging files below |
| `search/promote/RefinedDeadlines.lean` | the accepted improvement packaged for the library (two certificates and the guarantee restated with the new deadlines), and its check output |
| `search/promote/Limits.lean` | the limits packaged for the library (floors on both deadlines, the larger-`eps` variant record, the ceiling on `eps`), and its check output |
| `evidence/search/records.jsonl` | copy of the record |
| `evidence/search/summary.md`, `summary.json` | tables derived from the record |
| `evidence/search/numerics.json` | the numerical evidence in full |
| `evidence/search/deadline_gap.svg`, `eps_margins.svg` | two plots |

## 12. First iteration: what came out

The numbers below are copied from `evidence/search/summary.md`, which is
generated; if the two ever differ, the generated file is right. 64 records were
written: 21 accepted, 37 rejected, 6 counterexamples. The record was generated
twice by full runs; the second run reproduced all 64 records (same
`content_sha256` for each). Every statement marked
"Lean" was checked against commit `1880a36`; every statement marked "numerical"
is floating-point evidence about the same model.

**Deadlines (same circuit, same box, same thresholds, same safe domain, same
capacitance range, `eps = 2` µA).**

| | Baseline (single segment) | Best accepted (64 levels) | Suggested for the library (16 levels) | Model worst case (numerical) |
| --- | --- | --- | --- | --- |
| Rise | `7250/2119` ≈ 3.4214 ns, stated as 3.4215 | 2.2533 ns | 2.26 ns | 2.251190 ns |
| Fall | `4575/1787` ≈ 2.5602 ns, stated as 2.5602 | 1.4193 ns | 1.425 ns | 1.392352 ns |

For the rise the frozen library already contained a three-level certificate
with 2.34 ns; measured against that, the improvement is 3.7 %, not 34 %.

What improved is a proved bound for the same model under the same assumptions.
The circuit did not get faster, and no physical evidence was added.

**Limits found (these are results too, and none of them is an improvement).**

- *Lean:* no rise deadline below 2.168 ns and no fall deadline below 1.0234 ns
  is valid for the model. Each is witnessed by an explicit slow trajectory
  whose existence is proved. In particular no certificate can claim less
  (`riseCert_deadline_ge`, `fallCert_deadline_ge`).
- *Numerical:* a deadline taken from a simulation of the typical circuit
  (0.1795 ns rise, 0.1158 ns fall) or of nominal devices under the adverse
  stimulus (0.7380 ns, 0.6855 ns) is too small by a factor between 2 and 12.5.
  Lean rejects each as a certificate claim and also proves each false by a
  trajectory. A plausible prediction is not a proof.
- *Rise, numerical:* the certificate method converges to the model's worst-case
  delay. With 64 levels the proved deadline is 0.0021 ns above it; more levels
  buy almost nothing.
- *Fall, numerical:* the certificate method cannot get below 1.417563 ns, which
  is 0.0252 ns above the model's worst case. A deadline such as 1.405 ns is
  true according to the numerical worst case, and no certificate of this form
  can prove it. The loss is in the margin function `Idn`, which charges the
  PMOS its saturation current even where the node is above `VIH + Vtp` and the
  PMOS has left saturation. Closing it needs a sharper lemma, not a better
  search.
- *Disturbance bound, Lean:* with the split points unchanged the record is
  already admissible up to `eps = 2.3119` (slack that was there before any
  search); re-chosen split points (`uHi = 0.772486`, `uLo = 0.742506`) give
  `eps = 2.3801`, which is what the search itself contributed (+2.9 %); and
  for `eps ≥ 2.3802` no choice of split points makes the record admissible.
  The search over split points is therefore exhausted to four decimals.
- *Disturbance bound, numerical:* the model's own smallest restoring current is
  6.44 µA at the top of the safe domain and 5.92 µA at the bottom. The
  closed-form margins give up more than half of that. A larger provable `eps`
  needs a stronger boundary lemma (one that adds the two transistors'
  contributions instead of using one of them on each side of a split point).

**Direction.** For this record the certificate search is finished: the rise is
at the model's worst case and the fall is at the method's limit. The two places
where proof effort would still buy something are named above, and both are
changes to lemmas in the library, not to the search.

**A caveat about the worst case.** At the frozen commit the parameters are
constant during a run, and the numbers above use that. If the parameter point
may move inside the box during a run (the trajectory notion adopted on `main`
after the frozen commit), the numerical worst-case fall delay is 1.394538 ns
instead of 1.392352 ns; the rise is unchanged. No conclusion above changes.

**Independent agreement.** Two other workstreams computed the same numerical
quantities with their own code, and none of it is used by the loop. Workstream
D (`evidence/experiments/2026-11-09-D-illustrative-1v8-06ccc32a/03_worstcase/worst_case.json`)
has the same worst-case delays, the same slowest corners, the same limits of
the certificate method and, for 1 to 32 levels, the same grid-optimal sums to
the last printed digit. The adversarial review (`docs/adversarial-review.md`,
findings E1-05 and E1-06) has the same worst-case delays (2.2512 ns, 1.3924 ns),
the same boundary minima (6.44 µA, 5.92 µA) and the same best split-point
margins (2.38, 3.08), and its own Lean probes bracket the rise deadline from
below at 2.16 ns and the fall deadline at 1.0 ns, consistent with the floors
here (2.168 ns, 1.0234 ns). That review asked for each deadline to be reported
with its bracket and for a falling certificate; both are in this record.

## 13. What the loop does not establish

- Nothing about a physical inverter. The design numbers are illustrative; the
  device law is a model. A better proved bound for the model is not a faster
  circuit.
- Not optimality. "Best certificate found" is a search result. The only formal
  statements are the validity of each accepted claim and the floors/ceiling
  listed in §12.
- Not the meaning of the statements. The loop checks claims of a fixed form
  against a fixed library; whether that form is the right claim is a matter for
  the model and review workstreams.
- The numerical worst case is evidence, not a theorem.

## 14. Extending it

- A new proposer is a function returning `Proposal` objects
  (`search/v2bsearch/propose.py`). It needs no review: nothing it says is
  believed.
- A new objective is a new frozen context, a claim template in
  `search/v2bsearch/leanio.py`, and a screen for it in `exact.py`.
- A new design record or library commit is a new context. Old records stay
  valid for their context and are not comparable with new ones.

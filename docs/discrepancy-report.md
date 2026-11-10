# Discrepancy report: numerical experiments on the uncertain inverter

Workstream D (numerical experiments and model comparison). Prepared 2026-11-09.

| Item | Value |
| --- | --- |
| Evidence | `evidence/experiments/2026-11-09-D-illustrative-1v8-06ccc32a/` (`manifest.json` lists every input, code and output hash, versions, seeds, solver settings and timestamps) |
| Design record | `designs/illustrative-1v8.json`, sha256 `06ccc32a…7bc967`. ILLUSTRATIVE: not fitted to any process |
| Model definition | `docs/interface.md`, "v1 candidate (rev. 3)"; the trajectory notion is the rev. 2 one (parameter point free at each instant) |
| Entry point | `.venv/bin/python experiments/run_all.py` (about 7 minutes with 8 worker processes; deterministic, see §8) |
| Lean sources | Not read, by instruction. The simulator was written from the interface prose and the design record only |

## 1. Status in the three evidence dimensions

| Dimension | What this report contributes |
| --- | --- |
| Formal correctness | Nothing. The numerics are an independent check on the mathematics; "no counterexample found" is not a proof. |
| Applicability | Concrete trajectories of the illustrative record in both polarities with a positive disturbance allowance, a nonempty parameter box, and every admissibility condition evaluated exactly. |
| Physical evidence | None. No SPICE run and no measurement exist. §3.9 perturbs the model form; it is a sensitivity study, not validation against a device. |

## 2. Headline

**No counterexample to the claimed mathematics was found.** The four margin claims hold on every tested point in exact arithmetic, two of them with slack exactly 0 (the bounds are attained). The three guarantees held in all 161,448 simulated runs. The proved deadlines are conservative by a factor 1.52 (rise) and 1.84 (fall). All four negative controls fail in the way they should.

Key numbers (V, µA, fF, ns):

| Quantity | Exact | Decimal |
| --- | --- | --- |
| `I_up(V_OH)` | 2619/250 | 10.476 |
| `I_dn(V_OL)` | 2037/125 | 16.296 |
| `R_hiP`, `R_hiN` | 12/5, 289/125 | 2.4, 2.312 |
| `R_loN`, `R_loP` | 76/25, 392/125 | 3.04, 3.136 |
| `τ_up` | 7250/2119 | 3.421425… |
| `τ_dn` | 4575/1787 | 2.560157… |
| Admissible | all 22 conditions of D's checker hold; smallest slack `R_hiN − ε_I` = 0.312 | |
| Model worst-case rise delay | bracket [2.250895, 2.251486] (exact rational sums) | 2.251190 |
| Model worst-case fall delay | bracket [1.394263, 1.394815] | 1.394538 (1.392352 if the parameter point is held constant) |
| `τ_up` / worst rise, `τ_dn` / worst fall | | 1.520, 1.836 |
| Largest observed delay / bound over all runs | | 0.658 (rise), 0.545 (fall) |

Multi-segment bounds `Σ C_max·|c_i − c_{i−1}| / (I(c_i) − ε_I)`. The breakpoint lists are globally optimal on a 1 mV grid (dynamic programme) and are exact decimal strings in `03_worstcase/breakpoints.json`, ready to be checked as `ValidRiseCert` / `ValidFallCert`:

| N | Rise breakpoints (V) | Bound (ns) | / worst | Fall breakpoints (V) | Bound (ns) | / worst |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | −0.1, 1.35 | 3.421425 | 1.520 | 2.08, 0.25 | 2.560157 | 1.836 |
| 2 | −0.1, 1.077, 1.35 | 2.435806 | 1.082 | 2.08, 0.558, 0.25 | 1.583096 | 1.135 |
| 4 | −0.1, 1.015, 1.173, 1.276, 1.35 | 2.301804 | 1.022 | 2.08, 0.634, 0.445, 0.329, 0.25 | 1.460968 | 1.048 |
| 8 | −0.1, 1.004, 1.093, 1.157, 1.208, 1.251, 1.288, 1.321, 1.35 | 2.270838 | 1.009 | 2.08, 0.646, 0.539, 0.464, 0.405, 0.356, 0.315, 0.28, 0.25 | 1.434203 | 1.028 |
| ∞ | | 2.251190 | 1.000 | | 1.417563 | 1.017 |

Uniform breakpoints converge much more slowly (N = 8: 2.349959 and 1.517934; `03_worstcase/multisegment_convergence.csv`, `plots/fig5_multisegment_bounds.png`). Every bound is also stored as an exact rational (for example rise N = 2: 11855905/4867343).

## 3. Findings

**3.1 Margin claims: no negative slack.** Evaluated in exact integer arithmetic on a 0.1 mV lattice (no rounding): 32 corners on a 2.5 mV grid of `(u, v, c)` with `u` reaching −3 V and 5 V, plus 2000 seeded interior parameter points on a 10 mV grid; the barrier claims at 5032 parameter points with `u` at 0.5 mV. Minimum slack: 0 for `I_net ≥ I_up(c)`, 0 for `I_net ≤ −I_dn(c)`, 4.128 µA at `V_hi`, 2.88 µA at `V_lo`. A seeded global search off the grid reached −8.9·10⁻¹⁴ µA in float64 for the first claim; the exact rational value at that point is positive, so this is rounding. Both side conditions are necessary: with `c > VDD_min` the first inequality fails by up to 230 µA, with `c < 0` the second by up to 499 µA (probes outside the claims, `01_margins/margin_claims.json`).

**3.2 Guarantees: no violation in 161,448 runs.** Both polarities; 7 input waveforms each (held at the band edge, held 0.4 V beyond the safe domain, three ramps through the mid region, sine and random piecewise-linear wandering in the valid band); 6 initial states including `V_lo` and `V_hi` exactly; 32 corners at `C_min` and `C_max` plus 32 interior parameter points; 15 disturbances (zero, ±ε, four sinusoids, four random piecewise-linear signals, two state-feedback adversaries, two extremal selections for a fixed parameter point). The total includes 168 runs of the extremal selections of the rev. 2 inclusion, in which parameter point, capacitance and disturbance are all re-chosen at every instant. For a given input and initial state those two runs bound every admissible trajectory, and they produce the largest ratios in the table above.

**3.3 Which trajectory is slowest.** The band edge is the pointwise-worst valid input (checked on a grid, gap 0). Rise: one corner is worst at every voltage, `(VDD_min, k_p,min, V_tp,max, V_tn,max)`; `k_n` does not matter. Note `V_tn,max`: `I_up` charges the NMOS at `(k_n,max, V_tn,min)`, but that term is zero here, and with `V_tn,min` the NMOS conducts in reverse below −0.05 V, which helps the rise. Fall: for a constant parameter point the worst corner is `(VDD_max, k_n,min, V_tn,max, k_p,max, V_tp,min)`; with the parameter point free the adversary uses `(k_p,min, V_tp,max)` while `v > VDD_max` and switches at `v = VDD_max`, which adds 2.2 ps.

**3.4 Tightness.** Both single-segment bounds are loose because they charge the whole swing at the weakest current. The rise certificates converge to the model's worst case exactly. The fall certificates cannot get closer than 1.7 %, because `I_dn(c)` keeps the PMOS contention constant although the PMOS weakens above `V_IH + V_tp,min` and reverses above `VDD`.

**3.5 The boundary margins cap `ε_I`, and they are conservative.** The certificate accepts any `ε_I < 2.312 µA`. The model's own minimum restoring current is 5.92 µA at `V_lo` (`u = 0.82 V`) and 6.44 µA at `V_hi` (`u = 0.65 V`), and 3.56 µA at the supply-relative top `VDD + 0.1 V` (`VDD = 1.62 V`, `u = 0.65 V`). With `ε_I` set to 3, 4 and 5 µA the checker rejects the record and 3 × 32,256 runs show no violation: a failed sufficient condition, not a failed circuit. *Proposal, checked on an exact grid only, not proved:* bound the restoring current by `P(a_{j+1}) + N(a_j)` on each piece of a list of input split points (both transistors counted), with `P_hi` using `VDD_max` in both places (5.28 µA at the present `uHi` instead of `R_hiP` = 2.4). Certified minimum restoring current, top / bottom: 4.696 / 3.072 with one re-chosen split point each, 5.929 / 4.860 with 16 uniform points, 6.313 / 5.667 with 64 (`01_margins/proposal_barrier_refinement.json`). For comparison, workstream F reports 2.3801 as the best the present formulas can reach by moving the split points.

**3.6 Supply-relative safe domain (rev. 3).** For 37 supply values from 1.62 to 1.98 V the restricted record is admissible by D's checker, its deadlines are no larger, and simulation from `VDD + 0.1 V` with everything pushing up never exceeds it. `R_hiN'` = 2.312.

**3.7 Invalid inputs.** The theorem is silent there and the model shows why. Up to 0.098 V beyond `V_IL` (0.095 V beyond `V_IH`) the worst case still meets the proved deadline; beyond 0.224 V (0.171 V) an admissible trajectory never produces a valid output. For held inputs between 0.65 V and 1.0 V the output decodes high, low or undefined depending on corner and disturbance, so both bits occur at the same input. Exactly at the switching threshold with no disturbance a whole interval of outputs is stationary (nominal: 0.311 V to 1.361 V), so the final value depends on the initial state and can decode high. Settling there is arbitrarily slow: 34 of 5049 runs were still drifting after 250 ns. The decoder itself never returns a bit for a voltage strictly between `V_OL` and `V_OH` (property test). So "a mid-rail input gives an undefined output" is not a property of the model; "the decoder never maps an intermediate voltage to a bit" is.

**3.8 Unused safe-domain headroom.** At `ε_I` = 2 µA every stationary output lies in [−0.031, 2.012] V, 69 mV and 68 mV inside the declared domain.

**3.9 Model-form sensitivity (not validation; finite grids; no number here is a bound).**

| Perturbation, coded from its textbook formula | Sandwich residual against the box tube (rev. 2 obligation) | Simulated guarantees |
| --- | --- | --- |
| Channel-length modulation `(1 + λ·|V_DS|)`, λ from 0.02 to 0.3 /V | Nominal device: inside the tube up to λ ≈ 0.153 /V, then 11.8·ε_I at 0.2 and 36.9·ε_I at 0.3. Device at the weakest corner: inside for every tested λ. Device at a corner where a `k` is already maximal (here `k_p,max`): outside at once, 3.3·ε_I at λ = 0.02. Against one fixed parameter point (the superseded v0 obligation) the residual is 6.6·ε_I to 99·ε_I | 0 violations; delays shorter |
| Smooth subthreshold tail (EKV interpolation), n from 1 to 1.5, 233 K to 398 K | Nominal device: at most 0.09·ε_I. Corner devices: up to 0.54·ε_I, above the tube, because the smooth saturation knee carries slightly less current than the weakest box member | 0 violations; worst ratio 0.674 instead of 0.658 |
| Both together | As channel-length modulation | 0 violations |
| Gate-drain feedthrough `C_gd·du/dt` (extra; `C_gd` illustrative) | Equivalent disturbance up to 49.5·ε_I | Safe domain violated in 800 of 13,824 runs: `C_gd` = 0.5 fF at 99 V/ns leaves by 56 mV, 1 fF at 19.8 V/ns by 84 mV, 1 fF at 99 V/ns by 198 mV. No run with `C_gd` ≤ 0.25 fF left. No timing violation |

In total 489,216 runs of perturbed device laws with zero violations. Two readings. First, the parameter box absorbs gain-like model error only for devices away from its edges, so a box meant to cover a process spread needs extra width for model form. Second, "for every input `u`" is a property of the formal model only: with input-output coupling the output leaves `[V_lo, V_hi]` at fast edges, in agreement with `docs/model.md` §7 and interface §4.1.

**3.10 Numerical quality.** Worst-case crossing times agree with quadrature to within 6·10⁻¹¹ ns for five adaptive solvers at relative tolerance 10⁻¹², and to within 5·10⁻¹² ns for the fixed-step engine at the step used. Halving the step changes crossing times by at most 4·10⁻⁹ ns for time-only disturbances, 1.3·10⁻⁶ ns for the extremal selections and 4.5·10⁻⁵ ns for the discontinuous state-feedback adversaries, which are first-order accurate. All are far below the margins found. LSODA failed on one non-autonomous case ("Unexpected istate"); the failure is retained in `04_convergence/nonautonomous.csv`.

**3.11 Agreement with other workstreams' independent numbers.** Workstream F's quadrature, which does not use D's simulator (`docs/experiment-loop.md` §9, §12), gives the same worst-case delays (2.251190 ns; 1.392352 ns for a constant parameter point and 1.394538 ns for a moving one) and the same limit 1.417563 ns for the fall certificates. F's own dynamic programme arrives at the same levels and sums for N = 2, 4 and 8 (F lists levels without the starting level), and `evidence/search/summary.md` records the N = 4 and N = 8 certificates as accepted by Lean; D did not check that itself. Workstream B's hand and script calculation (`docs/model.md` §6.1) gives the same boundary minima 5.92, 6.44 and 3.56 µA at the same inputs. The Lean floors quoted by F (no rise deadline below 2.168 ns, no fall deadline below 1.0234 ns) lie below the numerical worst cases, as they must.

**3.12 Interface notes.**

- `Admissible` is not enumerated in the prose. D's checker uses 22 conditions: `lo ≤ hi` for six parameters; `0 < C_min`, `0 < k_n,min`, `0 < k_p,min`, `0 < V_tp,min`, `0 ≤ ε_I`; `V_OL ≤ V_IL < V_IH ≤ V_OH`; `V_lo ≤ 0`, `VDD_max ≤ V_hi`; six margins. Please compare with the Lean definition.
- A check of the six margins alone accepts a record with inverted bounds (control (i)). Box consistency must be part of the check.
- Not tested, because no prose statement was available to D: `rise_at_most`, `fall_at_most`, the two-stage chain, existence and uniqueness, gluing.
- `experiments/ngspice/work/` (scratch directory of the SPICE runner once it is run) should be git-ignored. D does not edit `.gitignore`.

## 4. Negative controls

| Control | Explicit rejection | Exhibited trajectory |
| --- | --- | --- |
| (i) Bounds inverted, `C: [20, 5]` | Checker rejects (`C_lo ≤ C_hi`). The six margins alone pass | With `C` = 20 fF the output is 0.472 V (undefined) at the deadline 0.855 ns computed from the record; it crosses at 2.251 ns |
| (i) Bounds inverted, `kp: [80, 10]` | Checker rejects. The six margins alone pass | With `k_p` = 10 the output never rises and settles at −0.231 V, outside the safe domain |
| (i) Float instead of decimal string | Rejected at load | not applicable |
| (ii) Observation too early | Window `[s + τ, e]` is empty | Slowest admissible trajectory: undefined at 0.9 × the lower bound (1.240 V at 2.026 ns; fall 0.373 V at 1.255 ns). Lower bounds 2.250895 ns and 1.394263 ns are exact rational sums |
| (iii) Swapped transistor roles | Margin analogue is negative (−15 and −36.3 µA) | Input low keeps the output low; input high keeps it high. 7680 runs: all violate persistence, 5462 never cross in time, 1492 leave the safe domain |
| (iv) `ε` beyond the margin | Checker rejects | Smallest `ε` with a stationary point at or below `V_OH` at the worst corner: exactly 10.476 µA = `I_up(V_OH)`. At 1.01× the output is stuck 3.8 mV below `V_OH`, at 1.05× 19.2 mV below, at 1.5× it settles at −0.265 V. Fall: 16.296 µA. Barriers: at 1.05× the model minimum the output leaves by 5.7 mV (bottom) and 4.8 mV (top) |

At exactly 10.476 µA the stationary point is `V_OH` itself and the exact solution approaches it without reaching it. Float64 cannot resolve that case, so it is not counted as an exhibit.

## 5. Finite-coverage statement

- Margin claims: the grid points listed in §3.1 and one seeded global search. Nothing is established between grid points or for `|u|` beyond the grid. That the box extremes are attained at corners is an argument (the law is monotone in each parameter), supported by 400,000 random points, not a grid result.
- Trajectories: for each of 14 input waveforms and 6 initial states the two extremal runs cover every disturbance, capacitance and parameter selection up to integration error. What remains finite is the set of input waveforms and of initial states. No statement is made about other waveforms.
- Worst-case delays: quadrature at the band-edge input, bracketed by exact rational sums.
- Sensitivity: three base devices, two correction families and one coupling term on finite grids. It says nothing about a real transistor.
- No SPICE run, no measurement.

## 6. Retained failing cases

| Case | Where |
| --- | --- |
| Formal model, trajectory matrix | none: `02_trajectories/failing_cases.csv` has a header and no rows |
| Negative-control trajectories | `05_negative_controls/trajectories.csv`, `controls.json`, `plots/fig7_negative_controls.png` |
| Feedthrough runs that leave the safe domain | `07_sensitivity/miller.csv` (worst case per row: corner, load, disturbance, initial state) |
| Perturbed devices outside the tube | `07_sensitivity/sandwich_residual.csv` |
| Side-condition probes with negative slack | `01_margins/margin_claims.json` |
| Float64 slack of −8.9·10⁻¹⁴ µA, positive when re-evaluated exactly | `01_margins/margin_claims.json` (`de_search`) |
| LSODA failure | `04_convergence/nonautonomous.csv` |

## 7. Completed and proposed checks

| Check | Status | Evidence |
| --- | --- | --- |
| Closed-form margins, deadlines, admissibility (exact) | COMPLETED | `01_margins/closed_form.json` |
| Four margin claims, exact grids and global search | COMPLETED | `01_margins/margin_claims.json` |
| Trajectory matrix, three guarantees | COMPLETED | `02_trajectories/` |
| Worst-case delays, tightness, multi-segment certificates | COMPLETED | `03_worstcase/` |
| Convergence of every reported crossing time | COMPLETED | `04_convergence/` |
| Negative controls (i) to (iv) | COMPLETED | `05_negative_controls/` |
| Boundary behaviour, supply-relative domain, mid-rail holds | COMPLETED | `06_boundary/` |
| Model-form sensitivity (not validation) | COMPLETED | `07_sensitivity/` |
| Runner plumbing on synthetic files written from the Python model (no SPICE involved) | COMPLETED | `08_ngspice_PROPOSED_NOT_RUN/runner_selftest_NO_SPICE.json` |
| T1: ngspice Level 1 (`LAMBDA=0`, `GAMMA=0`, `IS=1e-30`) against the Python simulator | PROPOSED, NOT RUN | `experiments/ngspice/decks/level1_*.cir`, `run_ngspice.py --part a` |
| T2: Level 1 with one omitted effect at a time | PROPOSED, NOT RUN (decks not rendered) | `compare_plan.json` |
| T3: SKY130 BSIM4 `nfet_01v8` / `pfet_01v8_hvt` (workstream B's recommendation, not frozen) | PROPOSED, NOT RUN | `experiments/ngspice/decks/sky130_T3_*.cir`, `run_ngspice.py --part b` |
| Minimum-delay, chain and existence statements | NOT TESTED | no prose statement available |

What T1 and T3 would compare is fixed in `08_ngspice_PROPOSED_NOT_RUN/compare_plan.json`. T1: the DC current map against the Python law at all 32 corners (pass below 10⁻³ µA) and transient crossing times. T3, organised by margin and by corner as in `docs/model.md` IP-9: the sandwich residual of the SPICE current map against the box tube, the four margins evaluated directly on that map, transient delays against `τ`, output excursions against the safe domain, and the incremental capacitances. The decks state what must be verified on first run: zero Level-1 device capacitance without `TOX`, the `wrdata` layout, the model library paths and settings.

## 8. Reproduction

```sh
uv venv .venv --python 3.14
uv pip install --python .venv/bin/python -r experiments/requirements.txt
.venv/bin/python experiments/run_all.py                      # writes evidence/experiments/<run-id>/
.venv/bin/python experiments/run_all.py --jobs 4 --out /tmp/x --run-id rerun \
    --compare-to evidence/experiments/2026-11-09-D-illustrative-1v8-06ccc32a   # determinism check
.venv/bin/python experiments/ngspice/run_ngspice.py --dry-run   # what the SPICE comparison would run
```

Python 3.14.0, numpy 2.4.6, scipy 1.18.0, matplotlib 3.11.2. Master seed 20261109; every random stream is named in the manifest. A second complete run with 4 worker processes instead of 8 reproduced all 46 output files byte for byte; the record is `evidence/experiments/2026-11-09-D-illustrative-1v8-06ccc32a.determinism.json`. Workstream D does not commit: the code is identified by the per-file SHA-256 list in the manifest, not by a commit.

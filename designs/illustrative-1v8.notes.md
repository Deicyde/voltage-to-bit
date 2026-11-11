# Notes for `illustrative-1v8.json`

These notes are kept beside the record rather than inside it so that the
record's SHA-256, which experiments and search records cite, does not change.

## Status

Illustrative. The numbers are plausible orders of magnitude for a small
1.8 V-class inverter. They are not fitted to any process, device model or
measurement, and the record must not be described as representing SKY130 or any
other real process.

## What caps the disturbance allowance

`ε_I = 2 µA` should be compared with the four boundary margins, not with the
switching margins:

| Margin | Value (µA) | Lean |
| --- | --- | --- |
| `R_hiN` | 2.312 | `illustrative_RhiN` |
| `R_hiP` | 2.4 | `illustrative_RhiP` |
| `R_loN` | 3.04 | `illustrative_RloN` |
| `R_loP` | 3.136 | `illustrative_RloP` |
| `I_up(V_OH)` | 10.476 | `illustrative_Iup` |
| `I_dn(V_OL)` | 16.296 | `illustrative_Idn` |

So the largest `ε_I` the present proof supports for this record is just under
2.312 µA: a margin of 16 %, not a factor of five. The four boundary numbers are
bounds obtained with the proof-only split points `uHi`, `uLo`; the true minima
of the restoring current over all inputs are larger: about 5.9 µA at the bottom
and 6.4 µA at the fixed top of 2.08 V, and about 3.6 µA at the top of the
supply-relative domain `VDD + 0.10 V`, which is the physically relevant one
(workstream B's calculation, `docs/model.md` §6.1; not a Lean result).
Re-choosing the split points alone gains little. With `uHi = 0.772486` and
`uLo = 0.742506`, which is a different record, the same circuit is admissible
for `ε_I = 2.3801 µA` (`illustrativeEps_admissible`), and for
`ε_I ≥ 2.3802 µA` no choice of split points makes it admissible
(`illustrative_eps_no_split_points`); both are proved in
`VoltageToBit/Examples/Limits.lean`. Only a boundary bound that counts both
transistors could approach the model's own minima (about 3.56 µA at the
supply-relative top, 5.92 and 6.44 µA at the fixed ends; numerical values,
not Lean results). The library has no such bound.

## An environment under which `ε_I = 2 µA` has a physical reading

Every number below is illustrative (workstream B, `docs/model.md` §7.3,
"Budget A"). None is proved or measured.

| Source | Assumption | Share |
| --- | --- | --- |
| Gate-drain feedthrough | `C_M ≤ 0.5 fF`, input slew `≤ 2 V/ns` | 1.0 µA |
| Aggressor coupling | total `C_c ≤ 0.1 fF` at `≤ 5 V/ns`, or no switching neighbour | 0.5 µA |
| Supply motion | junction capacitance `≤ 1 fF`, supply slew `≤ 0.1 V/ns` | 0.1 µA |
| Static leakage | hot, fast corner | 0.01 µA |
| Near-threshold conduction | `V_IL` 0.05 V below `V_tn,min`, up to 125 °C | 0.3 µA |
| Reserve | | 0.09 µA |
| Total | | 2.0 µA |

An input slew of 2 V/ns means a full swing takes about 0.9 ns. With
library-realistic edges (20 V/ns and 0.5 fF of gate-drain capacitance) the
feedthrough alone is 10 µA and the record is not admissible. The explicit run
in `Examples/Illustrative.lean` uses a 9 V/ns ramp and is a mathematical
witness, not a scenario inside this budget. That remains true of
`Examples.illustrative_scenario`, the run meant here. Note added 2026-11-09:
the same file now has a second explicit run,
`Examples.illustrative_feedthrough_scenario`, which is exactly at the
allowance (0.5 fF to the input at no more than 2 V/ns, 0.1 fF to one
aggressor at no more than 5 V/ns and a residual of at most 0.5 µA:
0.5·2 + 0.1·5 + 0.5 = 2.0 µA); its input stays valid-low, so only the rising
direction of the output occurs, and it is a mathematical witness inside this
assumed budget, not evidence about a device.

## Relation to SKY130 (the proposed comparison process)

From documentation only; nothing here has been simulated (`docs/model.md` §10).

- The record's thresholds (0.45 to 0.60 V) are about 0.15 to 0.35 V below
  SKY130's documented short-channel thresholds (0.60 to 0.85 V for the NMOS,
  0.68 to 0.96 V for the high-threshold PMOS).
- `VDD_max = 1.98 V` and the top of the safe domain (2.08 V) exceed the 1.95 V
  to which the SKY130 device models are documented.
- The record's `k_n`, `k_p` are roughly two to four times smaller than
  saturation-fit values for the SKY130 `inv_1` cell.
- No temperature is implied by the box.
- Expectation, untested: a box wide enough to bracket SKY130 devices has no
  voltage headroom at the slow corner and low supply, so the four boundary
  conditions cannot all hold there for an excursion of 0.1 V. The switching
  margins appear to survive. A SKY130-anchored record is a separate
  experiment; the options are listed in `docs/model.md` §10.3.

## Corrections after the independent fact-check (2026-11-09)

The fact-check is recorded in `evidence/factcheck/factcheck.json`, area
`sky130`. Each line below is one change. The last row follows a change of the
Lean library, not the fact-check. The record `illustrative-1v8.json` is
unchanged. The Lean statements named here were read in the sources at commit
`2bf6f81`, and again at commit `8c2637b` on 2026-11-10 (last paragraph of this
section); the project was not rebuilt for these corrections.

| Where | What was wrong | What it says now |
| --- | --- | --- |
| "What caps the disturbance allowance", end of the paragraph | It said that better split points would raise the provable `ε_I` towards the true minima, and called that an open improvement for the search loop. Re-choosing the split points gains less than 3 %, and the library now states that limit. | Split points alone reach 2.3801 µA and no choice reaches 2.3802 µA (`VoltageToBit/Examples/Limits.lean`). Only a bound that counts both transistors could approach the model's minima, and the library has none. |
| "Relation to SKY130", first bullet | "0.2 to 0.35 V" below does not follow from the quoted ranges: the NMOS low end differs by 0.15 V. | "about 0.15 to 0.35 V". |
| "Relation to SKY130", third bullet | "two to three times smaller" understated the spread, which reaches four. | "roughly two to four times smaller". |
| "Relation to SKY130", last bullet | "the four boundary conditions fail" can be read as "each one fails"; single conditions can still hold. | "cannot all hold". |
| "An environment under which `ε_I = 2 µA` has a physical reading", last paragraph | "The explicit run" was the only one when these notes were written; the library now has two. | The sentence is kept and said to be true of `Examples.illustrative_scenario`; a dated note adds `Examples.illustrative_feedthrough_scenario`, which is exactly at the allowance (0.5·2 + 0.1·5 + 0.5 = 2.0 µA). |

Name check on 2026-11-09: every Lean name quoted in these notes was searched
under `VoltageToBit/` at commit `2bf6f81`, and all resolve.

Check of 2026-11-10, after the second verification round
(`evidence/verification/round2-finish-fixes.json`, entry `model-doc`). No issue
of that round is located in these notes, and the text above this section is
unchanged. The Lean library moved from commit `2bf6f81` to `8c2637b`. The Lean
statements named in these notes were compared with the sources at `8c2637b` and
with the signatures printed by `#check` from the build products of the
checkout (scratch files compiled with `lake env lean`; the project was not
rebuilt): the six theorems of the margin table, `illustrativeEps_admissible`,
`illustrative_eps_no_split_points`, `Examples.illustrative_scenario` and
`Examples.illustrative_feedthrough_scenario`. Their statements are the same
text at both commits. For the sentence "The library has no such bound",
`VoltageToBit/Proofs/Margins.lean` was read again at `8c2637b`: each of its four
boundary bounds counts one transistor. A search of the theorem statements of
the library found, apart from these four and their two combinations
`Design.Inet_Vhi_lt` and `Design.Inet_Vlo_gt`, no bound on the net current at
an end of the safe domain that holds for every input. Name check: every Lean
name quoted in these notes resolves at `8c2637b` (a generated file with one
`#check` line per name, and a metaprogram that lists the project constants
whose name ends with it).

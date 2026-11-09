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
(workstream B's calculation, `docs/model.md` §6.1; not a Lean result). Better
split points, or a list of them with both devices counted on each piece, would
raise the provable `ε_I` towards those values without changing the circuit.
That is an open improvement for the search loop.

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
witness, not a scenario inside this budget.

## Relation to SKY130 (the proposed comparison process)

From documentation only; nothing here has been simulated (`docs/model.md` §10).

- The record's thresholds (0.45 to 0.60 V) are 0.2 to 0.35 V below SKY130's
  documented short-channel thresholds (0.60 to 0.85 V for the NMOS, 0.68 to
  0.96 V for the high-threshold PMOS).
- `VDD_max = 1.98 V` and the top of the safe domain (2.08 V) exceed the 1.95 V
  to which the SKY130 device models are documented.
- The record's `k_n`, `k_p` are two to three times smaller than
  saturation-fit values for the SKY130 `inv_1` cell.
- No temperature is implied by the box.
- Expectation, untested: a box wide enough to bracket SKY130 devices has no
  voltage headroom at the slow corner and low supply, so the four boundary
  conditions fail there for an excursion of 0.1 V. The switching margins appear
  to survive. A SKY130-anchored record is a separate experiment; the options
  are listed in `docs/model.md` §10.3.

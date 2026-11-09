# voltage-to-bit

When does a continuously changing voltage become a bit you can rely on?

This repository answers that question for **one CMOS inverter**, in a
transistor-level model with an explicit bound on model error, and checks the
answer in Lean 4. It is the first milestone of the plan in
[HANDOFF.md](HANDOFF.md). The provisional name and location can change.

## The claim

**Model.** Two transistors (PMOS from supply to output, NMOS from output to
ground, both gates on the input) following the symmetric Shichman–Hodges square
law, a load capacitance anywhere in `[C_min, C_max]`, device and supply
parameters anywhere in a box, and an unmodelled current into the output node of
magnitude at most `ε_I` at every instant. The dynamics are a differential
inclusion; see [docs/interface.md](docs/interface.md) for the exact definitions.

**Theorem.** For every design record whose numbers pass a finite list of
arithmetic checks, every parameter choice in the box, every input waveform (no
regularity assumed) and every trajectory that starts in the safe voltage
domain:

1. the output voltage stays in the safe domain;
2. if the input is valid-low on `[s, e)`, the output is valid-high on
   `[s + τ_up, e]`;
3. if the input is valid-high on `[s, e)`, the output is valid-low on
   `[s + τ_dn, e]`.

Voltages between the thresholds decode to *undefined*, never to a bit. The
current margins behind `τ_up` and `τ_dn` are derived from the device law, not
assumed. Trajectories are proved to exist (and, for the ODE form, to be
unique), so the statement is not vacuous.

**Concrete instance** ([designs/illustrative-1v8.json](designs/illustrative-1v8.json);
units V, µA, fF, ns):

| Quantity | Value |
| --- | --- |
| Supply | 1.62 to 1.98 V |
| Thresholds `V_tn`, `V_tp` | 0.45 to 0.60 V each |
| `k_n`, `k_p` | 160 to 240, 80 to 120 µA/V² |
| Load | 5 to 20 fF |
| Unmodelled current `ε_I` | 2 µA (strictly positive) |
| Valid input | low ≤ 0.40 V, high ≥ 1.25 V |
| Valid output | low ≤ 0.25 V, high ≥ 1.35 V |
| Safe domain | −0.10 to 2.08 V |
| Proved rise deadline | 7250/2119 ≈ 3.43 ns (refined: see below) |
| Proved fall deadline | 4575/1787 ≈ 2.57 ns |

These numbers are **illustrative**. They are plausible orders of magnitude and
are not fitted to any process, device model, or measurement.

## Status, in three separate dimensions

There is deliberately no single badge.

| Dimension | Status | Evidence |
| --- | --- | --- |
| Formal correctness | Checked by the Lean 4.35.0 kernel against Mathlib `v4.35.0`. Every declaration in the library depends only on `propext`, `Classical.choice`, `Quot.sound`. Not replayed through an independent checker. | `scripts/check.sh`, [evidence/lean/audit.txt](evidence/lean/audit.txt) |
| Applicability | One concrete record satisfies every hypothesis; the parameter box, safe domain and trajectory sets are proved nonempty for every admissible record; an explicit run exhibits both logic directions with observation windows of positive length. | `Examples/Illustrative.lean`, `Proofs/NonVacuity.lean` |
| Physical evidence | **None yet.** No measurement and no comparison against a foundry device model has been run. Whether a real inverter stays within `ε_I` of the square law is an open assumption. | [docs/assumptions.md](docs/assumptions.md), [docs/discrepancy-report.md](docs/discrepancy-report.md) |

## What is not claimed

- That any manufactured transistor obeys the square law, or that the
  illustrative numbers describe a real process.
- Anything about inputs that are neither valid-low nor valid-high for the whole
  window: then only the safe-domain statement applies.
- Anything about trajectories that start outside the safe domain.
- Metastability, interconnect, more than one dynamic node, time-varying supply,
  or noise with unbounded tails. See [docs/model.md](docs/model.md).

## Reproduce

Requires `elan` (Lean toolchain manager) and Python 3. The Lean version and
the Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get          # prebuilt Mathlib; skip if .lake/packages is populated
scripts/check.sh --fresh    # recompile this project, audit axioms, check design sync
```

`scripts/check.sh` stops at the first failure and prints
`ALL FORMAL CHECKS PASSED` otherwise.

## Where to look

| Path | Content |
| --- | --- |
| `VoltageToBit/Model/` | definitions: device law, design record, trajectories, decoding |
| `VoltageToBit/Proofs/Reach.lean` | circuit-free reachability lemmas |
| `VoltageToBit/Proofs/Margins.lean` | current margins derived from the device law |
| `VoltageToBit/Proofs/Guarantee.lean` | the guarantee for every trajectory |
| `VoltageToBit/Proofs/Existence.lean` | existence and uniqueness of solutions |
| `VoltageToBit/Proofs/NonVacuity.lean` | admissible records are never degenerate |
| `VoltageToBit/Proofs/Certificate.lean` | refined deadlines from lists of levels |
| `VoltageToBit/Proofs/ModelError.lean` | what another model must satisfy to be covered |
| `VoltageToBit/Proofs/Contamination.lean` | a minimum rise delay |
| `VoltageToBit/Proofs/Chain.lean` | two stages in series |
| `VoltageToBit/Examples/` | the concrete instance and the negative controls |
| `docs/` | interface, model and physical interpretation, assumption register, source audit, adversarial review, experiment loop |
| `designs/` | design records (single source of numbers for Lean and experiments) |
| `experiments/`, `evidence/` | numerical experiments and their compact outputs |
| `search/` | the propose, screen, check, record loop |
| `scripts/` | generation, build and audit entry points |

## Provenance

The starting point was an audit of
[Deicyde/assembly-to-physics](https://github.com/Deicyde/assembly-to-physics/tree/7359bfe8266d06954e221f881403e7e83d5592f6)
at commit `7359bfe`. The Lean development here was written fresh against
Mathlib for a different model (additive error bound, widened safe domain,
symmetric device law). What was examined and what was reused is recorded in
[docs/source-audit.md](docs/source-audit.md).

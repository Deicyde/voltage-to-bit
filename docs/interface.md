# Shared interface

Owner: coordinator. Status: **v1 candidate** (2026-11-09), to be frozen after
the first findings of workstreams A, B, D and E are dispositioned. Workstreams
propose changes to the coordinator; changes are recorded in the log at the end.
The Lean sources under `VoltageToBit/` are authoritative wherever this prose and
the Lean differ; report any difference as a defect.

## 1. Circuit identity

Static CMOS inverter, one dynamic state.

| Element | Connection |
| --- | --- |
| PMOS | source = supply rail `VDD`, gate = input `u`, drain = output node `v` |
| NMOS | source = ground (0 V), gate = input `u`, drain = output node `v` |
| Load | lumped capacitance from output node to ground |

State: output node voltage `v(t)`. Input: gate voltage `u(t)`, an arbitrary
real-valued function of time for the universal guarantee.

## 2. Units

Volts (V), microamps (µA), femtofarads (fF), nanoseconds (ns). The system is
coherent: µA / fF = V / ns. Transconductance parameters `k` are in µA/V².
Every number in a design record carries these units. A design record states
whether its numbers are illustrative, fitted, or measured. The Lean development
is unit-free; units are a convention of the design record.

## 3. Device law (model definition)

Symmetric Shichman–Hodges square law, no channel-length modulation, no body
effect, no subthreshold conduction. With `x₊ = max(x, 0)` and `psq(x) = x₊²`:

```text
I_n(u, v; θ) = (k_n / 2) · ( psq(u − V_tn) − psq(u − v − V_tn) )          output → ground
I_p(u, v; θ) = (k_p / 2) · ( psq(VDD − u − V_tp) − psq(v − u − V_tp) )    supply → output
I_net(u, v; θ) = I_p − I_n                                                 into the output node
```

`V_tp > 0` is the magnitude of the PMOS threshold. The expressions are defined
for all real `u`, `v`; for `v` outside `[0, VDD]` they describe reverse
conduction (source/drain exchange). Lean: `In`, `Ip`, `Inet` in
`Model/Device.lean`, with lemmas `In_cutoff`, `In_triode`, `In_sat`,
`Ip_cutoff`, `Ip_triode`, `Ip_sat` identifying the textbook regions.

Parameters `θ = (VDD, k_n, k_p, V_tn, V_tp)` lie in a box given by the design
record (`Design.InBox`). In the ODE form they are constant during a run; the
trajectory notion of §4 only requires a point of the box at each instant.

## 4. Dynamics and uncertainty (differential inclusion)

A trajectory on `[a, b]` (`IsTrajectory D u v a b`) is a function `v` that is
continuous on `[a, b]` and has, at each `t ∈ [a, b)`, a right derivative
`v'(t)` such that, for some capacitance value `c ∈ [C_min, C_max]` and some
parameter point `θ` of the box,

```text
| c · v'(t) − I_net(u(t), v(t); θ) | ≤ ε_I       (required whenever v(t) ∈ [V_lo, V_hi])
```

The capacitance value and the parameter point may differ from instant to
instant. Three sources of uncertainty are therefore explicit and separate:

| Source | Envelope | Covers, for example |
| --- | --- | --- |
| Load | `c ∈ [C_min, C_max]` at each instant | voltage-dependent or slowly varying capacitance |
| Devices and supply | `θ` anywhere in the box at each instant | process spread, a supply moving within its range, any device law lying between box members |
| Everything else | additive current `≤ ε_I` | coupling, leakage, conduction below threshold |

This contains every solution of `C(v) · dv/dt = I_net(u, v; θ) + w(t)` with
`C_min ≤ C(·) ≤ C_max`, `θ` in the box (constant, or moving within the box) and
`|w(t)| ≤ ε_I` that has a right derivative at every instant
(`IsTrajectory.of_ode`, `IsTrajectory.of_ode_varying`). No regularity of `u`,
`w`, or `C` is assumed for the universal guarantee.

Known scope limit: a solution that is only absolutely continuous (a
disturbance that is merely measurable, with no one-sided limits) need not have
a right derivative at every instant and is then not a trajectory in this sense.

`ε_I` has current units (µA). The envelopes are mathematical. Whether a
physical effect or a higher-fidelity model fits inside them is a separate,
empirical question (see `docs/model.md`, `docs/assumptions.md`). The exact
obligation is stated in `Proofs/ModelError.lean`: on the safe domain the other
model's net current must lie between the net currents of two box members, up to
`ε_m`, and any further disturbance must be within `ε_w`, with
`ε_m + ε_w ≤ ε_I` (`IsTrajectory.of_sandwich`).

## 5. Digital semantics

| Quantity | Meaning |
| --- | --- |
| `V_IL`, `V_IH` | input is valid-low iff `u ≤ V_IL`, valid-high iff `u ≥ V_IH` |
| `V_OL`, `V_OH` | output decodes to low iff `v ≤ V_OL`, high iff `v ≥ V_OH`, otherwise **undefined** |
| `[V_lo, V_hi]` | safe voltage domain, a superset of `[0, VDD]` |

Decoding is three-valued (`decode : ℝ → ℝ → ℝ → Option Bool`); intermediate
voltages are never mapped to a Boolean. Static discipline:
`V_OL ≤ V_IL < V_IH ≤ V_OH`. Thresholds are absolute voltages, not fractions
of `VDD`.

## 6. What is proved

For a design record `D` satisfying a finite list of numeric conditions
(`Design.Admissible`: box consistency, threshold ordering, and six
current-margin inequalities), for every input `u` and every trajectory `v` on
`[a, b]` with `v(a) ∈ [V_lo, V_hi]`:

1. Safe domain (`IsTrajectory.safe`): `v(t) ∈ [V_lo, V_hi]` for all `t ∈ [a, b]`.
2. Low in, high out (`IsTrajectory.rise`): if `u ≤ V_IL` on `[s, e) ⊆ [a, b]`
   then `v(t) ≥ V_OH` for all `t ∈ [s + τ_up, e]`.
3. High in, low out (`IsTrajectory.fall`): if `u ≥ V_IH` on `[s, e) ⊆ [a, b]`
   then `v(t) ≤ V_OL` for all `t ∈ [s + τ_dn, e]`.
4. Decoded form (`IsTrajectory.decoded`): if the input decodes to a bit on
   `[s, e)`, the output decodes to the opposite bit on `[s + τ, e]`.

The six margins are closed-form numbers of the record, and
`Proofs/Margins.lean` proves that the device law provides at least these
currents for every `θ` in the box:

```text
I_up(c) = (k_p,min/2)·(psq(VDD_min − V_IL − V_tp,max) − psq(c − V_IL − V_tp,max)) − (k_n,max/2)·psq(V_IL − V_tn,min)
I_dn(c) = (k_n,min/2)·(psq(V_IH − V_tn,max) − psq(V_IH − c − V_tn,max)) − (k_p,max/2)·psq(VDD_max − V_IH − V_tp,min)
R_hiP  = (k_p,min/2)·(psq(VDD_min − u_Hi − V_tp,max + (V_hi − VDD_max)) − psq(VDD_min − u_Hi − V_tp,max))
R_hiN  = (k_n,min/2)·(psq(u_Hi − V_tn,max) − psq(u_Hi − V_hi − V_tn,max))
R_loN  = (k_n,min/2)·(psq(u_Lo − V_lo − V_tn,max) − psq(u_Lo − V_tn,max))
R_loP  = (k_p,min/2)·(psq(VDD_min − u_Lo − V_tp,max) − psq(V_lo − u_Lo − V_tp,max))

τ_up = C_max · (V_OH − V_lo) / (I_up(V_OH) − ε_I)
τ_dn = C_max · (V_hi − V_OL) / (I_dn(V_OL) − ε_I)
```

`u_Hi` and `u_Lo` are proof-only split points: they select which transistor is
used to bound the restoring current at each end of the safe domain. They are
not circuit or environment parameters.

Also proved:

- Existence and uniqueness (`exists_solution`, `solution_unique`,
  `exists_trajectory`): for constant `θ` in the box, continuous `u`, continuous
  `w` with `|w| ≤ ε_I`, and a capacitance function with values in
  `[C_min, C_max]` that is Lipschitz on the safe domain, the ODE has exactly one
  solution on any `[a, b]` from any initial state in the safe domain. Existence
  is not proved for parameters that move in time or for less regular data; for
  those the guarantee is a statement about whatever trajectories there are.
- Non-vacuity for every admissible record (`Proofs/NonVacuity.lean`).
- Refined deadlines from a list of intermediate levels
  (`Design.ValidRiseCert`, `Design.ValidFallCert`, `rise_of_cert`,
  `fall_of_cert`): a certificate is a list of voltage levels; validity is
  arithmetic; the theorem is proved once for all lists.
- Minimum delays in both directions (`IsTrajectory.rise_at_most`,
  `IsTrajectory.fall_at_most`).
- Two stages in series (`Proofs/Chain.lean`).

## 7. Design records

Machine-readable design records live in `designs/*.json` with decimal strings
(exact rationals). They are the single source for the numbers used by the Lean
instance and by the experiments. `scripts/gen_design.py` generates the Lean
record; `scripts/check.sh` verifies the two are in sync. Current record:
`designs/illustrative-1v8.json` (illustrative, not fitted).

## 8. Experiment schema

Workstream F owns the record format (`docs/experiment-loop.md`). Every
experiment record names the design record and its SHA-256, the code version,
the solver and tolerances, seeds, and whether each reported check was
completed or only proposed.

## Change log

| Date | Version | Change | Reason |
| --- | --- | --- | --- |
| 2026-11-09 | v0 | Initial draft by coordinator. | Start of project. |
| 2026-11-09 | v1 candidate | Hypothesis window is `[s, e)`; six margins written out; existence extended to voltage-dependent Lipschitz capacitance; uniqueness, certificates, minimum delay, model-error obligation and the measurable-disturbance scope limit recorded. | Bring prose in line with the Lean at commit `cac4016`. |
| 2026-11-09 | v1 candidate (rev. 2) | `IsTrajectory` no longer takes a fixed `θ`: at each instant some point of the box must satisfy the current balance. Theorems lose their `θ` argument and are strictly more general. Model-error obligation restated as a sandwich between box members. | A fixed additive `ε_I` cannot absorb model-form error that scales with device current; the proofs only ever used bounds that hold throughout the box. Commit `eae25ed`. Statements reviewed by workstream E at `1880a36` are implied by the new ones via `IsTrajectory.of_ode`. |

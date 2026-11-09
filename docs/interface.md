# Shared interface

Owner: coordinator. Status: **DRAFT v0** (2026-11-09). Not frozen. Workstreams
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
whether its numbers are illustrative, fitted, or measured.

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
conduction (source/drain exchange).

Parameters `θ = (VDD, k_n, k_p, V_tn, V_tp)` are constant during a run and lie
in a box `Θ` given by the design record.

## 4. Dynamics and uncertainty (differential inclusion)

A trajectory on `[a, b]` is a function `v` that is continuous on `[a, b]` and
has, at each `t ∈ [a, b)`, a right derivative `v'(t)` such that for some
capacitance value `c ∈ [C_min, C_max]`

```text
| c · v'(t) − I_net(u(t), v(t); θ) | ≤ ε_I       (required whenever v(t) ∈ [V_lo, V_hi])
```

This contains every solution of `C(v) · dv/dt = I_net + w(t)` with
`C_min ≤ C(·) ≤ C_max` and `|w(t)| ≤ ε_I`, for any capacitance function and any
disturbance within the bounds. No regularity of `u`, `w`, or `C` is assumed for
the universal guarantee. Existence of trajectories is a separate theorem for
continuous `u` and `w`.

`ε_I` has current units (µA). It is a mathematical envelope. Whether a physical
effect or a higher-fidelity model fits inside it is a separate, empirical
question (see `docs/model.md`, `docs/assumptions.md`).

## 5. Digital semantics

| Quantity | Meaning |
| --- | --- |
| `V_IL`, `V_IH` | input is valid-low iff `u ≤ V_IL`, valid-high iff `u ≥ V_IH` |
| `V_OL`, `V_OH` | output decodes to low iff `v ≤ V_OL`, high iff `v ≥ V_OH`, otherwise **undefined** |
| `[V_lo, V_hi]` | safe voltage domain, a superset of `[0, VDD]` |

Decoding is three-valued (`Option Bool`); intermediate voltages are never
mapped to a Boolean. Static discipline: `V_OL ≤ V_IL < V_IH ≤ V_OH`.
Thresholds are absolute voltages, not fractions of `VDD`.

## 6. Target theorem (shape)

For a design record `D` satisfying a finite list of numeric conditions
(`Admissible D`: box consistency, threshold ordering, and six current-margin
inequalities derived from the device law), for every `θ ∈ Θ`, every input `u`,
and every trajectory `v` on `[a, b]` with `v(a) ∈ [V_lo, V_hi]`:

1. Safe domain: `v(t) ∈ [V_lo, V_hi]` for all `t ∈ [a, b]`.
2. Low in, high out: if `u ≤ V_IL` on `[s, e] ⊆ [a, b]` then `v(t) ≥ V_OH` for
   all `t ∈ [s + τ_up, e]`.
3. High in, low out: if `u ≥ V_IH` on `[s, e] ⊆ [a, b]` then `v(t) ≤ V_OL` for
   all `t ∈ [s + τ_dn, e]`.

with

```text
I_up = (k_p,min/2)·(psq(VDD_min − V_IL − V_tp,max) − psq(V_OH − V_IL − V_tp,max)) − (k_n,max/2)·psq(V_IL − V_tn,min)
I_dn = (k_n,min/2)·(psq(V_IH − V_tn,max) − psq(V_IH − V_OL − V_tn,max)) − (k_p,max/2)·psq(VDD_max − V_IH − V_tp,min)
τ_up = C_max · (V_OH − V_lo) / (I_up − ε_I)
τ_dn = C_max · (V_hi − V_OL) / (I_dn − ε_I)
```

Separately: existence of a trajectory on any `[a, b]` from any initial state in
the safe domain, for continuous `u`, continuous `w` with `|w| ≤ ε_I`, and
constant `C ∈ [C_min, C_max]`.

## 7. Design records

Machine-readable design records live in `designs/*.json` with decimal strings
(exact rationals). They are the single source for the numbers used by the Lean
instance and by the experiments. Current record: `designs/illustrative-1v8.json`
(illustrative, not fitted).

## 8. Experiment schema

Draft; workstream F owns the final record format. Every experiment record names
the design record and its SHA-256, the code version, the solver and tolerances,
seeds, and whether each reported check was completed or only proposed.

## Change log

| Date | Version | Change | Reason |
| --- | --- | --- | --- |
| 2026-11-09 | v0 | Initial draft by coordinator. | Start of project. |

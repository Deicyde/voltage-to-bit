# Shared interface

Owner: coordinator. Status: **v1.1, 2026-11-11** (v1, frozen 2026-11-10, with
corrections of prose only; see the change log). The findings of the
adversarial review (workstream E), of the independent fact-check and of five
verification rounds are dispositioned in `docs/review-disposition.md`; the
findings of workstreams A, B, D and F are recorded in their own documents
(`docs/source-audit.md`, `docs/model.md`, `docs/discrepancy-report.md`,
`docs/experiment-loop.md`). A later change needs a new version line in the log
at the end. The Lean sources under `VoltageToBit/` are authoritative
wherever this prose and the Lean differ; report any difference as a defect.

Base layer (owner decision, 2026-11-09): the circuit level. The primitives are
one lumped node and a compact transistor law. Nothing here is derived from
field theory or from semiconductor physics, and no such derivation is planned.

## 1. Circuit identity

Static CMOS inverter, one dynamic state.

| Element | Connection |
| --- | --- |
| PMOS | source = supply rail `VDD`, gate = input `u`, drain = output node `v` |
| NMOS | source = ground (0 V), gate = input `u`, drain = output node `v` |
| Load | lumped capacitance from output node to ground |

State: output node voltage `v(t)`. Input: gate voltage `u(t)`, an arbitrary
real-valued function of time for the universal guarantee. §6 says for which
inputs trajectories are known to exist.

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

`V_tp` is the magnitude of the PMOS threshold. The expressions are defined for
all real parameters; an admissible record (§6) has nonnegative lower bounds for
both thresholds. The expressions are also defined
for all real `u`, `v`; for `v` outside `[0, VDD]` they describe reverse
conduction (source/drain exchange). Lean: `In`, `Ip`, `Inet` in
`Model/Device.lean`, with lemmas `In_cutoff`, `In_triode`, `In_sat`,
`Ip_cutoff`, `Ip_triode`, `Ip_sat` identifying the textbook regions in forward
operation and `In_rev_*`, `Ip_rev_*` in reverse operation. This is the
channel-current law of ngspice MOS Level 1 with `LAMBDA = 0` and `GAMMA = 0` at
the model's nominal temperature: a reading of the ngspice source and a
numerical comparison of the two formulas (`docs/model.md` §3.2;
`docs/assumptions.md` EMP-07). No simulator was run, a Level 1 device also has
junction diodes and other elements, and this is not a Lean statement about
ngspice.

Parameters `θ = (VDD, k_n, k_p, V_tn, V_tp)` lie in a box given by the design
record (`Design.InBox`). In the ODE form they are constant during a run
(`IsTrajectory.of_ode`) or move within the box (`IsTrajectory.of_ode_varying`);
the trajectory notion of §4 only requires a point of the box at each instant.

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
| Load | `c ∈ [C_min, C_max]` at each instant | a voltage-dependent (incremental) capacitance; for a capacitance that changes in time, the current `(dc/dt)·v` is not part of `c` and has to fit in `ε_I` |
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
`ε_m + ε_w ≤ ε_I` (`IsTrajectory.of_sandwich`). For a current law `J(u, v)`
and an explicit set `U` of input values the comparison is a statement about
`U` and the safe domain alone, and the input waveform must stay in `U`
(`IsTrajectory.of_static_sandwich`). Both lemmas also require the node
capacitance of the other description to lie in `[C_min, C_max]` at every
instant. Where every member of the box carries the same net current the box
gives no slack and the other model must agree to within `ε_m` in absolute
terms. The header of `Proofs/ModelError.lean` gives one such place: for an
admissible record, at a grounded node with the input at or above
`VDD_max − V_tp,min`, every box member's net current is zero
(`Design.InBox.Inet_ground_eq_zero`). It gives a second place where only the
NMOS currents of all box members coincide: for inputs at or below `V_tn,min`
and a node at or above ground they are zero (`Design.InBox.In_eq_zero`), so
conduction below threshold has to fit between PMOS currents of the box or into
`ε_m`. These lemmas say nothing about whether solutions of the other model
exist.

Feedthrough and coupling. Let the output node be tied by constant linear
capacitors to ground (`C_L`), to the input (`C_M ≥ 0`, gate-drain) and to one
neighbouring node `g` (`C_c ≥ 0`), and let `C_min > 0`. If the node charge
`C_L·v + C_M·(v − u) + C_c·(v − g)` is continuous on `[a, b]` and has at every
instant of `[a, b)` the right derivative `I_net(u, v; θ) + w` for one parameter
point `θ` of the box (the same at every instant), the input and the neighbour
are continuous on `[a, b]` with right derivatives of magnitude at most `S_u`
and `S_g`, the total `C_L + C_M + C_c` lies in `[C_min, C_max]`,
`|w| ≤ ε_w`, and

```text
C_M · S_u + C_c · S_g + ε_w ≤ ε_I
```

then `v` is a trajectory (`IsTrajectory.of_charge_balance`). This is the one
place where a slew bound enters. The guarantee of §6 assumes none; a node with
feedthrough is shown to be among its trajectories only under such a budget. An
input with a jump at an instant of `(a, b)` is outside this lemma (one that
jumps exactly at `a` and already has its new value there is continuous on
`[a, b]`). With `C_M > 0` and a continuous neighbour, a continuous `v` cannot
conserve charge across a jump of `u`.

### 4.1 Physical reading of the envelopes (not part of any theorem)

These are environment restrictions, conventions and unresolved physical
assumptions. They are recorded in `docs/assumptions.md`: rows ENV-07 to ENV-10
and ENV-13 (environment restrictions), PHY-04 (the disturbance budget, with
leakage and near-threshold conduction), PHY-02 (a box that brackets a real
device), PHY-03 and PHY-14 (the admissibility of such a box, its margins
included) and PHY-07 (noise). None of them is proved.

- **Capacitance.** `c` is the incremental capacitance `∂Q/∂v` of the output
  node, with every attached capacitor counted once. Currents caused by *other*
  nodes moving (gate-drain feedthrough `C_M · du/dt`, coupling to a neighbour
  `C_c · dg/dt`, supply motion through junction capacitance) are not part of
  `c`; they belong to `ε_I`. The first instance therefore covers an ideal
  grounded capacitor load plus the inverter's own parasitics, not a switching
  gate load.
- **Additive allowance.** For `ε_I` to mean something physically, the
  environment must bound the input slew, the gate-drain capacitance, aggressor
  coupling, supply slew, leakage and near-threshold conduction so that their sum
  stays below `ε_I`. Each design record has a budget table in the notes file
  beside it. An amplitude bound is a poor description of crosstalk, which is
  bounded in charge; that is a known limitation of this model form.
- **Parameter box.** Process spread, supply range and allowance for model form
  all live in the box. A box wide enough to bracket a given real device may be
  much wider than an illustrative one, and the margins must be recomputed for
  it.
- **Noise.** Thermal, flicker and telegraph noise have no pointwise bound and
  are outside the theorem. For this node thermal noise is about 0.5 to 0.9 mV
  rms, more than a hundred standard deviations below the noise margins of the
  illustrative record; that is a probabilistic remark, not a guarantee.
- **Temperature** is not a parameter. A design record applies to whatever
  temperature range its box was chosen to cover.

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

Side conditions of absolute thresholds when the supply varies (they are where
the physical residual concentrates; see `docs/model.md` §8.2): the opposing
device is generally *not* off at the valid input level. In the illustrative
record the PMOS still conducts at `u = V_IH` when the supply is high (its
contention current is subtracted in `I_dn`), and `V_IL` sits only 0.05 V below
the smallest NMOS threshold, where a real device conducts a little although the
square law says zero.

## 6. What is proved

For a design record `D` satisfying a finite list of numeric conditions
(`Design.Admissible`, 26 conditions: positivity and ordering of the bounds of
the box and of the capacitance range, nonnegative threshold bounds,
`0 ≤ ε_I`, a safe domain that reaches to or beyond ground and the highest
supply, the ordering `0 ≤ V_OL ≤ V_IL < V_IH ≤ V_OH ≤ VDD_min`, and six
current-margin inequalities; row DEF-06 of `docs/assumptions.md` lists them one
by one), for every input
`u` and every trajectory `v` on `[a, b]` with `v(a) ∈ [V_lo, V_hi]`:

1. Safe domain (`IsTrajectory.safe`): `v(t) ∈ [V_lo, V_hi]` for all `t ∈ [a, b]`.
2. Low in, high out (`IsTrajectory.rise`): if `u ≤ V_IL` on `[s, e) ⊆ [a, b]`
   then `v(t) ≥ V_OH` for all `t ∈ [s + τ_up, e]`.
3. High in, low out (`IsTrajectory.fall`): if `u ≥ V_IH` on `[s, e) ⊆ [a, b]`
   then `v(t) ≤ V_OL` for all `t ∈ [s + τ_dn, e]`.
4. Decoded form (`IsTrajectory.decoded`): if the input decodes to one and the
   same bit at every instant of `[s, e) ⊆ [a, b]`, the output decodes to the
   opposite bit on `[s + τ, e]`, with `τ = τ_up` for a low input and
   `τ = τ_dn` for a high input.

How to read "every input" and "every trajectory":

- These are statements about all trajectories that exist for the given input.
  They have instances only for inputs that have trajectories. Existence is
  proved for continuous inputs and for an input with one jump that takes its
  new value at the jump instant (see "Also proved"). The trajectory notion
  evaluates the input at each instant, so the value at a jump instant matters.
- The window may have any length. If it is shorter than the deadline the
  conclusion is empty.
- If the input is neither valid-low nor valid-high throughout the window, only
  statement 1 applies. The output may then decode to either bit or to
  undefined.
- Nothing is said about a trajectory that starts outside the safe domain. The
  trajectory notion constrains the derivative only while `v` is inside it.

The six margins are closed-form numbers of the record, and
`Proofs/Margins.lean` proves, for an admissible record and every `θ` in the
box, that the device law provides at least these currents, each in its own
region: `I_up(c)` into the node for `u ≤ V_IL` and `v ≤ c ≤ VDD_min`; `I_dn(c)`
out of the node for `u ≥ V_IH` and `v ≥ c ≥ 0`; `R_hiP` (for `u ≤ u_Hi`) and
`R_hiN` (for `u ≥ u_Hi`) out of a node at `V_hi`; `R_loN` (for `u ≥ u_Lo`) and
`R_loP` (for `u ≤ u_Lo`) into a node at `V_lo`:

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

Safe-domain invariance is proved from the four boundary margins exceeding
`ε_I`. That is the condition the proof uses. It is sufficient, not necessary:
each margin bounds the restoring current with one transistor on one side of a
proof-only split point, and the restoring current of the model itself is
larger (`Examples/Limits.lean`). A rule of thumb such as "`VDD_min` exceeds the
sum of the largest thresholds" is neither necessary nor sufficient, but it
points at the right quantity: the restoring current at an excursion `δ` is
roughly `k · δ · (VDD − V_tn − V_tp)`, so it shrinks with the voltage headroom.
For the illustrative record it is the boundary margins (2.312 to 3.136 µA), not
the switching margins (10.476 and 16.296 µA), that cap the admissible `ε_I`
(see the notes file beside the record); for another record a switching margin
can be the smaller one.

For a run at one supply value `V0` of the record's range the safe domain can
be measured from that supply (`Proofs/AtSupply.lean`). For
`VDD_min ≤ V0 ≤ VDD_max` the record restricted to the single supply value
`V0`, with safe domain `[V_lo, V0 + (V_hi − VDD_max)]`, is again admissible
(`Design.Admissible.atSupply`); no condition beyond admissibility is needed. So
every trajectory of the restricted record that starts in that interval stays
in it (`trajectory_safe_atSupply`), and so does every solution of the node
equation with constant parameters that starts in the interval of its own
supply (`solution_safe_atSupply`). This is proved for a
supply that is the same number at every instant of the run. For a supply that
moves within its range, only the fixed domain `[V_lo, V_hi]` is proved
invariant, and the model-error obligation of §4 then has to be met on all of
it, which reaches 0.46 V above the lowest supply in the illustrative record.
For runs at one supply value the physical claim should be read with the
supply-relative domain.

Also proved:

- Existence and uniqueness (`exists_solution`, `solution_unique`,
  `exists_trajectory`): for constant `θ` in the box, continuous `u`, continuous
  `w` with `|w| ≤ ε_I`, and a capacitance function with values in
  `[C_min, C_max]` that is Lipschitz on the safe domain, the ODE has exactly one
  solution on any `[a, b]` from any initial state in the safe domain. Here `u`
  and `w` are continuous on the whole real line, and "solution" means a
  derivative within `[a, b]` at every point of `[a, b]`; uniqueness is not
  stated for the weaker notion that `IsTrajectory.of_ode` accepts. For an input
  that is continuous on `[a, b]` only, existence is stated for the illustrative
  record on `[0, 10]` (`Examples.exists_second_stage`), not in general.
  Existence is not proved for parameters that move in time or for less regular
  data; for those the guarantee is a statement about whatever trajectories
  there are.
- Non-vacuity for every admissible record (`Proofs/NonVacuity.lean`).
- Refined deadlines from a list of intermediate levels
  (`Design.ValidRiseCert`, `Design.ValidFallCert`, `IsTrajectory.rise_of_cert`,
  `IsTrajectory.fall_of_cert`): a certificate is a list of voltage levels; validity is
  arithmetic; the theorem is proved once for all lists.
- For the illustrative record, the deadlines and how far they can be improved
  (`Examples/RefinedDeadlines.lean`, `Examples/Limits.lean`,
  `Examples/DeadlineBrackets.lean`):

  | Direction | Closed form `τ` (rounded up) | Proved with a 16-level certificate | False for every deadline below |
  | --- | --- | --- | --- |
  | Rise (low in, high out) | 3.43 ns | 2.26 ns | 2.168 ns |
  | Fall (high in, low out) | 2.57 ns | 1.425 ns | 1.0234 ns |

  The closed-form deadlines are `7250/2119 ≈ 3.4214` ns and
  `4575/1787 ≈ 2.5602` ns. For `2.168 ≤ τ < 2.26` (rise) and
  `1.0234 ≤ τ < 1.425` (fall) no theorem of the library states that the
  deadline holds or that it is false. The four ends are rounded numbers, not
  sharp limits: the slow runs behind the false ends (`Examples.slow_rise_run`,
  `Examples.slow_fall_run`) imply slightly more, up to about 2.16806 ns and
  1.02349 ns, and that refinement is not stated as a theorem (see the header of
  `Examples/DeadlineBrackets.lean`). The "false below" column is shown by an
  explicit run that starts in the safe domain (`Examples.rise_deadline_bracket`,
  `Examples.fall_deadline_bracket`).
- Bounds on how fast the output can move, for inputs confined to a stated
  range `[u_lo, u_hi]` (`IsTrajectory.rise_at_most`,
  `IsTrajectory.fall_at_most`). Without such a range there is no minimum
  delay. The library states one instance and not the general fact: for the
  illustrative record, with the valid-low input held at −1 V, there is a run
  that starts at the valid-low level 0.25 V and is valid-high at 38 ps
  (`Examples.valid_low_input_can_give_valid_high_within_38ps`); and the rising
  slew at the start has no bound over the valid-low class
  (`Examples.valid_low_rise_slew_unbounded`).
- Two stages in series (`chain_low`, `chain_high` in `Proofs/Chain.lean`): a
  valid-low input of the first stage on `[s, e)` gives a valid-low output of
  the second stage on `[s + τ_up(first) + τ_dn(second), e]`, and the mirror
  image. The second stage is a trajectory whose input is the first stage's
  output. The lemmas need the compatibility `V_IH(second) ≤ V_OH(first)`,
  respectively `V_OL(first) ≤ V_IL(second)`; for two copies of one admissible
  record both hold. A witness for the illustrative record is in
  `Examples/TwoStage.lean`. Each stage is still the one-node model: neither
  the loading of the first node by the second gate nor the feedthrough from
  the first output into the second output is modelled beyond the capacitance
  ranges and `ε_I` of the two records. For the illustrative record that is not
  physically plausible (header of `Proofs/Chain.lean`: the 2 µA allowance
  would need a gate-drain capacitance below about 0.03 fF), so the corollary
  is a statement about two ideal one-node stages.
- Gluing of trajectories and existence for an input with one jump that takes
  its new value at the jump instant (`Proofs/Concat.lean`). For an input that
  keeps its old value at the jump instant a trajectory across the jump need
  not exist. One case is proved, for the illustrative record: for the
  full-swing falling step that is 1.8 V for `t ≤ 4` and 0 V afterwards, no
  trajectory on `[0, 10]` starts in the safe domain
  (`Examples.stepL_no_trajectory`, `Examples.step_input_scope`); for that input
  the guarantee is silent on `[0, 10]`. Nothing is stated about other jumps,
  other states of the node at the jump, or that input on other intervals.
- Negative controls (`Examples/NegativeControls.lean`): records that fail the
  arithmetic checks, a miswired device law, an allowance that is too large,
  and a rejected certificate. Each claim that is shown false is refuted by an
  explicit run that starts in the safe domain.
- Limits of the proof method for the illustrative record
  (`Examples/Limits.lean`): no choice of the two split points makes the record
  admissible with `ε_I ≥ 2.3802 µA`; with re-chosen split points 2.3801 µA is
  admissible.

## 7. Design records

Machine-readable design records live in `designs/*.json` with decimal strings
(exact rationals). They are the single source for the numbers used by the Lean
instance and by the experiments. `scripts/gen_design.py` generates the Lean
record; `scripts/check.sh` verifies the two are in sync. Current record:
`designs/illustrative-1v8.json` (illustrative, not fitted). Each record has a
notes file beside it (`designs/illustrative-1v8.notes.md`) stating its status,
the environment budget under which its `ε_I` has a physical reading, and how
it relates to any real process.

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
| 2026-11-09 | v1 candidate (rev. 3) | Added §4.1 (physical reading: incremental capacitance, capacitor load only, what gives `ε_I` meaning, noise, temperature), threshold side conditions, the exact invariance condition, the supply-relative safe domain, step inputs, and per-record notes files. No theorem changed. | Workstream B proposals IP-2 to IP-8 and IP-10 (`docs/model.md`). IP-9 (comparison plan) is for workstream D; IP-11 and IP-12 are deferred. |
| 2026-11-10 | v1 (frozen) | `Design.Admissible` gains `0 ≤ V_tn,min` and `0 ≤ V_tp,min` (26 conditions); the supply-relative safe domain no longer needs an extra condition and is stated for trajectories as well as ODE solutions. Added: how to read "every input", the static form of the model-error obligation, the charge-balance lemma with its slew budget, the deadline table with proved and refuted ends, the step-input scope as compiled statements, negative controls, and the limit on the provable `ε_I`. Base layer recorded as circuit level. After verification round 3 (prose only; no theorem changed): the exact hypotheses of the model-link lemmas (capacitance range; sign conditions and one parameter point in the charge balance), the regions of the six margins, invariance from the boundary margins as a sufficient condition, the supply-relative domain for trajectories that start in it, the existence and uniqueness class, the deadline gap with its rounded ends, the 38 ps run as one instance, the two-stage reading, the step-input scope with its interval, and the full names of the certificate theorems. | Workstream E findings and their independent re-verification (`docs/review-disposition.md`); workstream F results (`docs/experiment-loop.md`); owner decisions of 2026-11-09; verification round 3 (`evidence/verification/round3.json`, entries `prose` and `register`). |
| 2026-11-11 | v1.1 | Prose only; no definition or theorem changed. §4: an input with a jump at an instant of `(a, b)` is outside the charge-balance lemma, and one that jumps exactly at `a` and already has its new value there is continuous on `[a, b]` (was: "a jump inside `[a, b]`"). §4.1: what the section records is called environment restrictions, conventions and unresolved physical assumptions, and the register rows of the parameter box (PHY-02, PHY-03, PHY-14) are cited. §6: the supply-relative domain is the reading for runs at one supply value, and for a supply that moves the model-error obligation has to be met on the whole fixed domain; existence for an input continuous on `[a, b]` only is stated for the illustrative record on `[0, 10]`. This log: in the v1 row, "no theorem changed" now applies to the changes after verification round 3 only. Status line: v1.1. | Verification round 4 (`evidence/verification/round4.json`, entry `prose`, issues 7, 8, 10, 11 and 12). Issue 11 named PHY-02 and PHY-03 for the box; PHY-14 is cited as well, because the margins that the box bullet says must be recomputed include the two switching margins, which are in PHY-14 and not in PHY-03. A new version line, not an addition to the v1 row, because the header asks for one for every change after the freeze. |

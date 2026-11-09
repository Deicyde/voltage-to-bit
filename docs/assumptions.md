# Assumption register

Workstream B. Prepared 2026-11-09. Initial version.
This register lists everything the inverter claim rests on, and says for each item what kind of support it has.

## How to read it

A label is not evidence. Each row has two separate fields:

- **Evidence type** says what kind of support the item could have.
- **Discharge status** says whether that support is actually in hand.

The five evidence types are those of the handoff.

| Type | Meaning in this register |
| --- | --- |
| definition | A choice of words or numbers. Nothing to prove. Its relation to the physical world is always a separate row. |
| proved consequence | Follows from the definitions. Machine-checked in the repository at the pinned commit unless the row says "by hand" or "scratch". |
| environment restriction | A condition on the inverter's surroundings that the project chooses to assume. It narrows the claim. Only the user of the theorem can discharge it. |
| empirical evidence | Something observed, with its source. A finite sample never discharges a statement quantified over a continuum. |
| unresolved assumption | A claim about the physical world, or about a reference model, that the physical reading needs and that nobody has established. |

No row assigns a numerical residual bound. None has a justification yet.
`TBD (C)` marks a Lean name that does not exist yet. `TBD (D)` marks a check that workstream D has not run. `TBD (E)` marks a review that workstream E has not done.

## Pinned artifacts

| Short name | Artifact |
| --- | --- |
| `L@fe9f401` | Lean sources at commit `fe9f401af6026cf67f49b4ccebc9b9f4f54ef40d` |
| `IF` | `docs/interface.md`, "v1 candidate (rev. 2)", sha256 `973bb7fcd996d8f704cfcad3fe70c47c606bb32117345ea1c84e1685e3c9aeba` |
| `DR` | `designs/illustrative-1v8.json`, sha256 `06ccc32a64938f43350d6fb68d991c15e62b9d6815f0b174391be073727bc967` |
| `M` | `docs/model.md`, sha256 `5550139b536c5042e14ed1f2e800b3257e41188254cd51eff8dc061674ec0a78` |
| `A-py` | The Python block of `M` Appendix A, sha256 `9a9f48f30c6e44b545f42a31767f06d93973b70416a6904bf7ef5167c69957c0` |
| `B-lean` | The Lean block of `M` Appendix B, sha256 `9ee8b0f5e1f25a0522b0819780a3906af9b291764dae97b843b18ab0820f1a15` |

B did not rebuild the Lean project. Rows that cite `L@fe9f401` rely on the sources and on `evidence/lean/audit.txt` at that commit.

Notation: `psq(x) = max(x, 0)²`. `abs(x)` is the absolute value. Units are V, µA, fF, ns and µA/V².

## Definitions

| ID | Exact mathematical statement | Domain / units | Consumer theorems | Evidence type | Source or artifact hash | Discharge status | Responsible agent |
| --- | --- | --- | --- | --- | --- | --- | --- |
| DEF-01 | Voltages in V, currents in µA, capacitances in fF, times in ns, `k` in µA/V². `1 µA / 1 fF = 1 V/ns`. | all quantities | every theorem, through the reading of the numbers | definition | `IF` §2; `DR` | Convention. Nothing to discharge. | Coordinator |
| DEF-02 | `I_n(u, v) = (k_n/2)·(psq(u − V_tn) − psq(u − v − V_tn))`. `I_p(u, v) = (k_p/2)·(psq(VDD − u − V_tp) − psq(v − u − V_tp))`. `I_net = I_p − I_n`. | `u, v` real, in V; currents in µA | every theorem | definition | `L@fe9f401` `Model/PosSq.lean`, `Model/Device.lean` (`psq`, `In`, `Ip`, `Inet`) | Definition. Its relation to a device is PHY-02. | C |
| DEF-03 | Record `illustrative-1v8`: `VDD ∈ [1.62, 1.98]`; `k_n ∈ [160, 240]`; `k_p ∈ [80, 120]`; `V_tn, V_tp ∈ [0.45, 0.60]`; `C ∈ [5, 20]`; `ε_I = 2`; `V_IL = 0.40`, `V_IH = 1.25`, `V_OL = 0.25`, `V_OH = 1.35`; `V_lo = −0.10`, `V_hi = 2.08`; split points `uHi = 0.77`, `uLo = 0.74`. | V, µA/V², fF, µA | `Examples.illustrative_*` | definition, labelled ILLUSTRATIVE | `DR`; `L@fe9f401` `Examples/IllustrativeDesign.lean` | Values are unsourced by design. No physical provenance exists or is claimed. | Coordinator |
| DEF-04 | `v` is a trajectory on `[a, b]` for input `u` iff `v` is continuous on `[a, b]` and for every `t ∈ [a, b)` there are a right derivative `v'` and `c ∈ [C_min, C_max]` such that, if `v(t) ∈ [V_lo, V_hi]`, some `θ` in the box has `abs(c·v' − I_net(θ)(u(t), v(t))) ≤ ε_I`. | `t` in ns | all guarantee theorems | definition | `L@fe9f401` `Model/Inverter.lean` (`IsTrajectory`) | Definition. Before commit `eae25ed` the point `θ` was fixed per run. | C |
| DEF-05 | `decode(lo, hi, x)` is low if `x ≤ lo`, high if `x ≥ hi`, and undefined otherwise. Inputs use `(V_IL, V_IH)`. Outputs use `(V_OL, V_OH)`. | V | `IsTrajectory.decoded` | definition | `L@fe9f401` `Model/Inverter.lean` (`decode`, `Design.decodeIn`, `Design.decodeOut`) | Definition. | C |
| DEF-06 | Margins `I_up(c)`, `I_dn(c)`, `R_hiP`, `R_hiN`, `R_loN`, `R_loP` as written in `IF` §6. `τ_up = C_max·(V_OH − V_lo)/(I_up(V_OH) − ε_I)`. `τ_dn = C_max·(V_hi − V_OL)/(I_dn(V_OL) − ε_I)`. `Admissible` is: box consistency; `V_lo ≤ 0`; `VDD_max ≤ V_hi`; `0 ≤ V_OL ≤ V_IL < V_IH ≤ V_OH ≤ VDD_min`; and `ε_I` below each of the six margins. | µA, ns | `Design.Admissible`; `rise`, `fall` | definition | `L@fe9f401` `Model/Inverter.lean` | Definition. | C |

## Proved consequences

| ID | Exact mathematical statement | Domain / units | Consumer theorems | Evidence type | Source or artifact hash | Discharge status | Responsible agent |
| --- | --- | --- | --- | --- | --- | --- | --- |
| PC-01 | For `v ≥ 0` (NMOS) and `v ≤ VDD` (PMOS) the device law equals the piecewise cutoff, linear and saturation expressions. | forward operation | none; documents DEF-02 | proved consequence | `L@fe9f401` `In_cutoff`, `In_triode`, `In_sat`, `Ip_cutoff`, `Ip_triode`, `Ip_sat` | Discharged in Lean. | C |
| PC-02 | For all real `u, v`: `I_n` and `I_p` equal the channel current of ngspice MOS Level 1 with `LAMBDA = 0` and `GAMMA = 0`, at nominal temperature, under source/drain exchange. | all `u, v` | D's Level 1 identity check; `M` §3.2 | proved consequence, by hand; not machine-checked | `M` §3.2; ngspice `mos1load.c` and `mos1temp.c` read on 2026-11-09, commit not pinned | The equality of `In`, `Ip` with the piecewise law, forward and with source and drain exchanged, is discharged in Lean (`In_rev_cutoff`, `In_rev_triode`, `In_rev_sat`, `Ip_rev_cutoff`, `Ip_rev_triode`, `Ip_rev_sat`, commit `499cb39`). That the piecewise law is what ngspice implements remains a hand reading of its source. Confirmation in the simulator: `TBD (D)`. A supporting sample is EMP-05. | B, then C and D |
| PC-03 | `illustrative.Admissible`. `I_up = 10.476`, `I_dn = 16.296`, `R_hiP = 2.4`, `R_hiN = 2.312`, `R_loN = 3.04`, `R_loP = 3.136`, `τ_up = 7250/2119`, `τ_dn = 4575/1787`. | µA, ns | all `Examples.*` | proved consequence | `L@fe9f401` `Examples.illustrative_admissible`, `illustrative_Iup`, `illustrative_Idn`, `illustrative_RhiP`, `illustrative_RhiN`, `illustrative_RloN`, `illustrative_RloP`, `illustrative_tauUp`, `illustrative_tauDn` | Discharged in Lean. Recomputed independently by `A-py`. | C |
| PC-04 | For every `θ` in the box: `I_net ≥ I_up(c)` when `u ≤ V_IL` and `v ≤ c ≤ VDD_min`; `I_net ≤ −I_dn(c)` when `u ≥ V_IH` and `v ≥ c ≥ 0`; `I_net(u, V_lo) > ε_I` and `I_net(u, V_hi) < −ε_I` for every `u`. | µA | `safe`, `rise`, `fall` | proved consequence | `L@fe9f401` `Design.Inet_ge_Iup`, `Inet_le_neg_Idn`, `Inet_Vlo_gt`, `Inet_Vhi_lt` | Discharged in Lean. | C |
| PC-05 | For an admissible record, every input and every trajectory with `v(a) ∈ [V_lo, V_hi]`: `v` stays in `[V_lo, V_hi]`; `u ≤ V_IL` on `[s, e)` implies `v ≥ V_OH` on `[s + τ_up, e]`; `u ≥ V_IH` on `[s, e)` implies `v ≤ V_OL` on `[s + τ_dn, e]`. | V, ns | the headline claim | proved consequence | `L@fe9f401` `IsTrajectory.safe`, `.rise`, `.fall`, `.decoded`; `Examples.illustrative_guarantee` | Discharged in Lean, as a statement about DEF-04. It says nothing about a device. | C |
| PC-06 | Existence and uniqueness of ODE solutions for constant `θ`, continuous `u`, continuous `w` with `abs(w) ≤ ε_I`, and a Lipschitz capacitance in range. An explicit run shows both logic directions. | — | non-vacuity of PC-05 | proved consequence | `L@fe9f401` `exists_solution`, `solution_unique`, `exists_trajectory`, `Examples.illustrative_scenario` | Discharged in Lean. | C |
| PC-07 | Bridges. ODE solutions are trajectories. A current law that is bracketed on the safe domain by two box members up to `ε_m`, together with a disturbance within `ε_w` and `ε_m + ε_w ≤ ε_I`, yields trajectories. | µA | the physical-coverage argument | proved consequence, conditional | `L@fe9f401` `IsTrajectory.of_ode`, `.of_ode_varying`, `.of_model_error`, `.of_sandwich`, `Design.exists_inBox_of_between` | Discharged as mathematics. The hypotheses are PHY-02, PHY-04 and PHY-05. | C |
| PC-08 | With inputs in `[ulo, uhi]`, `v` rises no faster than `(IchargeMax + ε_I)/C_min` and falls no faster than `(IdischargeMax + ε_I)/C_min`. For the illustrative record and valid inputs these are 28.6 and 58.3 V/ns. | V/ns | `rise_at_most`, `fall_at_most`; ENV-07 for a following stage | proved consequence; the two numbers are B's arithmetic | `L@fe9f401` `Proofs/Contamination.lean`; `M` §7.4 | The formula is discharged in Lean. The numbers are discharged in Lean as `Examples.illustrative_max_rise_slew` (28.5508) and `Examples.illustrative_max_fall_slew` (58.3144, inputs in `[1.25, 1.98]`). | C, B |
| PC-09 | If `D` is admissible, `VDD_min ≤ V0 ≤ VDD_max` and `ε_I < RhiN'`, then `D.atSupply V0` is admissible. For the illustrative record `RhiN' = 2.312`, and the restricted safe domain is `[−0.10, V0 + 0.10]`. | V, µA | the proposed supply-relative form of every theorem (`M` IP-2) | proved consequence, scratch | `B-lean`; `lake env lean`, Lean 4.35.0, 2026-11-09 16:25; no errors; axioms `propext`, `Classical.choice`, `Quot.sound` | Type-checked by B outside the repository. Ported by the coordinator in commit `1fdf1d9` as `Proofs/AtSupply.lean` (`Design.Admissible.atSupply`, `solution_safe_atSupply`, `Examples.illustrative_safe_atSupply`); builds and passes the axiom audit. B did not rebuild or review that commit. Independent review: `TBD (E)`. | B, then C |
| PC-10 | The exact minimum over `u` of the boundary restoring current is `M(H, δ; k_a, k_b)` of `M` §6.1. For the illustrative record: 5.92 µA at `V_lo`, 6.44 µA at `V_hi`, 3.56 µA at `VDD + δ`. | µA | none; a cross-check on PC-04 for workstream E | derived by hand and checked numerically; not machine-checked | `M` §6.1; `A-py` item 3 | Not in Lean. `TBD (C)` if wanted. | B |

## Environment restrictions

| ID | Exact mathematical statement | Domain / units | Consumer theorems | Evidence type | Source or artifact hash | Discharge status | Responsible agent |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ENV-01 | Topology: PMOS source and bulk on the supply node; NMOS source and bulk on ground; both gates on `u`; both drains on `v`; no other conducting element on `v`. | — | the reading of DEF-02; no Lean consumer | environment restriction | `IF` §1 | Holds by construction in a test bench. Unverified for any layout. | D, Coordinator |
| ENV-02 | Rails: the NMOS source is at 0 V at all times. `VDD(t) ∈ [VDD_min, VDD_max]`. For the supply-relative claim `VDD` is constant during the run. | V | the box in DEF-04; PC-09 | environment restriction | `M` §7.2 | `IF` does not state it as a restriction. Ground bounce is not covered at all. | Coordinator |
| ENV-03 | Input validity: `u(t) ≤ V_IL` for all `t ∈ [s, e)`, or `u(t) ≥ V_IH` for all `t ∈ [s, e)`. | V, ns | hypothesis `hu` of `rise`, `fall`, `decoded` | environment restriction; a theorem premise | `L@fe9f401` | Premise. Supplied by whoever drives `u`. | user of the theorem |
| ENV-04 | Window: `e − s > τ_up`, respectively `e − s > τ_dn`. | ns | non-vacuity of the conclusions of `rise` and `fall` | environment restriction; a theorem premise | `L@fe9f401` `Design.Admissible.exists_rise_run`, `exists_fall_run` show that such runs exist | Premise. | user of the theorem |
| ENV-05 | Initial state: `v(a) ∈ [V_lo, V_hi]`. For the physical claim: `v(a) ∈ [V_lo, VDD + δ]`. | V | hypothesis `h0` of every guarantee theorem; PC-09 | environment restriction; a theorem premise | `L@fe9f401` | Premise. | user of the theorem |
| ENV-06 | Input regularity for existence: `u` is continuous. | — | `exists_solution`, `exists_trajectory` | environment restriction | `L@fe9f401` | Premise of existence only. The guarantee does not use it. | C |
| ENV-07 | Input slew: `abs(u(t₂) − u(t₁)) ≤ S_u·abs(t₂ − t₁)`, with `C_M,max·S_u ≤ ε_Miller`. Budget A: `S_u = 2 V/ns`, `C_M,max = 0.5 fF`, `ε_Miller = 1.0 µA`. | V/ns, fF, µA | PHY-04; no Lean consumer | environment restriction | `M` §7.2, §7.3 | Not in `IF`. Violated by `Examples.uRamp` (9 V/ns) for any `C_M > 0.22 fF`, and by the first stage of `Proofs/Chain.lean` (PC-08) for any `C_M > 0.07 fF`. | Coordinator to adopt; D to respect in benches |
| ENV-08 | Aggressors: `Σ_i C_c,i·S_a,i ≤ ε_couple`. Budget A: `ε_couple = 0.5 µA`, or no switching neighbour. | fF, V/ns, µA | PHY-04; no Lean consumer | environment restriction | `M` §7.2, §7.3 | Not in `IF`. | Coordinator |
| ENV-09 | Load: all charge storage on `v` is capacitive with incremental capacitance `∂Q/∂v ∈ [C_min, C_max]`. No series resistance or inductance between the devices and the load. First instance: an ideal linear capacitor to ground plus the inverter's own parasitics, and no switching gate load. | fF | `c ∈ [C_min, C_max]` in DEF-04; `rise_at_most` and `fall_at_most` use `C_min` | environment restriction | `M` §4.2 | `IF` §1 says "lumped capacitance to ground". It does not say incremental, and it does not exclude a gate load. | Coordinator, D |
| ENV-10 | Temperature: one declared temperature or range per run, and the box is claimed for it. | °C | PHY-02, PHY-03 | environment restriction | `M` §3.4, §6.4 | Stated nowhere. The illustrative record implies none. | Coordinator |
| ENV-11 | Input range: `u(t) ∈ [−δ, VDD + δ]` with `δ = 0.10 V`. | V | PHY-02, PHY-09; no Lean consumer, since the theorems hold for every `u` | environment restriction | `M` §4.4, §6.3 | Not in `IF`. | Coordinator |
| ENV-12 | Excursion and latch-up: the output stays within `δ ≤ 0.10 V` of its actual rails, and no parasitic thyristor conducts. | V | PHY-06 | environment restriction for the first part; unresolved assumption for the second | `M` §6.2, §6.3; JEITA ED-5003A Tables 1 and 4 | The first part is PC-05 for the fixed domain and PC-09 for the supply-relative one. Absence of latch-up cannot be derived from the model and is assumed. | Coordinator |

## Unresolved physical assumptions

| ID | Exact mathematical statement | Domain / units | Consumer theorems | Evidence type | Source or artifact hash | Discharge status | Responsible agent |
| --- | --- | --- | --- | --- | --- | --- | --- |
| PHY-01 | Lumped quasi-static node: `d/dt Q(v; u, VDD, a) = i_p − i_n + i_leak`, where the channel currents are functions of the present terminal voltages only. No interconnect state and no internal device state. | — | every theorem, since it justifies a scalar inclusion | unresolved assumption | `M` §4.1, §7.2 | Not discharged. B's transit-time estimate of about 1 ps suggests it is benign for edges slower than 10 ps. | D for evidence |
| PHY-02 | Model-form containment: for all `t` and all `x ∈ [V_lo, V_hi]` there are `θ₁, θ₂` in the box with `I_net(θ₁)(u(t), x) − ε_m ≤ J(t, x) ≤ I_net(θ₂)(u(t), x) + ε_m`, where `J` is the true net channel current. | µA | `IsTrajectory.of_sandwich` | unresolved assumption | `M` §5 | Not discharged. No value of `ε_m` and no fitted box has a justification. For the illustrative box and a SKY130 device B expects it to be false, because that box is narrow and its thresholds are 0.2 to 0.35 V too low. | D for evidence; Coordinator for the box |
| PHY-03 | Headroom for the real device: the box that satisfies PHY-02 also satisfies `ε_I < R_hiP, R_hiN, R_loN, R_loP`. In exact form: `M(VDD_min − V_tn,max − V_tp,max, δ; k_min) > ε_I` at both boundaries, with thresholds no lower than the device's real ones over the claimed corners and temperatures. | V, µA | `IsTrajectory.safe`, through `Design.Admissible` | unresolved assumption | `M` §6.4; EMP-01 | The arithmetic holds for the illustrative box, whose headroom is 0.42 V. For SKY130 high-density cell devices at the slow corner and 1.60 V, EMP-01 gives a headroom between −0.02 and −0.14 V. B expects the condition to FAIL there. Untested. | D for evidence; Coordinator for the decision |
| PHY-04 | Disturbance budget: `abs(w(t)) ≤ ε_w`, where `w = C_M·u' + Σ_i C_c,i·a_i' + C_jp·VDD' + i_leak + i_off`, and `ε_m + ε_w ≤ ε_I`. | µA | `IsTrajectory.of_ode`, `.of_sandwich` | unresolved assumption | `M` §7 | Not discharged. Under ENV-07, ENV-08 and Budget A it holds by arithmetic on assumed coefficients. No coefficient has been extracted from a model or measured. | D for coefficients; Coordinator |
| PHY-05 | Capacitance: `C_min ≤ ∂Q/∂v ≤ C_max` for all `v ∈ [V_lo, V_hi]` and all admitted values of `u`, supply and neighbour voltages; and `abs(∂Q/∂u) ≤ C_M,max`. | fF | `c ∈ [C_min, C_max]` in DEF-04; ENV-07 | unresolved assumption | `M` §4.2 | Not discharged. Self-loading is estimated at 1 to 2 fF from model-card values. | D |
| PHY-06 | Reverse conduction: for `v ∈ [−δ, 0)` and for `v ∈ (VDD, VDD + δ]` the real net restoring current is at least that of the lower-envelope square law. Junction and body effects only add restoring current. | µA | `IsTrajectory.safe`, through PHY-02 at the boundaries | unresolved assumption | `M` §6.2 | Not discharged. Supported by a physical argument only. | D |
| PHY-07 | Noise: thermal, flicker and telegraph noise are absent. What is ignored: `sqrt(kT/C)` is 0.46 to 0.91 mV rms at 300 K for 20 to 5 fF. | mV | every theorem | unresolved assumption; a deterministic bound cannot discharge it | `M` §7.5 | Not discharged, by design. A probabilistic argument would be a separate layer. | Coordinator |
| PHY-08 | Retired. Stationarity: `θ` does not change during a run. | — | the fixed-`θ` `IsTrajectory` of commit `1880a36` | unresolved assumption, no longer needed | `M` §5 | Removed by commit `eae25ed`, which lets `θ` differ at every instant. Kept here as a record of the removal. | Coordinator |
| PHY-09 | Comparison-model validity: the SKY130 BSIM4 cards are used inside their documented ranges, that is drain-source and gate-source magnitudes up to 1.95 V, and forward body bias up to 0.3 V (NMOS) and 0.1 V (PMOS). | V | every future EMP row that uses BSIM4 | unresolved assumption about the reference model | EMP-01 | Violated by design when `VDD > 1.95 V`, when `v > 1.95 V`, and for excursions more than 0.1 V above the supply. Results there are extrapolations of the reference. | D |
| PHY-10 | Opposing-device residual: for `u ≤ V_IL` the real NMOS current is at most `(k_n,max/2)·psq(V_IL − V_tn,min) + ε_off`; for `u ≥ V_IH` the real PMOS current is at most `(k_p,max/2)·psq(VDD_max − V_IH − V_tp,min) + ε_off`. | µA | `Design.Inet_ge_Iup`, `Inet_le_neg_Idn`, through PHY-02 | unresolved assumption. A special case of PHY-02, kept separate because here the hard threshold errs in the unsafe direction. | `M` §3.4, §7.2 | Not discharged. B's estimate of `ε_off` is 0.1 to 0.3 µA, from an interpolation formula quoted from memory. | D |

## Empirical evidence

| ID | Exact mathematical statement | Domain / units | Consumer theorems | Evidence type | Source or artifact hash | Discharge status | Responsible agent |
| --- | --- | --- | --- | --- | --- | --- | --- |
| EMP-01 | SKY130 device documentation. Thresholds at `L = 0.15 µm` over model corners and e-test limits: NMOS 0.603 to 0.852 V; PMOS high-threshold 0.678 to 0.963 V; PMOS standard 0.554 to 0.858 V. Typical drain currents at 7/0.15 µm: 3.512 mA (NMOS), 1.003 mA (PMOS high-threshold), 1.347 mA (PMOS standard). Stated model validity: magnitudes up to 1.95 V; bulk-source +0.3 V (NMOS) and −0.1 V (PMOS). | V, mA | PHY-03, PHY-09; `M` §6.4, §10 | empirical evidence: vendor documentation comparing model and e-test. Not a measurement by this project. | `google/skywater-pdk` at `7198cf647113f56041e02abf3eb623692820c5e1`, `docs/rules/device-details/` for `nfet_01v8`, `pfet_01v8`, `pfet_01v8_hvt` | Read on 2026-11-09. The page gives neither extraction method nor bias. Used for orders of magnitude only. | B |
| EMP-02 | SKY130 `sky130_fd_sc_hd__inv_1`: `nfet_01v8` 0.65/0.15 µm and `pfet_01v8_hvt` 1.0/0.15 µm. Input capacitance 2.302 fF. Leakage power 0.0001958 and 0.0104575 nW at tt, 25 °C, 1.8 V; 0.7000129 and 14.5579575 nW at ff, 100 °C, 1.95 V. Characterised input transitions 0.01 to 1.5 ns between 20 % and 80 %. Characterised loads 0.5 to 181 fF. | fF, nW, ns | `M` §4.2, §7.2 | empirical evidence: vendor library characterisation, which is itself simulation | `google/skywater-pdk-libs-sky130_fd_sc_hd` at `ac7fb61f06e6470b94e8afdf7c25268f62fbd7b1` | Read on 2026-11-09. | B |
| EMP-03 | SKY130 model-card values, first bin only: `toxe` 4.148 nm (NMOS) and 4.23 nm (PMOS high-threshold); `cgdo` 2.449e-10 and 5.932e-11 F/m; `cjs` 1.340e-3 and 7.433e-4 F/m²; `jss` 2.75e-3 and 2.17e-5 A/m²; level 54, version 4.5; `tnom` 30. | SI | `M` §4.2, §6.2 | empirical evidence: vendor model parameters | `google/skywater-pdk-libs-sky130_fd_pr` at `f62031a1be9aefe902d6d54cddd6f59b57627436`, the `tt.pm3.spice` files of `nfet_01v8` and `pfet_01v8_hvt` | Read on 2026-11-09. The bin is for L 20 to 100 µm and W 7 to 100 µm. It is not the 0.15 µm bin. | B |
| EMP-04 | 1.8 V interface standard: supply 1.65 to 1.95 V; `V_IH ≥ 0.65·VDD`; `V_IL ≤ 0.35·VDD`; inputs from −0.3 V to `VDD + 0.3 V`; absolute maximum −0.5 V to `VDD + 0.5 V`. | V | `M` §6.3, §8.2; ENV-12 | empirical evidence: a published standard | JEITA ED-5003A, May 2005, Tables 1 and 4 | Read on 2026-11-09. The JEDEC original was not accessed. | B |
| EMP-05 | The positive-part form and the piecewise Level 1 law agree at 200 000 random points with `u, v ∈ [−1, 3]`. The largest difference is 4.5e-13 µA. | µA | PC-02 | empirical evidence: a numerical check on a finite sample | `A-py` item 1 | Supports PC-02. Not a proof. | B |
| EMP-06 | Comparison of the formal model with ngspice Level 1 and with SKY130 BSIM4. | — | PHY-01 to PHY-06, PHY-09, PHY-10 | empirical evidence: none yet | `M` §9 is the plan | Not started. ngspice is not installed. | D |

## What would discharge the unresolved items

| ID | What would count | What would not count |
| --- | --- | --- |
| PHY-01 | A transient comparison against a reference with internal device state, over the admitted slews. | An argument from the transit-time estimate alone. |
| PHY-02 | An envelope fit against the pinned reference for a declared corner set and temperature range, with an argument that covers the points between samples, for example monotonicity together with a derivative bound. Or measurement. | The largest residual seen on a grid. |
| PHY-03 | The four boundary margins evaluated on the reference at the slow corner, lowest supply and lowest temperature, with the same caveat about points between samples. Or a recorded decision to narrow the claim (`M` §10.3). | The illustrative record's arithmetic. |
| PHY-04 | Extracted values of `C_M`, `C_c`, `C_jp`, leakage and near-threshold current, together with stated slew bounds. | Budget A as it stands. Its coefficients are assumed. |
| PHY-05 | `∂Q/∂v` and `∂Q/∂u` extracted over the safe domain and over the input range. | A single capacitance value at one bias. |
| PHY-06 | Reverse-region sweeps inside the reference model's validity range (PHY-09), including the mid-rail valley. | The symmetry argument. |
| PHY-07 | Nothing deterministic. | Any bound on a Gaussian tail. |
| PHY-09 | Keeping every evaluated bias inside the documented ranges, or a statement from the model's owner that extends them. | Smooth-looking curves outside the range. |
| PHY-10 | Off-device current sweeps of the reference near the valid input levels, at the fast corner and highest temperature. | The interpolation formula used for the estimate. |

## Open names

| Item | Needed from |
| --- | --- |
| Reverse-operation equality with the piecewise law (PC-02) | done, commit `499cb39` |
| Slew numbers 28.6 and 58.3 V/ns as theorems (PC-08) | done, `Examples/NegativeControls.lean` |
| Independent review of `Proofs/AtSupply.lean` at commit `1fdf1d9` (PC-09) | E |
| Valley minimum `M(H, δ; k_a, k_b)` (PC-10) | C, if wanted |
| Level 1 identity check and BSIM4 comparison (PC-02, EMP-06) | D |

## Change log

| Date | Change | By |
| --- | --- | --- |
| 2026-11-09 | Initial register, against commit `fe9f401`. PHY-08 entered as retired because commit `eae25ed` removed the need for it. PC-09 updated when commit `1fdf1d9` ported it. | B |
| 2026-11-09 | Discharge status of PC-02, PC-08 and PC-09 and the open-names table updated after the Lean additions. ENV-02 and ENV-07 to ENV-12 are now stated in prose in `docs/interface.md` §4.1 (rev. 3) and budgeted in `designs/illustrative-1v8.notes.md`; they remain unproved environment restrictions. No physical assumption was discharged. | Coordinator |

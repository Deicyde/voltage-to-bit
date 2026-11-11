# Circuit model and physical interpretation

Workstream B. Prepared 2026-11-09. This file analyses the draft model and proposes changes to it.
It does not change the shared interface; the coordinator owns `docs/interface.md`.
Corrected on 2026-11-09 after an independent fact-check, and on 2026-11-10 after the second and third verification rounds. Every change is listed in the last section, "Corrections after the independent fact-check (2026-11-09)".

Checked against:

| Artifact | Version |
| --- | --- |
| Lean core and `README.md` | commit `fe9f401af6026cf67f49b4ccebc9b9f4f54ef40d`, 16:25 on 2026-11-09 |
| `docs/interface.md` | "v1 candidate (rev. 2)" at that commit, sha256 `973bb7fcd996d8f704cfcad3fe70c47c606bb32117345ea1c84e1685e3c9aeba` |
| `designs/illustrative-1v8.json` | sha256 `06ccc32a64938f43350d6fb68d991c15e62b9d6815f0b174391be073727bc967` |
| `HANDOFF.md` | sha256 `c56544e4031fffa982402ef146e53f939d9dbfd662fb561f374be237a9ba261f` |

The repository moved while this was written.
B's analysis started from commit `1880a3619453d865a04f3b32d25edf69af618501`, where `IsTrajectory` took one fixed parameter point `θ` per run.
Commit `eae25edfb9bcd99d436bbaf37312f74f5d43ab16` (16:24) changed that: the parameter point is chosen per instant, and the model-error obligation is a sandwich between two members of the box.
B had reached the same proposal independently (§5.4).
Commit `1fdf1d9c00d313c36c9b5c70d7f0b222dee264af` (16:33) ported the lemma of Appendix B into `Proofs/AtSupply.lean`.
Statements tagged [L] refer to the commit in the table. B did not review the later commits.

## 0. How to read this document

The handoff keeps three statuses apart: formal correctness, applicability, and physical evidence.
This document is about the third, and about what the first two mean physically.

It contains no measurement and no SPICE run. ngspice is not installed on this machine.
Every statement about a real device or about BSIM4 is either taken from a cited source or is an estimate that workstream D has to test.

Owner decision, recorded 2026-11-09: the project's base layer stays at circuit level, and no derivation from field theory is planned.
Owner decision, recorded 2026-11-09: no further numerical experiments and no SPICE comparison are planned, so the comparison plan of §9, with every instruction to, and every expectation of work by, workstream D in this document, is prepared, not planned to be run for this milestone; physical evidence stays "none" (§11), and every statement in this document about a real device is to be read as an expectation or an assumption, never as a result.

Each claim carries one of these tags.

| Tag | Meaning |
| --- | --- |
| **[S]** | Read in the cited primary source during this session. Sources and versions are in §12. |
| **[S-bib]** | Bibliographic data confirmed. The text itself was not read. |
| **[M]** | From memory, not verified. A pointer, not evidence. |
| **[D]** | Derived here by hand or by the script in Appendix A, from stated inputs. Reproducible arithmetic. Not a proof, and not evidence about silicon. |
| **[L]** | Proved in Lean at the commit above, according to the sources and `evidence/lean/audit.txt` at that commit. B did not rebuild the project. |
| **[L-scratch]** | Type-checked by B with `lake env lean` against the project's build products. The file is in Appendix B and is not part of the repository. |
| **[search]** | Seen only in search-result summaries. Weaker than [S-bib]. |

Sections 1 to 11 answer the coordinator's eight questions. Section 12 lists sources.
The appendices hold the reproduction script and the scratch Lean file.
The section "Interface proposals" lists every proposed change.
The last section lists the corrections made on 2026-11-09 after the independent fact-check and on 2026-11-10 after the second and third verification rounds.

## 1. Findings in brief

1. **The draft arithmetic is right.** `I_up = 10.476 µA`, `I_dn = 16.296 µA`, `τ_up = 3.42 ns`, `τ_dn = 2.56 ns` reproduce exactly [D], and Lean proves the same values [L]. The boundary figures "2.3 to 3.1 µA" are the four split bounds of the proof (`RhiN = 2.312`, `RhiP = 2.4`, `RloN = 3.04`, `RloP = 3.136`) [L]. The true minima of the restoring current are larger: 5.92 µA at the bottom and 6.44 µA at the top [D].
2. **The device law is SPICE MOS Level 1 with `LAMBDA = 0` and `GAMMA = 0`, exactly,** including reverse conduction by source/drain exchange (§3.2).
3. **The bridge from the model to a real device was unusable in its first form and is repaired in the current one.** At commit `1880a36`, `IsTrajectory.of_model_error` asked for one fixed `θ` whose square law is within `ε_m ≤ ε_I = 2 µA` of the true current on the whole safe domain. A 0.15 µm transistor cannot meet that: the expected mismatch is tens of microamps (§5.2). Since commit `eae25ed` the parameter point is chosen per instant and the obligation is a sandwich between two box members (`IsTrajectory.of_sandwich`) [L]. B had checked the same change independently. This repairs the formulation. It does not yet give physical coverage: the box must be wide enough to bracket the real device, and the margins must survive that widening (§5.4).
4. **Safe-domain invariance by reverse conduction is sound mathematics that depends on voltage headroom.** The margin is roughly `k · δ · (VDD − V_tn − V_tp)`. The illustrative box has 0.42 V of headroom. The documented SKY130 thresholds leave about +0.05 V at the typical corner and between −0.02 and −0.14 V at the slow corner for `VDD = 1.60 V` (§6.4). For that corner the smallest restoring current over the input of a square law with the documented thresholds is 0 to 0.6 µA at the boundary for `δ = 0.1 V`, below `ε_I = 2 µA` [D]. B therefore expects that the four boundary conditions of the proof cannot all hold for a box that brackets SKY130 devices at that corner and supply. This is an untested expectation from documentation values: no device was simulated or measured, and a failed sufficient condition of the proof would not by itself show that a circuit fails.
5. **The fixed upper bound `V_hi = VDD_max + δ` admits states 0.46 V above the actual supply** when `VDD = VDD_min`. That is outside the documented validity of the SKY130 PMOS model, and how much the drain junction conducts there is an open question (§6.3). The same design record already implies the tighter bound `v ≤ VDD + δ` for a run at any one supply value: restricting an admissible record to one supply keeps it admissible (§6.3) [L-scratch].
6. **`ε_I = 2 µA` is far below realistic coupling currents.** Gate-drain feedthrough is `C_M · du/dt`. With `C_M` of 0.2 to 1 fF and library-realistic input slews of 5 to 50 V/ns that is 1 to 50 µA (§7). The explicit run in `Examples/Illustrative.lean` uses a 9 V/ns input ramp; with any gate-drain capacitance above 0.22 fF that ramp alone uses the whole 2 µA. In the two-stage corollary the first stage's output may slew at up to 29 to 58 V/ns by the model's own bounds, which leaves room for less than 0.07 fF (§7.4). Note added 2026-11-09: the run meant is `Examples.illustrative_scenario`. The same file now also has `Examples.illustrative_feedthrough_scenario`, an explicit run in which feedthrough, coupling and a residual current together use the allowance exactly, with an input slew of at most 2 V/ns (§7.4). Note added 2026-11-10: the 29 to 58 V/ns are bounds for first-stage inputs restricted to `[0, 0.40]` V (rising output) and to `[1.25, 1.98]` V (falling output). For the valid-input classes of the guarantee, which have no such range, the output slew has no bound (§7.4).
7. **`C_min ≤ C ≤ C_max` is a sound abstraction only if `C` means the incremental capacitance `∂Q/∂v`** and every current caused by another node moving is carried in the disturbance (§4.2). The first instance therefore covers an ideal grounded capacitor load, not a switching gate load.
8. **Thermal noise is outside any deterministic envelope.** Its effect on the node is about 0.5 to 0.9 mV rms for 20 to 5 fF (§7.5).
9. **Recommended comparison model:** SkyWater SKY130 BSIM4 (level 54, version 4.5) `nfet_01v8` and `pfet_01v8_hvt`, pinned as in §9.
10. **The illustrative record should stay labelled illustrative.** Its thresholds are about 0.15 to 0.35 V below SKY130's documented short-channel thresholds for the NMOS and the high-threshold PMOS, the two device types of the comparison cell, and its `VDD_max = 1.98 V` is above the 1.95 V limit of the SKY130 model documentation (§10).

## 2. Units

The unit system is volts, microamps, femtofarads and nanoseconds, with `k` in µA/V². It is coherent [D]:

```text
1 µA / 1 fF = 1e-6 A / 1e-15 F = 1e9 V/s = 1 V/ns
```

So `C · dv/dt = I` can be evaluated with no conversion factor. The derived units follow.

| Quantity | Unit | Check |
| --- | --- | --- |
| Charge | fC | fF · V = µA · ns |
| Conductance | µS | µA / V |
| Resistance | MΩ | V / µA |
| Time constant | ns | MΩ · fF |
| Slew rate | V/ns | µA / fF |
| Energy | fJ | fF · V² |
| Power | µW | µA · V |
| Transconductance parameter | µA/V² | |

Conversion from SPICE, which uses SI units [S, NGM §7.6.1]:
`KP` in A/V² times 1e6; capacitance in F times 1e15; time in s times 1e9; current in A times 1e6.
Instance `W` and `L` are in metres.

Labelling rules proposed for design records:

- The Lean reals are dimensionless. Only the design record gives them units.
- Each record carries a status word: `ILLUSTRATIVE`, `FITTED` (with model, commit and method), or `MEASURED`.
- For an illustrative record the units are real and the values are unsourced. Reports should say "2 µA (illustrative)", never a bare "2 µA".
- A normalized number, for example time in units of `C/(k·V)`, must be labelled normalized and must not be printed with ns, V or µA.

## 3. Circuit and device law

### 3.1 Definition

Static CMOS inverter. PMOS: source at the supply `VDD`, gate at the input `u`, drain at the output `v`.
NMOS: source at ground, gate at `u`, drain at `v`. One state, the output voltage `v`.

With `x₊ = max(x, 0)`:

```text
I_n(u, v) = (k_n / 2) · ( (u − V_tn)₊² − (u − v − V_tn)₊² )          output → ground
I_p(u, v) = (k_p / 2) · ( (VDD − u − V_tp)₊² − (v − u − V_tp)₊² )    supply → output
I_net     = I_p − I_n                                                into the output node
```

`V_tp > 0` is a magnitude. These are `VoltageToBit.In`, `Ip` and `Inet` in `Model/Device.lean`.

### 3.2 Exact correspondence with SPICE MOS Level 1

**Claim.** For all real `u`, `v` and all `k ≥ 0`, `I_n(u, v)` equals the channel current of an ngspice Level 1 NMOS with `LAMBDA = 0`, `GAMMA = 0`, `VTO = V_tn` and `KP · W / (L − 2·LD) · M = k_n`, source and bulk at 0, gate at `u`, drain at `v`. The same holds for the PMOS with all voltages mirrored and `VTO = −V_tp`.

**What Level 1 computes** [S, NGSRC `mos1load.c`]. The routine sets the mode from the sign of `vds`.
In inverse mode it uses `vgd` in place of `vgs` and `−vds` in place of `vds`, which is source/drain exchange.
With `vgst` the gate overdrive and `vds'` the non-negative drain-source voltage:

```text
vgst ≤ 0           : cdrain = 0
vgst ≤ vds'        : cdrain = Beta · (1 + LAMBDA·vds') · vgst² / 2            saturation
otherwise          : cdrain = Beta · (1 + LAMBDA·vds') · vds' · (vgst − vds'/2)   linear
Beta = KP · M · W / (L − 2·LD)
```

The channel contributes `mode · cdrain` to the drain terminal current. With `GAMMA = 0` and the device at the model's nominal temperature, the threshold is `VTO` in both modes and `Beta` uses `KP` unscaled [S, NGSRC `mos1temp.c`]. At other temperatures Level 1 rescales both.

**Proof of the claim** [D]. Write `a = u − V_tn`.

- Forward, `v ≥ 0`. If `a ≤ 0` both positive parts vanish, giving 0. If `0 < a ≤ v` the second vanishes, giving `k a²/2`. If `a > v` the difference is `(k/2)(a² − (a − v)²) = k(a v − v²/2)`.
- Reverse, `v < 0`. The acting source is the output. The overdrive is `a − v` and the acting drain-source voltage is `−v`. If `a − v ≤ 0` both terms vanish. If `a ≤ 0 < a − v` the result is `−(k/2)(a − v)²`, reverse saturation. If `a > 0` the result is `−k((a − v)(−v) − v²/2)`, reverse linear. Each is minus the Level 1 value, which is the correct sign for a current defined from output to ground.

**Checks.** The script in Appendix A compares the two forms at 200 000 random points with `u, v ∈ [−1, 3]`.
The largest difference is 4.5e-13 µA, which is rounding [D].
Lean proves the forward cases as `In_cutoff`, `In_triode`, `In_sat`, `Ip_cutoff`, `Ip_triode`, `Ip_sat` [L].
The reverse cases are not Lean lemmas. They hold by the same algebra.
Note added 2026-11-09: "The reverse cases are not Lean lemmas" describes the reference commit `fe9f401` only. Since commit `499cb39`, which also introduced this document, the reverse cases are Lean lemmas as well: `In_rev_cutoff`, `In_rev_triode`, `In_rev_sat`, `Ip_rev_cutoff`, `Ip_rev_triode`, `Ip_rev_sat` in `VoltageToBit/Model/Device.lean`.

**Parameter map.**

| Model | ngspice Level 1 | Source |
| --- | --- | --- |
| `k_n`, `k_p` | `KP · W / (L − 2·LD) · M` of the respective card | [S, NGSRC] |
| `V_tn` | `VTO` of the NMOS card, positive | [S, NGM §7.6.2.5] |
| `V_tp` | `−VTO` of the PMOS card | [S, NGM §7.6.2.5] |
| no channel-length modulation | `LAMBDA = 0`, the default | [S, NGM parameter table] |
| no body effect | `GAMMA = 0`, the default; `PHI` then has no effect on the channel current at the nominal temperature (`T = TNOM`). At other temperatures the Level 1 threshold depends on `PHI` even with `GAMMA = 0`, and `PHI` enters the Meyer capacitances when `TOX` is given. A Level 1 control should therefore run at `TNOM` or record `PHI`. | [S, NGM parameter table; NGSRC `mos1temp.c`, `mos1load.c`] |

**What an ngspice Level 1 device still contains with these settings** [S, NGM parameter table; NGSRC `mos1load.c`]:
bulk junction diodes with default `IS = 1e-14 A`, whose current is subtracted from the drain current; the simulator's `GMIN` in parallel with each junction; and capacitances if `CGSO`, `CGDO`, `CGBO`, `CBD`, `CBS`, `CJ`, `CJSW` or `TOX` are given.
The manual states that the Meyer capacitance model used by Level 1 does not conserve charge.
An identity check against the formal model must therefore leave all capacitance parameters unset and make the junction current negligible. See §9.4.

### 3.3 Provenance of the name

- The square law for switching-circuit simulation is due to Shichman and Hodges, 1968 [S-bib, SH68]. B did not read the paper, so no claim here rests on its text.
- SPICE2's Level 1 is described as the Shichman-Hodges model, implemented according to Nagel's 1975 SPICE2 report [S, VL80 p. 1]. The same memo defines `VTO` as the extrapolated zero-bias threshold of a long, wide device, neglecting weak inversion, and says Level 1 has zero output conductance when `LAMBDA` is not given [S, VL80 pp. 3–4].
- The ngspice manual calls Level 1 the Shichman-Hodges model and says it applies only to long-channel devices [S, NGM §7.6.2.1].
- The single-expression form with a forward and a reverse term is the strong-inversion limit of the EKV formulation, which refers all voltages to the substrate so that source and drain are interchangeable [S-bib, EKV95; the formulas used in §6 are from memory, M].

### 3.4 What the law omits

"Unsafe" means the real current deviates in the direction that weakens a bound used by the proofs.
The on-device is the one that should conduct; the opposing device is the one that should be off.

| Omitted effect | In a real device or BSIM4 | Direction of the error | Size |
| --- | --- | --- | --- |
| Channel-length modulation | Current keeps rising with drain-source voltage in saturation. | On-device: safe if `k` is fitted at low drain-source voltage. Opposing device: unsafe at high drain-source voltage. | 5 to 15 % of the saturation current over the swing for 0.15 µm [M]. |
| Body effect, threshold shift | Threshold depends on source-bulk voltage. | None in forward operation: each source is tied to its bulk [D]. In reverse operation the acting source is forward-biased against the bulk, which lowers the threshold. Safe. | Tens of millivolts at 0.1 V excursion [M]. |
| Body effect, bulk-charge factor | Saturation current and saturation voltage are reduced by a factor `1/n` even at zero source-bulk voltage. | A `k` taken from the linear region overestimates saturation current by `n`. Unsafe if the wrong fit is used. | `n ≈ 1.2 to 1.5` [M]; `n ≈ 1.3` from the card's `k1 = 0.54` [D from S]. |
| Subthreshold and moderate inversion | Exponential tail below threshold. | On-device: safe. Opposing device: unsafe, since the model says exactly zero. | At threshold 0.3 to 0.8 µA; 0.05 V below it 0.1 to 0.3 µA; 0.2 V below it under 0.01 µA, at 27 °C. About twice that near threshold at 125 °C, at equal distance from the threshold [D, formula M]. |
| Velocity saturation | Saturation current grows like overdrive to a power between 1 and 2 [S-bib, SN90]. Saturation voltage is below the overdrive. | Depends on the fit. One square law cannot follow the curve. | Best uniform fit of a square law to a power-law curve leaves 2.4 to 4.9 % of the on-current for exponents 1.5 to 1.2 [D]. That is 3.5 to 15 µA at 150 to 300 µA. |
| Mobility degradation, series resistance | Less current at high overdrive. | Same as velocity saturation. | Not estimated. |
| Drain-induced barrier lowering | Threshold falls as drain-source voltage rises. | Opposing device: unsafe. | Not estimated. |
| Gate leakage | Tunnelling through the oxide. | Loads the input node, not the output. | Negligible at 4.1 to 4.2 nm oxide [S for thickness, M for the conclusion]. |
| Junction diodes | Reverse leakage; forward conduction beyond a rail. | Forward conduction restores the node. Safe for invariance, but it injects carriers (§6.2). | Set by junction parameters that this document does not fix. Level 1 default diode (`IS = 1e-14 A`, emission coefficient 1, Level 1 temperature law): 1.1e-3 µA at 0.3 V, 2.5 µA at 0.5 V and 119 µA at 0.6 V at 27 °C; 1.0, 22 and 145 µA at 0.3, 0.4 and 0.46 V at 100 °C. Ideal-diode law with the junction parameters of the SKY130 cards (first bin) and an assumed drain 0.3 µm long: 0.06 to 0.10 µA at 0.6 V at 27 °C; 0.09 to 0.16 µA at 0.46 V at 100 °C [D from S, Appendix A item 8; parameters from NGSRC and SKY-PR]. Arithmetic, not a simulation. |
| Junction, overlap and channel capacitances | Charge storage on the node and coupling to other nodes. | Enter `C` and the disturbance (§4, §7). | 1 to 2 fF of self-loading for the SKY130 `inv_1` [D from S]. |
| Non-quasi-static effects | Channel charge needs a transit time to rearrange. | Adds state. | Transit time about `L²/(μ·V_ov)`: 1.0 ps (NMOS) and 2.7 ps (PMOS) for `L = 0.15 µm`, the long/wide-bin `u0` = 0.0319 and 0.0121 m²/(V·s) [S, SKY-PR] and 0.7 V of overdrive [D]. Negligible for edges slower than 10 ps, with less margin for the PMOS. |
| Temperature | Mobility and threshold move with temperature. | Unsafe unless the box covers the temperature range. | `k` falls roughly 35 % from 27 to 125 °C; thresholds fall 0.1 to 0.2 V [M]. |
| Mismatch, ageing, random telegraph noise | Parameters differ per device and drift. | Box or tube must cover them. | Not estimated. |

### 3.5 Structural properties [D]

- `∂I_net/∂v = −k_p (v − u − V_tp)₊ − k_n (u − v − V_tn)₊ ≤ 0`. The net current never increases with the output voltage. This gives forward uniqueness for fixed `c` and `w`.
- `I_n` is non-decreasing in `u` for `v ≥ 0` and non-increasing in `u` for `v < 0`. `I_p` is non-increasing in `u` for `v ≤ VDD`.
- For `v ≥ 0`, `I_n` is non-decreasing in `k_n` and non-increasing in `V_tn`. For `v < 0` both reverse. So the extreme currents over a box are always attained at corners.

## 4. Dynamics, trajectory class and capacitance

### 4.1 From charge balance to the inclusion

Kirchhoff's current law at the output node, for a lumped quasi-static circuit:

```text
d/dt Q(v; u, VDD, a_1, …, a_m) = i_p − i_n + i_leak
```

`Q` is the total charge on all capacitor plates attached to the node. The `a_i` are other node voltages coupled to it.
Expanding the derivative:

```text
c(t) · v' = i_p − i_n + w(t)
c(t) = ∂Q/∂v
w(t) = −(∂Q/∂u)·u' − (∂Q/∂VDD)·VDD' − Σ_i (∂Q/∂a_i)·a_i' + i_leak
```

For linear two-terminal capacitors this is:

```text
c = C_L + C_jn(v) + C_jp(VDD − v) + C_M + Σ_i C_c,i
w = C_M·u' + Σ_i C_c,i·a_i' + C_jp·VDD' + i_leak
```

`C_L` is the load to ground. `C_jn` and `C_jp` are the drain junction capacitances to substrate and to the n-well.
`C_M` is the gate-drain capacitance of both transistors. `C_c,i` couples to aggressor `i`.

`v` is then an `IsTrajectory` if it is continuous and has a right derivative at every instant (§4.3) and, while `v` is in the safe domain:

1. `c(t) ∈ [C_min, C_max]`, and
2. `|w(t) + (i_p − i_n) − I_net(θ)(u, v)| ≤ ε_I` for some `θ` in the box, which may differ from instant to instant.

This is a sufficient condition, not an equivalence: the definition asks only for some `c` in the range at each instant, so membership does not show that the physical `∂Q/∂v` lies in the range.
Lean proves sufficient conditions of this kind as `IsTrajectory.of_ode`, `of_ode_varying`, `of_model_error` and `of_sandwich` [L]. Each is a one-way implication, and each asks for the balance equation and the capacitance bound at every instant of `[a, b)`, not only while `v` is in the safe domain.
Those theorems state the obligation. They are not evidence that a physical node meets it.
Note added 2026-11-09, rewritten on 2026-11-10 for the library at commit `8c2637b`: `VoltageToBit/Proofs/ModelError.lean` has two further one-way lemmas of this kind, `IsTrajectory.of_static_sandwich` (§5.1) and `IsTrajectory.of_charge_balance`. The second is the linear-capacitor case above with one aggressor `a_1` (`g` in Lean) and one parameter point `θ`. It concludes that `v` is a trajectory. Its hypotheses are these, and no others:

| Hypothesis, in the notation of this section | Name and form in Lean |
| --- | --- |
| `C_M ≥ 0` and `C_c ≥ 0` | `hCM : 0 ≤ CM`, `hCc : 0 ≤ Cc` |
| `C_min > 0`, and `C_L + C_M + C_c` lies in `[C_min, C_max]` | `hClo : 0 < D.Clo`, `hC1 : D.Clo ≤ CL + CM + Cc`, `hC2 : CL + CM + Cc ≤ D.Chi` |
| `C_M·S_u + C_c·S_a + ε_w ≤ ε_I` | `hbudget : CM * Su + Cc * Sg + εw ≤ D.eps` |
| `θ` is a point of the box | `hθ : D.InBox θ` |
| `u` and `a_1` have a right derivative at every instant of `[a, b)` | `hu`, `hg` |
| those right derivatives have magnitude at most `S_u` and `S_a` | `hSu`, `hSg` |
| the residual `w` has magnitude at most `ε_w` at every instant of `[a, b)` | `hw` |
| the charge `C_L·v + C_M·(v − u) + C_c·(v − a_1)` is continuous on `[a, b]` | `hqcont` |
| `u` and `a_1` are continuous on `[a, b]` | `hucont`, `hgcont` |
| at every instant of `[a, b)` the charge has right derivative `I_net(θ)(u, v) + w` | `hq` |

Continuity of `v` is not a hypothesis: the proof derives it from the three continuity hypotheses.
The lemma gives the input slew bound of §4.4 and §7.3 a Lean consumer. For a waveform that is continuous on `[a, b]`, a bound `S` on the right derivative is a slew bound, `|u(t) − u(s)| ≤ S·(t − s)` for `a ≤ s ≤ t ≤ b` (`slew_bound_of_rderiv` in the same file). Without continuity it is not: the step `Examples.uStepR` has right derivative zero at every instant and is not continuous on `[0, 10]` (`Examples.uStepR_hasDerivWithinAt_zero`, `Examples.uStepR_not_continuousOn`). An input that is not continuous on `[a, b]` is therefore outside the lemma; that includes every input with a jump at an instant of `(a, b)`.
Like the four theorems above, the two lemmas state an obligation and are not evidence that a physical node meets it.

### 4.2 What `C` comprises, and when the bounds are sound

**The bounds are a reasonable abstraction** because every contribution above is positive and bounded over the safe domain, and the proofs use only `c > 0` and `c ≤ C_max` for the deadlines and `c ≥ C_min` for the minimum-delay bounds `IsTrajectory.rise_at_most` and `fall_at_most` [L].
Lean lets `c` differ at every instant, so any dependence on state or time is covered.

**Conditions for soundness.**

- **`C` is the incremental capacitance `∂Q/∂v`,** not the secant value `Q/v`. For a junction, `∂Q/∂v` changes by a factor of about two over the swing [M].
- **Every capacitor attached to the node counts once in `c`,** including `C_M` and the coupling capacitors. The motion of the other terminal is a current in `w`. It is not a change of `c`.
- **Coupling must not be folded into `[C_min, C_max]` by Miller factors.** The old repository counted coupling at factors 0 and 2. That convention is known to be unsound: for ramp inputs the effective factor ranges over about −1 to 3 [S-bib, CKK00; the range is reported by a later paper citing prior work, not read in the original].
- **A switching gate load is not a capacitor.** The load's own gate-drain capacitance couples `v` to the load's output `y`. It adds `C_gd,load` to `c` and `C_gd,load · y'` to `w`. `y'` is large exactly while `v` crosses the load's threshold, which is inside the interval that `τ_up` measures. The first instance should therefore claim only an ideal grounded capacitor load.
- **Charge-based caveat.** `C(v)·dv/dt` equals `dQ/dt` only when `Q` depends on `v` alone. Otherwise the cross terms above appear. For MOS channel charge the cross terms are not reciprocal: the gate-to-drain and drain-to-gate coefficients differ [S-bib, WD78]. The inclusion handles this correctly as long as `|∂Q/∂u|` is bounded by the `C_M` used in the budget of §7.
- **Simulation caveat.** The Meyer capacitance model in ngspice Level 1 does not conserve charge [S, NGM §7.6.2.1]. This is a simulator issue. It matters for D's Level 1 controls and not for the inclusion.

**Orders of magnitude for the SKY130 `sky130_fd_sc_hd__inv_1`** (NMOS 0.65/0.15 µm, PMOS 1.0/0.15 µm [S, SKY-HD]).

| Quantity | Value | Basis |
| --- | --- | --- |
| Oxide capacitance | 8.32 and 8.16 fF/µm² | [D] from `toxe` = 4.148 and 4.23 nm [S, SKY-PR] |
| Gate area capacitance `C_ox·W·L` | 0.81 fF (N), 1.22 fF (P) | [D] |
| Gate-drain overlap | 0.16 fF (N), 0.06 fF (P) | [D] from `cgdo` = 0.245 and 0.059 fF/µm [S, SKY-PR, long/wide bin] |
| Liberty input capacitance | 2.30 fF at tt, 25 °C, 1.8 V | [S, SKY-HD]. Consistent with 0.81 + 1.22 + 2 × 0.22 = 2.47 fF [D]. |
| Drain junction, zero bias | about 0.4 to 0.6 fF per device | [D] from `cjs`, `cjsws`, `cjswgs` [S] with an assumed drain 0.3 µm long. The cell netlist gives no drain area. |
| Self-loading of the output | about 1 to 2 fF | [D] |
| Characterised loads | 0.5 to 181 fF | [S, SKY-HD] |

`C ∈ [5, 20] fF` then corresponds to external loads of roughly 3 to 19 fF. That is a plausible range.

### 4.3 The trajectory class

`IsTrajectory` requires a right derivative at every `t ∈ [a, b)` that satisfies the balance at that instant.

- This covers every solution driven by a right-continuous disturbance and input.
- It does not cover all solutions driven by a merely measurable bounded disturbance. Such a solution is Lipschitz and differentiable almost everywhere, but it can lack a right derivative at some instants.
- The regularity therefore sits in the solution concept. Version 0 of `docs/interface.md` did not say so. The v1 candidate does, as a known scope limit.
- A weaker class would bound the upper and lower right Dini derivatives instead. Mathlib's comparison lemmas already take hypotheses of that kind, for example `image_le_of_liminf_slope_right_lt_deriv_boundary'` [S, MATHLIB]. For continuous `u` that class contains every Carathéodory solution [D]. This is a low-priority generalisation.
- White thermal noise produces paths that are nowhere differentiable. They are outside either class.

### 4.4 Input waveform class

The guarantee theorems take any `u : ℝ → ℝ`. Physical coverage needs more.
Each restriction below is tied to the claim that uses it.

| Restriction | Used by |
| --- | --- |
| `u ≤ V_IL` on `[s, e)`, or `u ≥ V_IH` on `[s, e)` | Premise `hu` of `IsTrajectory.rise`, `fall`, `decoded` [L] |
| `e − s > τ` | Non-vacuity of the conclusion |
| `u` continuous | `exists_solution`, `exists_trajectory` [L]. Not used by the guarantee. |
| `u(t) ∈ [−δ, VDD + δ]` | Physical validity of the device law and of the comparison model only. No Lean consumer. |
| `u` is Lipschitz with constant `S_u`, that is, its slew never exceeds `S_u` | The physical justification of the disturbance bound when the node has gate-drain capacitance (§7). No Lean consumer. |

Note added 2026-11-09: the two "No Lean consumer" entries describe commit `fe9f401`. In the library at commit `8c2637b` an input range is a hypothesis of `IsTrajectory.of_static_sandwich` (the input stays in an explicit set of values, §5.1). Continuity of the input and a bound on its right derivative, which together are a slew bound, are hypotheses of `IsTrajectory.of_charge_balance` (§4.1). That lemma asks for more than the Lipschitz condition of the table: a right derivative at every instant of `[a, b)`. The guarantee theorems still take every `u`.

## 5. Uncertainty: box, tube, and what a real device must satisfy

### 5.1 What the Lean core offers

`θ = (VDD, k_n, k_p, V_tn, V_tp)` lies in a box.
Since commit `eae25ed` a trajectory needs, at each instant and while `v` is in the safe domain, some `c ∈ [C_min, C_max]` and some `θ` in the box with

```text
| c · v' − I_net(θ)(u, v) | ≤ ε_I
```

The parameter point may differ at every instant [L, `IsTrajectory`].
The link to another current law `J(t, x)` is `IsTrajectory.of_sandwich` [L]:

```text
for all t and all x in [V_lo, V_hi] there are θ₁, θ₂ in the box with
I_net(θ₁)(u(t), x) − ε_m  ≤  J(t, x)  ≤  I_net(θ₂)(u(t), x) + ε_m
```

together with a further disturbance bounded by `ε_w` and `ε_m + ε_w ≤ ε_I`.

Note added 2026-11-09: the library at commit `8c2637b` also has `IsTrajectory.of_static_sandwich` in `VoltageToBit/Proofs/ModelError.lean`. It is the same obligation for a current law `J(x, y)` that depends only on the input voltage `x` and the node voltage `y`: the bracketing is required for every `x` in an explicit set `U` and every `y` in the safe domain, and the input waveform is required to stay in `U`. The comparison is then a statement about two current laws on `U` and the safe domain, with no reference to time or to a waveform.

Before that commit `θ` was one point per run, and the obligation was closeness to one square law, within `ε_m`, on the whole safe domain.
§5.2 records why that could not work. The same arithmetic tells D what a fitted box has to look like.

### 5.2 Why one square law plus 2 µA cannot describe a real device

The on-currents of the illustrative devices are 40 to 280 µA over the box. A model-form error of a few percent already exceeds `ε_I`.

- **Shape of the saturation curve.** For a saturation current proportional to overdrive to the power 1.2 to 1.5, the best uniform square-law fit over the overdrive range misses by 2.4 to 4.9 % of the on-current. At 150 to 300 µA that is 3.5 to 15 µA. The best-fit threshold is also 0.16 to 0.30 V below the true one, so the fitted law conducts where the device is off [D, Appendix A item 4]. This is a statement about two formulas, not about SKY130.
- **Linear region against saturation.** For the SKY130 pair the low-field value `u0 · C_ox · W/L` is about 1150 µA/V² (N) and 660 µA/V² (P) [D from S; `u0` and `toxe` are from the long/wide bin]. The value that reproduces the documented saturation current is about 540 and 320 µA/V² [D from S, assuming the e-test current is taken at 1.8 V on gate and drain; the value depends on the threshold paired with that current, 489 to 578 and 298 to 345 µA/V² for the two tabulated typical thresholds, §6.4]. One `k` cannot serve both regions. The mismatch in the linear region at full gate drive is tens to hundreds of microamps.
- **A finite sample can refute a containment hypothesis rigorously but cannot establish it.** If at one sampled bias every `θ` in the box misses by more than `ε_m`, the hypothesis is false. D should report that test for the sandwich form as well.

Conclusion: under the first formulation the physical-coverage theorem would have applied to no fabricated transistor.
Under the current one, `ε_I` should be read as a budget for environmental disturbance and for the off-state residual. Model-form error in the on-state belongs to the box.

### 5.3 What the proofs actually use

The proofs of `safe`, `rise` and `fall` use the device law only through four one-sided facts [L]:

| Fact | Lean lemma | Region |
| --- | --- | --- |
| `I_net ≥ I_up` | `Design.Inet_ge_Iup` | `u ≤ V_IL`, `v ≤ V_OH` |
| `I_net ≤ −I_dn` | `Design.Inet_le_neg_Idn` | `u ≥ V_IH`, `v ≥ V_OL` |
| `I_net > ε_I` | `Design.Inet_Vlo_gt` | `v = V_lo`, every `u` |
| `I_net < −ε_I` | `Design.Inet_Vhi_lt` | `v = V_hi`, every `u` |

Any current law with these four properties gives the same theorems.
The physical question is therefore four inequalities about the real current, not closeness to a square law everywhere.

### 5.4 What the per-instant form settles, and what it leaves open

**Settled.** The four facts of §5.3 hold for every `θ` in the box, so they apply at every instant whichever point is chosen.
The guarantee theorems keep the same `Admissible` conditions and the same deadlines [L].

B checked this independently before the commit. At 15:58 B type-checked, against the fixed-`θ` definition, an equivalent inclusion in which `c·v'` lies between `I_net(θ_lo) − ε_I` and `I_net(θ_hi) + ε_I`, with invariance, rise and fall under the unchanged `Admissible`. At 16:22 B type-checked that a current bracketed by two box members is matched by one member up to `ε_m`. Those scratch files are not reproduced, because the repository now has the same content as `IsTrajectory`, `Design.exists_inBox_of_between` and `IsTrajectory.of_sandwich`.

**What the sandwich form buys.**

- The physical obligation is "the real current surface lies inside the tube spanned by the box, up to `ε_m`". A box on `k` is a multiplicative band and a box on `V_t` is a horizontal shift band. That is the natural shape for fitting a short-channel device, and it is what an envelope fit produces (§9.5).
- Parameters need not be constant in time. Random telegraph noise, ageing and slow supply drift within the box are covered.

**What it leaves open.**

- The box now does two jobs: process and supply spread, and model-form error. The tube for a real device is wider than a process-corner box. Margins must be recomputed for it. Whether an admissible record exists for SKY130 is open (§6.4, §10.3).
- It does nothing for thresholds that are too high (§6.4), for coupling currents (§7), or for noise.
- A supply that moves also injects current through the junction capacitance, `C_jp·VDD'`. That term belongs to the disturbance budget (§7.2), not to the box.
- With the supply chosen per instant, a safe domain measured from the actual supply cannot be stated for a general trajectory. It can be stated for runs at one supply value (§6.3).
- Existence and uniqueness are proved for constant parameters only [L]. For moving parameters the guarantee speaks about whatever trajectories there are.

## 6. Safe domain

### 6.1 What is proved, and the true margins

Lean proves invariance of `[V_lo, V_hi] = [−0.10, 2.08] V` for the illustrative record [L].
Each boundary is handled by splitting the input range at `uLo = 0.74` or `uHi = 0.77` and bounding one device per branch.

| Boundary | Proved split bounds [L] | True minimum over `u` and the box [D] | Attained at |
| --- | --- | --- | --- |
| `v = V_lo = −0.10` | `RloP = 3.136`, `RloN = 3.04` µA | 5.92 µA | `u = 0.82`, `VDD = 1.62` |
| `v = V_hi = 2.08` | `RhiP = 2.4`, `RhiN = 2.312` µA | 6.44 µA | `u = 0.65`, `VDD = 1.98` |
| `v = VDD + 0.10` (supply-relative) | same record gives 2.4 and 2.312 µA [L-scratch] | 3.56 µA | `u = 0.65`, `VDD = 1.62` |

The smallest proved margin is 2.312 µA. So boundary invariance, not switching, limits `ε_I` in this record: the switching margins would tolerate 10 µA, the boundaries tolerate 2.3 µA.

**Closed form for the valley** [D]. Let `H = VDD − V_tn − V_tp` be the headroom, `δ` the excursion beyond the rail, `k_a` the parameter of the device that conducts in reverse and `k_b` that of the other device. The minimum over `u` of the restoring current is

```text
M(H, δ; k_a, k_b) = 0                                         if H + δ ≤ 0
                  = k_a·k_b / (2(k_a + k_b)) · (H + δ)²       if 0 < H + δ and H ≤ k_a·δ / k_b
                  = k_a·δ·H + k_a·δ²/2 − (k_a·δ)² / (2·k_b)   if H ≥ k_a·δ / k_b
```

At the bottom `k_a = k_n`, `k_b = k_p`. At the top they swap.
The worst corner is the smallest `k`, the largest thresholds and, for the supply-relative top, the smallest `VDD`.
Appendix A checks the formula against brute force: item 3 in three cases of the illustrative box, all in the third branch, and item 7a (added 2026-11-09) for the 32 values of item 6 and for 600 random values that cover all three branches.

Two consequences:

- The draft's condition `VDD_min > V_tn,max + V_tp,max` is neither necessary nor sufficient. Positivity needs `VDD + δ > V_tn + V_tp`. Exceeding `ε_I` needs `M > ε_I`.
- To first order the margin is `k_a · δ · H`. Here `k_n·δ = 16 µA/V` at the bottom and `k_p·δ = 8 µA/V` at the top. An error of 0.1 V in the sum of thresholds moves the margins by 1.6 and 0.8 µA. The proved slack over `ε_I` is 1.0 µA at the bottom and 0.3 µA at the top.

### 6.2 Is reverse conduction the right physics for small excursions?

In form, yes. A MOSFET channel is symmetric. Which terminal is the source is decided by the potentials.
Level 1 and BSIM4 4.5 both implement the exchange explicitly [S, NGSRC `mos1load.c`, `b4v5ld.c`].

Beyond a rail, other mechanisms act in addition.

| Mechanism | Direction | Onset | In the model? |
| --- | --- | --- | --- |
| Forward body bias of the acting source | More restoring current: the threshold drops. | Immediately | No. Omitting it is safe. |
| Bulk-charge factor in reverse | More restoring current than a `γ = 0` law matched in forward saturation [D, formulas M]. | Immediately | No. Omitting it is safe. |
| Drain-bulk junction forward conduction | Restoring. | Depends on the junction parameters (§3.4). Level 1 default diode: negligible to about 0.3 V at 27 °C, microamps near 0.5 V and above 100 µA at 0.6 V; microamps from 0.3 V at 100 °C. Ideal-diode law with the SKY130 cards' junction parameters: at most 0.1 µA up to 0.6 V at 27 °C, and 0.09 to 0.16 µA at 0.46 V at 100 °C [D from S, Appendix A item 8]. Not simulated. | No |
| Minority-carrier injection and latch-up | Catastrophic. A parasitic thyristor can short the rails. | Needs injected currents of the order of the standard test level, about 100 mA at a pin [M; JESD78 not read]. A femtofarad node holds femtocoulombs. | No. Excluded by assumption. |
| Oxide over-voltage | Reliability, not function. | Gate-to-channel voltage up to 2.18 V in the fixed domain, against a 1.95 V model limit [S, SKY-DD]. | No |
| Gate-induced drain leakage | Small current to bulk. | High gate-drain voltage | No |

### 6.3 Over what excursion is the symmetric law credible?

- **Documented model validity** [S, SKY-DD]. `nfet_01v8`: drain-source and gate-source 0 to 1.95 V, bulk-source +0.3 to −1.95 V. `pfet_01v8` and `pfet_01v8_hvt`: 0 to −1.95 V, bulk-source −0.1 to +1.95 V. Read as forward body bias limits, these allow 0.3 V below ground and 0.1 V above the supply. Mapping reverse operation onto these ranges is B's interpretation, not a statement of the PDK.
- **Interface standard** [S, JEITA]. The 1.8 V standard specifies inputs from −0.3 V to `VDD + 0.3 V` in normal operation and −0.5 V to `VDD + 0.5 V` as absolute maximum. The JEITA text says its specifications correspond to JEDEC JESD8-7.
- **Recommendation.** `δ = 0.1 V` measured from the actual rails is defensible on both sides. `δ` up to 0.3 V is defensible on the ground side only.

**The fixed top is the problem.** `V_hi = VDD_max + δ = 2.08 V` does not depend on `θ`.
For `VDD = 1.62 V` the safe domain admits `v` up to 0.46 V above the supply.
That is beyond the PMOS model's documented range. Whether junction conduction matters there depends on junction parameters that this document does not fix: at 100 °C and 0.46 V of forward bias a diode with the Level 1 defaults would carry about 145 µA, comparable to the channel currents, while the ideal-diode law with the SKY130 PMOS card's junction parameters and an assumed 0.3 µm drain gives about 0.16 µA [D from S, Appendix A item 8]. Neither figure is a simulation, so junction conduction at this point is an open question, not an estimate.
`IsTrajectory.of_sandwich` also demands its bracketing on that whole region, which makes the physical hypothesis harder than it needs to be.

**A supply-relative bound is already implied** [L-scratch, Appendix B].
For an admissible record `D` and a supply value `V0` in its range, let `D.atSupply V0` be `D` with the supply range collapsed to `V0` and the top of the safe domain set to `V0 + (V_hi − VDD_max)`.
In the scratch file of Appendix B the lemma has one extra hypothesis: if `ε_I < RhiN'`, then `D.atSupply V0` is admissible (`Design.Admissible.atSupply`).
`RhiN'` is `RhiN` with `V_hi` replaced by `VDD_min + (V_hi − VDD_max)`. For the illustrative record `RhiN' = RhiN = 2.312` (`illustrative_RhiN'` in the same scratch file).
Note added 2026-11-09: the extra hypothesis is not needed, and `RhiN'` and `illustrative_RhiN'` exist only in the scratch file of Appendix B, not in the library. In the library at commit `8c2637b` (`VoltageToBit/Proofs/AtSupply.lean`), `Design.Admissible.atSupply` says that `D.atSupply V0` is admissible for every admissible `D` and every `V0` in its supply range, with no further condition. `Design.Admissible` has two more fields there, `Vtn_nonneg : 0 ≤ D.Vtnlo` and `Vtp_nonneg : 0 ≤ D.Vtplo`. With them the restricted record has the same `RhiN` as `D` (`Design.Admissible.RhiN_atSupply`), so the condition holds automatically. The trajectory-level statements `trajectory_safe_atSupply` and `solution_safe_atSupply` need no extra condition either.

Every theorem about admissible records then applies to a run at constant supply `V0`, with the safe domain `[V_lo, V0 + δ]`:

- the output stays within `δ` of its own supply;
- the model-error obligation is needed only on that smaller domain;
- the deadlines of the restricted record are no larger [D];
- no number in the record changes.

The result uses only the `Design` and `Admissible` definitions, so it does not depend on how trajectories are defined.
B also checked the trajectory-level statement directly against the earlier fixed-`θ` definition.

### 6.4 Where a real device supplies less restoring current than the model

This is the direction that would make the invariance proof inapplicable.

1. **Thresholds above the box, in the mid-rail valley.** The minimum restoring current occurs with the input near mid-rail, where both devices are barely on. If the real thresholds sum to more than the box allows, the real current there falls to subthreshold levels. The model has a margin only because of its headroom.

   With thresholds like those in the SKY130 device table and `k` values fitted to the documented saturation currents (see below the table), the square-law valley is [D, Appendix A item 6]:

   | Thresholds `V_tn`, `V_tp` (V) | `VDD` | `H` | Valley, `δ = 0.1` | Valley, `δ = 0.3` |
   | --- | --- | --- | --- | --- |
   | 0.645, 0.888 (TT, W = 7 µm) | 1.60 | +0.067 | 2.82 µA | 13.6 µA |
   | 0.738, 0.819 (TT, W = 0.42 µm) | 1.60 | +0.043 | 2.07 µA | 11.9 µA |
   | 0.677, 0.940 (SS, W = 7 µm) | 1.60 | −0.017 | 0.61 µA | 7.15 µA |
   | 0.818, 0.918 (SS, W = 0.42 µm) | 1.60 | −0.136 | 0.00 µA | 2.40 µA |
   | 0.645, 0.888 (TT, W = 7 µm) | 1.80 | +0.267 | 12.6 / 9.3 µA | 32.5 / 31.8 µA |
   | 0.818, 0.918 (SS, W = 0.42 µm) | 1.80 | +0.064 | 2.40 / 2.39 µA | 11.8 µA |

   Where two values are given they are bottom and top.
   Thresholds are the model-corner columns for `L = 0.15 µm` [S, SKY-DD]. The cell's widths, 0.65 and 1.0 µm, lie between the tabulated ones.
   The page does not state how the thresholds are extracted or at what bias the currents are measured. The `k` values (539 and 324 µA/V² typical, 519 and 272 slow) assume 1.8 V on gate and drain and linear scaling with width: `k = 2·I_D·(W_cell / 7 µm) / (1.8 V − V_t)²`, with the tabulated drain currents at W/L = 7/0.15 (3.512 and 1.003 mA typical, 3.078 and 0.721 mA slow [S, SKY-DD]).
   The threshold paired with each current was not recorded. The four values are reproduced by `V_t` = 0.7000, 0.8595, 0.7505 and 0.9297 V, which are not the thresholds of the table rows. With each row's own thresholds the same formula gives 489/345, 578/298, 453/279 and 593/265 µA/V², and the entries of the table move by less than 5 %: at 1.60 V and `δ = 0.1 V` they become 2.82, 2.01, 0.59 and 0.00 µA [D, Appendix A item 7b]. The reading below is the same with either set.

   Reading: at 1.60 V and the slow corner the square-law lower envelope has a dead zone. With `δ = 0.1 V` its restoring current is between 0 and 0.6 µA, below `ε_I = 2 µA`. At the typical corner it is 2 to 3 µA, which is marginal.

2. **`k` taken from a low-field fit.** If `k` comes from the linear region, the model overstates saturation current by the bulk-charge factor and by velocity saturation, roughly a factor of two for these devices (§5.2). The pull-up and pull-down margins would then be optimistic.

3. **Cold.** Thresholds rise at low temperature [M]. A box fitted at 27 °C understates them at −40 °C, which shrinks `H`.

4. **Hot.** Mobility falls at high temperature [M]. A box fitted at 27 °C overstates `k`.

5. **Ageing.** Negative-bias temperature instability raises the PMOS threshold magnitude over life [M].

6. **Supply impedance.** In the valley part of the restoring current comes through the PMOS from the supply. The model assumes an ideal rail.

B found no mechanism that reduces reverse channel conduction below the square law when thresholds and `k` are matched in forward saturation. The effects listed in §6.2 all add current. That is a physical argument, not evidence.

### 6.5 What must be recorded as assumptions

See `docs/assumptions.md`: `PHY-03` (headroom for the real device), `PHY-06` (reverse conduction at least the lower envelope), `ENV-10` (temperature), `ENV-12` (excursion limits and, in the register at commit `2bf6f81`, the no-latch-up assumption), `PHY-09` (validity range of the comparison model).

## 7. Disturbance envelope

### 7.1 The mathematical object

`ε_I` is a number in the design record. The inclusion allows any deviation of `c·v'` from `I_net` up to `ε_I`, at every instant, with no structure.
That is all the mathematics says. Sections 7.2 to 7.5 are about which physical effects fit inside it.

### 7.2 Classification of physical effects

**(a) Exactly an additive bounded current, under a stated environment restriction.**

| Effect | Current into the node | Effect on `c` | Restriction needed | Order of magnitude |
| --- | --- | --- | --- | --- |
| Gate-drain feedthrough | `C_M · u'` | `+C_M` | Input slew at most `S_u` | `C_M` 0.2 to 1 fF for the SKY130 `inv_1` [D from S]. Slews 0.7 to 108 V/ns are characterised; 5 to 50 V/ns is typical for gate-driven edges at 5 to 25 fF [D from S, SKY-HD]. So 1 to 50 µA. |
| Capacitive coupling to an aggressor | `C_c · a'` | `+C_c` | Aggressor slew at most `S_a`, and a bound on `C_c` | Interlayer area and fringe capacitances are 7 to 134 aF/µm² and 6 to 83 aF/µm [S, SKY-RCX]. Same-layer sidewall coupling is not on that page; B assumes the same order [M]. A 10 µm parallel run is then about 0.5 fF, giving 2.5 to 25 µA. |
| Supply motion through the PMOS junction | `C_jp · VDD'` | none extra | Supply slew bound | 0.5 fF × 0.1 V/ns = 0.05 µA [D] |
| Static leakage: off-device channel, junctions, gate | bounded function of `(u, v)` | none | none | 0.1 to 5.8 pA at tt, 25 °C, 1.8 V; 0.36 to 7.5 nA at ff, 100 °C, 1.95 V [D from cell leakage power, S, SKY-HD]. Below 0.01 µA. |
| Near-threshold conduction of the opposing device | bounded function of `(u, v)` | none | none | 0.1 to 0.3 µA when the valid input level is within 0.05 V of the threshold (§3.4) [D] |
| Constant load current | bounded | none | bound on the load | by design |

"Exactly" assumes linear, time-invariant coupling capacitors. For bias-dependent channel capacitance read `C_M` as a bound on `|∂Q/∂u|`.

**(b) Only approximately representable, or not representable.**

| Effect | Why | Size |
| --- | --- | --- |
| Model-form error against BSIM4 or silicon | Roughly proportional to the current, not bounded by a small constant (§5.2). It belongs to the box (§5.4), not to `ε_I`. | Tens of microamps |
| Time-varying supply | The PMOS source moves. A supply moving inside the box is covered since commit `eae25ed`. Its displacement current `C_jp·VDD'` is a separate disturbance term (table above). | Design-dependent |
| Ground bounce | The NMOS source is at `V_ss(t)`. This is `I_n(u − V_ss, v − V_ss)`, not a threshold shift: in the linear region the second term changes too. It also adds `C · V_ss'`. | About `k·V_ov·V_ss`: 5 to 30 µA for 50 mV [D] |
| Thermal and flicker noise | Unbounded. White noise has no pointwise bound at all. | §7.5 |
| Crosstalk as an event | Physically it is bounded in charge, `C_c · ΔV`, with large amplitude and short duration. An amplitude bound is the wrong shape: too strict for the spike and too generous for a sustained current. | 0.5 fF × 1.8 V = 0.9 fC per aggressor edge |

**(c) Effects that add state and are out of scope.**
Interconnect resistance, inductance and distributed capacitance. Internal device charge dynamics. Well and substrate potential dynamics. Gate resistance. The driver of `u` reacting to charge kicked back through `C_M`.
The last is harmless for the theorem, which constrains the actual waveform `u` and assumes nothing about its driver.

### 7.3 Budget

A physical reading of the record needs

```text
ε_I ≥ C_M,max·S_u + Σ_i C_c,i·S_a,i + C_jp,max·S_VDD + I_leak,max + ε_off + ε_m
```

`ε_off` is the opposing device's conduction that the hard threshold calls zero. `ε_m` is the residual outside the tube.

**Budget A: an environment consistent with `ε_I = 2 µA`.** Every number is illustrative.

| Source | Assumption | Share |
| --- | --- | --- |
| Gate-drain feedthrough | `C_M ≤ 0.5 fF`, `S_u ≤ 2 V/ns` | 1.0 µA |
| Aggressor coupling | total `C_c ≤ 0.1 fF` at `S_a ≤ 5 V/ns`, or no switching neighbour | 0.5 µA |
| Supply motion | `C_jp ≤ 1 fF`, `S_VDD ≤ 0.1 V/ns` | 0.1 µA |
| Static leakage | hot, fast corner | 0.01 µA |
| Near-threshold conduction | `V_IL` 0.05 V below `V_tn,min`, up to 125 °C | 0.3 µA |
| Reserve | | 0.09 µA |
| Total | | 2.0 µA |

An input slew of 2 V/ns means a full swing takes about 0.9 ns.

**Budget B: library-realistic edges.** `S_u = 20 V/ns` with `C_M = 0.5 fF` gives 10 µA. A 0.5 fF aggressor at the same slew adds 10 µA.
The total exceeds both the boundary margins (2.3 µA) and `I_up` (10.5 µA). The record is then not admissible.

### 7.4 The explicit run and the two-stage corollary

**Explicit run.** `Examples.uRamp` falls from 1.8 V to 0 in 0.2 ns, which is 9 V/ns, and `Examples.wSin` already uses the full 2 µA [L].
As mathematics the run is a valid witness.
As a physical story it is consistent only for a node with no gate-drain capacitance: at `C_M = 0.22 fF` the ramp alone injects 2 µA.
Note added 2026-11-09: this run is `Examples.illustrative_scenario`, and the paragraph stays true of it. The library at commit `8c2637b` has a second explicit run, `Examples.illustrative_feedthrough_scenario`: nominal parameters, 9.4 fF to ground, 0.5 fF to the input and 0.1 fF to one aggressor, an input and an aggressor whose slews are at most 2 V/ns and 5 V/ns, and a residual current of at most 0.5 µA. Its budget is 0.5·2 + 0.1·5 + 0.5 = 2.0 µA, exactly the allowance, with the coefficients of Budget A (§7.3). Its input stays valid-low for the whole run, so only the rising direction of the output occurs. It is a mathematical witness inside an assumed budget; no coefficient comes from a device.

**Two stages.** `Proofs/Chain.lean` composes two stages [L].
Its header already says that the second stage's gate capacitance and its feedback onto the first node are covered only if the first stage's bounds contain them.
The same holds in the forward direction, and there the model itself fixes the number.

- The first stage's output is the second stage's input.
- `rise_at_most` and `fall_at_most` bound its slew by `(IchargeMax + ε_I)/C_min` and `(IdischargeMax + ε_I)/C_min` [L].
- For the illustrative record with valid inputs these bounds are 28.6 V/ns rising and 58.3 V/ns falling [D]. The fast corner at `C_min` comes within a few percent of them.
- A second stage with gate-drain capacitance `C_M` then sees a feedthrough current of up to `28.6·C_M` to `58.3·C_M` µA.
- That stays inside 2 µA only for `C_M` below 0.03 to 0.07 fF. The estimate for a small inverter is 0.2 to 1 fF.

Note added 2026-11-09: the two numbers are the bounds for inputs restricted to `[0, 0.40]` V (rising) and to `[1.25, 1.98]` V (falling). For these ranges they are Lean theorems in the library at commit `8c2637b`: 28.5508 and 58.3144 V/ns (`Examples.illustrative_max_rise_slew`, `Examples.illustrative_max_fall_slew`). For the valid-input classes of the guarantee, `u ≤ V_IL` and `u ≥ V_IH` with no further range, the output slew has no bound (`Examples.valid_low_rise_slew_unbounded`, `Examples.valid_high_fall_slew_unbounded`). That does not weaken the conclusion below.

Note added 2026-11-10: each of the two numbers is for one direction and one input range. For the other direction the same lemmas give about 32.3 V/ns falling for inputs in `[0, 0.40]` V and about 65.1 V/ns rising for inputs in `[1.25, 1.98]` V (arithmetic on the record, not stated as theorems). A bound on the size of the first-stage slew for inputs in either range is therefore about 65 V/ns, so the feedthrough into a second stage can reach about `65·C_M` µA, which stays inside 2 µA only for `C_M` below about 0.03 fF. The header of `Proofs/Chain.lean` says so since commit `fb8bc31`. The conclusion below is unchanged.

So under Budget A the two-stage corollary has no physical reading. It is a statement about two ideal one-node stages.

### 7.5 Noise

- The mean-square voltage of thermal noise on a capacitor is `kT/C` [M, N28; S-bib, SDM93]. `sqrt(kT/C)` is 0.91 mV at 5 fF and 0.46 mV at 20 fF, at 300 K [D].
- The noise margins of the record are 100 and 150 mV, more than 100 standard deviations. A noise-induced decoding error is physically negligible.
- That is a probabilistic argument outside the theorem. The theorem is conditional on the disturbance bound, and no finite bound covers a Gaussian tail.
- Thermal noise is better described as a small perturbation of the state than as a current.

A less conservative treatment of feedthrough and crosstalk would use the charge variable `C_tot·v − C_M·u − Σ C_c·a`, whose derivative contains no slew terms. It replaces the slew restrictions by bounded voltage offsets. It changes the theorem's shape and is not proposed for the first instance.

## 8. Digital semantics

### 8.1 Static discipline and noise margins

The record satisfies `V_OL ≤ V_IL < V_IH ≤ V_OH` with `0.25 ≤ 0.40 < 1.25 ≤ 1.35` [L, `illustrative_admissible`].
The noise margins are `NM_L = V_IL − V_OL = 0.15 V` and `NM_H = V_OH − V_IH = 0.10 V`.

These margins are an allowance for a voltage difference between a driver's output and the next gate's input, for example a ground offset between them.
They are a different quantity from `ε_I`, which is a current at the node.
Classical treatments of worst-case static noise margin are Hill 1968 [partially confirmed, H68] and Lohstroh, Seevinck and de Groot 1983 [S-bib, LSG83].

Decoding is three-valued and never maps an intermediate voltage to a bit [L, `decode_eq_none_iff`].

### 8.2 Absolute thresholds when `VDD` varies by ±10 %

Absolute thresholds are the conservative, compositional choice: a valid output is a valid input whatever the receiver's local supply.
Ratiometric thresholds need the two supplies to track. The 1.8 V interface standard notes this for its hysteresis inputs and asks for tracking within 0.1 V [S, JEITA notes 10 and 12].

Traps:

1. **Feasibility at low supply.** `V_OH = 1.35 V` must be reachable at `VDD = 1.62 V`. The gap is 0.27 V, and it is the PMOS drain-source voltage at the worst point of `I_up`. Lean requires only `V_OH ≤ VDD_min` and `ε_I < I_up` [L].
2. **The opposing device is not off at high supply.** At `VDD = 1.98 V` and `u = V_IH = 1.25 V` the PMOS has 0.73 V of gate drive against a threshold as low as 0.45 V. The model includes its 4.7 µA in `I_dn` [L]. A real PMOS adds near-threshold current on top.
3. **`V_IL` close to a threshold.** `V_IL = 0.40 V` is 0.05 V below `V_tn,min`. The model treats the NMOS as exactly off. The real one is in moderate inversion (§7.2).
4. **The switching point moves with the supply.** Over the box the inverter's switching voltage ranges over 0.66 to 1.03 V [D]. It stays inside the forbidden zone (0.40, 1.25), as it must.
5. **Comparison with the interface standard.** The normal-range standard uses `V_IL = 0.35·VDD`, `V_IH = 0.65·VDD`, `V_OH = VDD − 0.45 V` at 2 mA and `V_OL = 0.45 V` at 2 mA, for 1.65 to 1.95 V [S, JEITA Table 4]. The record's `V_IL` is stricter. Its `V_IH = 1.25 V` is below `0.65·VDD` once `VDD > 1.92 V`, so the inverter must accept weaker high inputs than the standard requires. That is a stronger claim about the inverter. It is not an error.
6. **No hold-time claim.** The guarantee says nothing about how long the old output persists after the input leaves validity, except through `rise_at_most` and `fall_at_most`.

## 9. Comparison device model for workstream D

### 9.1 Candidates

| Candidate | Model | License | Assessment |
| --- | --- | --- | --- |
| SkyWater SKY130 `nfet_01v8`, `pfet_01v8`, `pfet_01v8_hvt` | BSIM4, level 54, version 4.5 [S, SKY-PR] | Apache-2.0 [S] | **Recommended.** A real process with documented corners, documented validity ranges, a standard-cell inverter and Liberty data for cross-checks. ngspice documents its use [S, NGAPP]. |
| Predictive Technology Model, 130 or 180 nm bulk | BSIM4 [M] | None stated on the host page [S, PTM] | One self-contained card per device, so it is simple. Predictive, not tied to a foundry. Unclear terms. Possible second opinion. |
| GlobalFoundries GF180MCU | BSIM4, level 54 [search] | Apache-2.0 [search] | 3.3 V devices with longer channels. Closer to a square law, but the wrong supply for this record. |
| FreePDK45 | PTM-based 45 nm [search] | Apache-2.0 with a click-through [search] | About 1 V: the host page reports model currents simulated at a 1.0 V supply [S, FPDK45, read on 2026-11-09 for the corrections]. Strongly velocity-saturated [M]. A poor match for a Level 1 comparison. |
| IHP SG13G2 | PSP 103.6 through OpenVAF [S, NGAPP] | Apache-2.0 [M] | Needs a Verilog-A compile step. Not for the first comparison. |

### 9.2 Provenance to pin

| Item | Value |
| --- | --- |
| Maintained source | `https://github.com/fossi-foundation/skywater-pdk-libs-sky130_fd_pr`, Apache-2.0 [S] |
| Commit to pin | `403964dc7f9cca5ec1a8cc7b4f2a6f532b781676` (2026-01-12). This is the reference recorded by open_pdks 1.0.617 [S, OPDK]. |
| Head when read | `29b55153fd9f4badef05a02667184b81789d1f61` (2026-11-03). The most recent change (pull request 8: one commit of 2026-10-26 and its merge of 2026-11-03) reworks Monte Carlo parameters, including `models/parameters/critical.spice` in the original model tree, so the files are still moving [S]. |
| Original release | `https://github.com/google/skywater-pdk-libs-sky130_fd_pr` at `f62031a1be9aefe902d6d54cddd6f59b57627436` (2020-11-10), archived read-only on 2025-05-13 [S]. The values quoted in this document were read here. |
| Standard cell | `https://github.com/google/skywater-pdk-libs-sky130_fd_sc_hd` at `ac7fb61f06e6470b94e8afdf7c25268f62fbd7b1`, archived 2024-04-25 [S] |
| Documentation | `https://github.com/google/skywater-pdk` at `7198cf647113f56041e02abf3eb623692820c5e1` [S] |
| Installer | open_pdks (now the repository `fossi-foundation/open-pdks`, see OPDK in §12) `c6df28c1fccb05c286aa0a15e9c4c7dcd8502607`, version 1.0.617, Apache-2.0 [S] |
| Simulator | ngspice. The release manual listed on 2026-11-09 is version 47 [S]. It implements BSIM4 4.5.0 under level 54 [S, NGM §7.6.3.4]. D must record the version it installs. |

D should record the SHA-256 of every model file actually loaded. A commit hash of a repository is not a hash of the bytes the simulator read.

### 9.3 Files and settings

- Entry point: `models/sky130.lib.spice`, sections `tt`, `ss`, `ff`, `sf`, `fs` and further corners [S, SKY-PR-F]. The `tt` section includes four files: `corners/tt.spice`, two resistor-capacitor files (`r+c/res_typical__cap_typical.spice`, `r+c/res_typical__cap_typical__lin.spice`) and `corners/tt/specialized_cells.spice`. `corners/tt.spice` has 30 include statements of its own at the pinned commit, so these four are not the full list of files loaded.
- The repository also has `combined_models/sky130.lib.spice` with "continuous" models. Its README says the original models are binned at the characterised sizes and can be inaccurate between them, and that the continuous models were refitted to vary smoothly [S, SKY-PR-F]. D should state which set it uses and should prefer characterised sizes when using the original set.
- Devices: `sky130_fd_pr__nfet_01v8` and `sky130_fd_pr__pfet_01v8_hvt`, with `w = 0.65 µm`, `l = 0.15 µm` and `w = 1.0 µm`, `l = 0.15 µm` to match `sky130_fd_sc_hd__inv_1` [S, SKY-HD]. The standard-threshold `sky130_fd_pr__pfet_01v8` is a useful second case because it has more headroom.
- The cell netlist gives no drain area or perimeter [S, SKY-HD]. Junction capacitance and junction current then depend on model defaults. D should either supply them or state that they are absent.
- ngspice settings recommended by the ngspice project for this PDK: `set ngbehavior=hsa`, `set skywaterpdk`, optionally `set ng_nomodcheck` [S, NGAPP].
- Model reference temperature is 30 °C [S, SKY-PR].

Nothing in this subsection has been executed.

### 9.4 Comparison tiers

| Tier | Compared against the formal model | Purpose |
| --- | --- | --- |
| T0 | D's own integrator and the closed forms of §6.1 and `docs/interface.md` §6 | Catches implementation errors in the harness. |
| T1 | ngspice Level 1 with `LAMBDA = 0`, `GAMMA = 0`, no capacitance parameters, `IS` negligible, external capacitor only | Must agree to solver tolerance, including `v < 0` and `v > VDD`. Confirms §3.2 in the simulator. |
| T2 | Level 1 with one omitted effect switched back on at a time: `LAMBDA`, `CGDO` and `CGSO`, `CJ`, default `IS` | Attributes the residual to named mechanisms. |
| T3 | BSIM4 SKY130, corners tt, ss, ff, sf, fs; supply at minimum, nominal, maximum; −40, 27, 100 °C | The model-form comparison. |

A proposed T1 deck fragment, not executed:

```spice
.model nsh nmos level=1 vto=0.5  kp=200u lambda=0 gamma=0 is=1e-30
.model psh pmos level=1 vto=-0.5 kp=100u lambda=0 gamma=0 is=1e-30
M1 out in 0   0   nsh w=1u l=1u
M2 out in vdd vdd psh w=1u l=1u
CL out 0 10f
```

With `W = L` and no lateral diffusion, `KP` equals `k` in A/V². With the default `IS = 1e-14 A` the junction would carry about 0.5 µA at 0.46 V of forward bias [D], which would spoil the identity check near the fixed upper bound.

### 9.5 Extracting a square-law fit

There is no single fit. D should report all of the following and say which is used for what.

1. **Saturation extrapolation.** Sweep the gate with the drain at the supply. Fit a line to `sqrt(I_D)` against gate voltage over a declared window. The slope gives `sqrt(k/2)` and the intercept gives `V_t`. The result depends on the window because the real curve is not a parabola.
2. **Linear extrapolation.** At 50 mV drain-source voltage take the tangent at maximum transconductance. `V_t` is the intercept minus half the drain-source voltage, and `k` is the peak transconductance divided by the drain-source voltage. A survey of extraction methods is Ortiz-Conde et al. 2002 [S-bib, OC02].
3. **Envelope fits.** Find `(k_lo, V_t,hi)` whose square law lies below the BSIM4 current on the region where the device is the on-device, and `(k_hi, V_t,lo)` whose square law plus `ε_m` lies above it on the whole safe domain. These define the tube of §5.4. Checked on a grid, they are the hypothesis of `IsTrajectory.of_sandwich`.
4. **The four margins directly.** Evaluate on BSIM4 the minimum net pull-up current for `u ≤ V_IL`, `v ≤ V_OH`; the minimum net pull-down current for `u ≥ V_IH`, `v ≥ V_OL`; and the minimum restoring current over `u` at `v = −δ` and at `v = VDD + δ`. Compare with `I_up`, `I_dn` and the boundary margins.
5. **Capacitance.** Extract `∂Q/∂v` at the output over the safe domain and over `u`, and `∂Q/∂u`, and compare with `[C_min, C_max]` and the `C_M` of the budget.

Items 3 to 5 are finite-sample checks. A grid can refute a bound. It cannot establish one between grid points.
A bound claimed from a grid needs a separate argument, for example monotonicity plus a Lipschitz constant, and BSIM4 comes with no certified constants.

### 9.6 Expected shape of the residual

Stated before any run, so that D's results can contradict it.

- **Near and below threshold:** the real device conducts and the model does not. Small in absolute terms, 100 % in relative terms.
- **The knee:** real devices saturate at a drain-source voltage well below the overdrive. A square law matched to the saturation current is still in its linear region there and reads low, by perhaps a third at mid-knee [D, from the square law's own shape].
- **Saturation against gate voltage:** the real current is closer to linear in overdrive. A fit over the full range overshoots at the ends and undershoots in the middle, or the reverse.
- **Deep linear region at high gate drive:** a saturation-fitted `k` understates the conductance by roughly a factor of two for these devices (§5.2).
- **Saturation against drain voltage:** the real current rises slowly; the model is flat.
- **Reverse region, small excursion:** expected to be at or above the square law (§6.2).
- **Corners:** the slow corner at low supply is where the restoring-current valley is expected to collapse (§6.4).

## 10. The first instance

### 10.1 Verification of the draft numbers

| Quantity | Draft | Recomputed [D] | Lean [L] |
| --- | --- | --- | --- |
| `I_up` | ≈ 10.5 µA | 10.476 µA at `VDD = 1.62`, `k_p = 80`, `V_tp = 0.60`, `u = 0.40`, `v = 1.35` | `illustrative_Iup` = 10.476 |
| `I_dn` | ≈ 16.3 µA | 16.296 µA at `VDD = 1.98`, `k_n = 160`, `k_p = 120`, `V_tn = 0.60`, `V_tp = 0.45`, `u = 1.25`, `v = 0.25` | `illustrative_Idn` = 16.296 |
| `τ_up` | ≈ 3.4 ns | 3.4214 ns | 7250/2119 |
| `τ_dn` | ≈ 2.6 ns | 2.5602 ns | 4575/1787 |
| Boundary margins | ≈ 2.3 to 3.1 µA | split bounds 2.312, 2.4, 3.04, 3.136; true minima 5.92 and 6.44 µA | `illustrative_RhiN` and three others |

No discrepancy.

Note added 2026-11-09: `τ_up` and `τ_dn` are the closed-form deadline bounds of the record (`Design.tauUp`, `Design.tauDn`; rounded up to 3.43 and 2.57 ns in `Examples.illustrative_guarantee`). They are not the smallest deadlines known for it. The library at commit `8c2637b` has 2.26 ns (rise) and 1.425 ns (fall) for the same record under the same assumptions (`Examples.illustrative_guarantee_refined`), and shows that no deadline below 2.168 ns (rise) or 1.0234 ns (fall) is valid (`Examples.rise_deadline_counterexample`, `Examples.fall_deadline_counterexample`). `Examples.rise_deadline_bracket` and `Examples.fall_deadline_bracket` state the two ends of each direction in one theorem. For a deadline `τ` with `2.168 ≤ τ < 2.26` ns (rise) or `1.0234 ≤ τ < 1.425` ns (fall) the library has no statement in either direction.

### 10.2 Critique of the illustrative numbers

| Item | Value | Comment |
| --- | --- | --- |
| Supply | 1.62 to 1.98 V | ±10 % of 1.8 V. The SKY130 model documentation is valid to 1.95 V [S]. The standard-cell timing files cover at least 1.28 to 1.95 V [S, SKY-HD]. The interface standard's normal range is 1.65 to 1.95 V [S, JEITA]. |
| Thresholds | 0.45 to 0.60 V, both devices | Model-corner thresholds at `L = 0.15 µm` are 0.60 to 0.85 V (N), 0.68 to 0.96 V (P, high-threshold), 0.55 to 0.86 V (P, standard) [S, SKY-DD]. The box is about 0.15 to 0.35 V below the first two, which are the device types of the `inv_1` cell, and about 0.10 to 0.26 V below the standard PMOS. This is what makes the headroom comfortable. |
| `k_n`, `k_p` | 160 to 240, 80 to 120 µA/V² | Saturation-fit values for the `inv_1` are about 540 and 320 µA/V² [D from S; they depend on the threshold paired with the documented current, §6.4]. The illustrative devices are roughly two to four times weaker. Same order of magnitude. |
| Temperature | not stated | The box has no temperature. ±20 % on `k` does not cover −40 to 125 °C together with process spread [M]. |
| Capacitance | 5 to 20 fF | Plausible (§4.2). |
| `ε_I` | 2 µA | Consistent only with the quiet, slow-edge environment of Budget A (§7.3). Boundary invariance caps it at 2.31 µA in this record. |
| `δ` | 0.1 V | At the documented PMOS limit. Acceptable relative to the actual supply, not relative to `VDD_max` (§6.3). |
| `V_IL`, `V_IH`, `V_OL`, `V_OH` | 0.40, 1.25, 0.25, 1.35 V | Consistent (§8). `V_IL` is 0.05 V below `V_tn,min`. |
| Largest gate-channel voltage | 2.18 V | Input at −0.1 V with output at 2.08 V. Above the 1.95 V model limit. |

### 10.3 Can a better-justified box be given now?

No. A fitted box needs the device model to be run, and that is D's work.
What can be said from documentation alone:

- A box that covers the documented SKY130 corners would have thresholds up to about 0.85 V and 0.96 V. With `VDD_min = 1.60 V` the headroom is negative, the four boundary conditions of `Design.Admissible` cannot all hold for `δ = 0.1 V`, and the record is not admissible (§6.4).
- The pull-up margin survives. With `V_IL = 0.40 V`, `V_OH = 1.35 V`, `VDD = 1.60 V` and the slow-corner numbers of §6.4, the square-law pull-up current is 8 to 11 µA [D]. That is close to the illustrative 10.5 µA by coincidence: the weaker illustrative `k` offsets its lower threshold.
- So the open physical question for a SKY130-anchored instance is the safe domain, not the switching margins.

Options for the coordinator, each a different experiment under the handoff's rules:

| Option | Cost |
| --- | --- |
| Restrict the supply, for example `VDD_min = 1.70 V`, or restrict the corners | A narrower claim |
| Enlarge `δ` to about 0.3 V | Beyond the documented PMOS validity. How much the drain junctions conduct at such an excursion when hot is open: at 0.3 V of forward bias and 100 °C, about 1.0 µA with the Level 1 default diode and 0.002 to 0.003 µA with the SKY130 cards' junction parameters and an assumed 0.3 µm drain [D from S, Appendix A item 8; §6.2, §6.3]. Arithmetic, not a simulation. |
| Reduce `ε_I` | A quieter environment still |
| Use the standard-threshold PMOS | More headroom, but no longer the library cell |
| Add a restoring mechanism to the model, for example a junction law | A new model with a new proof |

### 10.4 Recommendation

Keep `illustrative-1v8` as the mathematical witness with its current label.
State next to it the environment under which its `ε_I` has a physical reading (Budget A).
Do not describe it as representing SKY130.
Create a fitted record only after D reports envelope fits and the four margins.

## 11. Evidence status

| Dimension | Status |
| --- | --- |
| Formal correctness | The guarantee, existence and uniqueness, minimum delays, the two-stage corollary and the negative controls are proved at the commit above [L]. B did not rebuild. B type-checked one record-level lemma against the build products [L-scratch]. |
| Applicability | The illustrative record satisfies every hypothesis, and an explicit run exists [L]. The record's numbers are unsourced. |
| Physical evidence | None. No simulation and no measurement exists in the repository. This document supplies documentation values, estimates and a comparison plan. Its expectations are that a box wide enough to bracket SKY130 devices will be much wider than the illustrative one (§5.2) and that the safe-domain condition fails at the slow corner (§6.4). Both are untested. |

## 12. Sources

Access date for every online source: 2026-11-09.

| Key | Source | Access |
| --- | --- | --- |
| SH68 | H. Shichman, D. A. Hodges, "Modeling and simulation of insulated-gate field-effect transistor switching circuits", IEEE J. Solid-State Circuits SC-3(3), Sept. 1968, from p. 285. DOI 10.1109/JSSC.1968.1049902. | [S-bib]. End page (289) from memory. Text not read. |
| VL80 | A. Vladimirescu, S. Liu, "The Simulation of MOS Integrated Circuits Using SPICE2", Memorandum UCB/ERL M80/7, Feb. 1980, revised Oct. 1980. `https://www2.eecs.berkeley.edu/Pubs/TechRpts/1980/9610.html` | [S] pp. 1–5 and the reference list. |
| N75 | L. W. Nagel, "SPICE2: A Computer Program to Simulate Semiconductor Circuits", ERL Memo ERL-M520, May 1975. | [S-bib], as reference 3 of VL80. Not read. |
| NGM | ngspice User's Manual, HTML edition, "Version 47+", preface dated March 2026. `https://ngspice.sourceforge.io/docs/ngspice-html-manual/manual.xhtml`. §7.6.1, §7.6.2, §7.6.2.1, §7.6.2.5 with the table "MOS level 1, 2, 3 and 6 parameters", §7.6.3.4. | [S], through text extraction. Section numbers may differ in the version 47 release PDF, which was not read. |
| NGSRC | ngspice source, `src/spicelib/devices/mos1/mos1load.c`, `mos1temp.c` and `src/spicelib/devices/bsim4v5/b4v5ld.c`. Mirror `https://github.com/imr/ngspice`, branch `master`. | [S], excerpts. Commit not pinned. For the corrections of 2026-11-09 these files and `mos1set.c`, `bsim4v5/b4v5temp.c`, `bsim4v5/b4v5set.c` were read at commit `a80f6e3e95d51534905b1f23410a951802666656`. |
| NGAPP | ngspice applications page. `https://ngspice.sourceforge.io/applic.html` | [S] |
| SKY-DD | SkyWater SKY130 PDK documentation, "Device Details". `https://skywater-pdk.readthedocs.io/en/main/rules/device-details.html`; sources under `docs/rules/device-details/` in `google/skywater-pdk`. | [S]. Tables checked against the repository files. |
| SKY-RCX | Same documentation, parasitic tables 91 and 93 to 95. `https://skywater-pdk.readthedocs.io/en/main/rules/rcx.html` | [S] |
| SKY-PR | `google/skywater-pdk-libs-sky130_fd_pr` at `f62031a1…`: `cells/nfet_01v8/sky130_fd_pr__nfet_01v8__tt.pm3.spice`, `cells/pfet_01v8_hvt/sky130_fd_pr__pfet_01v8_hvt__tt.pm3.spice`. | [S], the first bin of each file only (L 20 to 100 µm, W 7 to 100 µm). |
| SKY-PR-F | `fossi-foundation/skywater-pdk-libs-sky130_fd_pr`: `models/sky130.lib.spice`, `combined_models/README`. | [S] |
| SKY-HD | `google/skywater-pdk-libs-sky130_fd_sc_hd` at `ac7fb61f…`: `cells/inv/sky130_fd_sc_hd__inv_1.spice`, `…__inv_1__tt_025C_1v80.lib.json`, `…__inv_1__ff_100C_1v95.lib.json`, `timing/sky130_fd_sc_hd__common.lib.json`. | [S] |
| OPDK | open_pdks. `https://github.com/fossi-foundation/open-pdks` (formerly `https://github.com/RTimothyEdwards/open_pdks`, which redirects there): `VERSION`, `sky130/sky130.json`, `sky130/Makefile.in`. | [S] |
| BSIM4 | BSIM4 release list. `http://bsim.berkeley.edu/models/bsim4/`. 4.5.0 released 2005-07-29; 4.8.3 on 2025-05-19. | [S] for the list. Manual not read. |
| JEITA | JEITA ED-5003A, 1.8 V power supply voltage and interface standard for nonterminated digital integrated circuits, revised May 2005. `https://home.jeita.or.jp/tsc/std-pdf/ED5003A.pdf` | [S] Tables 1 to 5, notes 10 to 12, explanatory note. JEDEC JESD8-7A itself was not accessed. |
| EKV95 | C. Enz, F. Krummenacher, E. Vittoz, Analog Integrated Circuits and Signal Processing 8, 83–114, 1995. DOI 10.1007/BF01239381. | [S-bib] and abstract. Equations from memory. |
| SN90 | T. Sakurai, A. R. Newton, IEEE J. Solid-State Circuits 25(2), 584–594, 1990. DOI 10.1109/4.52187. | [S-bib] |
| WD78 | D. E. Ward, R. W. Dutton, IEEE J. Solid-State Circuits SC-13(5), 703–708, 1978. DOI 10.1109/JSSC.1978.1051123. | [S-bib] and abstract |
| M71 | J. E. Meyer, "MOS models and circuit simulation", RCA Review 32, 42–63, 1971. | [S-bib], through reference lists |
| YEC83 | P. Yang, B. D. Epler, P. K. Chatterjee, IEEE J. Solid-State Circuits 18(1), 128–138, 1983. | [S-bib] |
| OC02 | A. Ortiz-Conde et al., Microelectronics Reliability 42(4–5), 583–596, 2002. DOI 10.1016/S0026-2714(02)00027-6. | [S-bib] |
| RMM03 | K. Roy, S. Mukhopadhyay, H. Mahmoodi-Meimand, Proc. IEEE 91(2), 305–327, 2003. DOI 10.1109/JPROC.2002.808156. | [S-bib] |
| LSG83 | J. Lohstroh, E. Seevinck, J. de Groot, IEEE J. Solid-State Circuits 18(6), 803–807, 1983. DOI 10.1109/JSSC.1983.1052035. | [S-bib] |
| H68 | C. F. Hill, Microelectronics 1, p. 16, 1968. | Volume and page seen in one reference list. Title from memory. |
| J94 | K. O. Jeppson, IEEE J. Solid-State Circuits 29(6), 646–654, 1994. DOI 10.1109/4.293109. Input-to-output coupling capacitance in inverter delay. | [S-bib] |
| CKK00 | P. Chen, D. A. Kirkpatrick, K. Keutzer, "Miller factor for gate-level coupling delay calculation", ICCAD 2000, 68–74. | [S-bib]. The −1 to 3 range is from a later paper's summary of prior work. |
| SDM93 | R. Sarpeshkar, T. Delbrück, C. A. Mead, IEEE Circuits and Devices Magazine 9(6), 23–29, 1993. DOI 10.1109/101.261888. | [S-bib] |
| N28 | H. Nyquist, Physical Review 32, 110, 1928. | [M] |
| JESD78 | JEDEC JESD78F.02, "IC Latch-Up Test", 2023. | Listing seen. Text not accessed. |
| PTM | Predictive Technology Model host page. `https://mec.umn.edu/ptm` | [S] |
| GF180 | GlobalFoundries GF180MCU open PDK. `https://github.com/google/gf180mcu-pdk` | [search] |
| FPDK45 | FreePDK45. `https://eda.ncsu.edu/freepdk/freepdk45/` | [search]. For the corrections of 2026-11-09 the page was read for its supply-voltage statement only [S]. |
| MATHLIB | Mathlib at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Mathlib/Analysis/Calculus/MeanValue.lean` | [S], local copy |

## Appendix A. Reproduction script

Requires Python with numpy and scipy. Units are V, µA, fF, ns.
It reproduces these [D] numbers: the identity check of §3.2 (item 1), the margins and deadlines of §1 and §10.1 (item 2), the boundary minima of §6.1 (item 3), the square-law fit residuals of §3.4 and §5.2 (item 4), the subthreshold currents of §3.4 (item 5), the valley table of §6.4 (item 6) and, in the supplement at the end of this appendix, the cross-checks of item 7 and the junction-diode currents of §3.4, §6.2, §6.3 and §9.4 (item 8).
The other [D] numbers are hand calculations of a line or two. Some of them cannot be redone from this document alone, because their inputs are cited but not quoted: for example the drain-junction capacitances of §4.2 (card values `cjs`, `cjsws`, `cjswgs`) and the leakage currents and slew range of §7.2 (cell leakage powers and transition tables). The saturation-fit `k` values of §6.4 rest on thresholds that were not recorded (item 7b).
Items 5 and 6 use different values, 530 and 539 µA/V², for the saturation-fit `k_n` of the same NMOS. Item 7c repeats item 5 with 539: the values change by 1.7 %, and the ranges quoted in §3.4 hold for both.
SHA-256 of the code block below, taken over the text between the fences: `9a9f48f30c6e44b545f42a31767f06d93973b70416a6904bf7ef5167c69957c0`. The block is unchanged by the corrections of 2026-11-09.

```python
# Appendix A of docs/model.md (workstream B). Units: V, uA, fF, ns. numpy + scipy only.
# Reproduces the [D] numbers of the document. Arithmetic on stated inputs; not a proof,
# not evidence about any fabricated device.
import itertools
import numpy as np
from scipy.optimize import minimize

pp = lambda x: np.maximum(x, 0.0)
In = lambda u, v, kn, vtn: 0.5 * kn * (pp(u - vtn) ** 2 - pp(u - v - vtn) ** 2)
Ip = lambda u, v, vdd, kp, vtp: 0.5 * kp * (pp(vdd - u - vtp) ** 2 - pp(v - u - vtp) ** 2)
net = lambda u, v, t: Ip(u, v, t["vdd"], t["kp"], t["vtp"]) - In(u, v, t["kn"], t["vtn"])

BOX = dict(vdd=(1.62, 1.98), kn=(160.0, 240.0), kp=(80.0, 120.0), vtn=(0.45, 0.60), vtp=(0.45, 0.60))
EPS, CMAX, VIL, VIH, VOL, VOH, VLO, VHI, DELTA = 2.0, 20.0, 0.40, 1.25, 0.25, 1.35, -0.10, 2.08, 0.10

def grid(n):  # n points per parameter, corners included
    keys = list(BOX)
    for vals in itertools.product(*[np.linspace(*BOX[k], n) for k in keys]):
        yield dict(zip(keys, vals))

# 1. positive-part form == piecewise Level-1 law with source/drain exchange (lambda = gamma = 0)
def level1(vg, vd, vs, k, vt):          # channel current, positive from terminal d to terminal s
    if vd < vs:
        return -level1(vg, vs, vd, k, vt)
    vov, vds = vg - vs - vt, vd - vs
    return 0.0 if vov <= 0 else (0.5 * k * vov**2 if vds >= vov else k * (vov * vds - 0.5 * vds**2))
rng = np.random.default_rng(12345)
err = 0.0
for _ in range(200_000):
    u, v = rng.uniform(-1, 3, 2); kn, kp = rng.uniform(50, 300, 2)
    vtn, vtp = rng.uniform(0.2, 0.9, 2); vdd = rng.uniform(1.0, 2.5)
    err = max(err, abs(In(u, v, kn, vtn) - level1(u, v, 0.0, kn, vtn)),
              abs(Ip(u, v, vdd, kp, vtp) - level1(-u, -v, -vdd, kp, vtp)))
print(f"1. max |positive-part - piecewise| over 2e5 random points: {err:.2e} uA")

# 2. switching margins over the box (3^5 parameter grid, dense (u, v) grids) and deadlines
U1, V1 = np.meshgrid(np.linspace(VLO - 0.5, VIL, 181), np.linspace(VLO, VOH, 581), indexing="ij")
U2, V2 = np.meshgrid(np.linspace(VIH, VHI + 0.5, 267), np.linspace(VOL, VHI, 733), indexing="ij")
Iup = min(net(U1, V1, t).min() for t in grid(3)); Idn = min((-net(U2, V2, t)).min() for t in grid(3))
print(f"2. I_up={Iup:.3f}  I_dn={Idn:.3f}  tau_up={CMAX*(VOH-VLO)/(Iup-EPS):.4f}  tau_dn={CMAX*(VHI-VOL)/(Idn-EPS):.4f}")

# 3. boundary restoring currents: true minima over u (5^5 parameter grid) and the closed form
u = np.linspace(-1.0, 3.0, 400_001)
bot = min(net(u, VLO, t).min() for t in grid(5))
top_fixed = min((-net(u, VHI, t)).min() for t in grid(5))
top_rel = min((-net(u, t["vdd"] + DELTA, t)).min() for t in grid(5))
def valley(H, d, ka, kb):   # ka: reverse-conducting device, kb: forward device; H = VDD - Vtn - Vtp
    if H + d <= 0: return 0.0
    if H <= ka * d / kb: return 0.5 * ka * kb / (ka + kb) * (H + d) ** 2
    return ka * d * H + 0.5 * ka * d**2 - (ka * d) ** 2 / (2 * kb)
print(f"3. bottom={bot:.3f} (closed form {valley(0.42, 0.1, 160, 80):.3f})  top, fixed Vhi={top_fixed:.3f} "
      f"(closed form {valley(0.78, 0.1, 80, 160):.3f})  top, VDD+delta={top_rel:.3f} (closed form {valley(0.42, 0.1, 80, 160):.3f})")

# 4. one square law vs an alpha-power-law saturation curve: best uniform fit
for alpha, Ion, X in ((1.2, 300.0, 1.1), (1.5, 300.0, 1.1), (1.2, 150.0, 0.95), (1.5, 150.0, 0.95)):
    x = np.linspace(0.0, X, 4001); f = Ion * (x / X) ** alpha
    obj = lambda p: np.max(np.abs(0.5 * p[0] * pp(x - p[1]) ** 2 - f))
    best = min((minimize(obj, (k0, x0), method="Nelder-Mead", options=dict(xatol=1e-6, fatol=1e-6, maxiter=20000))
                for k0 in (200, 400, 800) for x0 in (-0.3, -0.1, 0.0, 0.1)), key=lambda r: r.fun)
    print(f"4. alpha={alpha} Ion={Ion:.0f}: minimax residual {best.fun:.2f} uA, fitted threshold shift {best.x[1]:+.3f} V")

# 5. current a hard-threshold law calls zero (EKV-style interpolation, formula from memory)
kB, q = 1.380649e-23, 1.602176634e-19
for T, ksat, n in ((300.15, 240.0, 1.5), (398.15, 240.0, 1.5), (300.15, 530.0, 1.3), (300.15, 530.0, 1.5)):
    UT = kB * T / q; IS = 2 * n * (n * ksat) * UT**2
    print(f"5. T={T-273.15:.0f}C k_sat={ksat:.0f} n={n}: " + ", ".join(
        f"I({dv:+.2f} V)={IS*np.log1p(np.exp(dv/(2*n*UT)))**2:.3f}" for dv in (-0.20, -0.10, -0.05, 0.0)) + " uA")

# 6. valley restoring current of a square law with thresholds like the SKY130 device-details table
for name, kn, kp, vtn, vtp in (("TT W=7", 539, 324, 0.645, 0.888), ("TT W=0.42", 539, 324, 0.738, 0.819),
                               ("SS W=7", 519, 272, 0.677, 0.940), ("SS W=0.42", 519, 272, 0.818, 0.918)):
    print(f"6. {name}: " + "; ".join(f"VDD={vdd} d={d}: {valley(vdd - vtn - vtp, d, kn, kp):.2f}/{valley(vdd - vtn - vtp, d, kp, kn):.2f}"
                                     for vdd in (1.60, 1.80) for d in (0.1, 0.3)) + " uA (bottom/top)")
```

Observed output on 2026-11-09 (Python 3.14.0, numpy 2.4.6, scipy 1.18.0):

```text
1. max |positive-part - piecewise| over 2e5 random points: 4.55e-13 uA
2. I_up=10.476  I_dn=16.296  tau_up=3.4214  tau_dn=2.5602
3. bottom=5.920 (closed form 5.920)  top, fixed Vhi=6.440 (closed form 6.440)  top, VDD+delta=3.560 (closed form 3.560)
4. alpha=1.2 Ion=300: minimax residual 14.67 uA, fitted threshold shift -0.302 V
4. alpha=1.5 Ion=300: minimax residual 7.08 uA, fitted threshold shift -0.181 V
4. alpha=1.2 Ion=150: minimax residual 7.34 uA, fitted threshold shift -0.261 V
4. alpha=1.5 Ion=150: minimax residual 3.54 uA, fitted threshold shift -0.156 V
5. T=27C k_sat=240 n=1.5: I(-0.20 V)=0.004, I(-0.10 V)=0.043, I(-0.05 V)=0.129, I(+0.00 V)=0.347 uA
5. T=125C k_sat=240 n=1.5: I(-0.20 V)=0.023, I(-0.10 V)=0.131, I(-0.05 V)=0.292, I(+0.00 V)=0.611 uA
5. T=27C k_sat=530 n=1.3: I(-0.20 V)=0.003, I(-0.10 V)=0.050, I(-0.05 V)=0.181, I(+0.00 V)=0.576 uA
5. T=27C k_sat=530 n=1.5: I(-0.20 V)=0.009, I(-0.10 V)=0.095, I(-0.05 V)=0.284, I(+0.00 V)=0.767 uA
6. TT W=7: VDD=1.6 d=0.1: 2.82/2.82; VDD=1.6 d=0.3: 13.63/13.63; VDD=1.8 d=0.1: 12.60/9.30; VDD=1.8 d=0.3: 32.53/31.77 uA (bottom/top)
6. TT W=0.42: VDD=1.6 d=0.1: 2.07/2.07; VDD=1.6 d=0.3: 11.90/11.90; VDD=1.8 d=0.1: 11.31/8.52; VDD=1.8 d=0.3: 29.83/29.44 uA (bottom/top)
6. SS W=7: VDD=1.6 d=0.1: 0.61/0.61; VDD=1.6 d=0.3: 7.15/7.15; VDD=1.8 d=0.1: 7.15/5.62; VDD=1.8 d=0.3: 20.82/20.76 uA (bottom/top)
6. SS W=0.42: VDD=1.6 d=0.1: 0.00/0.00; VDD=1.6 d=0.3: 2.40/2.40; VDD=1.8 d=0.1: 2.40/2.39; VDD=1.8 d=0.3: 11.82/11.82 uA (bottom/top)
```

**Supplement, added 2026-11-09 after the independent fact-check.** The block below continues the script above: put the two blocks into one file, the first unchanged, and run it.
It adds items 7 and 8 and changes none of the output lines of items 1 to 6.
SHA-256 of the supplement block, taken over the text between the fences: `f389b83f24f02285ee2116db61f4ffd4c312fd608764e629fd1daa1464253c98`.

```python
# Supplement to Appendix A of docs/model.md, added 2026-11-09 after the independent fact-check.
# It continues the script above: run the two blocks as one file. Units as above. Arithmetic on
# stated inputs; not a proof, not a simulation, not evidence about any fabricated device.

# 7a. the closed form valley() of item 3 against brute force over u, in all three branches of the formula
UG = np.linspace(-1.0, 3.0, 400_001)
def brute(vdd, d, kn, kp, vtn, vtp):      # min over u of the restoring current at v = -d and at v = VDD + d
    t = dict(vdd=vdd, kn=kn, kp=kp, vtn=vtn, vtp=vtp)
    return net(UG, -d, t).min(), (-net(UG, vdd + d, t)).min()
branch = lambda H, d, ka, kb: 1 if H + d <= 0 else (2 if H <= ka * d / kb else 3)
def crosscheck(cases):                    # cases: (vdd, d, kn, kp, vtn, vtp); the bottom and the top value of each
    err, count = 0.0, [0, 0, 0]
    for vdd, d, kn, kp, vtn, vtp in cases:
        H = vdd - vtn - vtp
        for b, ka, kb in zip(brute(vdd, d, kn, kp, vtn, vtp), (kn, kp), (kp, kn)):
            err = max(err, abs(b - valley(H, d, ka, kb))); count[branch(H, d, ka, kb) - 1] += 1
    return f"max |closed form - brute force| = {err:.1e} uA; values in branch 1/2/3: {count[0]}/{count[1]}/{count[2]}"
ROWS = (("TT W=7", "TT", 539, 324, 0.645, 0.888), ("TT W=0.42", "TT", 539, 324, 0.738, 0.819),
        ("SS W=7", "SS", 519, 272, 0.677, 0.940), ("SS W=0.42", "SS", 519, 272, 0.818, 0.918))   # the rows of item 6
print("7a. the 32 values of item 6: " + crosscheck(
    [(vdd, d, kn, kp, vtn, vtp) for _, _, kn, kp, vtn, vtp in ROWS for vdd in (1.60, 1.80) for d in (0.1, 0.3)]))
rng7 = np.random.default_rng(20261109)
print("7a. 300 random parameter sets, 600 values: " + crosscheck(
    [(rng7.uniform(1.2, 2.0), rng7.uniform(0.05, 0.3), *rng7.uniform(100, 600, 2), *rng7.uniform(0.4, 1.0, 2)) for _ in range(300)]))

# 7b. the k literals of item 6 against k = 2*I_D*(W_cell/7 um)/(1.8 V - Vt)^2, with I_D in uA at W/L = 7/0.15 from the
#     SKY130 device-details tables (NMOS, high-threshold PMOS; typical and slow) and W_cell = 0.65 um (N), 1.0 um (P)
IDS = {"TT": (3512.0, 1003.0), "SS": (3078.0, 721.0)}
kfit = lambda i, w, vt: 2 * i * (w / 7) / (1.8 - vt) ** 2
print("7b. threshold that reproduces each k literal of item 6: " + ", ".join(
    f"{k}: {1.8 - (2 * i * (w / 7) / k) ** 0.5:.4f} V" for k, i, w in ((539, 3512.0, 0.65), (324, 1003.0, 1.0), (519, 3078.0, 0.65), (272, 721.0, 1.0))))
for name, c, _, _, vtn, vtp in ROWS:      # item 6 again, with k from each row's own thresholds
    kn, kp = kfit(IDS[c][0], 0.65, vtn), kfit(IDS[c][1], 1.0, vtp)
    print(f"7b. {name}, k={kn:.0f}/{kp:.0f}: " + "; ".join(f"VDD={vdd} d={d}: {valley(vdd - vtn - vtp, d, kn, kp):.2f}/{valley(vdd - vtn - vtp, d, kp, kn):.2f}"
                                                       for vdd in (1.60, 1.80) for d in (0.1, 0.3)) + " uA (bottom/top)")

# 7c. item 5 with the k_n of item 6 (539 where item 5 has 530)
for T, ksat, n in ((300.15, 539.0, 1.3), (300.15, 539.0, 1.5)):
    UT = kB * T / q; IS = 2 * n * (n * ksat) * UT**2
    print(f"7c. T={T-273.15:.0f}C k_sat={ksat:.0f} n={n}: " + ", ".join(
        f"I({dv:+.2f} V)={IS*np.log1p(np.exp(dv/(2*n*UT)))**2:.3f}" for dv in (-0.20, -0.10, -0.05, 0.0)) + " uA")

# 8. junction forward current from the ideal-diode law I = Isat(T)*(exp(V/(n*kT/q)) - 1), with
#    Isat(T) = Isat(Tnom)*exp((Eg(Tnom)/Vt(Tnom) - Eg(T)/Vt(T) + xti*ln(T/Tnom))/n), Eg(T) = 1.16 - 7.02e-4*T^2/(T + 1108)
#    8a. generic SPICE diode with the ngspice Level 1 defaults: Isat = 1e-14 A, n = 1, xti = 0, Tnom = 27 C
#    8b. junction parameters of the SKY130 tt cards, first bin (jss in A/m2, jsws in A/m, njs; xtis = 2, tnom = 30 C),
#        for an assumed drain 0.3 um long: area W*0.3 um, perimeter W + 0.6 um (gate edge not counted)
Eg = lambda T: 1.16 - 7.02e-4 * T * T / (T + 1108.0)
def diode(V, TC, isat, n=1.0, xti=0.0, TnomC=27.0):      # uA
    T, Tn = TC + 273.15, TnomC + 273.15
    return 1e6 * isat * np.exp((Eg(Tn) / (kB * Tn / q) - Eg(T) / (kB * T / q) + xti * np.log(T / Tn)) / n) * np.expm1(V / (n * kB * T / q))
BIAS = ((27.0, (0.30, 0.46, 0.50, 0.60)), (100.0, (0.30, 0.40, 0.46)))
table = lambda f: "; ".join(f"{TC:.0f} C: " + ", ".join(f"I({V:.2f} V)={f(V, TC):.3g}" for V in Vs) for TC, Vs in BIAS) + " uA"
print("8a. Level 1 default diode: " + table(lambda V, TC: diode(V, TC, 1e-14)))
for name, W, jss, jsws, njs in (("NMOS", 0.65e-6, 2.75e-3, 6.0e-10, 1.2928), ("PMOS", 1.0e-6, 2.17e-5, 8.2e-10, 1.2556)):
    isat = W * 0.3e-6 * jss + (W + 0.6e-6) * jsws
    print(f"8b. SKY130 {name} card junction: " + table(lambda V, TC: diode(V, TC, isat, njs, 2.0, 30.0)))
```

Observed output of the supplement on 2026-11-09 (same versions; the first 15 lines of the combined run are the lines above):

```text
7a. the 32 values of item 6: max |closed form - brute force| = 9.1e-09 uA; values in branch 1/2/3: 2/20/10
7a. 300 random parameter sets, 600 values: max |closed form - brute force| = 1.3e-08 uA; values in branch 1/2/3: 96/224/280
7b. threshold that reproduces each k literal of item 6: 539: 0.7000 V, 324: 0.8595 V, 519: 0.7505 V, 272: 0.9297 V
7b. TT W=7, k=489/345: VDD=1.6 d=0.1: 2.82/2.82; VDD=1.6 d=0.3: 13.61/13.61; VDD=1.8 d=0.1: 12.03/9.71; VDD=1.8 d=0.3: 32.49/32.18 uA (bottom/top)
7b. TT W=0.42, k=578/298: VDD=1.6 d=0.1: 2.01/2.01; VDD=1.6 d=0.3: 11.56/11.56; VDD=1.8 d=0.1: 11.33/7.96; VDD=1.8 d=0.3: 28.98/28.21 uA (bottom/top)
7b. SS W=7, k=453/279: VDD=1.6 d=0.1: 0.59/0.59; VDD=1.6 d=0.3: 6.91/6.91; VDD=1.8 d=0.1: 6.87/5.63; VDD=1.8 d=0.3: 20.12/20.12 uA (bottom/top)
7b. SS W=0.42, k=593/265: VDD=1.6 d=0.1: 0.00/0.00; VDD=1.6 d=0.3: 2.46/2.46; VDD=1.8 d=0.1: 2.46/2.43; VDD=1.8 d=0.3: 12.13/12.13 uA (bottom/top)
7c. T=27C k_sat=539 n=1.3: I(-0.20 V)=0.003, I(-0.10 V)=0.051, I(-0.05 V)=0.184, I(+0.00 V)=0.586 uA
7c. T=27C k_sat=539 n=1.5: I(-0.20 V)=0.009, I(-0.10 V)=0.096, I(-0.05 V)=0.289, I(+0.00 V)=0.780 uA
8a. Level 1 default diode: 27 C: I(0.30 V)=0.00109, I(0.46 V)=0.529, I(0.50 V)=2.49, I(0.60 V)=119; 100 C: I(0.30 V)=0.999, I(0.40 V)=22.4, I(0.46 V)=145 uA
8b. SKY130 NMOS card junction: 27 C: I(0.30 V)=7e-06, I(0.46 V)=0.000838, I(0.50 V)=0.00277, I(0.60 V)=0.0552; 100 C: I(0.30 V)=0.00192, I(0.40 V)=0.0213, I(0.46 V)=0.09 uA
8b. SKY130 PMOS card junction: 27 C: I(0.30 V)=9.26e-06, I(0.46 V)=0.00128, I(0.50 V)=0.00438, I(0.60 V)=0.0952; 100 C: I(0.30 V)=0.00299, I(0.40 V)=0.0357, I(0.46 V)=0.158 uA
```

In item 7a the brute-force minimum is taken on a grid of input values 1e-5 V apart, so differences of the order of 1e-8 µA are grid error.

## Appendix B. Scratch Lean check: restricting a record to one supply value

This file imports the generated design record and adds declarations in the project's namespace. It is not in the repository.
It depends only on the `Design`, `InBox` and `Admissible` definitions, so it does not depend on how trajectories are defined.
It is offered for porting. Until the owner of the Lean sources ports and audits it, it is not a project claim.

Check performed: `lake env lean <file>` from the repository root on 2026-11-09 at 16:25, with Lean 4.35.0 and the build products then present. The repository head was `fe9f401`.
Result: no errors. `#print axioms` reported only `propext`, `Classical.choice` and `Quot.sound` for the four declarations listed at the end.
SHA-256 of the code block below, taken over the text between the fences: `9ee8b0f5e1f25a0522b0819780a3906af9b291764dae97b843b18ab0820f1a15`.

Note added 2026-11-09: the file below is reproduced unchanged, as it was checked at `fe9f401`. It no longer matches the library. Compiled again on 2026-11-10 against the library at commit `8c2637b` (`lake env lean`, with the block below as the whole file), it fails with one error: the fields `Vtn_nonneg` and `Vtp_nonneg` are missing in the structure literal. In the library at commit `8c2637b`, `Design.atSupply`, `Design.Admissible.atSupply` and `Design.InBox.atSupply` are declarations of `VoltageToBit/Proofs/AtSupply.lean`; `Design.Admissible` has two further fields, `Vtn_nonneg` and `Vtp_nonneg`, which the structure literal below does not supply; and `Design.Admissible.atSupply` has no hypothesis `hN'` (§6.3). `Design.RhiN'`, `Examples.illustrative_RhiN'`, `Examples.illustrative_atSupply` and `Examples.illustrative_atSupply_safe` are names of this scratch file only. The library's statement for the illustrative record is `Examples.illustrative_safe_atSupply`.

```lean
import VoltageToBit.Examples.IllustrativeDesign

/-!
Workstream B scratch check. Not part of the repository.

Everything here depends only on `Model/PosSq.lean`, the `Design`,
`Design.InBox` and `Design.Admissible` definitions of `Model/Inverter.lean`,
and the generated record `Examples/IllustrativeDesign.lean`. Nothing mentions
`IsTrajectory`, so the results do not depend on how the dynamics are stated.
-/

namespace VoltageToBit

open Set

/-! ## Restricting an admissible record to one supply value -/

namespace Design

/-- The record restricted to the single supply value `V0`, with the top of the
safe domain the same distance above `V0` as `Vhi` is above `VDDhi`. -/
noncomputable def atSupply (D : Design) (V0 : ℝ) : Design :=
  { D with VDDlo := V0, VDDhi := V0, Vhi := V0 + (D.Vhi - D.VDDhi) }

/-- `RhiN` with the top of the domain taken relative to the lowest supply. -/
noncomputable def RhiN' (D : Design) : ℝ :=
  D.knlo / 2 * (psq (D.uHi - D.Vtnhi)
    - psq (D.uHi - (D.VDDlo + (D.Vhi - D.VDDhi)) - D.Vtnhi))

/-- **Supply-relative admissibility.** If `D` is admissible and `eps < RhiN'`,
then for every supply value `V0` of its range the record with the supply fixed
at `V0` and the safe domain `[Vlo, V0 + (Vhi - VDDhi)]` is admissible too. Every
theorem about admissible records therefore holds with the safe domain measured
from the actual supply. -/
theorem Admissible.atSupply {D : Design} (hD : D.Admissible) {V0 : ℝ}
    (h1 : D.VDDlo ≤ V0) (h2 : V0 ≤ D.VDDhi) (hN' : D.eps < D.RhiN') :
    (D.atSupply V0).Admissible := by
  have hkp : 0 ≤ D.kplo / 2 := by linarith [hD.kp_pos]
  have hkn : 0 ≤ D.knlo / 2 := by linarith [hD.kn_pos]
  have hkph : 0 ≤ D.kphi / 2 := by linarith [hD.kp_pos, hD.kp_le]
  have hδ : 0 ≤ D.Vhi - D.VDDhi := by linarith [hD.Vhi_ge]
  refine
    { VDD_pos := ?_, VDD_le := ?_, kn_pos := hD.kn_pos, kn_le := hD.kn_le,
      kp_pos := hD.kp_pos, kp_le := hD.kp_le, Vtn_le := hD.Vtn_le, Vtp_le := hD.Vtp_le,
      C_pos := hD.C_pos, C_le := hD.C_le, eps_nonneg := hD.eps_nonneg, Vlo_le := hD.Vlo_le,
      Vhi_ge := ?_, VOL_nonneg := hD.VOL_nonneg, VOL_le_VIL := hD.VOL_le_VIL,
      VIL_lt_VIH := hD.VIL_lt_VIH, VIH_le_VOH := hD.VIH_le_VOH, VOH_le := ?_,
      up := ?_, dn := ?_, hiP := ?_, hiN := ?_, loN := hD.loN, loP := ?_ }
  · show 0 < V0
    linarith [hD.VDD_pos]
  · show V0 ≤ V0
    exact le_rfl
  · show V0 ≤ V0 + (D.Vhi - D.VDDhi)
    linarith
  · show D.VOH ≤ V0
    linarith [hD.VOH_le]
  · -- pull-up margin: a higher supply only helps
    show D.eps < D.kplo / 2 * (psq (V0 - D.VIL - D.Vtphi) - psq (D.VOH - D.VIL - D.Vtphi))
      - D.knhi / 2 * psq (D.VIL - D.Vtnlo)
    have hup := hD.up
    unfold Design.Iup at hup
    have hm : psq (D.VDDlo - D.VIL - D.Vtphi) ≤ psq (V0 - D.VIL - D.Vtphi) :=
      psq_mono (by linarith)
    have := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hm (psq (D.VOH - D.VIL - D.Vtphi))) hkp
    linarith
  · -- pull-down margin: a lower supply only weakens the opposing PMOS
    show D.eps < D.knlo / 2 * (psq (D.VIH - D.Vtnhi) - psq (D.VIH - D.VOL - D.Vtnhi))
      - D.kphi / 2 * psq (V0 - D.VIH - D.Vtplo)
    have hdn := hD.dn
    unfold Design.Idn at hdn
    have hm : psq (V0 - D.VIH - D.Vtplo) ≤ psq (D.VDDhi - D.VIH - D.Vtplo) :=
      psq_mono (by linarith)
    have := mul_le_mul_of_nonneg_left hm hkph
    linarith
  · -- top boundary, PMOS branch
    show D.eps < D.kplo / 2 * (psq (V0 - D.uHi - D.Vtphi + (V0 + (D.Vhi - D.VDDhi) - V0))
      - psq (V0 - D.uHi - D.Vtphi))
    have e : V0 + (D.Vhi - D.VDDhi) - V0 = D.Vhi - D.VDDhi := by ring
    rw [e]
    have hP := hD.hiP
    unfold Design.RhiP at hP
    have hm := psq_incr_mono (d := D.Vhi - D.VDDhi) (x := D.VDDlo - D.uHi - D.Vtphi)
      (y := V0 - D.uHi - D.Vtphi) hδ (by linarith)
    have := mul_le_mul_of_nonneg_left hm hkp
    linarith
  · -- top boundary, NMOS branch
    show D.eps < D.knlo / 2 * (psq (D.uHi - D.Vtnhi)
      - psq (D.uHi - (V0 + (D.Vhi - D.VDDhi)) - D.Vtnhi))
    unfold Design.RhiN' at hN'
    have hm : psq (D.uHi - (V0 + (D.Vhi - D.VDDhi)) - D.Vtnhi)
        ≤ psq (D.uHi - (D.VDDlo + (D.Vhi - D.VDDhi)) - D.Vtnhi) := psq_mono (by linarith)
    have := mul_le_mul_of_nonneg_left
      (sub_le_sub_left hm (psq (D.uHi - D.Vtnhi))) hkn
    linarith
  · -- bottom boundary, PMOS branch: a higher supply only helps
    show D.eps < D.kplo / 2 * (psq (V0 - D.uLo - D.Vtphi) - psq (D.Vlo - D.uLo - D.Vtphi))
    have hP := hD.loP
    unfold Design.RloP at hP
    have hm : psq (D.VDDlo - D.uLo - D.Vtphi) ≤ psq (V0 - D.uLo - D.Vtphi) :=
      psq_mono (by linarith)
    have := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hm (psq (D.Vlo - D.uLo - D.Vtphi))) hkp
    linarith

/-- A parameter point with supply `V0` that lies in the box of `D` lies in the
box of the restricted record. -/
theorem InBox.atSupply {D : Design} {θ : Params} (hθ : D.InBox θ) :
    (D.atSupply θ.VDD).InBox θ :=
  { VDD_ge := le_rfl, VDD_le := le_rfl, kn_ge := hθ.kn_ge, kn_le := hθ.kn_le,
    kp_ge := hθ.kp_ge, kp_le := hθ.kp_le, Vtn_ge := hθ.Vtn_ge, Vtn_le := hθ.Vtn_le,
    Vtp_ge := hθ.Vtp_ge, Vtp_le := hθ.Vtp_le }

end Design

/-! ## The illustrative record -/

namespace Examples

/-- For the illustrative record the extra condition uses the same number as `RhiN`. -/
theorem illustrative_RhiN' : illustrative.RhiN' = 2.312 := by
  norm_num [illustrative, Design.RhiN', psq_eq_ite]

/-- The illustrative record, restricted to any supply value of its range, is
admissible. `hadm` is `Examples.illustrative_admissible` in the repository. -/
theorem illustrative_atSupply (hadm : illustrative.Admissible) {V0 : ℝ}
    (h1 : (1.62 : ℝ) ≤ V0) (h2 : V0 ≤ 1.98) : (illustrative.atSupply V0).Admissible := by
  refine hadm.atSupply (by simpa [illustrative] using h1) (by simpa [illustrative] using h2) ?_
  rw [illustrative_RhiN']
  norm_num [illustrative]

/-- Its safe domain is `[-0.10, V0 + 0.10]`. -/
theorem illustrative_atSupply_safe (V0 : ℝ) :
    (illustrative.atSupply V0).Safe = Icc (-0.10 : ℝ) (V0 + 0.10) := by
  show Icc (-0.10 : ℝ) (V0 + ((2.08 : ℝ) - 1.98)) = Icc (-0.10 : ℝ) (V0 + 0.10)
  norm_num

end Examples

end VoltageToBit

#print axioms VoltageToBit.Design.Admissible.atSupply
#print axioms VoltageToBit.Design.InBox.atSupply
#print axioms VoltageToBit.Examples.illustrative_atSupply
#print axioms VoltageToBit.Examples.illustrative_atSupply_safe
```

## Interface proposals

Each proposal gives the change, the reason and the consequence.
"Draft" means the coordinator's draft v0 as given to B. Where the repository has moved since, the entry says so.
B applied none of them. While this was being written the coordinator adopted IP-1 in commit `eae25ed` and IP-2 in commit `1fdf1d9`.

### IP-1. Choose the parameter point per instant, and state the bridge as a bracketing condition (adopted)

- **Change.** Let `IsTrajectory` choose `θ` in the box at each instant, and state the model-error obligation as bracketing between two members of the box. Adopted in commit `eae25ed` as `IsTrajectory`, `Design.exists_inBox_of_between` and `IsTrajectory.of_sandwich`.
- **Reason.** No short-channel device is within 2 µA of one square law over the safe domain (§5.2). The proofs use only four one-sided margins (§5.3).
- **Consequence.** A strictly stronger theorem with the same `Admissible` conditions and the same deadlines. The physical obligation becomes an envelope fit that D can test (§9.5).
- **Still to do.**
  - Each design record should say which part of each box interval is process or supply spread and which is allowance for model form. A fitted box will be much wider, its margins must be recomputed, and an admissible fitted record may not exist (§10.3).
  - The displacement current of a moving supply, `C_jp·VDD'`, is a disturbance term and must be in the budget (§7.2).
  - `README.md` still lists a time-varying supply under "What is not claimed", while `docs/interface.md` §4 now says a supply moving within its range is covered. One of the two needs changing.
  - The handoff says time-varying parameters need an explicit extension. Record this change as that extension.

### IP-2. Add the supply-relative safe domain, and use it for the physical claim (adopted)

- **Change.** Add `Design.atSupply` and `Design.Admissible.atSupply` (Appendix B). State the physical claim for runs at one supply value `V0`, with the record `D.atSupply V0` and its safe domain `[V_lo, V0 + (V_hi − VDD_max)]`. Name that set as the initial-state set of the physical claim.
- **Reason.** The fixed bound admits 0.46 V above the actual supply at `VDD_min`. That is outside the comparison model's documented range, how much the drain junction conducts there is open, and the model-error obligation is currently demanded there too (§6.3).
- **Consequence.** In the form proposed here, one extra numeric condition, `ε_I < RhiN'`, where `RhiN'` equals `RhiN` for the illustrative record. No change to the record. The fixed-domain theorem remains true and can stay. The restricted record's deadlines are no larger. The lemma is independent of IP-1.
- **Status.** Ported by the coordinator in commit `1fdf1d9` as `Proofs/AtSupply.lean`. B has not reviewed the port, and an author should not be the only reviewer of this lemma. Still to do: name the supply-relative set as the initial-state set of the physical claim in `docs/interface.md`.
- **Note added 2026-11-09.** The extra numeric condition is no longer needed. Since commit `d420a20`, `Design.Admissible` requires nonnegative threshold lower bounds (`Vtn_nonneg`, `Vtp_nonneg`), `RhiN'` is no longer in the library, and `Design.Admissible.atSupply` holds for every admissible record and every supply value of its range (§6.3).

### IP-3. State the environment that gives `ε_I` a physical meaning

- **Change.** Add to the interface, as environment restrictions outside Lean: an input slew bound `S_u`; a bound on gate-drain capacitance `C_M`; a bound on aggressor coupling `Σ C_c·S_a`; a supply slew bound and zero ground bounce; a temperature or temperature range; an input range `[−δ, VDD + δ]`. Add the budget inequality of §7.3 and a budget table to each design record.
- **Reason.** Without them a positive `ε_I` reads as robustness to crosstalk and feedthrough, which at 2 µA it is not (§7).
- **Consequence.** The illustrative record needs Budget A or an equivalent written next to it. The explicit run's 9 V/ns ramp needs either a slower ramp or a note that the node has no gate-drain capacitance. The caveat in `Proofs/Chain.lean` should carry the number of §7.4: the first stage may slew at 29 to 58 V/ns, so the corollary is about ideal one-node stages. No change to any theorem.
- **Note added 2026-11-10.** The 29 to 58 V/ns are bounds for first-stage inputs restricted to `[0, 0.40]` V and to `[1.25, 1.98]` V; for the valid-input classes of the guarantee the slew has no bound (§7.4). At commit `8c2637b` the header of `VoltageToBit/Proofs/Chain.lean` carries the two figures with these input ranges, and says that the corollary is to be read as a statement about two ideal one-node stages.

### IP-4. Define `C` as incremental capacitance and restrict the first instance to a capacitor load

- **Change.** In the interface, define `c` as `∂Q/∂v` with every attached capacitor counted once. State that currents due to other nodes moving belong to the disturbance. State that the first instance covers an ideal grounded capacitor plus the inverter's own parasitics, and not a switching gate load.
- **Reason.** §4.2. Folding coupling into the capacitance range by Miller factors is unsound, and a switching load injects current during the very interval the deadline measures.
- **Consequence.** D's test bench uses a linear capacitor with `C_L` chosen so that `C_L` plus self-loading lies in `[C_min, C_max]`. A gate load becomes a later experiment with its own coupling budget.

### IP-5. Replace the headroom sentence by the exact condition

- **Change.** Where the draft says invariance needs `VDD_min > V_tn,max + V_tp,max`, say instead that it needs the boundary margins to exceed `ε_I`, and give the valley formula `M(H, δ; k_a, k_b)` of §6.1 as the exact minimum.
- **Reason.** The inequality is neither necessary nor sufficient. The margin's sensitivity to the threshold sum, `k·δ` per volt, is the important fact.
- **Consequence.** Documentation only. Workstream E gets an exact number to test the split bounds against: 5.92, 6.44 and 3.56 µA for the illustrative record.

### IP-6. Record that boundary invariance, not switching, limits `ε_I`

- **Change.** State in the interface or the design record that the largest admissible `ε_I` for `illustrative-1v8`, with its present split points, is just under 2.312 µA, set by `RhiN`.
- **Reason.** Readers will compare `ε_I = 2` with `I_up = 10.5` and conclude there is a factor of five in hand. There is 16 %.
- **Consequence.** Documentation only. Any experiment that raises `ε_I` must also raise `δ` or move the split points, which is a different record.

### IP-7. Keep absolute thresholds and list their side conditions

- **Change.** Keep thresholds in absolute volts. Add the traps of §8.2 to the interface, in particular that the opposing device is not off at `V_IH` when the supply is high and that `V_IL` is 0.05 V below `V_tn,min`.
- **Reason.** Absolute thresholds compose across supplies; the traps are where the physical residual concentrates.
- **Consequence.** Documentation only.

### IP-8. Label the illustrative record's relation to SKY130

- **Change.** In `designs/illustrative-1v8.json` or beside it, add: thresholds are about 0.15 to 0.35 V below SKY130's documented short-channel thresholds for the NMOS and the high-threshold PMOS; `VDD_max` and the domain top exceed the SKY130 models' documented 1.95 V; no temperature is implied.
- **Reason.** The record will be compared with SKY130 BSIM4 by D. Without the label a mismatch could be read as a defect of the proof.
- **Note added 2026-11-10.** "Will be compared" was the plan when this was written. By the owner decision recorded in §0 the comparison is prepared, not planned to be run for this milestone.
- **Consequence.** For any SKY130-anchored record, use a supply range within 1.60 to 1.95 V and decide among the options of §10.3 for the safe domain. That is a new experiment, not a revision of this one.

### IP-9. Fix the comparison model and what D reports

- **Change.** Adopt §9: SKY130 BSIM4 pinned as in §9.2, tiers T0 to T3, and the report items of §9.5, with the four margins and the envelope fit as the primary results.
- **Reason.** A whole-surface residual against one fitted square law will be large and uninformative. The four margins are what the theorem needs.
- **Consequence.** D's discrepancy report is organised by margin and by corner. The expected failures of §9.6 are written down beforehand so that results can contradict them.

### IP-10. State the noise exclusion in the claim

- **Change.** `README.md` already lists noise with unbounded tails as not claimed. Add the size estimate of §7.5 and the reason, and repeat the exclusion in the docstring of the headline theorem.
- **Reason.** No deterministic bound covers thermal, flicker or telegraph noise. A reader should see how small the effect is and that it is nevertheless outside the theorem.
- **Consequence.** Documentation only. A probabilistic layer is future work.

### IP-11. Optional: weaken the trajectory class to Dini-derivative bounds

- **Change.** Require bounds on the right Dini derivatives instead of a right derivative at every instant.
- **Reason.** It would cover every Carathéodory solution for continuous inputs (§4.3).
- **Consequence.** Rework of `Proofs/Reach.lean` on top of Mathlib's liminf-slope lemmas. Low priority. The v1 candidate of `docs/interface.md` already records the limit, so nothing is misstated if this is not done.

### IP-12. Later: a charge-form treatment of feedthrough and crosstalk

- **Change.** Use the state `C_tot·v − C_M·u − Σ C_c·a`.
- **Reason.** Physical coupling is bounded in charge, not in amplitude (§7.2, §7.5).
- **Consequence.** A different theorem shape, with voltage guard bands in place of slew restrictions. Not for the first instance.

## Corrections after the independent fact-check (2026-11-09)

The fact-check is recorded in `evidence/factcheck/factcheck.json`, areas `level1` and `sky130`. Each line below is one change.
The text before these corrections is the version with sha256 `5550139b536c5042e14ed1f2e800b3257e41188254cd51eff8dc061674ec0a78`; pins of that hash in other documents refer to it.
The first code block of Appendix A, its recorded output and the code block of Appendix B are unchanged. Statements tagged [L] still refer to commit `fe9f401`.
Where a paragraph that begins "Note added 2026-11-09" or "Note added 2026-11-10" describes the Lean library, it describes the library at commit `8c2637b`, according to its sources. The notes of 2026-11-09 were written against commit `2bf6f81` and checked again against `8c2637b` on 2026-11-10; what that check covered is in the last part of this section. The project was not rebuilt for them, and they carry no [L] tag; build products newer than every source file were present in the checkout.
Sources read for the corrections on 2026-11-09: ngspice at commit `a80f6e3e95d51534905b1f23410a951802666656`; the SKY130 cards at `f62031a1…` and the device-details tables at `7198cf64…` (§9.2); `fossi-foundation/skywater-pdk-libs-sky130_fd_pr` at `403964dc…` and its commit list; the open_pdks and FreePDK45 pages.

**Corrections from the fact-check, with the record of the owner's decisions.**

| Where | What was wrong | What it says now |
| --- | --- | --- |
| Header | No pointer to corrections. | One line pointing to this section. |
| §0 | Two decisions of the project owner were not recorded. | Two dated sentences: the base layer stays at circuit level; no further numerical experiments or SPICE comparison are planned, so §9 and the instructions to workstream D are prepared and not planned to be run, and statements about a real device are expectations or assumptions. |
| §0, last paragraph | It called "Interface proposals" the last section. | It names this section as the last one. |
| §1 item 4, last sentence | It stated as fact that a real device supplies less restoring current at the slow corner and that the invariance condition fails. The body gives this only as an untested expectation. | The smallest restoring current of a square law with the documented thresholds is 0 to 0.6 µA, below `ε_I` [D]; B expects that the four boundary conditions cannot all hold for a SKY130-bracketing box at that corner and supply; untested; a failed sufficient condition is not a failed circuit. |
| §1 item 5; IP-2, reason | "close to junction conduction" and "near junction conduction" rested on the junction figures corrected below. | How much the drain junction conducts 0.46 V above the supply is called open, with a pointer to §6.3. |
| §1 item 10, §10.2 row "Thresholds", IP-8 | "0.2 to 0.35 V" lower does not follow from the quoted ranges: the NMOS low end differs by 0.15 V. | "about 0.15 to 0.35 V". |
| §3.2, Checks | "The reverse cases are not Lean lemmas" is true of commit `fe9f401` only. | The sentence stays; a dated note names the six `*_rev_*` lemmas present since commit `499cb39`. |
| §3.2, parameter map, row "no body effect" | "`PHI` then has no effect" holds only at the nominal temperature and without `TOX`. | Restricted to the channel current at `T = TNOM`; the dependence on `PHI` at other temperatures and through `TOX` is stated; a control should run at `TNOM` or record `PHI`. |
| §3.4 row "Junction diodes", §6.2 row "Drain-bulk junction forward conduction" | The figures, tagged [D, with M inputs], had no stated inputs. They match a generic SPICE default diode, not the SKY130 junctions. | Two readings with stated inputs, computed in Appendix A item 8: the Level 1 default diode, which the old figures match, and the SKY130 cards' junction parameters with an assumed 0.3 µm drain, which give currents about three orders of magnitude lower. Marked as arithmetic, not simulation. |
| §6.3, sentence on junction currents at 100 °C | "B estimates junction currents comparable to the channel currents" held only for the unstated default diode. | About 145 µA for the Level 1 default diode and about 0.16 µA with the SKY130 PMOS card's parameters; called an open question. |
| §3.4 row "Non-quasi-static effects" | "≈ 1 ps" had no stated inputs and fits the NMOS only. | 1.0 ps (NMOS) and 2.7 ps (PMOS), with `L`, `u0` and the overdrive stated; less margin for the PMOS. |
| §4.1 | "exactly when" claimed an equivalence, and "Lean states this as" named four theorems that are one-way implications with stronger hypotheses. | "if", given continuity and a right derivative at every instant; said to be sufficient, not equivalent; the four theorems are described as one-way, with the balance and the capacitance bound required at every instant. |
| §4.2 table, row "Oxide capacitance" | 8.33 fF/µm² was misrounded. | 8.32 fF/µm² (3.9 times the vacuum permittivity over 4.148 nm is 8.3248). |
| §5.2, §10.2 row "`k_n`, `k_p`" | "about 540 and 320 µA/V²" did not say that the value depends on the threshold paired with the documented current; "two to three times weaker" understated the spread, which reaches four. | The dependence is stated (489 to 578 and 298 to 345 µA/V² for the two typical thresholds); "roughly two to four times weaker". |
| §6.1 | "Appendix A checks the formula against brute force": the script checked three cases, all in the third branch. | Says so, and cites the new item 7a: the 32 values of item 6 and 600 random values, all three branches. |
| §6.4 table, last row | A single 2.40 µA although bottom and top differ. | "2.40 / 2.39 µA". |
| §6.4, sentences on the `k` values | The four values could not be reproduced: the threshold paired with each documented current was not stated, and with the thresholds of the table rows they do not reproduce the documented currents. | "`k` values fitted to" in place of "that reproduce"; the formula and the currents are stated; item 7b gives the thresholds that reproduce the four values and the alternative with each row's own thresholds (table entries move by less than 5 %). The table entries are not recomputed. |
| §6.5 | "no latch-up" was listed under `PHY-06`; the register has it in `ENV-12` (found in the `register` area of the fact-check). | Listed under `ENV-12`, as in the register at commit `2bf6f81`. |
| §9.1 row "FreePDK45" | "1.1 V" is not on the cited page and had no tag. | "About 1 V", with the page's statement of a 1.0 V supply; "strongly velocity-saturated" is tagged [M]. |
| §9.2 row "Head when read" | "The two most recent changes" counted one pull request twice. | The most recent change, pull request 8 (a commit and its merge); it also touches `models/parameters/critical.spice` in the original model tree. |
| §9.2 row "Installer", §12 OPDK | The open_pdks repository has moved; the old address only redirects. | `fossi-foundation/open-pdks`, with the former address noted. |
| §9.3, first bullet | The `tt` section was described with three includes; it has four. | The four files are listed; `corners/tt.spice` has 30 include statements of its own. |
| §10.3, first bullet | "the four boundary conditions … fail" can be read as "each one fails"; single conditions can still hold. | "cannot all hold". |
| §12 NGSRC, FPDK45 | The readings made for these corrections were not recorded. | Files, commit and date of those readings. |
| Appendix A, introduction | "It reproduces every [D] number that is not a one-line calculation" overstated the coverage. | Lists what items 1 to 8 reproduce; says that some other [D] numbers cannot be redone from this document alone, with examples; notes that items 5 and 6 use 530 and 539 µA/V² for the same `k_n`; says that the first block is unchanged. The comment line "Reproduces the [D] numbers of the document" inside the unchanged first block is to be read with that list. |
| Appendix A, supplement | The valley formula was cross-checked in one branch only, and the junction figures and the `k` inputs were not reproducible. | A second block that continues the script (items 7a to 7c, 8a, 8b), with its SHA-256 and its recorded output. In that output item 7a reports a largest difference between the closed form and brute force of 1.3e-8 µA. |

**Changes that follow the Lean library.** The library moved after this document was written. These rows made the text consistent with it at commit `2bf6f81`. The same notes were checked again at commit `8c2637b` (last part of this section).

| Where | What was wrong | What it says now |
| --- | --- | --- |
| §1 item 6, §7.4 "Explicit run" | "The explicit run" was the only one at `fe9f401`; the library now has two. | Dated notes: the 9 V/ns run is `Examples.illustrative_scenario`, and the text stays true of it; `Examples.illustrative_feedthrough_scenario` is a second run exactly at the allowance (0.5·2 + 0.1·5 + 0.5 = 2.0 µA), with a valid-low input only, a witness and not evidence about a device. |
| §4.1, §5.1 | The lists of bridge lemmas predate two lemmas. | Dated notes on `IsTrajectory.of_static_sandwich` and `IsTrajectory.of_charge_balance` and on what each asks for. |
| §4.4 | "No Lean consumer" for the input range and for the input slew bound is true of `fe9f401` only. | Dated note: the two lemmas above take such hypotheses; the guarantee theorems still take every `u`. |
| §6.3, Appendix B, IP-2 | The text told the reader that the supply-relative lemma needs `ε_I < RhiN'`, and cited `Examples.illustrative_RhiN'` as if it were a library name. Neither holds for the library. | The condition and the two primed names are attributed to the scratch file of Appendix B. Dated notes say that `Design.Admissible.atSupply`, `trajectory_safe_atSupply` and `solution_safe_atSupply` need no extra condition (`Design.Admissible.RhiN_atSupply`), that `Design.Admissible` has the fields `Vtn_nonneg` and `Vtp_nonneg`, and that the scratch file no longer matches the library. |
| §7.4 "Two stages" | "with valid inputs these bounds are 28.6 … and 58.3 V/ns": the bounds need an input range. | Dated note: they hold for inputs in `[0, 0.40]` V and `[1.25, 1.98]` V, where they are now Lean theorems; for the input classes of the guarantee the slew has no bound; the conclusion of the paragraph stands. |
| §10.1 | `τ_up` and `τ_dn` could be read as the best deadlines known. | Dated note: they are the closed-form bounds; the library has 2.26 and 1.425 ns, and no deadline below 2.168 or 1.0234 ns is valid. |

Name check on 2026-11-09: every name of a project declaration quoted in the prose was searched under `VoltageToBit/` at commit `2bf6f81`. Two did not resolve, `RhiN'` and `Examples.illustrative_RhiN'`; both are now attributed to the scratch file of Appendix B. The names inside the code block of Appendix B were not changed. The Mathlib lemma named in §4.3 is in the local Mathlib copy at the revision given in §12.

**Corrections after the second verification round (2026-11-10).** The verdict is recorded in `evidence/verification/round2-finish-fixes.json`, entry `model-doc`: two issues to fix and five minor ones. The number of each issue is given in the first column. Each issue was checked again against the sources before the text was changed. For issue 1 the junction currents at 0.3 V and 100 °C were recomputed from the inputs stated in Appendix A item 8 with a separately written script: 0.9986 µA for the Level 1 default diode, 0.00192 and 0.00299 µA for the two cards. For issue 3 the three device-details tables were fetched again from the documentation repository at `7198cf64…` (§9.2): thresholds at `L = 0.15 µm` of 0.603 to 0.852 V (NMOS), 0.678 to 0.962 V (high-threshold PMOS; the EDR columns reach 0.963 V) and 0.554 to 0.858 V (standard PMOS). Each line below is one change.

| Where | What was wrong | What it says now |
| --- | --- | --- |
| §10.3, options table, row "Enlarge `δ` to about 0.3 V" (issue 1) | "closer to junction conduction when hot" was a third phrase that rested on the junction figures corrected above. It holds for the Level 1 default diode only. | How much the drain junctions conduct at such an excursion when hot is called open, with the two figures of Appendix A item 8 for 0.3 V and 100 °C: about 1.0 µA, and 0.002 to 0.003 µA. This completes the row "§1 item 5; IP-2, reason" above. |
| §4.1 (issue 2) | The note on `IsTrajectory.of_charge_balance` was pinned to commit `2bf6f81` and listed continuity of `u` and `a_1` among the conditions. At that commit the lemma had no such hypothesis; it asked for a continuous `v`. The three continuity hypotheses came with commit `9065e3b`. | Rewritten for commit `8c2637b`: a table of the sixteen hypotheses with their Lean names. Continuity is assumed of the charge, of `u` and of `a_1`, and not of `v`. `slew_bound_of_rderiv` and the step `Examples.uStepR` are cited for the role of continuity. An input that is not continuous on `[a, b]` is said to be outside the lemma. |
| §10.2 row "Thresholds"; §1 item 10; IP-8 (issue 3) | "about 0.15 to 0.35 V lower" does not hold for the standard PMOS quoted in the same row, for which the box is 0.10 to 0.26 V lower. | §10.2 gives both figures. §1 item 10 and IP-8 name the two device types for which 0.15 to 0.35 V holds: the NMOS and the high-threshold PMOS. |
| §1 item 6; IP-3 (issue 4) | "29 to 58 V/ns" was quoted as the model's own slew bound without the input ranges that the note of §7.4 gives. | Dated notes: the figures hold for inputs in `[0, 0.40]` V and `[1.25, 1.98]` V, and for the valid-input classes of the guarantee the slew has no bound. The note in IP-3 also records that the header of `Proofs/Chain.lean` carries the figures with these ranges at commit `8c2637b`. |
| §0; IP-8 (issue 5) | "The record will be compared with SKY130 BSIM4 by D" states a plan. The owner decided that no SPICE comparison is planned, and the clause of §0 covered instructions to D only. | The clause of §0 covers every instruction to, and every expectation of work by, workstream D. A dated note in IP-8 says that the comparison is prepared, not planned to be run for this milestone. |
| This section, rows "§6.1", "§6.4, sentences on the `k` values" and "Appendix A, supplement" (issue 6) | Two slips. "The table is unchanged" stood beside a row that records a change of the same table. "Largest difference 1.3e-8 µA" was attributed to §6.1, where it does not appear. | "The table entries are not recomputed". The figure is now in the row of the Appendix A supplement, whose recorded output contains it. |
| Header; §0, last paragraph (not one of the seven issues) | Both named only the corrections of 2026-11-09. | Both also name the corrections of 2026-11-10. |

Examined and left unchanged (issue 7): the first code block of Appendix A still uses 530 µA/V² in item 5 and 539 µA/V² in item 6 for the same `k_n`, and its comment line still reads "Reproduces the [D] numbers of the document". The block is kept byte-identical because its SHA-256 is pinned in `docs/assumptions.md` (key `A-py` at commit `8c2637b`). The introduction of Appendix A and item 7c state the two values and the size of the effect, 1.7 %. If the pin is released, one value should be used in both items and item 7c dropped.

**The notes on the Lean library, checked again at commit `8c2637b` (2026-11-10).** The library moved from commit `2bf6f81` to `8c2637b` after the notes of 2026-11-09 were written. Each of those notes was compared with the sources at `8c2637b`. The declarations it names were printed with `#check` from the build products of the checkout, by scratch files compiled with `lake env lean`; the project was not rebuilt. The hypothesis names quoted in §4.1 and §4.4 were checked by applying the lemmas with named arguments; that `Design.Admissible.atSupply` has no argument `hN'` (Appendix B note) was checked by an application that fails. Where a note named "commit `2bf6f81`", it now names "commit `8c2637b`". Of the declarations these notes named, only `IsTrajectory.of_charge_balance` has a different statement at `8c2637b` (statement texts compared between the two commits).

| Note | What was checked at `8c2637b` | Change besides the commit |
| --- | --- | --- |
| §3.2 | The six `*_rev_*` lemmas are in `VoltageToBit/Model/Device.lean`. `git log -S` gives `499cb39` as the commit that introduced them and this document; they are absent at `fe9f401`. | None. The note names no commit of the library head. |
| §4.1 | The statement of `IsTrajectory.of_charge_balance`, hypothesis by hypothesis; `slew_bound_of_rderiv`; `Examples.uStepR_hasDerivWithinAt_zero`, `Examples.uStepR_not_continuousOn`. `IsTrajectory.of_feedthrough`, which existed at `2bf6f81`, is gone, so "two further lemmas" is now exact for that file. | Rewritten (issue 2 above). |
| §4.4 | `hU` of `IsTrajectory.of_static_sandwich`; `hucont`, `hu`, `hSu` of `IsTrajectory.of_charge_balance`; `IsTrajectory.safe`, `rise`, `fall` and `decoded` take any `u`. | Continuity of the input is named as a hypothesis beside the bound on its right derivative. One sentence says that the lemma asks for a right derivative at every instant, which the Lipschitz condition of the table does not. |
| §5.1 | The statement of `IsTrajectory.of_static_sandwich`. | None. |
| §6.3; Appendix B; IP-2 | `Design.Admissible.atSupply` (hypotheses: admissibility, and `V0` in the supply range), `Design.Admissible.RhiN_atSupply`, the fields `Vtn_nonneg` and `Vtp_nonneg`, `trajectory_safe_atSupply`, `solution_safe_atSupply`, `Examples.illustrative_safe_atSupply`. `RhiN'` occurs in the library only in the header prose of `Proofs/AtSupply.lean`; `git log -S` gives `d420a20` as the commit that removed the declaration. The scratch file of Appendix B was compiled against the library. | Appendix B: "It was not checked again" is replaced by the result of the compilation, one error for the two missing fields. |
| §1 item 6; §7.4 "Explicit run" | The statements of `Examples.illustrative_scenario` and `Examples.illustrative_feedthrough_scenario`; the definitions `Examples.uRamp`, `Examples.wSin`, `Examples.uFeed`, `Examples.gFeed`; the capacitances, the residual and the budget arithmetic. | None. |
| §7.4 "Two stages" | `Examples.illustrative_max_rise_slew` and `Examples.illustrative_max_fall_slew` give 28.5508 and 58.3144 V/ns as the slopes of `IsTrajectory.rise_at_most` and `IsTrajectory.fall_at_most` for the two input ranges, for a trajectory that starts in the safe domain; the statements of `Examples.valid_low_rise_slew_unbounded` and `Examples.valid_high_fall_slew_unbounded`. | None. |
| §10.1 | `Design.tauUp`, `Design.tauDn`; 3.43 and 2.57 ns in `Examples.illustrative_guarantee`; 2.26 and 1.425 ns in `Examples.illustrative_guarantee_refined`; 2.168 and 1.0234 ns in the two counterexample statements. | Added: `Examples.rise_deadline_bracket` and `Examples.fall_deadline_bracket`, whose ends are 2.168 / 2.26 ns and 1.0234 / 1.425 ns at `8c2637b` (they were 2.16 / 2.34 and 1.0 / 1.51 at `2bf6f81`, in a file the root did not import), and the sentence that the library has no statement between the ends. |

The two references to the register "at commit `2bf6f81`" (§6.5 and its row above) are unchanged. `docs/assumptions.md` is the same file at `8c2637b`; the rows that §6.5 names (`PHY-03`, `PHY-06`, `ENV-10`, `ENV-12`, `PHY-09`) were read there. The register was being rewritten when this was checked, so these references have to be checked again against the rewritten register.

Name check on 2026-11-10: every inline code span of the prose (1085 spans) was split into identifier tokens (440 distinct tokens). Each token was checked against the build products at commit `8c2637b` in two ways, both compiled with `lake env lean`: a generated file with one `#check` line per token, and a metaprogram that lists the project constants whose name ends with the token. 91 tokens end the name of a declaration of the project, and 4 name constants of Lean or Mathlib (the three standard axioms and the lemma of §4.3). Tokens that are meant as Lean names and do not resolve are of three kinds. The first kind is declarations of the scratch file of Appendix B, marked as such in the text: `RhiN'`, `Design.RhiN'`, `illustrative_RhiN'`, `Examples.illustrative_RhiN'`, `Examples.illustrative_atSupply`, `Examples.illustrative_atSupply_safe`. The second kind is one declaration that the library had at `2bf6f81` and no longer has, named only in the table above: `IsTrajectory.of_feedthrough`. The third kind is hypothesis names, which are not constants: `hN'` of the scratch file, `hU`, and the sixteen names of the table in §4.1, of which `hu` is also the premise named in §4.4. The tokens that do not resolve were also compared with every declaration and field name that the library had at any of its 38 commits: apart from the names just listed, and field names written after the record variable `D`, none of them is a former name. The other tokens that do not resolve are symbols of the prose, variables of quoted Lean expressions, the pattern `*_rev_*` for the six reverse lemmas, SPICE and PDK names, file names, addresses and commit ids. The names inside the code blocks were not changed.

**Corrections after the third verification round (2026-11-10).** The verdict is recorded in `evidence/verification/round3.json`, entry `docs`: passed, with five minor issues. Issues 2, 3 and 5 are located in this file, issue 4 in this file and in `docs/source-audit.md`, and issue 1 in `docs/source-audit.md` only. The number of each issue is given in the first column. Each issue was checked again before the text was changed: for issue 2 the statement of `IsTrajectory.of_charge_balance` and the definition of `Examples.uStepR` were read at commit `8c2637b`; for issue 3 the three device-details tables at `7198cf64…` (§9.2) were read in the copies saved for the earlier rounds; for issue 4 the header and §0 were compared with the text before the second round; for issue 5 the scratch files of the second round and their recorded output were read. Nothing was compiled for these changes. Each line below is one change.

| Where | What was wrong | What it says now |
| --- | --- | --- |
| §4.1, the sentence on inputs with a jump; the row "§4.1 (issue 2)" above (issue 2) | "An input with a jump in `[a, b]` is therefore outside the lemma" holds for a jump at an instant of `(a, b)`, not for a jump at an end. The hypothesis `hucont` is continuity on `[a, b]`, and an input that jumps at `a` and takes its new value there meets it: `Examples.uStepR` jumps at `t = 4` and is constant on `[4, 10]`. | "An input that is not continuous on `[a, b]` is therefore outside the lemma; that includes every input with a jump at an instant of `(a, b)`." The row above describes the note in the same terms. |
| This section, paragraph "Corrections after the second verification round" (issue 3) | "0.678 to 0.963 V (high-threshold PMOS)" mixed two kinds of column of the device-details table. The model-corner columns, which §10.2 quotes, reach 0.962 V (corner SF at W/L = 7/0.15); 0.963 V is in the EDR column MIN. | "0.678 to 0.962 V (high-threshold PMOS; the EDR columns reach 0.963 V)". The NMOS and standard-PMOS ranges are the same with or without the EDR columns. §10.2 (0.68 to 0.96 V) is unchanged. |
| This section, table of the second round (issue 4) | The header and §0, last paragraph, were changed in the second round to name the corrections of 2026-11-10. That change was not a row of the table, although the header says that every change is listed in this section. | A last row, "Header; §0, last paragraph", records it. |
| Header; §0, last paragraph | Both named the corrections of 2026-11-09 and those after the second verification round only. | Both also name the third verification round. |
| This section, paragraph "The notes on the Lean library, checked again at commit `8c2637b`" (issue 5) | "The hypothesis names quoted in §4.1, §4.4 and §6.3 were checked by applying the lemmas with named arguments": §6.3 quotes no hypothesis name. The name `hN'` is quoted in the note of Appendix B, and the library lemma has no argument of that name, so its check is an application that fails. | §4.1 and §4.4 only, and a second clause: that `Design.Admissible.atSupply` has no argument `hN'` was checked by an application that fails. |
| §7.4 "Two stages" (noticed while applying the round-3 issues; finding R3-09 of the review of the integrated library) | The figures 28.6 and 58.3 V/ns read as a bound on the size of the slew, and `C_M` below 0.03 to 0.07 fF as its consequence; each figure is for one direction and one input range. | A dated note gives the other direction (about 32.3 and 65.1 V/ns), the size bound of about 65 V/ns and the limit of about 0.03 fF, as the header of `Proofs/Chain.lean` does since `fb8bc31`. The bullets themselves are B's text and are kept. |

The name check of 2026-11-10 above was made on the text before these changes, and its counts are those of that text. These changes add 26 inline code spans. Each of their tokens is one that the check covered, except three parts of the two file names in the introduction to this table, which are not Lean names.

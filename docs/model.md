# Circuit model and physical interpretation

Workstream B. Prepared 2026-11-09. This file analyses the draft model and proposes changes to it.
It does not change the shared interface; the coordinator owns `docs/interface.md`.

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
The last section, "Interface proposals", lists every proposed change.

## 1. Findings in brief

1. **The draft arithmetic is right.** `I_up = 10.476 µA`, `I_dn = 16.296 µA`, `τ_up = 3.42 ns`, `τ_dn = 2.56 ns` reproduce exactly [D], and Lean proves the same values [L]. The boundary figures "2.3 to 3.1 µA" are the four split bounds of the proof (`RhiN = 2.312`, `RhiP = 2.4`, `RloN = 3.04`, `RloP = 3.136`) [L]. The true minima of the restoring current are larger: 5.92 µA at the bottom and 6.44 µA at the top [D].
2. **The device law is SPICE MOS Level 1 with `LAMBDA = 0` and `GAMMA = 0`, exactly,** including reverse conduction by source/drain exchange (§3.2).
3. **The bridge from the model to a real device was unusable in its first form and is repaired in the current one.** At commit `1880a36`, `IsTrajectory.of_model_error` asked for one fixed `θ` whose square law is within `ε_m ≤ ε_I = 2 µA` of the true current on the whole safe domain. A 0.15 µm transistor cannot meet that: the expected mismatch is tens of microamps (§5.2). Since commit `eae25ed` the parameter point is chosen per instant and the obligation is a sandwich between two box members (`IsTrajectory.of_sandwich`) [L]. B had checked the same change independently. This repairs the formulation. It does not yet give physical coverage: the box must be wide enough to bracket the real device, and the margins must survive that widening (§5.4).
4. **Safe-domain invariance by reverse conduction is sound mathematics that depends on voltage headroom.** The margin is roughly `k · δ · (VDD − V_tn − V_tp)`. The illustrative box has 0.42 V of headroom. The documented SKY130 thresholds leave about +0.05 V at the typical corner and between −0.02 and −0.14 V at the slow corner for `VDD = 1.60 V` (§6.4). In that corner a real device supplies less restoring current than the illustrative model, and the invariance condition fails.
5. **The fixed upper bound `V_hi = VDD_max + δ` admits states 0.46 V above the actual supply** when `VDD = VDD_min`. That is outside the documented validity of the SKY130 PMOS model and close to junction conduction. The same design record already implies the tighter bound `v ≤ VDD + δ` for a run at any one supply value: restricting an admissible record to one supply keeps it admissible (§6.3) [L-scratch].
6. **`ε_I = 2 µA` is far below realistic coupling currents.** Gate-drain feedthrough is `C_M · du/dt`. With `C_M` of 0.2 to 1 fF and library-realistic input slews of 5 to 50 V/ns that is 1 to 50 µA (§7). The explicit run in `Examples/Illustrative.lean` uses a 9 V/ns input ramp; with any gate-drain capacitance above 0.22 fF that ramp alone uses the whole 2 µA. In the two-stage corollary the first stage's output may slew at up to 29 to 58 V/ns by the model's own bounds, which leaves room for less than 0.07 fF (§7.4).
7. **`C_min ≤ C ≤ C_max` is a sound abstraction only if `C` means the incremental capacitance `∂Q/∂v`** and every current caused by another node moving is carried in the disturbance (§4.2). The first instance therefore covers an ideal grounded capacitor load, not a switching gate load.
8. **Thermal noise is outside any deterministic envelope.** Its effect on the node is about 0.5 to 0.9 mV rms for 20 to 5 fF (§7.5).
9. **Recommended comparison model:** SkyWater SKY130 BSIM4 (level 54, version 4.5) `nfet_01v8` and `pfet_01v8_hvt`, pinned as in §9.
10. **The illustrative record should stay labelled illustrative.** Its thresholds are 0.2 to 0.35 V below SKY130's documented short-channel thresholds, and its `VDD_max = 1.98 V` is above the 1.95 V limit of the SKY130 model documentation (§10).

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

**Parameter map.**

| Model | ngspice Level 1 | Source |
| --- | --- | --- |
| `k_n`, `k_p` | `KP · W / (L − 2·LD) · M` of the respective card | [S, NGSRC] |
| `V_tn` | `VTO` of the NMOS card, positive | [S, NGM §7.6.2.5] |
| `V_tp` | `−VTO` of the PMOS card | [S, NGM §7.6.2.5] |
| no channel-length modulation | `LAMBDA = 0`, the default | [S, NGM parameter table] |
| no body effect | `GAMMA = 0`, the default; `PHI` then has no effect | [S, NGM parameter table] |

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
| Junction diodes | Reverse leakage; forward conduction beyond a rail. | Forward conduction restores the node. Safe for invariance, but it injects carriers (§6.2). | Below 1e-3 µA up to 0.3 V at 27 °C; microamps near 0.5 to 0.6 V; microamps from about 0.3 to 0.4 V at 100 °C [D, with M inputs]. |
| Junction, overlap and channel capacitances | Charge storage on the node and coupling to other nodes. | Enter `C` and the disturbance (§4, §7). | 1 to 2 fF of self-loading for the SKY130 `inv_1` [D from S]. |
| Non-quasi-static effects | Channel charge needs a transit time to rearrange. | Adds state. | Transit time about `L²/(μ·V_ov)` ≈ 1 ps [D]. Negligible for edges slower than 10 ps. |
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

`v` is then an `IsTrajectory` exactly when, while `v` is in the safe domain:

1. `c(t) ∈ [C_min, C_max]`, and
2. `|w(t) + (i_p − i_n) − I_net(θ)(u, v)| ≤ ε_I` for some `θ` in the box, which may differ from instant to instant.

Lean states this as `IsTrajectory.of_ode`, `of_ode_varying`, `of_model_error` and `of_sandwich` [L].
Those theorems state the obligation. They are not evidence that a physical node meets it.

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
| Oxide capacitance | 8.33 and 8.16 fF/µm² | [D] from `toxe` = 4.148 and 4.23 nm [S, SKY-PR] |
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

Before that commit `θ` was one point per run, and the obligation was closeness to one square law, within `ε_m`, on the whole safe domain.
§5.2 records why that could not work. The same arithmetic tells D what a fitted box has to look like.

### 5.2 Why one square law plus 2 µA cannot describe a real device

The on-currents of the illustrative devices are 40 to 280 µA over the box. A model-form error of a few percent already exceeds `ε_I`.

- **Shape of the saturation curve.** For a saturation current proportional to overdrive to the power 1.2 to 1.5, the best uniform square-law fit over the overdrive range misses by 2.4 to 4.9 % of the on-current. At 150 to 300 µA that is 3.5 to 15 µA. The best-fit threshold is also 0.16 to 0.30 V below the true one, so the fitted law conducts where the device is off [D, Appendix A item 4]. This is a statement about two formulas, not about SKY130.
- **Linear region against saturation.** For the SKY130 pair the low-field value `u0 · C_ox · W/L` is about 1150 µA/V² (N) and 660 µA/V² (P) [D from S; `u0` and `toxe` are from the long/wide bin]. The value that reproduces the documented saturation current is about 540 and 320 µA/V² [D from S, assuming the e-test current is taken at 1.8 V on gate and drain]. One `k` cannot serve both regions. The mismatch in the linear region at full gate drive is tens to hundreds of microamps.
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
Appendix A checks the formula against brute force.

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
| Drain-bulk junction forward conduction | Restoring. | Negligible to about 0.3 V at 27 °C. Microamps near 0.5 to 0.6 V. Microamps from 0.3 to 0.4 V at 100 °C [D, with M inputs]. | No |
| Minority-carrier injection and latch-up | Catastrophic. A parasitic thyristor can short the rails. | Needs injected currents of the order of the standard test level, about 100 mA at a pin [M; JESD78 not read]. A femtofarad node holds femtocoulombs. | No. Excluded by assumption. |
| Oxide over-voltage | Reliability, not function. | Gate-to-channel voltage up to 2.18 V in the fixed domain, against a 1.95 V model limit [S, SKY-DD]. | No |
| Gate-induced drain leakage | Small current to bulk. | High gate-drain voltage | No |

### 6.3 Over what excursion is the symmetric law credible?

- **Documented model validity** [S, SKY-DD]. `nfet_01v8`: drain-source and gate-source 0 to 1.95 V, bulk-source +0.3 to −1.95 V. `pfet_01v8` and `pfet_01v8_hvt`: 0 to −1.95 V, bulk-source −0.1 to +1.95 V. Read as forward body bias limits, these allow 0.3 V below ground and 0.1 V above the supply. Mapping reverse operation onto these ranges is B's interpretation, not a statement of the PDK.
- **Interface standard** [S, JEITA]. The 1.8 V standard specifies inputs from −0.3 V to `VDD + 0.3 V` in normal operation and −0.5 V to `VDD + 0.5 V` as absolute maximum. The JEITA text says its specifications correspond to JEDEC JESD8-7.
- **Recommendation.** `δ = 0.1 V` measured from the actual rails is defensible on both sides. `δ` up to 0.3 V is defensible on the ground side only.

**The fixed top is the problem.** `V_hi = VDD_max + δ = 2.08 V` does not depend on `θ`.
For `VDD = 1.62 V` the safe domain admits `v` up to 0.46 V above the supply.
That is beyond the PMOS model's documented range, and at 100 °C it is in the region where B estimates junction currents comparable to the channel currents.
`IsTrajectory.of_sandwich` also demands its bracketing on that whole region, which makes the physical hypothesis harder than it needs to be.

**A supply-relative bound is already implied** [L-scratch, Appendix B].
For an admissible record `D` and a supply value `V0` in its range, let `D.atSupply V0` be `D` with the supply range collapsed to `V0` and the top of the safe domain set to `V0 + (V_hi − VDD_max)`.
If `ε_I < RhiN'`, then `D.atSupply V0` is admissible (`Design.Admissible.atSupply`).
`RhiN'` is `RhiN` with `V_hi` replaced by `VDD_min + (V_hi − VDD_max)`. For the illustrative record `RhiN' = RhiN = 2.312` (`Examples.illustrative_RhiN'`).

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

   With thresholds like those in the SKY130 device table and `k` values that reproduce the documented saturation currents, the square-law valley is [D, Appendix A item 6]:

   | Thresholds `V_tn`, `V_tp` (V) | `VDD` | `H` | Valley, `δ = 0.1` | Valley, `δ = 0.3` |
   | --- | --- | --- | --- | --- |
   | 0.645, 0.888 (TT, W = 7 µm) | 1.60 | +0.067 | 2.82 µA | 13.6 µA |
   | 0.738, 0.819 (TT, W = 0.42 µm) | 1.60 | +0.043 | 2.07 µA | 11.9 µA |
   | 0.677, 0.940 (SS, W = 7 µm) | 1.60 | −0.017 | 0.61 µA | 7.15 µA |
   | 0.818, 0.918 (SS, W = 0.42 µm) | 1.60 | −0.136 | 0.00 µA | 2.40 µA |
   | 0.645, 0.888 (TT, W = 7 µm) | 1.80 | +0.267 | 12.6 / 9.3 µA | 32.5 / 31.8 µA |
   | 0.818, 0.918 (SS, W = 0.42 µm) | 1.80 | +0.064 | 2.40 µA | 11.8 µA |

   Where two values are given they are bottom and top.
   Thresholds are the model-corner columns for `L = 0.15 µm` [S, SKY-DD]. The cell's widths, 0.65 and 1.0 µm, lie between the tabulated ones.
   The page does not state how the thresholds are extracted or at what bias the currents are measured. The `k` values (539 and 324 µA/V² typical, 519 and 272 slow) assume 1.8 V on gate and drain and linear scaling with width.

   Reading: at 1.60 V and the slow corner the square-law lower envelope has a dead zone. With `δ = 0.1 V` its restoring current is between 0 and 0.6 µA, below `ε_I = 2 µA`. At the typical corner it is 2 to 3 µA, which is marginal.

2. **`k` taken from a low-field fit.** If `k` comes from the linear region, the model overstates saturation current by the bulk-charge factor and by velocity saturation, roughly a factor of two for these devices (§5.2). The pull-up and pull-down margins would then be optimistic.

3. **Cold.** Thresholds rise at low temperature [M]. A box fitted at 27 °C understates them at −40 °C, which shrinks `H`.

4. **Hot.** Mobility falls at high temperature [M]. A box fitted at 27 °C overstates `k`.

5. **Ageing.** Negative-bias temperature instability raises the PMOS threshold magnitude over life [M].

6. **Supply impedance.** In the valley part of the restoring current comes through the PMOS from the supply. The model assumes an ideal rail.

B found no mechanism that reduces reverse channel conduction below the square law when thresholds and `k` are matched in forward saturation. The effects listed in §6.2 all add current. That is a physical argument, not evidence.

### 6.5 What must be recorded as assumptions

See `docs/assumptions.md`: `PHY-03` (headroom for the real device), `PHY-06` (reverse conduction at least the lower envelope, no latch-up), `ENV-10` (temperature), `ENV-12` (excursion limits), `PHY-09` (validity range of the comparison model).

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

**Two stages.** `Proofs/Chain.lean` composes two stages [L].
Its header already says that the second stage's gate capacitance and its feedback onto the first node are covered only if the first stage's bounds contain them.
The same holds in the forward direction, and there the model itself fixes the number.

- The first stage's output is the second stage's input.
- `rise_at_most` and `fall_at_most` bound its slew by `(IchargeMax + ε_I)/C_min` and `(IdischargeMax + ε_I)/C_min` [L].
- For the illustrative record with valid inputs these bounds are 28.6 V/ns rising and 58.3 V/ns falling [D]. The fast corner at `C_min` comes within a few percent of them.
- A second stage with gate-drain capacitance `C_M` then sees a feedthrough current of up to `28.6·C_M` to `58.3·C_M` µA.
- That stays inside 2 µA only for `C_M` below 0.03 to 0.07 fF. The estimate for a small inverter is 0.2 to 1 fF.

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
| FreePDK45 | PTM-based 45 nm [search] | Apache-2.0 with a click-through [search] | 1.1 V and strongly velocity-saturated. A poor match for a Level 1 comparison. |
| IHP SG13G2 | PSP 103.6 through OpenVAF [S, NGAPP] | Apache-2.0 [M] | Needs a Verilog-A compile step. Not for the first comparison. |

### 9.2 Provenance to pin

| Item | Value |
| --- | --- |
| Maintained source | `https://github.com/fossi-foundation/skywater-pdk-libs-sky130_fd_pr`, Apache-2.0 [S] |
| Commit to pin | `403964dc7f9cca5ec1a8cc7b4f2a6f532b781676` (2026-01-12). This is the reference recorded by open_pdks 1.0.617 [S, OPDK]. |
| Head when read | `29b55153fd9f4badef05a02667184b81789d1f61` (2026-11-03). The two most recent changes rework Monte Carlo parameters, so the files are still moving [S]. |
| Original release | `https://github.com/google/skywater-pdk-libs-sky130_fd_pr` at `f62031a1be9aefe902d6d54cddd6f59b57627436` (2020-11-10), archived read-only on 2025-05-13 [S]. The values quoted in this document were read here. |
| Standard cell | `https://github.com/google/skywater-pdk-libs-sky130_fd_sc_hd` at `ac7fb61f06e6470b94e8afdf7c25268f62fbd7b1`, archived 2024-04-25 [S] |
| Documentation | `https://github.com/google/skywater-pdk` at `7198cf647113f56041e02abf3eb623692820c5e1` [S] |
| Installer | open_pdks `c6df28c1fccb05c286aa0a15e9c4c7dcd8502607`, version 1.0.617, Apache-2.0 [S] |
| Simulator | ngspice. The release manual listed on 2026-11-09 is version 47 [S]. It implements BSIM4 4.5.0 under level 54 [S, NGM §7.6.3.4]. D must record the version it installs. |

D should record the SHA-256 of every model file actually loaded. A commit hash of a repository is not a hash of the bytes the simulator read.

### 9.3 Files and settings

- Entry point: `models/sky130.lib.spice`, sections `tt`, `ss`, `ff`, `sf`, `fs` and further corners [S, SKY-PR-F]. The `tt` section includes `corners/tt.spice` and two resistor-capacitor files.
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

### 10.2 Critique of the illustrative numbers

| Item | Value | Comment |
| --- | --- | --- |
| Supply | 1.62 to 1.98 V | ±10 % of 1.8 V. The SKY130 model documentation is valid to 1.95 V [S]. The standard-cell timing files cover at least 1.28 to 1.95 V [S, SKY-HD]. The interface standard's normal range is 1.65 to 1.95 V [S, JEITA]. |
| Thresholds | 0.45 to 0.60 V, both devices | Model-corner thresholds at `L = 0.15 µm` are 0.60 to 0.85 V (N), 0.68 to 0.96 V (P, high-threshold), 0.55 to 0.86 V (P, standard) [S, SKY-DD]. The box is 0.2 to 0.35 V lower. This is what makes the headroom comfortable. |
| `k_n`, `k_p` | 160 to 240, 80 to 120 µA/V² | Saturation-fit values for the `inv_1` are about 540 and 320 µA/V² [D from S]. The illustrative devices are two to three times weaker. Same order of magnitude. |
| Temperature | not stated | The box has no temperature. ±20 % on `k` does not cover −40 to 125 °C together with process spread [M]. |
| Capacitance | 5 to 20 fF | Plausible (§4.2). |
| `ε_I` | 2 µA | Consistent only with the quiet, slow-edge environment of Budget A (§7.3). Boundary invariance caps it at 2.31 µA in this record. |
| `δ` | 0.1 V | At the documented PMOS limit. Acceptable relative to the actual supply, not relative to `VDD_max` (§6.3). |
| `V_IL`, `V_IH`, `V_OL`, `V_OH` | 0.40, 1.25, 0.25, 1.35 V | Consistent (§8). `V_IL` is 0.05 V below `V_tn,min`. |
| Largest gate-channel voltage | 2.18 V | Input at −0.1 V with output at 2.08 V. Above the 1.95 V model limit. |

### 10.3 Can a better-justified box be given now?

No. A fitted box needs the device model to be run, and that is D's work.
What can be said from documentation alone:

- A box that covers the documented SKY130 corners would have thresholds up to about 0.85 V and 0.96 V. With `VDD_min = 1.60 V` the headroom is negative, the four boundary conditions of `Design.Admissible` fail for `δ = 0.1 V`, and the record is not admissible (§6.4).
- The pull-up margin survives. With `V_IL = 0.40 V`, `V_OH = 1.35 V`, `VDD = 1.60 V` and the slow-corner numbers of §6.4, the square-law pull-up current is 8 to 11 µA [D]. That is close to the illustrative 10.5 µA by coincidence: the weaker illustrative `k` offsets its lower threshold.
- So the open physical question for a SKY130-anchored instance is the safe domain, not the switching margins.

Options for the coordinator, each a different experiment under the handoff's rules:

| Option | Cost |
| --- | --- |
| Restrict the supply, for example `VDD_min = 1.70 V`, or restrict the corners | A narrower claim |
| Enlarge `δ` to about 0.3 V | Beyond the documented PMOS validity; closer to junction conduction when hot |
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
| NGSRC | ngspice source, `src/spicelib/devices/mos1/mos1load.c`, `mos1temp.c` and `src/spicelib/devices/bsim4v5/b4v5ld.c`. Mirror `https://github.com/imr/ngspice`, branch `master`. | [S], excerpts. Commit not pinned. |
| NGAPP | ngspice applications page. `https://ngspice.sourceforge.io/applic.html` | [S] |
| SKY-DD | SkyWater SKY130 PDK documentation, "Device Details". `https://skywater-pdk.readthedocs.io/en/main/rules/device-details.html`; sources under `docs/rules/device-details/` in `google/skywater-pdk`. | [S]. Tables checked against the repository files. |
| SKY-RCX | Same documentation, parasitic tables 91 and 93 to 95. `https://skywater-pdk.readthedocs.io/en/main/rules/rcx.html` | [S] |
| SKY-PR | `google/skywater-pdk-libs-sky130_fd_pr` at `f62031a1…`: `cells/nfet_01v8/sky130_fd_pr__nfet_01v8__tt.pm3.spice`, `cells/pfet_01v8_hvt/sky130_fd_pr__pfet_01v8_hvt__tt.pm3.spice`. | [S], the first bin of each file only (L 20 to 100 µm, W 7 to 100 µm). |
| SKY-PR-F | `fossi-foundation/skywater-pdk-libs-sky130_fd_pr`: `models/sky130.lib.spice`, `combined_models/README`. | [S] |
| SKY-HD | `google/skywater-pdk-libs-sky130_fd_sc_hd` at `ac7fb61f…`: `cells/inv/sky130_fd_sc_hd__inv_1.spice`, `…__inv_1__tt_025C_1v80.lib.json`, `…__inv_1__ff_100C_1v95.lib.json`, `timing/sky130_fd_sc_hd__common.lib.json`. | [S] |
| OPDK | open_pdks. `https://github.com/RTimothyEdwards/open_pdks`: `VERSION`, `sky130/sky130.json`, `sky130/Makefile.in`. | [S] |
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
| FPDK45 | FreePDK45. `https://eda.ncsu.edu/freepdk/freepdk45/` | [search] |
| MATHLIB | Mathlib at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Mathlib/Analysis/Calculus/MeanValue.lean` | [S], local copy |

## Appendix A. Reproduction script

Requires Python with numpy and scipy. Units are V, µA, fF, ns.
It reproduces every [D] number that is not a one-line calculation.
SHA-256 of the code block below, taken over the text between the fences: `9a9f48f30c6e44b545f42a31767f06d93973b70416a6904bf7ef5167c69957c0`.

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

## Appendix B. Scratch Lean check: restricting a record to one supply value

This file imports the generated design record and adds declarations in the project's namespace. It is not in the repository.
It depends only on the `Design`, `InBox` and `Admissible` definitions, so it does not depend on how trajectories are defined.
It is offered for porting. Until the owner of the Lean sources ports and audits it, it is not a project claim.

Check performed: `lake env lean <file>` from the repository root on 2026-11-09 at 16:25, with Lean 4.35.0 and the build products then present. The repository head was `fe9f401`.
Result: no errors. `#print axioms` reported only `propext`, `Classical.choice` and `Quot.sound` for the four declarations listed at the end.
SHA-256 of the code block below, taken over the text between the fences: `9ee8b0f5e1f25a0522b0819780a3906af9b291764dae97b843b18ab0820f1a15`.

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
- **Reason.** The fixed bound admits 0.46 V above the actual supply at `VDD_min`. That is outside the comparison model's documented range and near junction conduction, and the model-error obligation is currently demanded there too (§6.3).
- **Consequence.** One extra numeric condition, `ε_I < RhiN'`, which equals `RhiN` for the illustrative record. No change to the record. The fixed-domain theorem remains true and can stay. The restricted record's deadlines are no larger. The lemma is independent of IP-1.
- **Status.** Ported by the coordinator in commit `1fdf1d9` as `Proofs/AtSupply.lean`. B has not reviewed the port, and an author should not be the only reviewer of this lemma. Still to do: name the supply-relative set as the initial-state set of the physical claim in `docs/interface.md`.

### IP-3. State the environment that gives `ε_I` a physical meaning

- **Change.** Add to the interface, as environment restrictions outside Lean: an input slew bound `S_u`; a bound on gate-drain capacitance `C_M`; a bound on aggressor coupling `Σ C_c·S_a`; a supply slew bound and zero ground bounce; a temperature or temperature range; an input range `[−δ, VDD + δ]`. Add the budget inequality of §7.3 and a budget table to each design record.
- **Reason.** Without them a positive `ε_I` reads as robustness to crosstalk and feedthrough, which at 2 µA it is not (§7).
- **Consequence.** The illustrative record needs Budget A or an equivalent written next to it. The explicit run's 9 V/ns ramp needs either a slower ramp or a note that the node has no gate-drain capacitance. The caveat in `Proofs/Chain.lean` should carry the number of §7.4: the first stage may slew at 29 to 58 V/ns, so the corollary is about ideal one-node stages. No change to any theorem.

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

- **Change.** In `designs/illustrative-1v8.json` or beside it, add: thresholds are 0.2 to 0.35 V below SKY130's documented short-channel thresholds; `VDD_max` and the domain top exceed the SKY130 models' documented 1.95 V; no temperature is implied.
- **Reason.** The record will be compared with SKY130 BSIM4 by D. Without the label a mismatch could be read as a defect of the proof.
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

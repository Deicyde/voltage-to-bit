import VoltageToBit.Model.Device

/-!
# The uncertain inverter: design record, trajectories, decoding

* `Design`: a record of numbers: a parameter box, a capacitance range, a
  disturbance bound, logic thresholds, a safe voltage domain, and two
  auxiliary split points.
* `Design.InBox`: membership of a parameter choice in the box.
* `Design.Iup`, `Design.Idn`, `Design.RhiP`, `Design.RhiN`, `Design.RloN`,
  `Design.RloP`: closed-form worst-corner current margins. They are *numbers
  computed from the record*; the theorems in `Proofs/Margins.lean` show that the
  device law really provides at least these currents.
* `Design.Admissible`: the finite list of numeric conditions a record must
  satisfy. Nothing in it mentions trajectories or the conclusion.
* `IsTrajectory`: the dynamics, as a differential inclusion over capacitance,
  parameter point and current error.
* `decode`: three-valued decoding of a voltage.
-/

namespace VoltageToBit

open Set

/-- A design record. All fields are plain numbers. -/
structure Design where
  /-- supply voltage range -/
  VDDlo : ℝ
  VDDhi : ℝ
  /-- NMOS transconductance range -/
  knlo : ℝ
  knhi : ℝ
  /-- PMOS transconductance range -/
  kplo : ℝ
  kphi : ℝ
  /-- NMOS threshold range -/
  Vtnlo : ℝ
  Vtnhi : ℝ
  /-- PMOS threshold-magnitude range -/
  Vtplo : ℝ
  Vtphi : ℝ
  /-- load capacitance range -/
  Clo : ℝ
  Chi : ℝ
  /-- bound on the unmodelled current into the output node -/
  eps : ℝ
  /-- input is valid-low iff `u ≤ VIL` -/
  VIL : ℝ
  /-- input is valid-high iff `VIH ≤ u` -/
  VIH : ℝ
  /-- output decodes to low iff `v ≤ VOL` -/
  VOL : ℝ
  /-- output decodes to high iff `VOH ≤ v` -/
  VOH : ℝ
  /-- safe voltage domain `[Vlo, Vhi]` for the output node -/
  Vlo : ℝ
  Vhi : ℝ
  /-- input split point used to bound the restoring current at `Vhi` -/
  uHi : ℝ
  /-- input split point used to bound the restoring current at `Vlo` -/
  uLo : ℝ

namespace Design

variable (D : Design)

/-- Membership of a parameter choice in the design's box. -/
structure InBox (θ : Params) : Prop where
  VDD_ge : D.VDDlo ≤ θ.VDD
  VDD_le : θ.VDD ≤ D.VDDhi
  kn_ge : D.knlo ≤ θ.kn
  kn_le : θ.kn ≤ D.knhi
  kp_ge : D.kplo ≤ θ.kp
  kp_le : θ.kp ≤ D.kphi
  Vtn_ge : D.Vtnlo ≤ θ.Vtn
  Vtn_le : θ.Vtn ≤ D.Vtnhi
  Vtp_ge : D.Vtplo ≤ θ.Vtp
  Vtp_le : θ.Vtp ≤ D.Vtphi

/-- The safe voltage domain of the output node. -/
def Safe : Set ℝ := Icc D.Vlo D.Vhi

/-- Worst-corner net pull-up current (weakest PMOS at the lowest supply,
strongest NMOS). It is a lower bound on the net current into the node for
`u ≤ VIL` and `v ≤ c`, provided `c ≤ VDDlo`: that is what `Inet_ge_Iup`
(`Proofs/Margins.lean`) proves, for an admissible record and every parameter
point of the box. Without the proviso the bound fails: a node above the supply
is discharged through the PMOS conducting in reverse. -/
noncomputable def Iup (c : ℝ) : ℝ :=
  D.kplo / 2 * (psq (D.VDDlo - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi))
    - D.knhi / 2 * psq (D.VIL - D.Vtnlo)

/-- Worst-corner net pull-down current (weakest NMOS, strongest PMOS at the
highest supply). It is a lower bound on the net current out of the node for
`VIH ≤ u` and `c ≤ v`, provided `0 ≤ c`: that is what `Inet_le_neg_Idn`
(`Proofs/Margins.lean`) proves, for an admissible record and every parameter
point of the box. Without the proviso the bound fails: a node below ground is
charged through the NMOS conducting in reverse. -/
noncomputable def Idn (c : ℝ) : ℝ :=
  D.knlo / 2 * (psq (D.VIH - D.Vtnhi) - psq (D.VIH - c - D.Vtnhi))
    - D.kphi / 2 * psq (D.VDDhi - D.VIH - D.Vtplo)

/-- Restoring current at `v = Vhi` from PMOS reverse conduction, for `u ≤ uHi`. -/
noncomputable def RhiP : ℝ :=
  D.kplo / 2 * (psq (D.VDDlo - D.uHi - D.Vtphi + (D.Vhi - D.VDDhi))
    - psq (D.VDDlo - D.uHi - D.Vtphi))

/-- Restoring current at `v = Vhi` from the NMOS, for `uHi ≤ u`. -/
noncomputable def RhiN : ℝ :=
  D.knlo / 2 * (psq (D.uHi - D.Vtnhi) - psq (D.uHi - D.Vhi - D.Vtnhi))

/-- Restoring current at `v = Vlo` from NMOS reverse conduction, for `uLo ≤ u`. -/
noncomputable def RloN : ℝ :=
  D.knlo / 2 * (psq (D.uLo - D.Vlo - D.Vtnhi) - psq (D.uLo - D.Vtnhi))

/-- Restoring current at `v = Vlo` from the PMOS, for `u ≤ uLo`. -/
noncomputable def RloP : ℝ :=
  D.kplo / 2 * (psq (D.VDDlo - D.uLo - D.Vtphi) - psq (D.Vlo - D.uLo - D.Vtphi))

/-- Deadline for the output to become valid-high after the input becomes valid-low.

Meaningful only for an admissible record. The formula returns a number for
every record: outside admissibility it can be negative (pull-up margin below
the disturbance bound, `Iup VOH < eps`) or, through Lean's convention
`x / 0 = 0`, zero (`Iup VOH = eps`). The theorems that use it as a deadline
(`IsTrajectory.rise` and its consequences) all assume `Admissible`. Any tool
that compares or ranks records by this number must check admissibility first. -/
noncomputable def tauUp : ℝ := D.Chi * (D.VOH - D.Vlo) / (D.Iup D.VOH - D.eps)

/-- Deadline for the output to become valid-low after the input becomes valid-high.

Meaningful only for an admissible record. The formula returns a number for
every record: outside admissibility it can be negative (pull-down margin below
the disturbance bound, `Idn VOL < eps`) or, through Lean's convention
`x / 0 = 0`, zero (`Idn VOL = eps`). The theorems that use it as a deadline
(`IsTrajectory.fall` and its consequences) all assume `Admissible`. Any tool
that compares or ranks records by this number must check admissibility first. -/
noncomputable def tauDn : ℝ := D.Chi * (D.Vhi - D.VOL) / (D.Idn D.VOL - D.eps)

/-- The numeric conditions a design record must satisfy. Every field is an
inequality between numbers computed from the record. -/
structure Admissible : Prop where
  VDD_pos : 0 < D.VDDlo
  VDD_le : D.VDDlo ≤ D.VDDhi
  kn_pos : 0 < D.knlo
  kn_le : D.knlo ≤ D.knhi
  kp_pos : 0 < D.kplo
  kp_le : D.kplo ≤ D.kphi
  Vtn_le : D.Vtnlo ≤ D.Vtnhi
  Vtp_le : D.Vtplo ≤ D.Vtphi
  /-- the NMOS threshold is nonnegative for every parameter point of the box -/
  Vtn_nonneg : 0 ≤ D.Vtnlo
  /-- the PMOS threshold magnitude is nonnegative for every parameter point of the box -/
  Vtp_nonneg : 0 ≤ D.Vtplo
  C_pos : 0 < D.Clo
  C_le : D.Clo ≤ D.Chi
  eps_nonneg : 0 ≤ D.eps
  /-- the safe domain extends to or below ground -/
  Vlo_le : D.Vlo ≤ 0
  /-- the safe domain extends to or above the highest supply -/
  Vhi_ge : D.VDDhi ≤ D.Vhi
  VOL_nonneg : 0 ≤ D.VOL
  /-- static discipline: `VOL ≤ VIL < VIH ≤ VOH` -/
  VOL_le_VIL : D.VOL ≤ D.VIL
  VIL_lt_VIH : D.VIL < D.VIH
  VIH_le_VOH : D.VIH ≤ D.VOH
  VOH_le : D.VOH ≤ D.VDDlo
  /-- pull-up margin exceeds the disturbance bound -/
  up : D.eps < D.Iup D.VOH
  /-- pull-down margin exceeds the disturbance bound -/
  dn : D.eps < D.Idn D.VOL
  /-- boundary restoring currents exceed the disturbance bound -/
  hiP : D.eps < D.RhiP
  hiN : D.eps < D.RhiN
  loN : D.eps < D.RloN
  loP : D.eps < D.RloP

end Design

/-- **Dynamics.** `v` is a trajectory of the uncertain inverter on `[a, b]`
for input `u` when it is continuous on `[a, b]` and, at each `t ∈ [a, b)`, has a
right derivative `v'` such that, for some capacitance value `c ∈ [Clo, Chi]`
and some parameter point `θ` of the box, the current balance
`c * v' = Inet θ (u t) (v t)` holds up to an error of at most `eps`.

The capacitance value and the parameter point may be different at every
instant. So the definition covers a supply that moves within its range, device
parameters that drift within theirs, and any device whose current, at each
operating point, lies between the currents of two square-law devices of the
box (see `Proofs/ModelError.lean`). A run with constant parameters is the
special case of a constant choice (`IsTrajectory.of_ode`).

The current balance is only required while `v t` is in the safe domain. This
makes the hypothesis weaker (the theorem stronger): a model that is only known
to be accurate on the safe domain is still covered.

This is a differential inclusion. It contains every solution of
`C (v) * dv/dt = Inet θ u v + w t` with `Clo ≤ C ≤ Chi`, `θ` in the box and
`|w| ≤ eps` that has a right derivative at every instant. -/
structure IsTrajectory (D : Design) (u v : ℝ → ℝ) (a b : ℝ) : Prop where
  cont : ContinuousOn v (Icc a b)
  incl : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
    D.Clo ≤ c ∧ c ≤ D.Chi ∧
    (v t ∈ D.Safe → ∃ θ : Params, D.InBox θ ∧ |c * v' - Inet θ (u t) (v t)| ≤ D.eps)

/-! ## Decoding -/

/-- Three-valued decoding of a voltage `x` against a low threshold `lo` and a
high threshold `hi`: `some false` at or below `lo`, `some true` at or above
`hi`, and `none` (undefined) strictly in between.

Meaningful only for ordered thresholds, `lo < hi`, which admissibility provides
for the thresholds of a design record. The definition accepts any two numbers:
with `hi ≤ lo` (inverted or equal thresholds) there is no undefined band and
every voltage decodes to a bit (`decode_eq_none_iff`). Any tool that compares
or ranks records by decoded values must check admissibility first. -/
noncomputable def decode (lo hi x : ℝ) : Option Bool :=
  if x ≤ lo then some false else if hi ≤ x then some true else none

theorem decode_eq_false_iff {lo hi x : ℝ} :
    decode lo hi x = some false ↔ x ≤ lo := by
  unfold decode
  split_ifs with h1 h2 <;> simp_all

theorem decode_eq_true_iff {lo hi x : ℝ} (h : lo < hi) :
    decode lo hi x = some true ↔ hi ≤ x := by
  unfold decode
  split_ifs with h1 h2
  · simp only [Option.some.injEq, Bool.false_eq_true, false_iff, not_le]
    linarith
  · simp [h2]
  · simp [h2]

theorem decode_eq_none_iff {lo hi x : ℝ} :
    decode lo hi x = none ↔ lo < x ∧ x < hi := by
  unfold decode
  split_ifs with h1 h2
  · simp only [false_iff, not_and, not_lt]
    intro h; linarith
  · simp only [false_iff, not_and, not_lt]
    intro _; exact h2
  · simp only [true_iff]
    exact ⟨not_le.mp h1, not_le.mp h2⟩

namespace Design

variable (D : Design)

/-- Decoding of the input voltage.

Meaningful only for an admissible record, where `VIL < VIH`. For a record with
`VIH ≤ VIL` the decoder has no undefined band (see `decode`). -/
noncomputable def decodeIn (x : ℝ) : Option Bool := decode D.VIL D.VIH x

/-- Decoding of the output voltage.

Meaningful only for an admissible record, where `VOL < VOH`. For a record with
`VOH ≤ VOL` the decoder has no undefined band (see `decode`). -/
noncomputable def decodeOut (x : ℝ) : Option Bool := decode D.VOL D.VOH x

/-- Deadline for an input bit: a low input drives the output high (`tauUp`),
a high input drives the output low (`tauDn`).

Meaningful only for an admissible record: outside admissibility `tauUp` and
`tauDn` can be negative or zero (see their doc comments), and any tool that
compares or ranks records by a deadline must check admissibility first. -/
noncomputable def tau (inBit : Bool) : ℝ := if inBit then D.tauDn else D.tauUp

end Design

end VoltageToBit

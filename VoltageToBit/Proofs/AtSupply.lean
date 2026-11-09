import VoltageToBit.Proofs.Existence

/-!
# The safe domain measured from the actual supply

The safe domain of a design record is one fixed interval `[Vlo, Vhi]` with
`Vhi` above the *highest* supply of the box. For a run at a lower supply value
`V0` that interval reaches far above the rail (0.46 V above it at the lowest
supply of the illustrative record), into a region where the square law is
least credible as a description of a real device.

This file shows that, for a run at *one* supply value, nothing is lost by
measuring the top of the domain from that supply: restricting an admissible
record to a single supply value `V0` of its range, with safe domain
`[Vlo, V0 + (Vhi - VDDhi)]`, gives an admissible record again. No condition
beyond admissibility is needed. Every theorem about admissible records then
applies to the restricted record.

* `Design.atSupply`, `Design.Admissible.atSupply`, `Design.InBox.atSupply`:
  the restriction and its admissibility.
* `Design.Admissible.uHi_lt`, `Design.Admissible.RhiN_atSupply`: why no extra
  condition is needed. The margin `hiP` forces the split point `uHi` below
  `VDDlo - Vtphi + (Vhi - VDDhi)`; with nonnegative thresholds
  (`Admissible.Vtn_nonneg`, `Admissible.Vtp_nonneg`) the worst-corner NMOS is
  then saturated, or off, at the top of the domain of the record and of each
  of its restrictions, so the margin `RhiN` is the same number for all of them.
* `trajectory_safe_atSupply`: every trajectory of the restricted record that
  starts in `[Vlo, V0 + (Vhi - VDDhi)]` stays there. The restricted record
  differs from `D` only in its supply range, which is the single value `V0`,
  and in the top of its safe domain; the other parameters may still move
  within their ranges from instant to instant.
* `IsTrajectory.of_ode_atSupply`: a solution of the node equation with constant
  parameters is a trajectory of the record restricted to its own supply.
* `solution_safe_atSupply`: such a solution stays in
  `[Vlo, θ.VDD + (Vhi - VDDhi)]`.

Scope. The supply-relative domain is proved for runs at one supply value: the
supply is the same number `V0` at every instant of the run. The trajectory
notion of the unrestricted record also allows a supply that moves within
`[VDDlo, VDDhi]` in time. For such a run only the fixed domain `[Vlo, Vhi]` is
proved (`IsTrajectory.safe`); nothing here bounds the node by the supply of
the moment. (If the supply drops while the node is near the top of the old
supply-relative interval, the node is above the new one.)

The definitions and the proof of `Admissible.atSupply` were contributed by
workstream B (`docs/model.md`, Appendix B) and ported here by the coordinator.
That version carried an extra hypothesis `eps < RhiN'`, where `RhiN'` was
`RhiN` with the top of the domain taken relative to the lowest supply.
Workstream E showed that it follows from admissibility once the thresholds are
nonnegative (`docs/adversarial-review.md`, E2-02, with the argument in
`review/D04_AtSupply_Chain_Reverse.lean`). The hypothesis and the auxiliary
number were removed when the two sign conditions were added to `Admissible`.
-/

namespace VoltageToBit

open Set

namespace Design

/-- The record restricted to the single supply value `V0`, with the top of the
safe domain the same distance above `V0` as `Vhi` is above `VDDhi`. -/
noncomputable def atSupply (D : Design) (V0 : ℝ) : Design :=
  { D with VDDlo := V0, VDDhi := V0, Vhi := V0 + (D.Vhi - D.VDDhi) }

/-- For an admissible record the split point `uHi` lies below
`VDDlo - Vtphi + (Vhi - VDDhi)`. Otherwise both terms of `RhiP` would vanish
(the PMOS branch would provide no restoring current at the top of the safe
domain), the margin `RhiP` would be zero, and `hiP` would fail. -/
theorem Admissible.uHi_lt {D : Design} (hD : D.Admissible) :
    D.uHi < D.VDDlo - D.Vtphi + (D.Vhi - D.VDDhi) := by
  have hδ : 0 ≤ D.Vhi - D.VDDhi := by linarith [hD.Vhi_ge]
  by_contra hneg
  push Not at hneg
  have h1 := hD.hiP
  unfold Design.RhiP at h1
  rw [psq_of_nonpos (by linarith), psq_of_nonpos (by linarith), sub_self, mul_zero] at h1
  linarith [hD.eps_nonneg]

/-- The NMOS margin at the top of the safe domain is the same number for an
admissible record and for its restriction to any supply value `V0 ≥ VDDlo`.
With nonnegative thresholds the second term of `RhiN` vanishes in both cases
(the worst-corner NMOS is saturated, or off, at the top of either domain), so
both numbers are `knlo / 2 * psq (uHi - Vtnhi)`. This is why
`Admissible.atSupply` needs no condition beyond admissibility. -/
theorem Admissible.RhiN_atSupply {D : Design} (hD : D.Admissible) {V0 : ℝ}
    (h1 : D.VDDlo ≤ V0) : (D.atSupply V0).RhiN = D.RhiN := by
  have hu := hD.uHi_lt
  have hle := hD.VDD_le
  have hn : 0 ≤ D.Vtnhi := le_trans hD.Vtn_nonneg hD.Vtn_le
  have hp : 0 ≤ D.Vtphi := le_trans hD.Vtp_nonneg hD.Vtp_le
  show D.knlo / 2 * (psq (D.uHi - D.Vtnhi)
      - psq (D.uHi - (V0 + (D.Vhi - D.VDDhi)) - D.Vtnhi))
    = D.knlo / 2 * (psq (D.uHi - D.Vtnhi) - psq (D.uHi - D.Vhi - D.Vtnhi))
  rw [psq_of_nonpos (by linarith : D.uHi - (V0 + (D.Vhi - D.VDDhi)) - D.Vtnhi ≤ 0),
    psq_of_nonpos (by linarith : D.uHi - D.Vhi - D.Vtnhi ≤ 0)]

/-- **Supply-relative admissibility.** If `D` is admissible, then for every
supply value `V0` of its range the record with the supply fixed at `V0` and the
safe domain `[Vlo, V0 + (Vhi - VDDhi)]` is admissible too. -/
theorem Admissible.atSupply {D : Design} (hD : D.Admissible) {V0 : ℝ}
    (h1 : D.VDDlo ≤ V0) (h2 : V0 ≤ D.VDDhi) :
    (D.atSupply V0).Admissible := by
  have hkp : 0 ≤ D.kplo / 2 := by linarith [hD.kp_pos]
  have hkph : 0 ≤ D.kphi / 2 := by linarith [hD.kp_pos, hD.kp_le]
  have hδ : 0 ≤ D.Vhi - D.VDDhi := by linarith [hD.Vhi_ge]
  refine
    { VDD_pos := ?_, VDD_le := ?_, kn_pos := hD.kn_pos, kn_le := hD.kn_le,
      kp_pos := hD.kp_pos, kp_le := hD.kp_le, Vtn_le := hD.Vtn_le, Vtp_le := hD.Vtp_le,
      Vtn_nonneg := hD.Vtn_nonneg, Vtp_nonneg := hD.Vtp_nonneg,
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
  · -- top boundary, NMOS branch: the same number as for the record itself
    show D.eps < (D.atSupply V0).RhiN
    rw [hD.RhiN_atSupply h1]
    exact hD.hiN
  · -- bottom boundary, PMOS branch: a higher supply only helps
    show D.eps < D.kplo / 2 * (psq (V0 - D.uLo - D.Vtphi) - psq (D.Vlo - D.uLo - D.Vtphi))
    have hP := hD.loP
    unfold Design.RloP at hP
    have hm : psq (D.VDDlo - D.uLo - D.Vtphi) ≤ psq (V0 - D.uLo - D.Vtphi) :=
      psq_mono (by linarith)
    have := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hm (psq (D.Vlo - D.uLo - D.Vtphi))) hkp
    linarith

/-- A parameter point of the box lies in the box of the record restricted to
its own supply value. -/
theorem InBox.atSupply {D : Design} {θ : Params} (hθ : D.InBox θ) :
    (D.atSupply θ.VDD).InBox θ :=
  { VDD_ge := le_rfl, VDD_le := le_rfl, kn_ge := hθ.kn_ge, kn_le := hθ.kn_le,
    kp_ge := hθ.kp_ge, kp_le := hθ.kp_le, Vtn_ge := hθ.Vtn_ge, Vtn_le := hθ.Vtn_le,
    Vtp_ge := hθ.Vtp_ge, Vtp_le := hθ.Vtp_le }

end Design

/-- **Safe domain measured from the supply, for every trajectory at that
supply.** Let `D` be admissible and `V0` a supply value of its range. Every
trajectory of the restricted record `D.atSupply V0` that starts in
`[Vlo, V0 + (Vhi - VDDhi)]` stays there.

In a trajectory of the restricted record the supply is `V0` at every instant;
the transconductances and thresholds may still be anywhere in their ranges at
each instant, and the capacitance and the current error are as for `D`. For a
supply that moves in time this statement does not apply, and only the fixed
domain `[Vlo, Vhi]` is proved (`IsTrajectory.safe`). -/
theorem trajectory_safe_atSupply {D : Design} (hD : D.Admissible) {V0 : ℝ}
    (h1 : D.VDDlo ≤ V0) (h2 : V0 ≤ D.VDDhi) {u v : ℝ → ℝ} {a b : ℝ}
    (h : IsTrajectory (D.atSupply V0) u v a b)
    (h0 : v a ∈ Icc D.Vlo (V0 + (D.Vhi - D.VDDhi))) :
    ∀ t ∈ Icc a b, v t ∈ Icc D.Vlo (V0 + (D.Vhi - D.VDDhi)) :=
  h.safe (hD.atSupply h1 h2) h0

/-- A solution of the node equation with constant parameters `θ` is a
trajectory of the record restricted to the supply value `θ.VDD`. -/
theorem IsTrajectory.of_ode_atSupply {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}
    {Cf w : ℝ → ℝ} (hθ : D.InBox θ) (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ D.eps) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet θ (u t) (v t) + w t) :
    IsTrajectory (D.atSupply θ.VDD) u v a b :=
  IsTrajectory.of_ode (D := D.atSupply θ.VDD) hθ.atSupply hCf hw hcont hode

/-- **Safe domain measured from the actual supply.** For an admissible record,
a solution of the node equation with constant parameters `θ` that starts in
`[Vlo, θ.VDD + (Vhi - VDDhi)]` stays there. -/
theorem solution_safe_atSupply {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}
    {Cf w : ℝ → ℝ} (hD : D.Admissible) (hθ : D.InBox θ)
    (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ D.eps) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet θ (u t) (v t) + w t)
    (h0 : v a ∈ Icc D.Vlo (θ.VDD + (D.Vhi - D.VDDhi))) :
    ∀ t ∈ Icc a b, v t ∈ Icc D.Vlo (θ.VDD + (D.Vhi - D.VDDhi)) :=
  trajectory_safe_atSupply hD hθ.VDD_ge hθ.VDD_le
    (IsTrajectory.of_ode_atSupply hθ hCf hw hcont hode) h0

end VoltageToBit

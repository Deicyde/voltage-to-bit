import VoltageToBit.Proofs.Existence

/-!
# The safe domain measured from the actual supply

The safe domain of a design record is one fixed interval `[Vlo, Vhi]` with
`Vhi` above the *highest* supply of the box. For a run at a lower supply value
`V0` that interval reaches far above the rail (0.46 V above it at the lowest
supply of the illustrative record), into a region where the square law is
least credible as a description of a real device.

This file shows that nothing is lost by measuring the top of the domain from
the actual supply: restricting an admissible record to a single supply value
`V0`, with safe domain `[Vlo, V0 + (Vhi - VDDhi)]`, gives an admissible record
again, provided one extra numeric condition `eps < RhiN'` holds. Every theorem
about admissible records then applies to the restricted record.

* `Design.atSupply`, `Design.RhiN'`, `Design.Admissible.atSupply`,
  `Design.InBox.atSupply`: the restriction and its admissibility.
* `IsTrajectory.of_ode_atSupply`: a solution of the node equation with constant
  parameters is a trajectory of the record restricted to its own supply.
* `solution_safe_atSupply`: such a solution stays in
  `[Vlo, θ.VDD + (Vhi - VDDhi)]`.

The definitions and the proof of `Admissible.atSupply` were contributed by
workstream B (`docs/model.md`, Appendix B) and ported here by the coordinator.
-/

namespace VoltageToBit

open Set

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
at `V0` and the safe domain `[Vlo, V0 + (Vhi - VDDhi)]` is admissible too. -/
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

/-- A parameter point of the box lies in the box of the record restricted to
its own supply value. -/
theorem InBox.atSupply {D : Design} {θ : Params} (hθ : D.InBox θ) :
    (D.atSupply θ.VDD).InBox θ :=
  { VDD_ge := le_rfl, VDD_le := le_rfl, kn_ge := hθ.kn_ge, kn_le := hθ.kn_le,
    kp_ge := hθ.kp_ge, kp_le := hθ.kp_le, Vtn_ge := hθ.Vtn_ge, Vtn_le := hθ.Vtn_le,
    Vtp_ge := hθ.Vtp_ge, Vtp_le := hθ.Vtp_le }

end Design

/-- A solution of the node equation with constant parameters `θ` is a
trajectory of the record restricted to the supply value `θ.VDD`. -/
theorem IsTrajectory.of_ode_atSupply {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}
    {Cf w : ℝ → ℝ} (hθ : D.InBox θ) (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ D.eps) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet θ (u t) (v t) + w t) :
    IsTrajectory (D.atSupply θ.VDD) u v a b :=
  IsTrajectory.of_ode (D := D.atSupply θ.VDD) hθ.atSupply hCf hw hcont hode

/-- **Safe domain measured from the actual supply.** For an admissible record
with `eps < RhiN'`, a solution of the node equation with constant parameters
`θ` that starts in `[Vlo, θ.VDD + (Vhi - VDDhi)]` stays there. -/
theorem solution_safe_atSupply {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}
    {Cf w : ℝ → ℝ} (hD : D.Admissible) (hN' : D.eps < D.RhiN') (hθ : D.InBox θ)
    (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ D.eps) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet θ (u t) (v t) + w t)
    (h0 : v a ∈ Icc D.Vlo (θ.VDD + (D.Vhi - D.VDDhi))) :
    ∀ t ∈ Icc a b, v t ∈ Icc D.Vlo (θ.VDD + (D.Vhi - D.VDDhi)) :=
  (IsTrajectory.of_ode_atSupply hθ hCf hw hcont hode).safe
    (hD.atSupply hθ.VDD_ge hθ.VDD_le hN') h0

end VoltageToBit

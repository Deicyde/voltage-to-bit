import VoltageToBit.Proofs.Existence

/-!
# Admissible records are not degenerate

The guarantee is a universally quantified implication, so it is worth proving
that its hypotheses can be met and its conclusion is not about an empty window,
**for every admissible record**, not only for one example.

* `Admissible.exists_inBox`: the parameter box is nonempty.
* `Admissible.zero_mem_safe`, `Admissible.VOL_mem_safe`, `Admissible.VOH_mem_safe`:
  the safe domain is nonempty and contains both valid output bands' edges.
* `Admissible.VOL_lt_VOH`: the two valid output bands are disjoint, so decoding
  is unambiguous and the undefined band has positive width.
* `Admissible.tauUp_pos`, `Admissible.tauDn_pos`: the deadlines are positive.
* `Admissible.exists_rise_run`, `Admissible.exists_fall_run`: there is an actual
  trajectory, starting from the *opposite* valid output level, with a valid
  input held for longer than the deadline, on which the conclusion holds over a
  window of positive length.
-/

namespace VoltageToBit

open Set

namespace Design.Admissible

variable {D : Design}

/-- The parameter box of an admissible record is nonempty. -/
theorem exists_inBox (hD : D.Admissible) : ∃ θ : Params, D.InBox θ :=
  ⟨⟨D.VDDlo, D.knlo, D.kplo, D.Vtnlo, D.Vtplo⟩,
    ⟨le_rfl, hD.VDD_le, le_rfl, hD.kn_le, le_rfl, hD.kp_le, le_rfl, hD.Vtn_le, le_rfl,
      hD.Vtp_le⟩⟩

theorem VOL_lt_VOH (hD : D.Admissible) : D.VOL < D.VOH := by
  linarith [hD.VOL_le_VIL, hD.VIL_lt_VIH, hD.VIH_le_VOH]

theorem zero_mem_safe (hD : D.Admissible) : (0 : ℝ) ∈ D.Safe :=
  ⟨hD.Vlo_le, by linarith [hD.VDD_pos, hD.VDD_le, hD.Vhi_ge]⟩

theorem VOL_mem_safe (hD : D.Admissible) : D.VOL ∈ D.Safe :=
  ⟨le_trans hD.Vlo_le hD.VOL_nonneg,
    by linarith [hD.VOL_lt_VOH, hD.VOH_le, hD.VDD_le, hD.Vhi_ge]⟩

theorem VOH_mem_safe (hD : D.Admissible) : D.VOH ∈ D.Safe :=
  ⟨by linarith [hD.Vlo_le, hD.VOL_nonneg, hD.VOL_lt_VOH],
    by linarith [hD.VOH_le, hD.VDD_le, hD.Vhi_ge]⟩

theorem tauUp_pos (hD : D.Admissible) : 0 < D.tauUp := by
  unfold Design.tauUp
  have h1 : 0 < D.Chi := lt_of_lt_of_le hD.C_pos hD.C_le
  have h2 : 0 < D.VOH - D.Vlo := by linarith [hD.VOH_mem_safe.1, hD.Vlo_le, hD.VOL_nonneg,
    hD.VOL_lt_VOH]
  have h3 : 0 < D.Iup D.VOH - D.eps := by linarith [hD.up]
  positivity

theorem tauDn_pos (hD : D.Admissible) : 0 < D.tauDn := by
  unfold Design.tauDn
  have h1 : 0 < D.Chi := lt_of_lt_of_le hD.C_pos hD.C_le
  have h2 : 0 < D.Vhi - D.VOL := by
    linarith [hD.VOL_lt_VOH, hD.VOH_le, hD.VDD_le, hD.Vhi_ge]
  have h3 : 0 < D.Idn D.VOL - D.eps := by linarith [hD.dn]
  positivity

/-- **The rise guarantee is not vacuous.** For every admissible record there is
a parameter choice in the box and a trajectory that starts valid-*low*, sees a
valid-low input for one time unit longer than the deadline, and is valid-high
throughout the final window `[tauUp, tauUp + 1]`. -/
theorem exists_rise_run (hD : D.Admissible) :
    ∃ (θ : Params) (u v : ℝ → ℝ), D.InBox θ ∧ IsTrajectory D θ u v 0 (D.tauUp + 1) ∧
      v 0 = D.VOL ∧ (∀ t, u t ≤ D.VIL) ∧
      ∀ t ∈ Icc D.tauUp (D.tauUp + 1), D.VOH ≤ v t := by
  obtain ⟨θ, hθ⟩ := hD.exists_inBox
  have hT : (0 : ℝ) ≤ D.tauUp + 1 := by linarith [hD.tauUp_pos]
  obtain ⟨v, hv0, htraj⟩ := exists_trajectory_const hD hθ (C := D.Clo) le_rfl hD.C_le
    (u := fun _ => D.VIL) (w := fun _ => 0) continuous_const continuous_const hT
    (fun t _ => by simpa using hD.eps_nonneg) hD.VOL_mem_safe
  refine ⟨θ, fun _ => D.VIL, v, hθ, htraj, hv0, fun _ => le_rfl, fun t ht => ?_⟩
  have h0 : v 0 ∈ D.Safe := by rw [hv0]; exact hD.VOL_mem_safe
  exact htraj.rise hD hθ h0 le_rfl le_rfl (fun _ _ => le_rfl) t
    ⟨by linarith [ht.1, hD.tauUp_pos], ht.2⟩ (by linarith [ht.1])

/-- **The fall guarantee is not vacuous.** Mirror image of `exists_rise_run`:
the trajectory starts valid-*high* and is valid-low throughout
`[tauDn, tauDn + 1]`. -/
theorem exists_fall_run (hD : D.Admissible) :
    ∃ (θ : Params) (u v : ℝ → ℝ), D.InBox θ ∧ IsTrajectory D θ u v 0 (D.tauDn + 1) ∧
      v 0 = D.VOH ∧ (∀ t, D.VIH ≤ u t) ∧
      ∀ t ∈ Icc D.tauDn (D.tauDn + 1), v t ≤ D.VOL := by
  obtain ⟨θ, hθ⟩ := hD.exists_inBox
  have hT : (0 : ℝ) ≤ D.tauDn + 1 := by linarith [hD.tauDn_pos]
  obtain ⟨v, hv0, htraj⟩ := exists_trajectory_const hD hθ (C := D.Clo) le_rfl hD.C_le
    (u := fun _ => D.VIH) (w := fun _ => 0) continuous_const continuous_const hT
    (fun t _ => by simpa using hD.eps_nonneg) hD.VOH_mem_safe
  refine ⟨θ, fun _ => D.VIH, v, hθ, htraj, hv0, fun _ => le_rfl, fun t ht => ?_⟩
  have h0 : v 0 ∈ D.Safe := by rw [hv0]; exact hD.VOH_mem_safe
  exact htraj.fall hD hθ h0 le_rfl le_rfl (fun _ _ => le_rfl) t
    ⟨by linarith [ht.1, hD.tauDn_pos], ht.2⟩ (by linarith [ht.1])

end Design.Admissible

end VoltageToBit

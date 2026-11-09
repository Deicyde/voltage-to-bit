import VoltageToBit.Proofs.Guarantee

/-!
# A minimum delay (contamination bound) for the rising output

The guarantee gives a deadline by which the output is valid. This file gives
the opposite kind of bound: the output cannot rise faster than the largest
available charging current allows. It is used as a negative control: a claimed
deadline shorter than this bound is false for every trajectory.

Only the rising direction is treated.
-/

namespace VoltageToBit

open Set

namespace Design

variable {D : Design} {θ : Params}

/-- An upper bound on the net charging current over the safe domain, for
inputs in `[ulo, uhi]`: strongest PMOS in saturation at the highest supply,
plus the strongest NMOS conducting in reverse at the bottom of the domain. -/
noncomputable def IchargeMax (D : Design) (ulo uhi : ℝ) : ℝ :=
  D.kphi / 2 * psq (D.VDDhi - ulo - D.Vtplo) + D.knhi / 2 * psq (uhi - D.Vlo - D.Vtnlo)

theorem IchargeMax_nonneg (hD : D.Admissible) (ulo uhi : ℝ) : 0 ≤ D.IchargeMax ulo uhi := by
  unfold IchargeMax
  have h1 : 0 ≤ D.kphi := le_trans hD.kp_pos.le hD.kp_le
  have h2 : 0 ≤ D.knhi := le_trans hD.kn_pos.le hD.kn_le
  have := psq_nonneg (D.VDDhi - ulo - D.Vtplo)
  have := psq_nonneg (uhi - D.Vlo - D.Vtnlo)
  positivity

theorem Inet_le_IchargeMax (hD : D.Admissible) (hθ : D.InBox θ) {u v ulo uhi : ℝ}
    (hu1 : ulo ≤ u) (hu2 : u ≤ uhi) (hv : D.Vlo ≤ v) :
    Inet θ u v ≤ D.IchargeMax ulo uhi := by
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  have hP : Ip θ u v ≤ D.kphi / 2 * psq (D.VDDhi - ulo - D.Vtplo) := by
    have h1 := Ip_le_sat (θ := θ) (u := u) (v := v) hkp
    have h2 : psq (θ.VDD - u - θ.Vtp) ≤ psq (D.VDDhi - ulo - D.Vtplo) :=
      psq_mono (by linarith [hθ.VDD_le, hθ.Vtp_ge])
    have h3 : θ.kp / 2 * psq (θ.VDD - u - θ.Vtp) ≤ θ.kp / 2 * psq (D.VDDhi - ulo - D.Vtplo) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : θ.kp / 2 * psq (D.VDDhi - ulo - D.Vtplo)
        ≤ D.kphi / 2 * psq (D.VDDhi - ulo - D.Vtplo) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kp_le]) (psq_nonneg _)
    linarith
  have hN : -In θ u v ≤ D.knhi / 2 * psq (uhi - D.Vlo - D.Vtnlo) := by
    unfold In
    have h1 : psq (u - v - θ.Vtn) ≤ psq (uhi - D.Vlo - D.Vtnlo) :=
      psq_mono (by linarith [hθ.Vtn_ge])
    have h2 := psq_nonneg (u - θ.Vtn)
    have h3 : θ.kn / 2 * psq (u - v - θ.Vtn) ≤ θ.kn / 2 * psq (uhi - D.Vlo - D.Vtnlo) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h4 : θ.kn / 2 * psq (uhi - D.Vlo - D.Vtnlo)
        ≤ D.knhi / 2 * psq (uhi - D.Vlo - D.Vtnlo) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kn_le]) (psq_nonneg _)
    have h5 : 0 ≤ θ.kn / 2 * psq (u - θ.Vtn) := mul_nonneg (by linarith) h2
    nlinarith
  unfold IchargeMax Inet
  linarith

end Design

namespace IsTrajectory

variable {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}

/-- **The output cannot rise faster than the available current allows.** With
the input in `[ulo, uhi]` on `[s, e)` and `v s ≤ l`, the output stays below the
line through `l` with slope `(IchargeMax ulo uhi + eps) / Clo`. -/
theorem rise_at_most (hD : D.Admissible) (hθ : D.InBox θ) (h : IsTrajectory D θ u v a b)
    (h0 : v a ∈ D.Safe) {s e ulo uhi l : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, ulo ≤ u t ∧ u t ≤ uhi) (hl : v s ≤ l) :
    ∀ t ∈ Icc s e, v t ≤ l + (D.IchargeMax ulo uhi + D.eps) / D.Clo * (t - s) := by
  intro t ht
  have hsub : Ico s e ⊆ Ico a b := Ico_subset_Ico hs he
  have hN : 0 ≤ D.IchargeMax ulo uhi + D.eps := by
    linarith [Design.IchargeMax_nonneg hD ulo uhi, hD.eps_nonneg]
  refine image_le_of_deriv_right_le_deriv_boundary
    (f := v) (f' := rderiv v) (a := s) (b := e)
    (h.cont.mono (Icc_subset_Icc hs he)) (fun x hx => h.hasDeriv x (hsub hx))
    (B := fun x => l + (D.IchargeMax ulo uhi + D.eps) / D.Clo * (x - s))
    (B' := fun _ => (D.IchargeMax ulo uhi + D.eps) / D.Clo)
    (by simpa using hl) (by fun_prop)
    (fun x _ => by
      have hd := (((hasDerivAt_id x).sub_const s).const_mul
        ((D.IchargeMax ulo uhi + D.eps) / D.Clo)).const_add l
      simpa using hd.hasDerivWithinAt)
    (fun x hx => ?_) ht
  -- slope bound at time `x`
  obtain ⟨cap, hc1, -, hb⟩ := h.balance x (hsub hx)
  have hxab : x ∈ Icc a b := ⟨(hsub hx).1, (hsub hx).2.le⟩
  have hsafe := h.safe hD hθ h0 x hxab
  have hb' := hb hsafe
  have hI := Design.Inet_le_IchargeMax hD hθ (hu x hx).1 (hu x hx).2 hsafe.1
  have hcap : 0 < cap := lt_of_lt_of_le hD.C_pos hc1
  have hupper : cap * rderiv v x ≤ D.IchargeMax ulo uhi + D.eps := by
    linarith [(abs_le.mp hb').2]
  rw [le_div_iff₀ hD.C_pos]
  rcases le_total (rderiv v x) 0 with hneg | hpos
  · have := mul_nonpos_of_nonpos_of_nonneg hneg hD.C_pos.le
    linarith
  · have := mul_le_mul_of_nonneg_left hc1 hpos
    linarith [mul_comm cap (rderiv v x)]

end IsTrajectory

end VoltageToBit

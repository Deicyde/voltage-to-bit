import VoltageToBit.Proofs.Reach
import VoltageToBit.Proofs.Margins

/-!
# The digital guarantee for every trajectory

For an admissible design `D`, every parameter choice `θ` in the box, every
input `u : ℝ → ℝ` (no regularity assumed) and every trajectory `v` of the
differential inclusion on `[a, b]` that starts in the safe domain:

* `IsTrajectory.safe`: `v` stays in the safe domain;
* `IsTrajectory.rise`: if `u ≤ VIL` on `[s, e)` then `VOH ≤ v t` for all
  `t ∈ [s + tauUp, e]`;
* `IsTrajectory.fall`: if `VIH ≤ u` on `[s, e)` then `v t ≤ VOL` for all
  `t ∈ [s + tauDn, e]`;
* `IsTrajectory.decoded`: the same two facts through the three-valued decoder.

These are statements about *all* trajectories. That trajectories exist is
proved separately in `Proofs/Existence.lean`.
-/

namespace VoltageToBit

open Set

/-- The right derivative of `v` at `t`, as a total function. -/
noncomputable def rderiv (v : ℝ → ℝ) (t : ℝ) : ℝ := derivWithin v (Ici t) t

namespace IsTrajectory

variable {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}

theorem hasDeriv (h : IsTrajectory D θ u v a b) :
    ∀ t ∈ Ico a b, HasDerivWithinAt v (rderiv v t) (Ici t) t := by
  intro t ht
  obtain ⟨v', c, hd, -⟩ := h.incl t ht
  exact hd.differentiableWithinAt.hasDerivWithinAt

/-- The current balance, stated for the canonical right derivative. -/
theorem balance (h : IsTrajectory D θ u v a b) :
    ∀ t ∈ Ico a b, ∃ c : ℝ, D.Clo ≤ c ∧ c ≤ D.Chi ∧
      (v t ∈ D.Safe → |c * rderiv v t - Inet θ (u t) (v t)| ≤ D.eps) := by
  intro t ht
  obtain ⟨v', c, hd, hc1, hc2, hb⟩ := h.incl t ht
  have hv' : rderiv v t = v' := hd.derivWithin (uniqueDiffWithinAt_Ici t)
  exact ⟨c, hc1, hc2, by rw [hv']; exact hb⟩

/-- A trajectory restricts to any sub-interval. -/
theorem mono (h : IsTrajectory D θ u v a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    IsTrajectory D θ u v a' b' where
  cont := h.cont.mono (Icc_subset_Icc ha hb)
  incl := fun t ht => h.incl t (Ico_subset_Ico ha hb ht)

/-- **Safe-domain invariance.** A trajectory that starts in the safe domain
stays in it, whatever the input does. -/
theorem safe (hD : D.Admissible) (hθ : D.InBox θ) (h : IsTrajectory D θ u v a b)
    (h0 : v a ∈ D.Safe) : ∀ t ∈ Icc a b, v t ∈ D.Safe := by
  have hdom : D.Vlo ≤ D.Vhi := by linarith [hD.Vlo_le, hD.VDD_pos, hD.VDD_le, hD.Vhi_ge]
  intro t ht
  constructor
  · -- at `Vlo` the right derivative is positive
    refine barrier_ge h.cont h.hasDeriv h0.1 ?_ t ht
    intro s hs hvs
    obtain ⟨c, hc1, -, hb⟩ := h.balance s hs
    have hb' := hb (by rw [hvs]; exact ⟨le_rfl, hdom⟩)
    rw [hvs] at hb'
    have hI := Design.Inet_Vlo_gt hD hθ (u s)
    have hcpos : 0 < c := lt_of_lt_of_le hD.C_pos hc1
    have hpos : 0 < c * rderiv v s := by linarith [(abs_le.mp hb').1]
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hcpos.le (not_lt.mp hneg)
    linarith
  · -- at `Vhi` the right derivative is negative
    refine barrier_le h.cont h.hasDeriv h0.2 ?_ t ht
    intro s hs hvs
    obtain ⟨c, hc1, -, hb⟩ := h.balance s hs
    have hb' := hb (by rw [hvs]; exact ⟨hdom, le_rfl⟩)
    rw [hvs] at hb'
    have hI := Design.Inet_Vhi_lt hD hθ (u s)
    have hcpos : 0 < c := lt_of_lt_of_le hD.C_pos hc1
    have hnegp : c * rderiv v s < 0 := by linarith [(abs_le.mp hb').2]
    by_contra hpos
    have := mul_nonneg hcpos.le (not_lt.mp hpos)
    linarith

/-- Slope bound while charging: with a valid-low input and the node at or
below a level `c ≤ VDDlo` whose margin `Iup c` exceeds `eps`, the node voltage
rises at least at rate `(Iup c - eps) / Chi`. -/
theorem slope_up (hD : D.Admissible) (hθ : D.InBox θ) (h : IsTrajectory D θ u v a b)
    (h0 : v a ∈ D.Safe) {c t : ℝ} (hc : c ≤ D.VDDlo) (hmargin : D.eps < D.Iup c)
    (ht : t ∈ Ico a b) (hu : u t ≤ D.VIL) (hv : v t ≤ c) :
    (D.Iup c - D.eps) / D.Chi ≤ rderiv v t := by
  obtain ⟨cap, hc1, hc2, hb⟩ := h.balance t ht
  have hb' := hb (h.safe hD hθ h0 t ⟨ht.1, ht.2.le⟩)
  have hI := Design.Inet_ge_Iup hD hθ hu hv hc
  have hcap : 0 < cap := lt_of_lt_of_le hD.C_pos hc1
  have hChi : 0 < D.Chi := lt_of_lt_of_le hcap hc2
  have hN : D.Iup c - D.eps ≤ cap * rderiv v t := by linarith [(abs_le.mp hb').1]
  have hpos : 0 < rderiv v t := by
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hcap.le (not_lt.mp hneg)
    linarith
  rw [div_le_iff₀ hChi]
  nlinarith

/-- Slope bound while discharging: with a valid-high input and the node at or
above a level `c ≥ 0` whose margin `Idn c` exceeds `eps`, the node voltage
falls at least at rate `(Idn c - eps) / Chi`. -/
theorem slope_dn (hD : D.Admissible) (hθ : D.InBox θ) (h : IsTrajectory D θ u v a b)
    (h0 : v a ∈ D.Safe) {c t : ℝ} (hc : 0 ≤ c) (hmargin : D.eps < D.Idn c)
    (ht : t ∈ Ico a b) (hu : D.VIH ≤ u t) (hv : c ≤ v t) :
    rderiv v t ≤ -((D.Idn c - D.eps) / D.Chi) := by
  obtain ⟨cap, hc1, hc2, hb⟩ := h.balance t ht
  have hb' := hb (h.safe hD hθ h0 t ⟨ht.1, ht.2.le⟩)
  have hI := Design.Inet_le_neg_Idn hD hθ hu hv hc
  have hcap : 0 < cap := lt_of_lt_of_le hD.C_pos hc1
  have hChi : 0 < D.Chi := lt_of_lt_of_le hcap hc2
  have hN : cap * rderiv v t ≤ -(D.Idn c - D.eps) := by linarith [(abs_le.mp hb').2]
  have hneg : rderiv v t < 0 := by
    by_contra hpos
    have := mul_nonneg hcap.le (not_lt.mp hpos)
    linarith
  rw [le_neg, div_le_iff₀ hChi]
  nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (neg_nonneg.mpr hneg.le)]

/-- **Low in, high out, by a deadline, and it stays.** If the input is
valid-low on `[s, e)`, the output is valid-high on `[s + tauUp, e]`. -/
theorem rise (hD : D.Admissible) (hθ : D.InBox θ) (h : IsTrajectory D θ u v a b)
    (h0 : v a ∈ D.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, u t ≤ D.VIL) :
    ∀ t ∈ Icc s e, s + D.tauUp ≤ t → D.VOH ≤ v t := by
  intro t ht htime
  have hse : s ≤ e := le_trans ht.1 ht.2
  have hsub : Ico s e ⊆ Ico a b := Ico_subset_Ico hs he
  have hChi : 0 < D.Chi := lt_of_lt_of_le hD.C_pos hD.C_le
  have hN : 0 < D.Iup D.VOH - D.eps := by linarith [hD.up]
  have hvs : D.Vlo ≤ v s := (h.safe hD hθ h0 s ⟨hs, le_trans hse he⟩).1
  have htau : (D.VOH - D.Vlo) / ((D.Iup D.VOH - D.eps) / D.Chi) = D.tauUp := by
    unfold Design.tauUp
    field_simp
  refine rise_by (h.cont.mono (Icc_subset_Icc hs he)) (fun x hx => h.hasDeriv x (hsub hx))
    (div_pos hN hChi) hvs
    (fun x hx hvx => h.slope_up hD hθ h0 hD.VOH_le hD.up (hsub hx) (hu x hx) hvx) t ht ?_
  rw [htau]
  exact htime

/-- **High in, low out, by a deadline, and it stays.** If the input is
valid-high on `[s, e)`, the output is valid-low on `[s + tauDn, e]`. -/
theorem fall (hD : D.Admissible) (hθ : D.InBox θ) (h : IsTrajectory D θ u v a b)
    (h0 : v a ∈ D.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, D.VIH ≤ u t) :
    ∀ t ∈ Icc s e, s + D.tauDn ≤ t → v t ≤ D.VOL := by
  intro t ht htime
  have hse : s ≤ e := le_trans ht.1 ht.2
  have hsub : Ico s e ⊆ Ico a b := Ico_subset_Ico hs he
  have hChi : 0 < D.Chi := lt_of_lt_of_le hD.C_pos hD.C_le
  have hN : 0 < D.Idn D.VOL - D.eps := by linarith [hD.dn]
  have hvs : v s ≤ D.Vhi := (h.safe hD hθ h0 s ⟨hs, le_trans hse he⟩).2
  have htau : (D.Vhi - D.VOL) / ((D.Idn D.VOL - D.eps) / D.Chi) = D.tauDn := by
    unfold Design.tauDn
    field_simp
  refine fall_by (h.cont.mono (Icc_subset_Icc hs he)) (fun x hx => h.hasDeriv x (hsub hx))
    (div_pos hN hChi) hvs
    (fun x hx hvx => h.slope_dn hD hθ h0 hD.VOL_nonneg hD.dn (hsub hx) (hu x hx) hvx) t ht ?_
  rw [htau]
  exact htime

/-- **Decoded form.** If the input decodes to the bit `inBit` throughout
`[s, e)`, then the output decodes to the opposite bit throughout
`[s + tau inBit, e]`. Voltages between the thresholds decode to `none`, so the
hypothesis fails for them and nothing is claimed. -/
theorem decoded (hD : D.Admissible) (hθ : D.InBox θ) (h : IsTrajectory D θ u v a b)
    (h0 : v a ∈ D.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b) (inBit : Bool)
    (hu : ∀ t ∈ Ico s e, D.decodeIn (u t) = some inBit) :
    ∀ t ∈ Icc s e, s + D.tau inBit ≤ t → D.decodeOut (v t) = some (!inBit) := by
  have hio : D.VIL < D.VIH := hD.VIL_lt_VIH
  have hoo : D.VOL < D.VOH := by linarith [hD.VOL_le_VIL, hD.VIL_lt_VIH, hD.VIH_le_VOH]
  intro t ht htime
  cases inBit with
  | false =>
    have hu' : ∀ x ∈ Ico s e, u x ≤ D.VIL := fun x hx => decode_eq_false_iff.mp (hu x hx)
    have := h.rise hD hθ h0 hs he hu' t ht (by simpa [Design.tau] using htime)
    simpa [Design.decodeOut] using (decode_eq_true_iff hoo).mpr this
  | true =>
    have hu' : ∀ x ∈ Ico s e, D.VIH ≤ u x := fun x hx => (decode_eq_true_iff hio).mp (hu x hx)
    have := h.fall hD hθ h0 hs he hu' t ht (by simpa [Design.tau] using htime)
    simpa [Design.decodeOut] using decode_eq_false_iff.mpr this

end IsTrajectory

end VoltageToBit

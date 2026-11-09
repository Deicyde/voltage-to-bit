import VoltageToBit.Proofs.Guarantee

/-!
# Refined delay bounds from a list of levels (certificates)

The deadlines `tauUp` and `tauDn` use one slope bound for the whole swing: the
worst-corner current at the final level. A list of intermediate levels gives a
smaller, still fully proved, deadline: on the way to each level `c` the slope
is at least `(Iup c - eps) / Chi`, and the deadline is the sum over segments.

A *certificate* is just the list of levels. The theorems below are checked
once, for every list; checking a particular certificate is then arithmetic.
Whoever proposes the list (a person, a search, a learned model) is not trusted.
-/

namespace VoltageToBit

open Set

namespace Design

variable (D : Design)

/-- Rising segments for a list of levels: each level `c` is paired with the
proved slope bound `(Iup c - eps) / Chi`. -/
noncomputable def upSegs (cs : List ℝ) : List (ℝ × ℝ) :=
  cs.map fun c => (c, (D.Iup c - D.eps) / D.Chi)

/-- Falling segments for a list of levels: each level `c` is paired with the
proved slope bound `(Idn c - eps) / Chi`. -/
noncomputable def dnSegs (cs : List ℝ) : List (ℝ × ℝ) :=
  cs.map fun c => (c, (D.Idn c - D.eps) / D.Chi)

/-- Numeric validity of a rising certificate `c :: cs` for a claimed deadline
`τ`: the levels are nondecreasing from `Vlo` with positive slope bounds, the
last level is `VOH`, and the summed segment times do not exceed `τ`. -/
def ValidRiseCert (c : ℝ) (cs : List ℝ) (τ : ℝ) : Prop :=
  RiseSegs D.Vlo (D.upSegs (c :: cs)) ∧
    finalLevel D.Vlo (D.upSegs (c :: cs)) = D.VOH ∧
    riseTime D.Vlo (D.upSegs (c :: cs)) ≤ τ

/-- Numeric validity of a falling certificate `c :: cs` for a claimed deadline
`τ`: the levels are nonincreasing from `Vhi` with positive slope bounds, the
last level is `VOL`, and the summed segment times do not exceed `τ`. -/
def ValidFallCert (c : ℝ) (cs : List ℝ) (τ : ℝ) : Prop :=
  FallSegs D.Vhi (D.dnSegs (c :: cs)) ∧
    finalLevel D.Vhi (D.dnSegs (c :: cs)) = D.VOL ∧
    fallTime D.Vhi (D.dnSegs (c :: cs)) ≤ τ

end Design

namespace IsTrajectory

variable {D : Design} {u v : ℝ → ℝ} {a b : ℝ}

/-- **Rising certificate.** Let `c :: cs` be levels that are nondecreasing from
`Vlo`, stay at or below `VDDlo`, and whose margins `Iup · - eps` are positive.
If the input is valid-low on `[s, e)`, the output is at or above the last
level on `[s + riseTime …, e]`. -/
theorem rise_certificate (hD : D.Admissible)
    (h : IsTrajectory D u v a b) (h0 : v a ∈ D.Safe) (c : ℝ) (cs : List ℝ)
    (hsegs : RiseSegs D.Vlo (D.upSegs (c :: cs)))
    (hmax : ∀ x ∈ c :: cs, x ≤ D.VDDlo)
    {s e : ℝ} (hs : a ≤ s) (he : e ≤ b) (hu : ∀ t ∈ Ico s e, u t ≤ D.VIL) :
    ∀ t ∈ Icc s e, s + riseTime D.Vlo (D.upSegs (c :: cs)) ≤ t →
      finalLevel D.Vlo (D.upSegs (c :: cs)) ≤ v t := by
  intro t ht htime
  have hse : s ≤ e := le_trans ht.1 ht.2
  have hsub : Ico s e ⊆ Ico a b := Ico_subset_Ico hs he
  have hChi : 0 < D.Chi := lt_of_lt_of_le hD.C_pos hD.C_le
  have hvs : D.Vlo ≤ v s := (h.safe hD h0 s ⟨hs, le_trans hse he⟩).1
  have hslope : ∀ p ∈ D.upSegs (c :: cs), ∀ x ∈ Ico s e, v x ≤ p.1 → p.2 ≤ rderiv v x := by
    intro p hp x hx hvx
    have hpos := hsegs.pos p hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    have hmargin : D.eps < D.Iup y := by
      have h1 : 0 < D.Iup y - D.eps := by
        by_contra hneg
        have := div_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hChi.le
        linarith
      linarith
    exact h.slope_up hD h0 (hmax y hy) hmargin (hsub hx) (hu x hx) hvx
  exact rise_chain (h.cont.mono (Icc_subset_Icc hs he)) (fun x hx => h.hasDeriv x (hsub hx))
    (D.upSegs cs) c ((D.Iup c - D.eps) / D.Chi) D.Vlo s hsegs hslope ⟨le_rfl, hse⟩ hvs t ht htime

/-- **Falling certificate.** Mirror image of `rise_certificate`: levels are
nonincreasing from `Vhi` and stay at or above `0`. -/
theorem fall_certificate (hD : D.Admissible)
    (h : IsTrajectory D u v a b) (h0 : v a ∈ D.Safe) (c : ℝ) (cs : List ℝ)
    (hsegs : FallSegs D.Vhi (D.dnSegs (c :: cs)))
    (hmin : ∀ x ∈ c :: cs, 0 ≤ x)
    {s e : ℝ} (hs : a ≤ s) (he : e ≤ b) (hu : ∀ t ∈ Ico s e, D.VIH ≤ u t) :
    ∀ t ∈ Icc s e, s + fallTime D.Vhi (D.dnSegs (c :: cs)) ≤ t →
      v t ≤ finalLevel D.Vhi (D.dnSegs (c :: cs)) := by
  intro t ht htime
  have hse : s ≤ e := le_trans ht.1 ht.2
  have hsub : Ico s e ⊆ Ico a b := Ico_subset_Ico hs he
  have hChi : 0 < D.Chi := lt_of_lt_of_le hD.C_pos hD.C_le
  have hvs : v s ≤ D.Vhi := (h.safe hD h0 s ⟨hs, le_trans hse he⟩).2
  have hslope : ∀ p ∈ D.dnSegs (c :: cs), ∀ x ∈ Ico s e, p.1 ≤ v x → rderiv v x ≤ -p.2 := by
    intro p hp x hx hvx
    have hpos := hsegs.pos p hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    have hmargin : D.eps < D.Idn y := by
      have h1 : 0 < D.Idn y - D.eps := by
        by_contra hneg
        have := div_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hChi.le
        linarith
      linarith
    exact h.slope_dn hD h0 (hmin y hy) hmargin (hsub hx) (hu x hx) hvx
  exact fall_chain (h.cont.mono (Icc_subset_Icc hs he)) (fun x hx => h.hasDeriv x (hsub hx))
    (D.dnSegs cs) c ((D.Idn c - D.eps) / D.Chi) D.Vhi s hsegs hslope ⟨le_rfl, hse⟩ hvs t ht htime

/-- **A valid rising certificate proves its deadline.** -/
theorem rise_of_cert (hD : D.Admissible)
    (h : IsTrajectory D u v a b) (h0 : v a ∈ D.Safe) {c : ℝ} {cs : List ℝ} {τ : ℝ}
    (hcert : D.ValidRiseCert c cs τ)
    {s e : ℝ} (hs : a ≤ s) (he : e ≤ b) (hu : ∀ t ∈ Ico s e, u t ≤ D.VIL) :
    ∀ t ∈ Icc s e, s + τ ≤ t → D.VOH ≤ v t := by
  obtain ⟨hsegs, hfinal, hτ⟩ := hcert
  intro t ht htime
  have hmax : ∀ x ∈ c :: cs, x ≤ D.VDDlo := by
    intro x hx
    have hmem : (x, (D.Iup x - D.eps) / D.Chi) ∈ D.upSegs (c :: cs) :=
      List.mem_map.mpr ⟨x, hx, rfl⟩
    have := hsegs.mem_le_finalLevel _ hmem
    rw [hfinal] at this
    exact le_trans this hD.VOH_le
  have := h.rise_certificate hD h0 c cs hsegs hmax hs he hu t ht (by linarith)
  rwa [hfinal] at this

/-- **A valid falling certificate proves its deadline.** -/
theorem fall_of_cert (hD : D.Admissible)
    (h : IsTrajectory D u v a b) (h0 : v a ∈ D.Safe) {c : ℝ} {cs : List ℝ} {τ : ℝ}
    (hcert : D.ValidFallCert c cs τ)
    {s e : ℝ} (hs : a ≤ s) (he : e ≤ b) (hu : ∀ t ∈ Ico s e, D.VIH ≤ u t) :
    ∀ t ∈ Icc s e, s + τ ≤ t → v t ≤ D.VOL := by
  obtain ⟨hsegs, hfinal, hτ⟩ := hcert
  intro t ht htime
  have hmin : ∀ x ∈ c :: cs, 0 ≤ x := by
    intro x hx
    have hmem : (x, (D.Idn x - D.eps) / D.Chi) ∈ D.dnSegs (c :: cs) :=
      List.mem_map.mpr ⟨x, hx, rfl⟩
    have := hsegs.finalLevel_le_mem _ hmem
    rw [hfinal] at this
    exact le_trans hD.VOL_nonneg this
  have := h.fall_certificate hD h0 c cs hsegs hmin hs he hu t ht (by linarith)
  rwa [hfinal] at this

end IsTrajectory

end VoltageToBit

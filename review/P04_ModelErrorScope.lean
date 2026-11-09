import VoltageToBit

/-!
# Probe P04 (workstream E): what the model-error hypothesis can and cannot absorb

`IsTrajectory.of_model_error` covers a "true" current law `J` only if, for ONE
fixed parameter choice `θ` in the box, `|J - Inet θ| ≤ εm ≤ eps` on the whole
safe domain. With `eps = 2 µA` this is an absolute 2 µA envelope around a
single square-law curve whose currents reach 85-170 µA.

Part A shows that the mildest refinement listed as "omitted on purpose" in
`Model/Device.lean`, channel-length modulation, already violates that
hypothesis for EVERY `θ` in the box (`clm_not_within_eps`), with a modulation
coefficient `λ = 0.05 /V` (an assumed, small value; not taken from any process).

Part B shows that the very same law IS a square law with in-box parameters at
each operating point (`clm_is_pointwise_square_law`).

Part C shows that the library's proofs do not need a fixed `θ`: the safe-domain,
rise and fall theorems hold verbatim for a trajectory notion in which the
parameter choice may differ from instant to instant
(`IsTrajectoryPW.safe/rise/fall`), so the channel-length-modulated inverter is
covered with the full `eps` left for disturbances (`clm_guarantee`).

Part C is NOT part of the reviewed development. It is evidence for a
recommended change of the interface, compiled against the frozen library.
-/

open Set
open VoltageToBit VoltageToBit.Examples

namespace Review.P04

/-! ## Part A: channel-length modulation does not fit the fixed-parameter envelope -/

/-- Nominal square law with first-order channel-length modulation on the NMOS:
`I_n` is multiplied by `1 + lam * V_DS`, where `V_DS = x` is the output voltage. -/
noncomputable def Jclm (lam u x : ℝ) : ℝ := Ip nominal u x - In nominal u x * (1 + lam * x)

/-- For every `θ` in the box and input `1.8 V`, the square-law current is the
same at `x = 1.35` and at `x = 2.08` (NMOS saturated, PMOS off). -/
theorem Inet_box_flat (θ : Params) (hθ : illustrative.InBox θ) {x : ℝ} (h1 : 1.35 ≤ x)
    (h2 : x ≤ 2.08) : Inet θ 1.8 x = -(θ.kn / 2 * (1.8 - θ.Vtn) ^ 2) := by
  have hVDD : θ.VDD ≤ 1.98 := by simpa [illustrative] using hθ.VDD_le
  have hVtp : (0.45 : ℝ) ≤ θ.Vtp := by simpa [illustrative] using hθ.Vtp_ge
  have hVtn : (0.45 : ℝ) ≤ θ.Vtn := by simpa [illustrative] using hθ.Vtn_ge
  have hVtn' : θ.Vtn ≤ 0.60 := by simpa [illustrative] using hθ.Vtn_le
  have hp : Ip θ 1.8 x = 0 := by
    unfold Ip
    rw [psq_of_nonpos (by linarith), psq_of_nonpos (by linarith)]
    ring
  have hn : In θ 1.8 x = θ.kn / 2 * (1.8 - θ.Vtn) ^ 2 := In_sat (by linarith) (by linarith)
  rw [Inet, hp, hn]
  ring

theorem Jclm_at {x : ℝ} (h1 : 1.35 ≤ x) (h2 : x ≤ 2.08) :
    Jclm 0.05 1.8 x = -(169 * (1 + 0.05 * x)) := by
  have hp : Ip nominal 1.8 x = 0 := by
    have e1 : psq ((1.8 : ℝ) - 1.8 - 0.5) = 0 := psq_of_nonpos (by norm_num)
    have e2 : psq (x - 1.8 - 0.5) = 0 := psq_of_nonpos (by linarith)
    simp only [Ip, nominal, e1, e2]
    norm_num
  have hn : In nominal 1.8 x = 169 := by
    have e : In nominal 1.8 x = nominal.kn / 2 * (1.8 - nominal.Vtn) ^ 2 :=
      In_sat (by norm_num [nominal]) (by norm_num [nominal]; linarith)
    rw [e]; norm_num [nominal]
  rw [Jclm, hp, hn]
  ring

/-- **No fixed in-box parameter choice keeps the channel-length-modulated law
within `eps` of the square law on the safe domain.** Hence the hypothesis `hJ`
of `IsTrajectory.of_model_error` (with `εm ≤ eps`) fails for every `θ`. -/
theorem clm_not_within_eps (θ : Params) (hθ : illustrative.InBox θ) :
    ¬ ∀ x ∈ illustrative.Safe, |Jclm 0.05 1.8 x - Inet θ 1.8 x| ≤ illustrative.eps := by
  intro h
  have m1 : (1.35 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  have m2 : (2.08 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  have h1 := h 1.35 m1
  have h2 := h 2.08 m2
  rw [Jclm_at le_rfl (by norm_num), Inet_box_flat θ hθ le_rfl (by norm_num)] at h1
  rw [Jclm_at (by norm_num) le_rfl, Inet_box_flat θ hθ (by norm_num) le_rfl] at h2
  have heps : illustrative.eps = 2 := by norm_num [illustrative]
  rw [heps] at h1 h2
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).1
  norm_num at a1 a2
  linarith

/-! ## Part B: pointwise, it is a square law with in-box parameters -/

theorem clm_is_pointwise_square_law (u x : ℝ) (hx : x ∈ illustrative.Safe) :
    ∃ θ : Params, illustrative.InBox θ ∧ Jclm 0.05 u x = Inet θ u x := by
  have hx' : -0.10 ≤ x ∧ x ≤ 2.08 := by simpa [Design.Safe, illustrative] using hx
  refine ⟨⟨1.8, 200 * (1 + 0.05 * x), 100, 0.5, 0.5⟩, ?_, ?_⟩
  · constructor <;> norm_num [illustrative] <;> linarith [hx'.1, hx'.2]
  · simp only [Jclm, Inet, Ip, In, nominal]
    ring

/-! ## Part C: the guarantee does not need a fixed parameter choice -/

/-- Like `IsTrajectory`, but the parameter choice in the box may be different
at every instant (so it may depend on time, on the state and on the input). -/
structure IsTrajectoryPW (D : Design) (u v : ℝ → ℝ) (a b : ℝ) : Prop where
  cont : ContinuousOn v (Icc a b)
  incl : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
    D.Clo ≤ c ∧ c ≤ D.Chi ∧
    (v t ∈ D.Safe → ∃ θ : Params, D.InBox θ ∧ |c * v' - Inet θ (u t) (v t)| ≤ D.eps)

namespace IsTrajectoryPW

variable {D : Design} {u v : ℝ → ℝ} {a b : ℝ}

/-- The library's notion is the special case of a constant parameter choice. -/
theorem of_fixed {θ : Params} (hθ : D.InBox θ) (h : IsTrajectory D θ u v a b) :
    IsTrajectoryPW D u v a b where
  cont := h.cont
  incl := fun t ht => by
    obtain ⟨v', c, hd, hc1, hc2, hb⟩ := h.incl t ht
    exact ⟨v', c, hd, hc1, hc2, fun hs => ⟨θ, hθ, hb hs⟩⟩

theorem hasDeriv (h : IsTrajectoryPW D u v a b) :
    ∀ t ∈ Ico a b, HasDerivWithinAt v (rderiv v t) (Ici t) t := by
  intro t ht
  obtain ⟨v', c, hd, -⟩ := h.incl t ht
  exact hd.differentiableWithinAt.hasDerivWithinAt

theorem balance (h : IsTrajectoryPW D u v a b) :
    ∀ t ∈ Ico a b, ∃ c : ℝ, D.Clo ≤ c ∧ c ≤ D.Chi ∧
      (v t ∈ D.Safe → ∃ θ : Params, D.InBox θ ∧
        |c * rderiv v t - Inet θ (u t) (v t)| ≤ D.eps) := by
  intro t ht
  obtain ⟨v', c, hd, hc1, hc2, hb⟩ := h.incl t ht
  have hv' : rderiv v t = v' := hd.derivWithin (uniqueDiffWithinAt_Ici t)
  exact ⟨c, hc1, hc2, by rw [hv']; exact hb⟩

theorem safe (hD : D.Admissible) (h : IsTrajectoryPW D u v a b) (h0 : v a ∈ D.Safe) :
    ∀ t ∈ Icc a b, v t ∈ D.Safe := by
  have hdom : D.Vlo ≤ D.Vhi := by linarith [hD.Vlo_le, hD.VDD_pos, hD.VDD_le, hD.Vhi_ge]
  intro t ht
  constructor
  · refine barrier_ge h.cont h.hasDeriv h0.1 ?_ t ht
    intro s hs hvs
    obtain ⟨c, hc1, -, hb⟩ := h.balance s hs
    obtain ⟨θ, hθ, hb'⟩ := hb (by rw [hvs]; exact ⟨le_rfl, hdom⟩)
    rw [hvs] at hb'
    have hI := Design.Inet_Vlo_gt hD hθ (u s)
    have hcpos : 0 < c := lt_of_lt_of_le hD.C_pos hc1
    have hpos : 0 < c * rderiv v s := by linarith [(abs_le.mp hb').1]
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hcpos.le (not_lt.mp hneg)
    linarith
  · refine barrier_le h.cont h.hasDeriv h0.2 ?_ t ht
    intro s hs hvs
    obtain ⟨c, hc1, -, hb⟩ := h.balance s hs
    obtain ⟨θ, hθ, hb'⟩ := hb (by rw [hvs]; exact ⟨hdom, le_rfl⟩)
    rw [hvs] at hb'
    have hI := Design.Inet_Vhi_lt hD hθ (u s)
    have hcpos : 0 < c := lt_of_lt_of_le hD.C_pos hc1
    have hnegp : c * rderiv v s < 0 := by linarith [(abs_le.mp hb').2]
    by_contra hpos
    have := mul_nonneg hcpos.le (not_lt.mp hpos)
    linarith

theorem slope_up (hD : D.Admissible) (h : IsTrajectoryPW D u v a b) (h0 : v a ∈ D.Safe)
    {c t : ℝ} (hc : c ≤ D.VDDlo) (hmargin : D.eps < D.Iup c)
    (ht : t ∈ Ico a b) (hu : u t ≤ D.VIL) (hv : v t ≤ c) :
    (D.Iup c - D.eps) / D.Chi ≤ rderiv v t := by
  obtain ⟨cap, hc1, hc2, hb⟩ := h.balance t ht
  obtain ⟨θ, hθ, hb'⟩ := hb (h.safe hD h0 t ⟨ht.1, ht.2.le⟩)
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

theorem slope_dn (hD : D.Admissible) (h : IsTrajectoryPW D u v a b) (h0 : v a ∈ D.Safe)
    {c t : ℝ} (hc : 0 ≤ c) (hmargin : D.eps < D.Idn c)
    (ht : t ∈ Ico a b) (hu : D.VIH ≤ u t) (hv : c ≤ v t) :
    rderiv v t ≤ -((D.Idn c - D.eps) / D.Chi) := by
  obtain ⟨cap, hc1, hc2, hb⟩ := h.balance t ht
  obtain ⟨θ, hθ, hb'⟩ := hb (h.safe hD h0 t ⟨ht.1, ht.2.le⟩)
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

theorem rise (hD : D.Admissible) (h : IsTrajectoryPW D u v a b)
    (h0 : v a ∈ D.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, u t ≤ D.VIL) :
    ∀ t ∈ Icc s e, s + D.tauUp ≤ t → D.VOH ≤ v t := by
  intro t ht htime
  have hse : s ≤ e := le_trans ht.1 ht.2
  have hsub : Ico s e ⊆ Ico a b := Ico_subset_Ico hs he
  have hChi : 0 < D.Chi := lt_of_lt_of_le hD.C_pos hD.C_le
  have hN : 0 < D.Iup D.VOH - D.eps := by linarith [hD.up]
  have hvs : D.Vlo ≤ v s := (h.safe hD h0 s ⟨hs, le_trans hse he⟩).1
  have htau : (D.VOH - D.Vlo) / ((D.Iup D.VOH - D.eps) / D.Chi) = D.tauUp := by
    unfold Design.tauUp
    field_simp
  refine rise_by (h.cont.mono (Icc_subset_Icc hs he)) (fun x hx => h.hasDeriv x (hsub hx))
    (div_pos hN hChi) hvs
    (fun x hx hvx => h.slope_up hD h0 hD.VOH_le hD.up (hsub hx) (hu x hx) hvx) t ht ?_
  rw [htau]
  exact htime

theorem fall (hD : D.Admissible) (h : IsTrajectoryPW D u v a b)
    (h0 : v a ∈ D.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, D.VIH ≤ u t) :
    ∀ t ∈ Icc s e, s + D.tauDn ≤ t → v t ≤ D.VOL := by
  intro t ht htime
  have hse : s ≤ e := le_trans ht.1 ht.2
  have hsub : Ico s e ⊆ Ico a b := Ico_subset_Ico hs he
  have hChi : 0 < D.Chi := lt_of_lt_of_le hD.C_pos hD.C_le
  have hN : 0 < D.Idn D.VOL - D.eps := by linarith [hD.dn]
  have hvs : v s ≤ D.Vhi := (h.safe hD h0 s ⟨hs, le_trans hse he⟩).2
  have htau : (D.Vhi - D.VOL) / ((D.Idn D.VOL - D.eps) / D.Chi) = D.tauDn := by
    unfold Design.tauDn
    field_simp
  refine fall_by (h.cont.mono (Icc_subset_Icc hs he)) (fun x hx => h.hasDeriv x (hsub hx))
    (div_pos hN hChi) hvs
    (fun x hx hvx => h.slope_dn hD h0 hD.VOL_nonneg hD.dn (hsub hx) (hu x hx) hvx) t ht ?_
  rw [htau]
  exact htime

end IsTrajectoryPW

/-- **The channel-length-modulated inverter is covered by the pointwise
notion**, with the whole `eps = 2 µA` still available for the disturbance `w`:
every solution of `c * v' = Jclm 0.05 (u t) (v t) + w t`, `c ∈ [5, 20]`,
`|w| ≤ 2`, that starts in the safe domain stays in it and meets both deadlines. -/
theorem clm_guarantee (u v w : ℝ → ℝ) (a b : ℝ) (hcont : ContinuousOn v (Icc a b))
    (hw : ∀ t ∈ Ico a b, |w t| ≤ 2)
    (hode : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      (5 : ℝ) ≤ c ∧ c ≤ 20 ∧ c * v' = Jclm 0.05 (u t) (v t) + w t)
    (h0 : v a ∈ Icc (-0.10 : ℝ) 2.08) :
    (∀ t ∈ Icc a b, v t ∈ Icc (-0.10 : ℝ) 2.08) ∧
    (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
      ∀ t ∈ Icc s e, s + 3.43 ≤ t → 1.35 ≤ v t) ∧
    (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
      ∀ t ∈ Icc s e, s + 2.57 ≤ t → v t ≤ 0.25) := by
  have hadm := illustrative_admissible
  have hsafe : illustrative.Safe = Icc (-0.10 : ℝ) 2.08 := by
    norm_num [Design.Safe, illustrative]
  have h : IsTrajectoryPW illustrative u v a b :=
    { cont := hcont
      incl := fun t ht => by
        obtain ⟨v', c, hd, hc1, hc2, he⟩ := hode t ht
        refine ⟨v', c, hd, by simpa [illustrative] using hc1, by simpa [illustrative] using hc2,
          fun hs => ?_⟩
        obtain ⟨θ, hθ, hJ⟩ := clm_is_pointwise_square_law (u t) (v t) hs
        refine ⟨θ, hθ, ?_⟩
        rw [he, hJ, add_sub_cancel_left]
        simpa [illustrative] using hw t ht }
  have h0' : v a ∈ illustrative.Safe := by rw [hsafe]; exact h0
  refine ⟨fun t ht => ?_, fun s e hs he hu t ht htime => ?_, fun s e hs he hu t ht htime => ?_⟩
  · rw [← hsafe]
    exact h.safe hadm h0' t ht
  · have := h.rise hadm h0' hs he (fun x hx => by simpa [illustrative] using hu x hx) t ht
      (by linarith [illustrative_tauUp_le])
    simpa [illustrative] using this
  · have := h.fall hadm h0' hs he (fun x hx => by simpa [illustrative] using hu x hx) t ht
      (by linarith [illustrative_tauDn_le])
    simpa [illustrative] using this

end Review.P04

#print axioms Review.P04.clm_not_within_eps
#print axioms Review.P04.clm_is_pointwise_square_law
#print axioms Review.P04.IsTrajectoryPW.safe
#print axioms Review.P04.IsTrajectoryPW.rise
#print axioms Review.P04.IsTrajectoryPW.fall
#print axioms Review.P04.clm_guarantee

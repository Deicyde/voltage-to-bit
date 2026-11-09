import VoltageToBit

/-!
# Probe D02 (workstream E, Part 2, commit 9b13e95): the per-instant trajectory notion

Claims under attack (coordinator's item 1 and 2):
"the new `IsTrajectory` is strictly more general than the fixed-parameter one",
"nothing in `safe`/`rise`/`fall` depends on the point being constant", and the
sandwich form of the model-error obligation.

* `IsTrajectoryFixed`: the definition of commit 1880a36, copied verbatim.
* `IsTrajectoryPW`: the reviewer's own per-instant definition, written for
  `P04_ModelErrorScope.lean` before seeing commit 9b13e95.
* `new_iff_reviewer_definition`: the library's new definition and the
  reviewer's independent one are the same proposition (so the safe/rise/fall
  proofs the reviewer wrote independently in P04 apply to it verbatim).
* `fixed_implies_new`: every fixed-parameter trajectory with parameters in the
  box is a trajectory in the new sense (the new theorems imply the old ones).
* `supply_tracking_is_new_trajectory`, `supply_tracking_not_fixed`: STRICTLY
  more general. The output `1.65 + 0.1 t` with the input at `0 V` is a
  trajectory in the new sense (the supply ramps, the PMOS holds the node at the
  supply), but for no single box member is it a fixed-parameter trajectory.
* `clm_not_within_eps_of_any_fixed_member` and `clm_guarantee`: the sandwich is
  satisfiable in a non-trivial case. Channel-length modulation (`λ = 0.05 /V`,
  an assumed value) is not within `eps` of any FIXED box member, yet it meets
  the new obligation with `εm = 0`, leaving the whole `eps` for disturbances.
-/

open Set
open VoltageToBit VoltageToBit.Examples

namespace Review.D02

/-- The trajectory notion of commit 1880a36 (fixed parameter point). -/
structure IsTrajectoryFixed (D : Design) (θ : Params) (u v : ℝ → ℝ) (a b : ℝ) : Prop where
  cont : ContinuousOn v (Icc a b)
  incl : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
    D.Clo ≤ c ∧ c ≤ D.Chi ∧ (v t ∈ D.Safe → |c * v' - Inet θ (u t) (v t)| ≤ D.eps)

/-- The reviewer's per-instant definition from P04 (written independently). -/
structure IsTrajectoryPW (D : Design) (u v : ℝ → ℝ) (a b : ℝ) : Prop where
  cont : ContinuousOn v (Icc a b)
  incl : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
    D.Clo ≤ c ∧ c ≤ D.Chi ∧
    (v t ∈ D.Safe → ∃ θ : Params, D.InBox θ ∧ |c * v' - Inet θ (u t) (v t)| ≤ D.eps)

theorem new_iff_reviewer_definition (D : Design) (u v : ℝ → ℝ) (a b : ℝ) :
    IsTrajectory D u v a b ↔ IsTrajectoryPW D u v a b :=
  ⟨fun h => ⟨h.cont, h.incl⟩, fun h => ⟨h.cont, h.incl⟩⟩

theorem fixed_implies_new {D : Design} {θ : Params} (hθ : D.InBox θ) {u v : ℝ → ℝ} {a b : ℝ}
    (h : IsTrajectoryFixed D θ u v a b) : IsTrajectory D u v a b where
  cont := h.cont
  incl := fun t ht => by
    obtain ⟨v', c, hd, hc1, hc2, hb⟩ := h.incl t ht
    exact ⟨v', c, hd, hc1, hc2, fun hs => ⟨θ, hθ, hb hs⟩⟩

/-! ## Strictness: a trajectory that no fixed box member explains -/

/-- The node follows a supply that ramps from 1.65 V to 1.75 V in 1 ns. -/
noncomputable def vRamp (t : ℝ) : ℝ := 1.65 + 0.1 * t

theorem hasDeriv_vRamp (t : ℝ) : HasDerivWithinAt vRamp 0.1 (Ici t) t := by
  have h := ((hasDerivAt_id t).const_mul (0.1 : ℝ)).const_add 1.65
  show HasDerivWithinAt (fun s : ℝ => 1.65 + 0.1 * s) 0.1 (Ici t) t
  simpa using h.hasDerivWithinAt

/-- With the input at 0 V and the supply equal to the node voltage, the device
current is zero. -/
theorem Inet_at_supply {x : ℝ} (hx : 0 ≤ x) : Inet ⟨x, 200, 100, 0.5, 0.5⟩ 0 x = 0 := by
  have e3 : psq ((0 : ℝ) - 0.5) = 0 := psq_of_nonpos (by norm_num)
  have e4 : psq ((0 : ℝ) - x - 0.5) = 0 := psq_of_nonpos (by linarith)
  simp only [Inet, Ip, In, e3, e4]
  ring

theorem supply_tracking_is_new_trajectory :
    IsTrajectory illustrative (fun _ => 0) vRamp 0 1 where
  cont := by unfold vRamp; fun_prop
  incl := fun t ht => by
    refine ⟨0.1, 5, hasDeriv_vRamp t, by norm_num [illustrative], by norm_num [illustrative],
      fun _ => ⟨⟨vRamp t, 200, 100, 0.5, 0.5⟩, ?_, ?_⟩⟩
    · constructor <;> norm_num [illustrative, vRamp] <;> linarith [ht.1, ht.2]
    · rw [Inet_at_supply (by unfold vRamp; linarith [ht.1])]
      norm_num [illustrative]

theorem supply_tracking_not_fixed (θ : Params) (hθ : illustrative.InBox θ) :
    ¬ IsTrajectoryFixed illustrative θ (fun _ => 0) vRamp 0 1 := by
  intro h
  have hkp : (80 : ℝ) ≤ θ.kp := hθ.kp_ge
  have hVtp1 : (0.45 : ℝ) ≤ θ.Vtp := hθ.Vtp_ge
  have hVtp2 : θ.Vtp ≤ 0.60 := hθ.Vtp_le
  have hVtn : (0.45 : ℝ) ≤ θ.Vtn := hθ.Vtn_ge
  -- the balance at an instant `t`, with the right derivative identified as 0.1
  have key : ∀ t ∈ Ico (0 : ℝ) 1, ∃ c : ℝ, 5 ≤ c ∧ c ≤ 20 ∧
      |c * 0.1 - Inet θ 0 (vRamp t)| ≤ 2 := by
    intro t ht
    obtain ⟨v', c, hd, hc1, hc2, hb⟩ := h.incl t ht
    have e : v' = 0.1 := by
      have h1 := hd.derivWithin (uniqueDiffWithinAt_Ici t)
      have h2 := (hasDeriv_vRamp t).derivWithin (uniqueDiffWithinAt_Ici t)
      rw [← h1, h2]
    have hs : vRamp t ∈ illustrative.Safe := by
      simp only [Design.Safe, illustrative, mem_Icc, vRamp]
      constructor <;> linarith [ht.1, ht.2]
    have hb' := hb hs
    rw [e] at hb'
    exact ⟨c, by simpa [illustrative] using hc1, by simpa [illustrative] using hc2,
      by simpa [illustrative] using hb'⟩
  -- the device current of a FIXED member at the two node voltages 1.65 and 1.74
  have hI : ∀ x : ℝ, 1.05 ≤ x → Inet θ 0 x
      = θ.kp / 2 * (psq (θ.VDD - 0 - θ.Vtp) - (x - 0 - θ.Vtp) ^ 2) := by
    intro x hx
    have hn : In θ 0 x = 0 := In_cutoff (by linarith) (by linarith)
    rw [Inet, hn, Ip, psq_of_nonneg (by linarith : (0 : ℝ) ≤ x - 0 - θ.Vtp)]
    ring
  obtain ⟨c0, hc0a, hc0b, hb0⟩ := key 0 ⟨le_rfl, by norm_num⟩
  obtain ⟨c1, hc1a, hc1b, hb1⟩ := key 0.9 ⟨by norm_num, by norm_num⟩
  have e0 : vRamp 0 = 1.65 := by norm_num [vRamp]
  have e1 : vRamp 0.9 = 1.74 := by norm_num [vRamp]
  rw [e0, hI 1.65 (by norm_num)] at hb0
  rw [e1, hI 1.74 (by norm_num)] at hb1
  have a0 := (abs_le.mp hb0).1
  have a1 := (abs_le.mp hb1).2
  nlinarith [psq_nonneg (θ.VDD - 0 - θ.Vtp)]

/-! ## The sandwich is satisfiable in a non-trivial case -/

/-- Nominal square law with first-order channel-length modulation on the NMOS. -/
noncomputable def Jclm (lam u x : ℝ) : ℝ := Ip nominal u x - In nominal u x * (1 + lam * x)

theorem clm_is_pointwise_box_member (u x : ℝ) (hx : x ∈ illustrative.Safe) :
    ∃ θ : Params, illustrative.InBox θ ∧ Jclm 0.05 u x = Inet θ u x := by
  have hx' : -0.10 ≤ x ∧ x ≤ 2.08 := by simpa [Design.Safe, illustrative] using hx
  refine ⟨⟨1.8, 200 * (1 + 0.05 * x), 100, 0.5, 0.5⟩, ?_, ?_⟩
  · constructor <;> norm_num [illustrative] <;> linarith [hx'.1, hx'.2]
  · simp only [Jclm, Inet, Ip, In, nominal]
    ring

/-- No FIXED box member is within `eps` of the modulated law on the safe domain
(so the 1880a36 form of the obligation could not be met). -/
theorem clm_not_within_eps_of_any_fixed_member (θ : Params) (hθ : illustrative.InBox θ) :
    ¬ ∀ x ∈ illustrative.Safe, |Jclm 0.05 1.8 x - Inet θ 1.8 x| ≤ illustrative.eps := by
  intro h
  have hVDD : θ.VDD ≤ 1.98 := hθ.VDD_le
  have hVtp : (0.45 : ℝ) ≤ θ.Vtp := hθ.Vtp_ge
  have hVtn : (0.45 : ℝ) ≤ θ.Vtn := hθ.Vtn_ge
  have hVtn' : θ.Vtn ≤ 0.60 := hθ.Vtn_le
  have flat : ∀ x : ℝ, 1.35 ≤ x → x ≤ 2.08 →
      Inet θ 1.8 x = -(θ.kn / 2 * (1.8 - θ.Vtn) ^ 2) := by
    intro x h1 h2
    have hp : Ip θ 1.8 x = 0 := by
      unfold Ip
      rw [psq_of_nonpos (by linarith), psq_of_nonpos (by linarith)]
      ring
    have hn : In θ 1.8 x = θ.kn / 2 * (1.8 - θ.Vtn) ^ 2 := In_sat (by linarith) (by linarith)
    rw [Inet, hp, hn]; ring
  have jat : ∀ x : ℝ, 1.35 ≤ x → x ≤ 2.08 → Jclm 0.05 1.8 x = -(169 * (1 + 0.05 * x)) := by
    intro x h1 h2
    have hp : Ip nominal 1.8 x = 0 := by
      have e1 : psq ((1.8 : ℝ) - 1.8 - 0.5) = 0 := psq_of_nonpos (by norm_num)
      have e2 : psq (x - 1.8 - 0.5) = 0 := psq_of_nonpos (by linarith)
      simp only [Ip, nominal, e1, e2]
      norm_num
    have hn : In nominal 1.8 x = 169 := by
      have e : In nominal 1.8 x = nominal.kn / 2 * (1.8 - nominal.Vtn) ^ 2 :=
        In_sat (by norm_num [nominal]) (by norm_num [nominal]; linarith)
      rw [e]; norm_num [nominal]
    rw [Jclm, hp, hn]; ring
  have h1 := h 1.35 (by norm_num [Design.Safe, illustrative])
  have h2 := h 2.08 (by norm_num [Design.Safe, illustrative])
  rw [jat 1.35 le_rfl (by norm_num), flat 1.35 le_rfl (by norm_num)] at h1
  rw [jat 2.08 (by norm_num) le_rfl, flat 2.08 (by norm_num) le_rfl] at h2
  have heps : illustrative.eps = 2 := by norm_num [illustrative]
  rw [heps] at h1 h2
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).1
  norm_num at a1 a2
  linarith

/-- **The modulated inverter is covered by the library's new obligation**, with
`εm = 0` and the whole `eps = 2` left for the disturbance. -/
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
  have h : IsTrajectory illustrative u v a b :=
    IsTrajectory.of_sandwich (J := fun t x => Jclm 0.05 (u t) x) (w := w) (εm := 0) (εw := 2)
      le_rfl (by norm_num [illustrative])
      (fun t _ x hx => by
        obtain ⟨θ, hθ, hJ⟩ := clm_is_pointwise_box_member (u t) x hx
        exact ⟨θ, θ, hθ, hθ, by simp [hJ], by simp [hJ]⟩)
      hw hcont
      (fun t ht => by
        obtain ⟨v', c, hd, hc1, hc2, he⟩ := hode t ht
        exact ⟨v', c, hd, by simpa [illustrative] using hc1,
          by simpa [illustrative] using hc2, he⟩)
  exact illustrative_guarantee u v a b h h0

end Review.D02

#print axioms Review.D02.new_iff_reviewer_definition
#print axioms Review.D02.fixed_implies_new
#print axioms Review.D02.supply_tracking_is_new_trajectory
#print axioms Review.D02.supply_tracking_not_fixed
#print axioms Review.D02.clm_not_within_eps_of_any_fixed_member
#print axioms Review.D02.clm_guarantee

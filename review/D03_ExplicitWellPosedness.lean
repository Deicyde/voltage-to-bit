import VoltageToBit

/-!
# Probe D03 (workstream E, Part 2, commit 9b13e95): the ODE form, restated without project definitions

Port and extension of `P06_ExplicitRestatement.lean` to the second snapshot.
The reviewer's own statement of what the prose (`docs/interface.md` rev. 3, §6,
and `README.md`) says about the illustrative instance in ODE form, written with
Mathlib notions and explicit numbers only, and derived from the library:

for every constant parameter point of the box, every capacitance function with
values in `[5, 20]` that is Lipschitz on `[-0.10, 2.08]`, all continuous `u`,
`w` with `|w| ≤ 2` on `[a, b]`, and every initial state in `[-0.10, 2.08]`:

1. a solution of `Cf(v) v' = I_net(u, v) + w` exists on all of `[a, b]`;
2. any two solutions with that initial state agree on `[a, b]`;
3. every solution stays in `[-0.10, 2.08]`, meets the rise deadline 3.43 and
   the fall deadline 2.57, and, if it starts at or below `VDD + 0.10`, stays
   at or below `VDD + 0.10` (the supply-relative safe domain).

All three parts are closed by library theorems (`exists_solution`,
`solution_unique`, `IsTrajectory.of_ode`, `illustrative_guarantee`,
`illustrative_safe_atSupply`) after definitional unfolding. So the new
existence, uniqueness and supply-relative statements compose the way the
prose says (the attack on their meaning failed).
-/

open Set
open VoltageToBit VoltageToBit.Examples

namespace Review.D03

/-- Net current into the output node, with `max` only. -/
noncomputable def InetX (VDD kn kp Vtn Vtp u v : ℝ) : ℝ :=
  kp / 2 * ((max (VDD - u - Vtp) 0) ^ 2 - (max (v - u - Vtp) 0) ^ 2)
    - kn / 2 * ((max (u - Vtn) 0) ^ 2 - (max (u - v - Vtn) 0) ^ 2)

/-- `v` solves the node equation on `[a, b]`. -/
def Solves (VDD kn kp Vtn Vtp : ℝ) (Cf u w : ℝ → ℝ) (a b : ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc a b,
    HasDerivWithinAt v ((InetX VDD kn kp Vtn Vtp (u t) (v t) + w t) / Cf (v t)) (Icc a b) t

theorem explicit_well_posed
    (VDD kn kp Vtn Vtp : ℝ)
    (hVDD : 1.62 ≤ VDD ∧ VDD ≤ 1.98) (hkn : 160 ≤ kn ∧ kn ≤ 240) (hkp : 80 ≤ kp ∧ kp ≤ 120)
    (hVtn : 0.45 ≤ Vtn ∧ Vtn ≤ 0.60) (hVtp : 0.45 ≤ Vtp ∧ Vtp ≤ 0.60)
    (Cf : ℝ → ℝ) (hCf : ∀ x, 5 ≤ Cf x ∧ Cf x ≤ 20) (Kc : ℝ)
    (hLip : ∀ x y : ℝ, -0.10 ≤ x ∧ x ≤ 2.08 → -0.10 ≤ y ∧ y ≤ 2.08 →
      |Cf x - Cf y| ≤ Kc * |x - y|)
    (u w : ℝ → ℝ) (hu : Continuous u) (hw : Continuous w) (a b : ℝ) (hab : a ≤ b)
    (hwb : ∀ t ∈ Icc a b, |w t| ≤ 2) (v₀ : ℝ) (hv₀ : -0.10 ≤ v₀ ∧ v₀ ≤ 2.08) :
    (∃ v : ℝ → ℝ, v a = v₀ ∧ Solves VDD kn kp Vtn Vtp Cf u w a b v) ∧
    (∀ v₁ v₂ : ℝ → ℝ, v₁ a = v₀ → v₂ a = v₀ → Solves VDD kn kp Vtn Vtp Cf u w a b v₁ →
      Solves VDD kn kp Vtn Vtp Cf u w a b v₂ → ∀ t ∈ Icc a b, v₁ t = v₂ t) ∧
    (∀ v : ℝ → ℝ, v a = v₀ → Solves VDD kn kp Vtn Vtp Cf u w a b v →
      (∀ t ∈ Icc a b, -0.10 ≤ v t ∧ v t ≤ 2.08) ∧
      (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
        ∀ t ∈ Icc s e, s + 3.43 ≤ t → 1.35 ≤ v t) ∧
      (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
        ∀ t ∈ Icc s e, s + 2.57 ≤ t → v t ≤ 0.25) ∧
      (v₀ ≤ VDD + 0.10 → ∀ t ∈ Icc a b, v t ≤ VDD + 0.10)) := by
  have hadm := illustrative_admissible
  have hθ : illustrative.InBox ⟨VDD, kn, kp, Vtn, Vtp⟩ :=
    ⟨hVDD.1, hVDD.2, hkn.1, hkn.2, hkp.1, hkp.2, hVtn.1, hVtn.2, hVtp.1, hVtp.2⟩
  have hCf' : ∀ x, illustrative.Clo ≤ Cf x ∧ Cf x ≤ illustrative.Chi := hCf
  have hLip' : ∀ x ∈ illustrative.Safe, ∀ y ∈ illustrative.Safe,
      |Cf x - Cf y| ≤ Kc * |x - y| := fun x hx y hy => hLip x y hx hy
  have hwb' : ∀ t ∈ Icc a b, |w t| ≤ illustrative.eps := hwb
  have hv₀' : v₀ ∈ illustrative.Safe := hv₀
  have hCpos : ∀ x, 0 < Cf x := fun x => by linarith [(hCf x).1]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv0, -, hode⟩ :=
      exists_solution hadm hθ (Cf := Cf) (Kc := Kc) (fun x => (hCf' x).1) hLip' hu hw hab hwb' hv₀'
    exact ⟨v, hv0, hode⟩
  · intro v₁ v₂ e1 e2 h1 h2 t ht
    exact solution_unique hadm hθ (Cf := Cf) hCf' hLip' hu hw hwb' h1 h2 (by rw [e1, e2])
      (by rw [e1]; exact hv₀') ht
  · intro v hv0 hode
    have hcont : ContinuousOn v (Icc a b) := fun t ht => (hode t ht).continuousWithinAt
    have hode' : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
        Cf (v t) * v' = Inet ⟨VDD, kn, kp, Vtn, Vtp⟩ (u t) (v t) + w t := fun t ht =>
      ⟨_, (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht), by
        show Cf (v t) * ((Inet ⟨VDD, kn, kp, Vtn, Vtp⟩ (u t) (v t) + w t) / Cf (v t)) = _
        have := (hCpos (v t)).ne'
        field_simp⟩
    have htraj : IsTrajectory illustrative u v a b :=
      IsTrajectory.of_ode hθ (Cf := Cf) (w := w) hCf'
        (fun t ht => hwb' t (Ico_subset_Icc_self ht)) hcont hode'
    obtain ⟨hs, hr, hf⟩ := illustrative_guarantee u v a b htraj (by rw [hv0]; exact hv₀)
    refine ⟨hs, hr, hf, fun htop t ht => ?_⟩
    have := illustrative_safe_atSupply ⟨VDD, kn, kp, Vtn, Vtp⟩ hθ Cf w u v a b hCf
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont hode'
      (by rw [hv0]; exact ⟨hv₀.1, htop⟩) t ht
    exact this.2

end Review.D03

#print axioms Review.D03.explicit_well_posed

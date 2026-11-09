import VoltageToBit

/-!
# Probe P06 (workstream E): the headline result restated without project definitions

An attack on meaning: do `Design`, `Admissible`, `InBox`, `IsTrajectory`,
`Safe`, `Inet`, `psq`, `decode` hide anything? Here the reviewer writes the
claim for the illustrative instance again, from the prose of
`docs/interface.md`, using only Mathlib notions (`max`, `|·|`, `Set.Icc`,
`Set.Ico`, `ContinuousOn`, `HasDerivWithinAt`, `Continuous`) and explicit
numbers, and derives it from the library theorems.

* `InetX`: the square-law current written with `max` only; `InetX_eq` shows it
  is the library's `Inet` by `rfl`.
* `explicit_inclusion_guarantee`: the differential-inclusion form of the
  guarantee.
* `explicit_end_to_end`: for every parameter choice in the box, every constant
  capacitance in `[5, 20]`, all continuous `u` and `w` with `|w| ≤ 2` on
  `[a, b]`, and every initial state in `[-0.10, 2.08]`: (1) a solution of
  `C v' = I_net(u, v) + w` exists on all of `[a, b]`, and (2) EVERY solution
  stays in `[-0.10, 2.08]`, is `≥ 1.35` from `s + 3.43` on while `u ≤ 0.40`
  holds since `s`, and is `≤ 0.25` from `s + 2.57` on while `u ≥ 1.25` holds
  since `s`.
* `explicit_decoding`: the three-valued decoder written out.
* `Ich_antisymm`, `In_eq_Ich`, `Ip_eq_Ich`: both transistors are instances of
  one channel formula that is antisymmetric in its two channel terminals.

Both theorems are closed by the library's theorems after constructing the
project structures by definitional unfolding only. This is evidence that the
statements mean what the prose says (the attack failed).
-/

open Set
open VoltageToBit VoltageToBit.Examples

namespace Review.P06

/-- Net current into the output node, with `max` only. -/
noncomputable def InetX (VDD kn kp Vtn Vtp u v : ℝ) : ℝ :=
  kp / 2 * ((max (VDD - u - Vtp) 0) ^ 2 - (max (v - u - Vtp) 0) ^ 2)
    - kn / 2 * ((max (u - Vtn) 0) ^ 2 - (max (u - v - Vtn) 0) ^ 2)

theorem InetX_eq (VDD kn kp Vtn Vtp u v : ℝ) :
    InetX VDD kn kp Vtn Vtp u v = Inet ⟨VDD, kn, kp, Vtn, Vtp⟩ u v := rfl

theorem explicit_inclusion_guarantee
    (VDD kn kp Vtn Vtp : ℝ)
    (hVDD : 1.62 ≤ VDD ∧ VDD ≤ 1.98) (hkn : 160 ≤ kn ∧ kn ≤ 240) (hkp : 80 ≤ kp ∧ kp ≤ 120)
    (hVtn : 0.45 ≤ Vtn ∧ Vtn ≤ 0.60) (hVtp : 0.45 ≤ Vtp ∧ Vtp ≤ 0.60)
    (u v : ℝ → ℝ) (a b : ℝ)
    (hcont : ContinuousOn v (Icc a b))
    (hincl : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧ 5 ≤ c ∧ c ≤ 20 ∧
      (-0.10 ≤ v t ∧ v t ≤ 2.08 → |c * v' - InetX VDD kn kp Vtn Vtp (u t) (v t)| ≤ 2))
    (h0 : -0.10 ≤ v a ∧ v a ≤ 2.08) :
    (∀ t ∈ Icc a b, -0.10 ≤ v t ∧ v t ≤ 2.08) ∧
    (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
      ∀ t ∈ Icc s e, s + 3.43 ≤ t → 1.35 ≤ v t) ∧
    (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
      ∀ t ∈ Icc s e, s + 2.57 ≤ t → v t ≤ 0.25) := by
  have hθ : illustrative.InBox ⟨VDD, kn, kp, Vtn, Vtp⟩ :=
    ⟨hVDD.1, hVDD.2, hkn.1, hkn.2, hkp.1, hkp.2, hVtn.1, hVtn.2, hVtp.1, hVtp.2⟩
  have htraj : IsTrajectory illustrative ⟨VDD, kn, kp, Vtn, Vtp⟩ u v a b :=
    ⟨hcont, fun t ht => by
      obtain ⟨v', c, hd, hc1, hc2, hb⟩ := hincl t ht
      exact ⟨v', c, hd, hc1, hc2, fun hs => hb hs⟩⟩
  exact illustrative_guarantee _ hθ u v a b htraj h0

theorem explicit_end_to_end
    (VDD kn kp Vtn Vtp C : ℝ)
    (hVDD : 1.62 ≤ VDD ∧ VDD ≤ 1.98) (hkn : 160 ≤ kn ∧ kn ≤ 240) (hkp : 80 ≤ kp ∧ kp ≤ 120)
    (hVtn : 0.45 ≤ Vtn ∧ Vtn ≤ 0.60) (hVtp : 0.45 ≤ Vtp ∧ Vtp ≤ 0.60) (hC : 5 ≤ C ∧ C ≤ 20)
    (u w : ℝ → ℝ) (hu : Continuous u) (hw : Continuous w) (a b : ℝ) (hab : a ≤ b)
    (hwb : ∀ t ∈ Icc a b, |w t| ≤ 2) (v₀ : ℝ) (hv₀ : -0.10 ≤ v₀ ∧ v₀ ≤ 2.08) :
    (∃ v : ℝ → ℝ, v a = v₀ ∧ ∀ t ∈ Icc a b,
        HasDerivWithinAt v ((InetX VDD kn kp Vtn Vtp (u t) (v t) + w t) / C) (Icc a b) t) ∧
    (∀ v : ℝ → ℝ, v a = v₀ →
      (∀ t ∈ Icc a b,
        HasDerivWithinAt v ((InetX VDD kn kp Vtn Vtp (u t) (v t) + w t) / C) (Icc a b) t) →
      (∀ t ∈ Icc a b, -0.10 ≤ v t ∧ v t ≤ 2.08) ∧
      (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
        ∀ t ∈ Icc s e, s + 3.43 ≤ t → 1.35 ≤ v t) ∧
      (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
        ∀ t ∈ Icc s e, s + 2.57 ≤ t → v t ≤ 0.25)) := by
  have hadm := illustrative_admissible
  have hθ : illustrative.InBox ⟨VDD, kn, kp, Vtn, Vtp⟩ :=
    ⟨hVDD.1, hVDD.2, hkn.1, hkn.2, hkp.1, hkp.2, hVtn.1, hVtn.2, hVtp.1, hVtp.2⟩
  have hC1 : illustrative.Clo ≤ C := hC.1
  have hC2 : C ≤ illustrative.Chi := hC.2
  have hCpos : 0 < C := by linarith [hC.1]
  have hwb' : ∀ t ∈ Icc a b, |w t| ≤ illustrative.eps := hwb
  have hv₀' : v₀ ∈ illustrative.Safe := hv₀
  constructor
  · obtain ⟨v, hv0, -, hode⟩ := exists_solution hadm hθ hC1 hu hw hab hwb' hv₀'
    exact ⟨v, hv0, hode⟩
  · intro v hv0 hode
    have htraj : IsTrajectory illustrative ⟨VDD, kn, kp, Vtn, Vtp⟩ u v a b :=
      IsTrajectory.of_ode (Cf := fun _ => C) (w := w) (fun _ => ⟨hC1, hC2⟩)
        (fun t ht => hwb' t (Ico_subset_Icc_self ht))
        (fun t ht => (hode t ht).continuousWithinAt)
        (fun t ht => ⟨_, (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht), by
            show C * ((Inet ⟨VDD, kn, kp, Vtn, Vtp⟩ (u t) (v t) + w t) / C) = _
            field_simp⟩)
    exact illustrative_guarantee _ hθ u v a b htraj (by rw [hv0]; exact hv₀)

/-- The decoder, written out: low at or below `0.25`, high at or above `1.35`,
undefined strictly in between. -/
theorem explicit_decoding (x : ℝ) :
    (illustrative.decodeOut x = some false ↔ x ≤ 0.25) ∧
    (illustrative.decodeOut x = some true ↔ 1.35 ≤ x) ∧
    (illustrative.decodeOut x = none ↔ 0.25 < x ∧ x < 1.35) := by
  have hoo : (0.25 : ℝ) < 1.35 := by norm_num
  have e : illustrative.decodeOut x = decode 0.25 1.35 x := rfl
  rw [e]
  exact ⟨decode_eq_false_iff, decode_eq_true_iff hoo, decode_eq_none_iff⟩

/-! ## The device law as one symmetric channel formula -/

/-- Square-law channel current of an n-type device with gate `g`, flowing from
terminal `d` to terminal `s`. -/
noncomputable def Ich (k Vt g s d : ℝ) : ℝ := k / 2 * (psq (g - s - Vt) - psq (g - d - Vt))

/-- Exchanging the two channel terminals reverses the current (the claim
"antisymmetric under source/drain exchange" of `Model/Device.lean`, for which
the library has no lemma). -/
theorem Ich_antisymm (k Vt g s d : ℝ) : Ich k Vt g d s = -Ich k Vt g s d := by
  unfold Ich; ring

/-- The NMOS of the inverter: gate `u`, one terminal at ground, the other at the output. -/
theorem In_eq_Ich (θ : Params) (u v : ℝ) : In θ u v = Ich θ.kn θ.Vtn u 0 v := by
  unfold In Ich; rw [sub_zero]

/-- The PMOS of the inverter is the same formula with all voltages negated:
gate `u`, one terminal at the supply, the other at the output. -/
theorem Ip_eq_Ich (θ : Params) (u v : ℝ) :
    Ip θ u v = Ich θ.kp θ.Vtp (-u) (-θ.VDD) (-v) := by
  have e1 : -u - -θ.VDD - θ.Vtp = θ.VDD - u - θ.Vtp := by ring
  have e2 : -u - -v - θ.Vtp = v - u - θ.Vtp := by ring
  unfold Ip Ich; rw [e1, e2]

end Review.P06

#print axioms Review.P06.explicit_inclusion_guarantee
#print axioms Review.P06.explicit_end_to_end
#print axioms Review.P06.explicit_decoding
#print axioms Review.P06.Ip_eq_Ich

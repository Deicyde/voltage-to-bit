import VoltageToBit

/-!
# Probe D04 (workstream E, Part 2, commit 9b13e95): AtSupply, Chain, reverse-operation lemmas

## A. The extra condition `eps < RhiN'` of `Proofs/AtSupply.lean`

`Design.Admissible.atSupply` and `solution_safe_atSupply` carry one hypothesis
beyond admissibility, `eps < RhiN'`. Attack: is it a real extra restriction?

* `RhiN'_eq_RhiN`: for every admissible record with `0 ≤ Vtnhi + Vtphi`
  (in particular whenever the thresholds are nonnegative, i.e. for every
  enhancement-mode record) `RhiN' = RhiN`.
* `atSupply_condition_is_automatic`: hence `eps < RhiN'` already follows from
  admissibility (`hiN`) there, and
* `solution_safe_atSupply_of_admissible`: the supply-relative safe-domain
  theorem holds with NO extra numeric condition for such records.

So the condition is not smuggling anything, and for physically meaningful
records it is redundant. It can only bite for records with negative threshold
sums, which `Admissible` does not exclude (it has no positivity condition on
thresholds although `docs/interface.md` §3 says `V_tp > 0`).

## B. The two-stage corollary has a witness

`Proofs/Chain.lean` proves four implications and no existence statement.
`chain_witness` builds an actual two-stage run of the illustrative record: both
stages start at 1.0 V (undefined), the first input is held at 0 V, and the
second output is valid-low throughout `[6, 10]`. So the hypotheses of
`chain_restores_low` can be met and its conclusion is about a nonempty window.

## C. The reverse-operation lemmas pin the exchanged-terminal textbook law

`shForward` is the reviewer's own textbook piecewise law of one device in
forward operation, as a function of `(V_GS, V_DS)`. `In_forward`, `In_reverse`,
`Ip_forward`, `Ip_reverse` show that the library's twelve region lemmas are
exhaustive and say: forward law when the output node is inside the rails, and
MINUS the forward law in the exchanged frame when it is outside
(`V_GS = u - v`, `V_DS = -v` for the NMOS below ground; `V_SG = v - u`,
`V_SD = v - VDD` for the PMOS above the supply).
-/

open Set
open VoltageToBit VoltageToBit.Examples

namespace Review.D04

/-! ## A. AtSupply -/

theorem RhiN'_eq_RhiN {D : Design} (hD : D.Admissible) (hV : 0 ≤ D.Vtnhi + D.Vtphi) :
    D.RhiN' = D.RhiN := by
  have hδ : 0 ≤ D.Vhi - D.VDDhi := by linarith [hD.Vhi_ge]
  -- `hiP` forces the first argument of `RhiP` to be positive
  have hpos : 0 < D.VDDlo - D.uHi - D.Vtphi + (D.Vhi - D.VDDhi) := by
    by_contra hneg
    push Not at hneg
    have h1 := hD.hiP
    unfold Design.RhiP at h1
    rw [psq_of_nonpos hneg, psq_of_nonpos (by linarith), sub_self, mul_zero] at h1
    linarith [hD.eps_nonneg]
  have hle := hD.VDD_le
  unfold Design.RhiN' Design.RhiN
  rw [psq_of_nonpos (by linarith : D.uHi - (D.VDDlo + (D.Vhi - D.VDDhi)) - D.Vtnhi ≤ 0),
    psq_of_nonpos (by linarith : D.uHi - D.Vhi - D.Vtnhi ≤ 0)]

theorem atSupply_condition_is_automatic {D : Design} (hD : D.Admissible)
    (hV : 0 ≤ D.Vtnhi + D.Vtphi) : D.eps < D.RhiN' := by
  rw [RhiN'_eq_RhiN hD hV]
  exact hD.hiN

/-- The supply-relative safe domain without any extra numeric condition, for
records whose largest thresholds have a nonnegative sum. -/
theorem solution_safe_atSupply_of_admissible {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}
    {Cf w : ℝ → ℝ} (hD : D.Admissible) (hV : 0 ≤ D.Vtnhi + D.Vtphi) (hθ : D.InBox θ)
    (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ D.eps) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet θ (u t) (v t) + w t)
    (h0 : v a ∈ Icc D.Vlo (θ.VDD + (D.Vhi - D.VDDhi))) :
    ∀ t ∈ Icc a b, v t ∈ Icc D.Vlo (θ.VDD + (D.Vhi - D.VDDhi)) :=
  solution_safe_atSupply hD (atSupply_condition_is_automatic hD hV) hθ hCf hw hcont hode h0

/-- More generally than the ODE statement of the library: every trajectory of
the restricted record (parameters other than the supply may still move in the
box) stays in the supply-relative domain. -/
theorem trajectory_safe_atSupply {D : Design} (hD : D.Admissible) (hN' : D.eps < D.RhiN')
    {V0 : ℝ} (h1 : D.VDDlo ≤ V0) (h2 : V0 ≤ D.VDDhi) {u v : ℝ → ℝ} {a b : ℝ}
    (h : IsTrajectory (D.atSupply V0) u v a b)
    (h0 : v a ∈ Icc D.Vlo (V0 + (D.Vhi - D.VDDhi))) :
    ∀ t ∈ Icc a b, v t ∈ Icc D.Vlo (V0 + (D.Vhi - D.VDDhi)) :=
  h.safe (hD.atSupply h1 h2 hN') h0

/-- The deadlines of the restricted record are no worse than those of the
record (they are what the library's theorems give for a run at supply `V0`). -/
theorem atSupply_Iup_ge {D : Design} (hD : D.Admissible) {V0 : ℝ} (h1 : D.VDDlo ≤ V0) (c : ℝ) :
    D.Iup c ≤ (D.atSupply V0).Iup c := by
  show D.kplo / 2 * (psq (D.VDDlo - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi))
      - D.knhi / 2 * psq (D.VIL - D.Vtnlo)
    ≤ D.kplo / 2 * (psq (V0 - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi))
      - D.knhi / 2 * psq (D.VIL - D.Vtnlo)
  have hm : psq (D.VDDlo - D.VIL - D.Vtphi) ≤ psq (V0 - D.VIL - D.Vtphi) :=
    psq_mono (by linarith)
  have := mul_le_mul_of_nonneg_left hm (by linarith [hD.kp_pos] : (0 : ℝ) ≤ D.kplo / 2)
  linarith

/-! ## B. Chain -/

theorem chain_witness :
    ∃ u v₁ v₂ : ℝ → ℝ, (∀ t, u t ≤ illustrative.VIL) ∧
      IsTrajectory illustrative u v₁ 0 10 ∧ IsTrajectory illustrative v₁ v₂ 0 10 ∧
      v₁ 0 = 1 ∧ v₂ 0 = 1 ∧ ∀ t ∈ Icc (6 : ℝ) 10, v₂ t ≤ 0.25 := by
  have hadm := illustrative_admissible
  obtain ⟨v₁, hv₁0, h₁⟩ := illustrative_exists_const nominal nominal_inBox 10 (by norm_num)
    (fun _ => 0) (fun _ => 0) continuous_const continuous_const 0 10 (by norm_num)
    (fun t _ => by norm_num) 1 (by norm_num)
  -- a globally continuous copy of the first output, to feed the existence theorem
  have hcl : Continuous (clamp 0 10) := by unfold clamp; fun_prop
  have hũ : Continuous (fun t => v₁ (clamp 0 10 t)) :=
    h₁.cont.comp_continuous hcl (fun t => clamp_mem (by norm_num) t)
  obtain ⟨v₂, hv₂0, h₂'⟩ := illustrative_exists_const nominal nominal_inBox 10 (by norm_num)
    (fun t => v₁ (clamp 0 10 t)) (fun _ => 0) hũ continuous_const 0 10 (by norm_num)
    (fun t _ => by norm_num) 1 (by norm_num)
  have h₂ : IsTrajectory illustrative v₁ v₂ 0 10 :=
    h₂'.congr_input (fun t ht => by
      show v₁ (clamp 0 10 t) = v₁ t
      rw [clamp_of_mem ⟨ht.1, ht.2.le⟩])
  have hs : (1 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  refine ⟨fun _ => 0, v₁, v₂, fun _ => by norm_num [illustrative], h₁, h₂, hv₁0, hv₂0,
    fun t ht => ?_⟩
  have := chain_restores_low hadm h₁ h₂ (by rw [hv₁0]; exact hs) (by rw [hv₂0]; exact hs)
    (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) t
    ⟨by linarith [ht.1], ht.2⟩
    (by linarith [ht.1, illustrative_tauUp_le, illustrative_tauDn_le])
  simpa [illustrative] using this

/-! ## C. Device law: forward and exchanged-terminal regions -/

/-- Textbook Shichman-Hodges law of one device in forward operation
(`vds ≥ 0`), as a function of gate-source and drain-source voltage. -/
noncomputable def shForward (k Vt vgs vds : ℝ) : ℝ :=
  if vgs ≤ Vt then 0
  else if vds ≤ vgs - Vt then k * ((vgs - Vt) * vds - vds ^ 2 / 2)
  else k / 2 * (vgs - Vt) ^ 2

theorem In_forward {θ : Params} {u v : ℝ} (hv : 0 ≤ v) :
    In θ u v = shForward θ.kn θ.Vtn u v := by
  unfold shForward
  split_ifs with h1 h2
  · exact In_cutoff h1 hv
  · exact In_triode hv h2
  · exact In_sat (le_of_not_ge h1) (le_of_not_ge h2)

theorem In_reverse {θ : Params} {u v : ℝ} (hv : v ≤ 0) :
    In θ u v = -shForward θ.kn θ.Vtn (u - v) (-v) := by
  unfold shForward
  split_ifs with h1 h2
  · rw [In_rev_cutoff hv h1, neg_zero]
  · exact In_rev_triode hv (by linarith)
  · exact In_rev_sat (by linarith [not_le.mp h2]) (le_of_not_ge h1)

theorem Ip_forward {θ : Params} {u v : ℝ} (hv : v ≤ θ.VDD) :
    Ip θ u v = shForward θ.kp θ.Vtp (θ.VDD - u) (θ.VDD - v) := by
  unfold shForward
  split_ifs with h1 h2
  · exact Ip_cutoff (by linarith) hv
  · exact Ip_triode hv (by linarith)
  · exact Ip_sat (by linarith [not_le.mp h1]) (by linarith [not_le.mp h2])

theorem Ip_reverse {θ : Params} {u v : ℝ} (hv : θ.VDD ≤ v) :
    Ip θ u v = -shForward θ.kp θ.Vtp (v - u) (v - θ.VDD) := by
  unfold shForward
  split_ifs with h1 h2
  · rw [Ip_rev_cutoff hv h1, neg_zero]
  · exact Ip_rev_triode hv (by linarith)
  · exact Ip_rev_sat (by linarith [not_le.mp h2]) (by linarith [not_le.mp h1])

end Review.D04

#print axioms Review.D04.RhiN'_eq_RhiN
#print axioms Review.D04.solution_safe_atSupply_of_admissible
#print axioms Review.D04.trajectory_safe_atSupply
#print axioms Review.D04.chain_witness
#print axioms Review.D04.In_reverse
#print axioms Review.D04.Ip_reverse

import VoltageToBit.Proofs.Guarantee

/-!
# What a higher-fidelity model must satisfy to be covered

`IsTrajectory.of_model_error` states the exact obligation that links the
square-law model to any other description of the same node: if the "true" net
current `J t x` differs from `Inet θ (u t) x` by at most `εm` **on the safe
domain**, and an additional disturbance is bounded by `εw`, with
`εm + εw ≤ eps`, then every solution of `c * v' = J t (v t) + w t` is a
trajectory, so every theorem about trajectories applies to it.

This is a statement about mathematics only. Whether a physical inverter, or a
SPICE model of one, satisfies the hypothesis `hJ` is an empirical question that
this repository does not settle. See `docs/assumptions.md`.

The hypothesis is needed only on the safe domain: the theorem
`IsTrajectory.safe` then shows the solution never leaves it, so no bound
outside the safe domain is ever used.
-/

namespace VoltageToBit

open Set

/-- **Model-error embedding.** A solution of a different current law that
stays within the error budget of the square-law model on the safe domain is a
trajectory of the uncertain inverter. -/
theorem IsTrajectory.of_model_error {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}
    {J : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {εm εw : ℝ} (hbudget : εm + εw ≤ D.eps)
    (hJ : ∀ t ∈ Ico a b, ∀ x ∈ D.Safe, |J t x - Inet θ (u t) x| ≤ εm)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ εw)
    (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      D.Clo ≤ c ∧ c ≤ D.Chi ∧ c * v' = J t (v t) + w t) :
    IsTrajectory D θ u v a b where
  cont := hcont
  incl := fun t ht => by
    obtain ⟨v', c, hd, hc1, hc2, he⟩ := hode t ht
    refine ⟨v', c, hd, hc1, hc2, fun hsafe => ?_⟩
    have h1 := hJ t ht (v t) hsafe
    have h2 := hw t ht
    have e : c * v' - Inet θ (u t) (v t) = (J t (v t) - Inet θ (u t) (v t)) + w t := by
      rw [he]; ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)

end VoltageToBit

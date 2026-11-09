import VoltageToBit

/-!
# Probe P08 (workstream E): the miswired control, for ALL trajectories

`miswired_counterexample` in `Examples/NegativeControls.lean` exhibits ONE
trajectory of the exchanged-transistor network (the constant 0.3 V, with the
input at 0 V) that never becomes valid-high. A sceptic may ask whether that is
a cherry-picked equilibrium.

`miswired_never_high` answers this for the same network, the same nominal
parameters, the same capacitance range `[5, 20]` and the same error bound
`2`: for EVERY input that is valid-low throughout and EVERY trajectory whose
output starts below `VOH = 1.35 V`, the output stays below `1.35 V` at all
times. So the miswired network does not merely admit a failing run; it has no
succeeding run.

Scope: this is about the function `InetSwapped`, which is the library's model
of the miswired network (checked here against the device formula by hand:
NMOS with drain at the supply and source at the output, PMOS with source at
the output and drain at ground). The library has no netlist layer, so no
control can show that the *checker* would notice a miswired design: topology
is fixed inside `Inet`.
-/

open Set
open VoltageToBit VoltageToBit.Examples

namespace Review.P08

/-- With a valid-low input, at any level `L ≥ 1.2` the miswired network pulls
the node DOWN by at least `50 (L - 0.9)² ≥ 4.5 µA`. -/
theorem InetSwapped_le {u L : ℝ} (hu : u ≤ 0.40) (hL1 : 1.2 ≤ L) :
    InetSwapped nominal u L ≤ -(50 * (L - 0.9) ^ 2) := by
  have e1 : psq (u - L - 0.5) = 0 := psq_of_nonpos (by linarith)
  have e2 : psq (u - 1.8 - 0.5) = 0 := psq_of_nonpos (by linarith)
  have e3 : psq (L - 0.40 - 0.5) - psq ((0 : ℝ) - 0.40 - 0.5)
      ≤ psq (L - u - 0.5) - psq (0 - u - 0.5) :=
    psq_sub_le_psq_sub (by linarith) (by linarith) (by linarith)
  rw [psq_of_nonneg (by linarith : (0 : ℝ) ≤ L - 0.40 - 0.5),
    psq_of_nonpos (by norm_num : (0 : ℝ) - 0.40 - 0.5 ≤ 0)] at e3
  simp only [InetSwapped, nominal, e1, e2]
  nlinarith

/-- **The miswired network never produces a valid-high output from a valid-low
input**, for every trajectory that starts below `VOH`. -/
theorem miswired_never_high {u v : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn v (Icc a b))
    (hincl : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      (5 : ℝ) ≤ c ∧ c ≤ 20 ∧ |c * v' - InetSwapped nominal (u t) (v t)| ≤ 2)
    (hu : ∀ t ∈ Ico a b, u t ≤ 0.40) (h0 : v a < 1.35) :
    ∀ t ∈ Icc a b, v t < 1.35 := by
  -- a barrier level strictly below 1.35 that the initial state does not exceed
  set L : ℝ := max (v a) 1.2 with hL
  have hL1 : 1.2 ≤ L := le_max_right _ _
  have hL2 : L < 1.35 := max_lt h0 (by norm_num)
  have hder : ∀ t ∈ Ico a b, HasDerivWithinAt v (rderiv v t) (Ici t) t := by
    intro t ht
    obtain ⟨v', c, hd, -⟩ := hincl t ht
    exact hd.differentiableWithinAt.hasDerivWithinAt
  have hbar : ∀ t ∈ Icc a b, v t ≤ L := by
    refine barrier_le hcont hder (le_max_left _ _) ?_
    intro s hs hvs
    obtain ⟨v', c, hd, hc1, hc2, hb⟩ := hincl s hs
    have hv' : rderiv v s = v' := hd.derivWithin (uniqueDiffWithinAt_Ici s)
    rw [hvs] at hb
    have hI := InetSwapped_le (hu s hs) hL1
    have hsq : (0.09 : ℝ) ≤ (L - 0.9) ^ 2 := by nlinarith
    have hneg : c * v' < 0 := by linarith [(abs_le.mp hb).2]
    rw [hv']
    by_contra hpos
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ c) (not_lt.mp hpos)
    linarith
  intro t ht
  exact lt_of_le_of_lt (hbar t ht) hL2

end Review.P08

#print axioms Review.P08.miswired_never_high

import VoltageToBit.Proofs.NonVacuity

/-!
# Two stages in series: the output bit is usable as an input bit

A corollary of the single-inverter guarantee, included because it is the point
of the threshold ordering `VOL ≤ VIL < VIH ≤ VOH`: a valid output of one stage
is a valid input of the next, so the digital abstraction composes.

The first stage has design `D₁`, the second `D₂`; compatibility of the two is
the pair of inequalities `D₂.VIH ≤ D₁.VOH` and `D₁.VOL ≤ D₂.VIL`. For two
copies of one admissible design these hold by the static discipline
(`chain_restores_low`, `chain_restores_high`).

Modelling caveat. Each stage is still the one-node model. The gate capacitance
of the second stage and any coupling between its input and its output are not
modelled as extra state; they are covered only if the stages' capacitance
bounds and error bounds `eps` contain them. That is an assumption about the
environment, not something proved here.

For the illustrative record the assumption is not physically plausible. The
only bounds the library has on the first stage's output slew are about
29 V/ns rising and 58 V/ns falling, and they hold for first-stage inputs
confined to `[0, 0.40]` V and `[1.25, 1.98]` V (`rise_at_most`, `fall_at_most`,
`Examples.illustrative_max_rise_slew`, `Examples.illustrative_max_fall_slew`);
for inputs outside those ranges the slew has no bound. A second stage with
gate-drain capacitance `C_M` would therefore have to allow for a feedthrough
current of up to `58 · C_M` µA, which stays inside the 2 µA allowance only for
`C_M` below about 0.03 fF (a small inverter has 0.2 to 1 fF). Read the
corollary as a statement about two ideal one-node stages. See `docs/model.md`,
section 7.4.
-/

namespace VoltageToBit

open Set

variable {D₁ D₂ : Design} {u v₁ v₂ : ℝ → ℝ} {a b : ℝ}

/-- A valid-low input to the first stage becomes a valid-low output of the
second stage after `D₁.tauUp + D₂.tauDn`. -/
theorem chain_low (hD₁ : D₁.Admissible) (hD₂ : D₂.Admissible)
    (hcompat : D₂.VIH ≤ D₁.VOH)
    (h₁ : IsTrajectory D₁ u v₁ a b) (h₂ : IsTrajectory D₂ v₁ v₂ a b)
    (h₁0 : v₁ a ∈ D₁.Safe) (h₂0 : v₂ a ∈ D₂.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, u t ≤ D₁.VIL) :
    ∀ t ∈ Icc s e, s + D₁.tauUp + D₂.tauDn ≤ t → v₂ t ≤ D₂.VOL := by
  intro t ht htime
  have hτ₁ := hD₁.tauUp_pos
  have hτ₂ := hD₂.tauDn_pos
  have hmid : ∀ x ∈ Ico (s + D₁.tauUp) e, D₂.VIH ≤ v₁ x := fun x hx =>
    le_trans hcompat
      (h₁.rise hD₁ h₁0 hs he hu x ⟨by linarith [hx.1], hx.2.le⟩ hx.1)
  exact h₂.fall hD₂ h₂0 (by linarith) he hmid t ⟨by linarith, ht.2⟩ htime

/-- A valid-high input to the first stage becomes a valid-high output of the
second stage after `D₁.tauDn + D₂.tauUp`. -/
theorem chain_high (hD₁ : D₁.Admissible) (hD₂ : D₂.Admissible)
    (hcompat : D₁.VOL ≤ D₂.VIL)
    (h₁ : IsTrajectory D₁ u v₁ a b) (h₂ : IsTrajectory D₂ v₁ v₂ a b)
    (h₁0 : v₁ a ∈ D₁.Safe) (h₂0 : v₂ a ∈ D₂.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, D₁.VIH ≤ u t) :
    ∀ t ∈ Icc s e, s + D₁.tauDn + D₂.tauUp ≤ t → D₂.VOH ≤ v₂ t := by
  intro t ht htime
  have hτ₁ := hD₁.tauDn_pos
  have hτ₂ := hD₂.tauUp_pos
  have hmid : ∀ x ∈ Ico (s + D₁.tauDn) e, v₁ x ≤ D₂.VIL := fun x hx =>
    le_trans
      (h₁.fall hD₁ h₁0 hs he hu x ⟨by linarith [hx.1], hx.2.le⟩ hx.1) hcompat
  exact h₂.rise hD₂ h₂0 (by linarith) he hmid t ⟨by linarith, ht.2⟩ htime

/-- Two copies of one admissible design restore a low bit. -/
theorem chain_restores_low {D : Design} (hD : D.Admissible)
    (h₁ : IsTrajectory D u v₁ a b) (h₂ : IsTrajectory D v₁ v₂ a b)
    (h₁0 : v₁ a ∈ D.Safe) (h₂0 : v₂ a ∈ D.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, u t ≤ D.VIL) :
    ∀ t ∈ Icc s e, s + D.tauUp + D.tauDn ≤ t → v₂ t ≤ D.VOL :=
  chain_low hD hD hD.VIH_le_VOH h₁ h₂ h₁0 h₂0 hs he hu

/-- Two copies of one admissible design restore a high bit. -/
theorem chain_restores_high {D : Design} (hD : D.Admissible)
    (h₁ : IsTrajectory D u v₁ a b) (h₂ : IsTrajectory D v₁ v₂ a b)
    (h₁0 : v₁ a ∈ D.Safe) (h₂0 : v₂ a ∈ D.Safe) {s e : ℝ} (hs : a ≤ s) (he : e ≤ b)
    (hu : ∀ t ∈ Ico s e, D.VIH ≤ u t) :
    ∀ t ∈ Icc s e, s + D.tauDn + D.tauUp ≤ t → D.VOH ≤ v₂ t :=
  chain_high hD hD hD.VOL_le_VIL h₁ h₂ h₁0 h₂0 hs he hu

end VoltageToBit

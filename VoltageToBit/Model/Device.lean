import VoltageToBit.Model.PosSq

/-!
# Device law: symmetric Shichman–Hodges square law

Two transistors of a static CMOS inverter, as functions of the gate voltage `u`
(the inverter input) and the drain voltage `v` (the inverter output node).

* NMOS: source at ground (0), gate `u`, drain `v`.
  `In θ u v` is the current from the output node to ground.
* PMOS: source at the supply `θ.VDD`, gate `u`, drain `v`.
  `Ip θ u v` is the current from the supply into the output node.
  `θ.Vtp` is the *magnitude* of the PMOS threshold.

The single expression `(k/2) * (psq (V_GS - V_t) - psq (V_GD - V_t))` equals the
textbook piecewise cutoff / triode / saturation law in forward operation (see
the `*_cutoff`, `*_triode`, `*_sat` lemmas below) and is antisymmetric under
source/drain exchange, so it also defines reverse conduction when the output
node is outside `[0, VDD]`.

Omitted on purpose: channel-length modulation, body effect, subthreshold
conduction, velocity saturation, junction diodes. See `docs/model.md`.

Units are a convention of the design record (V, µA, fF, ns; `k` in µA/V²);
the mathematics here is unit-free.
-/

namespace VoltageToBit

/-- Device and supply parameters, constant during a run. -/
structure Params where
  /-- supply voltage -/
  VDD : ℝ
  /-- NMOS transconductance parameter `k_n` -/
  kn : ℝ
  /-- PMOS transconductance parameter `k_p` -/
  kp : ℝ
  /-- NMOS threshold voltage -/
  Vtn : ℝ
  /-- PMOS threshold voltage magnitude -/
  Vtp : ℝ

/-- NMOS drain current, flowing from the output node to ground. -/
noncomputable def In (θ : Params) (u v : ℝ) : ℝ :=
  θ.kn / 2 * (psq (u - θ.Vtn) - psq (u - v - θ.Vtn))

/-- PMOS drain current, flowing from the supply into the output node. -/
noncomputable def Ip (θ : Params) (u v : ℝ) : ℝ :=
  θ.kp / 2 * (psq (θ.VDD - u - θ.Vtp) - psq (v - u - θ.Vtp))

/-- Net device current into the output node. -/
noncomputable def Inet (θ : Params) (u v : ℝ) : ℝ := Ip θ u v - In θ u v

/-! ## Agreement with the textbook piecewise law (forward operation) -/

theorem In_cutoff {θ : Params} {u v : ℝ} (hu : u ≤ θ.Vtn) (hv : 0 ≤ v) : In θ u v = 0 := by
  unfold In
  rw [psq_of_nonpos (by linarith), psq_of_nonpos (by linarith)]
  ring

theorem In_triode {θ : Params} {u v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ u - θ.Vtn) :
    In θ u v = θ.kn * ((u - θ.Vtn) * v - v ^ 2 / 2) := by
  unfold In
  rw [psq_of_nonneg (by linarith), psq_of_nonneg (by linarith)]
  ring

theorem In_sat {θ : Params} {u v : ℝ} (hu : θ.Vtn ≤ u) (hv : u - θ.Vtn ≤ v) :
    In θ u v = θ.kn / 2 * (u - θ.Vtn) ^ 2 := by
  unfold In
  rw [psq_of_nonneg (by linarith), psq_of_nonpos (by linarith)]
  ring

theorem Ip_cutoff {θ : Params} {u v : ℝ} (hu : θ.VDD - θ.Vtp ≤ u) (hv : v ≤ θ.VDD) :
    Ip θ u v = 0 := by
  unfold Ip
  rw [psq_of_nonpos (by linarith), psq_of_nonpos (by linarith)]
  ring

theorem Ip_triode {θ : Params} {u v : ℝ} (hv : v ≤ θ.VDD) (hu : u + θ.Vtp ≤ v) :
    Ip θ u v = θ.kp * ((θ.VDD - u - θ.Vtp) * (θ.VDD - v) - (θ.VDD - v) ^ 2 / 2) := by
  unfold Ip
  rw [psq_of_nonneg (by linarith), psq_of_nonneg (by linarith)]
  ring

theorem Ip_sat {θ : Params} {u v : ℝ} (hu : u ≤ θ.VDD - θ.Vtp) (hv : v ≤ u + θ.Vtp) :
    Ip θ u v = θ.kp / 2 * (θ.VDD - u - θ.Vtp) ^ 2 := by
  unfold Ip
  rw [psq_of_nonneg (by linarith), psq_of_nonpos (by linarith)]
  ring

/-! ## Signs -/

/-- The NMOS discharges the node when the node is above ground. -/
theorem In_nonneg {θ : Params} {u v : ℝ} (hk : 0 ≤ θ.kn) (hv : 0 ≤ v) : 0 ≤ In θ u v := by
  unfold In
  have := psq_mono (by linarith : u - v - θ.Vtn ≤ u - θ.Vtn)
  exact mul_nonneg (by linarith) (by linarith)

/-- The NMOS conducts in reverse (charges the node) when the node is below ground. -/
theorem In_nonpos {θ : Params} {u v : ℝ} (hk : 0 ≤ θ.kn) (hv : v ≤ 0) : In θ u v ≤ 0 := by
  unfold In
  have := psq_mono (by linarith : u - θ.Vtn ≤ u - v - θ.Vtn)
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- The PMOS charges the node when the node is below the supply. -/
theorem Ip_nonneg {θ : Params} {u v : ℝ} (hk : 0 ≤ θ.kp) (hv : v ≤ θ.VDD) : 0 ≤ Ip θ u v := by
  unfold Ip
  have := psq_mono (by linarith : v - u - θ.Vtp ≤ θ.VDD - u - θ.Vtp)
  exact mul_nonneg (by linarith) (by linarith)

/-- The PMOS conducts in reverse (discharges the node) when the node is above the supply. -/
theorem Ip_nonpos {θ : Params} {u v : ℝ} (hk : 0 ≤ θ.kp) (hv : θ.VDD ≤ v) : Ip θ u v ≤ 0 := by
  unfold Ip
  have := psq_mono (by linarith : θ.VDD - u - θ.Vtp ≤ v - u - θ.Vtp)
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- The saturation current bounds the NMOS current from above, for every `v`. -/
theorem In_le_sat {θ : Params} {u v : ℝ} (hk : 0 ≤ θ.kn) :
    In θ u v ≤ θ.kn / 2 * psq (u - θ.Vtn) := by
  unfold In
  have := psq_nonneg (u - v - θ.Vtn)
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- The saturation current bounds the PMOS current from above, for every `v`. -/
theorem Ip_le_sat {θ : Params} {u v : ℝ} (hk : 0 ≤ θ.kp) :
    Ip θ u v ≤ θ.kp / 2 * psq (θ.VDD - u - θ.Vtp) := by
  unfold Ip
  have := psq_nonneg (v - u - θ.Vtp)
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-! ## Regularity (used only for existence of trajectories) -/

theorem continuous_Inet (θ : Params) : Continuous (fun p : ℝ × ℝ => Inet θ p.1 p.2) := by
  unfold Inet Ip In
  have := continuous_psq
  fun_prop

/-- `v ↦ Inet θ u v` is Lipschitz on bounded sets, with an explicit modulus. -/
theorem abs_Inet_sub_le (θ : Params) (hkn : 0 ≤ θ.kn) (hkp : 0 ≤ θ.kp) (u v₁ v₂ : ℝ) :
    |Inet θ u v₁ - Inet θ u v₂| ≤
      (θ.kp / 2 * (|v₁ - u - θ.Vtp| + |v₂ - u - θ.Vtp|)
        + θ.kn / 2 * (|u - v₁ - θ.Vtn| + |u - v₂ - θ.Vtn|)) * |v₁ - v₂| := by
  have hp := abs_psq_sub_le (v₁ - u - θ.Vtp) (v₂ - u - θ.Vtp)
  have hn := abs_psq_sub_le (u - v₁ - θ.Vtn) (u - v₂ - θ.Vtn)
  have e1 : v₁ - u - θ.Vtp - (v₂ - u - θ.Vtp) = v₁ - v₂ := by ring
  have e2 : u - v₁ - θ.Vtn - (u - v₂ - θ.Vtn) = -(v₁ - v₂) := by ring
  rw [e1] at hp
  rw [e2, abs_neg] at hn
  have hsplit : Inet θ u v₁ - Inet θ u v₂ =
      -(θ.kp / 2 * (psq (v₁ - u - θ.Vtp) - psq (v₂ - u - θ.Vtp)))
        + θ.kn / 2 * (psq (u - v₁ - θ.Vtn) - psq (u - v₂ - θ.Vtn)) := by
    unfold Inet Ip In; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ.kp / 2),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ.kn / 2)]
  have h1 := mul_le_mul_of_nonneg_left hp (by linarith : (0 : ℝ) ≤ θ.kp / 2)
  have h2 := mul_le_mul_of_nonneg_left hn (by linarith : (0 : ℝ) ≤ θ.kn / 2)
  nlinarith

end VoltageToBit

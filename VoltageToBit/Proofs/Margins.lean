import VoltageToBit.Model.Inverter

/-!
# Current margins derived from the device law

The closed-form numbers `Iup`, `Idn`, `RhiP`, `RhiN`, `RloN`, `RloP` of a
design record are shown to be genuine bounds on the net device current
`Inet θ u v`, for every parameter choice in the box. Each proof is a chain of
monotonicity steps on `psq`; no margin is assumed.

* `Inet_ge_Iup`: for `u ≤ VIL` and `v ≤ c ≤ VDDlo`, the net current into the
  node is at least `Iup c`.
* `Inet_le_neg_Idn`: for `VIH ≤ u` and `0 ≤ c ≤ v`, the net current out of the
  node is at least `Idn c`.
* `Inet_Vhi_lt`, `Inet_Vlo_gt`: at the two ends of the safe domain the device
  current points strictly inwards by more than `eps`, for **every** input
  value `u`.
-/

namespace VoltageToBit

namespace Design

variable {D : Design} {θ : Params}

/-- Pull-up margin: with a valid-low input and the node at or below `c`, the
devices deliver at least `Iup c` into the node. -/
theorem Inet_ge_Iup (hD : D.Admissible) (hθ : D.InBox θ) {u v c : ℝ}
    (hu : u ≤ D.VIL) (hv : v ≤ c) (hc : c ≤ D.VDDlo) :
    D.Iup c ≤ Inet θ u v := by
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  -- PMOS: lower bound
  have hB : psq (v - u - θ.Vtp) ≤ psq (c - u - θ.Vtp) := psq_mono (by linarith)
  have hQ : psq (D.VDDlo - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi)
      ≤ psq (θ.VDD - u - θ.Vtp) - psq (c - u - θ.Vtp) :=
    psq_sub_le_psq_sub (by linarith) (by linarith [hθ.Vtp_le])
      (by linarith [hθ.VDD_ge])
  have hQ0 : 0 ≤ psq (D.VDDlo - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi) :=
    sub_nonneg.mpr (psq_mono (by linarith))
  have hP : D.kplo / 2 * (psq (D.VDDlo - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi))
      ≤ Ip θ u v := by
    unfold Ip
    have h1 : D.kplo / 2 * (psq (D.VDDlo - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi))
        ≤ θ.kp / 2 * (psq (D.VDDlo - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi)) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kp_ge]) hQ0
    have h2 : θ.kp / 2 * (psq (D.VDDlo - D.VIL - D.Vtphi) - psq (c - D.VIL - D.Vtphi))
        ≤ θ.kp / 2 * (psq (θ.VDD - u - θ.Vtp) - psq (v - u - θ.Vtp)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- NMOS: upper bound by the saturation current at the worst corner
  have hN : In θ u v ≤ D.knhi / 2 * psq (D.VIL - D.Vtnlo) := by
    have h1 := In_le_sat (θ := θ) (u := u) (v := v) hkn
    have h2 : psq (u - θ.Vtn) ≤ psq (D.VIL - D.Vtnlo) :=
      psq_mono (by linarith [hθ.Vtn_ge])
    have h3 : θ.kn / 2 * psq (u - θ.Vtn) ≤ θ.kn / 2 * psq (D.VIL - D.Vtnlo) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : θ.kn / 2 * psq (D.VIL - D.Vtnlo) ≤ D.knhi / 2 * psq (D.VIL - D.Vtnlo) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kn_le]) (psq_nonneg _)
    linarith
  unfold Iup Inet
  linarith

/-- Pull-down margin: with a valid-high input and the node at or above `c`,
the devices remove at least `Idn c` from the node. -/
theorem Inet_le_neg_Idn (hD : D.Admissible) (hθ : D.InBox θ) {u v c : ℝ}
    (hu : D.VIH ≤ u) (hv : c ≤ v) (hc : 0 ≤ c) :
    Inet θ u v ≤ -D.Idn c := by
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  -- NMOS: lower bound
  have hB : psq (u - v - θ.Vtn) ≤ psq (u - c - θ.Vtn) := psq_mono (by linarith)
  have hQ : psq (D.VIH - D.Vtnhi) - psq (D.VIH - c - D.Vtnhi)
      ≤ psq (u - θ.Vtn) - psq (u - c - θ.Vtn) :=
    psq_sub_le_psq_sub (by linarith) (by linarith [hθ.Vtn_le]) (by linarith)
  have hQ0 : 0 ≤ psq (D.VIH - D.Vtnhi) - psq (D.VIH - c - D.Vtnhi) :=
    sub_nonneg.mpr (psq_mono (by linarith))
  have hN : D.knlo / 2 * (psq (D.VIH - D.Vtnhi) - psq (D.VIH - c - D.Vtnhi)) ≤ In θ u v := by
    unfold In
    have h1 : D.knlo / 2 * (psq (D.VIH - D.Vtnhi) - psq (D.VIH - c - D.Vtnhi))
        ≤ θ.kn / 2 * (psq (D.VIH - D.Vtnhi) - psq (D.VIH - c - D.Vtnhi)) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kn_ge]) hQ0
    have h2 : θ.kn / 2 * (psq (D.VIH - D.Vtnhi) - psq (D.VIH - c - D.Vtnhi))
        ≤ θ.kn / 2 * (psq (u - θ.Vtn) - psq (u - v - θ.Vtn)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- PMOS: upper bound by the saturation current at the worst corner
  have hP : Ip θ u v ≤ D.kphi / 2 * psq (D.VDDhi - D.VIH - D.Vtplo) := by
    have h1 := Ip_le_sat (θ := θ) (u := u) (v := v) hkp
    have h2 : psq (θ.VDD - u - θ.Vtp) ≤ psq (D.VDDhi - D.VIH - D.Vtplo) :=
      psq_mono (by linarith [hθ.VDD_le, hθ.Vtp_ge])
    have h3 : θ.kp / 2 * psq (θ.VDD - u - θ.Vtp) ≤ θ.kp / 2 * psq (D.VDDhi - D.VIH - D.Vtplo) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : θ.kp / 2 * psq (D.VDDhi - D.VIH - D.Vtplo)
        ≤ D.kphi / 2 * psq (D.VDDhi - D.VIH - D.Vtplo) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kp_le]) (psq_nonneg _)
    linarith
  unfold Idn Inet
  linarith

/-- Upper boundary, PMOS branch: for `u ≤ uHi` the reverse-conducting PMOS
removes at least `RhiP` from a node at `Vhi`. -/
theorem Inet_Vhi_le_neg_RhiP (hD : D.Admissible) (hθ : D.InBox θ) {u : ℝ} (hu : u ≤ D.uHi) :
    Inet θ u D.Vhi ≤ -D.RhiP := by
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  have hVhi0 : 0 ≤ D.Vhi := by linarith [hD.VDD_pos, hD.VDD_le, hD.Vhi_ge]
  have hN : 0 ≤ In θ u D.Vhi := In_nonneg hkn hVhi0
  have hQ : psq (D.VDDlo - D.uHi - D.Vtphi + (D.Vhi - D.VDDhi)) - psq (D.VDDlo - D.uHi - D.Vtphi)
      ≤ psq (D.Vhi - u - θ.Vtp) - psq (θ.VDD - u - θ.Vtp) :=
    psq_sub_le_psq_sub (by linarith [hD.Vhi_ge]) (by linarith [hθ.VDD_ge, hθ.Vtp_le])
      (by linarith [hθ.VDD_le])
  have hQ0 : 0 ≤ psq (D.VDDlo - D.uHi - D.Vtphi + (D.Vhi - D.VDDhi))
      - psq (D.VDDlo - D.uHi - D.Vtphi) :=
    sub_nonneg.mpr (psq_mono (by linarith [hD.Vhi_ge]))
  have hP : Ip θ u D.Vhi ≤ -D.RhiP := by
    unfold Ip RhiP
    have h1 : D.kplo / 2 * (psq (D.VDDlo - D.uHi - D.Vtphi + (D.Vhi - D.VDDhi))
          - psq (D.VDDlo - D.uHi - D.Vtphi))
        ≤ θ.kp / 2 * (psq (D.VDDlo - D.uHi - D.Vtphi + (D.Vhi - D.VDDhi))
          - psq (D.VDDlo - D.uHi - D.Vtphi)) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kp_ge]) hQ0
    have h2 : θ.kp / 2 * (psq (D.VDDlo - D.uHi - D.Vtphi + (D.Vhi - D.VDDhi))
          - psq (D.VDDlo - D.uHi - D.Vtphi))
        ≤ θ.kp / 2 * (psq (D.Vhi - u - θ.Vtp) - psq (θ.VDD - u - θ.Vtp)) :=
      mul_le_mul_of_nonneg_left hQ (by linarith)
    linarith
  unfold Inet
  linarith

/-- Upper boundary, NMOS branch: for `uHi ≤ u` the NMOS removes at least
`RhiN` from a node at `Vhi`. -/
theorem Inet_Vhi_le_neg_RhiN (hD : D.Admissible) (hθ : D.InBox θ) {u : ℝ} (hu : D.uHi ≤ u) :
    Inet θ u D.Vhi ≤ -D.RhiN := by
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  have hVhi0 : 0 ≤ D.Vhi := by linarith [hD.VDD_pos, hD.VDD_le, hD.Vhi_ge]
  have hP : Ip θ u D.Vhi ≤ 0 := Ip_nonpos hkp (by linarith [hθ.VDD_le, hD.Vhi_ge])
  have hQ : psq (D.uHi - D.Vtnhi) - psq (D.uHi - D.Vhi - D.Vtnhi)
      ≤ psq (u - θ.Vtn) - psq (u - D.Vhi - θ.Vtn) :=
    psq_sub_le_psq_sub (by linarith) (by linarith [hθ.Vtn_le]) (by linarith)
  have hQ0 : 0 ≤ psq (D.uHi - D.Vtnhi) - psq (D.uHi - D.Vhi - D.Vtnhi) :=
    sub_nonneg.mpr (psq_mono (by linarith))
  have hN : D.RhiN ≤ In θ u D.Vhi := by
    unfold In RhiN
    have h1 : D.knlo / 2 * (psq (D.uHi - D.Vtnhi) - psq (D.uHi - D.Vhi - D.Vtnhi))
        ≤ θ.kn / 2 * (psq (D.uHi - D.Vtnhi) - psq (D.uHi - D.Vhi - D.Vtnhi)) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kn_ge]) hQ0
    have h2 : θ.kn / 2 * (psq (D.uHi - D.Vtnhi) - psq (D.uHi - D.Vhi - D.Vtnhi))
        ≤ θ.kn / 2 * (psq (u - θ.Vtn) - psq (u - D.Vhi - θ.Vtn)) :=
      mul_le_mul_of_nonneg_left hQ (by linarith)
    linarith
  unfold Inet
  linarith

/-- Lower boundary, NMOS branch: for `uLo ≤ u` the reverse-conducting NMOS
delivers at least `RloN` into a node at `Vlo`. -/
theorem RloN_le_Inet_Vlo (hD : D.Admissible) (hθ : D.InBox θ) {u : ℝ} (hu : D.uLo ≤ u) :
    D.RloN ≤ Inet θ u D.Vlo := by
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  have hP : 0 ≤ Ip θ u D.Vlo :=
    Ip_nonneg hkp (by linarith [hD.Vlo_le, hD.VDD_pos, hθ.VDD_ge])
  have hQ : psq (D.uLo - D.Vlo - D.Vtnhi) - psq (D.uLo - D.Vtnhi)
      ≤ psq (u - D.Vlo - θ.Vtn) - psq (u - θ.Vtn) :=
    psq_sub_le_psq_sub (by linarith [hD.Vlo_le]) (by linarith [hθ.Vtn_le]) (by linarith)
  have hQ0 : 0 ≤ psq (D.uLo - D.Vlo - D.Vtnhi) - psq (D.uLo - D.Vtnhi) :=
    sub_nonneg.mpr (psq_mono (by linarith [hD.Vlo_le]))
  have hN : In θ u D.Vlo ≤ -D.RloN := by
    unfold In RloN
    have h1 : D.knlo / 2 * (psq (D.uLo - D.Vlo - D.Vtnhi) - psq (D.uLo - D.Vtnhi))
        ≤ θ.kn / 2 * (psq (D.uLo - D.Vlo - D.Vtnhi) - psq (D.uLo - D.Vtnhi)) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kn_ge]) hQ0
    have h2 : θ.kn / 2 * (psq (D.uLo - D.Vlo - D.Vtnhi) - psq (D.uLo - D.Vtnhi))
        ≤ θ.kn / 2 * (psq (u - D.Vlo - θ.Vtn) - psq (u - θ.Vtn)) :=
      mul_le_mul_of_nonneg_left hQ (by linarith)
    linarith
  unfold Inet
  linarith

/-- Lower boundary, PMOS branch: for `u ≤ uLo` the PMOS delivers at least
`RloP` into a node at `Vlo`. -/
theorem RloP_le_Inet_Vlo (hD : D.Admissible) (hθ : D.InBox θ) {u : ℝ} (hu : u ≤ D.uLo) :
    D.RloP ≤ Inet θ u D.Vlo := by
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  have hN : In θ u D.Vlo ≤ 0 := In_nonpos hkn hD.Vlo_le
  have hQ : psq (D.VDDlo - D.uLo - D.Vtphi) - psq (D.Vlo - D.uLo - D.Vtphi)
      ≤ psq (θ.VDD - u - θ.Vtp) - psq (D.Vlo - u - θ.Vtp) :=
    psq_sub_le_psq_sub (by linarith [hD.Vlo_le, hD.VDD_pos]) (by linarith [hθ.Vtp_le])
      (by linarith [hθ.VDD_ge])
  have hQ0 : 0 ≤ psq (D.VDDlo - D.uLo - D.Vtphi) - psq (D.Vlo - D.uLo - D.Vtphi) :=
    sub_nonneg.mpr (psq_mono (by linarith [hD.Vlo_le, hD.VDD_pos]))
  have hP : D.RloP ≤ Ip θ u D.Vlo := by
    unfold Ip RloP
    have h1 : D.kplo / 2 * (psq (D.VDDlo - D.uLo - D.Vtphi) - psq (D.Vlo - D.uLo - D.Vtphi))
        ≤ θ.kp / 2 * (psq (D.VDDlo - D.uLo - D.Vtphi) - psq (D.Vlo - D.uLo - D.Vtphi)) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.kp_ge]) hQ0
    have h2 : θ.kp / 2 * (psq (D.VDDlo - D.uLo - D.Vtphi) - psq (D.Vlo - D.uLo - D.Vtphi))
        ≤ θ.kp / 2 * (psq (θ.VDD - u - θ.Vtp) - psq (D.Vlo - u - θ.Vtp)) :=
      mul_le_mul_of_nonneg_left hQ (by linarith)
    linarith
  unfold Inet
  linarith

/-- At the top of the safe domain the device current points strictly inwards
by more than `eps`, for every input value. -/
theorem Inet_Vhi_lt (hD : D.Admissible) (hθ : D.InBox θ) (u : ℝ) :
    Inet θ u D.Vhi < -D.eps := by
  rcases le_total u D.uHi with hu | hu
  · have := Inet_Vhi_le_neg_RhiP hD hθ hu
    linarith [hD.hiP]
  · have := Inet_Vhi_le_neg_RhiN hD hθ hu
    linarith [hD.hiN]

/-- At the bottom of the safe domain the device current points strictly
inwards by more than `eps`, for every input value. -/
theorem Inet_Vlo_gt (hD : D.Admissible) (hθ : D.InBox θ) (u : ℝ) :
    D.eps < Inet θ u D.Vlo := by
  rcases le_total u D.uLo with hu | hu
  · have := RloP_le_Inet_Vlo hD hθ hu
    linarith [hD.loP]
  · have := RloN_le_Inet_Vlo hD hθ hu
    linarith [hD.loN]

end Design

end VoltageToBit

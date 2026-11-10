"""Floating-point (numpy) current laws: the formal model, a miswired circuit,
and perturbed model forms used only for the sensitivity study.

Every law has the signature ``law(u, v, VDD, kn, kp, Vtn, Vtp) -> I_net`` (uA)
and broadcasts over numpy arrays. All are module-level so they can be pickled
for multiprocessing (use ``functools.partial`` to bind perturbation parameters).
"""
from __future__ import annotations

import numpy as np

# CODATA 2018 exact constants (SI): thermal voltage phi_t = k_B T / q
K_BOLTZMANN = 1.380649e-23
Q_ELECTRON = 1.602176634e-19


def thermal_voltage(T_kelvin: float) -> float:
    return K_BOLTZMANN * T_kelvin / Q_ELECTRON


def psq(x):
    m = np.maximum(x, 0.0)
    return m * m


def inet_formal(u, v, VDD, kn, kp, Vtn, Vtp):
    """interface.md section 3 (symmetric Shichman-Hodges, lambda = 0)."""
    ip = 0.5 * kp * (psq(VDD - u - Vtp) - psq(v - u - Vtp))
    i_n = 0.5 * kn * (psq(u - Vtn) - psq(u - v - Vtn))
    return ip - i_n


def ip_formal(u, v, VDD, kp, Vtp):
    return 0.5 * kp * (psq(VDD - u - Vtp) - psq(v - u - Vtp))


def in_formal(u, v, kn, Vtn):
    return 0.5 * kn * (psq(u - Vtn) - psq(u - v - Vtn))


def dinet_dv_formal(u, v, VDD, kn, kp, Vtn, Vtp):
    """Analytic d I_net / d v (always <= 0)."""
    return -kp * np.maximum(v - u - Vtp, 0.0) - kn * np.maximum(u - v - Vtn, 0.0)


def inet_miswired(u, v, VDD, kn, kp, Vtn, Vtp):
    """Negative control: NMOS pull-up (drain = VDD, source = out), PMOS pull-down
    (source = out, drain = ground), both gates on u (a complementary source follower)."""
    i_nup = 0.5 * kn * (psq(u - v - Vtn) - psq(u - VDD - Vtn))  # VDD -> out
    i_pdn = 0.5 * kp * (psq(v - u - Vtp) - psq(0.0 - u - Vtp))  # out -> ground
    return i_nup - i_pdn


def soft_psq(x, s):
    """Smooth weak-to-strong-inversion interpolation (EKV form):
    (s * ln(1 + exp(x / s)))^2 with s = 2 n phi_t.  -> x^2 for x >> s (the formal
    square law), -> s^2 exp(2x/s) = s^2 exp(x / (n phi_t)) for x << -s (subthreshold tail)."""
    y = s * np.logaddexp(0.0, np.asarray(x, dtype=float) / s)
    return y * y


def inet_perturbed(u, v, VDD, kn, kp, Vtn, Vtp, lam_n=0.0, lam_p=0.0, s_n=0.0, s_p=0.0):
    """Sensitivity-study model form (NOT a validated device model).

    * channel-length modulation: each device current multiplied by (1 + lambda * |V_DS|),
      the SPICE Level-1 form applied in both triode and saturation, symmetric in
      source/drain exchange;
    * subthreshold tail: psq replaced by ``soft_psq`` with s = 2 n phi_t (s = 0 keeps psq).
    """
    Pn = psq if s_n == 0.0 else (lambda x: soft_psq(x, s_n))
    Pp = psq if s_p == 0.0 else (lambda x: soft_psq(x, s_p))
    ip = 0.5 * kp * (Pp(VDD - u - Vtp) - Pp(v - u - Vtp)) * (1.0 + lam_p * np.abs(VDD - v))
    i_n = 0.5 * kn * (Pn(u - Vtn) - Pn(u - v - Vtn)) * (1.0 + lam_n * np.abs(v))
    return ip - i_n

#!/usr/bin/env python3
"""Workstream E, numeric probe n03.

Worst-case and best-case model delays of the illustrative instance, by
quadrature and by ODE integration, compared with the proved deadlines
(tauUp = 3.4214, tauDn = 2.5602), the three-level certificate (2.3384, claimed
<= 2.34), the rejected certificate deadline (2.0) and the contamination bound
(0.038 ns).

The slowest admissible rise is: weak pull-up corner, u = VIL, C = Chi,
w = -eps (constant, continuous, |w| <= eps). The slowest admissible fall is the
mirror image. These are genuine members of the trajectory class (they satisfy
the hypotheses of exists_trajectory), so any claimed deadline below these
numbers is false in the model.
"""
import numpy as np
from scipy.integrate import quad, solve_ivp

VDDlo, VDDhi = 1.62, 1.98
knlo, knhi = 160.0, 240.0
kplo, kphi = 80.0, 120.0
Vtnlo, Vtnhi = 0.45, 0.60
Vtplo, Vtphi = 0.45, 0.60
Clo, Chi = 5.0, 20.0
eps = 2.0
VIL, VIH, VOL, VOH = 0.40, 1.25, 0.25, 1.35
Vlo, Vhi = -0.10, 2.08


def psq(x):
    return max(x, 0.0) ** 2


def Inet(th, u, v):
    VDD, kn, kp, Vtn, Vtp = th
    return kp / 2 * (psq(VDD - u - Vtp) - psq(v - u - Vtp)) - kn / 2 * (psq(u - Vtn) - psq(u - v - Vtn))


def Iup(c):
    return kplo / 2 * (psq(VDDlo - VIL - Vtphi) - psq(c - VIL - Vtphi)) - knhi / 2 * psq(VIL - Vtnlo)


def Idn(c):
    return knlo / 2 * (psq(VIH - Vtnhi) - psq(VIH - c - Vtnhi)) - kphi / 2 * psq(VDDhi - VIH - Vtplo)


def crossing_time(th, u, C, w, v0, target, rising, tmax=50.0):
    f = lambda t, y: [(Inet(th, u, y[0]) + w) / C]
    ev = lambda t, y: y[0] - target
    ev.terminal = True
    ev.direction = 1 if rising else -1
    s = solve_ivp(f, (0, tmax), [v0], events=ev, rtol=1e-11, atol=1e-13, max_step=1e-3)
    return s.t_events[0][0] if len(s.t_events[0]) else float("nan")


weak_up = (VDDlo, knhi, kplo, Vtnhi, Vtphi)   # Vtn = Vtnhi removes NMOS reverse help below ground
weak_dn = (VDDhi, knlo, kphi, Vtnhi, Vtplo)
print("== rising output (input valid-low) ==")
q_up, _ = quad(lambda c: Chi / (Iup(c) - eps), Vlo, VOH, epsabs=1e-12, epsrel=1e-12)
print(f"infimum over all certificates = integral of Chi/(Iup(c)-eps) over [Vlo,VOH]      : {q_up:.6f} ns")
t1 = crossing_time(weak_up, VIL, Chi, -eps, Vlo, VOH, True)
t2 = crossing_time(weak_up, VIL, Chi, -eps, VOL, VOH, True)
print(f"slowest trajectory, start Vlo = -0.10 V (ODE)                                     : {t1:.6f} ns")
print(f"slowest trajectory, start VOL =  0.25 V (ODE)                                     : {t2:.6f} ns")
print(f"proved: tauUp = {Chi*(VOH-Vlo)/(Iup(VOH)-eps):.6f} ns ; certificate [1.0,1.2,1.35] = 2.338351 ns")
print(f"ratio tauUp / slowest-from-Vlo = {Chi*(VOH-Vlo)/(Iup(VOH)-eps)/t1:.3f} ; certificate / slowest = {2.338351/t1:.4f}")
print(f"a 2.0 ns deadline is {'FALSE' if t1 > 2.0 else 'not refuted'} in the model (slowest run needs {t1:.4f} ns)")

print("== falling output (input valid-high) ==")
q_dn, _ = quad(lambda c: Chi / (Idn(c) - eps), VOL, Vhi, epsabs=1e-12, epsrel=1e-12)
t3 = crossing_time(weak_dn, VIH, Chi, +eps, Vhi, VOL, False)
t4 = crossing_time(weak_dn, VIH, Chi, +eps, VOH, VOL, False)
print(f"integral of Chi/(Idn(c)-eps) over [VOL,Vhi]                                        : {q_dn:.6f} ns")
print(f"slowest trajectory, start Vhi = 2.08 V (ODE)                                       : {t3:.6f} ns")
print(f"slowest trajectory, start VOH = 1.35 V (ODE)                                       : {t4:.6f} ns")
print(f"proved: tauDn = {Chi*(Vhi-VOL)/(Idn(VOL)-eps):.6f} ns ; ratio tauDn / slowest-from-Vhi = {Chi*(Vhi-VOL)/(Idn(VOL)-eps)/t3:.3f}")

print("== fastest rise (contamination) ==")
fast = (VDDhi, knhi, kphi, Vtnlo, Vtplo)
for ulow in (0.40, 0.0, -1.0, -10.0, -100.0):
    t5 = crossing_time(fast, ulow, Clo, +eps, VOL, VOH, True)
    print(f"fast corner, C = Clo, w = +eps, constant input u = {ulow:7.2f} V, start 0.25 V: reaches 1.35 V at {t5*1000:9.4f} ps")
print("contamination bound of illustrative_no_early_high: 38 ps, stated for inputs in [0, 0.40] V only")

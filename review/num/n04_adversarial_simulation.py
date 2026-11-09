#!/usr/bin/env python3
"""Workstream E, numeric probe n04.

Randomised attempt to violate the illustrative guarantee by simulation.

For each run: a parameter choice in the box (half of the runs at a random
corner), a capacitance in [5, 20] that may switch between values, a random
piecewise-linear input in [-0.3, 2.1] V with dwell segments at valid-low /
valid-high levels, and a disturbance policy with |w| <= eps chosen to hurt:
  'outward'  : push the node towards the nearer end of the safe domain;
  'oppose'   : oppose the transition the input asks for;
  'bangbang' : random sign, random switching times;
  'sine'     : eps*sin(omega t + phi).
Integration: fixed-step RK4 with step 0.5 ps (the ODE is non-stiff at this
step: the largest |dI/dv|/C is about 240*2.5/5 = 120 /ns).

Checked on every run:
  (1) the node stays in [-0.10, 2.08];
  (2) whenever u <= 0.40 has held since time s, v >= 1.35 on [s + 3.43, ...];
  (3) whenever u >= 1.25 has held since time s, v <= 0.25 on [s + 2.57, ...].
Also reported: the extreme node voltages reached after the first nanosecond
(the initial state is drawn from the whole safe domain), and the largest
observed settling times, to compare with the deadlines.

A violation would mean that this reading of the model differs from the Lean
statement (the Lean theorem is proved); none is expected. Finite coverage:
this is a sanity check of the reading, not evidence for the theorem.
"""
import numpy as np

rng = np.random.default_rng(1880)
VDDr, knr, kpr, Vtnr, Vtpr = (1.62, 1.98), (160.0, 240.0), (80.0, 120.0), (0.45, 0.60), (0.45, 0.60)
Clo, Chi, eps = 5.0, 20.0, 2.0
VIL, VIH, VOL, VOH, Vlo, Vhi = 0.40, 1.25, 0.25, 1.35, -0.10, 2.08
TAU_UP, TAU_DN = 3.43, 2.57
H = 0.0005  # ns
T = 16.0


def psq(x):
    return x * x if x > 0 else 0.0


def Inet(th, u, v):
    VDD, kn, kp, Vtn, Vtp = th
    return kp / 2 * (psq(VDD - u - Vtp) - psq(v - u - Vtp)) - kn / 2 * (psq(u - Vtn) - psq(u - v - Vtn))


def make_input():
    """piecewise-linear input: alternating dwell levels joined by ramps"""
    ts, us = [0.0], []
    level = rng.choice([rng.uniform(-0.3, VIL), rng.uniform(VIH, 2.1), rng.uniform(VIL, VIH)], p=[0.45, 0.45, 0.10])
    us.append(level)
    t = 0.0
    while t < T:
        dwell = rng.choice([rng.uniform(0.2, 2.0), rng.uniform(3.5, 6.0)])
        t += dwell
        ts.append(t); us.append(level + rng.uniform(-0.02, 0.02) if VIL < level < VIH else level)
        ramp = rng.choice([0.0005, 0.05, 0.5])
        level = rng.choice([rng.uniform(-0.3, VIL), rng.uniform(VIH, 2.1), rng.uniform(VIL, VIH)], p=[0.45, 0.45, 0.10])
        t += ramp
        ts.append(t); us.append(level)
    return np.array(ts), np.array(us)


def run(policy):
    if rng.random() < 0.5:
        th = tuple(rng.choice(r) for r in (VDDr, knr, kpr, Vtnr, Vtpr))
    else:
        th = tuple(rng.uniform(*r) for r in (VDDr, knr, kpr, Vtnr, Vtpr))
    ts, us = make_input()
    n = int(T / H)
    tgrid = np.arange(n + 1) * H
    ugrid = np.interp(tgrid, ts, us)
    C = rng.choice([Clo, Chi, rng.uniform(Clo, Chi)])
    cswitch = rng.random() < 0.3
    v = rng.uniform(Vlo, Vhi)
    omega, phi = rng.uniform(0.5, 60.0), rng.uniform(0, 6.28)
    sgn, next_flip = rng.choice([-1.0, 1.0]), rng.exponential(0.3)
    low_since = high_since = None
    vmin_late, vmax_late = np.inf, -np.inf   # extremes reached after the first nanosecond
    settle_up = settle_dn = 0.0
    viol = []
    for i in range(n):
        t, u = tgrid[i], ugrid[i]
        # bookkeeping of valid-input windows (hypothesis is on [s, t))
        if policy == "outward":
            w = eps if v > (Vlo + Vhi) / 2 else -eps
        elif policy == "oppose":
            w = -eps if u <= VIL else (eps if u >= VIH else (eps if v > 1.0 else -eps))
        elif policy == "bangbang":
            if t >= next_flip:
                sgn, next_flip = -sgn, t + rng.exponential(0.3)
            w = sgn * eps
        else:
            w = eps * np.sin(omega * t + phi)
        if cswitch and i % 4000 == 0:
            C = rng.choice([Clo, Chi])
        f = lambda vv, uu: (Inet(th, uu, vv) + w) / C
        um, un = 0.5 * (u + ugrid[i + 1]), ugrid[i + 1]
        k1 = f(v, u); k2 = f(v + 0.5 * H * k1, um); k3 = f(v + 0.5 * H * k2, um); k4 = f(v + H * k3, un)
        # conclusions are checked at time t (before the step), with windows that held on [s, t)
        if low_since is not None:
            if t >= low_since + TAU_UP and v < VOH:
                viol.append(("rise", t, v))
            if v < VOH:
                settle_up = max(settle_up, t - low_since)
        if high_since is not None:
            if t >= high_since + TAU_DN and v > VOL:
                viol.append(("fall", t, v))
            if v > VOL:
                settle_dn = max(settle_dn, t - high_since)
        if t >= 1.0:
            vmin_late, vmax_late = min(vmin_late, v), max(vmax_late, v)
        if v < Vlo or v > Vhi:
            viol.append(("safe", t, v))
        low_since = (t if low_since is None else low_since) if u <= VIL else None
        high_since = (t if high_since is None else high_since) if u >= VIH else None
        v = v + H / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    return viol, (vmin_late, vmax_late), settle_up, settle_dn


NRUNS = 240
total_viol, lo_seen, hi_seen, worst_up, worst_dn = 0, np.inf, -np.inf, 0.0, 0.0
for r in range(NRUNS):
    policy = ["outward", "oppose", "bangbang", "sine"][r % 4]
    viol, ms, su, sd = run(policy)
    total_viol += len(viol)
    lo_seen, hi_seen = min(lo_seen, ms[0]), max(hi_seen, ms[1])
    worst_up, worst_dn = max(worst_up, su), max(worst_dn, sd)
    if viol:
        print("VIOLATION in run", r, policy, viol[:3])
print(f"runs: {NRUNS}  (horizon {T} ns, step {H} ns)   violations: {total_viol}")
print(f"extreme node voltages reached after t = 1 ns: min {lo_seen:.4f} V, max {hi_seen:.4f} V   (safe domain [-0.10, 2.08])")
print(f"longest time a valid-low  input was held with output still < 1.35 V: {worst_up:.4f} ns   (deadline 3.43)")
print(f"longest time a valid-high input was held with output still > 0.25 V: {worst_dn:.4f} ns   (deadline 2.57)")

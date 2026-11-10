"""Integrators for the scalar inclusion  c * v' = I_net(u(t), v; theta) + w.

* ``run_batch``: fixed-step classical RK4, vectorised over many scenarios that
  share one input waveform; tracks invariance, first valid-output crossing
  (cubic-Hermite event location), and persistence statistics without storing
  trajectories.
* ``solve_ref``: scipy ``solve_ivp`` reference integration of one scenario with
  event detection, restarted at input/disturbance kinks.

State-feedback disturbance kinds (``fb`` code per row), all with |w| <= eps and
w non-decreasing in v (so no sliding mode can form):
  1  adv_oppose  : w = -sgn*eps (opposes the intended transition), except
                   w = +eps within ``adv_delta`` of V_hi and w = -eps within
                   ``adv_delta`` of V_lo (pushes outward near the domain boundary)
  2  adv_outward : w = +eps above mid-domain, -eps below (always towards the nearer boundary)
  3  env_low     : extremal selection of the inclusion for ONE parameter point, lower envelope:
                   v' = (I - eps)/C_max if I - eps >= 0 else (I - eps)/C_min
  4  env_high    : upper envelope: v' = (I + eps)/C_min if I + eps >= 0 else (I + eps)/C_max
  5  box_low     : extremal selection of the interface.md v1 (rev. 2) inclusion, in which the
                   parameter point may differ from instant to instant: as env_low with
                   I replaced by m(u, v) = min over the box of I_net(u, v; theta)
  6  box_high    : as env_high with I replaced by M(u, v) = max over the box of I_net(u, v; theta)

I_net is monotone in each parameter separately, so its minimum and maximum over the box are
attained at corners; ``Batch.box`` holds the 32 corners. Every trajectory of the rev. 2
inclusion that starts between the box_low and box_high solutions stays between them (scalar
comparison principle), whatever the disturbance, capacitance and parameter selections.
"""
from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np
from scipy.integrate import solve_ivp

from . import signals

FB_NAMES = {0: "table", 1: "adv_oppose", 2: "adv_outward", 3: "env_low", 4: "env_high", 5: "box_low", 6: "box_high"}


@dataclass
class Batch:
    theta: np.ndarray  # (n, 5): VDD, kn, kp, Vtn, Vtp
    C: np.ndarray  # (n,)
    v0: np.ndarray  # (n,)
    w_idx: np.ndarray  # (n,) row of W used by each scenario
    fb: np.ndarray  # (n,) feedback code
    U: np.ndarray  # (2N+1,) input at half-step times k*dt/2
    W: np.ndarray  # (n_w, 2N+1) time-only disturbances at half-step times
    dt: float
    N: int
    s_idx: int  # grid index at which the input becomes (and stays) valid
    deadline_idx: int  # first grid index >= s + tau; -1 if no bound applies
    sgn: int  # +1: output must become >= Vth; -1: output must become <= Vth
    Vth: float
    eps: float
    Cmin: float
    Cmax: float
    Vlo: float
    Vhi: float
    law: object
    adv_delta: float = 0.02
    record_rows: list = field(default_factory=list)
    record_every: int = 0
    Cgd: float = 0.0  # gate-drain coupling capacitance in fF (sensitivity study only; 0 = formal model)
    box: np.ndarray | None = None  # (n_corners, 5) parameter-box corners, needed by fb codes 5 and 6
    u_row: np.ndarray | None = None  # optional per-row constant input (overrides U)


def _hermite_root(v0, f0, v1, f1, h, Vth, sgn):
    """theta in (0, 1] with H(theta) = Vth for the cubic Hermite interpolant (bisection)."""
    lo = np.zeros_like(v0)
    hi = np.ones_like(v0)
    for _ in range(60):
        m = 0.5 * (lo + hi)
        m2 = m * m
        m3 = m2 * m
        H = (2 * m3 - 3 * m2 + 1) * v0 + (m3 - 2 * m2 + m) * h * f0 + (-2 * m3 + 3 * m2) * v1 + (m3 - m2) * h * f1
        ok = sgn * (H - Vth) >= 0
        hi = np.where(ok, m, hi)
        lo = np.where(ok, lo, m)
    return hi


def run_batch(b: Batch) -> dict:
    """Integrate every row of the batch on the common grid t_k = k*dt, k = 0..N.

    With ``Cgd != 0`` (sensitivity study only) the model is
        (C + Cgd) v' = I_net(u, v) + w + Cgd u'(t).
    It is integrated in the variable x = v - kappa*u, kappa = Cgd / (C + Cgd), for which
        (C + Cgd) x' = I_net(u, x + kappa*u) + w,
    so no derivative of the input is needed and input kinks cost no accuracy.
    """
    n = b.v0.size
    VDD, kn, kp, Vtn, Vtp = (np.ascontiguousarray(b.theta[:, i]) for i in range(5))
    h = b.dt
    N = b.N
    eps, Cmin, Cmax, Vlo, Vhi, sgn, Vth = b.eps, b.Cmin, b.Cmax, b.Vlo, b.Vhi, b.sgn, b.Vth
    miller = b.Cgd != 0.0
    Ctot = b.C + b.Cgd
    invC = 1.0 / Ctot
    kap = b.Cgd / Ctot if miller else None
    Wt = np.ascontiguousarray(b.W.T)
    w_idx = b.w_idx
    i1 = np.flatnonzero(b.fb == 1)
    i2 = np.flatnonzero(b.fb == 2)
    i3 = np.flatnonzero(b.fb == 3)
    i4 = np.flatnonzero(b.fb == 4)
    i5 = np.flatnonzero(b.fb == 5)
    i6 = np.flatnonzero(b.fb == 6)
    i56 = np.concatenate([i5, i6])
    if i56.size:
        if b.box is None:
            raise ValueError("fb codes 5/6 need Batch.box")
        bx = [np.ascontiguousarray(b.box[:, j])[:, None] for j in range(5)]
    vmid = 0.5 * (Vlo + Vhi)
    law = b.law
    U = b.U
    u_row = b.u_row

    def f(k, x):
        uk = U[k] if u_row is None else u_row
        v = x + kap * U[k] if miller else x
        I = law(uk, v, VDD, kn, kp, Vtn, Vtp)
        num = I + Wt[k][w_idx]
        if i1.size:
            vv = v[i1]
            num[i1] = I[i1] + np.where(vv >= Vhi - b.adv_delta, eps, np.where(vv <= Vlo + b.adv_delta, -eps, -sgn * eps))
        if i2.size:
            num[i2] = I[i2] + np.where(v[i2] >= vmid, eps, -eps)
        out = num * invC
        if i3.size:
            xx = I[i3] - eps
            out[i3] = np.where(xx >= 0, xx / Cmax, xx / Cmin)
        if i4.size:
            xx = I[i4] + eps
            out[i4] = np.where(xx >= 0, xx / Cmin, xx / Cmax)
        if i56.size:
            ub = uk if u_row is None else u_row[i56][None, :]
            Iall = law(ub, v[i56][None, :], *bx)  # (n_corners, n_rows)
            if i5.size:
                xx = Iall[:, : i5.size].min(axis=0) - eps
                out[i5] = np.where(xx >= 0, xx / Cmax, xx / Cmin)
            if i6.size:
                xx = Iall[:, i5.size :].max(axis=0) + eps
                out[i6] = np.where(xx >= 0, xx / Cmin, xx / Cmax)
        return out

    v = b.v0.astype(float).copy()
    x = v - kap * U[0] if miller else v
    vmin = v.copy()
    vmax = v.copy()
    vmin_later = np.full(n, np.inf)
    vmax_later = np.full(n, -np.inf)
    crossed = np.zeros(n, dtype=bool)
    t_cross = np.full(n, np.nan)
    g_after_cross = np.full(n, np.inf)
    g_after_deadline = np.full(n, np.inf)
    v_deadline = np.full(n, np.nan)
    n_recross = np.zeros(n, dtype=np.int64)
    pend = None
    v_prev = k1_prev = None
    rec_t, rec_v = [], []

    for step in range(N + 1):
        k1 = f(2 * step, x)
        if pend is not None:
            if miller:  # derivative of v is not k1 here; linear event location is accurate enough
                th = (Vth - v_prev[pend]) / (v[pend] - v_prev[pend])
            else:
                th = _hermite_root(v_prev[pend], k1_prev[pend], v[pend], k1[pend], h, Vth, sgn)
            t_cross[pend] = (step - 1 + th) * h
            pend = None
        if step >= b.s_idx:
            g = sgn * (v - Vth)
            if step == b.s_idx:
                now = g >= 0
                crossed |= now
                t_cross[now] = step * h
            np.minimum(g_after_cross, np.where(crossed, g, np.inf), out=g_after_cross)
            n_recross += crossed & (g < 0)
            if b.deadline_idx >= 0 and step >= b.deadline_idx:
                np.minimum(g_after_deadline, g, out=g_after_deadline)
                if step == b.deadline_idx:
                    v_deadline = v.copy()
        if b.record_every and step % b.record_every == 0:
            rec_t.append(step * h)
            rec_v.append(v[b.record_rows].copy())
        if step == N:
            break
        k2 = f(2 * step + 1, x + (0.5 * h) * k1)
        k3 = f(2 * step + 1, x + (0.5 * h) * k2)
        k4 = f(2 * step + 2, x + h * k3)
        x_new = x + (h / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)
        v_new = x_new + kap * U[2 * step + 2] if miller else x_new
        if step >= b.s_idx:
            newly = (~crossed) & (sgn * (v_new - Vth) >= 0)
            if newly.any():
                pend = np.flatnonzero(newly)
                crossed[pend] = True
        v_prev, k1_prev = v, k1
        x, v = x_new, v_new
        np.minimum(vmin, v, out=vmin)
        np.maximum(vmax, v, out=vmax)
        np.minimum(vmin_later, v, out=vmin_later)
        np.maximum(vmax_later, v, out=vmax_later)

    out = {
        "vmin": vmin,
        "vmax": vmax,
        "vmin_later": vmin_later,
        "vmax_later": vmax_later,
        "t_cross": t_cross,
        "g_after_cross": g_after_cross,
        "g_after_deadline": g_after_deadline,
        "v_deadline": v_deadline,
        "v_final": v,
        "n_recross": n_recross,
    }
    if b.record_every:
        out["rec_t"] = np.array(rec_t)
        out["rec_v"] = np.array(rec_v)
    return out


def half_step_times(dt: float, N: int) -> np.ndarray:
    return 0.5 * dt * np.arange(2 * N + 1)


# --------------------------------------------------------------------------
# Reference (adaptive) integration of a single scenario
# --------------------------------------------------------------------------

def make_rhs(law, th, C, u_fun, w_fun=None, fb=0, sgn=1, eps=0.0, Cmin=None, Cmax=None, Vlo=None, Vhi=None, adv_delta=0.02, box=None):
    """Scalar right-hand side v' = f(t, v) for one scenario (``th`` is ignored for fb 5/6)."""
    vmid = None if Vlo is None else 0.5 * (Vlo + Vhi)
    if fb in (5, 6):
        bx = [np.ascontiguousarray(np.asarray(box)[:, j]) for j in range(5)]

        def rhs_box(t, y):
            Iall = law(u_fun(t), y[0], *bx)
            if fb == 5:
                x = float(Iall.min()) - eps
                return [x / Cmax if x >= 0 else x / Cmin]
            x = float(Iall.max()) + eps
            return [x / Cmin if x >= 0 else x / Cmax]

        return rhs_box
    VDD, kn, kp, Vtn, Vtp = (float(x) for x in th)

    def rhs(t, y):
        v = y[0]
        I = float(law(u_fun(t), v, VDD, kn, kp, Vtn, Vtp))
        if fb == 0:
            w = w_fun(t) if w_fun is not None else 0.0
            return [(I + w) / C]
        if fb == 1:
            w = eps if v >= Vhi - adv_delta else (-eps if v <= Vlo + adv_delta else -sgn * eps)
            return [(I + w) / C]
        if fb == 2:
            return [(I + (eps if v >= vmid else -eps)) / C]
        if fb == 3:
            x = I - eps
            return [x / Cmax if x >= 0 else x / Cmin]
        if fb == 4:
            x = I + eps
            return [x / Cmin if x >= 0 else x / Cmax]
        raise ValueError(fb)

    return rhs


def solve_ref(rhs, v0, t_end, method="DOP853", rtol=1e-11, atol=1e-13, breaks=(), Vth=None, sgn=1, t_from=0.0, max_step=np.inf, dense_t=None):
    """Integrate on [0, t_end], restarting at ``breaks``. Returns dict with the first
    time >= t_from at which sgn*(v - Vth) >= 0 (event-located), extremes, and optional samples."""
    inner = set(x for x in breaks if 0.0 < x < t_end)
    if 0.0 < t_from < t_end:
        inner.add(t_from)  # the checking window starts exactly at a restart point
    cuts = [0.0] + sorted(inner) + [t_end]
    y = [float(v0)]
    t_cross = None
    vmin = vmax = float(v0)
    nfev = 0
    samples_t, samples_v = [], []

    def ev(t, yy):
        return yy[0] - Vth

    ev.direction = float(sgn)
    ev.terminal = False
    for a, bnd in zip(cuts[:-1], cuts[1:]):
        want_dense = dense_t is not None
        if Vth is not None and t_cross is None and a >= t_from and sgn * (y[0] - Vth) >= 0:
            t_cross = a  # already valid when the window opens (or exactly at a restart point)
        sol = solve_ivp(rhs, (a, bnd), y, method=method, rtol=rtol, atol=atol, events=[ev] if Vth is not None else None, max_step=max_step, dense_output=want_dense)
        if not sol.success:
            raise RuntimeError(sol.message)
        nfev += sol.nfev
        vmin = min(vmin, float(sol.y[0].min()))
        vmax = max(vmax, float(sol.y[0].max()))
        if Vth is not None and t_cross is None and a >= t_from and sol.t_events[0].size:
            t_cross = float(sol.t_events[0][0])
        if want_dense:
            m = (dense_t >= a) & ((dense_t < bnd) | ((bnd == t_end) & (dense_t <= bnd)))
            if m.any():
                samples_t.append(dense_t[m])
                samples_v.append(sol.sol(dense_t[m])[0])
        y = [float(sol.y[0, -1])]
    out = {"t_cross": t_cross, "v_final": y[0], "vmin": vmin, "vmax": vmax, "nfev": nfev}
    if dense_t is not None:
        out["t"] = np.concatenate(samples_t) if samples_t else np.array([])
        out["v"] = np.concatenate(samples_v) if samples_v else np.array([])
    return out


def rk4_single(rhs, v0, t_end, dt, Vth=None, sgn=1, t_from=0.0, event="hermite"):
    """Plain fixed-step RK4 for one scenario with linear or Hermite event location (convergence study)."""
    N = int(round(t_end / dt))
    v = float(v0)
    t_cross = None
    if Vth is not None and t_from <= 0.0 and sgn * (v - Vth) >= 0:
        t_cross = 0.0
    k1 = rhs(0.0, [v])[0]
    for i in range(N):
        t = i * dt
        k2 = rhs(t + 0.5 * dt, [v + 0.5 * dt * k1])[0]
        k3 = rhs(t + 0.5 * dt, [v + 0.5 * dt * k2])[0]
        k4 = rhs(t + dt, [v + dt * k3])[0]
        vn = v + dt / 6.0 * (k1 + 2 * k2 + 2 * k3 + k4)
        k1n = rhs(t + dt, [vn])[0]
        if Vth is not None and t_cross is None and t + dt >= t_from and sgn * (vn - Vth) >= 0:
            if sgn * (v - Vth) >= 0:
                t_cross = max(t, t_from)
            elif event == "linear":
                t_cross = t + dt * (Vth - v) / (vn - v)
            else:
                th = float(_hermite_root(np.array([v]), np.array([k1]), np.array([vn]), np.array([k1n]), dt, Vth, sgn)[0])
                t_cross = t + th * dt
        v, k1 = vn, k1n
    return {"t_cross": t_cross, "v_final": v}

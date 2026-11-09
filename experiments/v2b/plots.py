"""Static figures (PNG). Every figure has a CSV/JSON twin in the same run directory;
the figure is a view of that data, never the only place a number lives.

Style: light surface, thin marks, recessive solid hairline grid, one y-axis per
panel, categorical colours in a fixed order (blue, orange, aqua; validated for
colour-vision deficiency on all pairs), text in ink colours only, dashed lines
reserved for thresholds and bounds.
"""
from __future__ import annotations

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"
PNG_META = {"Software": "voltage-to-bit workstream D (matplotlib)"}


def _style():
    plt.rcParams.update({
        "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
        "font.family": ["Helvetica Neue", "Helvetica", "Arial", "DejaVu Sans"], "font.size": 9,
        "axes.edgecolor": AXIS, "axes.linewidth": 0.8, "axes.labelcolor": INK2, "axes.titlesize": 10, "axes.titleweight": "bold", "axes.titlecolor": INK, "axes.titlelocation": "left",
        "axes.spines.top": False, "axes.spines.right": False, "axes.grid": True, "axes.axisbelow": True,
        "grid.color": GRID, "grid.linewidth": 0.6, "grid.linestyle": "-",
        "xtick.color": MUTED, "ytick.color": MUTED, "xtick.labelcolor": INK2, "ytick.labelcolor": INK2, "xtick.major.size": 3, "ytick.major.size": 3,
        "lines.linewidth": 2.0, "lines.solid_capstyle": "round", "lines.solid_joinstyle": "round",
        "legend.frameon": False, "legend.fontsize": 8.5, "legend.labelcolor": INK2,
        "figure.dpi": 100, "savefig.dpi": 160,
    })


def _save(fig, path):
    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path, metadata=PNG_META)
    plt.close(fig)


def _hline(ax, y, label, x=0.995, va="bottom", color=MUTED):
    ax.axhline(y, color=color, lw=1.0, ls=(0, (4, 3)), zorder=1)
    ax.annotate(label, xy=(x, y), xycoords=("axes fraction", "data"), xytext=(0, 2 if va == "bottom" else -2), textcoords="offset points", ha="right", va=va, color=INK2, fontsize=8)


def _vline(ax, x, label, y=0.03, ha="left", color=MUTED):
    ax.axvline(x, color=color, lw=1.0, ls=(0, (4, 3)), zorder=1)
    ax.annotate(label, xy=(x, y), xycoords=("data", "axes fraction"), xytext=(3 if ha == "left" else -3, 0), textcoords="offset points", ha=ha, va="bottom", color=INK2, fontsize=8)


def _note(fig, text, frac=0.05):
    """Source note in a reserved strip under the axes (so it never collides with axis labels)."""
    fig.get_layout_engine().set(rect=(0.0, frac, 1.0, 1.0 - frac))
    fig.text(0.008, 0.012, text, ha="left", va="bottom", color=MUTED, fontsize=7.5)


def fig_margins(path, mc, F, cf):
    _style()
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.1), constrained_layout=True)
    for ax, x, bound, model, title, thr, thr_name, blabel in (
        (axes[0], mc["c_up"], mc["I_up"], mc["min_inet_up"], "Pull-up current while the input is at V_IL", F.VOH, "V_OH", "closed-form bound I_up(c)"),
        (axes[1], mc["c_dn"], mc["I_dn"], mc["min_pulldown"], "Pull-down current while the input is at V_IH", F.VOL, "V_OL", "closed-form bound I_dn(c)"),
    ):
        ax.plot(x, model, color=ORANGE, lw=5.0, alpha=0.45, label="model: minimum over the 32 corners")
        ax.plot(x, bound, color=BLUE, lw=2.0, label=blabel)
        _hline(ax, F.eps, f"disturbance allowance eps_I = {F.eps:g} uA")
        _vline(ax, thr, thr_name, y=0.86, ha="left" if thr_name == "V_OL" else "right")
        ax.set_ylim(0, None)
        ax.set_xlabel("output voltage c (V)")
        ax.set_ylabel("current (uA)")
        ax.set_title(title)
        ax.legend(loc="center left" if thr_name == "V_OH" else "center right", bbox_to_anchor=(0.02, 0.42) if thr_name == "V_OH" else (0.98, 0.42))
    _note(fig, "Illustrative design record (not fitted to a process). Data: 01_margins/margin_curves.csv")
    _save(fig, path)


def fig_barriers(path, mc, F, bar):
    _style()
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.1), constrained_layout=True)
    for ax, y, side, title in ((axes[0], mc["inward_hi"], "hi", "Restoring current at the top of the safe domain (v = V_hi)"), (axes[1], mc["inward_lo"], "lo", "Restoring current at the bottom of the safe domain (v = V_lo)")):
        ax.plot(mc["u"], y, color=BLUE, label="model: minimum over the 32 corners")
        cert = bar[side]["claimed_bound_uA"]["float"]
        tru = bar[side]["min_inward_current_uA"]["float"]
        _hline(ax, cert, f"certificate bound min(R) = {cert:g} uA", va="bottom")
        _hline(ax, F.eps, f"eps_I = {F.eps:g} uA", va="top")
        iu = float(bar[side]["argmin"]["u"])
        ax.plot([iu], [tru], "o", ms=7, color=BLUE, mec=SURFACE, mew=2, zorder=5)
        ax.annotate(f"model minimum\n{tru:g} uA at u = {iu:g} V", xy=(iu, tru), xytext=(-9, -6), textcoords="offset points", color=INK2, fontsize=8, ha="right", va="top")
        ax.set_ylim(0, 20)
        ax.set_xlabel("held input voltage u (V)")
        ax.set_ylabel("current into the safe domain (uA)")
        ax.set_title(title)
    _note(fig, "The vertical axis is cut at 20 uA (the curves continue upward). Data: 01_margins/barrier_curves.csv")
    _save(fig, path)


def fig_worst(path, wt, F, wc):
    _style()
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.1), constrained_layout=True)
    for ax, key, thr, thr_name, title in ((axes[0], "rise", F.VOH, "V_OH", "Slowest admissible rise (input held at V_IL)"), (axes[1], "fall", F.VOL, "V_OL", "Slowest admissible fall (input held at V_IH)")):
        t, v = wt[key]
        tau = wc[key]["tau_ns"]["float"]
        Tw = wc[key]["true_worst_case"]["quadrature_ns"]
        ax.plot(t, v, color=BLUE)
        _hline(ax, thr, thr_name, x=0.995, va="bottom" if key == "rise" else "top")
        ya, yb = (0.05, 0.15) if key == "rise" else (0.90, 0.80)
        _vline(ax, Tw, f"model worst case {Tw:.3f} ns", y=ya, ha="right" if key == "rise" else "left")
        _vline(ax, tau, f"proved bound tau = {tau:.3f} ns", y=yb, ha="right")
        ax.set_xlabel("time since the input became valid (ns)")
        ax.set_ylabel("output voltage (V)")
        ax.set_title(title)
        ax.set_xlim(0, t[-1])
    _note(fig, "Worst corner, C = C_max, disturbance held at the adverse bound, start at the far end of the safe domain. Data: 03_worstcase/worst_case_trajectories.csv")
    _save(fig, path)


def fig_ratio_hist(path, traj):
    _style()
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.9), constrained_layout=True, sharey=True)
    edges = np.array(traj["ratio_hist"]["bin_edges"][:-1], dtype=float)
    centers = 0.5 * (edges[:-1] + edges[1:])
    for ax, pol, name in ((axes[0], "L", "Rise (input low)"), (axes[1], "H", "Fall (input high)")):
        counts = np.array(traj["ratio_hist"][pol][:20])
        over = traj["ratio_hist"][pol][20]
        pp = traj["per_polarity"][pol]
        ax.bar(centers, counts, width=0.038, color=BLUE, linewidth=0)
        ax.axvline(1.0, color=MUTED, lw=1.0, ls=(0, (4, 3)))
        ax.annotate("bound (ratio 1)", xy=(1.0, 0.93), xycoords=("data", "axes fraction"), xytext=(-3, 0), textcoords="offset points", ha="right", color=INK2, fontsize=8)
        ax.annotate(f"largest observed {pp['max_ratio']:.3f}", xy=(pp["max_ratio"], 0), xytext=(0, 26), textcoords="offset points", ha="center", color=INK2, fontsize=8, arrowprops={"arrowstyle": "-", "color": MUTED, "lw": 0.8})
        ax.set_xlim(0, 1.05)
        ax.set_xlabel("observed crossing time / proved bound")
        ax.set_title(f"{name}: {int(counts.sum()):,} runs that had to move; {over} beyond the bound")
    axes[0].set_ylabel("number of runs")
    _note(fig, "Runs whose output was already valid when the input became valid are excluded here and counted in 02_trajectories/summary.json. Data: 02_trajectories/summary.json (ratio_hist)")
    _save(fig, path)


def fig_multiseg(path, wc):
    _style()
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.1), constrained_layout=True)
    rows = wc["convergence_table"]["rows"]
    for ax, key, title in ((axes[0], "rise", "Rise: multi-segment bound versus number of segments"), (axes[1], "fall", "Fall: multi-segment bound versus number of segments")):
        rr = [r for r in rows if r[0] == key]
        N = np.array([r[1] for r in rr], dtype=float)
        uni = np.array([r[2] for r in rr])
        opt = np.array([r[3] for r in rr])
        Tw, lim = rr[0][4], rr[0][5]
        ax.plot(N, uni, "-o", color=BLUE, ms=6.5, mec=SURFACE, mew=1.6, label="uniform breakpoints")
        ok = ~np.isnan(opt)
        ax.plot(N[ok], opt[ok], "-o", color=ORANGE, ms=6.5, mec=SURFACE, mew=1.6, label="optimised breakpoints (1 mV grid)")
        _hline(ax, Tw, f"model worst-case delay {Tw:.4f} ns", va="top")
        if abs(lim - Tw) > 1e-6:
            _hline(ax, lim, f"limit of the bound as N grows {lim:.4f} ns", va="bottom")
        ax.annotate(f"N = 1 is tau = {uni[0]:.3f} ns", xy=(N[0], uni[0]), xytext=(10, -2), textcoords="offset points", color=INK2, fontsize=8, va="center")
        lo_, hi_ = ax.get_ylim()
        ax.set_ylim(min(Tw, lim) - 0.07 * (hi_ - min(Tw, lim)), hi_)
        ax.set_xscale("log", base=2)
        ax.set_xticks(N)
        ax.set_xticklabels([str(int(n)) for n in N])
        ax.set_xlabel("number of segments N")
        ax.set_ylabel("delay bound (ns)")
        ax.set_title(title)
        ax.legend(loc="upper right")
    _note(fig, "Data: 03_worstcase/multisegment_convergence.csv and breakpoints.json")
    _save(fig, path)


def fig_convergence(path, conv):
    _style()
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.1), constrained_layout=True)
    rows = [r for r in conv["autonomous"]["tolerance_sweep"]["rows"] if r[0] == "rise"]
    ax = axes[0]
    for m, col in (("DOP853", BLUE), ("Radau", ORANGE), ("LSODA", AQUA)):
        rr = [r for r in rows if r[1] == m and isinstance(r[5], float) and r[5] == r[5]]
        x = np.array([r[2] for r in rr])
        y = np.abs(np.array([r[5] for r in rr]))
        ax.plot(x, np.maximum(y, 1e-16), "-o", color=col, ms=6, mec=SURFACE, mew=1.5, label=m)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.invert_xaxis()
    ax.set_xlabel("relative tolerance (tighter to the right)")
    ax.set_ylabel("|crossing time - quadrature reference| (ns)")
    ax.set_title("Adaptive solvers: error of the worst-case rise time")
    ax.legend(loc="upper right")
    rows = [r for r in conv["autonomous"]["rk4_step_sweep"]["rows"] if r[0] == "rise"]
    ax = axes[1]
    for ev, col, lab in (("linear", BLUE, "linear event location"), ("hermite", ORANGE, "cubic Hermite event location")):
        rr = [r for r in rows if r[2] == ev]
        x = np.array([r[1] for r in rr])
        y = np.abs(np.array([r[4] for r in rr]))
        ax.plot(x, np.maximum(y, 1e-16), "-o", color=col, ms=6, mec=SURFACE, mew=1.5, label=lab)
    ax.axvline(5e-4, color=MUTED, lw=1.0, ls=(0, (4, 3)))
    ax.annotate("step used for the run matrix", xy=(5e-4, 0.93), xycoords=("data", "axes fraction"), xytext=(4, 0), textcoords="offset points", ha="left", color=INK2, fontsize=8)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("fixed step (ns)")
    ax.set_ylabel("|crossing time - quadrature reference| (ns)")
    ax.set_title("Fixed-step RK4: error of the worst-case rise time")
    ax.legend(loc="lower right")
    _note(fig, "RK45 and BDF, and the fall transition, are in the CSV. Data: 04_convergence/tolerance_sweep.csv, rk4_step_sweep.csv")
    _save(fig, path)


def fig_controls(path, ctl, traj, F, taus):
    _style()
    fig, axes = plt.subplots(2, 2, figsize=(10.2, 7.4), constrained_layout=True)
    # (i) inverted capacitance bounds
    ax = axes[0, 0]
    t, v = traj["i_a_C_inverted"]
    a = ctl["i_invalid_parameter_bounds"]["a_capacitance_bounds_inverted"]
    tn = a["naive_tau_up_ns (uses the second entry as C_max)"]
    ax.plot(t, v, color=BLUE)
    _hline(ax, F.VOH, "V_OH")
    _vline(ax, tn, f"deadline computed from the inverted bounds, {tn:.3f} ns", y=0.03)
    ax.plot([tn], [a["exhibited_trajectory"]["v_at_naive_tau_V"]], "o", ms=7, color=BLUE, mec=SURFACE, mew=2, zorder=5)
    ax.set_title("(i) Inverted C bounds: output not yet valid at the computed deadline")
    # (ii) insufficient observation time
    ax = axes[0, 1]
    t, v = traj["ii_rise_worst_case"]
    r = ctl["ii_insufficient_observation_time"]["rise"]
    ax.plot(t, v, color=BLUE)
    _hline(ax, F.VOH, "V_OH")
    for smp in r["samples"][:2]:
        ax.plot([smp["t_ns"]], [smp["v_V"]], "o", ms=7, color=BLUE, mec=SURFACE, mew=2, zorder=5)
        ax.annotate(f"sampled at {smp['t_ns']:.2f} ns: {smp['decoded']}", xy=(smp["t_ns"], smp["v_V"]), xytext=(8, -12), textcoords="offset points", color=INK2, fontsize=8)
    _vline(ax, taus[0], f"tau = {taus[0]:.3f} ns", y=0.03)
    ax.set_title("(ii) Sampling before the model's own delay")
    # (iii) miswired
    ax = axes[1, 0]
    t1, v1 = traj["iii_input_low_start_low"]
    t2, v2 = traj["iii_input_high_start_high"]
    ax.plot(t1, v1, color=BLUE, label="input low, start low: stays low")
    ax.plot(t2, v2, color=ORANGE, label="input high, start high: stays high")
    _hline(ax, F.VOH, "V_OH")
    _hline(ax, F.VOL, "V_OL", va="top")
    ax.set_xlim(0, 6)
    ax.set_ylim(F.Vlo - 0.25, F.Vhi + 0.1)
    ax.legend(loc="center right")
    ax.set_title("(iii) Swapped transistor roles: the output follows the input")
    # (iv) disturbance beyond the margin
    ax = axes[1, 1]
    t, v = traj["iv_rise_eps_x1.05"]
    tb, vb = traj["ii_rise_worst_case"]
    ax.plot(tb, vb, color=MUTED, lw=1.6, label=f"design eps_I = {F.eps:g} uA")
    ax.plot(t, v, color=BLUE, label="eps = 1.05 x I_up(V_OH): stuck below V_OH")
    _hline(ax, F.VOH, "V_OH")
    ax.set_xlim(0, 12)
    ax.legend(loc="lower right")
    ax.set_title("(iv) Disturbance larger than the current margin")
    for ax in axes.ravel():
        ax.set_xlabel("time (ns)")
        ax.set_ylabel("output voltage (V)")
    _note(fig, "Each panel is an exhibited trajectory of the stated (deliberately broken) setup. Data: 05_negative_controls/trajectories.csv, controls.json", frac=0.03)
    _save(fig, path)


def fig_transfer(path, tc, F):
    _style()
    fig, ax = plt.subplots(1, 1, figsize=(6.6, 4.6), constrained_layout=True)
    ax.fill_between(tc["u"], tc["v_min_envelope"], tc["v_max_envelope"], color=BLUE, alpha=0.12, linewidth=0, label="all 32 corners, |w| <= eps_I")
    ax.plot(tc["u"], tc["v_nominal"], color=BLUE, label="nominal, w = 0")
    _hline(ax, F.VOH, "V_OH (decodes high above)")
    _hline(ax, F.VOL, "V_OL (decodes low below)", va="top")
    _vline(ax, F.VIL, "V_IL", y=0.5, ha="right")
    _vline(ax, F.VIH, "V_IH", y=0.5, ha="left")
    ax.set_xlabel("held input voltage u (V)")
    ax.set_ylabel("settled output voltage (V)")
    ax.set_title("Settled output of the formal model versus held input")
    ax.legend(loc="center right", bbox_to_anchor=(0.99, 0.42))
    _note(fig, "Between V_OL and V_OH the output decodes to 'undefined'. Data: 06_boundary/transfer_curves.csv")
    _save(fig, path)


def fig_sensitivity(path, sens, F):
    _style()
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.1), constrained_layout=True)
    ax = axes[0]
    floor = 0.01
    res = [r for r in sens["residual"]["rows"] if r[1] == "channel-length modulation"]
    lam = np.array([r[2] for r in res])
    same = np.array([r[6] for r in res])
    sw = {}
    for r in sens["sandwich"]["rows"]:
        if r[1] == "channel-length modulation" and r[2] == "nominal":
            sw[float(r[0].split("=")[1].split("/")[0])] = r[10]
    ks = sorted(sw)
    ax.plot(lam, same, "-o", color=BLUE, ms=6.5, mec=SURFACE, mew=1.6, label="one fixed parameter point (worst corner)")
    ax.plot(ks, [max(sw[k], floor) for k in ks], "-o", color=ORANGE, ms=6.5, mec=SURFACE, mew=1.6, label="the parameter-box tube (nominal device)")
    zeros = [k for k in ks if sw[k] < floor]
    if zeros:
        ax.annotate("inside the tube (residual 0)", xy=(zeros[0], floor), xytext=(0, 9), textcoords="offset points", color=INK2, fontsize=8)
    _hline(ax, 1.0, "residual = eps_I")
    ax.set_yscale("log")
    ax.set_ylim(floor * 0.6, 300)
    ax.set_xlabel("channel-length modulation lambda (1/V)")
    ax.set_ylabel("largest current residual on the grid / eps_I")
    ax.set_title("Channel-length modulation: additive allowance versus box tube")
    leg = ax.legend(loc="lower right", bbox_to_anchor=(0.995, 0.09), title="distance of the perturbed current from", title_fontsize=8.5, alignment="left")
    leg.get_title().set_color(INK2)
    ax = axes[1]
    rows = sens["miller"]["rows"]
    for cgd, col in ((0.25, BLUE), (0.5, ORANGE), (1.0, AQUA)):
        rr = [r for r in rows if abs(r[0] - cgd) < 1e-9]
        x = np.array([r[2] for r in rr])
        y = 1e3 * np.maximum(np.array([r[9] for r in rr]), np.array([r[10] for r in rr]))
        o = np.argsort(x)
        ax.plot(x[o], y[o], "-o", color=col, ms=6.5, mec=SURFACE, mew=1.6, label=f"C_gd = {cgd:g} fF")
        ax.annotate(f"{cgd:g} fF", xy=(x[o][-1], y[o][-1]), xytext=(6, 0), textcoords="offset points", color=INK2, fontsize=8, va="center")
    ax.set_xscale("log")
    ax.set_xlabel("input slew rate (V/ns)")
    ax.set_ylabel("largest excursion outside [V_lo, V_hi] (mV)")
    ax.set_title("Gate-drain feedthrough: output leaves the safe domain at fast edges")
    ax.legend(loc="upper left")
    ax.margins(x=0.12)
    _note(fig, "SENSITIVITY STUDY of the model form, not validation against a device; finite grids, illustrative C_gd. Data: 07_sensitivity/*.csv")
    _save(fig, path)

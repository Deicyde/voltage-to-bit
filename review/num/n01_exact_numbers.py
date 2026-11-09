#!/usr/bin/env python3
"""Workstream E, numeric probe n01.

Independent exact (rational) recomputation of the six margin numbers, the two
deadlines, the certificate time and the contamination slope of the illustrative
instance, from the JSON design record. Nothing is imported from the project.

usage: n01_exact_numbers.py <path to designs/illustrative-1v8.json>
"""
import hashlib
import json
import sys
from fractions import Fraction as Fr

path = sys.argv[1]
raw = open(path, "rb").read()
rec = json.loads(raw)
print("sha256(json) =", hashlib.sha256(raw).hexdigest())

b = rec["box"]
VDDlo, VDDhi = map(Fr, b["VDD"])
knlo, knhi = map(Fr, b["kn"])
kplo, kphi = map(Fr, b["kp"])
Vtnlo, Vtnhi = map(Fr, b["Vtn"])
Vtplo, Vtphi = map(Fr, b["Vtp"])
Clo, Chi = map(Fr, b["C"])
eps = Fr(rec["eps"])
VIL, VIH, VOL, VOH = (Fr(rec["thresholds"][k]) for k in ("VIL", "VIH", "VOL", "VOH"))
Vlo, Vhi = Fr(rec["safe_domain"]["Vlo"]), Fr(rec["safe_domain"]["Vhi"])
uHi, uLo = Fr(rec["barrier_split"]["uHi"]), Fr(rec["barrier_split"]["uLo"])


def psq(x):
    return x * x if x > 0 else Fr(0)


def Iup(c):
    return kplo / 2 * (psq(VDDlo - VIL - Vtphi) - psq(c - VIL - Vtphi)) - knhi / 2 * psq(VIL - Vtnlo)


def Idn(c):
    return knlo / 2 * (psq(VIH - Vtnhi) - psq(VIH - c - Vtnhi)) - kphi / 2 * psq(VDDhi - VIH - Vtplo)


RhiP = kplo / 2 * (psq(VDDlo - uHi - Vtphi + (Vhi - VDDhi)) - psq(VDDlo - uHi - Vtphi))
RhiN = knlo / 2 * (psq(uHi - Vtnhi) - psq(uHi - Vhi - Vtnhi))
RloN = knlo / 2 * (psq(uLo - Vlo - Vtnhi) - psq(uLo - Vtnhi))
RloP = kplo / 2 * (psq(VDDlo - uLo - Vtphi) - psq(Vlo - uLo - Vtphi))
tauUp = Chi * (VOH - Vlo) / (Iup(VOH) - eps)
tauDn = Chi * (Vhi - VOL) / (Idn(VOL) - eps)

claimed = {
    "Iup(VOH)": (Iup(VOH), Fr("10.476")),
    "Idn(VOL)": (Idn(VOL), Fr("16.296")),
    "RhiP": (RhiP, Fr("2.4")),
    "RhiN": (RhiN, Fr("2.312")),
    "RloN": (RloN, Fr("3.04")),
    "RloP": (RloP, Fr("3.136")),
    "tauUp": (tauUp, Fr(7250, 2119)),
    "tauDn": (tauDn, Fr(4575, 1787)),
}
ok = True
for name, (mine, lean) in claimed.items():
    flag = "ok" if mine == lean else "MISMATCH"
    ok &= mine == lean
    print(f"{name:9s} mine = {str(mine):>12s} = {float(mine):.6f}   Lean theorem value = {float(lean):.6f}   {flag}")
print("tauUp <= 3.43:", tauUp <= Fr("3.43"), "  tauDn <= 2.57:", tauDn <= Fr("2.57"))

# admissibility conditions, one by one
conds = {
    "VDD_pos": 0 < VDDlo, "VDD_le": VDDlo <= VDDhi, "kn_pos": 0 < knlo, "kn_le": knlo <= knhi,
    "kp_pos": 0 < kplo, "kp_le": kplo <= kphi, "Vtn_le": Vtnlo <= Vtnhi, "Vtp_le": Vtplo <= Vtphi,
    "C_pos": 0 < Clo, "C_le": Clo <= Chi, "eps_nonneg": 0 <= eps, "Vlo_le": Vlo <= 0,
    "Vhi_ge": VDDhi <= Vhi, "VOL_nonneg": 0 <= VOL, "VOL_le_VIL": VOL <= VIL, "VIL_lt_VIH": VIL < VIH,
    "VIH_le_VOH": VIH <= VOH, "VOH_le": VOH <= VDDlo, "up": eps < Iup(VOH), "dn": eps < Idn(VOL),
    "hiP": eps < RhiP, "hiN": eps < RhiN, "loN": eps < RloN, "loP": eps < RloP,
}
print("admissibility fields all true:", all(conds.values()), [k for k, v in conds.items() if not v])
slack = {k: float(v - eps) for k, v in (("up", Iup(VOH)), ("dn", Idn(VOL)), ("hiP", RhiP), ("hiN", RhiN), ("loN", RloN), ("loP", RloP))}
print("margin minus eps (uA):", slack)
print("largest eps for which the record stays Admissible: eps <", float(min(Iup(VOH), Idn(VOL), RhiP, RhiN, RloN, RloP)),
      "(binding field:", min(slack, key=slack.get) + ")")

# certificate [1.0, 1.2, 1.35]
t, l = Fr(0), Vlo
for c in (Fr("1.0"), Fr("1.2"), Fr("1.35")):
    m = (Iup(c) - eps) / Chi
    t += (c - l) / m
    l = c
print("riseTime of certificate [1.0,1.2,1.35] =", float(t), " <= 2.34:", t <= Fr("2.34"), "  <= 2.0:", t <= Fr("2.0"))

# contamination slope used by illustrative_no_early_high
ich = kphi / 2 * psq(VDDhi - 0 - Vtplo) + knhi / 2 * psq(Fr("0.40") - Vlo - Vtnlo)
slope = (ich + eps) / Clo
print("(IchargeMax 0 0.40 + eps)/Clo =", float(slope), " == 28.5508:", slope == Fr("28.5508"),
      "  0.25 + slope*0.038 =", float(Fr("0.25") + slope * Fr("0.038")))
print("ALL EXACT VALUES MATCH" if ok else "SOME VALUE DIFFERS")

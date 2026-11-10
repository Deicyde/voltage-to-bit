"""voltage-to-bit, workstream D: numerical experiments on the formal inverter model.

Everything here is written from ``docs/interface.md`` (DRAFT v0) and the design
record JSON only. It is deliberately independent of the Lean sources so that it
can serve as a check on them.

Units (interface.md section 2): V, uA, fF, ns, k in uA/V^2 (coherent: uA/fF = V/ns).
"""

MASTER_SEED = 20261109

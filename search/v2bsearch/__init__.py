"""Workstream F: propose -> screen -> formally check -> evaluate -> record.

Modules
-------
exact     exact rational mirror of the numeric conditions Lean checks (the cheap screen)
numeric   floating-point quadrature / simulation (numerical evidence only, never a proof)
propose   proposers: baseline, uniform, grid-optimal search, perturbation, bad controls
leanio    generation of Lean files and the formal check (`lake env lean`)
record    experiment-record format, canonical hashing, JSON Lines I/O
report    summary tables and plots

Entry point: ``python3 search/run_search.py`` (see ``docs/experiment-loop.md``).
"""

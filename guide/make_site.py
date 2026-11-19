#!/usr/bin/env python3
"""Write the landing page of the overlay's local site (no Verso site exists here).

`pdf-overlay/overlay.config.json` names this script as the site's one build
command; `pdf-overlay/tools/build_site.py` then copies the viewer into the
directory and adds its link to the page. The directory is under `.lake/`, which
git ignores.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / ".lake" / "build" / "guide-site"
ROOT.mkdir(parents=True, exist_ok=True)
(ROOT / "index.html").write_text("""<!doctype html>
<html lang="en">
<head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>voltage-to-bit: the specification in plain words</title></head>
<body>
<h1>What voltage-to-bit specifies</h1>
<p>The specification in plain words, each passage linked to the Lean that states it.</p>
</body>
</html>
""", encoding="utf-8")
print(f"wrote {ROOT / 'index.html'}")

"""Build a machine's proof-status page from a JSON file.

usage: python3 tools/pages/build_status.py STATUS.json OUT.html

The page sorts every claim by what it rests on, so that a reader never mistakes evidence for proof:

  kernel     proved in Lean, checked by Lean's kernel alone (standard axioms; `decide`, `rfl`, ordinary proofs)
  native     proved in Lean with `native_decide` (also trusts Lean's compiler)
  trusted    computed outside Lean by a program in the repository (C or Python), exhaustive, and checked as the
             entry says, but not proved
  heuristic  evidence only: sampling, extrapolation, a pattern seen so far
  open       not known

The JSON has: title, machine, crumb (text after the site name), intro (list of paragraphs), asof, verdict (list of
paragraphs), sections (optional list of {heading, paragraphs}), claims (list of {level, title, text, where}), and
check (shell lines).  Text fields may hold inline HTML (code, b, i, a).  The design is the one of
pages/proof-status.html (same colours, fonts and tags), written out here so that new pages share it without editing
that page.
"""
import html
import json
import sys

LEVELS = [
    ("kernel", "t-kernel", "Proved in Lean, kernel-checked", "checked by Lean's kernel alone"),
    ("native", "t-native", "Proved in Lean with native_decide", "evaluated by compiled code"),
    ("trusted", "t-comp", "Computed, not proved", "C or Python in the repository, exhaustive"),
    ("heuristic", "t-heur", "Evidence only", "sampling, extrapolation, patterns"),
    ("open", "t-open", "Open", "not known"),
]

CSS = """
:root {
  --paper: #EEF1F5; --surface: #FFFFFF; --ink: #142033; --muted: #5A6679; --rule: #D0D8E2; --link: #2B59CF;
  --kernel: #1F7A4D; --kernel-bg: #E2F3EA; --native: #8A5A00; --native-bg: #FBF0D9;
  --comp: #5B3FB8; --comp-bg: #ECE7FA; --heur: #3D5A80; --heur-bg: #E3EAF3; --open: #B3261E; --open-bg: #FBE6E4;
  --font-display: "Martian Mono", ui-monospace, "SFMono-Regular", Menlo, Consolas, monospace;
  --font-body: "Atkinson Hyperlegible", system-ui, -apple-system, "Segoe UI", Roboto, sans-serif;
  --r: 6px;
  color-scheme: light;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --paper: #0E131A; --surface: #161E29; --ink: #E5EBF3; --muted: #95A2B4; --rule: #2B3644; --link: #7C9DFF;
    --kernel: #6FD3A0; --kernel-bg: #15301F; --native: #F0C060; --native-bg: #33280F;
    --comp: #B9A6F5; --comp-bg: #251C42; --heur: #9DB8DA; --heur-bg: #1B2838; --open: #FF8A80; --open-bg: #3A1714;
    color-scheme: dark;
  }
}
:root[data-theme="dark"] {
  --paper: #0E131A; --surface: #161E29; --ink: #E5EBF3; --muted: #95A2B4; --rule: #2B3644; --link: #7C9DFF;
  --kernel: #6FD3A0; --kernel-bg: #15301F; --native: #F0C060; --native-bg: #33280F;
  --comp: #B9A6F5; --comp-bg: #251C42; --heur: #9DB8DA; --heur-bg: #1B2838; --open: #FF8A80; --open-bg: #3A1714;
  color-scheme: dark;
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--paper); color: var(--ink); font-family: var(--font-body); font-size: 16px; line-height: 1.6; }
.wrap { max-width: 860px; margin: 0 auto; padding: 40px 16px 56px; display: grid; gap: 36px; }
h1, h2, h3 { font-family: var(--font-display); margin: 0; letter-spacing: -0.01em; text-wrap: balance; }
h1 { font-size: clamp(1.45rem, 3.2vw, 2.1rem); line-height: 1.2; }
h2 { font-size: 1.05rem; line-height: 1.35; }
h3 { font-size: 0.88rem; line-height: 1.4; }
p, ul, ol { margin: 0; }
a { color: var(--link); }
code { font-family: var(--font-display); font-size: 0.8em; overflow-wrap: anywhere; }
pre { margin: 0; background: var(--surface); border: 1px solid var(--rule); border-radius: var(--r); padding: 12px 14px; overflow-x: auto; font-family: var(--font-display); font-size: 0.74rem; line-height: 1.6; }
.top { display: grid; gap: 12px; max-width: 70ch; }
.crumb { font-size: 0.9rem; }
.machine { font-family: var(--font-display); font-size: 0.78rem; color: var(--muted); overflow-wrap: anywhere; }
.asof { font-size: 0.88rem; color: var(--muted); }
section { display: grid; gap: 14px; }
.prose { display: grid; gap: 12px; max-width: 70ch; }
.verdict { background: var(--surface); border: 1px solid var(--rule); border-left: 4px solid var(--link); border-radius: var(--r); padding: 16px 18px; display: grid; gap: 10px; }
.tag { display: inline-block; font-family: var(--font-display); font-size: 0.66rem; font-weight: 500; letter-spacing: 0.03em; padding: 1px 7px; border-radius: 999px; white-space: nowrap; vertical-align: 0.1em; }
.t-kernel { color: var(--kernel); background: var(--kernel-bg); }
.t-native { color: var(--native); background: var(--native-bg); }
.t-comp { color: var(--comp); background: var(--comp-bg); }
.t-heur { color: var(--heur); background: var(--heur-bg); }
.t-open { color: var(--open); background: var(--open-bg); }
.legend { display: flex; flex-wrap: wrap; gap: 8px 16px; font-size: 0.88rem; color: var(--muted); }
.legend span { display: inline-flex; align-items: center; gap: 6px; }
.cards { display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 12px; }
.card { background: var(--surface); border: 1px solid var(--rule); border-radius: var(--r); padding: 14px 16px; display: grid; gap: 8px; align-content: start; }
.card p { font-size: 0.94rem; }
.card .where { font-size: 0.84rem; color: var(--muted); }
.card.open { border-left: 4px solid var(--open); }
.empty { color: var(--muted); font-size: 0.94rem; }
footer { font-size: 0.88rem; color: var(--muted); display: grid; gap: 6px; }
"""

FONTS = ('<link rel="preconnect" href="https://fonts.googleapis.com">\n'
         '<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
         '<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible:ital,wght@0,400;'
         '0,700;1,400&family=Martian+Mono:wght@400;500;700&display=swap">')


def build(spec, home="../index.html"):
    claims = spec.get("claims", [])
    known = {lv[0] for lv in LEVELS}
    for c in claims:
        if c["level"] not in known:
            raise ValueError(f"unknown level {c['level']!r} in claim {c.get('title')!r}")
    out = ["<!doctype html>", '<html lang="en">', "<head>", '<meta charset="utf-8">',
           '<meta name="viewport" content="width=device-width,initial-scale=1">',
           f"<title>{html.escape(spec['title'])}</title>",
           f'<meta name="description" content="{html.escape(spec.get("description", spec["title"]))}">',
           FONTS, f"<style>{CSS}</style>", "</head>", "<body>", '<main class="wrap">', '  <header class="top">',
           f'    <p class="crumb"><a href="{home}">Busy Beaver Explorer</a> / {spec.get("crumb", "")}</p>',
           f"    <h1>{spec['title']}</h1>", f'    <p class="machine">{html.escape(spec["machine"])}</p>']
    out += [f"    <p>{p}</p>" for p in spec.get("intro", [])]
    if spec.get("asof"):
        out.append(f'    <p class="asof">{spec["asof"]}</p>')
    out.append("  </header>")
    if spec.get("verdict"):
        out += ['  <section aria-labelledby="h-short">', '    <h2 id="h-short">In short</h2>', '    <div class="verdict">']
        out += [f"      <p>{p}</p>" for p in spec["verdict"]]
        out += ["    </div>", "  </section>"]
    for i, s in enumerate(spec.get("sections", [])):
        out += [f'  <section aria-labelledby="h-s{i}">', f'    <h2 id="h-s{i}">{s["heading"]}</h2>', '    <div class="prose">']
        out += [f"      <p>{p}</p>" for p in s.get("paragraphs", [])]
        out += ["    </div>", "  </section>"]
    out += ['  <section aria-labelledby="h-claims">', '    <h2 id="h-claims">What each result rests on</h2>',
            '    <div class="legend" aria-label="Legend">']
    for key, cls, _, gloss in LEVELS:
        out.append(f'      <span><span class="tag {cls}">{key}</span> {gloss}</span>')
    out.append("    </div>")
    for key, cls, heading, _ in LEVELS:
        items = [c for c in claims if c["level"] == key]
        out += [f'    <h3><span class="tag {cls}">{key}</span> {heading}</h3>']
        if not items:
            out.append('    <p class="empty">Nothing yet.</p>')
            continue
        out.append('    <div class="cards">')
        for c in items:
            out.append(f'      <div class="card{" open" if key == "open" else ""}">')
            out.append(f"        <h3>{c['title']}</h3>")
            out.append(f"        <p>{c['text']}</p>")
            if c.get("where"):
                out.append(f'        <p class="where">{c["where"]}</p>')
            out.append("      </div>")
        out.append("    </div>")
    out.append("  </section>")
    if spec.get("check"):
        out += ['  <section aria-labelledby="h-check">', '    <h2 id="h-check">Check it yourself</h2>',
                "    <pre><code>" + html.escape("\n".join(spec["check"])) + "</code></pre>", "  </section>"]
    out += ["  <footer>", f'    <p>Built by <code>tools/pages/build_status.py</code> from <code>{html.escape(spec.get("source", ""))}</code>; '
            "edit that file and rebuild rather than editing this page.</p>",
            '    <p>Source: <a href="https://github.com/fractal-geometry-explorer/busy-beaver-explorer">'
            "github.com/fractal-geometry-explorer/busy-beaver-explorer</a></p>", "  </footer>",
            "</main>", "</body>", "</html>"]
    return "\n".join(out) + "\n"


def main(argv):
    if len(argv) != 2:
        print(__doc__, file=sys.stderr)
        return 1
    with open(argv[0]) as f:
        spec = json.load(f)
    spec.setdefault("source", argv[0])
    with open(argv[1], "w") as f:
        f.write(build(spec, spec.get("home", "../index.html")))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

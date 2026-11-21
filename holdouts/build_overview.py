"""Build the two overview pages of the holdouts: pages/holdouts/families.html and pages/holdouts/recent.html.

usage: python3 holdouts/build_overview.py      (build_pages.py also calls it, after the index)

families.html is the families of the undecided machines, from holdouts/families.json and the sections "How the
families were made" and "Recommended next attacks" of holdouts/FAMILIES.md (both written by regroup.py). Each
machine is shown with its standing today, read the same way as the index, so the page shows what was decided since
the families were drawn up.

recent.html is the newest results, from holdouts/recent.json, which is edited by hand: add an entry, newest first,
when a pull request changes what is known about a machine, then rebuild.
"""
import html
import json
import os
import re

import build_pages as bp

HERE = bp.HERE
PAGES = bp.PAGES
GH = "https://github.com/fractal-geometry-explorer/busy-beaver-explorer/"

STAND = [
    ("here", "Decided here"), ("computed", "Computed here, not proved"), ("outside", "Decided by an outside proof"),
    ("merged", "Proved elsewhere, merged"), ("pr", "Outside proof awaiting review"), ("cryptid", "Cryptid"),
    ("open", "Open")]
DECIDED = {"here", "computed", "outside"}


def rows_by_machine():
    with open(os.path.join(HERE, "triage.json")) as f:
        triage = json.load(f)
    with open(os.path.join(HERE, "known.json")) as f:
        known = {k: v for k, v in json.load(f).items() if not k.startswith("_")}
    spec_by = {s["machine"]: s for _, s in bp.specs()}
    return {r["m"]: r for r in bp.index_rows(triage, known, spec_by)}


def md_inline(s):
    """The little Markdown FAMILIES.md uses inside a line: code, bold, italics and links."""
    parts = re.split(r"(`[^`]*`)", s)
    out = []
    for p in parts:
        if p.startswith("`") and p.endswith("`") and len(p) > 1:
            out.append("<code>" + html.escape(p[1:-1]) + "</code>")
            continue
        p = html.escape(p, quote=False)
        p = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", p)
        p = re.sub(r"(?<![*\w])\*(?!\s)(.+?)\*(?!\w)", r"<i>\1</i>", p)
        p = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", lambda m: f'<a href="{link(m.group(2))}">{m.group(1)}</a>', p)
        out.append(p)
    return "".join(out)


def link(target):
    """A link written in holdouts/FAMILIES.md, made to work from pages/holdouts/."""
    if re.match(r"^[a-z]+:", target):
        return target
    if target.startswith("../pages/holdouts/"):
        return target[len("../pages/holdouts/"):]
    return GH + "blob/main/holdouts/" + target


def md_section(md, heading):
    """The body of one '## heading' section of a Markdown file, as HTML paragraphs and lists."""
    m = re.search(r"^## " + re.escape(heading) + r"\s*$(.*?)(?=^## |\Z)", md, re.M | re.S)
    if not m:
        return ""
    out, lst = [], None
    for line in m.group(1).strip().splitlines():
        s = line.strip()
        if not s:
            if lst:
                out.append(f"</{lst}>")
                lst = None
            continue
        item = re.match(r"^(\d+\.|-)\s+(.*)$", s)
        if item:
            kind = "ol" if item.group(1)[0].isdigit() else "ul"
            if lst != kind:
                if lst:
                    out.append(f"</{lst}>")
                out.append(f"<{kind}>")
                lst = kind
            out.append("<li>" + md_inline(item.group(2)) + "</li>")
        else:
            if lst:
                out.append(f"</{lst}>")
                lst = None
            out.append("<p>" + md_inline(s) + "</p>")
    if lst:
        out.append(f"</{lst}>")
    return "\n".join(out)


def jsdata(x):
    return json.dumps(x, separators=(",", ":"), ensure_ascii=False).replace("</", "<\\/")


def machine_entry(M, rows, extra=None):
    r = rows.get(M, {})
    e = {"m": M, "st": r.get("st", "open"), "x": r.get("x", f"{M}/explainer.html"),
         "p": r.get("p", f"{M}/proof-status.html"), "id": r.get("id", ""), "sum": r.get("sum", ""),
         "dec": r.get("dec", "open")}
    if extra:
        e.update(extra)
    return e


def build_families(rows):
    fam = bp.families()
    p = os.path.join(HERE, "FAMILIES.md")
    md = open(p).read() if os.path.isfile(p) else ""
    groups = []
    for f in fam["families"] + fam["residual"]:
        ms = [machine_entry(m["m"], rows, {"tc": m.get("tc", ""), "set": m.get("set", ""),
                                           "ss": m.get("set_size", 1), "old": m.get("old", "")})
              for m in f["machines"]]
        ms.sort(key=lambda x: (x["set"] and int(x["set"][1:]) if x["set"][1:].isdigit() else 9999, x["m"]))
        groups.append({
            "id": f["id"], "name": f["name"], "rank": f.get("rank"), "short": f.get("short", ""),
            "mech": md_inline(f.get("mechanism", "")), "known": md_inline(f.get("known", "")),
            "tech": md_inline(f.get("technique", "")), "odds": md_inline(f.get("odds", "")),
            "residual": f in fam["residual"], "ms": ms})
    groups.sort(key=lambda g: (g["residual"], 99 if g["rank"] is None else g["rank"], g["id"]))
    page = (FAMILIES.replace("__ASOF__", html.escape(fam.get("asof", "")))
            .replace("__UNDEC__", str(fam.get("undecided", "")))
            .replace("__HOW__", md_section(md, "How the families were made"))
            .replace("__NEXT__", md_section(md, "Recommended next attacks"))
            .replace("__DATA__", jsdata({"groups": groups, "stand": STAND})))
    with open(os.path.join(PAGES, "families.html"), "w") as f:
        f.write(page)


def build_recent(rows):
    with open(os.path.join(HERE, "recent.json")) as f:
        rec = json.load(f)
    entries = []
    for e in rec["entries"]:
        x = dict(e)
        x["machines"] = [machine_entry(M, rows) for M in e.get("machines", [])]
        entries.append(x)
    page = (RECENT.replace("__ASOF__", html.escape(rec.get("asof", "")))
            .replace("__DATA__", jsdata({"entries": entries, "stand": STAND})))
    with open(os.path.join(PAGES, "recent.html"), "w") as f:
        f.write(page)


def build():
    rows = rows_by_machine()
    build_families(rows)
    build_recent(rows)


HEAD = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>__TITLE__</title>
<meta name="description" content="__DESC__">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible:ital,wght@0,400;0,700;1,400&family=Martian+Mono:wght@400;500;700&display=swap">
<style>
:root{--paper:#EEF1F5;--surface:#FFFFFF;--sunk:#E3E8EF;--ink:#142033;--muted:#5A6679;--rule:#D0D8E2;--link:#2B59CF;
 --s-here:#1C7A4D;--s-computed:#B4541A;--s-merged:#2350A8;--s-outside:#0F7C86;--s-pr:#9A6400;--s-cryptid:#7A4FB5;--s-open:#8A93A3;
 --mono:"Martian Mono",ui-monospace,Menlo,Consolas,monospace;--body:"Atkinson Hyperlegible",system-ui,sans-serif;color-scheme:light}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--paper:#0E131A;--surface:#161E29;--sunk:#0B1016;--ink:#E5EBF3;--muted:#95A2B4;--rule:#2B3644;--link:#7C9DFF;
 --s-here:#5CC893;--s-computed:#F0935C;--s-merged:#8FB0F0;--s-outside:#5CC4CE;--s-pr:#E7B453;--s-cryptid:#B99CF0;--s-open:#6C7686;color-scheme:dark}}
:root[data-theme="dark"]{--paper:#0E131A;--surface:#161E29;--sunk:#0B1016;--ink:#E5EBF3;--muted:#95A2B4;--rule:#2B3644;--link:#7C9DFF;
 --s-here:#5CC893;--s-computed:#F0935C;--s-merged:#8FB0F0;--s-outside:#5CC4CE;--s-pr:#E7B453;--s-cryptid:#B99CF0;--s-open:#6C7686;color-scheme:dark}
*{box-sizing:border-box}
body{margin:0;background:var(--paper);color:var(--ink);font:16px/1.55 var(--body)}
.wrap{max-width:1100px;margin:0 auto;padding:32px 16px 64px;display:grid;gap:24px}
h1,h2,h3{font-family:var(--mono);margin:0;letter-spacing:-.01em;text-wrap:balance}
h1{font-size:clamp(1.4rem,3.2vw,2rem)} h2{font-size:.82rem;text-transform:uppercase;letter-spacing:.08em;color:var(--muted)}
h3{font-size:1rem;line-height:1.35}
p{margin:0;max-width:72ch} a{color:var(--link)} code{font-family:var(--mono);font-size:.82em;overflow-wrap:anywhere}
ol,ul{margin:0;padding-left:1.4em;display:grid;gap:6px;max-width:78ch}
.crumb{font-size:.9rem;color:var(--muted)}
.panel{background:var(--surface);border:1px solid var(--rule);border-radius:8px;padding:16px;display:grid;gap:12px;min-width:0}
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px}
.stat b{display:block;font:700 1.5rem var(--mono)} .stat span{font-size:.88rem;color:var(--muted)}
.controls{display:flex;flex-wrap:wrap;gap:8px;align-items:center}
input[type=search]{flex:1 1 240px;min-width:0;padding:8px 10px;border:1px solid var(--rule);border-radius:6px;background:var(--paper);color:var(--ink);font:14px var(--mono)}
.chip{border:1px solid var(--rule);background:var(--paper);color:var(--ink);border-radius:999px;padding:4px 10px;font:inherit;font-size:.85rem;cursor:pointer}
.chip[aria-pressed=true]{background:var(--ink);color:var(--paper);border-color:var(--ink)}
.chip:focus-visible,summary:focus-visible,a:focus-visible{outline:2px solid var(--link);outline-offset:2px}
.dot{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:6px;flex:none}
.legend{display:flex;flex-wrap:wrap;gap:6px 16px;font-size:.85rem;color:var(--muted)} .legend span{display:inline-flex;align-items:center}
.tag{font-size:.75rem;padding:1px 7px;border-radius:4px;background:var(--sunk);white-space:nowrap}
.ms{display:grid;gap:4px}
.mrow{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:2px 12px;padding:6px 0;border-top:1px solid var(--rule);font-size:.85rem}
.mrow .mn{font-family:var(--mono);font-size:.76rem;overflow-wrap:anywhere;display:flex;align-items:baseline;gap:0}
.mrow .lk{white-space:nowrap;font-size:.8rem} .mrow .lk a{margin-left:8px}
.mrow .sm{grid-column:1/-1;color:var(--muted);font-size:.8rem;max-width:none}
.mrow .sm sup{line-height:0}
details>summary{cursor:pointer;color:var(--link);font-size:.9rem}
footer{font-size:.88rem;color:var(--muted)}
[hidden]{display:none!important}
__CSS__
</style>
</head>
<body>
<main class="wrap">
"""

FOOT = r"""
<footer>Generated by <code>holdouts/build_overview.py</code> from __SRC__. Source and research notes:
<a href="https://github.com/fractal-geometry-explorer/busy-beaver-explorer">github.com/fractal-geometry-explorer/busy-beaver-explorer</a>.</footer>
</main>
<script type="application/json" id="data">__DATA__</script>
<script>
const $ = id => document.getElementById(id);
const D = JSON.parse($("data").textContent);
const SL = Object.fromEntries(D.stand);
const esc = s => String(s).replace(/[&<>"]/g, c => ({"&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;"})[c]);
const dot = st => `<span class="dot" style="background:var(--s-${st})" title="${esc(SL[st] || st)}"></span>`;
function mrow(m, tag) {
  return `<div class="mrow" data-q="${esc((m.m + " " + m.id + " " + (tag || "")).toLowerCase())}">` +
    `<span class="mn">${dot(m.st)}<span>${esc(m.m)}${tag ? ` <span class="tag">${esc(tag)}</span>` : ""}</span></span>` +
    `<span class="lk">${esc(SL[m.st] || "")}<a href="${esc(m.x)}">explainer</a><a href="${esc(m.p)}">proof status</a></span>` +
    (m.sum ? `<p class="sm">${m.sum}</p>` : "") + `</div>`;
}
function legend(el) {
  el.innerHTML = D.stand.map(([k, l]) => `<span>${dot(k)}${esc(l)}</span>`).join("");
}
__JS__
</script>
</body>
</html>
"""

FAMILIES = (HEAD.replace("__TITLE__", "Families of the BB(6) holdouts")
            .replace("__DESC__", "The undecided BB(6) holdouts grouped into families that one proof technique could settle together, ranked, with what is known and what each family needs.")
            .replace("__CSS__", r"""
.fbars{display:grid;gap:6px}
.frow{display:grid;grid-template-columns:minmax(0,15rem) minmax(0,1fr) 3.2rem;gap:10px;align-items:center;font-size:.85rem;text-decoration:none;color:var(--ink)}
.frow:hover .fname{text-decoration:underline}
.fname{overflow:hidden;text-overflow:ellipsis;white-space:nowrap} .fname b{font-family:var(--mono);font-size:.78rem;margin-right:6px}
.track{display:flex;height:16px;gap:1px;min-width:0}
.track i{display:block;height:100%;min-width:2px}
.num{font:500 .8rem var(--mono);text-align:right;color:var(--muted)}
.fam{scroll-margin-top:16px}
.fam .meta{display:flex;flex-wrap:wrap;gap:6px}
.fam dl{display:grid;grid-template-columns:7rem minmax(0,1fr);gap:8px 14px;margin:0}
.fam dt{font:700 .72rem var(--mono);text-transform:uppercase;letter-spacing:.06em;color:var(--muted);padding-top:3px}
.fam dd{margin:0;max-width:78ch}
.sep{height:1px;background:var(--rule)}
@media (max-width:640px){.frow{grid-template-columns:minmax(0,1fr) 2.6rem}.frow .track{grid-column:1/-1;grid-row:2}
 .fam dl{grid-template-columns:1fr}.fam dt{padding-top:0}}
""")
            + r"""
<header style="display:grid;gap:10px">
 <p class="crumb"><a href="../index.html">Busy Beaver Explorer</a> / <a href="index.html">holdouts</a> / families</p>
 <h1>Families of the undecided holdouts</h1>
 <p>When the families were drawn up (__ASOF__), __UNDEC__ of the 608 holdouts were undecided here. They are grouped
 so that one proof technique could settle a whole family at once: machines whose tables differ in at most one
 transition (up to renaming the states and mirroring the tape) share most of their macro rules, and table sets with
 the same mechanism were joined. The families are ranked by how many machines one argument would settle, weighed by
 how likely it is to work. The ranking is a judgement, not a result.</p>
 <p>Each machine below shows its standing <b>today</b>, so a family shrinks on this page as its machines are
 decided. The same families filter the table of the <a href="index.html">holdout map</a>; see also the
 <a href="recent.html">latest results</a>.</p>
</header>

<section class="panel">
 <h2>Since the families were drawn up</h2>
 <div class="stats" id="stats"></div>
</section>

<section class="panel">
 <h2>The families by size</h2>
 <p>One bar per family, one segment per machine, coloured by where that machine stands today. Click a family to
 jump to it.</p>
 <div class="legend" id="legend"></div>
 <div class="fbars" id="fbars"></div>
</section>

<section class="panel">
 <h2>Recommended next attacks</h2>
 __NEXT__
</section>

<section class="panel">
 <h2>How the families were made</h2>
 __HOW__
</section>

<section class="panel">
 <h2>Find a machine</h2>
 <div class="controls"><input type="search" id="q" placeholder="Search a machine or bbchallenge id" aria-label="search the families">
 <button class="chip" id="undec" aria-pressed="false">only still undecided</button></div>
 <p class="crumb" id="qn" aria-live="polite"></p>
</section>

<div id="fams" style="display:grid;gap:16px"></div>
""" + FOOT.replace("__SRC__", "<code>holdouts/families.json</code> and <code>holdouts/FAMILIES.md</code>")
            .replace("__JS__", r"""
const G = D.groups, ORDER = D.stand.map(s => s[0]);
const uniq = ms => [...new Map(ms.map(m => [m.m, m])).values()];
const all = uniq(G.flatMap(g => g.ms));
const dec = all.filter(m => ["here", "computed", "outside"].includes(m.st)).length;
const fams = G.filter(g => !g.residual);
$("stats").innerHTML = [
  [all.length, "machines undecided when the families were drawn up"],
  [fams.length, "families (R00 to R15) with a shared technique"],
  [uniq(fams.flatMap(g => g.ms)).length, "machines in those families"],
  [dec, "decided since then (here, computed or by a compiled outside proof)"],
  [all.length - dec, "still undecided"]].map(([n, l]) => `<div class="stat"><b>${n}</b><span>${l}</span></div>`).join("");
legend($("legend"));
const max = Math.max(...G.map(g => g.ms.length));
$("fbars").innerHTML = G.map(g => {
  const ms = [...g.ms].sort((a, b) => ORDER.indexOf(a.st) - ORDER.indexOf(b.st));
  return `<a class="frow" href="#${g.id}"><span class="fname"><b>${esc(g.id)}</b>${esc(g.name)}</span>` +
    `<span class="track" style="width:${(100 * g.ms.length / max).toFixed(1)}%">` +
    ms.map(m => `<i style="flex:1;background:var(--s-${m.st})" title="${esc(m.m)}: ${esc(SL[m.st])}"></i>`).join("") +
    `</span><span class="num">${g.ms.length}</span></a>`;
}).join("");
$("fams").innerHTML = G.map(g => {
  const d = g.ms.filter(m => ["here", "computed", "outside"].includes(m.st)).length;
  const rank = g.residual ? "13 November family" : g.rank === null || g.rank === undefined ? "parked" : g.rank === 0 ? "first: compile" : "rank " + g.rank;
  const big = g.ms.length > 12;
  const rowsH = g.ms.map(m => mrow(m, m.ss > 1 ? `${m.set} (${m.ss})` : "")).join("");
  return `<section class="panel fam" id="${esc(g.id)}" data-f="${esc(g.id)}">
   <h3>${esc(g.id)}. ${esc(g.name)}</h3>
   <div class="meta"><span class="tag">${rank}</span><span class="tag">${g.ms.length} machines</span>${d ? `<span class="tag" style="color:var(--s-here)">${d} decided since</span>` : ""}${g.ms.some(m => m.st === "pr") ? `<span class="tag" style="color:var(--s-pr)">${g.ms.filter(m => m.st === "pr").length} awaiting review</span>` : ""}</div>
   ${g.mech || g.tech ? `<dl>${g.mech ? `<dt>Mechanism</dt><dd>${g.mech}</dd>` : ""}${g.known ? `<dt>Known</dt><dd>${g.known}</dd>` : ""}${g.tech ? `<dt>Technique</dt><dd>${g.tech}</dd>` : ""}${g.odds ? `<dt>Odds</dt><dd>${g.odds}</dd>` : ""}</dl>` :
     `<p>No technique shared by several of these is in sight; they are listed so that every undecided machine has a place.</p>`}
   ${big ? `<details><summary>The ${g.ms.length} machines</summary><div class="ms">${rowsH}</div></details>` : `<div class="ms">${rowsH}</div>`}
  </section>`;
}).join("");
let onlyU = false;
function filter() {
  const q = $("q").value.trim().toLowerCase();
  let n = 0;
  for (const sec of document.querySelectorAll(".fam")) {
    let k = 0;
    for (const r of sec.querySelectorAll(".mrow")) {
      const st = r.querySelector(".dot").getAttribute("style");
      const hit = (!q || r.dataset.q.includes(q)) && (!onlyU || !/s-(here|computed|outside)\)/.test(st));
      r.hidden = !hit; if (hit) k++;
    }
    sec.hidden = (q || onlyU) && !k; n += k;
    const det = sec.querySelector("details"); if (det && q) det.open = k > 0;
  }
  $("qn").textContent = q || onlyU ? `${n} machine${n === 1 ? "" : "s"} shown` : "";
}
$("q").addEventListener("input", filter);
$("undec").addEventListener("click", e => { onlyU = !onlyU; e.currentTarget.setAttribute("aria-pressed", onlyU); filter(); });
if (location.hash) { const t = document.getElementById(location.hash.slice(1)); if (t) t.scrollIntoView(); }
"""))

RECENT = (HEAD.replace("__TITLE__", "Latest holdout results")
          .replace("__DESC__", "The newest results on the BB(6) holdouts: proofs, structure found, families and no-halt bounds, each with what it rests on.")
          .replace("__CSS__", r"""
.tl{display:grid;gap:14px}
.ent{display:grid;gap:10px}
.ent .meta{display:flex;flex-wrap:wrap;gap:6px;align-items:center;font-size:.85rem;color:var(--muted)}
.ent .meta time{font-family:var(--mono);font-size:.78rem}
.kind{font:700 .7rem var(--mono);text-transform:uppercase;letter-spacing:.06em;padding:2px 7px;border-radius:4px;border:1px solid currentColor}
.k-halts{color:var(--s-here)} .k-bound{color:var(--s-computed)} .k-structure{color:var(--s-merged)} .k-family{color:var(--s-cryptid)} .k-method{color:var(--muted)}
.rest{font-size:.75rem;padding:1px 7px;border-radius:4px;background:var(--sunk)}
.ent p{max-width:80ch}
""")
          + r"""
<header style="display:grid;gap:10px">
 <p class="crumb"><a href="../index.html">Busy Beaver Explorer</a> / <a href="index.html">holdouts</a> / latest results</p>
 <h1>Latest results</h1>
 <p>What changed recently about the 608 BB(6) holdouts, newest first (up to __ASOF__). Each result says what it
 rests on. A <b>Coq</b> or <b>Lean</b> result is a checked proof. A <b>computation</b> is an exact run of the machine
 that proves nothing about later steps. Each machine links to its explainer, which runs it in your browser, and to
 its proof status, the full ledger of what is known. The dot shows where the machine stands today.</p>
 <p>For the bigger picture see the <a href="families.html">families of the undecided machines</a> and the
 <a href="index.html">holdout map</a>.</p>
</header>

<section class="panel">
 <div class="controls" id="kinds"></div>
 <div class="legend" id="legend"></div>
</section>

<div class="tl" id="tl"></div>
""" + FOOT.replace("__SRC__", "<code>holdouts/recent.json</code>")
          .replace("__JS__", r"""
const KIND = {halts: "decided", bound: "no-halt bound", structure: "structure", family: "families", method: "methods"};
const REST = {coq: "Coq proof", lean: "Lean proof", computation: "computation", judgement: "judgement", notes: "write-up"};
const GH = "https://github.com/fractal-geometry-explorer/busy-beaver-explorer/pull/";
let kind = "";
legend($("legend"));
const kinds = [...new Set(D.entries.map(e => e.kind))];
function chips() {
  $("kinds").innerHTML = `<span class="crumb">Show</span>` + [["", "everything"], ...kinds.map(k => [k, KIND[k] || k])]
    .map(([k, l]) => `<button class="chip" data-k="${k}" aria-pressed="${kind === k}">${esc(l)}</button>`).join("");
}
$("kinds").addEventListener("click", e => { const b = e.target.closest("button"); if (!b) return; kind = b.dataset.k; chips(); draw(); });
function draw() {
  $("tl").innerHTML = D.entries.filter(e => !kind || e.kind === kind).map(e => {
    const ms = e.machines.map(m => mrow(m, e.tag && e.machines.length <= 2 ? e.tag : "")).join("");
    const many = e.machines.length > 6;
    return `<article class="panel ent"><div class="meta"><span class="kind k-${esc(e.kind)}">${esc(KIND[e.kind] || e.kind)}</span>` +
      `<span class="rest">${esc(REST[e.rests] || e.rests)}</span><time datetime="${esc(e.date)}">${esc(e.date)}</time>` +
      e.prs.map(n => `<a href="${GH}${n}">PR ${n}</a>`).join(" ") + `</div>` +
      `<h3>${e.title}</h3><p>${e.text}</p>` +
      (e.link ? `<p><a href="${esc(e.link)}">Read the write-up</a></p>` : "") +
      (ms ? (many ? `<details><summary>The ${e.machines.length} machines</summary><div class="ms">${ms}</div></details>` : `<div class="ms">${ms}</div>`) : "") +
      `</article>`;
  }).join("");
}
chips(); draw();
"""))


if __name__ == "__main__":
    build()

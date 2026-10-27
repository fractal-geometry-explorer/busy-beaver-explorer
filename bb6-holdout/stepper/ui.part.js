
/* ================= page ================= */
const $ = id => document.getElementById(id);
const VAR = { G: '--gap', M: '--marker', W: '--wall', B: '--block' };
const full = b => { const s = b.toString(); return s[0] === '-' ? '−' + sepS(s.slice(1)) : sepS(s); };
const shape = ms => ms.map(m => m.t.length === 1 ? m.t : '?').join('');
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const REAL_MAX = 4096n, REAL_BUDGET = 40000000;
const PILL = { halt: 'halts', close: 'at the end', broken: "can't continue", uncovered: 'not covered', unbuilt: 'rule not built in', mismatch: 'real machine differs' };

function kindOf(st) {
  const ms = st.marks; const W = st.W;
  if (ms.length === 2 && ms[0].t === 'G' && ms[0].p === 1n && ms[1].t === 'M' && ms[1].p === W - 2n) return { k: 'clean', n: (W - 6n) / 2n };
  if (ms.length === 3 && ms[0].t === 'G' && ms[0].p === 1n && ms[1].t === 'M' && ms[2].t === 'M' && ms[2].p === W - 2n) return { k: 'gmm', m: ms[1].p, E: W };
  return null;
}

/* ---------- state ---------- */
let H = [];          // H[i] = state after i rounds (H[0] = start)
let scale = 'log';
let playing = null;
const MAXROUNDS = 20000;
const opts = () => ({ keep: $('opt-keep').checked, real: $('opt-real').checked });
function initState(W, marks) {
  return { W, marks, ev: [], meets: [], warns: [], stop: null, lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity, segs: 0, cleans: 0, nwarn: 0, nreal: 0, real: null };
}
const cur = () => H[H.length - 1];
function step() {
  const s = cur(); if (s.stop || H.length > MAXROUNDS) return false;
  const o = opts();
  const nx = doRound(s, { keep: o.keep });
  nx.real = null;
  if (o.real && s.W <= REAL_MAX && s.marks.length && s.marks[0].t === 'G' && s.marks[0].p === 1n && !checkTape(s.W, s.marks).length) {
    const tm = realRound(s.W, s.marks, REAL_BUDGET);
    if (tm.timeout) nx.real = { kind: 'timeout', text: 'real machine: not finished within ' + full(BigInt(REAL_BUDGET)) + ' steps, so not compared' };
    else if (nx.stop) {
      nx.real = { kind: 'note', text: tm.halted ? 'on the real machine this round halts after ' + full(BigInt(tm.steps)) + ' steps' : 'on the real machine this round ends after ' + full(BigInt(tm.steps)) + ' steps with ' + shape(tm.marks) + ' (' + tm.marks.map(m => m.t.length === 1 ? m.t + full(m.p) : m.t + ' at ' + full(m.p)).join(' ') + ', width ' + full(tm.W) + ')' };
    } else if (tm.halted) {
      nx.real = { kind: 'bad', text: 'the real machine halts in this round, after ' + full(BigInt(tm.steps)) + ' steps, though the mark rules saw nothing wrong' };
      if (!o.keep) nx.stop = { k: 'mismatch', text: 'The real machine halts in this round, after ' + full(BigInt(tm.steps)) + ' steps, though the mark rules saw nothing wrong.' }; else nx.warns.push({ kind: 'mismatch', text: nx.real.text });
    } else if (tm.W === nx.W && sameMarks(tm.marks, nx.marks)) {
      nx.real = { kind: 'ok', text: 'real machine: same marks, ' + full(BigInt(tm.steps)) + ' steps' };
    } else {
      const got = tm.marks.map(m => m.t.length === 1 ? m.t + full(m.p) : m.t + ' at ' + full(m.p)).join(' ') + ', width ' + full(tm.W);
      nx.real = { kind: 'bad', text: 'the real machine ends this round differently: ' + got };
      if (!o.keep) nx.stop = { k: 'mismatch', text: 'The real machine ends this round differently from the mark rules: ' + got + '.' }; else nx.warns.push({ kind: 'mismatch', text: nx.real.text });
    }
  }
  const k = nx.stop ? null : kindOf(nx);
  nx.segs = s.segs + (k ? 1 : 0); nx.cleans = s.cleans + (k && k.k === 'clean' ? 1 : 0);
  nx.nwarn = s.nwarn + nx.warns.length + (nx.stop && nx.stop.k !== 'halt' && nx.stop.k !== 'close' ? 1 : 0);
  nx.nreal = s.nreal + (nx.real && (nx.real.kind === 'ok' || nx.real.kind === 'bad') ? 1 : 0);
  H.push(nx);
  return !nx.stop;
}
function runUntil(pred, cap) { for (let i = 0; i < cap; i++) { if (!step()) break; if (pred(cur())) break; } }

/* ---------- parsing and presets ---------- */
function parseTape(text, keep) {
  const errs = []; const notes = [];
  let W = null;
  const wm = text.match(/width\s*[:=]?\s*(\d+)/i);
  if (wm) W = BigInt(wm[1]);
  const body = text.replace(/width\s*[:=]?\s*\d+/i, ' ').replace(/([GMWBgmwb])\s+(?=\d)/g, '$1');
  const marks = [];
  for (const tok of body.split(/[\s,;]+/).filter(Boolean)) {
    const m = tok.match(/^([GMWBgmwb])(\d+)$/);
    if (!m) { errs.push('“' + tok + '” is not a mark. Write a letter and a cell number, like M100.'); continue; }
    marks.push({ t: m[1].toUpperCase(), p: BigInt(m[2]) });
  }
  if (W === null) errs.push('Add the width on its own line, for example: width 230.');
  if (!marks.length) errs.push('Add at least the gap, G1.');
  marks.sort(byPos);
  for (let i = 1; i < marks.length; i++) if (marks[i].p === marks[i - 1].p) errs.push('Two marks share cell ' + full(marks[i].p) + '.');
  if (marks.length && !(marks[0].t === 'G' && marks[0].p === 1n)) errs.push('A round starts with the gap at cell 1. Put G1 first.');
  if (!errs.length) {
    const bad = checkTape(W, marks);
    if (bad.length) {
      if (keep) notes.push('This is not a tape the proven rules cover; stepping it shows only the mark rules\' guess. ' + bad.join(' '));
      else errs.push(...bad, 'Fix the positions, or tick "Keep going past unhandled cases" to step it anyway.');
    }
    const last = marks[marks.length - 1];
    if (!bad.length && !(last.t === 'M' && last.p === W - 2n)) notes.push('No end marker at width − 2 (cell ' + full(W - 2n) + '). The rules still run, but tapes the machine reaches always have one between rounds.');
    if (marks.filter(m => m.t === 'G').length > 1) notes.push('There is more than one gap; the extra ones sleep until a packet wakes them.');
  }
  return { W, marks, errs, notes };
}
function tapeText(W, marks) {
  const lines = ['width ' + W.toString()];
  for (let i = 0; i < marks.length; i += 3) lines.push(marks.slice(i, i + 3).map(m => m.t + m.p.toString()).join(' '));
  return lines.join('\n');
}
const mk = (spec) => spec.split(' ').map(t => ({ t: t[0], p: BigInt(t.slice(1)) }));
const PRESET = {
  rec57: () => { const n = 114928805503523374n; const W = 2n * n + 6n; return [W, mk('G1 M' + (W - 2n))]; },
  loop: () => [229857611007046932n, mk('G1 W48706866353402967 W154775086763876062 W220997025913996563')],
  stair: () => [250271063336203911397195022n, mk('G1 W12822928591565336128372015 W130490052125864858612298040 W242802655202401478182523537')],
  halt413: () => [13n, mk('G1 M4 M11')],
  small: () => [2006n, mk('G1 M2004')],
  packed: () => [24n, mk('G1 B6 W9 M19 M22')],
  unbuilt: () => [18n, mk('G1 B6 M16')],
};
function presetTape() {
  const v = $('preset').value;
  if (v === 'clean') {
    const s = $('in-n').value.replace(/[,\s_]/g, '');
    if (!/^\d+$/.test(s) || BigInt(s) < 1n) return { err: 'n has to be a whole number, 1 or more.' };
    const n = BigInt(s); const W = 2n * n + 6n; return { W, marks: [{ t: 'G', p: 1n }, { t: 'M', p: W - 2n }] };
  }
  if (v === 'gmm') {
    const a = $('in-m').value.replace(/[,\s_]/g, ''), b = $('in-E').value.replace(/[,\s_]/g, '');
    if (!/^\d+$/.test(a) || !/^\d+$/.test(b)) return { err: 'm and E have to be whole numbers.' };
    const m = BigInt(a), E = BigInt(b);
    if (!(m > 1n && m < E - 2n)) return { err: 'The marker has to sit between the gap and the end marker: 1 < m < E − 2.' };
    return { W: E, marks: [{ t: 'G', p: 1n }, { t: 'M', p: m }, { t: 'M', p: E - 2n }] };
  }
  if (PRESET[v]) { const [W, marks] = PRESET[v](); return { W, marks }; }
  return null;
}
function showMsg(kind, html) { const el = $('msg'); if (!html) { el.hidden = true; return; } el.hidden = false; el.className = 'msg ' + kind; el.innerHTML = html; }
function load(text, autorun) {
  const r = parseTape(text, $('opt-keep').checked);
  if (r.errs.length) { showMsg('err', r.errs.map(esc).join('<br>')); return false; }
  showMsg('note', r.notes.length ? r.notes.map(esc).join('<br>') : '');
  stopPlay();
  H = [initState(r.W, r.marks)];
  try { localStorage.setItem('mrs-tape', text); } catch (e) {}
  if (autorun) runUntil(s => s.stop || (kindOf(s) && kindOf(s).k === 'clean'), 5000);
  render(true);
  return true;
}

/* ---------- drawing ---------- */
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
function xOf(p, W, maxH) {
  if (scale === 'lin') return Number(p * 100000n / W) / 100000;
  const dist = W - p; if (dist <= 0n) return 1;
  const h = lg2(W) - lg2(dist);
  return Math.max(0, Math.min(1, h / maxH));
}
function glyph(ctx, t, x, y, r) {
  const col = css(VAR[t] || '--muted'); ctx.fillStyle = col; ctx.strokeStyle = col; ctx.lineWidth = Math.max(1.4, r / 3);
  if (t === 'G') { ctx.beginPath(); ctx.arc(x, y, r * 0.8, 0, Math.PI * 2); ctx.stroke(); }
  else if (t === 'M') { ctx.beginPath(); ctx.arc(x, y, r * 0.8, 0, Math.PI * 2); ctx.fill(); }
  else if (t === 'W') { ctx.fillRect(x - Math.max(1, r * 0.28), y - r, Math.max(2, r * 0.56), 2 * r); }
  else { ctx.fillRect(x - r * 0.8, y - r * 0.8, r * 1.6, r * 1.6); }
}
function sizeCanvas(cv) {
  const dpr = window.devicePixelRatio || 1; const w = cv.clientWidth; const h = +cv.getAttribute('height');
  cv.style.height = h + 'px'; cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);
  const ctx = cv.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); return { ctx, w, h };
}
function axisMax() { let W = 0n; for (const s of H) if (s.W > W) W = s.W; return Math.max(4, lg2(W) - 1); }
function drawAxis(ctx, x0, x1, y, maxH) {
  ctx.strokeStyle = css('--rule'); ctx.fillStyle = css('--muted'); ctx.lineWidth = 1;
  ctx.font = '10px ' + css('--font-display'); ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  const ticks = [];
  if (scale === 'lin') for (const f of [0, 0.25, 0.5, 0.75, 1]) ticks.push([f, f === 0 ? '0' : f === 1 ? 'width' : f + ' w']);
  else { const stepH = maxH > 60 ? 20 : maxH > 24 ? 10 : 5; for (let h = 0; h <= maxH + 1e-9; h += stepH) ticks.push([h / maxH, String(h)]); }
  for (const [f, lab] of ticks) {
    const x = x0 + f * (x1 - x0);
    ctx.beginPath(); ctx.moveTo(x + 0.5, y - 4); ctx.lineTo(x + 0.5, y); ctx.stroke();
    ctx.fillText(lab, Math.min(Math.max(x, x0 + 10), x1 - 14), y + 2);
  }
}
function drawNow() {
  const cv = $('cv-now'); const { ctx, w, h } = sizeCanvas(cv); ctx.clearRect(0, 0, w, h);
  const s = cur(); const maxH = axisMax(); const x0 = 12, x1 = w - 12, y = 36;
  ctx.strokeStyle = css('--rule'); ctx.lineWidth = 6; ctx.lineCap = 'round';
  ctx.beginPath(); ctx.moveTo(x0, y); ctx.lineTo(x1, y); ctx.stroke(); ctx.lineCap = 'butt';
  ctx.font = '700 10px ' + css('--font-display'); ctx.textBaseline = 'alphabetic'; ctx.textAlign = 'center';
  const placed = [[], []];
  for (const m of s.marks) {
    const x = x0 + xOf(m.p, s.W, maxH) * (x1 - x0);
    glyph(ctx, m.t, x, y, 6);
    for (const lane of [0, 1]) {
      if (placed[lane].every(px => Math.abs(px - x) > 9)) { placed[lane].push(x); ctx.fillStyle = css(VAR[m.t] || '--muted'); ctx.fillText(m.t.length === 1 ? m.t : '?', x, lane === 0 ? y - 12 : y + 20); break; }
    }
  }
  drawAxis(ctx, x0, x1, h - 22, maxH);
  ctx.fillStyle = css('--muted'); ctx.font = '10px ' + css('--font-body'); ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic';
  ctx.fillText(scale === 'lin' ? 'cell ÷ width' : 'halvings from the end: log₂(width ÷ cells to the end)', x0, h - 2);
}
let histGeom = null;
function drawHist(hoverRow) {
  const cv = $('cv-hist'); const { ctx, w, h } = sizeCanvas(cv); ctx.clearRect(0, 0, w, h);
  const maxH = axisMax(); const barW = w < 520 ? 54 : 84; const x0 = 12, x1 = w - barW - 18; const bx0 = x1 + 14, bx1 = w - 8;
  const top = 6, bottom = h - 30; const avail = bottom - top;
  const N = H.length; const rowH = Math.max(1, Math.min(14, avail / N)); const shown = Math.min(N, Math.floor(avail / rowH));
  const first = N - shown;
  histGeom = { top, rowH, first, shown };
  ctx.strokeStyle = css('--rule'); ctx.lineWidth = 1;
  const grid = scale === 'lin' ? [0.25, 0.5, 0.75] : (() => { const st = maxH > 60 ? 20 : maxH > 24 ? 10 : 5; const a = []; for (let k = st; k < maxH; k += st) a.push(k / maxH); return a; })();
  for (const f of grid) { const x = Math.round(x0 + f * (x1 - x0)) + 0.5; ctx.beginPath(); ctx.moveTo(x, top); ctx.lineTo(x, bottom); ctx.stroke(); }
  const bmax = maxH + 1;
  ctx.beginPath(); ctx.moveTo(bx0 + 0.5, top); ctx.lineTo(bx0 + 0.5, bottom); ctx.stroke();
  const need = bx0 + (bx1 - bx0) * (maxH / bmax);
  ctx.setLineDash([3, 3]); ctx.strokeStyle = css('--bad'); ctx.beginPath(); ctx.moveTo(Math.round(need) + 0.5, top); ctx.lineTo(Math.round(need) + 0.5, bottom); ctx.stroke(); ctx.setLineDash([]);
  if (hoverRow != null && hoverRow >= first && hoverRow < N) { ctx.fillStyle = css('--sunk'); ctx.fillRect(0, top + (hoverRow - first) * rowH, w, Math.max(rowH, 2)); }
  const r = rowH >= 6 ? Math.min(5, rowH / 2 - 0.5) : 0;
  for (let i = first; i < N; i++) {
    const s = H[i]; const y = top + (i - first) * rowH + rowH / 2;
    if (s.warns.length || s.stop) { ctx.fillStyle = css('--bad'); ctx.fillRect(0, y - Math.max(0.5, rowH / 2), 3, Math.max(1, rowH)); }
    for (const m of s.marks) {
      const x = x0 + xOf(m.p, s.W, maxH) * (x1 - x0);
      if (r > 0) glyph(ctx, m.t, x, y, r); else { ctx.fillStyle = css(VAR[m.t] || '--muted'); ctx.fillRect(x - 1, y - Math.max(0.5, rowH / 2), 2, Math.max(1, rowH)); }
    }
    if (s.meets.length) {
      const hh = Math.max(...s.meets.map(q => q.h)); const len = Math.max(1, (bx1 - bx0) * Math.min(1, (isFinite(hh) ? hh : bmax) / bmax));
      ctx.fillStyle = css('--accent'); ctx.fillRect(bx0 + 1, y - Math.max(0.5, rowH * 0.35), len, Math.max(1, rowH * 0.7));
    }
  }
  drawAxis(ctx, x0, x1, bottom + 6, maxH);
  ctx.fillStyle = css('--muted'); ctx.font = '10px ' + css('--font-display'); ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  ctx.fillText('0', bx0 + 4, bottom + 8); ctx.fillText(maxH.toFixed(0), Math.min(need, bx1 - 10), bottom + 8);
  ctx.textAlign = 'left'; ctx.font = '10px ' + css('--font-body'); ctx.textBaseline = 'alphabetic';
  ctx.fillText(first > 0 ? 'rounds ' + first + '–' + (N - 1) + ' (earlier ones scrolled off)' : 'rounds 0–' + (N - 1), x0, h - 2);
  ctx.textAlign = 'right'; ctx.fillText('end meeting', bx1, h - 2);
}
function rowAt(evt) {
  if (!histGeom) return null; const rect = $('cv-hist').getBoundingClientRect(); const y = evt.clientY - rect.top;
  const i = histGeom.first + Math.floor((y - histGeom.top) / histGeom.rowH);
  return i >= histGeom.first && i < H.length ? i : null;
}
function readRow(i) {
  if (i == null) { $('readout').textContent = 'Point at a row to read it.'; return; }
  const s = H[i]; const k = s.stop ? null : kindOf(s);
  let t = 'Round ' + i + ' · ' + shape(s.marks) + ' · width ' + short(s.W);
  if (s.meets.length) t += ' · end meeting ' + s.meets.map(q => isFinite(q.h) ? q.h.toFixed(2) + ' halvings (chain ' + q.chain + ')' : 'd = ' + q.d).join(', ');
  if (s.stop) t += ' · stopped: ' + PILL[s.stop.k];
  else if (s.warns.length) t += ' · ' + s.warns.length + ' unhandled';
  if (k && k.k === 'clean') t += ' · clean tape n = ' + short(k.n);
  else if (k) t += ' · two-marker state m = ' + short(k.m);
  $('readout').textContent = t;
}

/* ---------- panels ---------- */
function render(rebuildLog) {
  const s = cur(); const k = s.stop ? null : kindOf(s);
  let pill = '<span class="pill run">running</span>';
  let text = 'Round ' + (H.length - 1) + '. The tape reads ' + shape(s.marks) + '.';
  if (s.stop) { pill = '<span class="pill ' + s.stop.k + '">' + PILL[s.stop.k] + '</span>'; text = s.stop.text; }
  else if (s.warns.length) { pill = '<span class="pill warned">past an unhandled case</span>'; text = s.warns[s.warns.length - 1].text + ' From here on the marks are only the mark rules\' guess.'; }
  else if (k && k.k === 'clean') { pill = '<span class="pill clean">clean tape</span>'; text = 'Clean tape n = ' + full(k.n) + ', after ' + (H.length - 1) + ' rounds.'; }
  else if (k) { pill = '<span class="pill seg2">two-marker state</span>'; text = 'Two-marker state (m, E) = (' + full(k.m) + ', ' + full(k.E) + ').'; }
  if (!s.stop && !s.warns.length && s.nwarn > 0) text += ' Earlier rounds went past ' + s.nwarn + ' unhandled case' + (s.nwarn > 1 ? 's' : '') + ', so this is only the mark rules\' guess.';
  $('status').innerHTML = pill + '<span>' + esc(text) + '</span>';
  const W = s.W; const need = lg2(W) - 1;
  const realSub = W <= REAL_MAX ? (opts().real ? 'rounds compared with the transition table' : 'turned off') : 'only on tapes up to 4,096 cells';
  const stats = [
    ['Rounds', String(H.length - 1), ''],
    ['Width', short(W), W.toString().length + ' digits · 2^' + lg2(W).toFixed(1)],
    ['Closest end meeting', isFinite(s.best) ? s.best.toFixed(2) : (s.best === Infinity ? 'd = 0' : '—'), 'halvings; a halt needs about ' + need.toFixed(1)],
    ['Longest chain', String(s.maxChain), 'end meetings in a row, each at about half the last distance'],
    ['Two-marker states', String(s.segs), s.cleans ? s.cleans + ' of them clean tapes' : 'passed so far'],
    ['Unhandled cases', String(s.nwarn), s.nwarn ? 'see the flagged rounds in the log' : 'every move matched a proven rule'],
    ['Checked on the real machine', String(s.nreal), realSub],
  ];
  $('stats').innerHTML = stats.map(([l, v, sub]) => '<div class="stat"><span class="lab">' + l + '</span><span class="v">' + esc(v) + '</span><span class="s">' + esc(sub) + '</span></div>').join('');
  const done = !!s.stop || H.length > MAXROUNDS;
  for (const id of ['b-step', 'b-10', 'b-seg', 'b-clean']) $(id).disabled = done;
  $('b-play').disabled = done && !playing;
  $('b-back').disabled = H.length <= 1; $('b-reset').disabled = H.length <= 1;
  const rows = s.marks.map(m => { const dist = W - m.p; const hv = dist > 0n ? (lg2(W) - lg2(dist)).toFixed(2) : '—';
    const nm = NAMES[m.t] || m.t;
    return '<tr><td class="t"><span class="dot" style="background:var(' + (VAR[m.t] || '--muted') + ');border-radius:' + (m.t === 'G' || m.t === 'M' ? '50%' : '1px') + '"></span>' + esc(nm) + '</td><td class="num">' + full(m.p) + '</td><td class="num">' + full(dist) + '</td><td class="num">' + hv + '</td></tr>'; });
  $('marks').innerHTML = '<thead><tr><th scope="col">Mark</th><th scope="col">Cell</th><th scope="col">Cells to the end</th><th scope="col">Halvings</th></tr></thead><tbody>' + rows.join('') + '</tbody>';
  renderLog(rebuildLog);
  drawNow(); drawHist(null); readRow(null);
}
let logCount = 0;
function roundHtml(i) {
  const s = H[i]; const prev = H[i - 1];
  const items = s.ev.map(e => typeof e === 'string' ? '<li>' + esc(e) + '</li>' : e.warn ? '<li class="warn">Unhandled: ' + esc(e.text) + '</li>' : '<li class="meet">' + esc(e.text) + '</li>');
  if (s.stop) items.push('<li class="stop">' + esc(s.stop.text) + '</li>');
  if (s.real) items.push('<li class="' + (s.real.kind === 'ok' ? 'real' : s.real.kind === 'bad' ? 'realbad' : '') + '">' + esc(s.real.text) + '</li>');
  const k = s.stop ? null : kindOf(s);
  const tag = k ? '<span class="tagE">' + (k.k === 'clean' ? 'clean tape' : 'two-marker state') + '</span>' : '';
  const fl = s.stop || s.warns.length ? ' flagged' : '';
  return '<div class="round' + fl + '"><div class="hd"><span class="rn">Round ' + i + '</span><span class="sh">' + shape(prev.marks) + ' → ' + (s.stop ? 'stopped' : shape(s.marks)) + '</span>' + tag + '</div><ul>' + items.join('') + '</ul></div>';
}
function renderLog(rebuild) {
  const el = $('log'); const N = H.length; const keep = 300;
  if (rebuild || logCount > N - 1) {
    const from = Math.max(1, N - keep); let html = '';
    if (N === 1) html = '<div class="round"><div class="hd"><span class="rn">Start</span><span class="sh">' + shape(H[0].marks) + '</span></div><ul><li>Width ' + esc(full(H[0].W)) + '. Press Step to run the first round.</li></ul></div>';
    else { if (from > 1) html += '<div class="round"><ul style="padding-left:0"><li>Rounds 1–' + (from - 1) + ' are not listed; the picture above still shows them.</li></ul></div>'; for (let i = from; i < N; i++) html += roundHtml(i); }
    el.innerHTML = html; logCount = N - 1;
  } else {
    let html = ''; for (let i = logCount + 1; i < N; i++) html += roundHtml(i);
    if (logCount === 0 && N > 1) el.innerHTML = '';
    el.insertAdjacentHTML('beforeend', html); logCount = N - 1;
    while (el.children.length > keep + 1) el.removeChild(el.firstChild);
  }
  el.scrollTop = el.scrollHeight;
}

/* ---------- controls ---------- */
function act(fn) { stopPlay(); fn(); render(false); }
$('b-step').onclick = () => act(() => step());
$('b-10').onclick = () => act(() => { for (let i = 0; i < 10; i++) if (!step()) break; });
$('b-seg').onclick = () => act(() => runUntil(s => !!kindOf(s), 20000));
$('b-clean').onclick = () => act(() => runUntil(s => { const k = kindOf(s); return k && k.k === 'clean'; }, 20000));
$('b-back').onclick = () => { stopPlay(); if (H.length > 1) { H.pop(); render(true); } };
$('b-reset').onclick = () => { stopPlay(); H = H.slice(0, 1); render(true); };
function stopPlay() { if (playing) { clearInterval(playing); playing = null; } $('b-play').textContent = 'Play'; $('b-play').setAttribute('aria-pressed', 'false'); }
function startPlay() { playing = setInterval(() => { if (!step()) stopPlay(); render(false); }, 1000 / +$('speed').value); $('b-play').textContent = 'Pause'; $('b-play').setAttribute('aria-pressed', 'true'); }
$('b-play').onclick = () => { if (playing) { stopPlay(); render(false); } else startPlay(); };
$('speed').oninput = () => { if (playing) { clearInterval(playing); startPlay(); } };
function setScale(s) { scale = s; $('sc-lin').setAttribute('aria-pressed', s === 'lin'); $('sc-log').setAttribute('aria-pressed', s === 'log'); try { localStorage.setItem('mrs-scale', s); } catch (e) {} drawNow(); drawHist(null); }
$('sc-lin').onclick = () => setScale('lin'); $('sc-log').onclick = () => setScale('log');
$('b-load').onclick = () => { $('preset').value = 'custom'; presetUI(); load($('tape').value, false); };
$('opt-real').onchange = () => render(false);
function presetUI() { const v = $('preset').value; $('f-n').hidden = v !== 'clean'; $('f-me').hidden = v !== 'gmm'; }
function applyPreset(autorun) {
  presetUI();
  if ($('preset').value === 'custom') return;
  const r = presetTape(); if (!r) return; if (r.err) { showMsg('err', esc(r.err)); return; }
  $('tape').value = tapeText(r.W, r.marks); load($('tape').value, autorun);
}
$('preset').onchange = () => applyPreset(false);
for (const id of ['in-n', 'in-m', 'in-E']) { $(id).addEventListener('change', () => applyPreset(false)); $(id).addEventListener('keydown', e => { if (e.key === 'Enter') applyPreset(false); }); }
const hist = $('cv-hist');
hist.addEventListener('mousemove', e => { const i = rowAt(e); drawHist(i); readRow(i); });
hist.addEventListener('mouseleave', () => { drawHist(null); readRow(null); });
hist.addEventListener('touchstart', e => { const t = e.touches[0]; const i = rowAt(t); drawHist(i); readRow(i); }, { passive: true });
document.addEventListener('keydown', e => {
  if (e.target.matches('input, textarea, select')) return;
  if (e.key === 'ArrowRight') { e.preventDefault(); $('b-step').click(); }
  else if (e.key === 'ArrowLeft') { e.preventDefault(); $('b-back').click(); }
});
$('legend').innerHTML = ['G', 'M', 'W', 'B'].map(t => {
  const c = 'var(' + VAR[t] + ')';
  const g = t === 'G' ? '<circle cx="7" cy="7" r="4.5" fill="none" stroke="' + c + '" stroke-width="2"/>' : t === 'M' ? '<circle cx="7" cy="7" r="5" fill="' + c + '"/>' : t === 'W' ? '<rect x="5.5" y="1" width="3" height="12" fill="' + c + '"/>' : '<rect x="2" y="2" width="10" height="10" fill="' + c + '"/>';
  return '<span><svg width="14" height="14" viewBox="0 0 14 14" aria-hidden="true">' + g + '</svg>' + NAMES[t] + '</span>';
}).join('') + '<span><svg width="22" height="14" viewBox="0 0 22 14" aria-hidden="true"><rect x="0" y="4" width="22" height="6" fill="var(--accent)"/></svg>closest end meeting that round (halvings; dashed line: a halt)</span>'
  + '<span><svg width="6" height="14" viewBox="0 0 6 14" aria-hidden="true"><rect x="0" y="1" width="3" height="12" fill="var(--bad)"/></svg>round with an unhandled case</span>';
const redraw = () => { drawNow(); drawHist(null); };
window.addEventListener('resize', () => { clearTimeout(redraw.t); redraw.t = setTimeout(redraw, 80); });
try { matchMedia('(prefers-color-scheme: dark)').addEventListener('change', redraw); } catch (e) {}
new MutationObserver(redraw).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });

/* ---------- start: the 57-digit record, run to its next clean tape ---------- */
try { const sc = localStorage.getItem('mrs-scale'); if (sc === 'lin' || sc === 'log') scale = sc; } catch (e) {}
$('sc-lin').setAttribute('aria-pressed', scale === 'lin'); $('sc-log').setAttribute('aria-pressed', scale === 'log');
$('preset').value = 'clean';
applyPreset(true);

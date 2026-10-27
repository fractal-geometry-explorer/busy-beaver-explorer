/* Mark-rule engine for the stepper: one round of the mark rules, the checks that a step is covered by the proven
   rules, and a bare transition-table run of one round for small tapes. Plain JS, BigInt positions. */
'use strict';
const LEN = { G: 3n, M: 2n, W: 2n, B: 3n };
const VAL = { G: 0, M: 1, W: 0, B: 1 };
const NAMES = { G: 'gap', M: 'marker', W: 'wall', B: 'block' };
const byPos = (a, b) => (a.p < b.p ? -1 : a.p > b.p ? 1 : 0);
const endOf = m => m.p + LEN[m.t] - 1n;
function sepS(s) { return s.replace(/\B(?=(\d{3})+(?!\d))/g, ','); }
function short(b) {
  const SUP = { '0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴', '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹' };
  const neg = b < 0n; const s = (neg ? -b : b).toString();
  if (s.length <= 9) return (neg ? '−' : '') + sepS(s);
  return (neg ? '−' : '') + s[0] + '.' + s.slice(1, 4) + ' × 10' + String(s.length - 1).split('').map(c => SUP[c]).join('');
}
function lg2(b) { const s = b.toString(); if (s.length < 300) return Math.log2(Number(b)); return (s.length - 17) * Math.log2(10) + Math.log2(Number(s.slice(0, 17))); }

/* Is this list of marks a real round-start tape? Between marks the tape alternates 1 0 1 0 ...; next to a mark the
   cell is the opposite of the mark's own cells; the tape runs from its first 1 (cell 0) to its last 1 (cell W - 1). */
function checkTape(W, marks) {
  const out = [];
  const ms = marks.slice().sort(byPos);
  if (!ms.length) return ['There are no marks.'];
  const f = ms[0];
  if (f.p < 0n) out.push('A mark sits left of cell 0.');
  else if (f.p === 0n) { if (VAL[f.t] === 0) out.push('Cell 0 is the tape\'s first 1, so a ' + NAMES[f.t] + ' cannot start there.'); }
  else if ((f.p % 2n === 1n) !== (VAL[f.t] === 0)) out.push('The ' + NAMES[f.t] + ' at cell ' + short(f.p) + ' does not fit the stripes that start at cell 0.');
  for (let i = 1; i < ms.length; i++) {
    const a = ms[i - 1], b = ms[i]; const L = b.p - endOf(a) - 1n;
    const where = 'the ' + NAMES[a.t] + ' at ' + short(a.p) + ' and the ' + NAMES[b.t] + ' at ' + short(b.p);
    if (L < 0n) out.push('Marks overlap: ' + where + '.');
    else if (L === 0n && VAL[a.t] === VAL[b.t]) out.push('Marks touch: ' + where + ' run together into ' + (LEN[a.t] + LEN[b.t]) + ' ' + VAL[a.t] + 's in a row, which is no mark.');
    else if (L > 0n && ((L % 2n === 1n) !== (VAL[a.t] === VAL[b.t]))) out.push('The stripes between ' + where + ' have the wrong length for any real tape (they cannot alternate 1 0 1 0 and fit).');
  }
  const l = ms[ms.length - 1]; const T = W - 1n - endOf(l);
  if (T < 0n) out.push('The ' + NAMES[l.t] + ' at ' + short(l.p) + ' runs past the width.');
  else if (T === 0n) { if (VAL[l.t] === 0) out.push('The tape\'s last cell must be a 1, but the ' + NAMES[l.t] + ' at ' + short(l.p) + ' ends there.'); }
  else if ((T % 2n === 1n) !== (VAL[l.t] === 0)) out.push('The stripes after the ' + NAMES[l.t] + ' at ' + short(l.p) + ' do not end on a 1 at the width.');
  return out;
}

/* One round of the mark rules. opts.keep: keep going past cases the proven rules do not cover. */
function doRound(st, opts) {
  opts = opts || {};
  let W = st.W;
  const marks = st.marks.map(m => ({ t: m.t, p: m.p })); marks.sort(byPos);
  const ev = []; const meets = []; const warns = [];
  let stop = null;
  let { lastD, lastKind, chain, maxChain, best } = st;
  const firstRight = x => { let r = null; for (const m of marks) if (m.p > x && (!r || m.p < r.p)) r = m; return r; };
  const lastMark = () => { let r = null; for (const m of marks) if (!r || m.p > r.p) r = m; return r; };
  const leftNeighbour = m => { let r = null; for (const k of marks) if (k !== m && k.p < m.p && (!r || k.p > r.p)) r = k; return r; };
  const touchesLeft = m => { const k = leftNeighbour(m); return k && endOf(k) + 1n === m.p ? k : null; };
  const remove = m => { const i = marks.indexOf(m); if (i >= 0) marks.splice(i, 1); };
  // a frame of the round, for the inside-a-round view: who moves, from where to where, and the tape after the move
  const trace = opts.trace ? [] : null;
  const fr = (actor, from, to, changed, text) => { if (trace) trace.push({ actor, from, to, text, W, marks: marks.slice().sort(byPos).map(m => ({ t: m.t, p: m.p, hi: changed.includes(m) })) }); };
  if (trace) trace.push({ actor: 'start', text: 'round starts', W, marks: marks.map(m => ({ t: m.t, p: m.p, hi: false })) });
  // a case the proven rules do not cover: stop, or note it and carry on with the mark model's guess
  function flag(kind, text) {
    if (opts.keep && kind !== 'halt' && kind !== 'broken') { warns.push({ kind, text }); ev.push({ warn: true, text }); return false; }
    stop = { k: kind, text }; return true;
  }
  function packetBack(x) {
    let b = null; for (const m of marks) if (m.p < x && m.t !== 'M' && (!b || m.p > b.p)) b = m;
    // markers the packet crosses on its way: each must have stripes on its left
    const crossed = marks.filter(m => m.t === 'M' && m.p < x && (!b || m.p > b.p)).sort(byPos).reverse();
    for (const m of crossed) {
      const k = touchesLeft(m);
      if (k && k.t === 'W' && flag('uncovered', 'A packet reaches the marker at ' + short(m.p) + ', which sits directly after a wall. No proven rule covers this.')) return null;
      if (k && k.t === 'G' && flag('unbuilt', 'A packet reaches the marker at ' + short(m.p) + ', which sits directly after a gap. A proven rule covers this (the packet merges the two), but the mark rules here have no step for it.')) return null;
    }
    if (!b) { ev.push('packet reaches the left end'); fr('packet', x, 0n, [], 'packet reaches the left end'); return null; }
    if (b.t === 'B') { ev.push('packet reaches the block at ' + short(b.p)); fr('packet', x, b.p, [b], 'packet reaches the block at ' + short(b.p)); flag('halt', 'A packet reached a block: the machine halts here.'); return null; }
    if (b.t === 'G') { const t0 = 'packet wakes the gap at ' + short(b.p) + ' and moves it 2 cells on'; ev.push(t0); const at = b.p; b.p += 2n; fr('packet', x, at, [b], t0); return b; }
    const k = touchesLeft(b);
    if (k && VAL[k.t] === 0 && flag('uncovered', 'A packet reaches the wall at ' + short(b.p) + ', which has a ' + NAMES[k.t] + ' directly on its left. No proven rule covers this.')) return null;
    const q = b.p; b.t = 'M'; b.p = q - 1n; const g = { t: 'G', p: q + 1n }; marks.push(g);
    ev.push('packet turns the wall at ' + short(q) + ' into a marker, with a new gap just right of it'); fr('packet', x, q, [b, g], 'packet turns the wall at ' + short(q) + ' into a marker, with a new gap just right of it'); return g;
  }
  function shiftFrom(x) {
    const k = firstRight(x);
    if (!k) { const w0 = W; W += 2n; const e = { t: 'M', p: W - 2n }; marks.push(e); ev.push('shift reaches blank tape: new end marker, width + 2'); fr('shift', x, w0, [e], 'shift reaches blank tape: new end marker, width + 2'); return packetBack(W - 2n); }
    if (k.t === 'M') { k.t = 'G'; ev.push('shift turns the marker at ' + short(k.p) + ' into the gap'); fr('shift', x, k.p, [k], 'shift turns the marker at ' + short(k.p) + ' into the gap'); return k; }
    if (k.t === 'W') { k.t = 'B'; ev.push('shift turns the wall at ' + short(k.p) + ' into a block'); fr('shift', x, k.p, [k], 'shift turns the wall at ' + short(k.p) + ' into a block'); return packetBack(k.p); }
    if (k.t === 'B') { k.t = 'W'; k.p += 2n; ev.push('shift turns the block at ' + short(k.p - 2n) + ' into a wall 2 cells on'); fr('shift', x, k.p - 2n, [k], 'shift turns the block at ' + short(k.p - 2n) + ' into a wall 2 cells on'); return packetBack(k.p); }
    flag('broken', 'A shift ran into a sleeping gap at ' + short(k.p) + '. No proven rule covers this, and the mark rules cannot guess.'); return null;
  }
  let gap = marks[0];
  let guard = 0;
  while (gap && !stop) {
    if (++guard > 100000) { stop = { k: 'broken', text: 'This round did not finish within 100,000 moves.' }; break; }
    const g = gap.p; const m = firstRight(g);
    const kl = touchesLeft(gap);
    if (kl && VAL[kl.t] === 0 && flag('uncovered', 'The gap at ' + short(g) + ' has a ' + NAMES[kl.t] + ' directly on its left, so it reads as a longer run of 0s. No proven rule covers this.')) break;
    if (!m) {
      const w0 = W; remove(gap); W += 3n; const e = { t: 'M', p: W - 2n }; marks.push(e);
      ev.push('gap reaches blank tape: new end marker, width + 3'); fr('gap', g, w0, [e], 'gap reaches blank tape: new end marker, width + 3'); gap = packetBack(W - 2n);
    } else if (m.t === 'M') {
      const d = m.p - g - 3n;
      if (d < 0n || d % 2n !== 0n) { flag('broken', 'The gap at ' + short(g) + ' and the marker at ' + short(m.p) + ' are ' + (d < 0n ? 'overlapping' : 'an odd distance apart') + ' (d = ' + d + '). No proven rule covers this, and the mark rules cannot guess.'); break; }
      const isEnd = m === lastMark();
      if (isEnd) {
        const kind = d % 4n === 0n ? 'swap' : 'merge';
        if (lastD !== null) { const pr = lastKind === 'merge' ? (lastD - 2n) / 2n : lastD / 2n + 4n; chain = d === pr ? chain + 1 : 1; } else chain = 1;
        if (chain > maxChain) maxChain = chain;
        const h = d > 0n ? lg2(W) - lg2(d) : Infinity;
        if (h > best) best = h;
        lastD = d; lastKind = kind;
        meets.push({ d, kind, h, chain });
        ev.push({ meet: true, text: 'gap meets the end marker at d = ' + short(d) + (isFinite(h) ? ', ' + h.toFixed(2) + ' halvings below the width' : '') + ' (' + kind + ', chain ' + chain + ')' });
        if (d <= 2n) fr('gap', g, m.p, [m], ev[ev.length - 1].text);
        if (d <= 2n && flag('close', 'The gap came within ' + d + ' cells of the end marker. Here the real machine can halt, as it does from the two-marker state (4, 13), and the proven rules stop describing it.')) break;
      }
      const mp0 = m.p; const meetText = isEnd ? ev[ev.length - 1].text : null;
      if (d % 4n === 0n) {
        m.p = g + d / 2n - 1n; gap.p = g + d / 2n + 1n;
        if (!isEnd) ev.push('swap with the marker at distance ' + short(d));
        if (!(isEnd && d <= 2n)) fr('gap', g, mp0, [m, gap], isEnd ? meetText.replace('(swap', '(swap: marker and gap trade places') : 'swap with the marker at distance ' + short(d) + ': the marker moves left, the gap carries on');
      } else {
        remove(gap); m.t = 'W'; m.p = g + d / 2n + 3n;
        if (!isEnd) ev.push('merge with the marker at distance ' + short(d) + ': wall at ' + short(m.p));
        if (!(isEnd && d <= 2n)) fr('gap', g, mp0, [m], isEnd ? meetText.replace('(merge', '(merge into a wall at ' + short(m.p)) : 'merge with the marker at distance ' + short(d) + ': wall at ' + short(m.p));
        gap = packetBack(m.p);
      }
    } else if (m.t === 'W') {
      const x = m.p; remove(gap); remove(m); ev.push('gap meets the wall at ' + short(x) + ': both vanish'); fr('gap', g, x, [], 'gap meets the wall at ' + short(x) + ': both vanish'); gap = shiftFrom(x);
    } else if (m.t === 'B') {
      m.t = 'W'; m.p -= 1n; ev.push('gap passes the block at ' + short(m.p + 1n) + ', which becomes a wall; the gap sleeps'); fr('gap', g, m.p + 1n, [m], 'gap passes the block at ' + short(m.p + 1n) + ', which becomes a wall; the gap sleeps'); gap = shiftFrom(m.p);
    } else {
      flag('broken', 'The gap ran into a sleeping gap at ' + short(m.p) + '. No proven rule covers this, and the mark rules cannot guess.');
    }
    marks.sort(byPos);
    for (let i = 1; i < marks.length && !stop; i++) if (endOf(marks[i - 1]) >= marks[i].p) { const a = marks[i - 1], b = marks[i];
      stop = { k: 'broken', text: 'The ' + NAMES[a.t] + ' at ' + short(a.p) + ' and the ' + NAMES[b.t] + ' at ' + short(b.p) + ' now overlap. The mark rules cannot represent this, so what the machine does next is not shown.' }; }
  }
  if (!stop) {
    let extra = 2n;
    if (marks.length && marks[0].t === 'M' && marks[0].p === 0n) { marks[0].t = 'W'; marks[0].p = 1n; extra = 4n; ev.push('the marker at cell 0 becomes a wall'); }
    for (const mk of marks) mk.p += extra;
    W += extra; const ng = { t: 'G', p: 1n }; marks.unshift(ng);
    ev.push('tape shifts ' + extra + ' cells right; new gap at cell 1');
    fr('tape', 0n, extra, [ng], (extra === 4n ? 'the marker at cell 0 becomes a wall, ' : '') + 'every mark moves ' + extra + ' cells right and a new gap appears at cell 1');
    const bad = checkTape(W, marks);
    for (const t of bad) if (flag('uncovered', 'The round ends on a tape the rules do not cover. ' + t)) break;
  }
  return { W, marks, ev, meets, warns, stop, lastD, lastKind, chain, maxChain, best, trace };
}

/* One round on the bare transition table 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE, for small tapes.
   Starts with the head in state E on the gap's last 0 (cell 3), stops at the next round start (state E on the third 0
   of a gap whose left neighbour is the tape's first 1) or at the halt. Returns the marks it finds. */
const TM = [ // [state][read] -> [write, move, next]; states A..F = 0..5, -1 = halt
  [[1, 1, 1], [0, 1, 4]], [[1, -1, 2], [0, 1, 0]], [[1, -1, 0], [1, -1, 3]], [[1, -1, 0], null], [[0, 1, 5], [0, -1, 1]], [[0, -1, 3], [1, 1, 4]]];
function realRound(W, marks, budget) {
  const w = Number(W); let pad = 64; let N = w + 2 * pad; let tape = new Uint8Array(N); let off = pad;
  const ms = marks.slice().sort(byPos);
  // build the cells: alternate from cell 0 = 1, marks overwrite with their own cells, stripes restart after each mark
  let x = 0, v = 1, mi = 0;
  while (x < w) {
    if (mi < ms.length && BigInt(x) === ms[mi].p) { const m = ms[mi]; const L = Number(LEN[m.t]); for (let i = 0; i < L; i++) tape[off + x + i] = VAL[m.t]; x += L; v = 1 - VAL[m.t]; mi++; }
    else { tape[off + x] = v; v = 1 - v; x++; }
  }
  let head = off + 3, s = 4, steps = 0;
  while (steps < budget) {
    if (head < 8 || head > N - 8) { // grow
      const nn = N * 2; const nt = new Uint8Array(nn); const shift = Math.floor((nn - N) / 2); nt.set(tape, shift); tape = nt; head += shift; off += shift; N = nn;
    }
    const c = tape[head]; const tr = TM[s][c];
    if (!tr) return { halted: true, steps };
    tape[head] = tr[0]; head += tr[1]; s = tr[2]; steps++;
    if (s === 4 && tape[head] === 0 && tape[head - 1] === 0 && tape[head - 2] === 0 && tape[head - 3] === 1) {
      let clear = true; for (let i = head - 4; i >= 0; i--) if (tape[i]) { clear = false; break; }
      if (clear) {
        const first = head - 3; let last = N - 1; while (last > first && !tape[last]) last--;
        const out = []; let i = first;
        while (i <= last) { let j = i; while (j + 1 <= last && tape[j + 1] === tape[i]) j++; const n = j - i + 1;
          if (n >= 2) { const t = tape[i] === 0 ? (n === 2 ? 'W' : n === 3 ? 'G' : null) : (n === 2 ? 'M' : n === 3 ? 'B' : null); out.push({ t: t || ('run of ' + n + ' ' + tape[i] + 's'), p: BigInt(i - first) }); }
          i = j + 1; }
        return { steps, W: BigInt(last - first + 1), marks: out };
      }
    }
  }
  return { timeout: true, steps };
}
function sameMarks(a, b) { if (a.length !== b.length) return false; for (let i = 0; i < a.length; i++) if (a[i].t !== b[i].t || a[i].p !== b[i].p) return false; return true; }
if (typeof module !== 'undefined') module.exports = { checkTape, doRound, realRound, sameMarks, short, lg2, LEN, VAL, NAMES, byPos };

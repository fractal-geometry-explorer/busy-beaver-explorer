// Map steppers for the in-browser runner of pages/holdouts/collatz-family.html, and for tools/collatz/test_maps.js.
// Each entry: the machine (TNF), the configuration the state stands for, the start from blank tape, and step(s),
// which returns the next state (an array of BigInt, or of BigInt and a tag) or {halt: reason} / {stop: reason}.
// The rules are transcribed from each machine's holdouts/<M>/status.json and README.md; "level" says how much of the
// rule is proved there (kernel: Lean proves the machine follows exactly this map and halts iff the stated condition).
"use strict";
(function (root) {
  const B = (x) => BigInt(x);
  const pow2 = (k) => 1n << B(k);
  const v2 = (d) => { let v = 0n; while ((d & 1n) === 0n) { d >>= 1n; v++; } return [v, d]; };
  const isPow2 = (d) => d > 0n && (d & (d - 1n)) === 0n;
  const v3 = (d) => { let v = 0n; while (d % 3n === 0n) { d /= 3n; v++; } return [v, d]; };

  const MAPS = [
    {
      m: "1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE", vars: ["n"], cfg: "P(n) = (10)^n A> 0", start: [4n],
      level: "kernel map (pstep), closed form checked for n <= 200,000",
      rule: "h_k = 5*2^k - k - 6; for h_k < n < h_{k+1}: n -> 3n - 10*2^k + 3k + 14; n = h_k halts",
      known: [4n, 9n, 24n, 52n, 99n, 163n, 198n, 303n, 618n, 1246n, 2493n, 4957n, 9792n, 19180n, 37107n, 70411n],
      step([n]) {
        let k = 1n;
        while (5n * pow2(k + 1n) - (k + 1n) - 6n <= n) k++;
        const h = 5n * pow2(k) - k - 6n;
        if (n === h) return { halt: "n = h_" + k };
        return [3n * n - 10n * pow2(k) + 3n * k + 14n];
      },
    },
    {
      m: "1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE", vars: ["n"], cfg: "S(n) at the left end", start: [1n],
      level: "kernel halts-iff for the recursive map; this closed form checked for n < 10,000",
      rule: "c_i = 10*2^i - i - 7; for c_i < n < c_{i+1}: n -> 3n - 2c_i + i + 3; n = c_i halts",
      known: [1n, 7n, 18n, 34n, 45n, 78n, 100n, 166n],
      step([n]) {
        if (n < 3n) return [3n * n + 4n]; // below c_0 = 3 (n = 1 -> 7), the rule with c_{-1} = -1, i = -1
        let i = 0n;
        while (10n * pow2(i + 1n) - (i + 1n) - 7n <= n) i++;
        const c = 10n * pow2(i) - i - 7n;
        if (n === c) return { halt: "n = c_" + i };
        return [3n * n - 2n * c + i + 3n];
      },
    },
    {
      m: "1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD", vars: ["D"], cfg: "Doucette term D (Space Needle)", start: [6n],
      level: "kernel halts-iff (halts_iff_pow2)", rule: "D = 2^v(2a+1) -> D + v + 3a; halts iff D is a power of 2",
      known: [6n, 10n, 17n, 41n, 101n, 251n, 626n],
      step([d]) {
        if (isPow2(d)) return { halt: "D is a power of 2" };
        const [v, o] = v2(d); const a = (o - 1n) / 2n;
        return [d + v + 3n * a];
      },
    },
    {
      m: "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE", vars: ["p", "q"], cfg: "K(p, q) = A>0 1^p 0 1^q", start: [0n, 2n],
      level: "kernel halts-iff", rule: "odd p: ((p-3)/2, q+(p+5)/2); even p >= 2: (3p/2+q, 1); p = 0: (2, q-1); p = 1 halts",
      step([p, q]) {
        if (p === 1n) return { halt: "p = 1" };
        if (p === 0n) return [2n, q - 1n];
        if (p & 1n) return [(p - 3n) / 2n, q + (p + 5n) / 2n];
        return [3n * p / 2n + q, 1n];
      },
    },
    {
      m: "1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB", vars: ["D"], cfg: "D = n + 2 for the pass P(n) = 1^n B>", start: [6n],
      level: "kernel halts-iff (halts_iff_doucette)", rule: "D = 2^v(2a+1) -> D + a + v + 2; D = 3*2^v with v even > 0: (3D+3v+10)/2; halts iff D is a power of 2",
      known: [6n, 10n, 15n, 24n, 30n, 40n, 47n],
      step([d]) {
        if (isPow2(d)) return { halt: "D is a power of 2" };
        const [v, o] = v2(d); const a = (o - 1n) / 2n;
        if (o === 3n && v > 0n && v % 2n === 0n) return [(3n * d + 3n * v + 10n) / 2n];
        return [d + a + v + 2n];
      },
    },
    {
      m: "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC", vars: ["p", "r"], cfg: "S(p, r): D> on 1^p 0 1^r", start: [2n, 2n],
      level: "kernel halts-iff", rule: "S(3,r) -> S(r+5, 2 if r odd else 1); S(2k+2,r) -> S(3k+r+4, 1); S(2m+1,r) -> S(m-1, m+r+3) (m >= 2); S(1,r) halts",
      step([p, r]) {
        if (p === 1n) return { halt: "p = 1" };
        if (p === 3n) return [r + 5n, (r & 1n) ? 2n : 1n];
        if ((p & 1n) === 0n) { const k = (p - 2n) / 2n; return [3n * k + r + 4n, 1n]; }
        const m = (p - 1n) / 2n; return [m - 1n, m + r + 3n];
      },
    },
    {
      m: "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB", vars: ["p", "r"], cfg: "S(p, r): C on 1^p 0 1^r", start: [3n, 1n],
      level: "kernel halts-iff", rule: "S(1,r) -> S(r+4,1); S(2,3m+1) -> S(3m+6,1); S(2,3m+2) -> S(3m+5,2); S(2,3m) halts; S(3k+3,r) -> S(4k+r+6,1); S(3k+4,r) -> S(4k+r+8,1); S(3k+5,r) -> S(k+1, 2k+r+5)",
      step([p, r]) {
        if (p === 1n) return [r + 4n, 1n];
        if (p === 2n) { const s = r % 3n; if (s === 0n) return { halt: "p = 2, 3 | r" }; return s === 1n ? [r + 5n, 1n] : [r + 3n, 2n]; }
        const k = (p - 3n) / 3n, s = (p - 3n) % 3n;
        if (s === 0n) return [4n * k + r + 6n, 1n];
        if (s === 1n) return [4n * k + r + 8n, 1n];
        return [k + 1n, 2n * k + r + 5n];
      },
    },
    {
      m: "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA", vars: ["p", "a"], cfg: "Q(p, a, b) (Antihydra)", start: [2n, 7n],
      level: "kernel halts-iff", rule: "a = 2k+1: (p+2, 3k+4); a = 2k: (p-1, 3k+2), halts if p = 0",
      known: [[2n, 7n], [4n, 13n], [6n, 22n], [5n, 35n], [7n, 55n], [9n, 85n], [11n, 130n]],
      step([p, a]) {
        const k = a / 2n;
        if (a & 1n) return [p + 2n, 3n * k + 4n];
        if (p === 0n) return { halt: "a even with p = 0" };
        return [p - 1n, 3n * k + 2n];
      },
    },
    {
      m: "1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC", vars: ["m", "k"], cfg: "E(m, k) = D> 110 (10)^m (110)^k", start: [8n, 1n],
      level: "kernel halts-iff", rule: "(3t, k) -> (4t+4, k-1) (k = 0 stays 0); (3t+1, k) -> (4t+4, k+1); (3t+2, k) -> (4t+5, k+1); (3t+2, 0) halts",
      step([m, k]) {
        const t = m / 3n, r = m % 3n;
        if (r === 0n) return [4n * t + 4n, k > 0n ? k - 1n : 0n];
        if (r === 1n) return [4n * t + 4n, k + 1n];
        if (k === 0n) return { halt: "m = 2 mod 3 with k = 0" };
        return [4n * t + 5n, k + 1n];
      },
    },
    {
      m: "1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA", vars: ["n", "m"], cfg: "R(n, m), or Z(k) shown as (k, -1)", start: [1n, -1n],
      level: "kernel halts-iff", rule: "R: even n -> (3n/2+2, m+2); odd n, m >= 1 -> ((3n+7)/2, m-1); odd n, m = 0 -> Z((3n+9)/2); Z(k): odd k -> R((3k+1)/2, 1), even k halts",
      step([n, m]) {
        if (m < 0n) { if ((n & 1n) === 0n) return { halt: "Z(k) with k even" }; return [(3n * n + 1n) / 2n, 1n]; }
        if ((n & 1n) === 0n) return [3n * n / 2n + 2n, m + 2n];
        if (m >= 1n) return [(3n * n + 7n) / 2n, m - 1n];
        return [(3n * n + 9n) / 2n, -1n];
      },
    },
    {
      m: "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---", vars: ["z", "y"], cfg: "wall C z y = A>0 0 10 0^z (10)^y 0 1", start: [0n, 0n],
      level: "kernel: never halts while the orbit stays in these rules", rule: "(3k, y) -> (4k+1, y+4); (3k+1, y) -> (4k+5, y+6); (3k+2, y) -> (4k+8, y-1); y = 0 with 3 not dividing z leaves the rules",
      step([z, y]) {
        const k = z / 3n, r = z % 3n;
        if (r === 0n) return [4n * k + 1n, y + 4n];
        if (y === 0n) return { stop: "leaves the rules (y = 0, z not a multiple of 3): may halt" };
        return r === 1n ? [4n * k + 5n, y + 6n] : [4n * k + 8n, y - 1n];
      },
    },
    {
      m: "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE", vars: ["p", "r"], cfg: "W p 0 r = 0 (10)^p 0 1^r E> 0", start: [2n, 1n],
      level: "kernel halts-iff", rule: "r >= p+2: (2p+2, r-p-1); r = p: (2, 4p+1); r < p: (p-r, 4r+2); r = p+1 halts",
      step([p, r]) {
        if (r === p + 1n) return { halt: "r = p + 1" };
        if (r >= p + 2n) return [2n * p + 2n, r - p - 1n];
        if (r === p) return [2n, 4n * p + 1n];
        return [p - r, 4n * r + 2n];
      },
    },
    {
      m: "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD", vars: ["u", "v", "Q"], cfg: "P(u, v) (Q = 0) or Q(u, v) (Q = 1)", start: [3n, 0n, 0n],
      level: "kernel halts-iff", rule: "u < v: P -> P(3u+2, v-u-1), Q -> Q(3u+3, v-u-1); u >= v+2: P -> Q(3v+3, u-v-2), Q -> P(3v+5, u-v-2); u = v or u = v+1 halts",
      step([u, v, q]) {
        if (u === v || u === v + 1n) return { halt: "u = v or u = v + 1" };
        if (u < v) return q ? [3n * u + 3n, v - u - 1n, 1n] : [3n * u + 2n, v - u - 1n, 0n];
        return q ? [3n * v + 5n, u - v - 2n, 0n] : [3n * v + 3n, u - v - 2n, 1n];
      },
    },
    {
      m: "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE", vars: ["i", "j", "J"], cfg: "two blocks of 1s (J = 0: R1, J = 1: R2)", start: [3n, 1n, 0n],
      level: "kernel halts-iff", rule: "j+2 <= i: (i-j-1, 3j+2 or 3j+3, J); i = j+1: R1 -> (3i-3, 3, R2), R2 -> (3i, 1, R1); i+2 = j: R1 -> (3i+3, 1, R1), R2 -> (3i+3, 3, R2); j > i+2: (j-i-2, 3i+3 or 3i+5, not J); halts at i = j or i+1 = j",
      step([i, j, J]) {
        if (i === j || i + 1n === j) return { halt: "i = j or i + 1 = j" };
        if (j + 2n <= i) return [i - j - 1n, 3n * j + (J ? 3n : 2n), J];
        if (i === j + 1n) return J ? [3n * i, 1n, 0n] : [3n * i - 3n, 3n, 1n];
        if (i + 2n === j) return J ? [3n * i + 3n, 3n, 1n] : [3n * i + 3n, 1n, 0n];
        return [j - i - 2n, 3n * i + (J ? 5n : 3n), J ? 0n : 1n];
      },
    },
    {
      m: "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA", vars: ["a", "c"], cfg: "round start A>0 1^a 0 1^c", start: [74n, 30n],
      level: "kernel halts-iff", rule: "c even: (a-c+12, 3c-6) if c <= a+8; (c-a-10, 3a+27) if c >= a+14; c odd: (a-c-1, 3c+6) if c <= a-5; (c-a+3, 3a) if c > a; halts at c-a = 10, 12 (c even) or a-c = 1, 3 (c odd)",
      step([a, c]) {
        if ((c & 1n) === 0n) {
          if (c <= a + 8n) return [a - c + 12n, 3n * c - 6n];
          if (c === a + 10n || c === a + 12n) return { halt: "c - a = " + (c - a) };
          return [c - a - 10n, 3n * a + 27n];
        }
        if (c <= a - 5n) return [a - c - 1n, 3n * c + 6n];
        if (c === a - 1n || c === a - 3n) return { halt: "a - c = " + (a - c) };
        return [c - a + 3n, 3n * a];
      },
    },
    {
      m: "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC", vars: ["n", "m"], cfg: "X(n, m) = C>0 0^n 1^m 0 1", start: [4n, 5n],
      level: "simulation-checked macro rules (halts-iff only as DeepMind's cited theorem)", rule: "m >= 2: n = 0 mod 4 -> (3n/2+4, m-1), n = 2 mod 4 -> ((3n+10)/2, m-2); m = 1: n = 0 mod 4 -> (3n/2+4, 0), else (4, 3n/2+6); m = 0: n = 0 mod 4 -> (4, 3n/2+5), else halt",
      step([n, m]) {
        const z = n % 4n === 0n;
        if (m >= 2n) return z ? [3n * n / 2n + 4n, m - 1n] : [(3n * n + 10n) / 2n, m - 2n];
        if (m === 1n) return z ? [3n * n / 2n + 4n, 0n] : [4n, 3n * n / 2n + 6n];
        return z ? [4n, 3n * n / 2n + 5n] : { halt: "X(n, 0) with n = 2 mod 4" };
      },
    },
    {
      m: "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC", vars: ["a", "b"], cfg: "A(a, b) = 1^a 0 C> 1^b", start: [2n, 9n],
      level: "kernel halts-iff (via the finer 30-case frame map)", rule: "a even, b >= a+3: (2a+4, b-a-1); a odd, b >= a+4: (2a+3, b-a); a odd, b = a+3: (2a+1, 9); b = a+2: (1, 2a+7); b = a+1: (4, 2a+4); a >= b >= 4: (a-b+1, 2b+3); b = 2: (a-3, 7); b = 3 halts",
      known: [[2n, 9n], [8n, 6n], [3n, 15n], [9n, 12n], [19n, 9n], [11n, 21n], [25n, 10n], [16n, 23n], [36n, 6n]],
      step([a, b]) {
        if (b === 3n) return { halt: "b = 3" };
        const odd = (a & 1n) === 1n;
        if (!odd && b >= a + 3n) return [2n * a + 4n, b - a - 1n];
        if (odd && b >= a + 4n) return [2n * a + 3n, b - a];
        if (odd && b === a + 3n) return [2n * a + 1n, 9n];
        if (b === a + 2n) return [1n, 2n * a + 7n];
        if (b === a + 1n) return [4n, 2n * a + 4n];
        if (a >= b && b >= 4n) return [a - b + 1n, 2n * b + 3n];
        if (b === 2n) return [a - 3n, 7n];
        return { stop: "outside the rules" };
      },
    },
    {
      m: "1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---", vars: ["m", "k", "b"], cfg: "C(m, k, b) = 1^m (10)^k C> 1^b", start: [0n, 0n, 2n],
      level: "kernel halts-iff (DeepMind's map, proved here in core Lean)", rule: "DeepMind's next, with the step (m+3, k, b+1) -> (m, k+2, b) repeated at once; halts iff a sweep start has m = 3b+1",
      step([m, k, b]) {
        if (b === 0n) return [m + 1n, 0n, 2n * k + 2n];
        if (m === 0n) return b === 1n ? [2n * k + 3n, 0n, 2n] : [2n * k + 2n, 1n, b - 2n];
        if (m === 1n) { if (k === 0n) return [0n, 0n, b + 2n]; return b === 1n ? [2n * k + 5n, 0n, 2n] : [2n * k + 4n, 1n, b - 2n]; }
        if (m === 2n) {
          if (k === 0n) return b === 1n ? [0n, 1n, 0n] : { halt: "C(2, 0, b) with b >= 2" };
          if (k === 1n) return [0n, 1n, b];
          return b === 1n ? [2n * k + 3n, 0n, 2n] : [2n * k + 2n, 1n, b - 2n];
        }
        let t = m / 3n; if (t > b) t = b;
        return [m - 3n * t, k + 2n * t, b - t];
      },
    },
    {
      m: "1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB", vars: ["k", "z"], cfg: "(k, fuel z)", start: [0n, 5n],
      known: [[0n, 5n], [1n, 4n], [4n, 2n], [7n, 1n], [0n, 14n], [1n, 13n], [4n, 11n], [7n, 10n], [13n, 8n], [22n, 6n], [34n, 5n], [52n, 4n], [79n, 3n], [121n, 1n], [0n, 185n]],
      level: "kernel halts-iff", rule: "k even: (3(k/2)+1, z-1) if z >= 1, (0, 3(k/2)+2) if z = 0; k odd: (3(k/2)+4, z-2) if z >= 2, (0, 3(k/2)+5) if z = 1, halt if z = 0",
      step([k, z]) {
        const h = k / 2n;
        if ((k & 1n) === 0n) return z >= 1n ? [3n * h + 1n, z - 1n] : [0n, 3n * h + 2n];
        if (z >= 2n) return [3n * h + 4n, z - 2n];
        if (z === 1n) return [0n, 3n * h + 5n];
        return { halt: "k odd with no fuel" };
      },
    },
    {
      m: "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA", vars: ["m", "n"], cfg: "P m n = (1011)^m 1^n (10)^3 A> 1", start: [14n, 5n],
      level: "kernel halts-iff", rule: "n = 3k+3+r. r = 0: (m-1, 8k+19), or (2k+4, 5) if m = 0; r = 1: (m-2, 8k+29) if m >= 2, halt if m = 1, (0, 8k+18) if m = 0; r = 2: (m-2, 8k+35) if m >= 2, (2k+8, 5) if m = 1, (0, 8k+18) if m = 0",
      step([m, n]) {
        const k = (n - 3n) / 3n, r = (n - 3n) % 3n;
        if (r === 0n) return m >= 1n ? [m - 1n, 8n * k + 19n] : [2n * k + 4n, 5n];
        if (r === 1n) { if (m >= 2n) return [m - 2n, 8n * k + 29n]; if (m === 1n) return { halt: "m = 1, n = 1 mod 3" }; return [0n, 8n * k + 18n]; }
        if (m >= 2n) return [m - 2n, 8n * k + 35n];
        return m === 1n ? [2n * k + 8n, 5n] : [0n, 8n * k + 18n];
      },
    },
  ];
  if (typeof module !== "undefined") module.exports = { MAPS };
  else root.COLLATZ_MAPS = MAPS;
})(this);

// Fast drop-in for makefun-diff 1.0.0 (make.fun's own line diff).
//
// Same answer as makefun-diff 1.0.0 on every input, computed with the same
// rule (common prefix, then common suffix, then Myers's greedy search with
// the deletion tie-break, then the same patch layout), but with the search
// run over interned line ids in flat Int32Arrays instead of one heap object
// per path, so it runs several times faster than the reference.
//
// Lines are interned to small integers: two lines are equal exactly when
// their ids are equal. A line with a trailing newline and the same text
// without one are different lines, so they intern through separate tables.

const FORMAT = 'makefun-diff/1';
const CONTEXT = 3;
const KEEP = 0;
const DELETE = 1;
const INSERT = 2;

/** Split a text into its lines' parts, without building the line strings. */
function splitLines(text) {
  const parts = text.split('\n');
  const last = parts.length - 1;
  // Number of lines: every part but the last has a newline; the last part
  // is a line too unless it is empty (the text ended in a newline, or is empty).
  const count = parts[last] === '' ? last : last + 1;
  return { parts, last, count };
}

/** The edit runs of the middle (after prefix/suffix trim), Myers greedy. */
function myersRuns(ai, bi, n, m) {
  // ai, bi: Int32Array views of the interned ids; n, m: their lengths.
  const kEnd = n - m;
  const trace = [];
  // Level 0: the initial snake from (0, 0).
  let v0 = new Int32Array(1);
  let x = 0;
  let y = 0;
  while (ai[x] === bi[y]) { x++; y++; }
  v0[0] = x;
  trace.push(v0);
  let D = -1;
  if (x === n && kEnd === 0) {
    D = 0;
  } else {
    let vp = v0;
    const maxD = n + m;
    outer:
    for (let d = 1; d <= maxD; d++) {
      const vc = new Int32Array(d + 1);
      // i = 0, k = -d: insertion only.
      {
        const k = -d;
        const vp1 = vp[0];
        if (vp1 !== -1 && vp1 - k - 1 < m) {
          let xx = vp1;
          let yy = xx - k;
          while (ai[xx] === bi[yy]) { xx++; yy++; }
          vc[0] = xx;
          if (xx === n && k === kEnd) { D = d; trace.push(vc); break outer; }
        } else {
          vc[0] = -1;
        }
      }
      for (let i = 1; i < d; i++) {
        const k = 2 * i - d;
        const vm1 = vp[i - 1];
        const vp1 = vp[i];
        const canRemove = vm1 !== -1 && vm1 < n;
        const canAdd = vp1 !== -1 && vp1 - k - 1 < m;
        let xx;
        if (canRemove && (!canAdd || vm1 >= vp1 - 1)) xx = vm1 + 1;
        else if (canAdd) xx = vp1;
        else { vc[i] = -1; continue; }
        let yy = xx - k;
        while (ai[xx] === bi[yy]) { xx++; yy++; }
        vc[i] = xx;
        if (xx === n && k === kEnd) { D = d; trace.push(vc); break outer; }
      }
      // i = d, k = d: deletion only.
      {
        const k = d;
        const vm1 = vp[d - 1];
        if (vm1 !== -1 && vm1 < n) {
          let xx = vm1 + 1;
          let yy = xx - k;
          while (ai[xx] === bi[yy]) { xx++; yy++; }
          vc[d] = xx;
          if (xx === n && k === kEnd) { D = d; trace.push(vc); break outer; }
        } else {
          vc[d] = -1;
        }
      }
      trace.push(vc);
      vp = vc;
    }
  }
  if (D < 0) throw new Error('makefun-diff: the search ended without reaching both ends');

  // Backtrack the trace into runs, collected from the end backwards.
  const rev = [];
  const pushRun = (kind, count) => {
    if (count <= 0) return;
    const last = rev[rev.length - 1];
    if (last !== undefined && last.kind === kind) last.count += count;
    else rev.push({ kind, count });
  };
  let cx = n;
  let cy = m;
  let ck = kEnd;
  for (let d = D; d >= 1; d--) {
    const i = (ck + d) >> 1;
    const prev = trace[d - 1];
    const vm1 = i - 1 >= 0 ? prev[i - 1] : -1;
    const vp1 = i < prev.length ? prev[i] : -1;
    const canRemove = vm1 !== -1 && vm1 < n;
    const canAdd = vp1 !== -1 && vp1 - ck - 1 < m;
    const byDel = canRemove ? vm1 : -2;
    const byIns = canAdd ? vp1 - 1 : -2;
    let xStep;
    let yStep;
    let px;
    let py;
    let pk;
    let op;
    if (byDel >= byIns) {
      xStep = vm1 + 1;
      yStep = xStep - ck;
      px = vm1;
      py = vm1 - (ck - 1);
      pk = ck - 1;
      op = DELETE;
    } else {
      xStep = vp1;
      yStep = xStep - ck;
      px = vp1;
      py = vp1 - (ck + 1);
      pk = ck + 1;
      op = INSERT;
    }
    pushRun(KEEP, cx - xStep);
    pushRun(op, 1);
    cx = px;
    cy = py;
    ck = pk;
  }
  pushRun(KEEP, cx);
  rev.reverse();
  return rev;
}

/** makefun-diff 1.0.0's answer for one case's input. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const a = splitLines(input.old);
  const b = splitLines(input.new);
  const n = a.count;
  const m = b.count;

  // Intern every line to an integer id (a newline-terminated line and the
  // same text bare are different lines, hence the two tables).
  const mapNL = new Map();
  const mapBare = new Map();
  let nextId = 0;
  const ai = new Int32Array(n + 1);
  const bi = new Int32Array(m + 1);
  ai[n] = -1;
  bi[m] = -2;
  for (let i = 0; i < n; i++) {
    const part = a.parts[i];
    if (i < a.last) {
      let id = mapNL.get(part);
      if (id === undefined) { id = nextId++; mapNL.set(part, id); }
      ai[i] = id;
    } else {
      let id = mapBare.get(part);
      if (id === undefined) { id = nextId++; mapBare.set(part, id); }
      ai[i] = id;
    }
  }
  for (let i = 0; i < m; i++) {
    const part = b.parts[i];
    if (i < b.last) {
      let id = mapNL.get(part);
      if (id === undefined) { id = nextId++; mapNL.set(part, id); }
      bi[i] = id;
    } else {
      let id = mapBare.get(part);
      if (id === undefined) { id = nextId++; mapBare.set(part, id); }
      bi[i] = id;
    }
  }

  // The common prefix, then the common suffix of what is left.
  let prefix = 0;
  while (prefix < n && prefix < m && ai[prefix] === bi[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && ai[n - 1 - suffix] === bi[m - 1 - suffix]) suffix++;

  const runs = [];
  if (prefix > 0) runs.push({ kind: KEEP, count: prefix });
  const midN = n - prefix - suffix;
  const midM = m - prefix - suffix;
  if (midN > 0 || midM > 0) {
    const aMid = new Int32Array(midN + 1);
    const bMid = new Int32Array(midM + 1);
    aMid.set(ai.subarray(prefix, n - suffix));
    bMid.set(bi.subarray(prefix, m - suffix));
    aMid[midN] = -1;
    bMid[midM] = -2;
    runs.push(...myersRuns(aMid, bMid, midN, midM));
  }
  if (suffix > 0) runs.push({ kind: KEEP, count: suffix });

  // The change runs: each a stretch of deletions and insertions between two kept lines, at old line o and new line p.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (const r of runs) {
    if (r.kind === KEEP) {
      o += r.count;
      p += r.count;
      continue;
    }
    let c = changes.at(-1);
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (r.kind === DELETE) {
      c.dels += r.count;
      o += r.count;
      deleted += r.count;
    } else {
      c.ins += r.count;
      p += r.count;
      inserted += r.count;
    }
  }

  // The hunks: change runs at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks.at(-1);
    const prev = h?.at(-1);
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }

  // A line as the patch writes it: its op, the line, a newline, and "%" on a
  // line of its own when the line had none. Pushed as pieces, never built.
  const out = [`${FORMAT} old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  const pushLine = (op, parts, last, idx) => {
    out.push(op, parts[idx]);
    if (idx < last) out.push('\n');
    else out.push('\n%\n');
  };
  for (const h of hunks) {
    const first = h[0];
    const last = h.at(-1);
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) pushLine('=', a.parts, a.last, at);
      for (let i = 0; i < c.dels; i++) pushLine('-', a.parts, a.last, c.o + i);
      for (let i = 0; i < c.ins; i++) pushLine('+', b.parts, b.last, c.p + i);
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) pushLine('=', a.parts, a.last, at);
  }
  return out.join('');
}

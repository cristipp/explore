(function () {
'use strict';
const PAGE = document.body.dataset.page || 'grid'; // 'grid' (in-head: no thinking / thinking) | 'sota' (SOTA factoring)
const slug = s => String(s).toLowerCase().replace(/[^a-z0-9.]+/g, '-').replace(/^-|-$/g, '');
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const uniq = a => [...new Set(a)];
const FIELDS = ['task', 'model', 'mode', 'arm', 'source']; // per-panel cascade
// grid metrics: percent complete | answer time (s/n per cell) | coding time + answer time
const METRICS = [['acc', 'percent complete'], ['time', 'answer time'], ['codetime', 'coding time + answer time']];
const verbOf = t => t === 'factor' ? 'factor' : 'answer';
const metricLabel = (m, t) => METRICS.find(x => x[0] === m)[1]; // same wording for every task
const codeSec = r => (r && r.code_seconds > 0) ? r.code_seconds : 0;
const ORDER = {
  task: ['words', 'mul', 'factor'],
  mode: ['nothink', 'think', 'sota_rust_M', 'sota_rust_R', 'sota_rust_L'],
  level: ['none', 'grid', 'minimal', 'low', 'medium', 'high', 'max']
};
const PALETTE = ['#0072B2', '#E69F00', '#009E73', '#CC79A7', '#56B4E9', '#D55E00', '#8C6BB1', '#999933',
  '#882255', '#44AA99'];
// shape = condition on the SOTA page (M memory only, R web references, L anything goes); no thinking / thinking in-head
const SHAPES = { nothink: 'circle', think: 'square', sota_rust_M: 'circle', sota_rust_R: 'square', sota_rust_L: 'triangle' };
const shapeOf = mode => SHAPES[mode] || (/^sota/.test(mode) ? 'triangle' : 'diamond');
function rank(list, v) { const i = list.indexOf(v); return i < 0 ? list.length : i; }
function sortOpts(field, vals, rs) {
  if (field === 'task' || field === 'mode')
    return vals.sort((a, b) => rank(ORDER[field], a) - rank(ORDER[field], b) || String(a).localeCompare(b));
  if (field === 'arm') {
    const lv = a => { const r = rs.find(x => x.arm === a); return r ? rank(ORDER.level, r.level) : 99; };
    return vals.sort((a, b) => lv(a) - lv(b) || String(a).localeCompare(b));
  }
  return vals; // model, source: data order (first appearance)
}

// ---------- data (reloadable) ----------
let DATA, RUNS, MODELS, DOMAIN, TASK_N, GEN = null;
function cellValue(cell, metric, run) {
  if (!cell || !cell.n) return null;
  if (metric === 'acc') return cell.k / cell.n;
  if (metric === 'time') return cell.s / cell.n;
  return codeSec(run) + cell.s / cell.n;
}
function loadData() {
  DATA = window.LONGMUL_DATA || { runs: [] };
  GEN = DATA.generated_at || null;
  // each page shows its own runs: SOTA factoring programs vs in-head runs (Qwen + simonw's reference; no SOTA programs, no Claude)
  RUNS = (DATA.runs || []).filter(r => PAGE === 'sota' ? !!r.solution : !/^sota/.test(r.arm || '') && !/^claude/.test(r.model || '')).map((r, i) => Object.assign({}, r, {
    _i: i, model_short: r.model_short || slug(r.model), arm: r.arm || (r.mode + '-' + r.level),
    source: r.source || ('run ' + i), cells: r.cells || {}
  }));
  MODELS = uniq(RUNS.map(r => r.model));
  // ONE global log time domain for every time-colored value: grid answer times, grid coding+answer totals and
  // frontier answer / coding+answer times, across all runs and tasks (floor 1 µs). Same duration = same color everywhere.
  {
    let lo = Infinity, hi = -Infinity;
    const add = v => { if (v != null && isFinite(v)) { v = Math.max(v, DUR_FLOOR); lo = Math.min(lo, v); hi = Math.max(hi, v); } };
    RUNS.forEach(r => Object.values(r.cells).forEach(c => { add(cellValue(c, 'time', r)); add(cellValue(c, 'codetime', r)); }));
    frontierSeries().forEach(se => se.f.tested.forEach(t => { add(ptTime(t, se, 'time')); add(ptTime(t, se, 'codetime')); add(ptTime(t, se, 'coding')); }));
    if (!isFinite(lo)) { lo = 0.1; hi = 10; }
    if (hi <= lo) hi = lo * 10;
    DOMAIN = { T: [lo, hi] };
  }
  TASK_N = {}; // grid size per task = largest digit count seen in any run of that task
  RUNS.forEach(r => Object.keys(r.cells).forEach(k => {
    const [x, y] = k.split(',').map(Number);
    if (isFinite(x) && isFinite(y)) TASK_N[r.task] = Math.max(TASK_N[r.task] || 1, x, y);
  }));
}
const modelColor = m => PALETTE[Math.max(0, MODELS.indexOf(m)) % PALETTE.length];
// display labels for tasks (ids stay words/mul/factor in data, hash and code)
const TASK_LABEL = { words: 'add + words', mul: 'mul + words', factor: 'factor' };
const tl = t => TASK_LABEL[t] || t;
const tasks = () => sortOpts('task', uniq(RUNS.map(r => r.task)), RUNS);

// ---------- formatting ----------
// below 1 ms: whole microseconds ("12 µs"), "<1 µs" when it rounds to zero (incl. exactly 0); never "0 s"/"0 ms"
function fmtSub(s, sp) {
  const us = Math.round(Math.max(0, s) * 1e6);
  return us >= 1 ? us + sp + 'µs' : '<1' + sp + 'µs';
}
const DUR_FLOOR = 1e-6; // log scales clamp tiny/zero durations to 1 µs
function fmtDur(s) {
  if (s == null || !isFinite(s)) return '–';
  if (s < 1e-3) return fmtSub(s, ' ');
  if (s < 1) return (s < 0.01 ? (s * 1000).toFixed(1) : Math.round(s * 1000)) + ' ms';
  if (s < 60) return (s < 10 ? s.toFixed(2) : s.toFixed(1)) + ' s';
  if (s < 3600) return (s / 60).toFixed(1) + ' min';
  return (s / 3600).toFixed(2) + ' h';
}
function fmtDurRound(s) { // badge style: "18 s", "16 min", "1.2 h"
  if (s == null || !isFinite(s)) return '–';
  if (s === 0) return '0 s'; // used for coding time, where 0 means "no coding step", not a rounded duration
  if (s < 1e-3) return fmtSub(s, ' ');
  if (s < 1) return Math.round(s * 1000) + ' ms';
  if (s < 60) return Math.round(s) + ' s';
  if (s < 3600) return Math.round(s / 60) + ' min';
  return (s / 3600).toFixed(1) + ' h';
}
function fmtDurShort(s) { // fits in a 40-unit grid cell
  if (s < 1e-3) return fmtSub(s, '');
  if (s < 1) return Math.round(s * 1000) + 'ms';
  if (s < 10) return s.toFixed(1) + 's';
  if (s < 60) return Math.round(s) + 's';
  if (s < 3600) { const m = s / 60; return (m < 10 ? m.toFixed(1) : Math.round(m)) + 'm'; }
  const h = s / 3600; return (h < 10 ? h.toFixed(1) : Math.round(h)) + 'h';
}
const fmtInt = n => n == null ? '–' : Number(n).toLocaleString('en-US');
const accOf = r => r.accuracy != null ? r.accuracy : (r.cases ? r.correct / r.cases : 0);
const isGraded = r => !!(r.graded && r.graded.of > 0);
// official score: graded frontier fraction for graded runs, else benchmark accuracy
const scoreOf = r => isGraded(r) ? (r.graded.total_factored || 0) / r.graded.of : accOf(r);
const pct = x => Math.round(100 * x) + '%';
function statusBadge(r) {
  const att = fmtInt(r.attempted != null ? r.attempted : 0) + '/' + fmtInt(r.cases) + ' attempted';
  if (r.status === 'in_progress') return '<span class="stbadge run" title="still running; numbers will change">in progress · ' + att + '</span>';
  if (r.status === 'budget_cut') return '<span class="stbadge cut" title="the arm\'s 1 h budget ran out before every case was attempted">budget cut · ' + att + '</span>';
  return '';
}
// "13/91 (14%) · 13/65 of attempted"
function benchLine(r) {
  let h = fmtInt(r.correct) + '/' + fmtInt(r.cases) + ' (' + pct(accOf(r)) + ')';
  if (r.attempted != null && r.attempted < r.cases) h += ' · ' + fmtInt(r.correct) + '/' + fmtInt(r.attempted) + ' of attempted';
  return h;
}

// fine frontier (overnight galloping + binary search at one shared per-number cap); absent until post-processed
const fineOf = r => {
  const f = r && r.fine_frontier;
  return f && typeof f === 'object' && Number.isFinite(f.fine_frontier) ? f : null;
};
// "37 digits @ 17 s/number"; not exact: "≥ 37 digits" (no failure found) or "37 digits (bounds 37–40)" (upper = first_failure − 1)
function fmtFine(f, short) {
  if (!f) return '';
  const cap = Number.isFinite(f.cap_seconds) ? ' @ ' + fmtDurRound(f.cap_seconds) + '/number' : '';
  let v;
  if (f.exact) v = f.fine_frontier + (short ? '' : ' digits');
  else if (!Number.isFinite(f.first_failure)) v = '≥ ' + f.fine_frontier + (short ? '' : ' digits');
  else v = f.fine_frontier + (short ? '' : ' digits') + ' (bounds ' + f.fine_frontier + '–' + (f.first_failure - 1) + ')';
  return v + cap;
}
// compact table cell: "37 exact · 17 s cap", "33–40 · 17 s cap", "≥ 20 · 17 s cap"
function fineCell(f) {
  const v = f.exact ? f.fine_frontier + ' exact' : !Number.isFinite(f.first_failure) ? '≥ ' + f.fine_frontier
    : f.fine_frontier + '–' + (f.first_failure - 1);
  return v + (Number.isFinite(f.cap_seconds) ? ' · ' + fmtDurRound(f.cap_seconds) + ' cap' : '');
}
// "better" hints are chart chrome, not data: short (28 px), thin, muted axis ink, small head, always in a margin
const BETTER_INK = 'var(--muted)', BETTER_LEN = 28;
function arrowSvg(x1, y1, x2, y2) { // straight, axis-aligned, head at (x2,y2)
  const h = 5, dx = Math.sign(x2 - x1), dy = Math.sign(y2 - y1);
  const head = dx ? 'M' + x2 + ',' + y2 + 'l' + (-dx * h) + ',' + (-h * 0.6) + 'v' + (h * 1.2) + 'z'
    : 'M' + x2 + ',' + y2 + 'l' + (-h * 0.6) + ',' + (-dy * h) + 'h' + (h * 1.2) + 'z';
  return '<line x1="' + x1 + '" y1="' + y1 + '" x2="' + (x2 - dx * h) + '" y2="' + (y2 - dy * h) + '" stroke="' + BETTER_INK +
    '" stroke-width="1.25"/><path d="' + head + '" fill="' + BETTER_INK + '"/>';
}
// vertical hint for a y axis: rotated muted label + arrow, centered on cy, arrow column at x (label baseline at x+5)
function axisBetter(x, cy, up, label) {
  const w = label.length * 6.6, total = w + 6 + BETTER_LEN, top = cy - total / 2, bot = cy + total / 2;
  let s = '<g class="better" aria-hidden="true">';
  if (up) {
    s += arrowSvg(x, top + BETTER_LEN, x, top);
    s += '<text transform="translate(' + (x + 5) + ',' + (top + BETTER_LEN + 6) + ') rotate(-90)" text-anchor="end" style="font-size:13px;fill:' + BETTER_INK + '">' + label + '</text>';
  } else {
    s += arrowSvg(x, bot - BETTER_LEN, x, bot);
    s += '<text transform="translate(' + (x + 5) + ',' + (bot - BETTER_LEN - 6) + ') rotate(-90)" text-anchor="start" style="font-size:13px;fill:' + BETTER_INK + '">' + label + '</text>';
  }
  return s + '</g>';
}
// horizontal hint: arrow head at x0 pointing left/right, label beside the tail
function hBetter(x0, y, left, label) {
  const tail = left ? x0 + BETTER_LEN : x0 - BETTER_LEN;
  return '<g class="better" aria-hidden="true">' + arrowSvg(tail, y, x0, y) +
    '<text x="' + (left ? tail + 5 : tail - 5) + '" y="' + (y + 4) + '" text-anchor="' + (left ? 'start' : 'end') +
    '" style="font-size:12px;fill:' + BETTER_INK + '">' + label + '</text></g>';
}
function fmtFrontier(f) {
  if (!f) return '';
  const fd = f.frontier_digits, ff = f.first_failure_digits;
  return 'frontier: ' + (fd == null ? '–' : fd + ' digits') +
    (ff != null ? ' (fails at ' + ff + ')' : ' (no failure up to ' + Math.max(0, ...(f.tested || []).map(t => t.d)) + ')');
}

// how the frontier eval limited time: fixed per-number cap (older) or the v4 shared-hour budget
function frProto(f) {
  return 'p, q both d digits; ' + (f.k != null ? f.k : '?') + ' pairs each; ' + (f.time_limit != null
    ? f.time_limit + ' s cap' : 'each number gets T = time left ÷ numbers left (v4)');
}
// v4: a size where nothing passed and the whole size took ~no time = the program crashed instantly
const isCrash = (t, k) => (t.passed || 0) === 0 && t.wall != null && t.wall / (k || 1) < 0.1 && t.cap !== 'skipped';

// ---------- color scales ----------
const lerp = (a, b, t) => a.map((x, i) => Math.round(x + (b[i] - x) * t));
const ORANGE = [230, 97, 1], NEUTRAL = [247, 247, 247], BLUE = [33, 102, 172];
const SEQ = [[252, 251, 253], [158, 154, 200], [63, 0, 125]]; // purples, for time (log)
function divColor(t) {
  t = Math.min(1, Math.max(0, t));
  return t < 0.5 ? lerp(ORANGE, NEUTRAL, t * 2) : lerp(NEUTRAL, BLUE, (t - 0.5) * 2);
}
function seqColor(t) {
  t = Math.min(1, Math.max(0, t));
  return t < 0.5 ? lerp(SEQ[0], SEQ[1], t * 2) : lerp(SEQ[1], SEQ[2], (t - 0.5) * 2);
}
const rgb = c => 'rgb(' + c.join(',') + ')';
function textOn(c) {
  const L = (0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2]) / 255;
  return L < 0.5 ? '#fff' : '#111';
}
// THE time color: one ramp (seqColor) over one domain (DOMAIN.T), used by every time-colored mark on the page
function timeT(v) { const [lo, hi] = DOMAIN.T; return (Math.log(Math.min(Math.max(v, lo), hi)) - Math.log(lo)) / (Math.log(hi) - Math.log(lo)); }
const timeColor = v => seqColor(timeT(v));
function colorFor(v, metric) {
  if (metric === 'acc') return divColor(v);
  return timeColor(v); // same for 'time' and 'codetime': no per-metric scale
}

// ---------- state ----------
let panels = [];   // [{id, task, model, mode, arm, source, metric, from}]  from = id of the panel whose task it follows
let ovTask = null; // overview task; null = follow the first panel
let uid = 0;
let ovY = 'acc';     // overview y axis: 'acc' | 'frontier' (frontier only offered when the task has it)
let frMetric = 'time'; // frontier chart y: 'evals' | 'time' | 'coding'
let frAnchorTest = false; // timeline: anchor reach steps to the first test instead of the code edit
let frRefs = false; // show the R (web references) runs: off by default, since no run used the web
let frFine = false; // show partial factorization success + fine-frontier markers (off by default)
let frOff = []; // frontier series ids toggled off (new runs show by default)
let ovModes = null; // null = all modes; else array of modes to plot (may include modes the task lacks)

function candidates(sel, upto) {
  let rs = RUNS;
  for (const f of FIELDS) {
    if (f === upto) break;
    rs = rs.filter(r => r[f] === sel[f]);
  }
  return rs;
}
function optionsFor(sel, field) {
  const rs = candidates(sel, field);
  return sortOpts(field, uniq(rs.map(r => r[field])), rs);
}
// keep each field if still valid, else first valid option; fields before fromIdx+1 are left alone
function normalize(sel, fromIdx) {
  for (let i = fromIdx + 1; i < FIELDS.length; i++) {
    const f = FIELDS[i], opts = optionsFor(sel, f);
    if (!opts.includes(sel[f])) { if (!opts.length) break; sel[f] = opts[0]; }
  }
  if (sel.metric === 'mean' || sel.metric === 'total') sel.metric = 'time'; // pre-v5 hashes
  if (!METRICS.some(m => m[0] === sel.metric)) sel.metric = 'acc';
  return sel;
}
const runOf = sel => RUNS.find(r => FIELDS.every(f => r[f] === sel[f])) || null;
// a panel whose model/mode/arm now exist but whose source is unknown (e.g. data just arrived) resolves itself
function resolve(p) {
  if (runOf(p)) return;
  const head = FIELDS.slice(0, 4);
  if (head.every(f => optionsFor(p, f).includes(p[f]))) p.source = optionsFor(p, 'source')[0];
}
function selFromRun(r, metric) {
  const s = { metric: metric || 'acc' };
  FIELDS.forEach(f => s[f] = r[f]);
  return s;
}
function defaultTask() { const ts = tasks(); return ts.includes('words') ? 'words' : (ts[0] || 'words'); }
function defaults(t) {
  const rs = RUNS.filter(r => r.task === (t || defaultTask()));
  const flash = rs.filter(r => /flash/i.test(r.model));
  const a = flash.find(r => r.arm === 'nothink'), b = flash.find(r => r.arm === 'think-medium');
  if (a && b) return [selFromRun(a), selFromRun(b)];
  return rs.slice(0, 2).map(r => selFromRun(r));
}
// default view: #1 = add + words, no thinking; #2 clones #1 with one override, task = mul + words
function defaultPanels() {
  const ps = defaults().slice(0, 1).map(newPanel);
  if (ps.length && RUNS.some(r => r.task === 'mul')) {
    const q = newPanel(Object.assign({}, ps[0], { from: ps[0].id, ov: { task: true }, ovv: { task: 'mul' } }));
    q.task = 'mul';
    ps.push(q);
  }
  panels = ps;
  propagate();
  return panels;
}
const byId = id => panels.find(x => x.id === id) || null;
// does q (directly or transitively) take its task from p?
function followsChain(q, p) {
  const seen = new Set();
  for (let cur = q; cur && cur.from != null && !seen.has(cur.id); cur = byId(cur.from)) {
    seen.add(cur.id);
    if (cur.from === p.id) return true;
  }
  return false;
}
// push tasks down "clone from" links (chains resolve; dangling links are dropped, keeping the current task)
// a follower inherits every selector from its (resolved) source, except fields in p.ov (local overrides);
// an override that is invalid for the inherited upstream fields falls back to the first valid value (marker kept)
const LINKED = ['task', 'model', 'mode', 'arm', 'source', 'metric'];
const snap = p => LINKED.map(f => p[f]).join('\u0001');
function propagate() {
  panels.forEach(p => {
    if (!p.ov) p.ov = {};
    if (!p.ovv) p.ovv = {};
    if (p.from != null && (!byId(p.from) || p.from === p.id)) p.from = null;
  });
  for (let n = 0; n <= panels.length + 1; n++) {
    let changed = false;
    panels.forEach(p => {
      if (p.from == null) return;
      const src = byId(p.from); if (!src) return;
      const before = snap(p);
      // overrides re-apply their wanted value (p.ovv) each time, so they come back once valid again
      LINKED.forEach(f => { p[f] = p.ov[f] ? (p.ovv && p.ovv[f] != null ? p.ovv[f] : p[f]) : src[f]; });
      delete p._ms;
      normalize(p, 0);
      if (snap(p) !== before) changed = true;
    });
    if (!changed) break;
  }
}
const wantOf = (p, f) => p.ovv && p.ovv[f] != null ? p.ovv[f] : p[f];
const nOv = p => p.from != null ? Object.keys(p.ov || {}).filter(f => p.ov[f]).length : 0;
const effTask = () => ovTask || (panels[0] && panels[0].task) || defaultTask();

// ---------- URL hash ----------
// #p=<panel>;<panel>...[&o=<overview task>][&m=<mode>,...][&y=frontier][&fr=<id toggled from default>,...][&fm=evals|coding]
//   <panel> = task|model_short|mode|arm|metric|c<k>[:field=value,...][|source]   (c<k>: all selectors follow pane k,
//   1-based, except the listed local overrides; c0 = independent;
//   parts URI-encoded;
//   source only when ambiguous or unresolved)
// o absent = overview follows panel 1's task. m absent = all modes, m= empty = none. fm absent = answer time (old fm=pass = # evals).
// fr = frontier-chart series switched off; id = model_short/arm[/source if ambiguous][/sub-entry key].
// Accepted older formats: s0/s1 instead of c<k> (s1 panels follow the first s1 panel; s0 = none);
// #t=<task>&p=model_short|mode|arm|metric[|source] (t applied to every panel; all follow panel 1); and
// #p=task|model_short|mode|arm|metric[|source] (no links).
function shortOf(model) { const r = RUNS.find(x => x.model === model); return r ? r.model_short : model; }
function encodeHash() {
  if (PAGE === 'sota') {
    const h = [frOff.length ? 'fr=' + frOff.map(encodeURIComponent).join(',') : '', frFine ? 'ff=1' : '', frRefs ? 'rr=1' : '', frAnchorTest ? 'at=1' : ''].filter(Boolean).join('&');
    return h ? '#' + h : location.pathname + location.search;
  }
  const ps = panels.map(p => {
    const k = p.from != null ? panels.findIndex(x => x.id === p.from) + 1 : 0;
    const parts = [p.task, shortOf(p.model), p.mode, p.arm, p.metric].map(encodeURIComponent);
    // link part: c<k>[:field=value,...] with only the overridden fields
    const ovs = k > 0 ? LINKED.filter(f => p.ov && p.ov[f]) : [];
    parts.push('c' + Math.max(0, k) + (ovs.length ? ':' + ovs.map(f =>
      f + '=' + encodeURIComponent(f === 'model' ? shortOf(wantOf(p, f)) : wantOf(p, f))).join(',') : ''));
    const nsrc = RUNS.filter(x => ['task', 'model', 'mode', 'arm'].every(f => x[f] === p[f])).length;
    if (nsrc > 1 || !runOf(p)) parts.push(encodeURIComponent(p.source || ''));
    return parts.join('|');
  });
  return '#p=' + ps.join(';') + (ovTask ? '&o=' + encodeURIComponent(ovTask) : '') +
    (ovModes ? '&m=' + ovModes.map(encodeURIComponent).join(',') : '') + (ovY !== 'acc' ? '&y=' + ovY : '') +
    (frOff.length ? '&fr=' + frOff.map(encodeURIComponent).join(',') : '') + (frMetric !== 'time' ? '&fm=' + frMetric : '');
}
function writeHash() {
  const h = encodeHash();
  if (location.hash !== h) history.replaceState(null, '', h);
}
function modelFromShort(ms) { const m = RUNS.find(r => r.model_short === ms || r.model === ms); return m ? m.model : ms; }
function readHash() {
  const h = location.hash.replace(/^#/, '');
  if (!h) return false;
  const kv = {};
  h.split('&').forEach(x => { const i = x.indexOf('='); if (i > 0) kv[x.slice(0, i)] = x.slice(i + 1); });
  frMetric = kv.fm === 'evals' || kv.fm === 'pass' ? 'evals' : kv.fm === 'coding' || kv.fm === 'codetime' ? 'coding' : 'time'; // absent -> answer time
  frOff = kv.fr ? kv.fr.split(',').filter(Boolean).map(decodeURIComponent) : [];
  frFine = kv.ff === '1';
  frRefs = kv.rr === '1';
  frAnchorTest = kv.at === '1';
  if (PAGE === 'sota') return true; // the SOTA page has no panels
  if (kv.p == null && kv.t == null) return false;
  ovY = kv.y === 'frontier' ? 'frontier' : 'acc';
  ovModes = kv.m == null ? null : kv.m.split(',').filter(Boolean).map(decodeURIComponent);
  const o = kv.o != null ? decodeURIComponent(kv.o) : null;
  ovTask = o && o !== 'all' ? o : null;
  // the link part (index 5) is parsed raw: its override values are URI-encoded individually
  const raw = kv.p ? kv.p.split(';').filter(Boolean).map(s => s.split('|').map((x, i) =>
    i === 5 && /^c\d+/.test(x || '') ? x : decodeURIComponent(x || ''))) : [];
  let rows;
  if (kv.t != null) { // global-task format: t applies to every panel, all synced
    const t = decodeURIComponent(kv.t);
    rows = raw.map(([ms, mode, arm, metric, source]) => ({ task: t, ms, mode, arm, metric, source, link: 's1' }));
  } else {
    rows = raw.map(a => /^(s[01]$|c\d+)/.test(a[5] || '')
      ? { task: a[0], ms: a[1], mode: a[2], arm: a[3], metric: a[4], link: a[5], source: a[6] }
      : { task: a[0], ms: a[1], mode: a[2], arm: a[3], metric: a[4], link: 'c0', source: a[5] }); // oldest format
  }
  panels = rows.map(r => {
    const p = { id: ++uid, task: r.task, model: modelFromShort(r.ms), mode: r.mode, arm: r.arm,
      metric: ({ mean: 'time', total: 'time' })[r.metric] || r.metric || 'acc', source: r.source || '', from: null, ov: {}, ovv: {}, _ms: r.ms };
    const m = /^c\d+:(.*)$/.exec(r.link || '');
    if (m) m[1].split(',').filter(Boolean).forEach(kvp => {
      const j = kvp.indexOf('='); if (j < 0) return;
      const f = kvp.slice(0, j), v = decodeURIComponent(kvp.slice(j + 1));
      if (!LINKED.includes(f)) return;
      p.ov[f] = true; p[f] = p.ovv[f] = f === 'model' ? modelFromShort(v) : v;
    });
    // old sync (s1) only shared the task: keep the other fields as local overrides
    if (r.link === 's1') ['model', 'mode', 'arm', 'metric'].forEach(f => { p.ov[f] = true; p.ovv[f] = p[f]; });
    resolve(p);
    return p;
  });
  // links: c<k> -> pane k; old s1 -> first s1 pane
  const firstS1 = rows.findIndex(r => r.link === 's1');
  rows.forEach((r, i) => {
    let k = -1;
    if (/^c\d+/.test(r.link)) k = parseInt(r.link.slice(1), 10) - 1;
    else if (r.link === 's1' && i !== firstS1) k = firstS1;
    if (k >= 0 && k < panels.length && k !== i) panels[i].from = panels[k].id;
  });
  panels.forEach(p => { if (p.from != null && followsChain(byId(p.from), p)) p.from = null; }); // break cycles
  propagate();
  return true;
}

// ---------- panel rendering ----------
// a follower's locally overridden field: bold label with a dot, plus a ↺ button that reverts it to inherited
function markOverride(lab, p, f, idx) {
  if (p.from == null || !(p.ov && p.ov[f])) return;
  lab.classList.add('ovr');
  const row = document.createElement('span'); // label text and ↺ on one line, select below
  row.textContent = '• ' + lab.textContent + ' ';
  lab.textContent = '';
  lab.appendChild(row);
  const b = document.createElement('button');
  b.type = 'button'; b.className = 'revert'; b.dataset.act = 'revert'; b.dataset.f = f; b.textContent = '↺';
  b.title = 'Revert ' + f + ' to the value inherited from the clone-from panel';
  b.setAttribute('aria-label', 'Chart ' + (idx + 1) + ': revert ' + f + ' to inherited');
  row.appendChild(b);
}
const STAT_LINES = 4; // fixed number of stats lines per panel header
const LABELS = { task: 'task', model: 'model', mode: 'mode', arm: 'arm (level)', source: 'source', metric: 'metric' };

function renderPanel(p, idx) {
  // model names from the hash may predate the data that defines them; map short -> full once available
  if (p._ms && !MODELS.includes(p.model)) p.model = modelFromShort(p._ms);
  resolve(p);
  const el = document.createElement('section');
  el.className = 'panel';
  el.dataset.id = p.id;
  el.setAttribute('aria-label', 'Chart ' + (idx + 1));
  const top = document.createElement('div');
  top.className = 'ptop';
  top.innerHTML = '<span class="pnum">#' + (idx + 1) + '</span><span class="pbtns">' +
    '<button type="button" data-act="clone" aria-label="Clone chart ' + (idx + 1) + '">Clone</button>' +
    '<button type="button" data-act="remove" aria-label="Remove chart ' + (idx + 1) + '">Remove</button></span>';
  // fixed row structure (controls / title+stats / chart / footer) shared with the neighbours via CSS subgrid,
  // so charts in the same grid row line up whatever the header holds
  const ctrl = document.createElement('div'), head = document.createElement('div');
  const chart = document.createElement('div'), foot = document.createElement('div');
  ctrl.className = 'prow-ctrl'; head.className = 'prow-head'; chart.className = 'prow-chart'; foot.className = 'prow-foot';
  [ctrl, head, chart, foot].forEach(x => el.appendChild(x));
  ctrl.appendChild(top);

  const sels = document.createElement('div');
  sels.className = 'sels';
  let broken = false;
  FIELDS.forEach(f => {
    const opts = broken ? [] : optionsFor(p, f);
    if (f === 'source' && opts.length <= 1 && !broken && opts.includes(p.source)) return; // hide when unambiguous
    const lab = document.createElement('label');
    lab.textContent = LABELS[f];
    const s = document.createElement('select');
    s.dataset.field = f;
    s.setAttribute('aria-label', 'Chart ' + (idx + 1) + ' ' + LABELS[f]);

    const all = opts.slice();
    if (!all.includes(p[f])) all.unshift(p[f]);
    all.forEach(v => {
      const o = document.createElement('option');
      o.value = v == null ? '' : v;
      const lab = f === 'task' ? tl(v) : v;
      o.textContent = opts.includes(v) ? lab : (lab || '(none)') + ' — no data';
      if (v === p[f]) o.selected = true;
      s.appendChild(o);
    });
    if (!opts.includes(p[f])) broken = true;
    markOverride(lab, p, f, idx);
    lab.appendChild(s);
    sels.appendChild(lab);
    if (f === 'task') { // "clone from": follow another pane's task; panes that follow this one are left out (no cycles)
      const cl = document.createElement('label');
      cl.textContent = 'clone from';
      const cs = document.createElement('select');
      cs.dataset.act = 'from';
      cs.setAttribute('aria-label', 'Chart ' + (idx + 1) + ' clone task from');
      cs.title = 'Follow another panel’s task, live';
      let opts = '<option value="">—</option>';
      panels.forEach((q, j) => {
        if (q === p || followsChain(q, p)) return;
        opts += '<option value="' + q.id + '"' + (p.from === q.id ? ' selected' : '') + '>#' + (j + 1) + '</option>';
      });
      cs.innerHTML = opts;
      cl.appendChild(cs);
      sels.appendChild(cl);
      if (p.from != null && byId(p.from)) { // inline note, same row as the clone-from select
        const nt = document.createElement('span');
        nt.className = 'fromnote';
        const n = nOv(p);
        nt.textContent = '↳ from #' + (panels.findIndex(x => x.id === p.from) + 1) + (n ? ' (' + n + ' override' + (n > 1 ? 's' : '') + ')' : '');
        sels.appendChild(nt);
      }
    }
  });
  const ml = document.createElement('label');
  ml.textContent = LABELS.metric;
  const ms = document.createElement('select');
  ms.dataset.field = 'metric';
  ms.setAttribute('aria-label', 'Chart ' + (idx + 1) + ' metric');
  markOverride(ml, p, 'metric', idx);
  METRICS.forEach(([v]) => {
    const o = document.createElement('option'); o.value = v; o.textContent = metricLabel(v, p.task);
    if (v === p.metric) o.selected = true; ms.appendChild(o);
  });
  ml.appendChild(ms);
  sels.appendChild(ml);
  ctrl.appendChild(sels);

  const run = runOf(p);
  if (!run) {
    const e = document.createElement('div');
    e.className = 'empty';
    e.innerHTML = '<strong>No run for this combination.</strong><br>' +
      esc([tl(p.task), p.model, p.mode, p.arm].join(' · ')) +
      '<br>Pick another option above. Options marked “no data” are not in summary-data.js (yet). ' +
      'This panel fills in by itself if the run arrives.';
    chart.appendChild(e);
    return el;
  }
  // title line: run name (ellipsis) + right-aligned pills, so badges never add a line
  const t = document.createElement('div');
  t.className = 'ptitle';
  const ttxt = tl(run.task) + ' · ' + run.model + ' · ' + run.arm;
  t.innerHTML = '<span class="tt" title="' + esc(ttxt) + '">' + esc(ttxt) + '</span><span class="pills">' +
    statusBadge(run) + '</span>';
  head.appendChild(t);
  // stats: exactly STAT_LINES lines, each one line high (ellipsis + full-text tooltip), so the header height is constant
  const lines = [];
  let l1 = isGraded(run)
    ? '<strong>frontier ' + esc(run.graded.frontier_digits) + ' digits · ' + fmtInt(run.graded.total_factored) + '/' +
      fmtInt(run.graded.of) + ' factored</strong> (graded) · '
    : '<strong>' + benchLine(run) + '</strong> · ';
  l1 += 'total ' + esc(fmtDur(run.seconds)) + ' · ' + fmtInt(run.tokens) + ' tokens';
  if (run.attempted != null && run.attempted !== run.cases && !run.status)
    l1 += ' · <span class="m">attempted ' + fmtInt(run.attempted) + '</span>';
  if (run.cap) l1 += ' · cap: <strong>' + esc(run.cap) + '</strong>';
  // coding time once at most: in the stats line, except in the coding+answer view where it is inside every cell
  if (codeSec(run) > 0 && p.metric !== 'codetime') l1 += ' · coding time ' + esc(fmtDur(run.code_seconds));
  lines.push(l1);
  const extras = [];
  // fine frontier first: it gets its own stats line (later extras may be merged onto one line)
  if (fineOf(run)) extras.push('<strong>fine frontier ' + esc(fmtFine(fineOf(run))) + '</strong>');
  if (isGraded(run)) extras.push('<span class="m">benchmark ' + benchLine(run) + '</span>');
  if (run.hidden && run.hidden.cases != null)
    extras.push('hidden <strong>' + fmtInt(run.hidden.correct) + '/' + fmtInt(run.hidden.cases) + '</strong>' +
      (run.hidden.cap ? ' <span class="m">(cap: ' + esc(run.hidden.cap) + ')</span>' : ''));
  if (Array.isArray(run.history) && run.history.length)
    extras.push('<span class="m">' + run.history.map(h => {
      const tip = [h.cap ? 'cap ' + h.cap : '', h.hidden_correct != null ? 'hidden ' + h.hidden_correct : '',
        h.spent_seconds != null ? 'spent ' + fmtDur(h.spent_seconds) : ''].filter(Boolean).join(', ');
      return '<span title="' + esc(tip) + '">iter ' + esc(h.iter) + ': ' + fmtInt(h.correct) + '/' + fmtInt(h.cases) + '</span>';
    }).join(' → ') + '</span>');
  if (run.frontier) extras.push('<strong>' + esc(fmtFrontier(run.frontier)) + '</strong> <span class="m">(' +
    esc(frProto(run.frontier)) + ')</span>');
  const room = STAT_LINES - 2; // minus headline and source
  if (extras.length > room) extras.splice(room - 1, extras.length, extras.slice(room - 1).join(' · '));
  lines.push(...extras);
  while (lines.length < STAT_LINES - 1) lines.push('');
  lines.push('<span class="m">source: ' + esc(run.source) + '</span>');
  const st = document.createElement('div');
  st.className = 'pstats';
  st.innerHTML = lines.map(h => '<div class="sl' + (h ? '' : ' blank') + '">' + (h || '&nbsp;') + '</div>').join('');
  st.querySelectorAll('.sl').forEach(d => { if (d.textContent.trim()) d.title = d.textContent; });
  head.appendChild(st);
  const g = document.createElement('div');
  g.className = 'hm';
  g.innerHTML = heatmap(run, p.metric, p.id);
  chart.appendChild(g);
  if (run.frontier && Array.isArray(run.frontier.tested) && run.frontier.tested.length) {
    const fs = document.createElement('div');
    fs.className = 'hm';
    fs.innerHTML = frontierStrip(run.frontier);
    foot.appendChild(fs);
  }
  return el;
}

function heatmap(run, metric, id) {
  const N = TASK_N[run.task] || 13, X = N, Y = N; // always square, same size for every run of a task
  const fac = run.task === 'factor';
  const xn = fac ? 'p' : 'a', yn = fac ? 'q' : 'b';
  const C = 40, ml = 54, mt = 6, mb = 50;
  const W = ml + X * C + 6, legH = metric === 'acc' ? 58 : 78, H = mt + Y * C + mb + legH;
  let s = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="' +
    esc('Grid of ' + metricLabel(metric, run.task) + ' by digits of ' + xn + ' and ' + yn) + '">';
  const hid = 'hatch' + id;
  if (metric !== 'acc') s += '<defs><pattern id="' + hid + '" width="7" height="7" patternUnits="userSpaceOnUse" ' +
    'patternTransform="rotate(45)"><line x1="0" y1="0" x2="0" y2="7" stroke="#e66101" stroke-width="3"/></pattern></defs>';
  for (let y = 1; y <= Y; y++) {
    const py = mt + (Y - y) * C;
    s += '<text class="ax" x="' + (ml - 6) + '" y="' + (py + C / 2 + 4) + '" text-anchor="end">' + y + '</text>';
    for (let x = 1; x <= X; x++) {
      const px = ml + (x - 1) * C, cell = run.cells[x + ',' + y], v = cellValue(cell, metric, run);
      if (v == null) {
        s += '<rect x="' + px + '" y="' + py + '" width="' + (C - 1) + '" height="' + (C - 1) +
          '" fill="var(--empty)"><title>' + xn + '=' + x + ', ' + yn + '=' + y + ': no data</title></rect>';
        continue;
      }
      const c = colorFor(v, metric);
      const failed = cell.k < cell.n;
      // text and color show the same value: answer time (time view) or coding time + answer time (codetime view)
      const txt = metric === 'acc' ? String(Math.round(v * 100)) : (failed ? '≥' : '') + fmtDurShort(v);
      const tip = xn + '=' + x + ' digits, ' + yn + '=' + y + ' digits: ' + cell.k + '/' + cell.n + ' correct; ' +
        'coding time ' + fmtDurRound(codeSec(run)) + ', answer time ' + fmtDur(cell.s / cell.n) + '/case, total ' +
        fmtDur(codeSec(run) + cell.s / cell.n) + (cell.n > 1 ? ' (cell answer time ' + fmtDur(cell.s) + ' for ' + cell.n + ' cases)' : '') +
        (metric !== 'acc' && failed ? '. Some cases failed or timed out: time is a lower bound' : '');
      s += '<rect x="' + px + '" y="' + py + '" width="' + (C - 1) + '" height="' + (C - 1) + '" fill="' + rgb(c) +
        '"><title>' + esc(tip) + '</title></rect>';
      if (metric !== 'acc' && failed)
        s += '<rect x="' + px + '" y="' + py + '" width="' + (C - 1) + '" height="' + (C - 1) + '" fill="url(#' + hid +
          ')" opacity=".55" pointer-events="none"/>';
      s += '<text class="cellv" x="' + (px + C / 2 - 0.5) + '" y="' + (py + C / 2 + 4) +
        '" text-anchor="middle" style="fill:' + textOn(c) + (txt.length > 4 ? ';font-size:' + (txt.length > 5 ? 9 : 10.5) + 'px' : '') +
        '">' + txt + '</text>';
    }
  }
  const by = mt + Y * C;
  for (let x = 1; x <= X; x++)
    s += '<text class="ax" x="' + (ml + (x - 1) * C + C / 2) + '" y="' + (by + 16) + '" text-anchor="middle">' + x + '</text>';
  s += '<text class="axt" x="' + (ml + X * C / 2) + '" y="' + (by + 38) + '" text-anchor="middle">digits of ' + xn + '</text>';
  s += '<text class="axt" transform="translate(16,' + (mt + Y * C / 2) + ') rotate(-90)" text-anchor="middle">digits of ' + yn + '</text>';
  // legend
  const ly = by + mb + 16, lw = Math.max(80, Math.min(260, X * C - 110)), gid = 'lg' + id + metric;
  const stops = [];
  for (let i = 0; i <= 10; i++) stops.push('<stop offset="' + i * 10 + '%" stop-color="' +
    rgb(metric === 'acc' ? divColor(i / 10) : seqColor(i / 10)) + '"/>');
  s += '<defs><linearGradient id="' + gid + '">' + stops.join('') + '</linearGradient></defs>';
  s += '<rect x="' + ml + '" y="' + ly + '" width="' + lw + '" height="14" fill="url(#' + gid + ')" stroke="var(--rule)"/>';
  // which end is better: percent complete → right (higher), time views → left (lower = faster)
  s += metric === 'acc' ? hBetter(ml + lw, ly - 7, false, 'higher is better') : hBetter(ml, ly - 7, true, 'lower is better');
  let lo, hi;
  if (metric === 'acc') { lo = '0%'; hi = '100%'; }
  else { lo = fmtDur(DOMAIN.T[0]); hi = fmtDur(DOMAIN.T[1]); }
  if (metric !== 'acc') { // same ticks in every panel: the time scale is global
    const [a, b] = DOMAIN.T, la = Math.log(a), lb = Math.log(b);
    let lastX = -1e9;
    [[1e-6, '1µs'], [1e-3, '1ms'], [1, '1s'], [60, '1m'], [3600, '1h']].forEach(([v, lab]) => {
      if (v <= a || v >= b) return;
      const x = ml + (Math.log(v) - la) / (lb - la) * lw;
      s += '<line x1="' + x + '" x2="' + x + '" y1="' + ly + '" y2="' + (ly + 18) + '" stroke="var(--fg)" stroke-width="1"/>';
      if (x - lastX < 34 || x - ml < 34 || ml + lw - x < 52) return; // keep clear of the end labels
      lastX = x;
      s += '<text class="ax" x="' + x + '" y="' + (ly + 32) + '" text-anchor="middle">' + lab + '</text>';
    });
  }
  if (metric !== 'acc') {
    const hx = ml + lw + 120;
    s += '<rect x="' + hx + '" y="' + ly + '" width="14" height="14" fill="url(#' + hid + ')" stroke="var(--rule)"/>';
    s += '<text class="ax" x="' + (hx + 20) + '" y="' + (ly + 12) + '">≥ some failed</text>';
  }
  s += '<text class="ax" x="' + ml + '" y="' + (ly + 32) + '">' + esc(lo) + '</text>';
  s += '<text class="ax" x="' + (ml + lw) + '" y="' + (ly + 32) + '" text-anchor="end">' + esc(hi) + '</text>';
  const gx = ml + lw + 16;
  s += '<rect x="' + gx + '" y="' + ly + '" width="14" height="14" fill="var(--empty)"/>';
  s += '<text class="ax" x="' + (gx + 20) + '" y="' + (ly + 12) + '">no data</text>';
  if (metric !== 'codetime') // codetime states its cell meaning on the line under the bar
    s += '<text class="ax" x="' + (gx + 20) + '" y="' + (ly + 32) + '" style="fill:var(--muted)">' +
      (metric === 'acc' ? 'cell = % correct' : 'cell = answer time / case') + '</text>';
  if (metric !== 'acc') // one line under the bar: what the cell shows + the shared-scale note
    s += '<text class="ax" x="' + ml + '" y="' + (ly + 54) + '" style="fill:var(--muted)">' +
      (metric === 'codetime' ? 'cell = coding time + answer time per case · ' : '') + 'log scale shared by all panels</text>';
  return s + '</svg>';
}

// strip of the galloping frontier search: one cell per tested balanced size d, colored by passed/k
function frontierStrip(f) {
  const byD = new Map(f.tested.map(t => [t.d, t]));
  const ds = uniq((f.points || []).concat(f.tested.map(t => t.d))).sort((a, b) => a - b);
  const ts = ds.map(d => byD.get(d) || { d, missing: true });
  const C = 60, ml = 54, mt = 30, W = Math.max(ml + ts.length * C + 6, 900), H = mt + C + 46;
  let s = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="' + esc('Frontier eval: ' + fmtFrontier(f)) + '">';
  s += '<text class="axt" x="0" y="16">frontier eval (' + esc(frProto(f)) + ')</text>';
  s += '<text class="ax" x="' + (ml - 6) + '" y="' + (mt + C / 2 + 4) + '" text-anchor="end">pass</text>';
  ts.forEach((t, i) => {
    const x = ml + i * C, k = t.k || f.k || 1, frac = (t.passed || 0) / k, c = divColor(frac);
    if (t.missing || t.cap === 'skipped') {
      const lab = t.missing ? '–' : 'skip';
      const tip = 'd=' + t.d + ': ' + (t.missing ? 'not tested' : 'skipped (previous size scored 0), counted as 0/' + k);
      s += '<rect x="' + (x + 1) + '" y="' + mt + '" width="' + (C - 3) + '" height="' + (C - 3) + '" fill="' +
        (t.missing ? 'var(--empty)' : rgb(divColor(0))) + '" fill-opacity="' + (t.missing ? 1 : 0.3) +
        '" stroke="var(--muted)" stroke-dasharray="3 3"><title>' + esc(tip) + '</title></rect>';
      s += '<text class="cellv" x="' + (x + C / 2) + '" y="' + (mt + C / 2 + 3) + '" text-anchor="middle" style="font-size:14px">' + lab + '</text>';
      s += '<text class="ax" x="' + (x + C / 2) + '" y="' + (mt + C + 12) + '" text-anchor="middle">' + esc(t.d) + '</text>';
      return;
    }
    const tip = 'd=' + t.d + ': ' + (t.passed || 0) + '/' + k + ' passed, cap ' + (t.cap || '–') +
      (t.t_given_min != null ? ', time limit ≥ ' + fmtDur(t.t_given_min) : '') +
      (t.wall != null ? ', wall ' + fmtDur(t.wall) : '') + (t.timeouts != null ? ', timeouts ' + t.timeouts : '') +
      (t.median_solve_s != null ? ', median solve ' + fmtDur(t.median_solve_s) : '') +
      (isCrash(t, k) ? ' (crashed instantly)' : '');
    const edge = t.d === f.frontier_digits ? ' stroke="var(--fg)" stroke-width="3"' :
      t.d === f.first_failure_digits ? ' stroke="var(--fg)" stroke-width="1.5" stroke-dasharray="4 3"' : '';
    s += '<rect x="' + (x + 1) + '" y="' + mt + '" width="' + (C - 3) + '" height="' + (C - 3) + '" fill="' + rgb(c) + '"' + edge +
      '><title>' + esc(tip) + '</title></rect>';
    s += '<text class="cellv" x="' + (x + C / 2) + '" y="' + (mt + C / 2 + 3) + '" text-anchor="middle" style="font-size:15px;fill:' +
      textOn(c) + '">' + esc(t.passed || 0) + '/' + esc(k) + '</text>';
    if (t.cap === 'late' || t.cap === 'violated')
      s += '<path d="M' + (x + C / 2) + ',' + (mt - 11) + 'l6,9h-12z" fill="' + (t.cap === 'violated' ? '#d55e00' : '#e69f00') +
        '"><title>cap ' + esc(t.cap) + '</title></path>';
    s += '<text class="ax" x="' + (x + C / 2) + '" y="' + (mt + C + 12) + '" text-anchor="middle">' + esc(t.d) + '</text>';
  });
  s += '<text class="axt" x="' + ml + '" y="' + (mt + C + 34) + '">prime size d (digits); solid outline = frontier, dashed = first failure; ▲ = cap late/violated</text>';
  return s + '</svg>';
}

// ---------- frontier comparison chart ----------
const LEVEL_DASH = { max: '', high: '9 4', medium: '5 4', low: '2 4', minimal: '1 4', none: '1 4' };
// one series per run frontier, plus any sub-entry (e.g. an early version) that itself has a `tested` array
// a run whose program never ran (every size skipped)
const noProg = se => se.f.tested.length > 0 && se.f.tested.every(t => t.cap === 'skipped');
const frDefaultOn = se => !noProg(se);
// frOff lists series toggled AWAY from their default (no-program runs default off, others on)
const frIsOn = se => frDefaultOn(se) !== frOff.includes(se.id);
function frontierSeries() {
  const out = [];
  const rs = RUNS.filter(r => r.frontier && Array.isArray(r.frontier.tested));
  rs.forEach(r => {
    const dup = rs.filter(x => x.model === r.model && x.arm === r.arm).length > 1;
    const base = r.model_short + '/' + r.arm + (dup ? '/' + r.source : '');
    const label = r.model + ' · ' + r.arm + (dup ? ' · ' + r.source : '');
    out.push({ id: base, label, run: r, f: r.frontier, sub: null });
    const subs = [];
    Object.keys(r.frontier).forEach(key => {
      const v = r.frontier[key];
      if (v && typeof v === 'object' && !Array.isArray(v) && Array.isArray(v.tested)) subs.push([key, v]);
      if (Array.isArray(v) && key !== 'tested' && key !== 'points')
        v.forEach((x, i) => { if (x && Array.isArray(x.tested)) subs.push([key + '-' + (x.version || x.name || i), x]); });
    });
    Object.keys(r).forEach(key => { // run-level siblings such as frontier_early
      const v = r[key];
      if (key !== 'frontier' && /^frontier/.test(key) && v && typeof v === 'object' && Array.isArray(v.tested)) subs.push([key, v]);
    });
    subs.forEach(([key, v]) => out.push({ id: base + '/' + key, label: label + ' (' + key + ')', run: r,
      f: Object.assign({ k: r.frontier.k, time_limit: r.frontier.time_limit }, v), sub: key }));
  });
  return out;
}
function seriesStyle(se) {
  const so = se.run.solution; // SOTA runs: one color per model, dash per condition (M solid, R dashed, L dotted)
  const dash = se.sub ? '1 4' : so ? ({ M: '', R: '9 4', L: '2 4' }[so.cond] || '') :
    (LEVEL_DASH[se.run.level] != null ? LEVEL_DASH[se.run.level] : '7 3 1 3');
  return { color: modelColor(se.run.model), dash, width: se.sub ? 2 : 3, opacity: se.sub ? 0.6 : 1 };
}
// time to factor one pair at size d: median solve time if recorded, else wall / k; null when skipped/unknown
function ptTime(t, se, metric) {
  if (t.cap === 'skipped') return null;
  const k = t.k || se.f.k || 1;
  if (isCrash(t, k)) return null; // crashed instantly: its ~0 time says nothing about speed
  const v = t.median_solve_s != null ? t.median_solve_s : (t.wall != null ? t.wall / k : null);
  if (v == null) return null;
  if (metric === 'coding') return (t.passed || 0) > 0 && codeSec(se.run) ? codeSec(se.run) : null; // flat: the run's coding time
  return Math.max(DUR_FLOOR, metric === 'codetime' ? v + codeSec(se.run) : v);
}
function renderFrontier() {
  const series = frontierSeries();
  ['frontier', 'frnote', 'frmwrap', 'frlegend', 'frcharts', 'frtable'].forEach(id => { document.getElementById(id).hidden = !series.length; });
  if (!series.length) return;
  const isOn = frIsOn;
  const lg = document.getElementById('frlegend');
  const ae = document.activeElement, fv = ae && lg.contains(ae) ? ae.value : null;
  const chip = se => {
    const st = seriesStyle(se), np = noProg(se);
    return '<label class="chip frchip' + (isOn(se) ? '' : ' off') + (np ? ' noprog' : '') + '"><input type="checkbox" value="' + esc(se.id) + '"' +
      (isOn(se) ? ' checked' : '') + '><svg viewBox="0 0 34 14"><line x1="2" y1="7" x2="32" y2="7" stroke="' + st.color +
      '" stroke-width="3" stroke-dasharray="' + st.dash + '" opacity="' + st.opacity + '"/>' +
      shapePath(shapeOf(se.run.mode), 17, 7, 4.5) + ' fill="' + st.color + '"/></svg>' + esc(se.label) +
      (np ? ' — <em>no program</em>' : '') +
      '</label>';
  };
  lg.innerHTML = '<span class="lbl">Show</span><button type="button" data-frq="all">all</button>' +
    series.filter(se => frRefs || !isRefs(se)).map(chip).join('');
  if (fv != null) { const i = [...lg.querySelectorAll('input')].find(x => x.value === fv); if (i) i.focus({ preventScroll: true }); }

  const shown = series.filter(se => isOn(se) && (frRefs || !isRefs(se)));
  const ffb = document.getElementById('frfine'); if (ffb) ffb.checked = frFine;
  const frb = document.getElementById('frrefs'); if (frb) frb.checked = frRefs;
  const fab = document.getElementById('franchor'); if (fab) fab.checked = frAnchorTest;
  // three charts, one per metric; each draws into fr-<metric> with its caption in frtitle-<metric>
  for (const m of FR_METRICS) { frMetric = m; if (frId('fr')) drawFrChart(series, shown); }
  renderFrTable(series, isOn);
  renderEpisodes(shown);
}
// charts drawn = those whose fr-<metric> container exists on the page
const isRefs = se => !!(se.run.solution && se.run.solution.cond === 'R');
const FR_METRICS = ['timeline', 'time', 'evals', 'coding'];
// with the fine frontier off, only fully factored sizes are drawn (partial sizes belong to the fine search)
const frKeep = (t, se) => frFine || (t.cap !== 'skipped' && (t.passed || 0) >= (t.k || se.f.k || 1));
const frId = id => document.getElementById(id + '-' + frMetric);
function drawFrChart(series, shown) {
  const timeView = frMetric !== 'evals';
  if (frMetric === 'timeline') {
    frId('frtitle').textContent = 'Minutes from the start of each session (the budget was 60). Each reach step starts when the ' +
      (frAnchorTest ? 'model first tested that size (tick off “anchor to tests” to start it at the code edit that earned it). ' :
        'code that earned it was written: the last code edit before the test that showed it. ') + 'Reach = the largest d (digits per ' +
      'prime) the model’s program factored within 60 s in its own tests by that minute, read from the session logs; these ' +
      'tests are one or two numbers, so reach can sit 1–2 digits above the graded 16/16 frontier.';
    frId('fr').innerHTML = timelineChart(shown.filter(se => !se.sub && se.run.solution && se.run.solution.timeline));
    return;
  }
  if (frMetric === 'coding') { // scatter: one point per program, coding time vs code length
    frId('frtitle').textContent = 'x = time the model spent writing the program, y = lines of its own code ' +
      '(vendored crates not counted). Label = condition and fine frontier (digits per prime).';
    frId('fr').innerHTML = codingScatter(shown.filter(se => !se.sub && se.run.solution));
    return;
  }
  const allD = uniq([].concat(...series.map(se => (frFine ? se.f.points || [] : []).concat(se.f.tested.filter(t => frKeep(t, se)).map(t => t.d)))))
    .filter(d => d > 0).sort((a, b) => a - b);
  // keep fine-frontier marks inside the x range (they don't get grid lines/labels of their own)
  const fineDs = series.map(se => frFine && !se.sub && fineOf(se.run) ? fineOf(se.run).fine_frontier : null).filter(d => d > 0);
  const xMin = Math.min(allD[0] || 1, ...fineDs), xMax = Math.max(allD[allD.length - 1] || 2, ...fineDs);
  const W = 960, H = 440, ml = 96, mr = 24, mt = 30, mb = 58;
  const lo = Math.log2(xMin), hi = Math.max(lo + 1, Math.log2(xMax));
  const xs = d => ml + (Math.log2(d) - lo) / (hi - lo) * (W - ml - mr);
  // y value per point (null = not plotted, e.g. skipped sizes in the time views)
  const yval = (t, se) => timeView ? ptTime(t, se, frMetric) : (t.cap === 'skipped' ? 0 : (t.passed || 0));
  let yticks, ylab, ys, capLines = [];
  if (!timeView) { // # evals: pairs factored at that size, linear 0..k
    const kmax = Math.max(1, ...shown.concat(series).map(se => se.f.k || 0), ...[].concat(...shown.map(se => se.f.tested.map(t => t.k || 0))));
    const step = kmax % 4 === 0 ? kmax / 4 : Math.max(1, Math.ceil(kmax / 4));
    ys = a => mt + (1 - a / kmax) * (H - mt - mb);
    yticks = []; for (let v = 0; v <= kmax; v += step) yticks.push(v);
    if (yticks[yticks.length - 1] !== kmax) yticks.push(kmax);
    ylab = a => String(a);
  } else {
    // y range = the global time domain (same as the grid colors), not this chart's own data
    const capS = uniq(shown.map(se => se.f.time_limit).filter(x => x > 0));
    let ylo = DOMAIN.T[0], yhi = Math.max(DOMAIN.T[1], ...capS);
    const NICE = [[1e-6, '1 µs'], [1e-5, '10 µs'], [1e-4, '100 µs'], [1e-3, '1 ms'], [1e-2, '10 ms'], [0.1, '100 ms'], [1, '1 s'], [10, '10 s'], [60, '1 min'],
      [600, '10 min'], [3600, '1 h'], [36000, '10 h'], [360000, '100 h']];
    ylo = (NICE.filter(n => n[0] <= ylo).pop() || NICE[0])[0];
    yhi = (NICE.find(n => n[0] >= yhi) || NICE[NICE.length - 1])[0];
    if (yhi <= ylo) yhi = ylo * 10;
    ys = v => mt + (1 - (Math.log10(v) - Math.log10(ylo)) / (Math.log10(yhi) - Math.log10(ylo))) * (H - mt - mb);
    yticks = NICE.filter(n => n[0] >= ylo && n[0] <= yhi).map(n => n[0]);
    ylab = v => (NICE.find(n => n[0] === v) || [0, fmtDur(v)])[1];
    capLines = capS.map(c => [c, ys(c)]);
  }
  const yName = !timeView ? '# evals (pairs factored)' : frMetric === 'time' ? 'answer time per pair (log)' :
    'coding time (log)';
  frId('frtitle').textContent = 'y = ' + (!timeView ? 'number of pairs factored at that size' : frMetric === 'time'
    ? 'answer time for one pair (median solve time, else wall ÷ k)' : 'time the model spent writing the program, drawn at every size it factored') +
    (frMetric === 'coding' ? '. Each line ends at the largest size its program factored.' :
    timeView ? '. Hollow = some pairs failed or timed out, so the time is a lower bound. Skipped sizes and instant crashes ' +
      '(0 passed, ~0 s) are not plotted.' : '. Hollow = size skipped (counted as 0).');
  let s = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="' + esc(yName + ' by prime size for each factoring run') + '">';
  s += '<g class="grid">';
  yticks.forEach(a => s += '<line x1="' + ml + '" x2="' + (W - mr) + '" y1="' + ys(a) + '" y2="' + ys(a) + '"/>');
  allD.forEach(d => s += '<line x1="' + xs(d) + '" x2="' + xs(d) + '" y1="' + mt + '" y2="' + (H - mb) + '" stroke-dasharray="2 4"/>');
  s += '</g>';
  yticks.forEach(a => s += '<text class="ax" style="font-size:15px" x="' + (ml - 8) + '" y="' + (ys(a) + 5) +
    '" text-anchor="end">' + ylab(a) + '</text>');
  if (timeView && frMetric === 'time') capLines.forEach(([c, y]) => {
    s += '<line x1="' + ml + '" x2="' + (W - mr) + '" y1="' + y + '" y2="' + y + '" stroke="#e66101" stroke-dasharray="6 4"/>';
    s += '<text class="ax" x="' + (W - mr - 4) + '" y="' + (y - 5) + '" text-anchor="end" style="fill:#e66101;font-size:14px">' +
      'cap ' + esc(fmtDur(c)) + ' per pair</text>';
  });
  let lastX = -1e9;
  allD.forEach(d => { // skip labels that would collide
    const x = xs(d); if (x - lastX < 26) return; lastX = x;
    s += '<text class="ax" style="font-size:15px" x="' + x + '" y="' + (H - mb + 22) + '" text-anchor="middle">' + d + '</text>';
  });
  s += '<text class="axt" style="font-size:16px" x="' + (ml + (W - ml - mr) / 2) + '" y="' + (H - 10) +
    '" text-anchor="middle">prime size d = digits of p and of q (log₂ scale)</text>';
  // y title, with the "better" direction as a muted second line right next to it (one line would not fit)
  s += '<text class="axt" style="font-size:16px" transform="translate(15,' + (mt + (H - mt - mb) / 2) +
    ') rotate(-90)" text-anchor="middle">' + esc(yName) + '</text>';
  s += axisBetter(27, mt + (H - mt - mb) / 2, !timeView, timeView ? 'lower is better (faster)' : 'higher is better');
  if (!shown.length) s += '<text class="axt" style="font-size:18px" x="' + (ml + (W - ml - mr) / 2) + '" y="' + (mt + 40) +
    '" text-anchor="middle">All runs are switched off. Tick one above.</text>';
  shown.forEach(se => {
    const st = seriesStyle(se), si = series.indexOf(se);
    const ts = se.f.tested.filter(t => t.d > 0).slice().sort((a, b) => a.d - b.d)
      .filter(t => { const v = yval(t, se); return frKeep(t, se) && v != null && (!timeView || v > 0); });
    if (!ts.length) return;
    s += '<g opacity="' + st.opacity + '">';
    s += '<path d="' + ts.map((t, j) => (j ? 'L' : 'M') + xs(t.d).toFixed(1) + ',' + ys(yval(t, se)).toFixed(1)).join('') +
      '" fill="none" stroke="' + st.color + '" stroke-width="' + st.width + '" stroke-dasharray="' + st.dash + '" stroke-linejoin="round"/>';
    ts.forEach(t => {
      const x = xs(t.d), y = ys(yval(t, se)), j = se.f.tested.indexOf(t), sk = t.cap === 'skipped';
      const k = t.k || se.f.k, hollow = timeView ? (t.passed || 0) < k : sk;
      s += '<g class="frpt" data-s="' + si + '" data-j="' + j + '" tabindex="0" aria-label="' + esc(se.label + ', d=' + t.d + ': ' +
        (sk ? 'skipped' : (t.passed || 0) + '/' + k) + (timeView ? ', ' + fmtDur(yval(t, se)) : '') + ', cap ' + (t.cap || '–')) + '">';
      s += '<circle cx="' + x + '" cy="' + y + '" r="11" fill="transparent"/>';
      s += shapePath(shapeOf(se.run.mode), x, y, 6) + ' fill="' + (hollow ? 'var(--bg)' : st.color) + '" stroke="' + st.color + '" stroke-width="2"/>';
      if (t.cap === 'late' || t.cap === 'violated')
        s += '<path d="M' + x + ',' + (y - 20) + 'l6,10h-12z" fill="' + (t.cap === 'violated' ? '#d55e00' : '#e69f00') +
          '" stroke="var(--bg)" stroke-width="1"/>';
      s += '</g>';
    });
    // fine frontier: hollow diamond on the line at x = fine_frontier (y interpolated along the drawn line)
    const fine = frFine && !se.sub && fineOf(se.run);
    if (fine && ts.length) {
      const fx = xs(fine.fine_frontier), pts = ts.map(t => [xs(t.d), ys(yval(t, se))]);
      let fy = pts[0][1];
      if (fx >= pts[pts.length - 1][0]) fy = pts[pts.length - 1][1];
      else for (let j = 1; j < pts.length; j++) if (fx <= pts[j][0]) {
        const [x0, y0] = pts[j - 1], [x1, y1] = pts[j];
        fy = x1 === x0 ? y1 : y0 + (y1 - y0) * (fx - x0) / (x1 - x0); break;
      }
      s += '<g class="finemark"><title>' + esc(se.label + ': fine frontier ' + fmtFine(fine)) + '</title>' +
        '<line x1="' + fx + '" x2="' + fx + '" y1="' + (fy - 16) + '" y2="' + (fy + 16) + '" stroke="' + st.color + '" stroke-width="2"/>' +
        shapePath('diamond', fx, fy, 7) + ' fill="var(--bg)" stroke="' + st.color + '" stroke-width="2.5"/></g>';
    }
    s += '</g>';
  });
  if (frFine && series.some(se => !se.sub && fineOf(se.run)))
    s += '<text class="ax" x="' + (W - mr) + '" y="' + (mt - 10) + '" text-anchor="end" style="font-size:14px">◇ = fine frontier (shared cap)</text>';
  frId('fr').innerHTML = s + '</svg>';
}
const COND_WORDS = { M: 'memory only', R: 'web references', L: 'anything goes' };
// reach steps anchored to when the winning code was written (default) or to when it was first tested
const stepsOf = tl => (frAnchorTest ? tl.reach : tl.reach_code || tl.reach) || [];
function episodesOf(tl) {
  const steps = stepsOf(tl), test = tl.reach || [], code = tl.reach_code || [], info = tl.episodes || [];
  const eps = [{ from: 0, to: steps.length ? steps[0][0] : tl.stopped, d: null }]
    .concat(steps.map(([m, d], k) => ({ from: m, to: k + 1 < steps.length ? steps[k + 1][0] : tl.stopped, d,
      code: code[k] ? code[k][0] : null, test: test[k] ? test[k][0] : null })));
  eps.forEach((e, k) => Object.assign(e, info[k] ? { solution: info[k].solution, measured: info[k].measured } : {}));
  return eps;
}
function episodeTip(se, e) {
  return '<strong>' + esc(se.run.model + ' · ' + (COND_WORDS[se.run.solution.cond] || '')) + '</strong><br>minutes ' + e.from + '–' + e.to +
    ' · ' + (e.d == null ? 'writing' : 'reach d = ' + e.d) +
    (e.d != null && e.code != null ? '<br>code written at ' + e.code + ' min · first tested at ' + e.test + ' min' : '') + (e.solution ? '<br>' + esc(e.solution) : '') +
    (e.measured ? '<br><em>' + esc(e.measured) + '</em>' : '');
}
// one bar per run on a 60-minute axis: grey until the first measured result, then one segment per reach level
// (largest d its program factored within 60 s, by the model's own tests), shaded darker for more digits
function timelineChart(ss) {
  const ROW = 34, W = 960, ml = 250, mr = 24, mt = 30, mb = 96, H = mt + mb + ROW * ss.length;
  const xs = v => ml + v / 60 * (W - ml - mr);
  const shade = d => Math.max(0.12, Math.min(1, 0.12 + 0.88 * (d - 30) / 12)); // d <= 30 lightest, 42 full
  let s = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="how each SOTA session spent its hour, by reach over time">';
  for (let v = 0; v <= 60; v += 10) s += '<line x1="' + xs(v) + '" x2="' + xs(v) + '" y1="' + mt + '" y2="' + (H - mb) + '" stroke="var(--rule)"/>' +
    '<text class="ax" x="' + xs(v) + '" y="' + (H - mb + 18) + '" text-anchor="middle">' + v + ' min</text>';
  ss.forEach((se, i) => {
    const tl = se.run.solution.timeline, c = seriesStyle(se).color, y = mt + i * ROW + 6, h = ROW - 12;
    const steps = stepsOf(tl);
    s += '<text class="ax" x="' + (ml - 10) + '" y="' + (y + h / 2 + 5) + '" text-anchor="end" style="font-size:15px">' +
      esc(se.run.model.replace('claude-', '').replace(/-5-5$/, ' 5.5') + ' · ' + (COND_WORDS[se.run.solution.cond] || '')) + '</text>';
    const first = steps.length ? steps[0][0] : tl.stopped;
    s += '<rect class="tlseg" data-s="' + esc(se.id) + '" data-k="0" x="' + xs(0) + '" y="' + y + '" width="' + (xs(first) - xs(0)) + '" height="' + h + '" fill="var(--fg)" fill-opacity="0.12"></rect>';
    steps.forEach(([m, d], k) => {
      const m1 = k + 1 < steps.length ? steps[k + 1][0] : tl.stopped, w = xs(m1) - xs(m);
      s += '<rect class="tlseg" data-s="' + esc(se.id) + '" data-k="' + (k + 1) + '" x="' + xs(m) + '" y="' + y + '" width="' + Math.max(0, w) + '" height="' + h + '" fill="' + c + '" fill-opacity="' + shade(d) + '"></rect>';
      if (w >= 22) s += '<text x="' + (xs(m) + w / 2) + '" y="' + (y + h / 2 + 5) + '" text-anchor="middle" style="font-size:13px;fill:' +
        (shade(d) > 0.55 ? '#fff' : 'var(--fg)') + ';pointer-events:none">' + d + '</text>';
    });
    s += '<line x1="' + xs(tl.last_edit) + '" x2="' + xs(tl.last_edit) + '" y1="' + (y - 3) + '" y2="' + (y + h + 3) + '" stroke="var(--fg)" stroke-width="2.5">' +
      '<title>' + esc(se.label + ': last code change at ' + tl.last_edit + ' min') + '</title></line>';
    s += '<rect x="' + xs(tl.stopped) + '" y="' + y + '" width="' + (xs(60) - xs(tl.stopped)) + '" height="' + h +
      '" fill="none" stroke="var(--rule)" stroke-dasharray="4 3"><title>' + esc(se.label + ': unused, ' + (60 - tl.stopped).toFixed(0) + ' min') + '</title></rect>' +
      '<text class="ax" x="' + (xs(tl.stopped) + 6) + '" y="' + (y + h / 2 + 5) + '" style="font-size:13px">' + (60 - tl.stopped).toFixed(0) + ' min unused</text>';
  });
  const LEG = [['<rect width="16" height="12" fill="var(--fg)" fill-opacity="0.12"/>', frAnchorTest ? 'writing, before the first measured result' : 'writing, before the first working code'],
    ['<rect width="16" height="12" fill="var(--fg)" fill-opacity="0.6"/>', 'reach d (label): darker = more digits'],
    ['<line x1="8" x2="8" y1="-2" y2="14" stroke="var(--fg)" stroke-width="2.5"/>', 'last code change'],
    ['<rect width="16" height="12" fill="none" stroke="var(--rule)" stroke-dasharray="4 3"/>', 'unused budget']];
  LEG.forEach(([icon, what], j) => {
    const lx = ml + (j % 2) * (W - ml - mr) / 2, ly = H - 38 + Math.floor(j / 2) * 22;
    s += '<g transform="translate(' + lx + ',' + (ly - 10) + ')">' + icon + '</g>' +
      '<text class="ax" x="' + (lx + 22) + '" y="' + ly + '" style="font-size:13px">' + esc(what) + '</text>';
  });
  return s + '</svg>';
}
function codingScatter(ss) {
  const W = 960, H = 440, ml = 96, mr = 24, mt = 30, mb = 58;
  const tx = se => se.run.solution.dev_seconds / 60, ty = se => se.run.solution.lines;
  const xhi = Math.max(60, ...ss.map(tx)), yhi = Math.ceil(Math.max(500, ...ss.map(ty)) / 500) * 500;
  const xs = v => ml + v / xhi * (W - ml - mr), ys = v => mt + (1 - v / yhi) * (H - mt - mb);
  let s = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="coding time vs code length for each SOTA program">';
  for (let v = 0; v <= xhi; v += 10) s += '<line x1="' + xs(v) + '" x2="' + xs(v) + '" y1="' + mt + '" y2="' + (H - mb) + '" stroke="var(--rule)"/>' +
    '<text class="ax" x="' + xs(v) + '" y="' + (H - mb + 18) + '" text-anchor="middle">' + v + ' min</text>';
  for (let v = 0; v <= yhi; v += 500) s += '<line x1="' + ml + '" x2="' + (W - mr) + '" y1="' + ys(v) + '" y2="' + ys(v) + '" stroke="var(--rule)"/>' +
    '<text class="ax" x="' + (ml - 6) + '" y="' + (ys(v) + 4) + '" text-anchor="end">' + fmtInt(v) + '</text>';
  s += '<text class="axt" x="' + ((ml + W - mr) / 2) + '" y="' + (H - 12) + '" text-anchor="middle">coding time (min)</text>' +
    '<text class="axt" transform="translate(22,' + ((mt + H - mb) / 2) + ') rotate(-90)" text-anchor="middle">code length (lines)</text>';
  ss.forEach(se => {
    const st = seriesStyle(se), so = se.run.solution, ff = fineOf(se.run), x = xs(tx(se)), y = ys(ty(se));
    s += '<g><title>' + esc(se.label + ': ' + fmtDur(so.dev_seconds) + ' coding, ' + fmtInt(so.lines) + ' lines' +
      (ff ? ', fine frontier ' + ff.fine_frontier : '')) + '</title>' + shapePath(shapeOf(se.run.mode), x, y, 9) + ' fill="' + st.color + '"/>' +
      '<text class="ax" x="' + (x + 12) + '" y="' + (y + 5) + '" style="font-size:15px">' + esc(({ M: 'memory only', R: 'web references', L: 'anything goes' }[so.cond] || so.cond) + (ff ? ' · ' + ff.fine_frontier : '')) + '</text></g>';
  });
  return s + '</svg>';
}
function renderEpisodes(shown) {
  const el = document.getElementById('eptable'); if (!el) return;
  const rows = [];
  shown.filter(se => !se.sub && se.run.solution && se.run.solution.timeline).forEach(se => episodesOf(se.run.solution.timeline).forEach(e =>
    rows.push('<tr><td>' + esc(COND[se.run.solution.cond] || '') + '</td><td><span style="color:' + seriesStyle(se).color + '">■</span> ' +
      esc(se.run.model + ' · ' + se.run.level) + '</td><td class="num">' + (e.d == null ? '0–' + e.to : e.code + ' / ' + e.test) + ' min</td><td class="num">' +
      (e.d == null ? '<em>writing</em>' : '<strong>' + e.d + '</strong>') + '</td><td>' + esc(e.solution || '–') + '</td><td>' + esc(e.measured || '') + '</td></tr>')));
  el.innerHTML = rows.length ? '<table><thead><tr><th>condition</th><th>model · effort</th><th class="num">code written / first tested</th><th class="num">reach d</th>' +
    '<th>solution at this point</th><th>measured</th></tr></thead><tbody>' + rows.join('') + '</tbody></table>' : '';
}
function renderFrTable(series, isOn) {
  document.getElementById('frtable').innerHTML = '<table><thead><tr><th>run</th><th>frontier d</th><th>first failure d</th>' +
    '<th>sizes run</th><th>fine</th></tr></thead><tbody>' + series.map(se => '<tr class="' + (isOn(se) ? '' : 'off') + '"><td>' +
      '<span style="color:' + seriesStyle(se).color + '">■</span> ' + esc(se.label) + '</td><td>' +
      (noProg(se) ? '<em>no program</em>' : esc(se.f.frontier_digits != null ? se.f.frontier_digits : '–')) + '</td><td>' +
      esc(se.f.first_failure_digits != null ? se.f.first_failure_digits : 'none') + '</td><td>' +
      se.f.tested.filter(t => t.cap !== 'skipped').length + '/' + (se.f.points || se.f.tested).length + '</td><td>' +
      (!se.sub && fineOf(se.run) ? esc(fineCell(fineOf(se.run))) : '–') +
      '</td></tr>').join('') +
    '</tbody></table>';
}
function showFrTip(g, evt) {
  const se = frontierSeries()[+g.dataset.s]; if (!se) return;
  const t = se.f.tested[+g.dataset.j]; if (!t) return;
  const wrap = g.closest('.frwrap'), tip = wrap.querySelector('.frtip');
  const k = t.k || se.f.k;
  tip.innerHTML = '<strong>' + esc(se.label) + '</strong><br>d = ' + esc(t.d) + ' digits<br>' +
    (t.cap === 'skipped' ? 'skipped (previous size 0/' + esc(k) + ') → counted 0/' + esc(k)
      : esc(t.passed || 0) + '/' + esc(k) + ' passed') + '<br>cap: ' + esc(t.cap || '–') +
    (t.t_given_min != null ? ' · time limit ≥ ' + esc(fmtDur(t.t_given_min)) : '') +
    (isCrash(t, k) ? '<br><strong>crashed instantly</strong> (0 passed, ~0 s): no time plotted' : '') +
    (t.wall != null ? '<br>wall ' + esc(fmtDur(t.wall)) + ' for the size' : '') + (t.timeouts != null ? ' · timeouts ' + esc(t.timeouts) : '') +
    (t.median_solve_s != null ? '<br>median solve ' + esc(fmtDur(t.median_solve_s)) : '') +
    (t.max_solve_s != null ? ' · max ' + esc(fmtDur(t.max_solve_s)) : '') +
    (t.cap !== 'skipped' && !isCrash(t, k) ? '<br>answer time ' + esc(fmtDur(ptTime(t, se, 'time'))) + '/pair' +
      ((t.passed || 0) < k ? ' (lower bound: failures)' : '') : '') +
    (codeSec(se.run) ? '<br>coding time ' + esc(fmtDur(codeSec(se.run))) : '');
  tip.style.display = 'block';
  const wb = wrap.getBoundingClientRect();
  let px, py;
  if (evt && evt.clientX != null) { px = evt.clientX - wb.left; py = evt.clientY - wb.top; }
  else { const b = g.getBoundingClientRect(); px = b.right - wb.left; py = b.top - wb.top; }
  const tw = tip.offsetWidth, th = tip.offsetHeight;
  let left = px + 14, top = py - th - 10;
  if (left + tw > wb.width) left = px - tw - 14;
  left = Math.max(0, Math.min(left, wb.width - tw));
  if (top < 0) top = py + 16;
  tip.style.left = left + 'px'; tip.style.top = top + 'px';
}
const hideFrTip = () => { document.querySelectorAll('.frtip').forEach(t => { t.style.display = 'none'; }); };

function renderTask() { // the overview's own task selector
  const sel = document.getElementById('ovtask');
  const ts = tasks(), cur = effTask();
  sel.innerHTML = '';
  const all = ts.includes(cur) ? ts : [cur].concat(ts);
  all.forEach(v => {
    const o = document.createElement('option'); o.value = v;
    o.textContent = (ts.includes(v) ? tl(v) : tl(v) + ' — no data') + (!ovTask && v === cur ? ' (as panel 1)' : '');
    if (v === cur) o.selected = true; sel.appendChild(o);
  });
}

// fallback for layouts where subgrid doesn't apply: equalize the controls and header rows of panels sharing a visual row
function equalizePanels() {
  const ps = [...document.querySelectorAll('#panels .panel')];
  ps.forEach(p => p.querySelectorAll('.prow-ctrl,.prow-head').forEach(x => { x.style.minHeight = ''; }));
  const rows = new Map();
  ps.forEach(p => { const k = Math.round(p.getBoundingClientRect().top + window.scrollY); if (!rows.has(k)) rows.set(k, []); rows.get(k).push(p); });
  rows.forEach(group => {
    if (group.length < 2) return;
    ['.prow-ctrl', '.prow-head'].forEach(sel => {
      const h = Math.max(...group.map(p => p.querySelector(sel).getBoundingClientRect().height));
      group.forEach(p => { p.querySelector(sel).style.minHeight = h + 'px'; });
    });
  });
}
let eqT = null;
window.addEventListener('resize', () => { clearTimeout(eqT); eqT = setTimeout(equalizePanels, 100); });
function renderPanels() {
  propagate();
  const box = document.getElementById('panels');
  const ae = document.activeElement;
  let focus = null;
  if (ae && box.contains(ae)) {
    const pe = ae.closest('.panel');
    focus = { id: pe && pe.dataset.id, field: ae.dataset.field, act: ae.dataset.act };
  }
  box.style.minHeight = box.offsetHeight + 'px'; // avoid a height collapse (and scroll jump) while rebuilding
  box.innerHTML = '';
  if (!panels.length) {
    const e = document.createElement('div');
    e.className = 'empty';
    e.textContent = RUNS.length ? 'No charts. Use “+ Add chart”.' : 'No runs in summary-data.js yet.';
    box.appendChild(e);
  }
  panels.forEach((p, i) => box.appendChild(renderPanel(p, i)));
  equalizePanels();
  box.style.minHeight = '';
  if (focus && focus.id) {
    const pe = box.querySelector('.panel[data-id="' + focus.id + '"]');
    const t = pe && (focus.field ? pe.querySelector('select[data-field="' + focus.field + '"]')
      : pe.querySelector('[data-act="' + focus.act + '"]'));
    if (t) t.focus({ preventScroll: true });
  }
}

// ---------- overview scatter ----------
function shapePath(shape, x, y, r) {
  switch (shape) {
    case 'square': return '<rect x="' + (x - r * 0.88) + '" y="' + (y - r * 0.88) + '" width="' + r * 1.76 + '" height="' + r * 1.76 + '"';
    case 'triangle': return '<path d="M' + x + ',' + (y - r * 1.15) + 'L' + (x + r * 1.05) + ',' + (y + r * 0.75) + 'L' + (x - r * 1.05) + ',' + (y + r * 0.75) + 'Z"';
    case 'tridown': return '<path d="M' + x + ',' + (y + r * 1.15) + 'L' + (x + r * 1.05) + ',' + (y - r * 0.75) + 'L' + (x - r * 1.05) + ',' + (y - r * 0.75) + 'Z"';
    case 'diamond': return '<path d="M' + x + ',' + (y - r * 1.2) + 'L' + (x + r * 1.2) + ',' + y + 'L' + x + ',' + (y + r * 1.2) + 'L' + (x - r * 1.2) + ',' + y + 'Z"';
    default: return '<circle cx="' + x + '" cy="' + y + '" r="' + r + '"';
  }
}
function shapeIcon(shape, color) {
  return '<svg width="18" height="18" viewBox="0 0 18 18" style="width:18px;display:inline">' +
    shapePath(shape, 9, 9, 6.5) + ' fill="' + color + '"/></svg>';
}
const TIME_TICKS = [[1, '1 s'], [10, '10 s'], [60, '1 min'], [600, '10 min'], [3600, '1 h'], [36000, '10 h'],
  [360000, '100 h']];
const SUBTICKS = [0.1, 0.3, 1, 3, 10, 30, 100, 300, 1000, 3000, 1e4, 3e4, 1e5, 3e5, 1e6];

function renderOverview() {
  const task = effTask();
  renderTask();
  const taskRuns = RUNS.filter(r => r.task === task);
  const present = sortOpts('mode', uniq(taskRuns.map(r => r.mode)), taskRuns);
  renderModeChips(present);
  const on = m => !ovModes || ovModes.includes(m);
  const shownModes = present.filter(on);
  const canFrontier = task === 'factor' || taskRuns.some(r => r.frontier);
  const yMode = canFrontier && ovY === 'frontier' ? 'frontier' : 'acc';
  document.getElementById('ovywrap').hidden = !canFrontier;
  document.getElementById('ovy').value = yMode;
  document.getElementById('ovtitle').textContent = 'Overview: ' + (yMode === 'frontier' ? 'frontier digits' : 'accuracy') +
    ' vs time to completion — ' + tl(task || '') + ' · ' +
    (shownModes.length === present.length ? 'all modes' : shownModes.length ? shownModes.join(', ') : 'no modes');
  const inModes = taskRuns.filter(r => on(r.mode));
  const all = yMode === 'frontier' ? inModes.filter(r => r.frontier) : inModes;
  const rs = all.filter(r => r.seconds > 0);
  const yv = r => yMode === 'frontier' ? (r.frontier.frontier_digits || 0) : scoreOf(r);
  document.getElementById('ovynote').textContent = yMode === 'frontier' && inModes.length > all.length
    ? (inModes.length - all.length) + ' run(s) without a frontier search are hidden in this view' : '';
  const shown = new Map();
  panels.forEach((p, i) => { const r = runOf(p); if (r) { if (!shown.has(r._i)) shown.set(r._i, []); shown.get(r._i).push(i + 1); } });

  const lg = document.getElementById('ovlegend');
  const ms = uniq(rs.map(r => r.model)), mds = sortOpts('mode', uniq(rs.map(r => r.mode)), rs);
  lg.innerHTML = ms.map(m => '<span>' + shapeIcon('circle', modelColor(m)) + esc(m) + '</span>').join('') +
    (mds.length ? '<span style="color:var(--muted)">·</span>' : '') +
    mds.map(m => '<span>' + shapeIcon(shapeOf(m), 'var(--muted)') + esc(m) + '</span>').join('') +
    (all.length > rs.length ? '<span class="note">' + (all.length - rs.length) + ' run(s) without a time are not plotted</span>' : '') +
    (rs.some(r => r.status === 'in_progress') ? '<span class="note">hollow = still running</span>' : '') +
    (yMode !== 'frontier' && rs.some(isGraded) ? '<span class="note">graded runs plot factored / total, not the benchmark</span>' : '');

  const box = document.getElementById('ov');
  if (!rs.length) {
    box.innerHTML = '<div class="empty">' + (yMode === 'frontier' && inModes.length && !all.length
      ? 'No run in the selected modes has a frontier search.'
      : taskRuns.length && !inModes.length ? 'No mode selected. Tick one above.'
      : 'No timed runs for task “' + esc(tl(task)) + '” in the selected modes.') + '</div>';
    return;
  }
  const W = 960, H = 460, ml = 84, mr = 24, mt = 24, mb = 56;
  let lo = Math.min(...rs.map(r => r.seconds)), hi = Math.max(...rs.map(r => r.seconds));
  lo = Math.pow(10, Math.floor(Math.log10(lo) - 0.05));
  hi = Math.pow(10, Math.ceil(Math.log10(hi) + 0.05));
  const xs = v => ml + (Math.log10(v) - Math.log10(lo)) / (Math.log10(hi) - Math.log10(lo)) * (W - ml - mr);
  let ymax = 1, yticks = [0, 0.2, 0.4, 0.6, 0.8, 1], ylab = a => Math.round(a * 100) + '%';
  if (yMode === 'frontier') {
    const top = Math.max(4, ...all.map(r => Math.max(r.frontier.frontier_digits || 0, r.frontier.first_failure_digits || 0)));
    const step = top <= 10 ? 1 : top <= 24 ? 2 : 5;
    ymax = Math.ceil(top / step) * step;
    yticks = []; for (let v = 0; v <= ymax; v += step) yticks.push(v);
    ylab = v => String(v);
  }
  const ys = a => mt + (1 - a / ymax) * (H - mt - mb);
  let s = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="Scatter of accuracy versus total time per run">';
  s += '<g class="grid">';
  for (const a of yticks) s += '<line x1="' + ml + '" x2="' + (W - mr) + '" y1="' + ys(a) + '" y2="' + ys(a) + '"/>';
  SUBTICKS.filter(v => v >= lo && v <= hi).forEach(v => s += '<line x1="' + xs(v) + '" x2="' + xs(v) + '" y1="' + mt + '" y2="' + (H - mb) + '" stroke-dasharray="2 4"/>');
  s += '</g>';
  for (const a of yticks)
    s += '<text class="ax" style="font-size:15px" x="' + (ml - 8) + '" y="' + (ys(a) + 5) + '" text-anchor="end">' + ylab(a) + '</text>';
  TIME_TICKS.filter(([v]) => v >= lo && v <= hi).forEach(([v, t]) => {
    s += '<line x1="' + xs(v) + '" x2="' + xs(v) + '" y1="' + mt + '" y2="' + (H - mb) + '" stroke="var(--muted)" stroke-opacity=".35"/>';
    s += '<text class="ax" style="font-size:15px" x="' + xs(v) + '" y="' + (H - mb + 22) + '" text-anchor="middle">' + t + '</text>';
  });
  s += '<text class="axt" style="font-size:16px" x="' + (ml + (W - ml - mr) / 2) + '" y="' + (H - 10) + '" text-anchor="middle">total time to completion (log scale)</text>';
  s += '<text class="axt" style="font-size:16px" transform="translate(15,' + (mt + (H - mt - mb) / 2) + ') rotate(-90)" text-anchor="middle">' + (yMode === 'frontier' ? 'frontier (digits of p and q)' : 'score (accuracy; graded runs: factored)') + '</text>';
  // "better" hints in the margins: up beside the y title, left under the x axis (best corner = top-left)
  s += axisBetter(27, mt + (H - mt - mb) / 2, true, 'higher is better');
  s += hBetter(ml, H - 14, true, 'lower is better (faster)');
  const order = rs.slice().sort((a, b) => (shown.has(a._i) ? 1 : 0) - (shown.has(b._i) ? 1 : 0));
  order.forEach(r => {
    const x = xs(r.seconds), y = ys(yv(r));
    const hl = shown.has(r._i), col = modelColor(r.model);
    s += '<g class="pt" tabindex="0" data-i="' + r._i + '" role="button" aria-label="' +
      esc(tl(r.task) + ' ' + r.model + ' ' + r.arm + (r.status === 'in_progress' ? ' (running)' : '') + ': ' + (100 * scoreOf(r)).toFixed(1) + '% in ' + fmtDur(r.seconds) + (r.frontier ? ', ' + fmtFrontier(r.frontier) : '') + '. Open as panel') + '">';
    if (hl) s += '<circle cx="' + x + '" cy="' + y + '" r="16" fill="none" stroke="var(--fg)" stroke-width="2.5"/>';
    s += shapePath(shapeOf(r.mode), x, y, hl ? 9 : 8) + (r.status === 'in_progress'
      ? ' fill="var(--bg)" stroke="' + col + '" stroke-width="2.5"/>' : ' fill="' + col + '" stroke="var(--bg)" stroke-width="1.5"/>');
    if (hl) s += '<text x="' + (x + 18) + '" y="' + (y - 12) + '" style="font-size:15px;font-weight:700">' +
      shown.get(r._i).map(n => '#' + n).join(' ') + '</text>';
    s += '</g>';
  });
  box.innerHTML = s + '</svg>';
}

function renderModeChips(present) {
  const box = document.getElementById('ovmodes');
  const ae = document.activeElement, fv = ae && box.contains(ae) ? ae.value : null;
  const on = m => !ovModes || ovModes.includes(m);
  const allOn = present.every(on);
  const chip = (v, label, checked) => '<label class="chip"><input type="checkbox" value="' + esc(v) + '"' +
    (checked ? ' checked' : '') + '> ' + (v === '*' ? '' : shapeIcon(shapeOf(v), 'var(--muted)')) + esc(label) + '</label>';
  box.innerHTML = '<span class="lbl">Modes</span>' + chip('*', 'all', allOn) + present.map(m => chip(m, m, on(m))).join('');
  if (fv != null) { const i = box.querySelector('input[value="' + fv + '"]'); if (i) i.focus({ preventScroll: true }); }
}
document.getElementById('ovy')?.addEventListener('change', e => {
  ovY = e.target.value === 'frontier' ? 'frontier' : 'acc'; hideTip(); renderOverview(); writeHash();
});
document.getElementById('ovmodes')?.addEventListener('change', e => {
  const i = e.target; if (i.type !== 'checkbox') return;
  const taskRuns = RUNS.filter(r => r.task === effTask());
  const present = uniq(taskRuns.map(r => r.mode));
  if (i.value === '*') ovModes = i.checked ? null : (ovModes || []).filter(m => !present.includes(m));
  else {
    // remember modes of other tasks; toggle within the current task's modes
    let cur = ovModes ? ovModes.slice() : uniq(RUNS.map(r => r.mode));
    cur = i.checked ? uniq(cur.concat([i.value])) : cur.filter(m => m !== i.value);
    const everything = uniq(RUNS.map(r => r.mode));
    ovModes = everything.every(m => cur.includes(m)) ? null : cur;
  }
  hideTip(); renderOverview(); writeHash();
});

function showTip(g, evt) {
  const r = RUNS[+g.dataset.i], tip = document.getElementById('tip'), wrap = document.getElementById('ovwrap');
  if (!r) return hideTip();
  tip.innerHTML = '<strong>' + esc(tl(r.task) + ' · ' + r.arm) + '</strong><br>' + esc(r.model) + '<br>' +
    (r.status === 'in_progress' ? '<strong>running</strong>: ' + fmtInt(r.attempted) + '/' + fmtInt(r.cases) + ' attempted so far (hollow)<br>' : '') +
    (r.status === 'budget_cut' ? 'budget cut: ' + fmtInt(r.attempted) + '/' + fmtInt(r.cases) + ' attempted<br>' : '') +
    (isGraded(r) ? '<strong>graded</strong>: frontier ' + esc(r.graded.frontier_digits) + ' digits, ' + fmtInt(r.graded.total_factored) +
      '/' + fmtInt(r.graded.of) + ' factored (' + pct(scoreOf(r)) + ') = plotted y<br>benchmark (not plotted) ' : '') +
    benchLine(r) + '<br>total ' +
    esc(fmtDur(r.seconds)) + ' · ' + fmtInt(r.tokens) + ' tokens' + (r.cap ? '<br>cap: ' + esc(r.cap) : '') +
    (r.hidden && r.hidden.cases != null ? '<br>hidden ' + fmtInt(r.hidden.correct) + '/' + fmtInt(r.hidden.cases) : '') +
    (r.frontier ? '<br>' + esc(fmtFrontier(r.frontier)) : '') +
    (fineOf(r) ? '<br>fine frontier ' + esc(fmtFine(fineOf(r))) : '') +
    '<br><span style="color:var(--muted)">' + esc(r.source) + '</span>';
  tip.style.display = 'block';
  const wb = wrap.getBoundingClientRect();
  let px, py;
  if (evt && evt.clientX != null) { px = evt.clientX - wb.left; py = evt.clientY - wb.top; }
  else { const b = g.getBoundingClientRect(); px = b.right - wb.left; py = b.top - wb.top; }
  const tw = tip.offsetWidth, th = tip.offsetHeight;
  let left = px + 14, top = py - th - 10;
  if (left + tw > wb.width) left = Math.max(0, px - tw - 14);
  left = Math.max(0, Math.min(left, wb.width - tw));
  if (top < 0) top = py + 16;
  tip.style.left = left + 'px'; tip.style.top = top + 'px';
}
const hideTip = () => { const t = document.getElementById('tip'); if (t) t.style.display = 'none'; };

// ---------- live data ----------
const REFRESH_MS = 30000;
let paused = false, timer = null, lastFetch = null, flashT = null;
function hhmmss(d) { return d.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit', hour12: false }); }
function renderLive(flash, err) {
  const el = document.getElementById('live');
  const g = GEN ? new Date(GEN) : null;
  let txt = RUNS.length || GEN
    ? 'data updated ' + (g && !isNaN(g) ? hhmmss(g) : '?') + ' · ' + RUNS.length + ' runs'
    : 'no data yet (summary-data.js missing or empty)';
  if (paused) txt += ' · auto-refresh paused';
  else if (lastFetch) txt += ' · checked ' + hhmmss(lastFetch);
  if (err) txt += ' · last check failed';
  el.textContent = txt;
  el.title = GEN ? 'generated_at ' + GEN : '';
  el.classList.toggle('err', !!err);
  if (flash) {
    el.classList.add('flash');
    clearTimeout(flashT);
    flashT = setTimeout(() => el.classList.remove('flash'), 1800);
  }
}
const COND = { M: 'M · memory only', R: 'R · web references', L: 'L · anything goes' };
function renderSota() {
  const rs = RUNS.filter(r => r.solution).sort((a, b) => rank(['M', 'R', 'L'], a.solution.cond) - rank(['M', 'R', 'L'], b.solution.cond) ||
    String(a.model).localeCompare(b.model));
  const el = document.getElementById('sotatable');
  ['sota', 'sotatable'].forEach(id => { document.getElementById(id).hidden = !rs.length; });
  if (!rs.length) { el.innerHTML = ''; return; }
  const maxDev = Math.max(3600, ...rs.map(r => r.solution.dev_seconds || 0));
  el.innerHTML = '<table><thead><tr><th>condition</th><th>model · effort</th><th>solution chosen</th>' +
    '<th class="num">coding time</th><th class="num">own code</th><th>crates</th><th class="num">fine frontier</th></tr></thead><tbody>' +
    rs.map(r => {
      const so = r.solution, ff = fineOf(r), c = modelColor(r.model);
      const w = Math.round(120 * (so.dev_seconds || 0) / maxDev);
      return '<tr><td>' + esc(COND[so.cond] || so.cond) + '</td><td><span style="color:' + c + '">■</span> ' +
        esc(r.model + ' · ' + r.level) + '</td><td>' + esc(so.approach || '–') + '</td><td class="num">' +
        '<span class="bar" style="width:' + w + 'px;background:' + c + '"></span>' + esc(fmtDurRound(so.dev_seconds || 0)) +
        '</td><td class="num">' + esc(so.lines) + ' lines</td><td>' +
        esc(so.crates.length ? so.crates.join(', ') + (so.vendored ? ' (vendored)' : '') : 'none') + '</td><td class="num"><strong>' +
        esc(ff ? ff.fine_frontier : '–') + '</strong> digits</td></tr>';
    }).join('') + '</tbody></table>';
}
function renderAll() {
  if (PAGE === 'grid') { renderTask(); renderPanels(); renderOverview(); } else { renderSota(); renderFrontier(); }
  writeHash();
}
// called after a new summary-data.js has executed; re-renders only if generated_at changed
function onData() {
  const g = (window.LONGMUL_DATA || {}).generated_at || null;
  if (g === GEN && RUNS) { renderLive(false); return false; }
  const sx = window.scrollX, sy = window.scrollY;
  loadData();
  if (!panels.length && RUNS.length) defaultPanels();
  hideTip(); hideFrTip();
  renderAll();
  window.scrollTo(sx, sy);
  renderLive(true);
  return true;
}
function reloadData() {
  const old = document.getElementById('datascript');
  const s = document.createElement('script');
  s.src = 'summary-data.js?t=' + Date.now();
  s.onload = () => { lastFetch = new Date(); if (old) old.remove(); s.id = 'datascript'; onData(); };
  s.onerror = () => { lastFetch = new Date(); s.remove(); renderLive(false, true); };
  document.head.appendChild(s);
}
function schedule() {
  clearInterval(timer);
  timer = paused ? null : setInterval(reloadData, REFRESH_MS);
}

// ---------- wiring ----------
function newPanel(sel) { const p = Object.assign({}, sel); p.ov = Object.assign({}, sel.ov || {}); p.ovv = Object.assign({}, sel.ovv || {}); p.id = ++uid; delete p._ms; return p; }

document.getElementById('ovtask')?.addEventListener('change', e => {
  ovTask = e.target.value; hideTip(); renderOverview(); writeHash();
});
// set a panel's task; keeps model/mode/arm when that run exists for the new task, else first valid
function setTask(p, t) { p.task = t; delete p._ms; normalize(p, 0); }
document.getElementById('panels')?.addEventListener('change', e => {
  const s = e.target;
  const pe = s.closest('.panel'); if (!pe) return;
  const p = panels.find(x => String(x.id) === pe.dataset.id); if (!p) return;
  if (s.dataset.act === 'from') {
    const id = s.value === '' ? null : +s.value;
    p.from = id != null && byId(id) && !followsChain(byId(id), p) ? id : null;
    p.ov = {}; p.ovv = {}; // a new link starts by following every field
    propagate();
    renderPanels(); renderOverview(); writeHash();
    return;
  }
  if (!s.dataset.field) return;
  const f = s.dataset.field;
  p[f] = s.value;
  delete p._ms;
  if (p.from != null) { p.ov[f] = true; p.ovv[f] = s.value; } // a follower's edit becomes a local override
  // an explicit pick downstream clears stale wishes for fields that now cascade from it
  FIELDS.slice(FIELDS.indexOf(f) + 1).forEach(g => { if (p.ovv && p.ovv[g] != null && !p.ov[g]) delete p.ovv[g]; });
  if (f === 'task') setTask(p, s.value);
  else if (f !== 'metric') normalize(p, FIELDS.indexOf(f));
  propagate();
  renderPanels(); renderOverview(); writeHash();
});
document.getElementById('panels')?.addEventListener('click', e => {
  const b = e.target.closest('button[data-act]'); if (!b) return;
  const pe = b.closest('.panel'), i = panels.findIndex(x => String(x.id) === pe.dataset.id);
  if (b.dataset.act === 'revert') {
    const p = panels[i];
    if (p && p.ov) { delete p.ov[b.dataset.f]; if (p.ovv) delete p.ovv[b.dataset.f]; }
    propagate();
    renderPanels(); renderOverview(); writeHash();
    const sel = document.querySelectorAll('#panels .panel')[i];
    const t = sel && sel.querySelector('select[data-field="' + b.dataset.f + '"]'); if (t) t.focus({ preventScroll: true });
    return;
  }
  if (b.dataset.act === 'clone') {
    panels.splice(i + 1, 0, newPanel(panels[i]));
    renderPanels(); renderOverview(); writeHash();
    const n = document.querySelectorAll('#panels .panel')[i + 1];
    if (n) n.querySelector('select:not([disabled])').focus();
  } else if (b.dataset.act === 'remove') {
    const gone = panels.splice(i, 1)[0];
    panels.forEach(q => { if (q.from === gone.id) q.from = null; }); // followers keep their current task
    renderPanels(); renderOverview(); writeHash();
    const rest = document.querySelectorAll('#panels .panel button[data-act="remove"]');
    if (rest.length) rest[Math.min(i, rest.length - 1)].focus(); else document.getElementById('add').focus();
  }
});
document.getElementById('add')?.addEventListener('click', () => {
  const d = defaults()[0];
  if (!d) return;
  d.from = null;
  panels.push(newPanel(d));
  renderPanels(); renderOverview(); writeHash();
  const all = document.querySelectorAll('#panels .panel');
  all[all.length - 1].scrollIntoView({ behavior: 'smooth', block: 'nearest' });
});
document.getElementById('reset')?.addEventListener('click', () => {
  ovTask = null; defaultPanels(); ovModes = null; renderAll();
});
document.getElementById('pause').addEventListener('click', e => {
  paused = !paused;
  e.target.textContent = paused ? 'Resume auto-refresh' : 'Pause auto-refresh';
  e.target.setAttribute('aria-pressed', String(paused));
  schedule();
  if (!paused) reloadData();
  renderLive(false);
});
const ov = document.getElementById('ov');
ov?.addEventListener('mousemove', e => { const g = e.target.closest('.pt'); if (g) showTip(g, e); else hideTip(); });
ov?.addEventListener('mouseleave', hideTip);
ov?.addEventListener('focusin', e => { const g = e.target.closest('.pt'); if (g) showTip(g); });
ov?.addEventListener('focusout', hideTip);
function openRun(g) {
  const r = RUNS[+g.dataset.i];
  if (!r) return;
  panels.push(newPanel(selFromRun(r)));
  hideTip(); renderPanels(); renderOverview(); writeHash();
  const all = document.querySelectorAll('#panels .panel');
  all[all.length - 1].scrollIntoView({ behavior: 'smooth', block: 'nearest' });
}
ov?.addEventListener('click', e => { const g = e.target.closest('.pt'); if (g) openRun(g); });
ov?.addEventListener('keydown', e => {
  const g = e.target.closest('.pt');
  if (g && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); openRun(g); }
});
window.addEventListener('resize', () => { hideTip(); hideFrTip(); });
document.getElementById('fr-timeline')?.addEventListener('mousemove', e => {
  const g = e.target.closest('.tlseg'), wrap = e.currentTarget.closest('.frwrap'), tip = wrap.querySelector('.frtip');
  if (!g) { tip.style.display = 'none'; return; }
  const se = frontierSeries().find(x => x.id === g.dataset.s); if (!se) return;
  const ep = episodesOf(se.run.solution.timeline)[+g.dataset.k]; if (!ep) return;
  tip.innerHTML = episodeTip(se, ep); tip.style.display = 'block';
  const wb = wrap.getBoundingClientRect();
  tip.style.left = Math.max(4, Math.min(e.clientX - wb.left + 14, wb.width - tip.offsetWidth - 4)) + 'px';
  tip.style.top = (e.clientY - wb.top + 14) + 'px';
});
document.getElementById('fr-timeline')?.addEventListener('mouseleave', hideFrTip);
document.querySelectorAll('.frchart:not(#fr-timeline)').forEach(frEl => { // the timeline has its own tooltip
frEl.addEventListener('mousemove', e => { const g = e.target.closest('.frpt'); if (g) showFrTip(g, e); else hideFrTip(); });
frEl.addEventListener('mouseleave', hideFrTip);
frEl.addEventListener('focusin', e => { const g = e.target.closest('.frpt'); if (g) showFrTip(g); });
frEl.addEventListener('focusout', hideFrTip);
});
document.getElementById('franchor')?.addEventListener('change', e => {
  frAnchorTest = e.target.checked; hideFrTip(); renderFrontier(); writeHash();
});
document.getElementById('frrefs')?.addEventListener('change', e => {
  frRefs = e.target.checked; hideFrTip(); renderFrontier(); writeHash();
});
document.getElementById('frfine')?.addEventListener('change', e => {
  frFine = e.target.checked; hideFrTip(); renderFrontier(); writeHash();
});
document.getElementById('frlegend')?.addEventListener('change', e => {
  const i = e.target; if (i.type !== 'checkbox') return;
  const se = frontierSeries().find(x => x.id === i.value); if (!se) return;
  frOff = i.checked === frDefaultOn(se) ? frOff.filter(x => x !== i.value) : uniq(frOff.concat([i.value]));
  hideFrTip(); renderFrontier(); writeHash();
});
document.getElementById('frlegend')?.addEventListener('click', e => { // quick toggle: all
  const b = e.target.closest('button[data-frq]'); if (!b) return;
  const q = b.dataset.frq;
  frOff = [];
  frontierSeries().forEach(se => {
    const want = !noProg(se) && q === 'all';
    if (want !== frDefaultOn(se)) frOff.push(se.id);
  });
  hideFrTip(); renderFrontier(); writeHash();
  const nb = document.querySelector('#frlegend button[data-frq="' + q + '"]'); if (nb) nb.focus({ preventScroll: true });
});
window.addEventListener('hashchange', () => {
  if (location.hash !== encodeHash()) { readHash(); renderAll(); }
});

loadData();
if (!readHash() && PAGE === 'grid') defaultPanels();
renderAll();
renderLive(false);
schedule();
window.bignumReload = reloadData; // manual refresh hook (also handy from the console)
})();

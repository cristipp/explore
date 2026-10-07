// Widgets for report.html: jump-ahead (rule 90 vs rule 30) and the halving tower.
(function () {
  const $ = id => document.getElementById(id), NS = 'http://www.w3.org/2000/svg';
  function el(t, a, p, x) { const e = document.createElementNS(NS, t); for (const k in a) e.setAttribute(k, a[k]); if (x != null) e.textContent = x; if (p) p.appendChild(e); return e }
  const dark = () => matchMedia('(prefers-color-scheme: dark)').matches;

  // ---------- 1. Jump ahead: rule 90 (Lucas) vs rule 30 (must simulate) ----------
  // Cells: BigInt bit p = cell at position p; higher bits are to the LEFT. Start: one black cell at bit `off`.
  function stepRule(x, rule, mask) {
    const L = x >> 1n, R = (x << 1n) & mask;                 // L: left neighbour value at p, R: right neighbour value at p
    return rule === 90 ? (L ^ R) : (L ^ (x | R));           // rule 30: left XOR (centre OR right)
  }
  function drawTriangle(id, rule, steps) {
    const cv = $(id), W = 2 * steps + 1; cv.width = W; cv.height = steps;
    const ctx = cv.getContext('2d'), im = ctx.createImageData(W, steps), on = dark() ? [230, 230, 230] : [20, 20, 20], off = dark() ? [30, 30, 30] : [250, 250, 248];
    const mask = (1n << BigInt(W)) - 1n; let x = 1n << BigInt(steps);
    for (let t = 0; t < steps; t++) { for (let p = 0; p < W; p++) { const v = (x >> BigInt(W - 1 - p)) & 1n; im.data.set([...(v ? on : off), 255], 4 * (t * W + p)) } x = stepRule(x, rule, mask) }
    ctx.putImageData(im, 0, 0);
  }
  // rule 90, single cell: value at time t, offset j from the start cell = C(t, (t+j)/2) mod 2 (Lucas: odd iff k & ~t == 0)
  function rule90At(t, j) { if (j < -t || j > t || ((t + j) & 1n)) return 0; const k = (t + j) / 2n; return (k & ~t) === 0n ? 1 : 0 }
  function rule30Centre(t) { const W = 2n * t + 3n, mask = (1n << W) - 1n, mid = t + 1n; let x = 1n << mid; for (let i = 0n; i < t; i++) x = stepRule(x, 30, mask); return Number((x >> mid) & 1n) }
  function runJump() {
    const t90 = BigInt($('j90').value || '0'), t30 = BigInt($('j30').value || '0');
    let t0 = performance.now(); const v90 = rule90At(t90, 0n), d90 = performance.now() - t0;
    let v30 = '—', d30 = 0;
    if (t30 <= 40000n) { t0 = performance.now(); v30 = rule30Centre(t30); d30 = performance.now() - t0 } else v30 = 'too long to simulate here';
    $('jOut').innerHTML = `Rule 90, centre cell after <b>${t90.toLocaleString()}</b> steps: <b>${v90 ? '█ black' : '░ white'}</b> in ${d90.toFixed(3)} ms (one binomial-parity check, about log₂ t bit operations).<br>` +
      `Rule 30, centre cell after <b>${t30.toLocaleString()}</b> steps: <b>${typeof v30 === 'number' ? (v30 ? '█ black' : '░ white') : v30}</b>${d30 ? ` in ${d30.toFixed(1)} ms (simulating every step of a row about 2t cells wide)` : ''}.`;
  }

  // ---------- 2. The halving tower ----------
  function runTower() {
    const n = +$('tN').value, c = +$('tC').value, y0 = +$('tY').value, Fz = +$('tF').value;
    const T = 2 ** n; const rows = []; let a = T, y = y0, k = 0;
    rows.push([0, y, a]);
    while (k < 400) { k++; y = y0 + k * Fz; const next = a / 2 + c * y; if (next >= a) break; a = next; rows.push([k, y, a]) }
    const last = rows[rows.length - 1];
    $('tOut').innerHTML = `Direct run: T = 2<sup>${n}</sup> ≈ ${T.toExponential(2)} steps. After <b>${last[0]}</b> levels the tower's runtime bottoms out at about <b>${Math.round(last[2]).toLocaleString()}</b> steps: roughly the cost of reading the ${Math.round(last[1]).toLocaleString()}-symbol input. ` +
      `That is a ${(T / last[2]).toExponential(1)}× speedup from nothing. The time hierarchy theorem says some problems at this size provably need about 2<sup>${n}</sup> steps, so the halving foreseer F can't exist.`;
    const box = $('tChart'); box.innerHTML = ''; const W = 760, H = 260, L = 70, R = 20, Tp = 10, B = 36, svg = el('svg', { viewBox: `0 0 ${W} ${H}` }, box);
    const kmax = Math.max(4, last[0]), lmax = Math.log10(T) + 0.5, lmin = Math.max(0, Math.floor(Math.log10(Math.min(...rows.map(r => r[2])))) - 0.5);
    const x = k => L + k / kmax * (W - L - R), yv = v => Tp + (lmax - Math.log10(v)) / (lmax - lmin) * (H - Tp - B);
    for (let e = Math.ceil(lmin); e <= Math.floor(lmax); e += Math.max(1, Math.round((lmax - lmin) / 6))) { el('line', { x1: L, x2: W - R, y1: yv(10 ** e), y2: yv(10 ** e), stroke: 'var(--grid)' }, svg); el('text', { x: L - 8, y: yv(10 ** e) + 5, 'text-anchor': 'end', class: 'muted', 'font-size': 13 }, svg, '1e' + e) }
    el('text', { x: (L + W - R) / 2, y: H - 4, 'text-anchor': 'middle', class: 'muted', 'font-size': 13 }, svg, 'tower level k (F foreseeing F foreseeing … P) · runtime bound in steps (log)');
    el('polyline', { points: rows.map(r => x(r[0]) + ',' + yv(r[2])).join(' '), fill: 'none', stroke: 'var(--s1)', 'stroke-width': 2.5 }, svg);
    el('polyline', { points: rows.map(r => x(r[0]) + ',' + yv(c * r[1])).join(' '), fill: 'none', stroke: 'var(--s2)', 'stroke-width': 2, 'stroke-dasharray': '5 4' }, svg);
  }

  window.addEventListener('load', () => {
    if ($('c90')) { drawTriangle('c90', 90, 64); drawTriangle('c30', 30, 64); $('jGo').onclick = runJump; runJump() }
    if ($('tN')) { for (const id of ['tN', 'tC', 'tY', 'tF']) $(id).oninput = runTower; runTower() }
  });
})();

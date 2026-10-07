// Widget for report.html section 7: bugs in tiny Turing machines that are meant to compute n -> n+1.
// Data (window.TMDATA) comes from tmdata.js, produced by an exhaustive enumeration (see the report for the convention).
// Rule table: entry (state*2 + colour) -> newstate*4 + newcolour*2 + move (1 = right).
(function () {
  const $ = id => document.getElementById(id), D = window.TMDATA;
  if (!D) return;
  const fmt = x => Number(x).toLocaleString('en-US');

  // ---------- simulator (same convention as the enumeration) ----------
  function run(rule, n, keepHistory) {
    const START = 300, tape = new Uint8Array(START + 2), hist = [];
    let lo = START;
    for (let i = 0, m = n; m; i++, m = Math.floor(m / 2)) { tape[START - i] = m % 2; lo = START - i }
    let pos = START, st = 0;
    for (let step = 0; step < 5000; step++) {
      if (keepHistory) hist.push({ tape: tape.slice(), pos, st });
      const c = rule[st * 2 + tape[pos]];
      tape[pos] = (c >> 1) & 1; st = c >> 2; pos += (c & 1) ? 1 : -1;
      if (pos > START) {
        let v = 0; for (let i = lo; i <= START; i++) v = v * 2 + tape[i];
        if (keepHistory) hist.push({ tape: tape.slice(), pos, st: -1 });
        return { halted: true, value: v, steps: step + 1, hist, lo, START };
      }
      if (pos < lo) lo = pos;
      if (pos < 1) break;
    }
    return { halted: false, steps: 5000, hist, lo, START };
  }

  // ---------- 1. where do machines first go wrong? ----------
  function table() {
    const S = Object.keys(D.runs).sort();
    const ns = [...new Set(S.flatMap(s => Object.keys(D.runs[s].first_fail).map(Number)))].filter(n => n > 1).sort((a, b) => a - b);
    const max = Math.max(...S.flatMap(s => [D.runs[s].correct, ...ns.map(n => sum(D.runs[s].first_fail[n]))]));
    function sum(v) { return v ? v[0] + v[1] : 0 }
    function cell(v, cls) {
      if (!v) return '<td style="color:var(--muted)">·</td>';
      const w = Math.max(2, 120 * Math.log10(1 + v) / Math.log10(1 + max));
      return `<td><span class="bar ${cls || ''}" style="width:${w}px"></span> ${fmt(v)}</td>`;
    }
    let h = '<table class="bugtab"><tr><th>first wrong answer at n =</th>' + S.map(s => `<th>${s} states<br><span class="small">${fmt(D.runs[s].total)} machines</span></th>`).join('') + '</tr>';
    h += '<tr><td>1 (wrong right away, or never stops)</td>' + S.map(s => cell(sum(D.runs[s].first_fail[1]), 'dim')).join('') + '</tr>';
    for (const n of ns) h += `<tr><td>${n}${(n & (n + 1)) === 0 ? ' <span class="small">(binary all 1s)</span>' : ''}</td>` + S.map(s => cell(sum(D.runs[s].first_fail[n]), n >= 7 ? 'late' : '')).join('') + '</tr>';
    h += `<tr><td><strong>never, for n ≤ ${D.nmax}</strong></td>` + S.map(s => cell(D.runs[s].correct, 'ok')).join('') + '</tr></table>';
    $('bugTable').innerHTML = h;
  }

  // ---------- 2. explore one machine ----------
  const picks = D.examples;
  function strip(rule) {
    let h = ''; const N = 80;
    for (let n = 1; n <= N; n++) {
      const r = run(rule, n), ok = r.halted && r.value === n + 1;
      h += `<span class="cellb ${ok ? 'g' : 'b'}" data-n="${n}" title="n = ${n}: ${r.halted ? 'output ' + r.value : 'never stops'}">${ok ? '' : '✗'}</span>`;
    }
    $('bugStrip').innerHTML = h;
    $('bugStrip').querySelectorAll('.cellb').forEach(e => e.onclick = () => { $('bugN').value = e.dataset.n; draw() });
  }
  function draw() {
    const ex = picks[+$('bugPick').value], rule = ex.rule, n = Math.max(1, Math.min(4095, +$('bugN').value || 1));
    const r = run(rule, n, true), cv = $('bugCanvas');
    const lo = Math.min(r.lo, ...r.hist.map(h => h.pos)) - 1, hi = r.START + 1, W = hi - lo + 1, H = r.hist.length;
    const px = Math.max(4, Math.min(18, Math.floor(560 / W), Math.floor(1400 / H)));
    cv.width = W * px; cv.height = H * px; cv.style.width = Math.min(W * px, 700) + 'px';
    const ctx = cv.getContext('2d'), css = getComputedStyle(document.documentElement);
    const fg = css.getPropertyValue('--fg').trim() || '#111', bg = css.getPropertyValue('--card').trim() || '#f7f7f5', grid = css.getPropertyValue('--grid').trim() || '#ddd';
    const stc = ['--s1', '--s2', '--s3', '--warn'].map(v => css.getPropertyValue(v).trim());
    ctx.fillStyle = bg; ctx.fillRect(0, 0, cv.width, cv.height);
    r.hist.forEach((h, t) => {
      for (let i = lo; i <= hi; i++) {
        if (i <= r.START && h.tape[i]) { ctx.fillStyle = fg; ctx.fillRect((i - lo) * px, t * px, px, px) }
      }
      if (h.st >= 0) { ctx.strokeStyle = stc[h.st] || fg; ctx.lineWidth = Math.max(2, px / 4); ctx.strokeRect((h.pos - lo) * px + 1.5, t * px + 1.5, px - 3, px - 3) }
    });
    ctx.fillStyle = grid; ctx.fillRect((r.START + 1 - lo) * px, 0, 1, cv.height);
    const ok = r.halted && r.value === n + 1;
    $('bugOut').innerHTML = `${ex.label}. Input n = <b>${n}</b> (binary ${n.toString(2)}): ` +
      (r.halted ? `stops after ${r.steps} steps with output <b>${r.value}</b> (binary ${r.value.toString(2)}). ${ok ? '<span style="color:var(--good)">Correct.</span>' : `<span style="color:var(--bad)">Wrong: n+1 = ${n + 1}.</span>`}`
        : '<span style="color:var(--bad)">never stops.</span>') +
      `<br><span class="small">Rows are steps, top to bottom; black cells are 1s; the outlined square is the head, coloured by state. The machine stops when the head crosses the line on the right.</span>`;
  }
  function pick() {
    const ex = picks[+$('bugPick').value]; strip(ex.rule); $('bugN').value = ex.bug || 7; draw();
  }

  window.addEventListener('load', () => {
    table();
    $('bugPick').innerHTML = picks.map((e, i) => `<option value="${i}">${e.label}</option>`).join('');
    $('bugPick').onchange = pick; $('bugN').oninput = draw;
    $('bugPick').value = String(picks.length - 1); pick();
  });
})();

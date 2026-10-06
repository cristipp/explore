// Widget for report.html: coarse-graining elementary cellular automata (after Israeli & Goldenfeld 2004).
// Rule A with block size N and projection P coarse-grains to rule B when "run A for N steps, then project each block"
// always equals "project, then run B for one step". The pairs below were found by exhaustive search (block sizes 2–5).
(function () {
  const $ = id => document.getElementById(id);
  // P: truth table over block values; a block's value reads its cells left to right as a binary number
  const PAIRS = [
    { A: 105, N: 2, P: 3, B: 150, label: 'Rule 105 → Rule 150 (blocks of 2; coarse cell = "left cell is white")' },
    { A: 146, N: 3, P: 128, B: 128, density: 0.9, label: 'Rule 146 → Rule 128 (blocks of 3; coarse cell = "block is all black")' },
    { A: 90, N: 2, P: 6, B: 90, label: 'Rule 90 → Rule 90 (blocks of 2; coarse cell = "the two cells differ")' },
    { A: 110, N: 5, P: 1 << 10, B: 0, label: 'Rule 110 → Rule 0 (blocks of 5; coarse cell = "block is 01010")' },
  ];
  const WC = 100, TC = 50;     // coarse width and coarse steps
  function step(rule, row) {
    const n = row.length, out = new Uint8Array(n);
    for (let i = 0; i < n; i++) out[i] = (rule >> (row[(i + n - 1) % n] * 4 + row[i] * 2 + row[(i + 1) % n])) & 1;
    return out;
  }
  function project(pair, row) {
    const out = new Uint8Array(row.length / pair.N);
    for (let b = 0; b < out.length; b++) {
      let v = 0; for (let j = 0; j < pair.N; j++) v = v * 2 + row[b * pair.N + j];
      out[b] = (pair.P >> v) & 1;
    }
    return out;
  }
  let seed = 7;
  const rnd = () => (seed = (seed * 16807) % 2147483647) / 2147483647;
  function draw() {
    const pair = PAIRS[+$('cgPick').value], N = pair.N, css = getComputedStyle(document.documentElement);
    const fg = css.getPropertyValue('--fg').trim(), bg = css.getPropertyValue('--card').trim(), bad = css.getPropertyValue('--bad').trim(), acc = css.getPropertyValue('--s1').trim();
    let fine = new Uint8Array(WC * N).map(() => rnd() < (pair.density || 0.5) ? 1 : 0);
    const fineRows = [fine];
    for (let t = 0; t < TC * N; t++) { fine = step(pair.A, fine); fineRows.push(fine) }
    let coarse = project(pair, fineRows[0]); const coarseRows = [coarse];
    for (let t = 0; t < TC; t++) { coarse = step(pair.B, coarse); coarseRows.push(coarse) }
    // left: fine evolution, all rows; right: B's prediction, outlined red where it disagrees with the projected fine rows
    const cf = $('cgFine'), cc = $('cgCoarse'), s = 3;
    cf.width = WC * N; cf.height = TC * N + 1; cc.width = WC * s; cc.height = (TC + 1) * s;
    const xf = cf.getContext('2d'); xf.fillStyle = bg; xf.fillRect(0, 0, cf.width, cf.height); xf.fillStyle = fg;
    fineRows.forEach((r, t) => r.forEach((v, i) => v && xf.fillRect(i, t, 1, 1)));
    const xc = cc.getContext('2d'); xc.fillStyle = bg; xc.fillRect(0, 0, cc.width, cc.height);
    let wrong = 0, ones = 0;
    coarseRows.forEach((r, t) => {
      const truth = project(pair, fineRows[t * N]);
      r.forEach((v, i) => {
        if (v) { xc.fillStyle = acc; xc.fillRect(i * s, t * s, s, s); ones++ }
        if (v !== truth[i]) { wrong++; xc.fillStyle = bad; xc.fillRect(i * s, t * s, s, s) }
      });
    });
    $('cgOut').innerHTML = `Fine rule ${pair.A} ran ${TC * N} steps on ${WC * N} cells (left). Rule ${pair.B} ran ${TC} steps on the ${WC} projected cells (right).
      Disagreements between the coarse prediction and the projected fine run: <b>${wrong}</b> of ${(TC + 1) * WC} cells.` +
      (pair.B === 0 ? ` Here the coarse prediction is only "the block 01010 never appears after the first block-step", which is all a coarse-graining onto rule 0 can say.` : '');
  }
  window.addEventListener('load', () => {
    if (!$('cgPick')) return;
    $('cgPick').innerHTML = PAIRS.map((p, i) => `<option value="${i}">${p.label}</option>`).join('');
    $('cgPick').onchange = draw; $('cgNew').onclick = draw; draw();
  });
})();

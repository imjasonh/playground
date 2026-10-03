// Q builds a version-40 symbol (level L, mask 0, byte mode) and D paints it.
// build.js copies both into a data:text/html URL. That URL has to fit in the
// symbol, 2953 bytes, so comments and spare whitespace stay out of the copy.
// Chrome leaves this script's bytes in location.href only after "%" "?" "#"
// "<" ">" and backticks are percent-encoded. D(location.href) draws that URL.

const N = 177;
export function Q(h) {
  const E = [];
  const L = [];
  for (let x = 1, i = 0; i < 255; i++) {
    E[i] = x;
    L[x] = i;
    x <<= 1;
    if (x > 255) {
      x ^= 285;
    }
  }
  const mul = (a, b) => (a && b ? E[(L[a] + L[b]) % 255] : 0);
  function rs(d) {
    let g = [1, 212, 246, 77, 73, 195, 192, 75, 98, 5, 70, 103, 177, 22, 217, 138, 51, 181, 246, 72, 25, 18, 46, 228, 74, 216, 195, 11, 106, 130, 150];
    const m = d.concat(Array(30));
    for (let i = 0; i < d.length; i++) {
      const f = m[i];
      if (f) {
        for (let j = 0; j < g.length; j++) {
          m[i + j] ^= mul(g[j], f);
        }
      }
    }
    return m.slice(d.length);
  }
  const M = new Uint8Array(N * N);
  const set = (r, c, v) => {
    if (r < 0 || c < 0 || r >= N || c >= N) {
      return;
    }
    M[r * N + c] = (v ? 1 : 0) | 2;
  };
  const finder = (y, x) => {
    for (let r = -1; r < 8; r++) {
      for (let c = -1; c < 8; c++) {
        const o = r < 0 || c < 0 || r > 6 || c > 6;
        const e = r === 0 || c === 0 || r === 6 || c === 6;
        const k = r > 1 && r < 5 && c > 1 && c < 5;
        set(y + r, x + c, !o && (e || k));
      }
    }
  };
  finder(0, 0);
  finder(0, N - 7);
  finder(N - 7, 0);
  for (let i = 8; i < N - 8; i++) {
    const on = i % 2 === 0;
    set(i, 6, on);
    set(6, i, on);
  }
  const ap = [6, 30, 58, 86, 114, 142, 170];
  for (let i = 0; i < 7; i++) {
    for (let j = 0; j < 7; j++) {
      if ((i === 0 && j === 0) || (i === 0 && j === 6) || (i === 6 && j === 0)) {
        continue;
      }
      for (let r = -2; r < 3; r++) {
        for (let c = -2; c < 3; c++) {
          set(ap[i] + r, ap[j] + c, r === -2 || r === 2 || c === -2 || c === 2 || (r === 0 && c === 0));
        }
      }
    }
  }
  const bitsAt = (bits, len, place) => {
    for (let i = 0; i < len; i++) {
      place(i, (bits >> i) & 1);
    }
  };
  bitsAt(30660, 15, (i, on) => {
    if (i < 6) {
      set(i, 8, on);
    } else if (i < 8) {
      set(i + 1, 8, on);
    } else {
      set(N - 15 + i, 8, on);
    }
    if (i < 8) {
      set(8, N - i - 1, on);
    } else if (i < 9) {
      set(8, 15 - i, on);
    } else {
      set(8, 14 - i, on);
    }
  });
  set(N - 8, 8, 1);
  bitsAt(167017, 18, (i, on) => {
    const y = (i / 3) | 0;
    const x = (i % 3) + N - 11;
    set(y, x, on);
    set(x, y, on);
  });
  const bytes = [];
  let acc = 0;
  let nb = 0;
  const put = (v, l) => {
    for (let i = l - 1; i >= 0; i--) {
      acc = (acc << 1) | ((v >>> i) & 1);
      nb++;
      if (nb === 8) {
        bytes.push(acc);
        acc = 0;
        nb = 0;
      }
    }
  };
  put(4, 4);
  put(h.length, 16);
  for (let i = 0; i < h.length; i++) {
    put(h.charCodeAt(i), 8);
  }
  put(0, Math.min(4, 23648 - bytes.length * 8 - nb));
  if (nb) {
    put(0, 8 - nb);
  }
  for (let p = 236; bytes.length < 2956; p ^= 253) {
    put(p, 8);
  }
  const blocks = [];
  const ecs = [];
  let off = 0;
  for (let b = 0; b < 25; b++) {
    const len = b < 19 ? 118 : 119;
    const block = bytes.slice(off, off + len);
    off += len;
    blocks.push(block);
    ecs.push(rs(block));
  }
  const out = [];
  for (let i = 0; i < 119; i++) {
    for (let b = 0; b < 25; b++) {
      if (i < blocks[b].length) {
        out.push(blocks[b][i]);
      }
    }
  }
  for (let i = 0; i < 30; i++) {
    for (let b = 0; b < 25; b++) {
      out.push(ecs[b][i]);
    }
  }
  let bi = 0;
  let bp = 7;
  let row = N - 1;
  let dir = -1;
  for (let col = N - 1; col > 0; col -= 2) {
    if (col === 6) {
      col--;
    }
    for (;;) {
      for (let c = 0; c < 2; c++) {
        const id = row * N + col - c;
        if (M[id] < 2) {
          let on = bi < out.length && ((out[bi] >>> bp) & 1);
          if (!((row + col - c) & 1)) {
            on ^= 1;
          }
          M[id] = on;
          bp--;
          if (bp < 0) {
            bi++;
            bp = 7;
          }
        }
      }
      row += dir;
      if (row < 0 || row >= N) {
        row -= dir;
        dir = -dir;
        break;
      }
    }
  }
  return M;
}
export function D(h) {
  const c = document.createElement("canvas");
  c.width = c.height = 740;
  const g = c.getContext("2d");
  g.fillStyle = "#fff";
  g.fillRect(0, 0, 740, 740);
  g.fillStyle = "#000";
  const M = Q(h);
  for (let r = 0; r < N; r++) {
    for (let k = 0; k < N; k++) {
      if (M[r * N + k] & 1) {
        g.fillRect(k * 4 + 16, r * 4 + 16, 4, 4);
      }
    }
  }
  document.documentElement.appendChild(c);
}

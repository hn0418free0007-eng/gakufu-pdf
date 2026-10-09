"use strict";

/* ===========================================================================
   楽譜メモ消しPDF  ―  端末内（ブラウザ内）で完結する画像処理 + PDF生成
   方式D（検証済み）のJavaScript移植:
     1) 影ムラ補正（背景推定して割り算）
     2) 色ペン除去（彩度で判定して白化）
     3) 適応的2値化(Sauvola)で印刷を残し、紙を真っ白に（手書きは薄化）
     4) 微小ノイズ（薄い鉛筆の芯の断片）を連結成分で除去
   PDFは外部ライブラリ無しで生成（各ページをJPEGで埋め込み / DCTDecode）
   =========================================================================== */

const MAX_SIDE = 2200;        // 長辺の最大px（処理速度と印刷品質のバランス）
const SAT_THR = 55;           // これ以上の彩度は色ペンとみなす
const VAL_THR = 55;           // 暗すぎる画素は彩度判定から除外
const MIN_AREA = 6;           // これ未満の連結成分（黒）はノイズとして除去
const BG_SCALE = 18;          // 背景推定の縮小率（大きいほど広域の影を均す）

/** ページ状態: { name, w, h, norm:Uint8Array(0..255 影補正済みグレー, 色ペンは255) } */
const pages = [];

const $ = (id) => document.getElementById(id);
const fileInput = $("fileInput");
const controlCard = $("controlCard");
const exportCard = $("exportCard");
const pagesEl = $("pages");
const statusEl = $("status");
const thr = $("thr");
const thrVal = $("thrVal");
const thick = $("thick");
const thickVal = $("thickVal");

function setStatus(msg) {
  if (!msg) { statusEl.hidden = true; return; }
  statusEl.hidden = false;
  statusEl.textContent = msg;
}

/* --- 画像読み込み（EXIF向きはブラウザが自動適用） --- */
function loadImage(file) {
  return new Promise((resolve, reject) => {
    const url = URL.createObjectURL(file);
    const img = new Image();
    img.onload = () => { URL.revokeObjectURL(url); resolve(img); };
    img.onerror = (e) => { URL.revokeObjectURL(url); reject(e); };
    img.src = url;
  });
}

/* --- 元画像 → キャッシュ（影補正グレー norm）を計算 --- */
function buildCache(img, name) {
  let w = img.naturalWidth, h = img.naturalHeight;
  const scale = Math.min(1, MAX_SIDE / Math.max(w, h));
  w = Math.round(w * scale); h = Math.round(h * scale);

  const cv = document.createElement("canvas");
  cv.width = w; cv.height = h;
  const ctx = cv.getContext("2d", { willReadFrequently: true });
  ctx.drawImage(img, 0, 0, w, h);
  const src = ctx.getImageData(0, 0, w, h).data;

  // グレー化
  const n = w * h;
  const gray = new Float32Array(n);
  for (let i = 0, j = 0; i < n; i++, j += 4) {
    gray[i] = 0.299 * src[j] + 0.587 * src[j + 1] + 0.114 * src[j + 2];
  }

  // 背景推定: 面積平均で縮小 → 双線形で拡大（広域の影ムラを近似）。
  // Canvasのdrawimage縮小はブラウザ依存で背景がずれ、印刷まで削れたため、
  // 自前の決定論的な面積平均に置き換え（Python検証版と一致）。
  const bg = estimateBackground(gray, w, h, BG_SCALE);

  // 影補正(割り算) + 色ペン除去 → norm
  const norm = new Uint8Array(n);
  for (let i = 0, j = 0; i < n; i++, j += 4) {
    const bgg = bg[i];
    let v = bgg > 1 ? (gray[i] / bgg) * 255 : 255;
    if (v > 255) v = 255;

    // 彩度（色ペン判定）
    const r = src[j], g = src[j + 1], b = src[j + 2];
    const mx = Math.max(r, g, b), mn = Math.min(r, g, b);
    const sat = mx > 0 ? ((mx - mn) / mx) * 255 : 0;
    if (sat > SAT_THR && mx > VAL_THR) v = 255; // 色ペンは背景(白)扱い

    norm[i] = v;
  }

  return { name, w, h, norm };
}

/* --- 背景推定: 面積平均で1/scaleに縮小 → 双線形で元サイズへ拡大 ---
   ブラウザ非依存・決定論的（cv2のINTER_AREA + INTER_LINEAR相当）。 */
function estimateBackground(gray, w, h, scale) {
  const sw = Math.max(1, Math.ceil(w / scale));
  const sh = Math.max(1, Math.ceil(h / scale));
  const sum = new Float64Array(sw * sh);
  const cnt = new Int32Array(sw * sh);
  for (let y = 0; y < h; y++) {
    const sy = Math.min(sh - 1, (y / scale) | 0);
    for (let x = 0; x < w; x++) {
      const sx = Math.min(sw - 1, (x / scale) | 0);
      const si = sy * sw + sx;
      sum[si] += gray[y * w + x];
      cnt[si]++;
    }
  }
  const small = new Float32Array(sw * sh);
  for (let i = 0; i < sw * sh; i++) small[i] = cnt[i] ? sum[i] / cnt[i] : 255;

  const bg = new Float32Array(w * h);
  for (let y = 0; y < h; y++) {
    let fy = (y + 0.5) / scale - 0.5; if (fy < 0) fy = 0; if (fy > sh - 1) fy = sh - 1;
    const y0 = Math.floor(fy), y1 = Math.min(sh - 1, y0 + 1), wy = fy - y0;
    for (let x = 0; x < w; x++) {
      let fx = (x + 0.5) / scale - 0.5; if (fx < 0) fx = 0; if (fx > sw - 1) fx = sw - 1;
      const x0 = Math.floor(fx), x1 = Math.min(sw - 1, x0 + 1), wx = fx - x0;
      const a = small[y0 * sw + x0], b = small[y0 * sw + x1];
      const c = small[y1 * sw + x0], d = small[y1 * sw + x1];
      const top = a + (b - a) * wx, bot = c + (d - c) * wx;
      bg[y * w + x] = top + (bot - top) * wy;
    }
  }
  return bg;
}

/* --- 適応的2値化（Sauvola法） ---
   各画素を「その周囲（ローカル窓）の明るさ・ばらつき」と比べて白黒を決める。
   固定しきい値だと影の中の音符が消え白地が灰色化するが、適応的なら
   紙は真っ白・印刷はくっきり残り、市販スキャナアプリ相当の仕上がりになる。
   しきい値  T = m * (1 + k * (s/R - 1))   (m=局所平均, s=局所標準偏差, R=128)
   k を上げるほど ink と判定される画素が減る → より白く（メモが消え気味）。
   高速化のため積分画像(summed-area table)で局所平均・分散を O(1)/画素 で計算。 */
const SAUVOLA_R = 128;        // Sauvolaの正規化定数（8bit画像の標準値）
function adaptiveInk(norm, w, h, k) {
  const n = w * h;
  // ローカル窓の半径（画像長辺に比例, 8〜40pxにクランプ）。
  // 五線・符頭をまたぐ程度の広さで、影ムラには十分追従する。
  let r = Math.round(Math.max(w, h) / 80);
  if (r < 8) r = 8;
  if (r > 40) r = 40;

  // 積分画像: I=Σnorm, I2=Σnorm^2 （サイズ (w+1)x(h+1), 先頭行・列は0）
  const sw = w + 1;
  const I = new Float64Array(sw * (h + 1));
  const I2 = new Float64Array(sw * (h + 1));
  for (let y = 0; y < h; y++) {
    let rs = 0, rs2 = 0;
    const up = y * sw, dn = (y + 1) * sw;
    for (let x = 0; x < w; x++) {
      const v = norm[y * w + x];
      rs += v; rs2 += v * v;
      I[dn + x + 1] = I[up + x + 1] + rs;
      I2[dn + x + 1] = I2[up + x + 1] + rs2;
    }
  }

  const ink = new Uint8Array(n);
  for (let y = 0; y < h; y++) {
    const y0 = y - r < 0 ? 0 : y - r;
    const y1 = y + r >= h ? h - 1 : y + r;
    const a0 = y0 * sw, a1 = (y1 + 1) * sw;
    for (let x = 0; x < w; x++) {
      const x0 = x - r < 0 ? 0 : x - r;
      const x1 = x + r >= w ? w - 1 : x + r;
      const area = (x1 - x0 + 1) * (y1 - y0 + 1);
      const sum = I[a1 + x1 + 1] - I[a0 + x1 + 1] - I[a1 + x0] + I[a0 + x0];
      const sum2 = I2[a1 + x1 + 1] - I2[a0 + x1 + 1] - I2[a1 + x0] + I2[a0 + x0];
      const mean = sum / area;
      let varr = sum2 / area - mean * mean;
      if (varr < 0) varr = 0;
      const std = Math.sqrt(varr);
      const T = mean * (1 + k * (std / SAUVOLA_R - 1));
      ink[y * w + x] = norm[y * w + x] < T ? 1 : 0;
    }
  }
  return ink;
}

/* --- norm + 適応的2値化 → 2値(ink) → ノイズ除去 → 白黒Canvas --- */
function renderPage(cache, k, thickness) {
  const { w, h, norm } = cache;
  const n = w * h;

  // 2値: 適応的しきい値（Sauvola）でローカルに判定
  let ink = adaptiveInk(norm, w, h, k);

  // 閉処理（膨張→収縮）: しきい値の境目で欠けた細い線（音符の軸・五線）を
  // つなぎ直し、かすれ・消えかかりを防ぐ。
  ink = closing3x3(ink, w, h);

  // 縁の黒い塊（本の綴じ目・ページ端・隣ページの影）を除去。
  // 画像の外周に接する「塗りつぶし状（濃い）」の成分だけを消し、
  // 細い五線・スラー・音符（線状で密度が低い）は残す。膨張前に行う。
  removeBorderBlobs(ink, w, h);

  // 線の太らせ（元写真に近い濃さにする）。thickness回だけ2x2膨張。
  for (let t = 0; t < thickness; t++) ink = dilate2x2(ink, w, h);

  // 微小ノイズ除去（連結成分の面積フィルタ, 4近傍）
  removeSmallComponents(ink, w, h, MIN_AREA);

  // Canvas へ描画（黒字=ink, 背景=白）
  const cv = document.createElement("canvas");
  cv.width = w; cv.height = h;
  const ctx = cv.getContext("2d");
  const out = ctx.createImageData(w, h);
  const d = out.data;
  for (let i = 0, j = 0; i < n; i++, j += 4) {
    const val = ink[i] ? 0 : 255;
    d[j] = d[j + 1] = d[j + 2] = val;
    d[j + 3] = 255;
  }
  ctx.putImageData(out, 0, 0);
  return cv;
}

/* --- 連結成分の面積が minArea 未満の黒画素を消す（明示スタックでBFS） --- */
function removeSmallComponents(ink, w, h, minArea) {
  const n = w * h;
  const label = new Int32Array(n).fill(-1);
  const stack = new Int32Array(n);
  for (let start = 0; start < n; start++) {
    if (ink[start] === 0 || label[start] !== -1) continue;
    // 1成分をBFS収集
    let sp = 0;
    stack[sp++] = start;
    label[start] = start;
    let count = 0;
    const members = [];
    while (sp > 0) {
      const p = stack[--sp];
      members.push(p);
      count++;
      const x = p % w, y = (p - x) / w;
      if (x > 0)      { const q = p - 1; if (ink[q] && label[q] === -1) { label[q] = start; stack[sp++] = q; } }
      if (x < w - 1)  { const q = p + 1; if (ink[q] && label[q] === -1) { label[q] = start; stack[sp++] = q; } }
      if (y > 0)      { const q = p - w; if (ink[q] && label[q] === -1) { label[q] = start; stack[sp++] = q; } }
      if (y < h - 1)  { const q = p + w; if (ink[q] && label[q] === -1) { label[q] = start; stack[sp++] = q; } }
    }
    if (count < minArea) {
      for (const p of members) ink[p] = 0;
    }
  }
}

/* --- 縁の黒い塊・余白のゴミを除去（綴じ目・ページ端・影の黒化、五線から離れた
       読めないメモ対策） ---
   連結成分(4近傍)ごとに bbox・面積・外周接触・充填率を調べ、
   次のいずれかを満たすものを消す:
     (a) 外周に接し、bboxが外周マージン帯(上下左右いずれか)に完全に収まる
         → ページ端・隅の汚れ・五線から離れた余白のメモ
     (b) 外周に接し、充填率が非常に高い(塗りつぶし状)
         → 綴じ目・影の濃い塗りつぶし領域
   五線・音符・タイトルは中央の内側領域にあり、(a)(b)に該当しないため保持。
   マージン帯はタイトル(約10%)より上に収まるよう控えめ(6%)に設定。 */
const BORDER_MARGIN_FRAC = 0.06;    // 外周マージン帯の割合（短辺基準で控えめ）
const BORDER_SOLID_FILL = 0.50;     // これ以上の充填率は塗りつぶし状（影の塊）とみなす
function removeBorderBlobs(ink, w, h) {
  const n = w * h;
  const mx = Math.round(w * BORDER_MARGIN_FRAC);
  const my = Math.round(h * BORDER_MARGIN_FRAC);
  const seen = new Uint8Array(n);
  const stack = new Int32Array(n);
  const members = new Int32Array(n);
  for (let start = 0; start < n; start++) {
    if (ink[start] === 0 || seen[start]) continue;
    // 1成分をBFS収集しつつ bbox・外周接触を記録
    let sp = 0, mc = 0;
    stack[sp++] = start; seen[start] = 1;
    let minx = w, miny = h, maxx = -1, maxy = -1, touch = false;
    while (sp > 0) {
      const p = stack[--sp];
      members[mc++] = p;
      const x = p % w, y = (p - x) / w;
      if (x < minx) minx = x; if (x > maxx) maxx = x;
      if (y < miny) miny = y; if (y > maxy) maxy = y;
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) touch = true;
      if (x > 0)     { const q = p - 1; if (ink[q] && !seen[q]) { seen[q] = 1; stack[sp++] = q; } }
      if (x < w - 1) { const q = p + 1; if (ink[q] && !seen[q]) { seen[q] = 1; stack[sp++] = q; } }
      if (y > 0)     { const q = p - w; if (ink[q] && !seen[q]) { seen[q] = 1; stack[sp++] = q; } }
      if (y < h - 1) { const q = p + w; if (ink[q] && !seen[q]) { seen[q] = 1; stack[sp++] = q; } }
    }
    // bboxが外周マージン帯に完全に収まるか（上 or 下 or 左 or 右）
    const inMargin = (maxy < my) || (miny > h - 1 - my) ||
                     (maxx < mx) || (minx > w - 1 - mx);
    // 塗りつぶし状（充填率が非常に高い＝影の黒塊）
    const bw = maxx - minx + 1, bh = maxy - miny + 1;
    const solid = touch && (mc / (bw * bh)) >= BORDER_SOLID_FILL;
    // (a) bboxが外周マージン帯(6%)に完全に収まる成分 → 余白のゴミ・ページ端・隅の汚れ
    //     ※外周6%には本来コンテンツが無い。五線や音符は幅/高さ方向に伸びて
    //       マージン外へ跨るため「完全に収まる」に該当せず保護される。
    // (b) 縁に接する塗りつぶし状の黒塊（綴じ目・影）
    if (inMargin || solid) {
      for (let i = 0; i < mc; i++) ink[members[i]] = 0;
    }
  }
}

/* --- 3x3 膨張 --- */
function dilate3x3(src, w, h) {
  const n = w * h;
  const dst = new Uint8Array(n);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      if (src[i]) { dst[i] = 1; continue; }
      let on = 0;
      for (let dy = -1; dy <= 1 && !on; dy++) {
        const yy = y + dy; if (yy < 0 || yy >= h) continue;
        for (let dx = -1; dx <= 1; dx++) {
          const xx = x + dx; if (xx < 0 || xx >= w) continue;
          if (src[yy * w + xx]) { on = 1; break; }
        }
      }
      dst[i] = on;
    }
  }
  return dst;
}

/* --- 3x3 収縮 --- */
function erode3x3(src, w, h) {
  const n = w * h;
  const dst = new Uint8Array(n);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      if (!src[i]) { dst[i] = 0; continue; }
      let keep = 1;
      for (let dy = -1; dy <= 1 && keep; dy++) {
        const yy = y + dy; if (yy < 0 || yy >= h) { keep = 0; break; }
        for (let dx = -1; dx <= 1; dx++) {
          const xx = x + dx; if (xx < 0 || xx >= w) { keep = 0; break; }
          if (!src[yy * w + xx]) { keep = 0; break; }
        }
      }
      dst[i] = keep;
    }
  }
  return dst;
}

/* --- 閉処理 = 膨張 → 収縮（1px程度の欠けを埋める） --- */
function closing3x3(ink, w, h) {
  return erode3x3(dilate3x3(ink, w, h), w, h);
}

/* --- 2x2 膨張（線を少しだけ太らせる。3x3より穏やか） --- */
function dilate2x2(src, w, h) {
  const dst = new Uint8Array(w * h);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      let on = src[i];
      if (!on && x + 1 < w) on = src[i + 1];
      if (!on && y + 1 < h) on = src[i + w];
      if (!on && x + 1 < w && y + 1 < h) on = src[i + w + 1];
      dst[i] = on ? 1 : 0;
    }
  }
  return dst;
}

/* --- 全ページを再描画してサムネイル表示 --- */
function refreshPages() {
  const k = parseInt(thr.value, 10) / 100;   // 適応的2値化の感度
  const thickness = parseInt(thick.value, 10);
  pagesEl.innerHTML = "";
  pages.forEach((cache, idx) => {
    const cv = renderPage(cache, k, thickness);
    cache._lastCanvas = cv; // PDF生成で再利用
    const item = document.createElement("div");
    item.className = "page-item";
    const num = document.createElement("span");
    num.className = "num"; num.textContent = "P" + (idx + 1);
    const del = document.createElement("button");
    del.className = "del"; del.textContent = "×";
    del.onclick = () => { pages.splice(idx, 1); refreshPages(); updateVisibility(); };
    const im = document.createElement("img");
    im.src = cv.toDataURL("image/png");
    item.append(num, del, im);
    pagesEl.appendChild(item);
  });
}

function updateVisibility() {
  const has = pages.length > 0;
  controlCard.hidden = !has;
  exportCard.hidden = !has;
}

/* --- ファイル選択 --- */
fileInput.addEventListener("change", async (e) => {
  const files = Array.from(e.target.files || []);
  if (!files.length) return;
  setStatus("読み込み中… 0/" + files.length);
  for (let i = 0; i < files.length; i++) {
    try {
      const img = await loadImage(files[i]);
      const cache = buildCache(img, files[i].name);
      pages.push(cache);
    } catch (err) {
      console.error("load fail", files[i].name, err);
    }
    setStatus("読み込み中… " + (i + 1) + "/" + files.length);
    await new Promise((r) => setTimeout(r, 0)); // UIを更新させる
  }
  setStatus(null);
  updateVisibility();
  refreshPages();
  fileInput.value = ""; // 同じ写真を再選択できるように
});

thr.addEventListener("input", () => { thrVal.textContent = thr.value; });
thick.addEventListener("input", () => { thickVal.textContent = thick.value; });
$("reprocessBtn").addEventListener("click", () => {
  setStatus("再処理中…");
  setTimeout(() => { refreshPages(); setStatus(null); }, 10);
});

/* --- PDF生成（外部ライブラリ無し）
   可能なら可逆圧縮(FlateDecode・グレースケール)で真っ黒くっきりに埋め込む。
   CompressionStream非対応の古い環境ではJPEG(DCTDecode)にフォールバック。 --- */
$("pdfBtn").addEventListener("click", async () => {
  if (!pages.length) return;
  setStatus("PDF作成中…");
  await new Promise((r) => setTimeout(r, 10));
  try {
    const k = parseInt(thr.value, 10) / 100;
    const thickness = parseInt(thick.value, 10);
    const canUseFlate = typeof CompressionStream !== "undefined";
    const imgs = [];
    for (const c of pages) {
      const cv = c._lastCanvas || renderPage(c, k, thickness);
      const w = cv.width, h = cv.height;
      if (canUseFlate) {
        const gray = canvasToGray(cv);           // 1画素1バイト(0/255)
        const flate = await deflate(gray);        // zlib(FlateDecode)
        imgs.push({ flate, w, h });
      } else {
        imgs.push({ jpeg: dataUrlToBytes(cv.toDataURL("image/jpeg", 0.95)), w, h });
      }
    }
    const bytes = buildPdf(imgs);
    const name = ($("fname").value || "楽譜").trim() + ".pdf";
    downloadBytes(bytes, name);
    setStatus(null);
  } catch (err) {
    console.error(err);
    setStatus("PDF作成でエラーが発生しました");
  }
});

/* Canvasから1画素1バイトのグレー値配列を取り出す */
function canvasToGray(cv) {
  const ctx = cv.getContext("2d");
  const d = ctx.getImageData(0, 0, cv.width, cv.height).data;
  const n = cv.width * cv.height;
  const gray = new Uint8Array(n);
  for (let i = 0, j = 0; i < n; i++, j += 4) gray[i] = d[j]; // R=G=B
  return gray;
}

/* zlib(deflate)圧縮。PDFの /FlateDecode が期待する形式。 */
async function deflate(bytes) {
  const cs = new CompressionStream("deflate");
  const writer = cs.writable.getWriter();
  writer.write(bytes);
  writer.close();
  const buf = await new Response(cs.readable).arrayBuffer();
  return new Uint8Array(buf);
}

function dataUrlToBytes(dataUrl) {
  const b64 = dataUrl.split(",")[1];
  const bin = atob(b64);
  const arr = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
  return arr;
}

function downloadBytes(bytes, filename) {
  const blob = new Blob([bytes], { type: "application/pdf" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url; a.download = filename;
  document.body.appendChild(a);
  a.click();
  setTimeout(() => { document.body.removeChild(a); URL.revokeObjectURL(url); }, 4000);
}

/* --- 最小PDFライター: 各ページ = A4縦に収まるようアスペクト維持で配置 --- */
function buildPdf(imgs) {
  const A4 = { w: 595.28, h: 841.89 }; // ポイント
  const parts = [];       // {bytes:Uint8Array} の配列（連結してファイル化）
  const offsets = [];     // 各オブジェクトのバイト開始位置
  let length = 0;
  const enc = new TextEncoder();
  const push = (data) => {
    const b = typeof data === "string" ? enc.encode(data) : data;
    parts.push(b); length += b.length; return b.length;
  };

  push("%PDF-1.4\n%\xE2\xE3\xCF\xD3\n");

  // オブジェクト番号割当: 1=Catalog, 2=Pages, 以降ページ毎に (Page, Content, Image)
  const nPages = imgs.length;
  const pageObjIds = [], contentObjIds = [], imageObjIds = [];
  let next = 3;
  for (let i = 0; i < nPages; i++) {
    pageObjIds.push(next++); contentObjIds.push(next++); imageObjIds.push(next++);
  }
  const totalObjs = next - 1;

  const startObj = (id) => { offsets[id] = length; push(id + " 0 obj\n"); };
  const endObj = () => { push("endobj\n"); };

  // 1: Catalog
  startObj(1); push("<< /Type /Catalog /Pages 2 0 R >>\n"); endObj();

  // 2: Pages
  startObj(2);
  push("<< /Type /Pages /Count " + nPages + " /Kids [" +
       pageObjIds.map((id) => id + " 0 R").join(" ") + "] >>\n");
  endObj();

  // 各ページ
  for (let i = 0; i < nPages; i++) {
    const im = imgs[i];
    // A4縦に収まるスケール（アスペクト維持, 中央配置）
    const s = Math.min(A4.w / im.w, A4.h / im.h);
    const dw = im.w * s, dh = im.h * s;
    const ox = (A4.w - dw) / 2, oy = (A4.h - dh) / 2;

    // Page
    startObj(pageObjIds[i]);
    push("<< /Type /Page /Parent 2 0 R /MediaBox [0 0 " + A4.w.toFixed(2) + " " + A4.h.toFixed(2) + "] " +
         "/Resources << /XObject << /Im0 " + imageObjIds[i] + " 0 R >> >> " +
         "/Contents " + contentObjIds[i] + " 0 R >>\n");
    endObj();

    // Content（画像を配置する描画命令）
    const content = "q\n" + dw.toFixed(2) + " 0 0 " + dh.toFixed(2) + " " +
                    ox.toFixed(2) + " " + oy.toFixed(2) + " cm\n/Im0 Do\nQ\n";
    const contentBytes = enc.encode(content);
    startObj(contentObjIds[i]);
    push("<< /Length " + contentBytes.length + " >>\nstream\n");
    push(contentBytes);
    push("\nendstream\n");
    endObj();

    // Image: 可逆(FlateDecode/グレー) か JPEG(DCTDecode) を埋め込み
    startObj(imageObjIds[i]);
    if (im.flate) {
      push("<< /Type /XObject /Subtype /Image /Width " + im.w + " /Height " + im.h +
           " /ColorSpace /DeviceGray /BitsPerComponent 8 /Filter /FlateDecode /Length " +
           im.flate.length + " >>\nstream\n");
      push(im.flate);
    } else {
      push("<< /Type /XObject /Subtype /Image /Width " + im.w + " /Height " + im.h +
           " /ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length " +
           im.jpeg.length + " >>\nstream\n");
      push(im.jpeg);
    }
    push("\nendstream\n");
    endObj();
  }

  // xref
  const xrefStart = length;
  push("xref\n");
  push("0 " + (totalObjs + 1) + "\n");
  push("0000000000 65535 f \n");
  for (let id = 1; id <= totalObjs; id++) {
    const off = offsets[id] || 0;
    push(String(off).padStart(10, "0") + " 00000 n \n");
  }
  push("trailer\n<< /Size " + (totalObjs + 1) + " /Root 1 0 R >>\n");
  push("startxref\n" + xrefStart + "\n%%EOF\n");

  // 連結
  const result = new Uint8Array(length);
  let pos = 0;
  for (const b of parts) { result.set(b, pos); pos += b.length; }
  return result;
}

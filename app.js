/* ============================================================
 * MiniPS — 网页版图像编辑器
 * 纯前端实现：图层 / 选区(选框·套索·多边形·魔棒) / 画笔 / 橡皮擦
 * 油漆桶 / 吸管 / 文字 / 形状 / 裁剪 / 调整滤镜 / 撤销重做
 * 导入导出 PNG·JPEG / 工程文件(.psx)
 * ============================================================ */
'use strict';

/* ---------------- 小工具 ---------------- */
const $ = s => document.querySelector(s);

function el(tag, attrs, ...kids) {
  const n = document.createElement(tag);
  if (attrs) for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') n.className = v;
    else if (k === 'style') n.style.cssText = v;
    else if (k.startsWith('on')) n.addEventListener(k.slice(2), v);
    else if (k === 'html') n.innerHTML = v;
    else n.setAttribute(k, v);
  }
  for (const kid of kids) {
    if (kid == null) continue;
    n.append(kid.nodeType ? kid : document.createTextNode(kid));
  }
  return n;
}
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const pad2 = n => String(n).padStart(2, '0');

function hexToRgb(hex) {
  let h = hex.replace('#', '');
  if (h.length === 3) h = h.split('').map(c => c + c).join('');
  const n = parseInt(h, 16);
  return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}
function hexToRgba(hex, a) {
  const [r, g, b] = hexToRgb(hex);
  return `rgba(${r},${g},${b},${a === undefined ? 1 : a})`;
}
function mkCanvas(w, h) { const c = document.createElement('canvas'); c.width = w; c.height = h; return c; }
function cloneCanvas(cv) { const c = mkCanvas(cv.width, cv.height); c.getContext('2d').drawImage(cv, 0, 0); return c; }
function trimCanvas(cv) {
  const w = cv.width, h = cv.height;
  const d = cv.getContext('2d', { willReadFrequently: true }).getImageData(0, 0, w, h).data;
  let x0 = w, y0 = h, x1 = -1, y1 = -1;
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    if (d[(y * w + x) * 4 + 3] > 0) {
      if (x < x0) x0 = x; if (x > x1) x1 = x;
      if (y < y0) y0 = y; if (y > y1) y1 = y;
    }
  }
  if (x1 < 0) return null;
  const out = mkCanvas(x1 - x0 + 1, y1 - y0 + 1);
  out.getContext('2d').drawImage(cv, x0, y0, x1 - x0 + 1, y1 - y0 + 1, 0, 0, x1 - x0 + 1, y1 - y0 + 1);
  return { canvas: out, x: x0, y: y0, w: out.width, h: out.height };
}
function loadImage(src) {
  return new Promise((res, rej) => {
    const img = new Image();
    img.onload = () => res(img);
    img.onerror = rej;
    img.src = src;
  });
}
function fileToDataURL(file) {
  return new Promise((res, rej) => {
    const r = new FileReader();
    r.onload = () => res(r.result);
    r.onerror = rej;
    r.readAsDataURL(file);
  });
}
function download(blob, name) {
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = name;
  a.click();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000);
}
function timestamp() {
  const d = new Date();
  return `${d.getFullYear()}${pad2(d.getMonth() + 1)}${pad2(d.getDate())}-${pad2(d.getHours())}${pad2(d.getMinutes())}${pad2(d.getSeconds())}`;
}
let toastTimer = null;
function toast(msg) {
  let t = $('#toast');
  if (!t) { t = el('div', { id: 'toast' }); document.body.append(t); }
  t.textContent = msg;
  t.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('show'), 2200);
}

/* ---------------- 全局状态 ---------------- */
const state = {
  w: 800, h: 600,
  layers: [], activeIdx: 0,
  tool: 'move',
  fg: '#000000', bg: '#ffffff',
  zoom: 1, panX: 0, panY: 0,
  brush: { size: 24, hardness: 100, flow: 100 },
  eraser: { size: 30, hardness: 100 },
  wand: { tol: 32, contiguous: true },
  fill: { tol: 32 },
  shape: { kind: 'rect', hollow: false },
  text: { size: 48, font: 'sans-serif' },
  sel: null,          // { mask: canvas, path: Path2D }
  clipboard: null,    // { canvas, x, y, w, h }
  crop: null,         // {x,y,w,h}
  mouse: null,        // 光标所在文档坐标
};
let preview = null;   // 拖拽中的临时预览 {kind:'rect'|'poly'|'shape', ...}
let poly = null;      // 多边形套索进行中 {pts, mode}
let spaceDown = false;
let textEditorOpen = false;

const history = { stack: [], idx: -1, max: 20, liveStored: false };
let restoring = false;

const composite = $('#composite'), compCtx = composite.getContext('2d', { willReadFrequently: true });
const overlay = $('#overlay'), ovCtx = overlay.getContext('2d');
const stage = $('#stage'), area = $('#canvas-area');

/* ---------------- 图层 ---------------- */
let LAYER_SEQ = 1;
class Layer {
  constructor(w, h, name) {
    this.id = 'L' + (LAYER_SEQ++);
    this.name = name || ('图层 ' + LAYER_SEQ);
    this.canvas = mkCanvas(w, h);
    this.ctx = this.canvas.getContext('2d', { willReadFrequently: true });
    this.visible = true;
    this.opacity = 1;
    this.blend = 'source-over';
  }
  clone(nameSuffix) {
    const l = new Layer(state.w, state.h, this.name + (nameSuffix || ' 副本'));
    l.ctx.drawImage(this.canvas, 0, 0);
    l.visible = this.visible; l.opacity = this.opacity; l.blend = this.blend;
    return l;
  }
}
function activeLayer() { return state.layers[state.activeIdx] || null; }
function ensureActive() {
  if (!activeLayer()) addLayerObj(new Layer(state.w, state.h, '图层 1'), 0);
  return activeLayer();
}
function addLayerObj(layer, idx) {
  state.layers.splice(idx === undefined ? state.activeIdx + 1 : idx, 0, layer);
  state.activeIdx = state.layers.indexOf(layer);
  return layer;
}
function addLayer(name) { return addLayerObj(new Layer(state.w, state.h, name)); }

/* ---------------- 文档尺寸与视图 ---------------- */
function setDocSize(w, h) {
  state.w = w; state.h = h;
  composite.width = overlay.width = w;
  composite.height = overlay.height = h;
  stage.style.width = w + 'px';
  stage.style.height = h + 'px';
  $('#status-doc').textContent = `${w} × ${h} 像素`;
}
function applyView() {
  stage.style.transform = `translate(${state.panX}px,${state.panY}px) scale(${state.zoom})`;
  $('#zoom-label').textContent = Math.round(state.zoom * 100) + '%';
  composite.classList.toggle('pix', state.zoom >= 3);
  requestRender();
}
function setZoom(z, cx, cy) {
  z = clamp(z, 0.05, 16);
  const r = area.getBoundingClientRect();
  const ax = (cx === undefined ? r.width / 2 : cx - r.left);
  const ay = (cy === undefined ? r.height / 2 : cy - r.top);
  const dx = (ax - state.panX) / state.zoom, dy = (ay - state.panY) / state.zoom;
  state.zoom = z;
  state.panX = ax - dx * z;
  state.panY = ay - dy * z;
  applyView();
}
function fitView() {
  const r = area.getBoundingClientRect();
  const z = clamp(Math.min((r.width - 60) / state.w, (r.height - 60) / state.h), 0.05, 4);
  state.zoom = z;
  state.panX = (r.width - state.w * z) / 2;
  state.panY = (r.height - state.h * z) / 2;
  applyView();
}
function toDoc(e) {
  const r = composite.getBoundingClientRect();
  return {
    x: (e.clientX - r.left) * state.w / r.width,
    y: (e.clientY - r.top) * state.h / r.height,
  };
}

/* ---------------- 渲染 ---------------- */
let rafPending = false;
function requestRender() {
  if (rafPending) return;
  rafPending = true;
  requestAnimationFrame(() => { rafPending = false; renderDoc(); renderOverlay(); });
}
function renderDoc() {
  compCtx.setTransform(1, 0, 0, 1, 0, 0);
  compCtx.clearRect(0, 0, state.w, state.h);
  for (const l of state.layers) {
    if (!l.visible || l.opacity === 0) continue;
    compCtx.globalAlpha = l.opacity;
    compCtx.globalCompositeOperation = l.blend || 'source-over';
    compCtx.drawImage(l.canvas, 0, 0);
  }
  compCtx.globalAlpha = 1;
  compCtx.globalCompositeOperation = 'source-over';
}
function renderOverlay() {
  ovCtx.setTransform(1, 0, 0, 1, 0, 0);
  ovCtx.clearRect(0, 0, state.w, state.h);
  const z = state.zoom;
  const dash = a => { ovCtx.setLineDash([5 / z, 5 / z]); ovCtx.lineDashOffset = a / z; };
  // 裁剪框
  if (state.crop) {
    const c = state.crop;
    const p = new Path2D();
    p.rect(0, 0, state.w, state.h);
    p.rect(c.x, c.y, c.w, c.h);
    ovCtx.fillStyle = 'rgba(0,0,0,.55)';
    ovCtx.fill(p, 'evenodd');
    ovCtx.lineWidth = 1 / z;
    ovCtx.strokeStyle = '#fff';
    dash(0); ovCtx.strokeRect(c.x, c.y, c.w, c.h); ovCtx.setLineDash([]);
  }
  // 选区蚂蚁线
  if (state.sel && state.sel.path) {
    ovCtx.lineWidth = 1 / z;
    ovCtx.strokeStyle = '#000'; dash(state.antsPhase); ovCtx.stroke(state.sel.path);
    ovCtx.strokeStyle = '#fff'; dash(state.antsPhase + 5); ovCtx.stroke(state.sel.path);
    ovCtx.setLineDash([]);
  }
  // 拖拽预览
  if (preview) {
    ovCtx.lineWidth = 1 / z;
    ovCtx.strokeStyle = '#000'; dash(0);
    if (preview.kind === 'rect') {
      ovCtx.strokeRect(preview.x, preview.y, preview.w, preview.h);
      ovCtx.strokeStyle = '#fff'; dash(4); ovCtx.strokeRect(preview.x, preview.y, preview.w, preview.h);
    } else if (preview.kind === 'poly' && preview.pts.length) {
      const pts = preview.cursor ? preview.pts.concat([preview.cursor]) : preview.pts;
      ovCtx.beginPath();
      ovCtx.moveTo(pts[0].x, pts[0].y);
      for (let i = 1; i < pts.length; i++) ovCtx.lineTo(pts[i].x, pts[i].y);
      if (preview.close) ovCtx.closePath();
      ovCtx.stroke();
      ovCtx.strokeStyle = '#fff'; dash(4); ovCtx.stroke();
    } else if (preview.kind === 'shape') {
      drawShapePath(ovCtx, preview, true);
      ovCtx.strokeStyle = '#fff'; dash(4); ovCtx.stroke();
    }
    ovCtx.setLineDash([]);
  }
  // 画笔/橡皮光标圈
  if ((state.tool === 'brush' || state.tool === 'eraser') && state.mouse) {
    const r = (state.tool === 'brush' ? state.brush.size : state.eraser.size) / 2;
    ovCtx.lineWidth = 1 / z;
    ovCtx.strokeStyle = 'rgba(0,0,0,.8)';
    ovCtx.beginPath(); ovCtx.arc(state.mouse.x, state.mouse.y, r, 0, Math.PI * 2); ovCtx.stroke();
    ovCtx.strokeStyle = 'rgba(255,255,255,.9)';
    ovCtx.beginPath(); ovCtx.arc(state.mouse.x, state.mouse.y, r - 1 / z, 0, Math.PI * 2); ovCtx.stroke();
  }
}
setInterval(() => {
  if (state.sel) { state.antsPhase = ((state.antsPhase || 0) + 1) % 10; requestRender(); }
}, 110);

/* ---------------- 选区 ---------------- */
function getSelMask() {
  if (!state.sel) {
    const cv = mkCanvas(state.w, state.h);
    state.sel = { mask: cv, path: null };
  }
  return state.sel.mask;
}
function clearSelection() {
  if (state.sel) { state.sel = null; requestRender(); }
}
function shapeCanvasFrom(draw) {
  const cv = mkCanvas(state.w, state.h);
  draw(cv.getContext('2d'));
  return cv;
}
function applyMaskShape(cv, mode) {
  if (mode === 'sub' && !state.sel) return;
  const m = getSelMask();
  const c = m.getContext('2d', { willReadFrequently: true });
  if (mode === 'replace') c.clearRect(0, 0, state.w, state.h);
  if (mode === 'sub') c.globalCompositeOperation = 'destination-out';
  c.drawImage(cv, 0, 0);
  c.globalCompositeOperation = 'source-over';
  retraceSelection();
}
function selectionMaskFromBool(bool) {
  return shapeCanvasFrom(c => {
    const id = c.createImageData(state.w, state.h);
    for (let i = 0; i < bool.length; i++) if (bool[i]) id.data[i * 4 + 3] = 255;
    c.putImageData(id, 0, 0);
  });
}
function selectAll() { applyMaskShape(shapeCanvasFrom(c => c.fillRect(0, 0, state.w, state.h)), 'replace'); }
function invertSelection() {
  if (!state.sel) { selectAll(); return; }
  const inv = shapeCanvasFrom(c => {
    c.fillStyle = '#fff';
    c.fillRect(0, 0, state.w, state.h);
    c.globalCompositeOperation = 'destination-out';
    c.drawImage(state.sel.mask, 0, 0);
  });
  applyMaskShape(inv, 'replace');
}
/* 从蒙版描出选区轮廓（Moore 邻域跟踪），生成 Path2D 供蚂蚁线与裁剪 */
function retraceSelection() {
  if (!state.sel) { requestRender(); return; }
  const w = state.w, h = state.h, N = w * h;
  const d = state.sel.mask.getContext('2d', { willReadFrequently: true }).getImageData(0, 0, w, h).data;
  const A = new Uint8Array(N);
  for (let i = 0; i < N; i++) A[i] = d[i * 4 + 3] > 127 ? 1 : 0;
  const S = (x, y) => (x >= 0 && y >= 0 && x < w && y < h) ? A[y * w + x] : 0;
  const visited = new Uint8Array(N);
  const NB = [[1, 0], [1, 1], [0, 1], [-1, 1], [-1, 0], [-1, -1], [0, -1], [1, -1]]; // 顺时针
  const path = new Path2D();
  let loops = 0;
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const i = y * w + x;
    if (!A[i] || visited[i]) continue;
    if (!(!S(x + 1, y) || !S(x - 1, y) || !S(x, y + 1) || !S(x, y - 1))) continue; // 仅边界像素
    if (S(x - 1, y)) continue; // 以「左侧为外部」的像素作为起点
    let cx = x, cy = y, bx = x - 1, by = y;
    let guard = N;
    path.moveTo(x + 0.5, y + 0.5);
    do {
      visited[cy * w + cx] = 1;
      let bi = 0;
      for (let k = 0; k < 8; k++) if (NB[k][0] === bx - cx && NB[k][1] === by - cy) { bi = k; break; }
      let nx = -1, ny = -1, found = false;
      for (let k = 1; k <= 8; k++) {
        const idx = (bi + k) % 8;
        if (S(cx + NB[idx][0], cy + NB[idx][1])) {
          nx = cx + NB[idx][0]; ny = cy + NB[idx][1];
          const pb = NB[(bi + k - 1 + 8) % 8];
          bx = cx + pb[0]; by = cy + pb[1];
          found = true; break;
        }
      }
      if (!found) break;
      path.lineTo(nx + 0.5, ny + 0.5);
      cx = nx; cy = ny;
    } while ((cx !== x || cy !== y) && --guard > 0);
    path.closePath();
    loops++;
    if (loops > 4000) break; // 防御极端噪点选区
  }
  if (!loops) state.sel = null;
  else state.sel.path = path;
  requestRender();
}
/* 泛洪：返回与 (sx,sy) 颜色相近的像素布尔阵 */
function floodBool(d, sx, sy, tol, contiguous) {
  const w = state.w, h = state.h, N = w * h;
  const out = new Uint8Array(N);
  sx = sx | 0; sy = sy | 0;
  if (sx < 0 || sy < 0 || sx >= w || sy >= h) return out;
  const si = sy * w + sx;
  const r0 = d[si * 4], g0 = d[si * 4 + 1], b0 = d[si * 4 + 2], a0 = d[si * 4 + 3];
  const T = tol * 4;
  const match = i => {
    const q = i * 4;
    return Math.abs(d[q] - r0) + Math.abs(d[q + 1] - g0) + Math.abs(d[q + 2] - b0) + Math.abs(d[q + 3] - a0) <= T;
  };
  if (!contiguous) {
    for (let i = 0; i < N; i++) if (match(i)) out[i] = 1;
    return out;
  }
  const stack = [si];
  out[si] = 1;
  while (stack.length) {
    const i = stack.pop();
    const x = i % w, y = (i / w) | 0;
    if (x > 0 && !out[i - 1] && match(i - 1)) { out[i - 1] = 1; stack.push(i - 1); }
    if (x < w - 1 && !out[i + 1] && match(i + 1)) { out[i + 1] = 1; stack.push(i + 1); }
    if (y > 0 && !out[i - w] && match(i - w)) { out[i - w] = 1; stack.push(i - w); }
    if (y < h - 1 && !out[i + w] && match(i + w)) { out[i + w] = 1; stack.push(i + w); }
  }
  return out;
}

/* ---------------- 工具实现 ---------------- */
let drag = null;

function normRect(d) {
  return { x: Math.min(d.x0, d.x1), y: Math.min(d.y0, d.y1), w: Math.abs(d.x1 - d.x0), h: Math.abs(d.y1 - d.y0) };
}

/* --- 移动 --- */
function startMove(p) {
  const L = ensureActive();
  pushHistory();
  const snap = cloneCanvas(L.canvas);
  let floatCv = null, mask0 = null;
  if (state.sel) {
    mask0 = cloneCanvas(state.sel.mask);
    floatCv = mkCanvas(state.w, state.h);
    const fc = floatCv.getContext('2d');
    fc.drawImage(mask0, 0, 0);
    fc.globalCompositeOperation = 'source-in';
    fc.drawImage(snap, 0, 0);
  }
  drag = { kind: 'move', sx: p.x, sy: p.y, layer: L, snap, float: floatCv, mask0, dx: 0, dy: 0 };
}
function moveMove(p) {
  drag.dx = Math.round(p.x - drag.sx);
  drag.dy = Math.round(p.y - drag.sy);
  const c = drag.layer.ctx;
  c.setTransform(1, 0, 0, 1, 0, 0);
  c.globalCompositeOperation = 'source-over';
  c.globalAlpha = 1;
  c.clearRect(0, 0, state.w, state.h);
  if (drag.float) {
    // 有选区：底层内容留在原地，仅挖空选区并把选中像素搬到新位置
    c.drawImage(drag.snap, 0, 0);
    c.globalCompositeOperation = 'destination-out';
    c.drawImage(drag.mask0, 0, 0);
    c.globalCompositeOperation = 'source-over';
    c.drawImage(drag.float, drag.dx, drag.dy);
  } else {
    // 无选区：整层平移
    c.drawImage(drag.snap, drag.dx, drag.dy);
  }
  requestRender();
}
function endMove(d) {
  if (d.float && (d.dx || d.dy)) {
    const nm = mkCanvas(state.w, state.h);
    nm.getContext('2d').drawImage(d.mask0, d.dx, d.dy);
    state.sel.mask = nm;
    retraceSelection();
  }
  updateThumb(d.layer);
  requestRender();
}

/* --- 画笔 / 橡皮擦 --- */
function startStroke(p, kind) {
  const L = ensureActive();
  pushHistory();
  drag = { kind: 'stroke', brushKind: kind, layer: L, last: p };
  paintSegment(L, p, { x: p.x + 0.01, y: p.y + 0.01 }, kind);
  requestRender();
}
function strokeTo(p) {
  paintSegment(drag.layer, drag.last, p, drag.brushKind);
  drag.last = p;
  requestRender();
}
function paintSegment(L, a, b, kind) {
  const st = kind === 'brush' ? state.brush : state.eraser;
  const c = L.ctx;
  const r = Math.max(0.5, st.size / 2);
  c.save();
  if (state.sel) c.clip(state.sel.path, 'evenodd');
  c.globalCompositeOperation = kind === 'eraser' ? 'destination-out' : 'source-over';
  const color = kind === 'eraser' ? '#000000' : state.fg;
  if (kind === 'brush') c.globalAlpha = state.brush.flow / 100;
  if (st.hardness >= 100) {
    c.strokeStyle = color;
    c.lineWidth = st.size;
    c.lineCap = 'round';
    c.lineJoin = 'round';
    c.beginPath();
    c.moveTo(a.x, a.y);
    c.lineTo(b.x, b.y);
    c.stroke();
  } else {
    const dist = Math.hypot(b.x - a.x, b.y - a.y);
    const n = Math.max(1, Math.ceil(dist / Math.max(0.5, r * 0.18)));
    for (let i = 0; i <= n; i++) {
      const t = i / n;
      const x = a.x + (b.x - a.x) * t, y = a.y + (b.y - a.y) * t;
      const g = c.createRadialGradient(x, y, r * st.hardness / 100, x, y, r);
      g.addColorStop(0, color);
      g.addColorStop(1, hexToRgba(color, 0));
      c.fillStyle = g;
      c.beginPath();
      c.arc(x, y, r, 0, Math.PI * 2);
      c.fill();
    }
  }
  c.restore();
}
function endStroke(d) { updateThumb(d.layer); }

/* --- 油漆桶 --- */
function bucketAt(p) {
  if (p.x < 0 || p.y < 0 || p.x >= state.w || p.y >= state.h) return;
  const L = ensureActive();
  pushHistory();
  const d = L.ctx.getImageData(0, 0, state.w, state.h).data;
  const bool = floodBool(d, p.x, p.y, state.fill.tol, true);
  applyBoolColor(L, bool, state.fg);
  requestRender();
  renderLayersPanel();
}
function applyBoolColor(L, bool, color) {
  const shape = shapeCanvasFrom(c => {
    const [r, g, b] = hexToRgb(color);
    const id = c.createImageData(state.w, state.h);
    for (let i = 0; i < bool.length; i++) if (bool[i]) {
      id.data[i * 4] = r; id.data[i * 4 + 1] = g; id.data[i * 4 + 2] = b; id.data[i * 4 + 3] = 255;
    }
    c.putImageData(id, 0, 0);
  });
  L.ctx.save();
  if (state.sel) L.ctx.clip(state.sel.path, 'evenodd');
  L.ctx.drawImage(shape, 0, 0);
  L.ctx.restore();
}

/* --- 魔棒 --- */
function wandAt(p, e) {
  if (p.x < 0 || p.y < 0 || p.x >= state.w || p.y >= state.h) return;
  const mode = e.shiftKey ? 'add' : (e.altKey ? 'sub' : 'replace');
  const d = compCtx.getImageData(0, 0, state.w, state.h).data;
  const bool = floodBool(d, p.x, p.y, state.wand.tol, state.wand.contiguous);
  applyMaskShape(selectionMaskFromBool(bool), mode);
}

/* --- 吸管 --- */
function pickAt(p, e) {
  if (p.x < 0 || p.y < 0 || p.x >= state.w || p.y >= state.h) return;
  const d = compCtx.getImageData(Math.floor(p.x), Math.floor(p.y), 1, 1).data;
  const hex = '#' + [d[0], d[1], d[2]].map(v => v.toString(16).padStart(2, '0')).join('');
  if (e.altKey) { state.bg = hex; $('#bg-input').value = hex; }
  else { state.fg = hex; $('#fg-input').value = hex; }
  updateSwatches();
  requestRender();
}

/* --- 形状 --- */
function startShape(p, e) {
  drag = { kind: 'shape', x0: p.x, y0: p.y, x1: p.x, y1: p.y, square: e.shiftKey };
  preview = { kind: 'shape', x: p.x, y: p.y, w: 0, h: 0 };
}
function updateShapePreview() {
  const r = normRect(drag);
  let rr = { x: r.x, y: r.y, w: r.w, h: r.h };
  if (drag.square && r.w && r.h) {
    const s = Math.max(r.w, r.h);
    rr = { x: drag.x0, y: drag.y0, w: (drag.x1 >= drag.x0 ? s : -s), h: (drag.y1 >= drag.y0 ? s : -s) };
    rr = { x: Math.min(rr.x, rr.x + rr.w), y: Math.min(rr.y, rr.y + rr.h), w: Math.abs(rr.w), h: Math.abs(rr.h) };
  }
  Object.assign(preview, rr);
}
function drawShapePath(c, r, dashed) {
  c.strokeStyle = dashed ? '#000' : state.fg;
  c.fillStyle = state.fg;
  if (!dashed) c.lineWidth = state.brush.size;
  if (state.shape.kind === 'rect') {
    if (state.shape.hollow && !dashed) c.strokeRect(r.x, r.y, r.w, r.h);
    else c.fillRect(r.x, r.y, r.w, r.h);
  } else {
    c.beginPath();
    c.ellipse(r.x + r.w / 2, r.y + r.h / 2, Math.abs(r.w / 2), Math.abs(r.h / 2), 0, 0, Math.PI * 2);
    if (state.shape.hollow && !dashed) c.stroke();
    else c.fill();
  }
}
function commitShape() {
  const r = preview;
  if (r.w >= 1 && r.h >= 1) {
    const L = ensureActive();
    pushHistory();
    L.ctx.save();
    if (state.sel) L.ctx.clip(state.sel.path, 'evenodd');
    drawShapePath(L.ctx, r, false);
    L.ctx.restore();
    updateThumb(L);
  }
  preview = null;
  requestRender();
}

/* --- 裁剪 --- */
function startCrop(p) {
  state.crop = null;
  drag = { kind: 'crop', x0: p.x, y0: p.y, x1: p.x, y1: p.y };
  preview = null;
}
function updateCrop(d) {
  const r = normRect(d);
  state.crop = r.w > 3 && r.h > 3 ? r : null;
}
function applyCrop() {
  const c = state.crop;
  if (!c || c.w < 4 || c.h < 4) { state.crop = null; requestRender(); return; }
  pushHistory();
  const x = Math.round(c.x), y = Math.round(c.y), w = Math.round(c.w), h = Math.round(c.h);
  for (const L of state.layers) {
    const nc = mkCanvas(w, h);
    nc.getContext('2d').drawImage(L.canvas, -x, -y);
    L.canvas = nc;
    L.ctx = nc.getContext('2d', { willReadFrequently: true });
  }
  state.crop = null;
  clearSelection();
  setDocSize(w, h);
  fitView();
  renderLayersPanel();
  requestRender();
  toast('裁剪已应用');
}

/* --- 文字 --- */
const textEditor = $('#text-editor');
function placeText(p) {
  commitText();
  textEditorOpen = true;
  textEditor.hidden = false;
  textEditor.textContent = '';
  textEditor.style.left = Math.round(p.x) + 'px';
  textEditor.style.top = Math.round(p.y) + 'px';
  textEditor.style.fontSize = state.text.size + 'px';
  textEditor.style.fontFamily = state.text.font;
  textEditor.style.color = state.fg;
  setTimeout(() => textEditor.focus(), 0);
}
function commitText() {
  if (!textEditorOpen) return;
  const txt = textEditor.textContent.replace(/\n$/, '');
  textEditorOpen = false;
  textEditor.hidden = true;
  textEditor.textContent = '';
  textEditor.blur();
  if (!txt.trim()) return;
  const L = ensureActive();
  pushHistory();
  const c = L.ctx;
  c.save();
  if (state.sel) c.clip(state.sel.path, 'evenodd');
  c.fillStyle = state.fg;
  c.textBaseline = 'top';
  c.font = `${state.text.size}px ${state.text.font}`;
  const lines = txt.split('\n');
  const lh = state.text.size * 1.3;
  const x = parseFloat(textEditor.style.left), y = parseFloat(textEditor.style.top);
  lines.forEach((line, i) => c.fillText(line, x, y + i * lh));
  c.restore();
  updateThumb(L);
  requestRender();
}
textEditor.addEventListener('pointerdown', e => e.stopPropagation());
textEditor.addEventListener('keydown', e => {
  e.stopPropagation();
  if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); commitText(); }
  if (e.key === 'Escape') { textEditor.textContent = ''; commitText(); }
});
textEditor.addEventListener('blur', () => commitText());

/* ---------------- 指针交互 ---------------- */
area.addEventListener('contextmenu', e => e.preventDefault());

function handleDown(e) {
  if (e.target.closest && e.target.closest('.modal-mask')) return;
  if (textEditorOpen) { commitText(); return; }
  const p = toDoc(e);
  try { area.setPointerCapture(e.pointerId); } catch (_) { /* 合成事件可能没有活动指针 */ }
  closePolyIfNeeded();

  if (spaceDown || e.button === 1 || state.tool === 'hand') {
    drag = { kind: 'pan', sx: e.clientX, sy: e.clientY, px: state.panX, py: state.panY };
    area.classList.add('grabbing');
    return;
  }
  if (state.tool === 'zoom') {
    setZoom(e.altKey ? state.zoom / 1.5 : state.zoom * 1.5, e.clientX, e.clientY);
    return;
  }
  switch (state.tool) {
    case 'move': startMove(p); break;
    case 'marquee':
      drag = {
        kind: 'marquee', x0: p.x, y0: p.y, x1: p.x, y1: p.y,
        mode: e.shiftKey ? 'add' : (e.altKey ? 'sub' : 'replace'),
      };
      preview = { kind: 'rect', x: p.x, y: p.y, w: 0, h: 0 };
      break;
    case 'lasso':
      drag = {
        kind: 'lasso', pts: [p],
        mode: e.shiftKey ? 'add' : (e.altKey ? 'sub' : 'replace'),
      };
      preview = { kind: 'poly', pts: drag.pts };
      break;
    case 'polylasso': polyAddPoint(p, e); break;
    case 'wand': wandAt(p, e); break;
    case 'brush': startStroke(p, 'brush'); break;
    case 'eraser': startStroke(p, 'eraser'); break;
    case 'bucket': bucketAt(p); break;
    case 'picker': pickAt(p, e); break;
    case 'text': placeText(p); break;
    case 'shape': startShape(p, e); break;
    case 'crop': startCrop(p); break;
  }
}

function handleMove(e) {
  const p = toDoc(e);
  state.mouse = p;
  $('#status-pos').textContent = `X: ${Math.floor(p.x)}   Y: ${Math.floor(p.y)}`;
  if (!drag) { requestRender(); return; }
  switch (drag.kind) {
    case 'pan':
      state.panX = drag.px + (e.clientX - drag.sx);
      state.panY = drag.py + (e.clientY - drag.sy);
      applyView();
      break;
    case 'move': moveMove(p); break;
    case 'marquee':
      drag.x1 = p.x; drag.y1 = p.y;
      Object.assign(preview, normRect(drag));
      requestRender();
      break;
    case 'lasso': {
      const last = drag.pts[drag.pts.length - 1];
      if (Math.hypot(p.x - last.x, p.y - last.y) > 1.2) drag.pts.push(p);
      requestRender();
      break;
    }
    case 'stroke': strokeTo(p); break;
    case 'shape':
      drag.x1 = p.x; drag.y1 = p.y;
      updateShapePreview();
      requestRender();
      break;
    case 'crop':
      drag.x1 = p.x; drag.y1 = p.y;
      updateCrop(drag);
      requestRender();
      break;
  }
}

function handleUp() {
  if (!drag) return;
  const d = drag;
  drag = null;
  area.classList.remove('grabbing');
  switch (d.kind) {
    case 'move': endMove(d); break;
    case 'marquee': {
      preview = null;
      const r = normRect(d);
      if (Math.round(r.w) < 1 && Math.round(r.h) < 1) clearSelection();
      else applyMaskShape(shapeCanvasFrom(c => c.fillRect(Math.round(r.x), Math.round(r.y), Math.round(r.w), Math.round(r.h))), d.mode);
      requestRender();
      break;
    }
    case 'lasso': {
      preview = null;
      if (d.pts.length >= 3) {
        const path = new Path2D();
        path.moveTo(d.pts[0].x, d.pts[0].y);
        for (let i = 1; i < d.pts.length; i++) path.lineTo(d.pts[i].x, d.pts[i].y);
        path.closePath();
        applyMaskShape(shapeCanvasFrom(c => c.fill(path, 'evenodd')), d.mode);
      }
      requestRender();
      break;
    }
    case 'stroke': endStroke(d); break;
    case 'shape': commitShape(); break;
    case 'crop': updateCrop(d); break;
  }
}

area.addEventListener('pointerleave', () => { state.mouse = null; requestRender(); });

/* pointer 事件为主，mouse 事件兜底（个别环境不派发 pointer 序列）。
 * 去重按事件类型分别计时：真实指针的 pointerdown 会紧跟 mousedown，
 * 只拦同类型的连续重复，避免无关的 pointermove 流误挡 mouse 手势。 */
const lastPointer = { down: 0, move: 0, up: 0 };
area.addEventListener('pointerdown', e => { lastPointer.down = performance.now(); handleDown(e); });
area.addEventListener('mousedown', e => { if (performance.now() - lastPointer.down > 50) handleDown(e); });
window.addEventListener('pointermove', e => { lastPointer.move = performance.now(); handleMove(e); });
window.addEventListener('mousemove', e => { if (performance.now() - lastPointer.move > 50) handleMove(e); });
window.addEventListener('pointerup', e => { lastPointer.up = performance.now(); handleUp(e); });
window.addEventListener('mouseup', e => { if (performance.now() - lastPointer.up > 50) handleUp(e); });

/* --- 多边形套索 --- */
function polyAddPoint(p, e) {
  if (!poly) poly = { pts: [], mode: e.shiftKey ? 'add' : (e.altKey ? 'sub' : 'replace') };
  if (poly.pts.length >= 3 && Math.hypot(p.x - poly.pts[0].x, p.y - poly.pts[0].y) < 8 / state.zoom) {
    polyClose();
    return;
  }
  const last = poly.pts[poly.pts.length - 1];
  if (last && Math.hypot(p.x - last.x, p.y - last.y) < 2) return;
  poly.pts.push(p);
  preview = { kind: 'poly', pts: poly.pts, cursor: p };
  requestRender();
}
function polyClose() {
  if (poly && poly.pts.length >= 3) {
    const path = new Path2D();
    path.moveTo(poly.pts[0].x, poly.pts[0].y);
    for (let i = 1; i < poly.pts.length; i++) path.lineTo(poly.pts[i].x, poly.pts[i].y);
    path.closePath();
    applyMaskShape(shapeCanvasFrom(c => c.fill(path, 'evenodd')), poly.mode);
  }
  poly = null;
  preview = null;
  requestRender();
}
function polyCancel() { poly = null; preview = null; requestRender(); }
function closePolyIfNeeded() { /* 点击新工具前先不动，Enter/双击才闭合 */ }

area.addEventListener('dblclick', () => { if (poly) polyClose(); });

/* ---------------- 滚轮 / 平移缩放 ---------------- */
area.addEventListener('wheel', e => {
  e.preventDefault();
  if (e.ctrlKey || e.metaKey || e.altKey) {
    const f = e.deltaY < 0 ? 1.12 : 1 / 1.12;
    setZoom(state.zoom * f, e.clientX, e.clientY);
  } else {
    state.panX -= (e.shiftKey ? e.deltaY : e.deltaX);
    state.panY -= (e.shiftKey ? 0 : e.deltaY);
    applyView();
  }
}, { passive: false });

/* ---------------- 历史记录（撤销 / 重做） ---------------- */
function serializeDoc() {
  return {
    w: state.w, h: state.h, active: state.activeIdx,
    layers: state.layers.map(l => ({
      name: l.name, visible: l.visible, opacity: l.opacity, blend: l.blend,
      data: l.canvas.toDataURL('image/png'),
    })),
  };
}
function pushHistory() {
  if (restoring) return;
  history.stack = history.stack.slice(0, history.idx + 1);
  history.stack.push(serializeDoc());
  if (history.stack.length > history.max) history.stack.shift();
  history.idx = history.stack.length - 1;
  history.liveStored = false;
}
async function restoreHistory(snap) {
  restoring = true;
  try {
    setDocSize(snap.w, snap.h);
    const layers = [];
    for (const s of snap.layers) {
      const l = new Layer(snap.w, snap.h, s.name);
      l.visible = s.visible; l.opacity = s.opacity; l.blend = s.blend;
      try {
        const img = await loadImage(s.data);
        l.ctx.drawImage(img, 0, 0);
      } catch (_) { /* 图片解码失败时保留空层 */ }
      layers.push(l);
    }
    state.layers = layers;
    state.activeIdx = clamp(snap.active, 0, layers.length - 1);
    clearSelection();
    state.crop = null;
    renderLayersPanel();
    updateBlendControls();
    requestRender();
  } finally {
    restoring = false;
  }
}
/* 快照为"每次操作前"捕获。live（当前画面）在首次撤销前是隐式的：
 * - 首次撤销：先把 live 存为栈顶，再回退到 stack[idx]（= 最后一次操作之前）
 * - 后续撤销：idx-- 逐个回退
 * - 重做：idx++ 依次前进，终点即当初补存的 live */
function doUndo() {
  if (history.idx < 0) { toast('没有可撤销的操作'); return; }
  if (!history.liveStored && history.idx === history.stack.length - 1) {
    history.liveStored = true;
    history.stack.push(serializeDoc());
    if (history.stack.length > history.max) history.stack.shift();
    restoreHistory(history.stack[history.idx]);
    return;
  }
  if (history.idx <= 0) { toast('没有可撤销的操作'); return; }
  history.idx--;
  restoreHistory(history.stack[history.idx]);
}
function doRedo() {
  if (history.idx >= history.stack.length - 1) { toast('没有可重做的操作'); return; }
  history.idx++;
  restoreHistory(history.stack[history.idx]);
}

/* ---------------- 编辑操作 ---------------- */
function copySel() {
  const L = activeLayer();
  if (!L) return;
  const t = cloneCanvas(L.canvas);
  if (state.sel) {
    const c = t.getContext('2d');
    c.globalCompositeOperation = 'destination-in';
    c.drawImage(state.sel.mask, 0, 0);
  }
  const trim = trimCanvas(t);
  state.clipboard = trim || { canvas: mkCanvas(1, 1), x: 0, y: 0, w: 1, h: 1 };
  toast('已复制');
}
function deleteSelPixels(withHistory) {
  const L = activeLayer();
  if (!L) return;
  if (withHistory) pushHistory();
  const c = L.ctx;
  c.save();
  if (state.sel) {
    c.globalCompositeOperation = 'destination-out';
    c.drawImage(state.sel.mask, 0, 0);
  } else {
    c.clearRect(0, 0, state.w, state.h);
  }
  c.restore();
  updateThumb(L);
  requestRender();
}
function cutSel() { pushHistory(); copySel(); deleteSelPixels(false); }
function pasteClip() {
  if (!state.clipboard) { toast('剪贴板为空'); return; }
  pushHistory();
  const L = addLayer('粘贴的图层');
  L.ctx.drawImage(state.clipboard.canvas,
    Math.round((state.w - state.clipboard.w) / 2),
    Math.round((state.h - state.clipboard.h) / 2));
  renderLayersPanel();
  requestRender();
}
function fillWith(color) {
  const L = ensureActive();
  pushHistory();
  L.ctx.save();
  if (state.sel) L.ctx.clip(state.sel.path, 'evenodd');
  L.ctx.fillStyle = color;
  L.ctx.fillRect(0, 0, state.w, state.h);
  L.ctx.restore();
  updateThumb(L);
  requestRender();
}

/* ---------------- 滤镜 / 调整 ---------------- */
function bakeFilter(L, filter) {
  if (!filter) return;
  const tmp = mkCanvas(state.w, state.h);
  const c = tmp.getContext('2d');
  c.filter = filter;
  c.drawImage(L.canvas, 0, 0);
  c.filter = 'none';
  L.ctx.save();
  if (state.sel) L.ctx.clip(state.sel.path, 'evenodd');
  L.ctx.clearRect(0, 0, state.w, state.h);
  L.ctx.drawImage(tmp, 0, 0);
  L.ctx.restore();
}
function adjustmentDialog(title, defs, buildFilter) {
  const L = ensureActive();
  const orig = cloneCanvas(L.canvas);
  const vals = {};
  const rows = defs.map(d => {
    vals[d.key] = d.value;
    const val = el('span', { class: 'opt-val' }, d.value + (d.unit || ''));
    const input = el('input', {
      type: 'range', min: d.min, max: d.max, step: d.step || 1, value: d.value,
      oninput: e => {
        vals[d.key] = +e.target.value;
        val.textContent = vals[d.key] + (d.unit || '');
        applyPreview();
      },
    });
    return el('div', { class: 'row' }, el('label', {}, d.label), input, val);
  });
  function applyPreview() {
    const f = buildFilter(vals);
    L.ctx.setTransform(1, 0, 0, 1, 0, 0);
    L.ctx.globalCompositeOperation = 'source-over';
    L.ctx.globalAlpha = 1;
    L.ctx.clearRect(0, 0, state.w, state.h);
    L.ctx.filter = f || 'none';
    L.ctx.drawImage(orig, 0, 0);
    L.ctx.filter = 'none';
    requestRender();
  }
  const previewCv = mkCanvas(Math.min(280, state.w), Math.round(Math.min(280, state.w) * state.h / state.w));
  const body = el('div', { class: 'modal-body' }, ...rows);
  openModal(title, body, [
    {
      label: '取消', action: close => {
        L.ctx.clearRect(0, 0, state.w, state.h);
        L.ctx.drawImage(orig, 0, 0);
        close();
        requestRender();
      },
    },
    {
      label: '应用', primary: true, action: close => {
        L.ctx.clearRect(0, 0, state.w, state.h);
        L.ctx.drawImage(orig, 0, 0);
        pushHistory();
        const f = buildFilter(vals);
        if (state.sel) {
          bakeFilter(L, f);
        } else {
          L.ctx.filter = f || 'none';
          L.ctx.drawImage(orig, 0, 0);
          L.ctx.filter = 'none';
        }
        close();
        updateThumb(L);
        requestRender();
      },
    },
  ]);
  applyPreview();
}
const adjustBrightnessContrast = () => adjustmentDialog('亮度 / 对比度',
  [
    { key: 'b', label: '亮度', min: -100, max: 100, value: 0 },
    { key: 'c', label: '对比度', min: -100, max: 100, value: 0 },
  ],
  v => `brightness(${100 + v.b}%) contrast(${100 + v.c}%)`);
const adjustHueSat = () => adjustmentDialog('色相 / 饱和度',
  [
    { key: 'h', label: '色相', min: -180, max: 180, value: 0, unit: '°' },
    { key: 's', label: '饱和度', min: -100, max: 100, value: 0 },
  ],
  v => `hue-rotate(${v.h}deg) saturate(${100 + v.s}%)`);
const adjustBlur = () => adjustmentDialog('高斯模糊',
  [{ key: 'r', label: '半径', min: 0, max: 40, value: 2, unit: 'px' }],
  v => `blur(${v.r}px)`);

function quickFilter(filter) {
  const L = ensureActive();
  pushHistory();
  bakeFilter(L, filter);
  updateThumb(L);
  requestRender();
}
const invertColors = () => quickFilter('invert(100%)');
const desaturate = () => quickFilter('grayscale(100%)');

/* ---------------- 图像 / 画布操作 ---------------- */
function rebuildLayers(w, h, transform) {
  for (const L of state.layers) {
    const nc = mkCanvas(w, h);
    const c = nc.getContext('2d');
    c.imageSmoothingQuality = 'high';
    transform(c, L.canvas);
    L.canvas = nc;
    L.ctx = nc.getContext('2d', { willReadFrequently: true });
  }
}
function imageSizeDialog() {
  const wIn = el('input', { type: 'number', min: 1, max: 6000, value: state.w });
  const hIn = el('input', { type: 'number', min: 1, max: 6000, value: state.h });
  const link = el('input', { type: 'checkbox', checked: true });
  const ratio = state.w / state.h;
  wIn.addEventListener('input', () => { if (link.checked && wIn.value) hIn.value = Math.max(1, Math.round(wIn.value / ratio)); });
  hIn.addEventListener('input', () => { if (link.checked && hIn.value) wIn.value = Math.max(1, Math.round(hIn.value * ratio)); });
  const body = el('div', { class: 'modal-body' },
    el('div', { class: 'row' }, el('label', {}, '宽度(像素)'), wIn),
    el('div', { class: 'row' }, el('label', {}, '高度(像素)'), hIn),
    el('div', { class: 'row' }, el('label', {}, '保持比例'), link));
  openModal('图像大小', body, [
    { label: '取消', action: c => c() },
    {
      label: '应用', primary: true, action: c => {
        const w = clamp(+wIn.value | 0, 1, 6000), h = clamp(+hIn.value | 0, 1, 6000);
        pushHistory();
        rebuildLayers(w, h, (ctx, old) => ctx.drawImage(old, 0, 0, w, h));
        clearSelection();
        setDocSize(w, h);
        fitView();
        renderLayersPanel();
        requestRender();
        c();
        toast(`图像已调整为 ${w} × ${h}`);
      },
    },
  ]);
}
function canvasSizeDialog() {
  const wIn = el('input', { type: 'number', min: 1, max: 6000, value: state.w });
  const hIn = el('input', { type: 'number', min: 1, max: 6000, value: state.h });
  const anchors = ['左上', '中上', '右上', '左中', '居中', '右中', '左下', '中下', '右下'];
  const anchorSel = el('select', {}, ...anchors.map(a => el('option', { value: a }, a)));
  anchorSel.value = '居中';
  const body = el('div', { class: 'modal-body' },
    el('div', { class: 'row' }, el('label', {}, '宽度(像素)'), wIn),
    el('div', { class: 'row' }, el('label', {}, '高度(像素)'), hIn),
    el('div', { class: 'row' }, el('label', {}, '定位'), anchorSel));
  openModal('画布大小', body, [
    { label: '取消', action: c => c() },
    {
      label: '应用', primary: true, action: c => {
        const w = clamp(+wIn.value | 0, 1, 6000), h = clamp(+hIn.value | 0, 1, 6000);
        const col = ['左', '中', '右'].indexOf(anchorSel.value[0]);
        const row = ['上', '中', '下'].indexOf(anchorSel.value[1]);
        const dx = col === 0 ? 0 : col === 1 ? (state.w - w) / 2 : state.w - w;
        const dy = row === 0 ? 0 : row === 1 ? (state.h - h) / 2 : state.h - h;
        pushHistory();
        rebuildLayers(w, h, (ctx, old) => ctx.drawImage(old, Math.round(dx), Math.round(dy)));
        clearSelection();
        setDocSize(w, h);
        fitView();
        renderLayersPanel();
        requestRender();
        c();
        toast(`画布已调整为 ${w} × ${h}`);
      },
    },
  ]);
}
function rotateCanvas(deg) {
  pushHistory();
  const nw = deg === 180 ? state.w : state.h;
  const nh = deg === 180 ? state.w : state.h;
  rebuildLayers(nw, nh, (ctx, old) => {
    ctx.translate(nw / 2, nh / 2);
    ctx.rotate(deg * Math.PI / 180);
    ctx.drawImage(old, -state.w / 2, -state.h / 2);
  });
  clearSelection();
  setDocSize(nw, nh);
  fitView();
  renderLayersPanel();
  requestRender();
}
function flipCanvas(axis) {
  pushHistory();
  rebuildLayers(state.w, state.h, (ctx, old) => {
    ctx.translate(axis === 'h' ? state.w : 0, axis === 'v' ? state.h : 0);
    ctx.scale(axis === 'h' ? -1 : 1, axis === 'v' ? -1 : 1);
    ctx.drawImage(old, 0, 0);
  });
  clearSelection();
  renderLayersPanel();
  requestRender();
}

/* ---------------- 图层操作 ---------------- */
function updateBlendControls() {
  const L = activeLayer();
  if (!L) return;
  $('#blend-select').value = L.blend || 'source-over';
  $('#opacity-slider').value = Math.round(L.opacity * 100);
  $('#opacity-val').textContent = Math.round(L.opacity * 100) + '%';
}
function uiAddLayer() {
  pushHistory();
  addLayer();
  renderLayersPanel();
  requestRender();
}
function uiDuplicateLayer() {
  const L = activeLayer();
  if (!L) return;
  pushHistory();
  addLayerObj(L.clone());
  renderLayersPanel();
  requestRender();
}
function uiDeleteLayer() {
  if (state.layers.length <= 1) { toast('至少需要保留一个图层'); return; }
  pushHistory();
  state.layers.splice(state.activeIdx, 1);
  state.activeIdx = clamp(state.activeIdx, 0, state.layers.length - 1);
  clearSelection();
  renderLayersPanel();
  updateBlendControls();
  requestRender();
}
function moveLayer(dir) {
  const i = state.activeIdx, j = i + dir;
  if (j < 0 || j >= state.layers.length) return;
  pushHistory();
  [state.layers[i], state.layers[j]] = [state.layers[j], state.layers[i]];
  state.activeIdx = j;
  renderLayersPanel();
  requestRender();
}
function mergeDown() {
  const i = state.activeIdx;
  if (i <= 0) { toast('下方没有可合并的图层'); return; }
  pushHistory();
  const top = state.layers[i], bottom = state.layers[i - 1];
  const c = bottom.ctx;
  c.save();
  c.globalAlpha = top.opacity;
  c.globalCompositeOperation = top.blend || 'source-over';
  c.drawImage(top.canvas, 0, 0);
  c.restore();
  state.layers.splice(i, 1);
  state.activeIdx = i - 1;
  clearSelection();
  renderLayersPanel();
  requestRender();
  toast('已向下合并');
}
function mergeVisible() {
  const vis = state.layers.map((l, i) => ({ l, i })).filter(o => o.l.visible);
  if (vis.length <= 1) { toast('可见图层不足两层'); return; }
  pushHistory();
  const merged = new Layer(state.w, state.h, '合并图层');
  const c = merged.ctx;
  for (const { l } of vis) {
    c.save();
    c.globalAlpha = l.opacity;
    c.globalCompositeOperation = l.blend || 'source-over';
    c.drawImage(l.canvas, 0, 0);
    c.restore();
  }
  const insertAt = vis[vis.length - 1].i - vis.length + 1;
  const kept = state.layers.filter(l => !l.visible);
  state.layers = [...kept.slice(0, insertAt), merged, ...kept.slice(insertAt)];
  state.activeIdx = state.layers.indexOf(merged);
  clearSelection();
  renderLayersPanel();
  requestRender();
  toast('已合并可见图层');
}
function flattenImage() {
  if (state.layers.length <= 1) return;
  pushHistory();
  const merged = new Layer(state.w, state.h, '背景');
  for (const l of state.layers) {
    if (!l.visible) continue;
    merged.ctx.save();
    merged.ctx.globalAlpha = l.opacity;
    merged.ctx.globalCompositeOperation = l.blend || 'source-over';
    merged.ctx.drawImage(l.canvas, 0, 0);
    merged.ctx.restore();
  }
  state.layers = [merged];
  state.activeIdx = 0;
  clearSelection();
  renderLayersPanel();
  requestRender();
  toast('已拼合图像');
}

/* ---------------- 图层面板 ---------------- */
const BLEND_MODES = [
  ['正常', 'source-over'], ['正片叠底', 'multiply'], ['滤色', 'screen'], ['叠加', 'overlay'],
  ['变暗', 'darken'], ['变亮', 'lighten'], ['颜色减淡', 'color-dodge'], ['颜色加深', 'color-burn'],
  ['强光', 'hard-light'], ['柔光', 'soft-light'], ['差值', 'difference'], ['排除', 'exclusion'],
  ['色相', 'hue'], ['饱和度', 'saturation'], ['颜色', 'color'], ['明度', 'luminosity'],
];
function buildBlendSelect() {
  const sel = $('#blend-select');
  for (const [label, val] of BLEND_MODES) sel.append(el('option', { value: val }, label));
  sel.addEventListener('change', () => {
    const L = activeLayer();
    if (!L) return;
    pushHistory();
    L.blend = sel.value;
    requestRender();
  });
}
function drawThumb(cv, layer) {
  const c = cv.getContext('2d');
  c.setTransform(1, 0, 0, 1, 0, 0);
  c.clearRect(0, 0, cv.width, cv.height);
  const s = Math.min(cv.width / state.w, cv.height / state.h);
  const w = state.w * s, h = state.h * s;
  c.drawImage(layer.canvas, (cv.width - w) / 2, (cv.height - h) / 2, w, h);
}
function updateThumb(layer) {
  const cv = $(`.layer-thumb[data-id="${layer.id}"]`);
  if (cv) drawThumb(cv, layer);
}
function renderLayersPanel() {
  const list = $('#layer-list');
  list.innerHTML = '';
  for (let i = state.layers.length - 1; i >= 0; i--) {
    const L = state.layers[i];
    const thumb = el('canvas', { class: 'layer-thumb', width: 44, height: 33 });
    thumb.dataset.id = L.id;
    drawThumb(thumb, L);
    const eye = el('span', {
      class: 'layer-eye' + (L.visible ? '' : ' off'),
      title: '显示 / 隐藏',
      onclick: e => {
        e.stopPropagation();
        L.visible = !L.visible;
        eye.classList.toggle('off', !L.visible);
        requestRender();
      },
    }, L.visible ? '👁' : '✕');
    const name = el('span', { class: 'layer-name' }, L.name);
    name.addEventListener('dblclick', e => {
      e.stopPropagation();
      const input = el('input', { value: L.name });
      name.innerHTML = '';
      name.append(input);
      input.focus();
      input.select();
      const done = () => {
        L.name = input.value.trim() || L.name;
        renderLayersPanel();
      };
      input.addEventListener('blur', done);
      input.addEventListener('keydown', ev => {
        ev.stopPropagation();
        if (ev.key === 'Enter') input.blur();
        if (ev.key === 'Escape') { input.value = L.name; input.blur(); }
      });
    });
    const row = el('div', {
      class: 'layer-row' + (i === state.activeIdx ? ' active' : ''),
      onclick: () => {
        state.activeIdx = i;
        for (const r of list.children) r.classList.remove('active');
        row.classList.add('active');
        updateBlendControls();
      },
    }, eye, thumb, name,
      el('button', { class: 'mini-btn', title: '上移一层', onclick: e => { e.stopPropagation(); state.activeIdx = i; moveLayer(1); } }, '↑'),
      el('button', { class: 'mini-btn', title: '下移一层', onclick: e => { e.stopPropagation(); state.activeIdx = i; moveLayer(-1); } }, '↓'));
    list.append(row);
  }
  updateBlendControls();
}

/* ---------------- 工具栏 / 选项栏 ---------------- */
const ICONS = {
  move: '<svg viewBox="0 0 24 24"><path d="M12 3v18M3 12h18M12 3l-2.4 2.4M12 3l2.4 2.4M12 21l-2.4-2.4M12 21l2.4-2.4M3 12l2.4-2.4M3 12l2.4 2.4M21 12l-2.4-2.4M21 12l-2.4 2.4"/></svg>',
  marquee: '<svg viewBox="0 0 24 24"><rect x="4" y="5" width="16" height="14" stroke-dasharray="3 2.4"/></svg>',
  lasso: '<svg viewBox="0 0 24 24"><path d="M4.5 11c0-4 3.4-6.5 7.5-6.5s7.5 2.5 7.5 6-3.4 6.5-7.5 6.5c-1.7 0-3.3.5-3.3 2.1s1.8 2.4 3.3 2.9"/></svg>',
  polylasso: '<svg viewBox="0 0 24 24"><path d="M5.5 8.5l5-4.2 8 3 2 6.2-6 7-7.3-3z" stroke-dasharray="3 2.2"/></svg>',
  wand: '<svg viewBox="0 0 24 24"><path d="M4 20l9.5-9.5"/><path d="M17 3v3.5M15.2 4.8h3.6M20 9v3M18.5 10.5h3M13 6.5v2M12 7.5h2"/></svg>',
  brush: '<svg viewBox="0 0 24 24"><path d="M13.5 4.5l6 6-7.2 7.2c-1.8 1.8-4.6 2-5.9.7s-1.1-4.1.7-5.9z"/><path d="M4.5 20.5c1.6-.4 2.7-1.4 3.2-2.9"/></svg>',
  eraser: '<svg viewBox="0 0 24 24"><path d="M8.5 19.5H20"/><path d="M9.5 17.5l-4-4a1.8 1.8 0 010-2.6l6-6a1.8 1.8 0 012.6 0l5 5a1.8 1.8 0 010 2.6l-7 7h-2.6z"/></svg>',
  bucket: '<svg viewBox="0 0 24 24"><path d="M11.5 3.5l7.5 7.5-6.3 6.3a2.4 2.4 0 01-3.4 0l-4.1-4.1a2.4 2.4 0 010-3.4z"/><path d="M4.5 11.5h13.5"/><path d="M20 15.5c1.3 1.8 1.3 3.6.1 4.5-1.2.9-2.9-.4-2-2.6z"/></svg>',
  picker: '<svg viewBox="0 0 24 24"><path d="M13.5 6.5l4 4"/><path d="M15.5 4.5l4 4-9.3 9.3-4.7 1.2 1.2-4.7z"/></svg>',
  text: '<svg viewBox="0 0 24 24"><path d="M5.5 5.5h13M12 5.5v13M9.5 18.5h5"/></svg>',
  shape: '<svg viewBox="0 0 24 24"><rect x="4" y="4" width="11" height="11"/><circle cx="15" cy="15" r="5"/></svg>',
  crop: '<svg viewBox="0 0 24 24"><path d="M7 2.5V17h14.5M2.5 7H17v14.5"/></svg>',
  hand: '<svg viewBox="0 0 24 24"><path d="M8 12.5V6a1.4 1.4 0 012.8 0v5m0-6.7a1.4 1.4 0 012.8 0V11m0-4.3a1.4 1.4 0 012.8 0v6.8m0-3.5a1.4 1.4 0 012.8 0v5.2a6 6 0 01-6 6h-1.8a6 6 0 01-5-2.7l-2-3a1.5 1.5 0 012.3-1.9L8 15.6"/></svg>',
  zoom: '<svg viewBox="0 0 24 24"><circle cx="10.5" cy="10.5" r="6"/><path d="M15 15l5.5 5.5M8 10.5h5M10.5 8v5"/></svg>',
};
const TOOLS = {
  move: { name: '移动', key: 'V', hint: '拖动移动整层；存在选区时只移动选区内像素' },
  marquee: { name: '矩形选框', key: 'M', hint: '拖动创建矩形选区；Shift 加选，Alt 减选；单击空白取消选区' },
  lasso: { name: '套索', key: 'L', hint: '按住拖动绘制任意形状选区；Shift 加选，Alt 减选' },
  polylasso: { name: '多边形套索', key: 'P', hint: '单击添加顶点，双击 / 回车闭合，Esc 取消' },
  wand: { name: '魔棒', key: 'W', hint: '单击选取颜色相近的区域；Shift 加选，Alt 减选' },
  brush: { name: '画笔', key: 'B', hint: '按住拖动绘制；[ ] 调整笔刷大小' },
  eraser: { name: '橡皮擦', key: 'E', hint: '擦除当前图层像素' },
  bucket: { name: '油漆桶', key: 'G', hint: '单击填充颜色相近的连通区域' },
  picker: { name: '吸管', key: 'I', hint: '单击取色为前景色，Alt+单击取为背景色' },
  text: { name: '文字', key: 'T', hint: '单击画布输入文字，回车确认，Esc 取消' },
  shape: { name: '形状', key: 'U', hint: '拖动绘制矩形 / 椭圆，Shift 画正方形 / 正圆' },
  crop: { name: '裁剪', key: 'C', hint: '拖出裁剪框，回车或双击应用，Esc 取消' },
  hand: { name: '抓手', key: 'H', hint: '拖动平移视图；任何工具下按住空格同样可以平移' },
  zoom: { name: '缩放', key: 'Z', hint: '单击放大，Alt+单击缩小；也可 Ctrl+滚轮' },
};
const TOOL_ORDER = [
  ['move'],
  ['marquee', 'lasso', 'polylasso', 'wand'],
  ['brush', 'eraser', 'bucket', 'picker'],
  ['text', 'shape'],
  ['crop'],
  ['hand', 'zoom'],
];
function buildToolbar() {
  const bar = $('#toolbar');
  for (const group of TOOL_ORDER) {
    if (group !== TOOL_ORDER[0]) bar.append(el('div', { class: 'tool-sep' }));
    for (const key of group) {
      const t = TOOLS[key];
      bar.append(el('div', {
        class: 'tool', 'data-tool': key, title: `${t.name} (${t.key})`,
        html: ICONS[key],
        onclick: () => setTool(key),
      }));
    }
  }
}
function setTool(key) {
  if (textEditorOpen) commitText();
  polyCancel();
  state.crop = null;
  preview = null;
  drag = null;
  state.tool = key;
  for (const n of document.querySelectorAll('.tool')) n.classList.toggle('active', n.dataset.tool === key);
  const cur = { move: 'move', marquee: 'crosshair', lasso: 'crosshair', polylasso: 'crosshair', wand: 'crosshair', brush: 'crosshair', eraser: 'crosshair', bucket: 'crosshair', picker: 'crosshair', text: 'text', shape: 'crosshair', crop: 'crosshair', hand: 'grab', zoom: 'zoom-in' }[key];
  area.dataset.cursor = cur;
  $('#status-tool').textContent = '工具: ' + TOOLS[key].name;
  $('#status-hint').textContent = TOOLS[key].hint || '';
  renderOptionsBar();
  requestRender();
}
function renderOptionsBar() {
  const bar = $('#optionsbar');
  bar.innerHTML = '';
  bar.append(el('span', { class: 'opt-tool' }, TOOLS[state.tool].name));
  const slider = (label, get, set, min, max, unit) => {
    const val = el('span', { class: 'opt-val' }, get() + (unit || ''));
    const input = el('input', {
      type: 'range', min, max, value: get(),
      oninput: e => { set(+e.target.value); val.textContent = get() + (unit || ''); requestRender(); },
    });
    return el('label', { class: 'opt' }, label, input, val);
  };
  const check = (label, get, set) => {
    const input = el('input', { type: 'checkbox' });
    input.checked = get();
    input.addEventListener('change', e => set(e.target.checked));
    return el('label', { class: 'opt' }, input, label);
  };
  const selectW = (label, options, get, set) => {
    const sel = el('select', { onchange: e => set(e.target.value) },
      ...options.map(([l, v]) => el('option', { value: v }, l)));
    sel.value = get();
    return el('label', { class: 'opt' }, label, sel);
  };
  switch (state.tool) {
    case 'brush':
      bar.append(slider('大小', () => state.brush.size, v => state.brush.size = v, 1, 300, ' px'));
      bar.append(slider('硬度', () => state.brush.hardness, v => state.brush.hardness = v, 1, 100, '%'));
      bar.append(slider('流量', () => state.brush.flow, v => state.brush.flow = v, 1, 100, '%'));
      break;
    case 'eraser':
      bar.append(slider('大小', () => state.eraser.size, v => state.eraser.size = v, 1, 300, ' px'));
      bar.append(slider('硬度', () => state.eraser.hardness, v => state.eraser.hardness = v, 1, 100, '%'));
      break;
    case 'wand':
      bar.append(slider('容差', () => state.wand.tol, v => state.wand.tol = v, 0, 255));
      bar.append(check('连续', () => state.wand.contiguous, v => state.wand.contiguous = v));
      break;
    case 'bucket':
      bar.append(slider('容差', () => state.fill.tol, v => state.fill.tol = v, 0, 255));
      break;
    case 'text':
      bar.append(slider('字号', () => state.text.size, v => state.text.size = v, 8, 400, ' px'));
      bar.append(selectW('字体',
        [['无衬线', 'sans-serif'], ['衬线', 'serif'], ['等宽', 'monospace'], ['手写', 'cursive']],
        () => state.text.font, v => state.text.font = v));
      break;
    case 'shape':
      bar.append(selectW('形状', [['矩形', 'rect'], ['椭圆', 'ellipse']], () => state.shape.kind, v => state.shape.kind = v));
      bar.append(check('空心(线宽=画笔大小)', () => state.shape.hollow, v => state.shape.hollow = v));
      break;
    case 'crop': {
      if (state.crop) {
        bar.append(el('button', { onclick: applyCrop }, '✓ 应用裁剪 (回车)'));
        bar.append(el('button', { onclick: () => { state.crop = null; requestRender(); } }, '✕ 取消 (Esc)'));
      }
      break;
    }
  }
  if (state.tool === 'crop' && state.crop) renderOptionsBar.__redo = true;
  bar.append(el('span', { class: 'opt-hint' }, TOOLS[state.tool].hint || ''));
}

/* ---------------- 菜单栏 ---------------- */
function openModal(title, bodyEl, buttons) {
  const root = $('#modal-root');
  root.innerHTML = '';
  const close = () => { root.innerHTML = ''; };
  const btnRow = el('div', { class: 'modal-buttons' },
    ...buttons.map(b => el('button', { class: 'btn' + (b.primary ? ' primary' : ''), onclick: () => b.action(close) }, b.label)));
  const box = el('div', { class: 'modal' },
    el('div', { class: 'modal-title' }, title),
    bodyEl, btnRow);
  const mask = el('div', { class: 'modal-mask', onclick: e => { if (e.target === mask) close(); } }, box);
  root.append(mask);
  return close;
}
function confirmDialog(title, message, onOk) {
  openModal(title, el('div', { class: 'modal-body' }, message), [
    { label: '取消', action: c => c() },
    { label: '确定', primary: true, action: c => { c(); onOk(); } },
  ]);
}
function newDocDialog() {
  const wIn = el('input', { type: 'number', min: 1, max: 6000, value: 800 });
  const hIn = el('input', { type: 'number', min: 1, max: 6000, value: 600 });
  const bgSel = el('select', {},
    el('option', { value: 'white' }, '白色'),
    el('option', { value: 'transparent' }, '透明'),
    el('option', { value: 'black' }, '黑色'));
  const body = el('div', { class: 'modal-body' },
    el('div', { class: 'row' }, el('label', {}, '宽度(像素)'), wIn),
    el('div', { class: 'row' }, el('label', {}, '高度(像素)'), hIn),
    el('div', { class: 'row' }, el('label', {}, '背景'), bgSel));
  openModal('新建文档', body, [
    { label: '取消', action: c => c() },
    {
      label: '创建', primary: true, action: c => {
        const w = clamp(+wIn.value | 0, 1, 6000), h = clamp(+hIn.value | 0, 1, 6000);
        newDocument(w, h, bgSel.value);
        fitView();
        c();
      },
    },
  ]);
}
function newDocument(w, h, bg) {
  const L = new Layer(w, h, '背景');
  if (bg === 'white') { L.ctx.fillStyle = '#ffffff'; L.ctx.fillRect(0, 0, w, h); }
  if (bg === 'black') { L.ctx.fillStyle = '#000000'; L.ctx.fillRect(0, 0, w, h); }
  state.layers = [L];
  state.activeIdx = 0;
  state.clipboard = null;
  setDocSize(w, h);
  clearSelection();
  state.crop = null;
  history.stack = [];
  history.idx = -1;
  pushHistory();
  renderLayersPanel();
  requestRender();
}
async function openImageFile(file, asLayer) {
  const url = await fileToDataURL(file);
  const img = await loadImage(url);
  if (asLayer) {
    pushHistory();
    const L = addLayer(file.name.replace(/\.[^.]+$/, ''));
    let w = img.width, h = img.height;
    const scale = Math.min(1, state.w / w, state.h / h);
    w = Math.round(w * scale); h = Math.round(h * scale);
    L.ctx.imageSmoothingQuality = 'high';
    L.ctx.drawImage(img, Math.round((state.w - w) / 2), Math.round((state.h - h) / 2), w, h);
    renderLayersPanel();
    requestRender();
    toast('已导入图层: ' + L.name);
  } else {
    // 整幅打开：以图片为文档尺寸（过大则等比缩小）
    let w = img.width, h = img.height;
    const scale = Math.min(1, 4096 / w, 4096 / h);
    w = Math.round(w * scale); h = Math.round(h * scale);
    const L = new Layer(w, h, '背景');
    L.ctx.imageSmoothingQuality = 'high';
    L.ctx.drawImage(img, 0, 0, w, h);
    state.layers = [L];
    state.activeIdx = 0;
    setDocSize(w, h);
    clearSelection();
    state.crop = null;
    history.stack = [];
    history.idx = -1;
    pushHistory();
    renderLayersPanel();
    fitView();
    toast('已打开: ' + file.name);
  }
}
function exportImage(type) {
  const cv = type === 'jpeg' ? (() => {
    const t = mkCanvas(state.w, state.h);
    const c = t.getContext('2d');
    c.fillStyle = '#fff';
    c.fillRect(0, 0, state.w, state.h);
    c.drawImage(composite, 0, 0);
    return t;
  })() : composite;
  const mime = type === 'jpeg' ? 'image/jpeg' : type === 'webp' ? 'image/webp' : 'image/png';
  const ext = type === 'jpeg' ? 'jpg' : type;
  cv.toBlob(blob => {
    download(blob, `minips-${timestamp()}.${ext}`);
    toast(`已导出 ${ext.toUpperCase()}`);
  }, mime, 0.92);
}
function saveProject() {
  const data = {
    app: 'MiniPS', version: 1,
    w: state.w, h: state.h,
    layers: state.layers.map(l => ({
      name: l.name, visible: l.visible, opacity: l.opacity, blend: l.blend,
      data: l.canvas.toDataURL('image/png'),
    })),
  };
  download(new Blob([JSON.stringify(data)], { type: 'application/json' }), `minips-${timestamp()}.psx`);
  toast('项目已保存 (.psx)');
}
async function openProjectFile(file) {
  try {
    const data = JSON.parse(await file.text());
    if (data.app !== 'MiniPS') throw new Error('不是 MiniPS 工程文件');
    setDocSize(data.w, data.h);
    const layers = [];
    for (const s of data.layers) {
      const l = new Layer(data.w, data.h, s.name);
      l.visible = s.visible; l.opacity = s.opacity; l.blend = s.blend;
      try {
        const img = await loadImage(s.data);
        l.ctx.drawImage(img, 0, 0);
      } catch (_) { }
      layers.push(l);
    }
    state.layers = layers;
    state.activeIdx = 0;
    clearSelection();
    state.crop = null;
    history.stack = [];
    history.idx = -1;
    pushHistory();
    renderLayersPanel();
    fitView();
    toast('项目已打开');
  } catch (err) {
    toast('打开失败: ' + err.message);
  }
}

function showShortcuts() {
  const rows = [
    ['V / M / L / P / W', '移动 / 选框 / 套索 / 多边形套索 / 魔棒'],
    ['B / E / G / I', '画笔 / 橡皮擦 / 油漆桶 / 吸管'],
    ['T / U / C / H / Z', '文字 / 形状 / 裁剪 / 抓手 / 缩放'],
    ['空格拖动', '任意工具下平移视图'],
    ['Ctrl + 滚轮', '以光标为中心缩放'],
    ['Ctrl+Z / Ctrl+Shift+Z', '撤销 / 重做'],
    ['Ctrl+A / Ctrl+D', '全选 / 取消选择'],
    ['Ctrl+Shift+I', '反选'],
    ['Ctrl+C / X / V', '复制 / 剪切 / 粘贴（粘贴为新图层）'],
    ['Delete', '删除选区内像素'],
    ['Ctrl+J / Ctrl+E', '复制图层 / 向下合并'],
    ['Ctrl+Shift+N', '新建图层'],
    ['[ / ]', '减小 / 增大笔刷大小'],
    ['X / D', '交换前景背景色 / 重置黑白'],
    ['Alt+Delete', '填充前景色'],
    ['Ctrl+0 / Ctrl+1', '适应窗口 / 100% 显示'],
    ['Ctrl+S', '保存工程文件 (.psx)'],
    ['Ctrl+O', '打开图像'],
    ['Shift+Ctrl+E', '导出 PNG'],
  ];
  const table = el('table', { class: 'kbd-table' }, el('tbody', {}, ...rows.map(r => el('tr', {}, el('td', {}, r[0]), el('td', {}, r[1])))));
  openModal('快捷键一览', el('div', { class: 'modal-body' }, table), [{ label: '关闭', primary: true, action: c => c() }]);
}

function buildMenus() {
  const MENUS = [
    {
      label: '文件', items: [
        { label: '新建…', key: 'Ctrl+N', action: newDocDialog },
        { label: '打开图像…', key: 'Ctrl+O', action: () => $('#file-open').click() },
        { label: '导入为图层…', action: () => $('#file-import').click() },
        { sep: true },
        { label: '导出为 PNG', key: 'Shift+Ctrl+E', action: () => exportImage('png') },
        { label: '导出为 JPEG', action: () => exportImage('jpeg') },
        { sep: true },
        { label: '保存工程 (.psx)', key: 'Ctrl+S', action: saveProject },
        { label: '打开工程…', action: () => $('#file-project').click() },
      ],
    },
    {
      label: '编辑', items: [
        { label: '撤销', key: 'Ctrl+Z', action: doUndo },
        { label: '重做', key: 'Ctrl+Shift+Z', action: doRedo },
        { sep: true },
        { label: '剪切', key: 'Ctrl+X', action: cutSel },
        { label: '复制', key: 'Ctrl+C', action: copySel },
        { label: '粘贴为新图层', key: 'Ctrl+V', action: pasteClip },
        { label: '删除选区内像素', key: 'Delete', action: () => deleteSelPixels(true) },
        { sep: true },
        { label: '填充前景色', key: 'Alt+Delete', action: () => fillWith(state.fg) },
        { label: '填充背景色', action: () => fillWith(state.bg) },
      ],
    },
    {
      label: '图像', items: [
        { label: '图像大小…', action: imageSizeDialog },
        { label: '画布大小…', action: canvasSizeDialog },
        { sep: true },
        { label: '亮度 / 对比度…', action: adjustBrightnessContrast },
        { label: '色相 / 饱和度…', action: adjustHueSat },
        { label: '高斯模糊…', action: adjustBlur },
        { sep: true },
        { label: '反相', action: invertColors },
        { label: '去色', action: desaturate },
        { sep: true },
        { label: '顺时针旋转 90°', action: () => rotateCanvas(90) },
        { label: '逆时针旋转 90°', action: () => rotateCanvas(-90) },
        { label: '旋转 180°', action: () => rotateCanvas(180) },
        { label: '水平翻转画布', action: () => flipCanvas('h') },
        { label: '垂直翻转画布', action: () => flipCanvas('v') },
      ],
    },
    {
      label: '图层', items: [
        { label: '新建图层', key: 'Ctrl+Shift+N', action: uiAddLayer },
        { label: '复制图层', key: 'Ctrl+J', action: uiDuplicateLayer },
        { label: '删除图层', action: uiDeleteLayer },
        { sep: true },
        { label: '上移一层', action: () => moveLayer(1) },
        { label: '下移一层', action: () => moveLayer(-1) },
        { sep: true },
        { label: '向下合并', key: 'Ctrl+E', action: mergeDown },
        { label: '合并可见图层', action: mergeVisible },
        { label: '拼合图像', action: flattenImage },
      ],
    },
    {
      label: '选择', items: [
        { label: '全选', key: 'Ctrl+A', action: selectAll },
        { label: '取消选择', key: 'Ctrl+D', action: clearSelection },
        { label: '反选', key: 'Ctrl+Shift+I', action: invertSelection },
      ],
    },
    {
      label: '视图', items: [
        { label: '放大', key: 'Ctrl++', action: () => setZoom(state.zoom * 1.25) },
        { label: '缩小', key: 'Ctrl+-', action: () => setZoom(state.zoom / 1.25) },
        { label: '适应窗口', key: 'Ctrl+0', action: fitView },
        { label: '100%', key: 'Ctrl+1', action: () => setZoom(1) },
      ],
    },
    {
      label: '帮助', items: [
        { label: '快捷键一览', action: showShortcuts },
        { label: '关于 MiniPS', action: () => openModal('关于 MiniPS',
          el('div', { class: 'modal-body' },
            el('p', {}, 'MiniPS —— 一个纯前端实现的网页版图像编辑器。'),
            el('p', { style: 'color:#999' }, '支持图层、混合模式、选区（选框 / 套索 / 多边形套索 / 魔棒）、画笔、橡皮擦、油漆桶、文字、形状、裁剪、常用调整滤镜、撤销重做，以及 PNG / JPEG 导出与 .psx 工程文件。')),
          [{ label: '关闭', primary: true, action: c => c() }]) },
      ],
    },
  ];
  const nav = $('#menus');
  for (const m of MENUS) {
    const btn = el('div', { class: 'menu-btn' }, m.label);
    const drop = el('div', { class: 'menu-drop' });
    for (const it of m.items) {
      if (it.sep) { drop.append(el('div', { class: 'menu-sep' })); continue; }
      drop.append(el('div', {
        class: 'menu-item',
        onclick: () => { closeMenus(); it.action && it.action(); },
      }, el('span', {}, it.label), el('span', { class: 'menu-key' }, it.key || '')));
    }
    const wrap = el('div', { class: 'menu-wrap' }, btn, drop);
    btn.addEventListener('click', e => {
      e.stopPropagation();
      const open = drop.classList.contains('show');
      closeMenus();
      if (!open) { drop.classList.add('show'); btn.classList.add('open'); }
    });
    btn.addEventListener('pointerenter', () => {
      if (nav.querySelector('.menu-drop.show')) {
        closeMenus();
        drop.classList.add('show');
        btn.classList.add('open');
      }
    });
    nav.append(wrap);
  }
}
function closeMenus() {
  document.querySelectorAll('.menu-drop.show').forEach(d => d.classList.remove('show'));
  document.querySelectorAll('.menu-btn.open').forEach(b => b.classList.remove('open'));
}
document.addEventListener('click', closeMenus);

/* ---------------- 键盘快捷键 ---------------- */
const TOOL_KEYS = {
  v: 'move', m: 'marquee', l: 'lasso', p: 'polylasso', w: 'wand',
  b: 'brush', e: 'eraser', g: 'bucket', i: 'picker',
  t: 'text', u: 'shape', c: 'crop', h: 'hand', z: 'zoom',
};
window.addEventListener('keydown', e => {
  const t = e.target;
  if (t && (t.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(t.tagName))) {
    if (e.key === 'Escape') t.blur();
    return;
  }
  const k = e.key.toLowerCase();
  const mod = e.ctrlKey || e.metaKey;
  if (mod) {
    const stops = () => e.preventDefault();
    switch (k) {
      case 'z': stops(); e.shiftKey ? doRedo() : doUndo(); return;
      case 'y': stops(); doRedo(); return;
      case 'a': stops(); selectAll(); return;
      case 'd': stops(); clearSelection(); return;
      case 'i': stops(); e.shiftKey ? invertSelection() : invertColors(); return;
      case 'c': stops(); copySel(); return;
      case 'x': stops(); cutSel(); return;
      case 'v': stops(); pasteClip(); return;
      case 'j': stops(); uiDuplicateLayer(); return;
      case 'e': stops(); e.shiftKey ? exportImage('png') : mergeDown(); return;
      case 'n': stops(); e.shiftKey ? uiAddLayer() : newDocDialog(); return;
      case 'o': stops(); $('#file-open').click(); return;
      case 's': stops(); saveProject(); return;
      case '0': stops(); fitView(); return;
      case '1': stops(); setZoom(1); return;
      case '=': case '+': stops(); setZoom(state.zoom * 1.25); return;
      case '-': stops(); setZoom(state.zoom / 1.25); return;
    }
    return;
  }
  if (e.altKey && k === 'delete') { e.preventDefault(); fillWith(state.fg); return; }
  if (k === ' ') { spaceDown = true; area.dataset.cursor = 'grab'; e.preventDefault(); return; }
  if (k === 'delete' || k === 'backspace') { deleteSelPixels(true); return; }
  if (k === 'escape') {
    if (poly) polyCancel();
    else if (state.crop) { state.crop = null; requestRender(); }
    else clearSelection();
    return;
  }
  if (k === 'enter') {
    if (poly) { polyClose(); return; }
    if (state.tool === 'crop' && state.crop) { applyCrop(); return; }
  }
  if (k === 'x') { const f = state.fg; state.fg = state.bg; state.bg = f; $('#fg-input').value = state.fg; $('#bg-input').value = state.bg; updateSwatches(); return; }
  if (k === 'd') { state.fg = '#000000'; state.bg = '#ffffff'; $('#fg-input').value = state.fg; $('#bg-input').value = state.bg; updateSwatches(); return; }
  if (k === '[') {
    const st = state.tool === 'eraser' ? state.eraser : state.brush;
    st.size = clamp(st.size - (st.size > 40 ? 10 : 4), 1, 300);
    renderOptionsBar();
    return;
  }
  if (k === ']') {
    const st = state.tool === 'eraser' ? state.eraser : state.brush;
    st.size = clamp(st.size + (st.size >= 40 ? 10 : 4), 1, 300);
    renderOptionsBar();
    return;
  }
  if (TOOL_KEYS[k] && !mod) setTool(TOOL_KEYS[k]);
});
window.addEventListener('keyup', e => {
  if (e.key === ' ') {
    spaceDown = false;
    area.dataset.cursor = { move: 'move', marquee: 'crosshair', lasso: 'crosshair', polylasso: 'crosshair', wand: 'crosshair', brush: 'crosshair', eraser: 'crosshair', bucket: 'crosshair', picker: 'crosshair', text: 'text', shape: 'crosshair', crop: 'crosshair', hand: 'grab', zoom: 'zoom-in' }[state.tool] || 'default';
  }
});

/* ---------------- 其余 UI 绑定 ---------------- */
function updateSwatches() {
  $('#fg-swatch').style.background = state.fg;
  $('#bg-swatch').style.background = state.bg;
}
function bindUI() {
  buildBlendSelect();
  // 颜色
  $('#fg-input').addEventListener('input', e => { state.fg = e.target.value; updateSwatches(); });
  $('#bg-input').addEventListener('input', e => { state.bg = e.target.value; updateSwatches(); });
  $('#swap-colors').addEventListener('click', () => {
    const f = state.fg; state.fg = state.bg; state.bg = f;
    $('#fg-input').value = state.fg; $('#bg-input').value = state.bg;
    updateSwatches();
  });
  $('#reset-colors').addEventListener('click', () => {
    state.fg = '#000000'; state.bg = '#ffffff';
    $('#fg-input').value = state.fg; $('#bg-input').value = state.bg;
    updateSwatches();
  });
  // 图层面板
  $('#opacity-slider').addEventListener('input', e => {
    const L = activeLayer();
    if (!L) return;
    L.opacity = +e.target.value / 100;
    $('#opacity-val').textContent = e.target.value + '%';
    requestRender();
  });
  $('#opacity-slider').addEventListener('change', () => pushHistory());
  $('#btn-add-layer').addEventListener('click', uiAddLayer);
  $('#btn-dup-layer').addEventListener('click', uiDuplicateLayer);
  $('#btn-merge-layer').addEventListener('click', mergeDown);
  $('#btn-del-layer').addEventListener('click', uiDeleteLayer);
  // 缩放
  $('#zoom-in').addEventListener('click', () => setZoom(state.zoom * 1.25));
  $('#zoom-out').addEventListener('click', () => setZoom(state.zoom / 1.25));
  $('#zoom-fit').addEventListener('click', fitView);
  $('#zoom-100').addEventListener('click', () => setZoom(1));
  // 文件
  $('#file-open').addEventListener('change', e => {
    if (e.target.files[0]) openImageFile(e.target.files[0], false);
    e.target.value = '';
  });
  $('#file-import').addEventListener('change', e => {
    for (const f of e.target.files) openImageFile(f, true);
    e.target.value = '';
  });
  $('#file-project').addEventListener('change', e => {
    if (e.target.files[0]) openProjectFile(e.target.files[0]);
    e.target.value = '';
  });
  // 拖拽导入
  area.addEventListener('dragover', e => { e.preventDefault(); area.classList.add('dropping'); $('#drop-hint').hidden = false; });
  area.addEventListener('dragleave', () => { area.classList.remove('dropping'); $('#drop-hint').hidden = true; });
  area.addEventListener('drop', async e => {
    e.preventDefault();
    area.classList.remove('dropping');
    $('#drop-hint').hidden = true;
    for (const f of e.dataTransfer.files) {
      if (/\.(psx|json)$/i.test(f.name)) await openProjectFile(f);
      else if (f.type.startsWith('image/')) await openImageFile(f, true);
    }
  });
  window.addEventListener('resize', () => requestRender());
}

/* ---------------- 启动 ---------------- */
function init() {
  buildToolbar();
  buildMenus();
  bindUI();
  updateSwatches();
  newDocument(800, 600, 'white');
  fitView();
  setTool('brush');
  $('#status-tool').textContent = '工具: 画笔';
  $('#status-hint').textContent = TOOLS.brush.hint;
}
init();

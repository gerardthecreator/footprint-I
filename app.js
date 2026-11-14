/* ============================================================================
   APP.JS — Footprint BTCUSDT · Order Flow Pro
   Capa de presentación. Consume los snapshots de script.js y los pinta en el DOM.

   Nuevas capacidades:
   - Pills editables: umbral de imbalance y monto mínimo (manual/auto/relativo).
   - Selector de modo de imbalance (diagonal / nivel / media / percentil / compuesto).
   - Columna Δ nivel con estado de muro (stable / growing / shrinking / vanished).
   - Imbalance con color por percentil (p80 / p95 / p99).
   - Panel de manipulación con tipo de zona, edad, volumen, ratio y penetración.
   - Termómetro de 3 barras: acumulada, instantánea y zona del muro dominante.
   - Lock real de señal (FP.lockCurrentSignal / FP.unlockSignal).
   - Scrubber con max = Date.now() fijo (no histCursor).
   - Replay determinista: el histórico no muta activeSignalHist por trailing.
   - Velocidad de replay real (step = PLAY_STEP_S * speed).
   - Restauración de connLabel al volver a live.
   - Tema: actualiza meta[name=theme-color] y el icono.
   - Debounce de inputs numéricos para no invalidar grid en cada tecla.
   ============================================================================ */

(function(){
"use strict";

/* ============================================================================
   1. SHORTCUTS Y GUARDIAS
   ============================================================================ */
const FP = window.FP;
if (!FP){
  console.error("[app.js] script.js no cargado. Abortando.");
  return;
}

const { CONFIG, state, store, coverage } = FP;
const $ = sel => document.querySelector(sel);

/* ============================================================================
   2. CACHE DE NODOS DOM
   ============================================================================ */
const ui = {
  // Header
  connDot: null, connLabel: null,
  clockLocal: null, clockUtc: null,
  priceEl: null, pocVolEl: null, pocDeltaEl: null,
  deltaWindowLabel: null, deltaLongEl: null,
  deltaInstEl: null, deltaInstDir: null,
  tradesCountEl: null, volWindowLabel: null, volumeEl: null,
  coverage: null, covTxt: null,

  // Pills base
  pillWindow: null, pillWindowVal: null,
  pillBucket: null, pillBucketVal: null,
  pillImbMode: null, pillImbModeVal: null,
  pillImbThrInput: null, pillImbThrAuto: null,
  pillMinInput: null, pillMinAuto: null, pillMinRel: null,
  pillHeat: null, pillBars: null, pillThermo: null,
  pillLines: null, pillWalls: null, pillSound: null,

  // Live
  liveGrid: null, liveEmpty: null, statusLive: null,
  thermoFillLive: null, thermoFillInstLive: null, thermoFillZoneLive: null,
  thermoZoneWrapLive: null,
  thermoSubLive: null, thermoZoneSubLive: null,
  thermoValLive: null, thermoImbLive: null, thermoWarnLive: null,
  btnSignalLock: null,

  // Manip panel live
  manipPanelLive: null, manipBadgeLive: null, manipLevelLive: null,
  manipStateLive: null, manipAgeLive: null, manipVolLive: null,
  manipRatioLive: null, manipPenLive: null,

  // Hist
  histGrid: null, histEmpty: null, histEmptyTxt: null, statusHist: null,
  thermoFillHist: null, thermoFillInstHist: null, thermoFillZoneHist: null,
  thermoZoneWrapHist: null,
  thermoSubHist: null, thermoZoneSubHist: null,
  thermoValHist: null, thermoImbHist: null, thermoWarnHist: null,
  btnWindowHist: null, btnSignalLockHist: null,

  // Hist manip panel
  manipPanelHist: null, manipBadgeHist: null, manipLevelHist: null,
  manipStateHist: null, manipAgeHist: null, manipVolHist: null,
  manipRatioHist: null, manipPenHist: null,

  // Hist controls
  dtInput: null, scrub: null, timelineEvents: null,
  btnPlay: null, speedSel: null, btnFreeze: null,

  // Señales live
  signalsPanelLive: null, signalEntryLive: null, signalSideLive: null,
  signalSLLive: null, signalSLExtraLive: null,
  signalTPLive: null, signalTPExtraLive: null,
  signalMotorLive: null,

  // Señales hist
  signalsPanelHist: null, signalEntryHist: null, signalSideHist: null,
  signalSLHist: null, signalSLExtraHist: null,
  signalTPHist: null, signalTPExtraHist: null,
  signalMotorHist: null,

  // Global
  toasts: null,
  metaThemeColor: null,
  themeIcon: null
};

/* Cache de filas por modo */
const rowCache = { live: new Map(), hist: new Map() };
const gridInitialized = { live: false, hist: false };
const prevVol = { live: new Map(), hist: new Map() };
let lastStackCount = 0;

/* Debounce para inputs numéricos */
let debounceThrTimer = null;
let debounceMinTimer = null;

/* ============================================================================
   3. FORMATO Y HELPERS
   ============================================================================ */
const fmtUSD = v => {
  if (!v || v <= 0) return "·";
  if (v >= 1e9) return (v / 1e9).toFixed(2) + "B";
  if (v >= 1e6) return (v / 1e6).toFixed(2) + "M";
  if (v >= 1e3) return (v / 1e3).toFixed(1) + "k";
  return v.toFixed(0);
};
const fmtSigned = v => {
  if (Math.abs(v) < 1) return "0";
  return (v > 0 ? "+" : "-") + fmtUSD(Math.abs(v));
};
const fmtPrice = v => v.toLocaleString("en-US", { maximumFractionDigits: 0 });
const pad2 = n => String(n).padStart(2, "0");
const msToLocal = ms => {
  const d = new Date(ms);
  return `${d.getFullYear()}-${pad2(d.getMonth()+1)}-${pad2(d.getDate())} ${pad2(d.getHours())}:${pad2(d.getMinutes())}:${pad2(d.getSeconds())}`;
};
const msToUtcShort = ms => {
  const d = new Date(ms);
  return `${pad2(d.getUTCHours())}:${pad2(d.getUTCMinutes())}:${pad2(d.getUTCSeconds())}`;
};
const msToInputValue = ms => {
  const d = new Date(ms);
  return new Date(ms - d.getTimezoneOffset() * 60000).toISOString().slice(0, 19);
};

function getActiveWindowMin(){
  return state.windowMin || CONFIG.WINDOW_MIN || 40;
}

function toast(msg, kind){
  if (!ui.toasts) return;
  const t = document.createElement("div");
  t.className = "toast" + (kind ? " " + kind : "");
  t.textContent = msg;
  ui.toasts.appendChild(t);
  setTimeout(() => {
    t.style.opacity = "0";
    setTimeout(() => t.remove(), 300);
  }, 3500);
}

function vibrate(){
  if (!state.sound) return;
  if (navigator.vibrate) navigator.vibrate(CONFIG.VIBRATE_MS || 120);
}

const isMobile = () => window.matchMedia("(max-width: 767px)").matches;

/* Umbrales auxiliares para el color del imbalance */
function pctBucket(pct){
  if (pct >= 99) return "p99";
  if (pct >= 95) return "p95";
  if (pct >= 80) return "p80";
  return "";
}

/* ============================================================================
   4. CACHE UI
   ============================================================================ */
function cacheUI(){
  ui.connDot = $("#connDot"); ui.connLabel = $("#connLabel");
  ui.clockLocal = $("#clockLocal"); ui.clockUtc = $("#clockUtc");
  ui.priceEl = $("#priceEl"); ui.pocVolEl = $("#pocVolEl"); ui.pocDeltaEl = $("#pocDeltaEl");
  ui.deltaWindowLabel = $("#deltaWindowLabel");
  ui.deltaLongEl = $("#deltaLongEl");
  ui.deltaInstEl = $("#deltaInstEl");
  ui.deltaInstDir = $("#deltaInstDir");
  ui.tradesCountEl = $("#tradesCountEl");
  ui.volWindowLabel = $("#volWindowLabel");
  ui.volumeEl = $("#volumeEl");
  ui.coverage = $("#coverageIndicator"); ui.covTxt = $("#coverageTxt");

  // Pills
  ui.pillWindow = $("#pillWindow"); ui.pillWindowVal = $("#pillWindowVal");
  ui.pillBucket = $("#pillBucket"); ui.pillBucketVal = $("#pillBucketVal");
  ui.pillImbMode = $("#pillImbMode"); ui.pillImbModeVal = $("#pillImbModeVal");
  ui.pillImbThrInput = $("#pillImbThrInput"); ui.pillImbThrAuto = $("#pillImbThrAuto");
  ui.pillMinInput = $("#pillMinInput"); ui.pillMinAuto = $("#pillMinAuto");
  ui.pillMinRel = $("#pillMinRel");
  ui.pillHeat = $("#pillHeat"); ui.pillBars = $("#pillBars");
  ui.pillThermo = $("#pillThermo"); ui.pillLines = $("#pillLines");
  ui.pillWalls = $("#pillWalls"); ui.pillSound = $("#pillSound");

  // Live
  ui.liveGrid = $("#liveGrid"); ui.liveEmpty = $("#liveEmpty"); ui.statusLive = $("#statusLive");
  ui.thermoFillLive = $("#thermoFillLive"); ui.thermoFillInstLive = $("#thermoFillInstLive");
  ui.thermoFillZoneLive = $("#thermoFillZoneLive");
  ui.thermoZoneWrapLive = $("#thermoZoneLiveWrap");
  ui.thermoSubLive = $("#thermoSubLive");
  ui.thermoZoneSubLive = $("#thermoZoneSubLive");
  ui.thermoValLive = $("#thermoValLive"); ui.thermoImbLive = $("#thermoImbLive");
  ui.thermoWarnLive = $("#thermoWarnLive");
  ui.btnSignalLock = $("#btnSignalLock");

  // Manip live
  ui.manipPanelLive = $("#manipPanelLive");
  ui.manipBadgeLive = $("#manipBadgeLive");
  ui.manipLevelLive = $("#manipLevelLive");
  ui.manipStateLive = $("#manipStateLive");
  ui.manipAgeLive = $("#manipAgeLive");
  ui.manipVolLive = $("#manipVolLive");
  ui.manipRatioLive = $("#manipRatioLive");
  ui.manipPenLive = $("#manipPenLive");

  // Hist
  ui.histGrid = $("#histGrid"); ui.histEmpty = $("#histEmpty");
  ui.histEmptyTxt = $("#histEmptyTxt"); ui.statusHist = $("#statusHist");
  ui.thermoFillHist = $("#thermoFillHist"); ui.thermoFillInstHist = $("#thermoFillInstHist");
  ui.thermoFillZoneHist = $("#thermoFillZoneHist");
  ui.thermoZoneWrapHist = $("#thermoZoneHistWrap");
  ui.thermoSubHist = $("#thermoSubHist");
  ui.thermoZoneSubHist = $("#thermoZoneSubHist");
  ui.thermoValHist = $("#thermoValHist"); ui.thermoImbHist = $("#thermoImbHist");
  ui.thermoWarnHist = $("#thermoWarnHist");
  ui.btnWindowHist = $("#btnWindowHist");
  ui.btnSignalLockHist = $("#btnSignalLockHist");

  // Manip hist
  ui.manipPanelHist = $("#manipPanelHist");
  ui.manipBadgeHist = $("#manipBadgeHist");
  ui.manipLevelHist = $("#manipLevelHist");
  ui.manipStateHist = $("#manipStateHist");
  ui.manipAgeHist = $("#manipAgeHist");
  ui.manipVolHist = $("#manipVolHist");
  ui.manipRatioHist = $("#manipRatioHist");
  ui.manipPenHist = $("#manipPenHist");

  // Hist controls
  ui.dtInput = $("#dtInput"); ui.scrub = $("#scrub"); ui.timelineEvents = $("#timelineEvents");
  ui.btnPlay = $("#btnPlay"); ui.speedSel = $("#speedSel"); ui.btnFreeze = $("#btnFreeze");

  // Señales
  ui.signalsPanelLive = $("#signalsPanelLive");
  ui.signalEntryLive = $("#signalEntryLive"); ui.signalSideLive = $("#signalSideLive");
  ui.signalSLLive = $("#signalSLLive"); ui.signalSLExtraLive = $("#signalSLExtraLive");
  ui.signalTPLive = $("#signalTPLive"); ui.signalTPExtraLive = $("#signalTPExtraLive");
  ui.signalMotorLive = $("#signalMotorLive");

  ui.signalsPanelHist = $("#signalsPanelHist");
  ui.signalEntryHist = $("#signalEntryHist"); ui.signalSideHist = $("#signalSideHist");
  ui.signalSLHist = $("#signalSLHist"); ui.signalSLExtraHist = $("#signalSLExtraHist");
  ui.signalTPHist = $("#signalTPHist"); ui.signalTPExtraHist = $("#signalTPExtraHist");
  ui.signalMotorHist = $("#signalMotorHist");

  // Global
  ui.toasts = $("#toasts");
  ui.metaThemeColor = $("#metaThemeColor");
  ui.themeIcon = document.querySelector("[data-theme-icon]");
}

/* ============================================================================
   5. RENDERIZADO DE TABLA
   ============================================================================ */
function initGrid(containerId, cacheKey){
  if (gridInitialized[cacheKey]) return;
  const container = document.getElementById(containerId);
  if (!container) return;
  container.innerHTML = "";
  container.appendChild($("#tplHead").content.cloneNode(true));
  gridInitialized[cacheKey] = true;
}

function getRow(cacheKey, idx){
  let entry = rowCache[cacheKey].get(idx);
  if (entry) return entry;

  const row = $("#tplRow").content.firstElementChild.cloneNode(true);
  entry = {
    row,
    imbL:      row.querySelector('[data-k="imbL"]'),
    imbR:      row.querySelector('[data-k="imbR"]'),
    sellLbl:   row.querySelector('[data-k="sellLbl"]'),
    sellBar:   row.querySelector('[data-k="sellBar"]'),
    sellCell:  row.querySelector('[data-k="sell"]'),
    buyLbl:    row.querySelector('[data-k="buyLbl"]'),
    buyBar:    row.querySelector('[data-k="buyBar"]'),
    buyCell:   row.querySelector('[data-k="buy"]'),
    deltaCell: row.querySelector('[data-k="delta"]'),
    deltaLbl:  row.querySelector('[data-k="deltaLbl"]'),
    priceCell: row.querySelector('[data-k="price"]'),
    ratioBuy:  row.querySelector('[data-k="ratioBuy"]'),
    ratioSell: row.querySelector('[data-k="ratioSell"]'),
    levelCell: row.querySelector('[data-k="level"]'),
    levelDelta:row.querySelector('[data-k="levelDelta"]'),
    wallState: row.querySelector('[data-k="wallState"]')
  };
  rowCache[cacheKey].set(idx, entry);
  return entry;
}

function computeWallThreshold(buy, sell, lo, hi){
  let sum = 0;
  let activeLevels = 0;
  for (let i = lo; i <= hi; i++){
    const b = buy.get(i) || 0;
    const s = sell.get(i) || 0;
    if (b > 0){ sum += b; activeLevels++; }
    if (s > 0){ sum += s; activeLevels++; }
  }
  if (activeLevels === 0) return Infinity;
  const avg = sum / activeLevels;
  return Math.max(avg * 2.2, 250000);
}

function renderFootprint(cacheKey, containerId, snapshot){
  if (!snapshot || !snapshot.trades.length){
    const container = document.getElementById(containerId);
    if (container) container.innerHTML = "";
    gridInitialized[cacheKey] = false;
    for (const [, entry] of rowCache[cacheKey]) entry.row.remove();
    rowCache[cacheKey].clear();
    prevVol[cacheKey].clear();
    return null;
  }

  initGrid(containerId, cacheKey);
  const container = document.getElementById(containerId);

  const {
    bucket, buy, sell, maxVol, lo, hi, center,
    pocVolIdx, imbB, imbS, alB, alS,
    stB, stS, absB, absS, weakB, weakS,
    signal,
    imbPctB, imbPctS,        // Map idx -> bucket pct ("p80"|"p95"|"p99"|"")
    wallState,               // Map idx -> "stable"|"growing"|"shrinking"|"vanished"
    absSustained,            // Set idx con absorción sostenida
    zoneContext              // { dominantWall, vetoActive, ... }
  } = snapshot;

  const wallThreshold = snapshot.wallThreshold || computeWallThreshold(buy, sell, lo, hi);

  // Limpiar filas fuera de rango
  for (const [idx, entry] of rowCache[cacheKey]){
    if (idx < lo || idx > hi){
      entry.row.remove();
      rowCache[cacheKey].delete(idx);
    }
  }

  let prevSibling = container.querySelector(".row-head");

  for (let idx = hi; idx >= lo; idx--){
    const entry = getRow(cacheKey, idx);

    const nextEl = prevSibling.nextSibling;
    if (entry.row !== nextEl){
      container.insertBefore(entry.row, nextEl);
    }
    prevSibling = entry.row;

    const b = buy.get(idx) || 0;
    const s = sell.get(idx) || 0;
    const d = b - s;

    entry.row.classList.toggle("current", idx === center);
    entry.row.classList.toggle("poc", idx === pocVolIdx);

    // Muros institucionales
    const isWallBuy = b >= wallThreshold && idx !== pocVolIdx;
    const isWallSell = s >= wallThreshold && idx !== pocVolIdx;
    entry.row.classList.toggle("wall-buy", isWallBuy);
    entry.row.classList.toggle("wall-sell", isWallSell);

    // Estado del muro (nuevo)
    const ws = wallState ? wallState.get(idx) : null;
    entry.row.classList.toggle("wall-stable", ws === "stable");
    entry.row.classList.toggle("wall-growing", ws === "growing");
    entry.row.classList.toggle("wall-shrinking", ws === "shrinking");
    entry.row.classList.toggle("wall-vanished", ws === "vanished");

    // Absorción sostenida (nuevo)
    entry.row.classList.toggle("absorption-sustained", absSustained && absSustained.has(idx));

    // Líneas dinámicas
    entry.row.classList.remove("line-entry", "line-sl", "line-tp", "line-moving");
    if (state.lines && signal){
      const rowPrice = idx * bucket;
      const sigEntry = Math.round(signal.entry / bucket) * bucket;
      const sigSL = Math.round(signal.sl / bucket) * bucket;
      const sigTP = Math.round(signal.tp / bucket) * bucket;

      if (rowPrice === sigEntry) entry.row.classList.add("line-entry");
      if (rowPrice === sigSL) entry.row.classList.add("line-sl");
      if (rowPrice === sigTP) entry.row.classList.add("line-tp");

      if (signal.trailMoved && rowPrice === sigSL) entry.row.classList.add("line-moving");
    }

    const intB = state.heatmap ? Math.min(1, b / maxVol) * 0.45 : 0;
    const intS = state.heatmap ? Math.min(1, s / maxVol) * 0.45 : 0;

    const isAbsB = absB && absB.has(idx);
    const isAbsS = absS && absS.has(idx);

    // Compra
    entry.buyLbl.textContent = b > 0 ? fmtUSD(b) : "·";
    entry.buyLbl.dataset.zero = b > 0 ? "false" : "true";
    entry.buyCell.classList.toggle("heat", state.heatmap && b > 0);
    entry.buyCell.classList.toggle("absorbed", state.heatmap && d < 0 && b > 0);
    entry.buyCell.classList.toggle("absorbed-flow", Boolean(isAbsB));
    entry.buyCell.style.setProperty("--intensity", intB.toFixed(3));
    entry.buyBar.style.width = state.bars ? (b / maxVol * 100) + "%" : "0";

    // Venta
    entry.sellLbl.textContent = s > 0 ? fmtUSD(s) : "·";
    entry.sellLbl.dataset.zero = s > 0 ? "false" : "true";
    entry.sellCell.classList.toggle("heat", state.heatmap && s > 0);
    entry.sellCell.classList.toggle("absorbed", state.heatmap && d > 0 && s > 0);
    entry.sellCell.classList.toggle("absorbed-flow", Boolean(isAbsS));
    entry.sellCell.style.setProperty("--intensity", intS.toFixed(3));
    entry.sellBar.style.width = state.bars ? (s / maxVol * 100) + "%" : "0";

    // Flash por nueva liquidez
    const prevB = prevVol[cacheKey].get(idx + "_b");
    const prevS = prevVol[cacheKey].get(idx + "_s");
    if (prevB != null && b > prevB){
      entry.buyCell.classList.remove("flash");
      void entry.buyCell.offsetWidth;
      entry.buyCell.classList.add("flash");
    }
    if (prevS != null && s > prevS){
      entry.sellCell.classList.remove("flash");
      void entry.sellCell.offsetWidth;
      entry.sellCell.classList.add("flash");
    }
    prevVol[cacheKey].set(idx + "_b", b);
    prevVol[cacheKey].set(idx + "_s", s);

    entry.deltaLbl.textContent = fmtSigned(d);
    entry.deltaCell.dataset.dir = d > 0 ? "up" : d < 0 ? "dn" : "zero";
    entry.priceCell.textContent = (idx * bucket).toLocaleString("en-US");

    // Imbalance Venta
    const imbLTxt = imbS.get(idx) || "";
    const imbLAlert = alS.get(idx);
    const imbLStack = stS.has(idx);
    const weakL = weakS.get(idx);
    const pctL = imbPctS ? imbPctS.get(idx) : "";
    entry.imbL.className = "c c-imb c-imbL";
    if (pctL) entry.imbL.dataset.pct = pctL;
    else delete entry.imbL.dataset.pct;
    let fullL = imbLTxt;
    if (imbLAlert) fullL += imbLStack ? " 🔥" : (isAbsS ? " 🟡" : " 🚨");
    else if (isAbsS) fullL = (imbLTxt ? imbLTxt + " " : "") + "🟡";
    else if (weakL && imbLTxt === "∞·") fullL = "∞·";
    entry.imbL.textContent = fullL;
    if (imbLAlert && imbLStack) entry.imbL.classList.add("alert-stack");
    else if (isAbsS) entry.imbL.classList.add("absorbed");
    else if (imbLAlert) entry.imbL.classList.add("alert");

    // Imbalance Compra
    const imbRTxt = imbB.get(idx) || "";
    const imbRAlert = alB.get(idx);
    const imbRStack = stB.has(idx);
    const weakR = weakB.get(idx);
    const pctR = imbPctB ? imbPctB.get(idx) : "";
    entry.imbR.className = "c c-imb c-imbR";
    if (pctR) entry.imbR.dataset.pct = pctR;
    else delete entry.imbR.dataset.pct;
    let fullR = imbRTxt;
    if (imbRAlert) fullR += imbRStack ? " 🔥" : (isAbsB ? " 🟡" : " 🚨");
    else if (isAbsB) fullR = (imbRTxt ? imbRTxt + " " : "") + "🟡";
    else if (weakR && imbRTxt === "∞·") fullR = "∞·";
    entry.imbR.textContent = fullR;
    if (imbRAlert && imbRStack) entry.imbR.classList.add("alert-stack");
    else if (isAbsB) entry.imbR.classList.add("absorbed");
    else if (imbRAlert) entry.imbR.classList.add("alert");

    // Ratio
    const tot = b + s;
    if (tot > 0){
      entry.ratioBuy.style.width = (b / tot * 100) + "%";
      entry.ratioSell.style.width = (s / tot * 100) + "%";
    } else {
      entry.ratioBuy.style.width = "0%";
      entry.ratioSell.style.width = "0%";
    }

    // NUEVO: columna Δ nivel + estado del muro
    if (entry.levelDelta){
      entry.levelDelta.textContent = fmtSigned(d);
      entry.levelCell.dataset.dir = d > 0 ? "up" : d < 0 ? "dn" : "zero";
    }
    if (entry.wallState){
      if (ws){
        entry.wallState.dataset.state = ws;
        entry.wallState.title = `Muro ${ws}`;
      } else {
        delete entry.wallState.dataset.state;
        entry.wallState.removeAttribute("title");
      }
    }
  }

  for (const k of prevVol[cacheKey].keys()){
    const idx = parseInt(k.split("_")[0], 10);
    if (idx < lo || idx > hi) prevVol[cacheKey].delete(k);
  }

  return { pocVolIdx };
}

/* ============================================================================
   6. RENDERIZADO DE HEADER, TERMÓMETRO, SEÑALES Y MANIPULACIÓN
   ============================================================================ */
function renderHeader(snapshot, cursorMs){
  if (!snapshot) return;
  ui.clockLocal.textContent = msToLocal(cursorMs);
  ui.clockUtc.textContent = "UTC " + msToUtcShort(cursorMs);

  if (snapshot.lastPrice != null){
    const pStr = "$" + snapshot.lastPrice.toLocaleString("en-US", { minimumFractionDigits: 2, maximumFractionDigits: 2 });
    if (ui.priceEl.textContent !== pStr) ui.priceEl.textContent = pStr;
  } else {
    ui.priceEl.textContent = "—";
  }

  ui.pocVolEl.textContent = snapshot.pocVolIdx != null ? (snapshot.pocVolIdx * snapshot.bucket).toLocaleString("en-US") : "—";
  ui.pocDeltaEl.textContent = snapshot.pocDeltaIdx != null ? (snapshot.pocDeltaIdx * snapshot.bucket).toLocaleString("en-US") : "—";

  ui.deltaLongEl.textContent = fmtSigned(snapshot.delta);
  ui.deltaLongEl.className = "metric-value " + (snapshot.delta > 0 ? "up" : snapshot.delta < 0 ? "dn" : "");

  ui.tradesCountEl.textContent = snapshot.trades.length.toLocaleString("en-US");
  ui.volumeEl.textContent = fmtUSD(snapshot.total) + "$";

  const di = snapshot.instantDeltaShort || 0;
  ui.deltaInstEl.textContent = fmtSigned(di);
  ui.deltaInstEl.className = "metric-value " + (di > 0 ? "up" : di < 0 ? "dn" : "");

  if (ui.deltaInstDir){
    if (di > 1000){
      ui.deltaInstDir.textContent = "▲";
      ui.deltaInstDir.className = "up";
      ui.deltaInstDir.setAttribute("aria-label", "delta instantáneo positivo");
    } else if (di < -1000){
      ui.deltaInstDir.textContent = "▼";
      ui.deltaInstDir.className = "dn";
      ui.deltaInstDir.setAttribute("aria-label", "delta instantáneo negativo");
    } else {
      ui.deltaInstDir.textContent = "";
      ui.deltaInstDir.className = "";
      ui.deltaInstDir.setAttribute("aria-label", "delta instantáneo neutro");
    }
  }
}

function renderCoverage(ratio){
  let label, key;
  if (ratio >= 0.98) { label = "completa"; key = "full"; }
  else if (ratio >= 0.6) { label = "parcial " + Math.round((1 - ratio) * 100) + "%"; key = "partial"; }
  else { label = "insuficiente " + Math.round((1 - ratio) * 100) + "%"; key = "low"; }
  ui.coverage.dataset.state = key;
  ui.covTxt.textContent = label;
}

function renderThermo(which, snapshot){
  const fillAcum = which === "live" ? ui.thermoFillLive : ui.thermoFillHist;
  const fillInst = which === "live" ? ui.thermoFillInstLive : ui.thermoFillInstHist;
  const fillZone = which === "live" ? ui.thermoFillZoneLive : ui.thermoFillZoneHist;
  const zoneWrap = which === "live" ? ui.thermoZoneWrapLive : ui.thermoZoneWrapHist;
  const valEl = which === "live" ? ui.thermoValLive : ui.thermoValHist;
  const imbEl = which === "live" ? ui.thermoImbLive : ui.thermoImbHist;
  const warnEl = which === "live" ? ui.thermoWarnLive : ui.thermoWarnHist;

  if (!fillAcum || !snapshot) return;

  const maxAcum = snapshot.maxAcumRef || 400000;
  const maxInst = snapshot.maxInstRef || 50000;
  const mobile = isMobile();

  // Acumulada
  let pctAcum = 50 + (snapshot.delta / maxAcum) * 50;
  pctAcum = Math.max(1, Math.min(99, pctAcum));
  if (mobile){
    fillAcum.style.width = pctAcum + "%";
    fillAcum.style.height = "";
  } else {
    fillAcum.style.height = pctAcum + "%";
    fillAcum.style.width = "";
  }
  fillAcum.classList.toggle("is-negative", snapshot.delta < 0);
  fillAcum.parentElement.setAttribute("aria-valuenow", Math.round(pctAcum));
  fillAcum.parentElement.setAttribute("aria-valuetext", fmtSigned(snapshot.delta) + " USD");

  // Instantánea
  const instShort = snapshot.instantDeltaShort || 0;
  let pctInst = 50 + (instShort / maxInst) * 50;
  pctInst = Math.max(1, Math.min(99, pctInst));
  if (mobile){
    fillInst.style.width = pctInst + "%";
    fillInst.style.height = "";
  } else {
    fillInst.style.height = pctInst + "%";
    fillInst.style.width = "";
  }
  fillInst.classList.toggle("is-negative", instShort < 0);
  fillInst.parentElement.setAttribute("aria-valuenow", Math.round(pctInst));
  fillInst.parentElement.setAttribute("aria-valuetext", fmtSigned(instShort) + " USD");

  // NUEVO: tercera barra — delta de la zona del muro dominante
  if (fillZone && zoneWrap){
    const zone = snapshot.zoneContext && snapshot.zoneContext.dominantWall;
    if (!zone){
      zoneWrap.dataset.state = "empty";
      zoneWrap.setAttribute("aria-valuetext", "sin zona dominante");
      fillZone.style.width = mobile ? "50%" : "";
      fillZone.style.height = mobile ? "" : "50%";
      fillZone.classList.remove("is-negative");
    } else {
      zoneWrap.dataset.state = "active";
      const zoneDelta = zone.delta || 0;
      const zoneMax = Math.max(Math.abs(snapshot.delta) || 1, 1);
      let pctZone = 50 + (zoneDelta / zoneMax) * 50;
      pctZone = Math.max(1, Math.min(99, pctZone));
      if (mobile){
        fillZone.style.width = pctZone + "%";
        fillZone.style.height = "";
      } else {
        fillZone.style.height = pctZone + "%";
        fillZone.style.width = "";
      }
      fillZone.classList.toggle("is-negative", zoneDelta < 0);
      zoneWrap.setAttribute("aria-valuenow", Math.round(pctZone));
      zoneWrap.setAttribute("aria-valuetext",
        `Zona ${(zone.idx * snapshot.bucket).toLocaleString("en-US")}: ${fmtSigned(zoneDelta)} USD`);
      zoneWrap.dataset.absorption = zone.absorption ? "true" : "false";
    }
  }

  // Valores
  if (snapshot.delta > 0){ valEl.textContent = "+" + fmtUSD(snapshot.delta); valEl.style.color = "var(--green)"; }
  else if (snapshot.delta < 0){ valEl.textContent = "-" + fmtUSD(Math.abs(snapshot.delta)); valEl.style.color = "var(--red)"; }
  else { valEl.textContent = "0"; valEl.style.color = "var(--text-dim)"; }

  // Imbalance general
  const tot = snapshot.total;
  if (tot > 0){
    const ratio = (snapshot.tb / tot) * 100;
    if (ratio >= 55) { imbEl.textContent = `C ${ratio.toFixed(0)}%`; imbEl.style.color = "var(--green)"; }
    else if (ratio <= 45) { imbEl.textContent = `V ${(100 - ratio).toFixed(0)}%`; imbEl.style.color = "var(--red)"; }
    else { imbEl.textContent = "≈ neutro"; imbEl.style.color = "var(--text-dim)"; }
  } else { imbEl.textContent = "—"; }

  // Absorción
  const hasAbs = (snapshot.absB && snapshot.absB.size > 0) || (snapshot.absS && snapshot.absS.size > 0);
  const hasExh = snapshot.pressure && snapshot.pressure.exhaustion;
  if (hasAbs || hasExh){
    warnEl.hidden = false;
    warnEl.textContent = hasAbs ? "⚠ ABSORCIÓN" : "⚠ AGOTAMIENTO";
    if (state.sound && !state.signalLocked) vibrate();
  } else {
    warnEl.hidden = true;
  }
}

function renderSignals(which, snapshot){
  const panel = which === "live" ? ui.signalsPanelLive : ui.signalsPanelHist;
  const entryEl = which === "live" ? ui.signalEntryLive : ui.signalEntryHist;
  const sideEl = which === "live" ? ui.signalSideLive : ui.signalSideHist;
  const slEl = which === "live" ? ui.signalSLLive : ui.signalSLHist;
  const slExtraEl = which === "live" ? ui.signalSLExtraLive : ui.signalSLExtraHist;
  const tpEl = which === "live" ? ui.signalTPLive : ui.signalTPHist;
  const tpExtraEl = which === "live" ? ui.signalTPExtraLive : ui.signalTPExtraHist;
  const motorEl = which === "live" ? ui.signalMotorLive : ui.signalMotorHist;

  if (!panel) return;

  panel.classList.toggle("is-locked", Boolean(state.signalLocked));

  if (!snapshot || !snapshot.signal || !state.lines){
    panel.hidden = true;
    return;
  }

  const sig = snapshot.signal;
  panel.hidden = false;

  const sideTxt = sig.side === "long" ? "LARGO" : "CORTO";

  entryEl.textContent = "$" + fmtPrice(sig.entry);
  sideEl.textContent = sideTxt;
  sideEl.className = "signal-side " + (sig.side === "long" ? "long" : "short");

  slEl.textContent = "$" + fmtPrice(sig.sl);
  const slRisk = Math.abs(sig.entry - sig.sl);
  slExtraEl.textContent = `Riesgo: -${fmtPrice(slRisk)}$`;

  tpEl.textContent = "$" + fmtPrice(sig.tp);
  const tpGain = Math.abs(sig.tp - sig.entry);
  const rr = slRisk > 0 ? (tpGain / slRisk).toFixed(1) : "∞";
  tpExtraEl.textContent = `Ganancia: +${fmtPrice(tpGain)}$ (R:B ${rr})`;

  // Motor
  if (sig.motor === "A") {
    motorEl.textContent = "⚡ Motor A: Caza-Reversiones (Absorción + Δ)";
    motorEl.className = "signal-motor motor-a";
  } else if (sig.motor === "B") {
    motorEl.textContent = "🌊 Motor B: Surfista de Tendencia (Stacked + Δ)";
    motorEl.className = "signal-motor motor-b";
  } else if (sig.motor === "ABS") {
    motorEl.textContent = "🧱 Motor ABS: Absorción sostenida (muro que aguanta)";
    motorEl.className = "signal-motor motor-abs";
  } else if (sig.motor === "SPOOF") {
    motorEl.textContent = "💨 Motor SPOOF: Ruptura de muro retirado";
    motorEl.className = "signal-motor motor-spoof";
  } else {
    motorEl.textContent = "🎯 Señal Estructural (POC / Imbalance Dominante)";
    motorEl.className = "signal-motor";
  }
}

/* NUEVO: panel de manipulación */
function renderManip(which, snapshot){
  const panel = which === "live" ? ui.manipPanelLive : ui.manipPanelHist;
  const badgeEl = which === "live" ? ui.manipBadgeLive : ui.manipBadgeHist;
  const levelEl = which === "live" ? ui.manipLevelLive : ui.manipLevelHist;
  const stateEl = which === "live" ? ui.manipStateLive : ui.manipStateHist;
  const ageEl = which === "live" ? ui.manipAgeLive : ui.manipAgeHist;
  const volEl = which === "live" ? ui.manipVolLive : ui.manipVolHist;
  const ratioEl = which === "live" ? ui.manipRatioLive : ui.manipRatioHist;
  const penEl = which === "live" ? ui.manipPenLive : ui.manipPenHist;

  if (!panel) return;

  const zone = snapshot && snapshot.zoneContext && snapshot.zoneContext.dominantWall;
  if (!zone){
    panel.hidden = true;
    delete panel.dataset.zoneType;
    return;
  }

  panel.hidden = false;
  panel.dataset.zoneType = zone.type || "support";
  panel.style.animation = "manipIn .25s ease-out";

  const typeLabel =
    zone.type === "absorption-bid" ? "ABSORCIÓN BID" :
    zone.type === "absorption-ask" ? "ABSORCIÓN ASK" :
    zone.type === "spoof-bid" ? "SPOOF BID" :
    zone.type === "spoof-ask" ? "SPOOF ASK" :
    zone.type === "support" ? "SOPORTE" :
    zone.type === "resistance" ? "RESISTENCIA" : "ZONA";

  badgeEl.textContent = typeLabel;
  levelEl.textContent = "$" + fmtPrice(zone.idx * snapshot.bucket);
  stateEl.textContent = zone.wallState ? `· ${zone.wallState}` : "";

  const ageMs = zone.ageMs || 0;
  const ageSec = Math.round(ageMs / 1000);
  const ageTxt = ageSec < 60 ? ageSec + "s" : Math.floor(ageSec / 60) + "m" + (ageSec % 60 ? " " + (ageSec % 60) + "s" : "");
  ageEl.textContent = ageTxt;

  volEl.textContent = fmtUSD(zone.vol || 0);
  ratioEl.textContent = (zone.ratioContra != null ? zone.ratioContra.toFixed(2) : "—") + ":1";
  penEl.textContent = (zone.penetrationTicks != null ? zone.penetrationTicks : "—") + " t";
}

/* ============================================================================
   7. FRAMES Y TIMELINE
   ============================================================================ */
function renderLiveFrame(){
  if (state.mode !== "live" || state.paused) return;

  const snapshot = FP.getLiveSnapshot();
  if (!snapshot) return;

  ui.liveEmpty.hidden = snapshot.trades.length > 0;

  renderFootprint("live", "liveGrid", snapshot);
  renderHeader(snapshot, snapshot.cursorMs);
  renderCoverage(1);
  renderThermo("live", snapshot);
  renderSignals("live", snapshot);
  renderManip("live", snapshot);

  const totalStack = (snapshot.stB ? snapshot.stB.size : 0) + (snapshot.stS ? snapshot.stS.size : 0);
  if (totalStack > lastStackCount && !state.signalLocked) vibrate();
  lastStackCount = totalStack;

  const feed = FP.getFeed();
  const age = snapshot.trades.length ? ((snapshot.cursorMs - snapshot.trades[snapshot.trades.length - 1].T) / 1000).toFixed(1) : "—";
  ui.statusLive.textContent = (feed ? feed.getStatus() : "—") + " · último trade hace " + age + "s" + (FP.getRestNote() ? " · " + FP.getRestNote() : "");
  ui.connDot.className = "dot " + (feed && feed.getStatus() === "EN VIVO" ? "live" : "err");

  // Restaurar connLabel si venía de histórico
  if (ui.connLabel && ui.connLabel.textContent === "HISTÓRICO"){
    ui.connLabel.textContent = "EN VIVO";
  }
}

async function renderHistFrame(showLoading){
  if (state.mode !== "hist") return;
  if (showLoading){ ui.histEmpty.hidden = false; ui.histEmptyTxt.textContent = "Cargando…"; }

  await FP.ensureHistLoaded(state.histCursor, (txt) => {
    ui.histEmpty.hidden = false; ui.histEmptyTxt.textContent = txt;
  });

  const snapshot = FP.getHistSnapshot(state.histCursor);
  if (!snapshot) return;

  ui.histEmpty.hidden = snapshot.trades.length > 0;
  if (!snapshot.trades.length) ui.histEmptyTxt.textContent = "Sin trades en esta ventana.";

  renderFootprint("hist", "histGrid", snapshot);
  renderHeader(snapshot, state.histCursor);
  renderThermo("hist", snapshot);
  renderSignals("hist", snapshot);
  renderManip("hist", snapshot);

  const winMin = getActiveWindowMin();
  const ratio = FP.coverageRatio(Math.max(CONFIG.LISTING_MS, state.histCursor - winMin * 60000), Math.min(state.histCursor, Date.now()));
  renderCoverage(ratio);

  // Scrubber: max = Date.now() fijo, no histCursor
  const scrub = ui.scrub;
  const now = Date.now();
  const oneHourAgo = Math.max(CONFIG.LISTING_MS, now - 60 * 60 * 1000);
  scrub.min = oneHourAgo; scrub.max = now; scrub.value = Math.min(state.histCursor, now);

  renderTimeline(snapshot, oneHourAgo, now);

  const playTxt = state.histFrozen ? "⏸ congelado" : (state.histPlaying ? `▶ replay ×${CONFIG.SPEEDS[state.histSpeed - 1] || 1}` : "⏸ pausado");
  ui.statusHist.textContent = playTxt + ` · ${msToLocal(state.histCursor)}` + (FP.getRestNote() ? " · " + FP.getRestNote() : "");
  ui.connDot.className = "dot replay";
  ui.connLabel.textContent = "HISTÓRICO";
}

function renderTimeline(snapshot, startMs, endMs){
  const container = ui.timelineEvents;
  if (!container) return;
  container.innerHTML = "";
  const span = endMs - startMs;
  if (span <= 0) return;
  const events = snapshot.events || [];
  const frag = document.createDocumentFragment();
  for (const ev of events){
    if (ev.t < startMs || ev.t > endMs) continue;
    const pct = ((ev.t - startMs) / span) * 100;
    const dot = document.createElement("span");
    dot.className = "tl-dot"; dot.dataset.type = ev.type; dot.style.left = pct + "%";
    frag.appendChild(dot);
  }
  container.appendChild(frag);
}

/* ============================================================================
   8. LOOPS
   ============================================================================ */
let liveRafId = null, liveLastDraw = 0;
function liveLoop(){
  if (liveRafId) return;
  liveRafId = requestAnimationFrame(() => {
    liveRafId = null;
    const now = performance.now();
    if (state.mode === "live" && !state.paused && now - liveLastDraw >= CONFIG.REFRESH_LIVE){
      liveLastDraw = now;
      renderLiveFrame();
    }
    liveLoop();
  });
}

let histRafId = null;
function scheduleHistRender(showLoading){
  if (histRafId) return;
  histRafId = requestAnimationFrame(() => { histRafId = null; renderHistFrame(showLoading); });
}

function histReplayLoop(){
  setInterval(() => {
    if (state.mode !== "hist" || !state.histPlaying || state.histFrozen) return;
    const now = Date.now();
    const speed = CONFIG.SPEEDS[state.histSpeed - 1] || 1;
    if (now - state.histLastTick >= 1000 / speed){
      state.histLastTick = now;
      // Avance real: step = PLAY_STEP_S * speed
      const step = CONFIG.PLAY_STEP_S * 1000 * speed;
      state.histCursor = Math.min(now, state.histCursor + step);
      if (state.histCursor >= now){ state.histPlaying = false; ui.btnPlay.textContent = "▶"; ui.btnPlay.setAttribute("aria-pressed", "false"); }
      scheduleHistRender(false);
    }
  }, 50);
}

/* ============================================================================
   9. ACCIONES
   ============================================================================ */
function invalidateGrids(){
  for (const key of ["live", "hist"]){
    for (const [, entry] of rowCache[key]) entry.row.remove();
    rowCache[key].clear(); prevVol[key].clear(); gridInitialized[key] = false;
    const grid = document.getElementById(key === "live" ? "liveGrid" : "histGrid");
    if (grid) grid.innerHTML = "";
  }
}

function updatePillLabels(){
  const winMin = getActiveWindowMin();
  const winTxt = winMin + "m";

  if (ui.pillWindowVal) ui.pillWindowVal.textContent = winTxt;
  if (ui.pillWindow) ui.pillWindow.dataset.short = winMin <= 5 ? "true" : "false";
  if (ui.btnWindowHist){
    const b = ui.btnWindowHist.querySelector("b");
    if (b) b.textContent = winTxt;
  }

  if (ui.deltaWindowLabel) ui.deltaWindowLabel.textContent = "Δ " + winTxt;
  if (ui.volWindowLabel) ui.volWindowLabel.textContent = "Vol " + winTxt;
  if (ui.thermoSubLive) ui.thermoSubLive.textContent = "Δ " + winTxt;
  if (ui.thermoSubHist) ui.thermoSubHist.textContent = "Δ " + winTxt;

  ui.pillBucketVal.textContent = state.bucket + "$";

  // Modo de imbalance
  const modeLabel = state.imbMode === "diagonal" ? "diag"
                  : state.imbMode === "nivel" ? "nivel"
                  : state.imbMode === "media" ? "media"
                  : state.imbMode === "percentil" ? "pct"
                  : state.imbMode === "compuesto" ? "comp" : "diag";
  if (ui.pillImbModeVal) ui.pillImbModeVal.textContent = modeLabel;
  const histImbB = $("#btnImbHist b");
  if (histImbB) histImbB.textContent = modeLabel;

  // Umbral de imbalance
  if (ui.pillImbThrInput && document.activeElement !== ui.pillImbThrInput){
    ui.pillImbThrInput.value = String(Math.round(state.threshold));
    ui.pillImbThrInput.disabled = state.thresholdMode === "auto";
  }
  if (ui.pillImbThrAuto){
    ui.pillImbThrAuto.setAttribute("aria-pressed", state.thresholdMode === "auto" ? "true" : "false");
  }
  const thrWrap = ui.pillImbThrInput ? ui.pillImbThrInput.closest(".pill-edit") : null;
  if (thrWrap) thrWrap.dataset.auto = state.thresholdMode === "auto" ? "true" : "false";

  // Monto mínimo
  if (ui.pillMinInput && document.activeElement !== ui.pillMinInput){
    ui.pillMinInput.value = String(Math.round(state.minUSD));
    ui.pillMinInput.disabled = state.minMode === "auto";
  }
  if (ui.pillMinAuto) ui.pillMinAuto.setAttribute("aria-pressed", state.minMode === "auto" ? "true" : "false");
  if (ui.pillMinRel) ui.pillMinRel.setAttribute("aria-pressed", state.minRelativeToImb ? "true" : "false");
  if (ui.pillMinRel) ui.pillMinRel.dataset.relative = state.minRelativeToImb ? "true" : "false";
  const minWrap = ui.pillMinInput ? ui.pillMinInput.closest(".pill-edit") : null;
  if (minWrap) minWrap.dataset.auto = state.minMode === "auto" ? "true" : "false";

  const histMinB = $("#btnMinHist b");
  if (histMinB) histMinB.textContent = fmtUSD(state.minUSD);

  ui.pillHeat.setAttribute("aria-pressed", state.heatmap ? "true" : "false");
  ui.pillBars.setAttribute("aria-pressed", state.bars ? "true" : "false");
  ui.pillThermo.setAttribute("aria-pressed", state.thermo ? "true" : "false");
  if (ui.pillLines) ui.pillLines.setAttribute("aria-pressed", state.lines ? "true" : "false");
  if (ui.pillWalls) ui.pillWalls.setAttribute("aria-pressed", state.walls ? "true" : "false");
  ui.pillSound.setAttribute("aria-pressed", state.sound ? "true" : "false");

  const histBucketB = $("#btnBucketHist b");
  if (histBucketB) histBucketB.textContent = state.bucket + "$";
}

function nextWindow(){
  if (typeof FP.nextWindow === "function") FP.nextWindow();
  invalidateGrids();
  updatePillLabels();
  toast(`Ventana: ${getActiveWindowMin()}m`, "ok");
  if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(true);
}

function nextBucket(){ FP.nextBucket(); invalidateGrids(); updatePillLabels(); if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false); }
function nextImbMode(){ if (typeof FP.nextImbMode === "function") FP.nextImbMode(); invalidateGrids(); updatePillLabels(); if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false); }

function thrDelta(d){ FP.thrDelta(d); invalidateGrids(); updatePillLabels(); if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false); }

function togglePauseLive(){ state.paused = !state.paused; if (!state.paused) renderLiveFrame(); }

function toggleSignalLock(){
  const wasLocked = state.signalLocked;
  if (typeof FP.lockCurrentSignal === "function" && !wasLocked){
    FP.lockCurrentSignal();
  } else if (typeof FP.unlockSignal === "function" && wasLocked){
    FP.unlockSignal();
  }
  state.signalLocked = !wasLocked;

  [ui.btnSignalLock, ui.btnSignalLockHist].forEach(btn => {
    if (!btn) return;
    btn.classList.toggle("on", state.signalLocked);
    btn.setAttribute("aria-pressed", state.signalLocked ? "true" : "false");
    btn.textContent = state.signalLocked ? "📌 Señal fijada" : "📌 Fijar señal";
  });

  if (ui.signalsPanelLive) ui.signalsPanelLive.classList.toggle("is-locked", state.signalLocked);
  if (ui.signalsPanelHist) ui.signalsPanelHist.classList.toggle("is-locked", state.signalLocked);

  toast(state.signalLocked ? "Señal fijada en pantalla" : "Señal liberada (dinámica)", "ok");
  if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false);
}

function histSeek(deltaMs){
  state.histCursor = Math.max(CONFIG.LISTING_MS, Math.min(Date.now(), state.histCursor + deltaMs));
  state.histFrozen = true;
  ui.btnFreeze.setAttribute("aria-pressed", "true");
  ui.btnFreeze.textContent = "⏸ Congelado";
  scheduleHistRender(false);
}

function histSetFrozen(frozen){
  state.histFrozen = frozen;
  ui.btnFreeze.setAttribute("aria-pressed", frozen ? "true" : "false");
  ui.btnFreeze.textContent = frozen ? "⏸ Congelado" : "▶ Replay";
}

function histPlayToggle(){
  if (state.histPlaying){
    state.histPlaying = false;
    ui.btnPlay.textContent = "▶";
    ui.btnPlay.setAttribute("aria-pressed", "false");
  } else {
    state.histPlaying = true;
    state.histFrozen = false;
    histSetFrozen(false);
    ui.btnPlay.textContent = "⏸";
    ui.btnPlay.setAttribute("aria-pressed", "true");
  }
}

function switchMode(mode){
  if (state.mode === mode) return;
  state.mode = mode;
  $("#tabLive").setAttribute("aria-selected", mode === "live" ? "true" : "false");
  $("#tabHist").setAttribute("aria-selected", mode === "hist" ? "true" : "false");
  $("#panelLive").hidden = mode !== "live";
  $("#panelHist").hidden = mode !== "hist";
  if (mode === "live"){
    FP.startLive(); renderLiveFrame();
  } else {
    state.histCursor = Date.now();
    state.histFrozen = true;
    state.histPlaying = false;
    ui.btnPlay.textContent = "▶";
    ui.btnPlay.setAttribute("aria-pressed", "false");
    ui.dtInput.value = msToInputValue(state.histCursor);
    histSetFrozen(true);
    scheduleHistRender(true);
  }
}

function applyTheme(theme){
  document.documentElement.setAttribute("data-theme", theme);
  state.theme = theme;
  try { localStorage.setItem("fp-theme", theme); } catch(_){}
  if (ui.metaThemeColor){
    ui.metaThemeColor.setAttribute("content", theme === "light" ? "#f6f7f9" : "#000000");
  }
  if (ui.themeIcon){
    ui.themeIcon.textContent = theme === "light" ? "☀️" : "🌙";
  }
}

/* ============================================================================
   10. BINDINGS
   ============================================================================ */
function bindEvents(){
  $("#tabLive").addEventListener("click", () => switchMode("live"));
  $("#tabHist").addEventListener("click", () => switchMode("hist"));
  $("#btnTheme").addEventListener("click", () => applyTheme(state.theme === "dark" ? "light" : "dark"));

  if (ui.pillWindow) ui.pillWindow.addEventListener("click", nextWindow);
  ui.pillBucket.addEventListener("click", nextBucket);
  if (ui.pillImbMode) ui.pillImbMode.addEventListener("click", nextImbMode);

  // Umbral de imbalance: input + toggle auto
  if (ui.pillImbThrInput){
    ui.pillImbThrInput.addEventListener("input", e => {
      const v = parseFloat(e.target.value);
      if (isNaN(v)) return;
      state.threshold = Math.max(100, Math.min(5000, v));
      clearTimeout(debounceThrTimer);
      debounceThrTimer = setTimeout(() => {
        invalidateGrids(); updatePillLabels();
        if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false);
      }, 400);
    });
    ui.pillImbThrInput.addEventListener("keydown", e => {
      if (e.key === "Enter") e.target.blur();
    });
  }
  if (ui.pillImbThrAuto){
    ui.pillImbThrAuto.addEventListener("click", () => {
      state.thresholdMode = state.thresholdMode === "auto" ? "manual" : "auto";
      updatePillLabels();
      invalidateGrids();
      if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false);
      toast(state.thresholdMode === "auto" ? "Umbral de imbalance: auto" : "Umbral de imbalance: manual", "ok");
    });
  }

  // Monto mínimo: input + toggle auto + relativo
  if (ui.pillMinInput){
    ui.pillMinInput.addEventListener("input", e => {
      const v = parseFloat(e.target.value);
      if (isNaN(v)) return;
      state.minUSD = Math.max(0, v);
      clearTimeout(debounceMinTimer);
      debounceMinTimer = setTimeout(() => {
        invalidateGrids(); updatePillLabels();
        if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false);
      }, 400);
    });
    ui.pillMinInput.addEventListener("keydown", e => {
      if (e.key === "Enter") e.target.blur();
    });
  }
  if (ui.pillMinAuto){
    ui.pillMinAuto.addEventListener("click", () => {
      state.minMode = state.minMode === "auto" ? "manual" : "auto";
      updatePillLabels();
      invalidateGrids();
      if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false);
      toast(state.minMode === "auto" ? "Monto mínimo: auto" : "Monto mínimo: manual", "ok");
    });
  }
  if (ui.pillMinRel){
    ui.pillMinRel.addEventListener("click", () => {
      state.minRelativeToImb = !state.minRelativeToImb;
      updatePillLabels();
      invalidateGrids();
      if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false);
      toast(state.minRelativeToImb ? "Monto mínimo relativo al imbalance" : "Monto mínimo absoluto", "ok");
    });
  }

  ui.pillHeat.addEventListener("click", () => { state.heatmap = !state.heatmap; updatePillLabels(); invalidateGrids(); if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false); });
  ui.pillBars.addEventListener("click", () => { state.bars = !state.bars; updatePillLabels(); invalidateGrids(); if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false); });
  ui.pillThermo.addEventListener("click", () => { state.thermo = !state.thermo; updatePillLabels(); document.querySelectorAll(".thermo").forEach(el => { el.style.display = state.thermo ? "" : "none"; }); });
  if (ui.pillLines) ui.pillLines.addEventListener("click", () => { state.lines = !state.lines; updatePillLabels(); if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false); });
  if (ui.pillWalls) ui.pillWalls.addEventListener("click", () => { state.walls = !state.walls; updatePillLabels(); invalidateGrids(); if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false); });
  ui.pillSound.addEventListener("click", () => { state.sound = !state.sound; updatePillLabels(); });

  $("#btnPauseLive").addEventListener("click", togglePauseLive);
  $("#btnClearLive").addEventListener("click", () => {
    store.clear(); coverage.intervals = [];
    if (typeof FP.clearActiveSignals === "function") FP.clearActiveSignals();
    invalidateGrids(); toast("Memoria limpiada", "ok"); renderLiveFrame();
  });

  if (ui.btnSignalLock) ui.btnSignalLock.addEventListener("click", toggleSignalLock);
  if (ui.btnSignalLockHist) ui.btnSignalLockHist.addEventListener("click", toggleSignalLock);

  $("#btnGo").addEventListener("click", () => {
    const v = ui.dtInput.value; if (!v) return;
    const ms = new Date(v).getTime();
    if (isNaN(ms)) return toast("Fecha inválida", "err");
    if (ms > Date.now()) return toast("Esa hora es futura", "err");
    if (ms < CONFIG.LISTING_MS) return toast("Antes del listing", "err");
    state.histCursor = ms; histSetFrozen(true); scheduleHistRender(true);
  });
  $("#btnNow").addEventListener("click", () => { state.histCursor = Date.now(); ui.dtInput.value = msToInputValue(state.histCursor); histSetFrozen(true); scheduleHistRender(true); });
  ui.btnFreeze.addEventListener("click", () => { histSetFrozen(!state.histFrozen); if (state.histFrozen){ state.histPlaying = false; ui.btnPlay.textContent = "▶"; ui.btnPlay.setAttribute("aria-pressed", "false"); } });

  $("#btnBackBig").addEventListener("click", () => histSeek(-CONFIG.STEP_BIG_S * 1000));
  $("#btnBackSmall").addEventListener("click", () => histSeek(-CONFIG.STEP_SMALL_S * 1000));
  $("#btnFwdSmall").addEventListener("click", () => histSeek(CONFIG.STEP_SMALL_S * 1000));
  $("#btnFwdBig").addEventListener("click", () => histSeek(CONFIG.STEP_BIG_S * 1000));
  ui.btnPlay.addEventListener("click", histPlayToggle);
  ui.speedSel.addEventListener("change", e => { const i = CONFIG.SPEEDS.indexOf(+e.target.value); state.histSpeed = i >= 0 ? i + 1 : 2; });
  ui.scrub.addEventListener("input", e => {
    state.histCursor = Math.min(+e.target.value, Date.now());
    histSetFrozen(true);
    state.histPlaying = false;
    ui.btnPlay.textContent = "▶";
    ui.btnPlay.setAttribute("aria-pressed", "false");
    scheduleHistRender(false);
  });

  if (ui.btnWindowHist) ui.btnWindowHist.addEventListener("click", nextWindow);
  $("#btnBucketHist").addEventListener("click", nextBucket);
  $("#btnImbHist").addEventListener("click", nextImbMode);
  $("#btnMinHist").addEventListener("click", () => {
    // En histórico, el botón Mín cicla el modo auto/manual del monto
    state.minMode = state.minMode === "auto" ? "manual" : "auto";
    updatePillLabels(); invalidateGrids();
    if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false);
    toast(state.minMode === "auto" ? "Monto mínimo: auto" : "Monto mínimo: manual", "ok");
  });

  document.addEventListener("keydown", e => {
    const tag = e.target.tagName;
    if (tag === "INPUT" || tag === "SELECT" || tag === "TEXTAREA") return;
    const k = e.key, kl = k.toLowerCase();
    if (kl === "g"){ nextWindow(); e.preventDefault(); return; }
    if (kl === "f"){ toggleSignalLock(); e.preventDefault(); return; }
    if (kl === "b"){ nextBucket(); e.preventDefault(); return; }
    if (kl === "i"){ nextImbMode(); e.preventDefault(); return; }
    if (kl === "m"){ state.minMode = state.minMode === "auto" ? "manual" : "auto"; updatePillLabels(); invalidateGrids(); if (state.mode === "live") renderLiveFrame(); else scheduleHistRender(false); e.preventDefault(); return; }
    if (k === "["){ thrDelta(-50); e.preventDefault(); return; }
    if (k === "]"){ thrDelta(50); e.preventDefault(); return; }
    if (kl === "h"){ ui.pillHeat.click(); e.preventDefault(); return; }
    if (kl === "v"){ ui.pillBars.click(); e.preventDefault(); return; }
    if (kl === "t"){ ui.pillThermo.click(); e.preventDefault(); return; }
    if (kl === "l" && ui.pillLines){ ui.pillLines.click(); e.preventDefault(); return; }
    if (kl === "w" && ui.pillWalls){ ui.pillWalls.click(); e.preventDefault(); return; }
    if (kl === "n"){ ui.pillSound.click(); e.preventDefault(); return; }
    if (state.mode === "live"){ if (kl === "p"){ togglePauseLive(); e.preventDefault(); } return; }
    if (k === "ArrowLeft" || kl === "a"){ histSeek(-CONFIG.STEP_SMALL_S * 1000); e.preventDefault(); }
    else if (k === "ArrowRight" || kl === "d"){ histSeek(CONFIG.STEP_SMALL_S * 1000); e.preventDefault(); }
    else if (k === "ArrowDown" || kl === "s"){ histSeek(-CONFIG.STEP_BIG_S * 1000); e.preventDefault(); }
    else if (k === "ArrowUp" || kl === "w"){ histSeek(CONFIG.STEP_BIG_S * 1000); e.preventDefault(); }
    else if (k === " "){ histPlayToggle(); e.preventDefault(); }
  });

  window.addEventListener("resize", () => { if (state.mode === "live") renderLiveFrame(); else if (state.mode === "hist") scheduleHistRender(false); });
}

/* ============================================================================
   11. BOOT
   ============================================================================ */
async function boot(){
  cacheUI(); bindEvents();
  const savedTheme = (() => { try { return localStorage.getItem("fp-theme"); } catch(_){ return null; } })();
  applyTheme(savedTheme === "light" ? "light" : "dark");
  updatePillLabels();
  liveLoop(); histReplayLoop();
  await FP.startLive();
  renderLiveFrame();
}

if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
else boot();

})();
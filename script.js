/* ============================================================================
   SCRIPT.JS — Footprint BTCUSDT · Order Flow Pro
   Motor de datos, microestructura y cálculos cuantitativos.
   No conoce el DOM. Expone window.FP.

   Capacidades:
   - Store con búsqueda binaria y retención máxima.
   - Cobertura de datos con intervalos fusionados y acotados.
   - Agregación y umbrales dinámicos (percentiles locales).
   - Modos de imbalance: diagonal, nivel, media, percentil, compuesto.
   - Umbral de imbalance y monto mínimo: manual / auto / relativo.
   - Tracking temporal de muros (wallTracker): stable/growing/shrinking/vanished.
   - Absorción por nivel (absorptionTracker) y absorción sostenida.
   - Detección de spoofing (muro retirado sin cruce vs ejecutado con cruce).
   - zoneContext con muro dominante (tipo, edad, ratio, penetración, delta).
   - Reglas de señal: A (absorción sostenida), B (ruptura de muro),
     E (veto contra muro dominante), F (validación direccional de TP).
   - Lock real de señal (lockCurrentSignal / unlockSignal).
   - Histórico determinista: no muta activeSignalHist por trailing.
   - detectEvents O(N) con tipos: volume, stack, wall-formed,
     wall-vanished, absorption-confirmed, spoof-suspected.
   - Watchdog WS con timer de conexión separado.
   - fetch con AbortSignal.timeout.
   ============================================================================ */

(function(){
"use strict";

/* ============================================================================
   1. CONFIGURACIÓN
   ============================================================================ */
const CONFIG = {
  SYMBOL:                "BTCUSDT",
  WINDOW_MIN:            40,
  WINDOW_OPTIONS:        [3, 15, 40],
  ROWS:                  25,
  BUCKETS:               [5, 10, 20, 50, 70, 100],
  MIN_USD_OPTIONS:       [5000, 10000, 25000, 50000, 100000, 250000],
  THRESHOLD:             300,
  MIN_SIDE_USD:          25000,
  STACKED_N:             3,
  WEAK_BASE_USD:         5000,
  ABSORPTION_WINDOW_MS:  4000,
  ABSORPTION_MIN_VOL_FACTOR: 0.25,
  DYNAMIC_MIN_FACTOR:    0.12,
  WALL_MULTIPLIER:       2.1,
  RECENT_POC_MS:         90 * 1000,
  REFRESH_LIVE:          350,
  PAGE_LIMIT:            1000,
  PAD_MS:                5 * 60 * 1000,
  STEP_SMALL_S:          15,
  STEP_BIG_S:            60,
  PLAY_STEP_S:           5,
  SPEEDS:                [0.5, 1, 2, 4, 8],
  LISTING_MS:            Date.UTC(2017, 7, 17),
  WS_BASES:              ["wss://stream.binance.com:9443", "wss://data-stream.binance.vision"],
  REST_BASES:            ["https://api.binance.com", "https://data-api.binance.vision", "https://api-gcp.binance.com"],
  MAX_STORE_TRADES:      450000,
  VIBRATE_MS:            120,

  // --- Señales ---
  SIGNAL_TP_WALL_USD:    1000000,
  SIGNAL_SL_EXTRA_TICKS: 2,
  SIGNAL_MAX_AGE_MS:     30000,
  SIGNAL_TRAIL_STEP:     1,
  SIGNAL_MIN_RR:         1.2,

  // --- Percentiles adaptativos ---
  PCT_VOL:               70,
  PCT_IMB:               80,
  PCT_WALL_AGE:          75,

  // --- Absorción sostenida ---
  ABS_SUSTAINED_MIN_MS:  180000,   // 3 minutos
  ABS_SUSTAINED_MIN_PEN: 1,        // 1 tick de penetración máxima
  ABS_SUSTAINED_MIN_RATIO: 3.0,    // ratio contra/pasivo mínimo

  // --- Tracking de muros ---
  WALL_TRACKER_MAX_HISTORY: 12,    // últimos 12 snapshots por nivel
  WALL_TRACKER_STALE_MS:    600000,// 10 minutos sin updates → olvidar
  WALL_VANISH_RATIO:        0.2,   // volNow/peak < 0.2 → vanished
  WALL_GROWING_DELTA:       0.15,  // +15% en últimos 60s → growing
  WALL_SHRINKING_DELTA:     0.5,   // -50% en últimos 60s → shrinking

  // --- Spoofing ---
  SPOOF_WINDOW_MS:          90000, // 90s para considerar "reciente"
  SPOOF_MIN_PEAK_USD:       500000,// muro debe haber sido significativo

  // --- Healthcheck ---
  FETCH_TIMEOUT_MS:         15000,
  WS_CONNECT_TIMEOUT_MS:    10000
};

/* ============================================================================
   2. ESTADO GLOBAL
   ============================================================================ */
const state = {
  mode:         "live",
  windowMin:    CONFIG.WINDOW_MIN,
  bucket:       20,
  imbMode:      "diagonal",          // diagonal | nivel | media | percentil | compuesto

  threshold:          CONFIG.THRESHOLD,
  thresholdMode:      "manual",      // manual | auto
  minUSD:             CONFIG.MIN_SIDE_USD,
  minMode:            "manual",      // manual | auto
  minRelativeToImb:   false,

  paused:       false,
  heatmap:      true,
  bars:         true,
  thermo:       true,
  lines:        true,
  walls:        true,
  sound:        false,
  theme:        "dark",
  signalLocked: false,

  activeSignalLive: null,
  activeSignalHist: null,
  lockedSignalLive: null,
  lockedSignalHist: null,

  histCursor:   Date.now(),
  histFrozen:   true,
  histPlaying:  false,
  histSpeed:    2,
  histLastTick: 0
};

const store = new Map();
let sortedCache = null;
let sortedTimes = null;

const coverage = { intervals: [] };

let restBaseIdx = 0;
let restNote = "";

/* Trackers persistentes (limpiados en clearActiveSignals) */
const wallTracker = new Map();       // idx -> { firstSeen, lastSeen, peakVol, history: [{t, vol, side}], side }
const absorptionTracker = new Map(); // idx -> { touchedAt, maxPen, flowAgainst, flowWith, side }

/* ============================================================================
   3. HELPERS
   ============================================================================ */
function nowMs(){ return Date.now(); }
function pad2(n){ return String(n).padStart(2, "0"); }
function msToLocal(ms){
  const d = new Date(ms);
  return `${d.getFullYear()}-${pad2(d.getMonth()+1)}-${pad2(d.getDate())} ${pad2(d.getHours())}:${pad2(d.getMinutes())}:${pad2(d.getSeconds())}`;
}

/* Percentil de un array numérico */
function percentile(arr, p){
  if (!arr.length) return 0;
  const sorted = arr.slice().sort((a, b) => a - b);
  const idx = (sorted.length - 1) * (p / 100);
  const lo = Math.floor(idx);
  const hi = Math.ceil(idx);
  if (lo === hi) return sorted[lo];
  const w = idx - lo;
  return sorted[lo] * (1 - w) + sorted[hi] * w;
}

/* ============================================================================
   4. TRADE STORE
   ============================================================================ */
function storeAdd(trade){
  if (store.has(trade.a)) return false;
  store.set(trade.a, trade);
  sortedCache = null;
  sortedTimes = null;
  return true;
}

function storeAddMany(trades){
  let changed = false;
  for (const t of trades){
    if (storeAdd(t)) changed = true;
  }
  return changed;
}

function storePrune(cutoffMs){
  let changed = false;
  for (const [id, t] of store){
    if (t.T < cutoffMs){
      store.delete(id);
      changed = true;
    }
  }
  if (changed){
    sortedCache = null;
    sortedTimes = null;
  }
  if (store.size > CONFIG.MAX_STORE_TRADES){
    storeEnsureSorted();
    const dropCount = store.size - CONFIG.MAX_STORE_TRADES;
    for (let i = 0; i < dropCount; i++){
      store.delete(sortedCache[i].a);
    }
    sortedCache = null;
    sortedTimes = null;
  }
}

function storeEnsureSorted(){
  if (sortedCache) return;
  const arr = Array.from(store.values());
  arr.sort((a, b) => a.T !== b.T ? a.T - b.T : a.a - b.a);
  sortedCache = arr;
  sortedTimes = arr.map(t => t.T);
}

function storeWindow(startMs, endMs){
  storeEnsureSorted();
  const times = sortedTimes;
  if (!times.length) return [];

  let lo = 0, hi = times.length;
  while (lo < hi){
    const m = (lo + hi) >> 1;
    if (times[m] < startMs) lo = m + 1;
    else hi = m;
  }
  const i0 = lo;

  lo = i0; hi = times.length;
  while (lo < hi){
    const m = (lo + hi) >> 1;
    if (times[m] <= endMs) lo = m + 1;
    else hi = m;
  }
  return sortedCache.slice(i0, lo);
}

/* ============================================================================
   5. COBERTURA
   ============================================================================ */
function coverageAdd(s, e){
  coverage.intervals.push([s, e]);
  coverage.intervals.sort((a, b) => a[0] - b[0]);
  const out = [];
  for (const [s2, e2] of coverage.intervals){
    if (out.length && s2 <= out[out.length - 1][1] + 1){
      out[out.length - 1][1] = Math.max(out[out.length - 1][1], e2);
    } else {
      out.push([s2, e2]);
    }
  }
  coverage.intervals = out;
}

function coverageMissing(s, e){
  const gaps = [];
  let cur = s;
  for (const [s2, e2] of coverage.intervals){
    if (e2 < cur) continue;
    if (s2 > cur) gaps.push([cur, Math.min(s2 - 1, e)]);
    cur = Math.max(cur, e2 + 1);
    if (cur > e) break;
  }
  if (cur <= e) gaps.push([cur, e]);
  return gaps.filter(([a, b]) => a <= b);
}

function coverageRatio(startMs, endMs){
  const total = endMs - startMs;
  if (total <= 0) return 1;
  const gaps = coverageMissing(startMs, endMs);
  const missing = gaps.reduce((acc, [a, b]) => acc + (b - a), 0);
  return 1 - missing / total;
}

/* ============================================================================
   6. AGREGACIÓN, UMBRALES, IMBALANCE
   ============================================================================ */
function aggregate(trades, bucket){
  const buy = new Map(), sell = new Map();
  let tb = 0, ts = 0;
  for (const t of trades){
    const idx = Math.floor(t.p / bucket);
    const v = t.p * t.q;
    if (t.m){
      sell.set(idx, (sell.get(idx) || 0) + v);
      ts += v;
    } else {
      buy.set(idx, (buy.get(idx) || 0) + v);
      tb += v;
    }
  }
  return { buy, sell, tb, ts };
}

/**
 * Estadísticas visibles + percentiles para umbrales adaptativos.
 */
function computeVisibleStats(buy, sell, lo, hi, imbRatios){
  let sumVol = 0;
  let activeSides = 0;
  let maxVol = 1;
  const sideVols = [];

  for (let i = lo; i <= hi; i++){
    const b = buy.get(i) || 0;
    const s = sell.get(i) || 0;
    if (b > 0){ sumVol += b; activeSides++; if (b > maxVol) maxVol = b; sideVols.push(b); }
    if (s > 0){ sumVol += s; activeSides++; if (s > maxVol) maxVol = s; sideVols.push(s); }
  }

  const avgSideVol = activeSides > 0 ? sumVol / activeSides : 0;
  const effectiveMinUSD = Math.max(state.minUSD, avgSideVol * CONFIG.DYNAMIC_MIN_FACTOR);
  const effectiveWeakBase = Math.max(CONFIG.WEAK_BASE_USD, avgSideVol * 0.04);

  // Percentiles para auto
  const p70vol = percentile(sideVols, CONFIG.PCT_VOL);
  const p80imb = imbRatios && imbRatios.length ? percentile(imbRatios, CONFIG.PCT_IMB) : state.threshold;

  return {
    maxVol, avgSideVol,
    effectiveMinUSD,
    effectiveWeakBase,
    p70vol,
    p80imb
  };
}

/**
 * Calcula umbrales efectivos del snapshot según el modo del usuario.
 * p80imb y p70vol vienen de computeVisibleStats.
 */
function computeUmbrales(stats){
  let threshold = state.threshold;
  if (state.thresholdMode === "auto"){
    threshold = Math.max(100, Math.min(5000, stats.p80imb || state.threshold));
  }

  let minUSD = state.minUSD;
  if (state.minMode === "auto"){
    minUSD = Math.max(0, stats.p70vol || state.minUSD);
  }

  return {
    threshold,
    minUSD,
    weakBase: stats.effectiveWeakBase,
    minRelativeToImb: state.minRelativeToImb
  };
}

function sideImb(num, den, umbrales){
  if (num <= 0 || num <= den) return ["", false, false];
  const { threshold, minUSD, weakBase, minRelativeToImb } = umbrales;
  if (den <= 0){
    const isStrong = num >= minUSD;
    return [isStrong ? "∞" : "∞·", isStrong, !isStrong];
  }
  const weak = den < weakBase;
  const pct = (num / den) * 100;

  // Monto requerido: si minRelativeToImb, escala con el ratio de imbalance
  let requiredMin = minUSD;
  if (minRelativeToImb){
    requiredMin = minUSD * (1 + pct / 300);
  }

  const alert = pct >= threshold && num >= requiredMin && !weak;
  const label = weak ? "∞·" : Math.min(pct, 99999).toFixed(0) + "%";
  return [label, alert, weak];
}

function stackedSet(alerts, lo, hi, n){
  const out = new Set();
  let run = [];
  for (let i = lo; i <= hi; i++){
    if (alerts.get(i)) run.push(i);
    else {
      if (run.length >= n) run.forEach(x => out.add(x));
      run = [];
    }
  }
  if (run.length >= n) run.forEach(x => out.add(x));
  return out;
}

/**
 * Para cada nivel, calcula el imbalance según el modo activo y devuelve
 * las etiquetas y alertas. Además devuelve el percentil bucket (p80/p95/p99)
 * y el array de ratios usados (para calibrar p80imb del siguiente frame).
 */
function computeImbalances(buy, sell, lo, hi, umbrales){
  const imbB = new Map(), imbS = new Map();
  const alB = new Map(), alS = new Map();
  const weakB = new Map(), weakS = new Map();
  const ratioB = new Map(), ratioS = new Map();
  const imbRatios = [];

  for (let idx = lo - 1; idx <= hi + 1; idx++){
    const b = buy.get(idx) || 0;
    const s = sell.get(idx) || 0;
    let denB, denS;

    if (state.imbMode === "diagonal"){
      denB = sell.get(idx - 1) || 0;
      denS = buy.get(idx + 1) || 0;
    } else if (state.imbMode === "nivel"){
      denB = s;
      denS = b;
    } else if (state.imbMode === "media"){
      // "media" se rellena después con el promedio de la ventana
      denB = 0; denS = 0;
    } else if (state.imbMode === "percentil"){
      // "percentil" también se calcula después
      denB = 0; denS = 0;
    } else if (state.imbMode === "compuesto"){
      // Ambos: diagonal AND media
      denB = sell.get(idx - 1) || 0;
      denS = buy.get(idx + 1) || 0;
    }

    if (state.imbMode === "media" || state.imbMode === "compuesto" || state.imbMode === "percentil"){
      // placeholder: se completan luego
    }

    const [lblB, alrB, wk] = sideImb(b, denB, umbrales);
    imbB.set(idx, lblB);
    alB.set(idx, alrB);
    weakB.set(idx, wk);
    if (denB > 0) { ratioB.set(idx, (b / denB) * 100); imbRatios.push((b / denB) * 100); }

    const [lblS, alrS, wkS] = sideImb(s, denS, umbrales);
    imbS.set(idx, lblS);
    alS.set(idx, alrS);
    weakS.set(idx, wkS);
    if (denS > 0) { ratioS.set(idx, (s / denS) * 100); imbRatios.push((s / denS) * 100); }
  }

  // Modo media: comparar cada lado contra el promedio del lado en la ventana
  if (state.imbMode === "media" || state.imbMode === "compuesto"){
    let sumB = 0, sumS = 0, cntB = 0, cntS = 0;
    for (let i = lo; i <= hi; i++){
      const b = buy.get(i) || 0;
      const s = sell.get(i) || 0;
      if (b > 0){ sumB += b; cntB++; }
      if (s > 0){ sumS += s; cntS++; }
    }
    const avgB = cntB > 0 ? sumB / cntB : 0;
    const avgS = cntS > 0 ? sumS / cntS : 0;

    for (let idx = lo; idx <= hi; idx++){
      const b = buy.get(idx) || 0;
      const s = sell.get(idx) || 0;

      if (state.imbMode === "media"){
        const denB = avgS;
        const denS = avgB;
        const [lblB, alrB, wk] = sideImb(b, denB, umbrales);
        imbB.set(idx, lblB); alB.set(idx, alrB); weakB.set(idx, wk);
        if (denB > 0) { ratioB.set(idx, (b / denB) * 100); imbRatios.push((b / denB) * 100); }

        const [lblS, alrS, wkS] = sideImb(s, denS, umbrales);
        imbS.set(idx, lblS); alS.set(idx, alrS); weakS.set(idx, wkS);
        if (denS > 0) { ratioS.set(idx, (s / denS) * 100); imbRatios.push((s / denS) * 100); }
      } else {
        // compuesto: requiere que el imbalance diagonal Y el vs media coincidan
        const denBdiag = sell.get(idx - 1) || 0;
        const denSdiag = buy.get(idx + 1) || 0;
        const [, alrBdiag] = sideImb(b, denBdiag, umbrales);
        const [, alrSdiag] = sideImb(s, denSdiag, umbrales);
        const [, alrBmedia] = sideImb(b, avgS, umbrales);
        const [, alrSmedia] = sideImb(s, avgB, umbrales);

        alB.set(idx, alrBdiag && alrBmedia);
        alS.set(idx, alrSdiag && alrSmedia);
      }
    }
  }

  // Modo percentil: calcular percentil de cada nivel y marcar p80/p95/p99
  if (state.imbMode === "percentil"){
    const allRatiosB = [];
    const allRatiosS = [];
    for (let i = lo; i <= hi; i++){
      const b = buy.get(i) || 0;
      const s = sell.get(i) || 0;
      if (b > 0) allRatiosB.push(b);
      if (s > 0) allRatiosS.push(s);
    }
    const p80B = percentile(allRatiosB, 80);
    const p80S = percentile(allRatiosS, 80);
    for (let idx = lo; idx <= hi; idx++){
      const b = buy.get(idx) || 0;
      const s = sell.get(idx) || 0;
      alB.set(idx, b >= p80B && b > 0);
      alS.set(idx, s >= p80S && s > 0);
    }
  }

  // Bucket de percentil por nivel para colorear
  const imbPctB = new Map();
  const imbPctS = new Map();
  const ratiosB = [];
  const ratiosS = [];
  for (let i = lo; i <= hi; i++){
    const rB = ratioB.get(i);
    const rS = ratioS.get(i);
    if (rB != null) ratiosB.push(rB);
    if (rS != null) ratiosS.push(rS);
  }
  const p95B = percentile(ratiosB, 95);
  const p99B = percentile(ratiosB, 99);
  const p95S = percentile(ratiosS, 95);
  const p99S = percentile(ratiosS, 99);
  for (let i = lo; i <= hi; i++){
    const rB = ratioB.get(i) || 0;
    const rS = ratioS.get(i) || 0;
    if (rB >= p99B && p99B > 0) imbPctB.set(i, "p99");
    else if (rB >= p95B && p95B > 0) imbPctB.set(i, "p95");
    else if (rB >= percentile(ratiosB, 80) && ratiosB.length) imbPctB.set(i, "p80");

    if (rS >= p99S && p99S > 0) imbPctS.set(i, "p99");
    else if (rS >= p95S && p95S > 0) imbPctS.set(i, "p95");
    else if (rS >= percentile(ratiosS, 80) && ratiosS.length) imbPctS.set(i, "p80");
  }

  return { imbB, imbS, alB, alS, weakB, weakS, ratioB, ratioS, imbRatios, imbPctB, imbPctS };
}

/* ============================================================================
   7. WALL TRACKER (tracking temporal de muros)
   ============================================================================ */
function updateWallTracker(buy, sell, lo, hi, cursorMs, wallThreshold){
  if (!state.walls){
    wallTracker.clear();
    return;
  }

  // Limpiar viejos
  for (const [idx, entry] of wallTracker){
    if (cursorMs - entry.lastSeen > CONFIG.WALL_TRACKER_STALE_MS){
      wallTracker.delete(idx);
    }
  }

  for (let idx = lo; idx <= hi; idx++){
    const b = buy.get(idx) || 0;
    const s = sell.get(idx) || 0;

    const isWallBuy = b >= wallThreshold;
    const isWallSell = s >= wallThreshold;

    if (!isWallBuy && !isWallSell){
      // si existía, lo dejamos envejecer (para detectar vanished)
      continue;
    }

    const side = isWallBuy ? "buy" : "sell";
    const vol = isWallBuy ? b : s;

    let entry = wallTracker.get(idx);
    if (!entry){
      entry = {
        firstSeen: cursorMs,
        lastSeen: cursorMs,
        peakVol: vol,
        side,
        history: [{ t: cursorMs, vol }]
      };
      wallTracker.set(idx, entry);
    } else {
      entry.lastSeen = cursorMs;
      if (vol > entry.peakVol) entry.peakVol = vol;
      entry.history.push({ t: cursorMs, vol });
      if (entry.history.length > CONFIG.WALL_TRACKER_MAX_HISTORY){
        entry.history.shift();
      }
    }
  }
}

/**
 * Deriva el estado de cada muro:
 * - stable: vol actual ~ peak (≥80%) y edad ≥ 60s
 * - growing: vol creció ≥15% en últimos 60s
 * - shrinking: vol cayó 50-80% del peak
 * - vanished: vol cayó <20% del peak
 */
function computeWallStates(cursorMs){
  const states = new Map();
  for (const [idx, entry] of wallTracker){
    const hist = entry.history;
    if (!hist.length) continue;
    const last = hist[hist.length - 1];
    const volNow = last.vol;

    let volPrev60 = volNow;
    for (let i = hist.length - 1; i >= 0; i--){
      if (cursorMs - hist[i].t >= 60000){
        volPrev60 = hist[i].vol;
        break;
      }
    }

    let state;
    if (volNow < entry.peakVol * CONFIG.WALL_VANISH_RATIO){
      state = "vanished";
    } else if (volPrev60 > 0 && volNow > volPrev60 * (1 + CONFIG.WALL_GROWING_DELTA)){
      state = "growing";
    } else if (volPrev60 > 0 && volNow < volPrev60 * (1 - CONFIG.WALL_SHRINKING_DELTA)){
      state = "shrinking";
    } else {
      state = "stable";
    }

    states.set(idx, state);
  }
  return states;
}

/* ============================================================================
   8. ABSORPTION TRACKER
   ============================================================================ */
function updateAbsorptionTracker(trades, buy, sell, bucket, cursorMs, lo, hi, avgSideVol){
  if (!trades.length) return;

  // Limpiar viejos
  for (const [idx, entry] of absorptionTracker){
    if (cursorMs - entry.touchedAt > 10 * 60 * 1000){
      absorptionTracker.delete(idx);
    }
  }

  // Recorrer trades de la ventana de absorción
  const cutoff = cursorMs - CONFIG.ABSORPTION_WINDOW_MS;
  const minFlow = Math.max(state.minUSD, avgSideVol * CONFIG.ABSORPTION_MIN_VOL_FACTOR);

  for (let i = trades.length - 1; i >= 0; i--){
    const t = trades[i];
    if (t.T < cutoff) break;
    const idx = Math.floor(t.p / bucket);
    if (idx < lo - 2 || idx > hi + 2) continue;
    const v = t.p * t.q;
    const pen = t.p - idx * bucket;

    let entry = absorptionTracker.get(idx);
    if (!entry){
      entry = {
        touchedAt: t.T,
        maxPen: 0,
        flowAgainst: 0,
        flowWith: 0,
        side: t.m ? "sell" : "buy"
      };
      absorptionTracker.set(idx, entry);
    }

    // Penetración: cuánto bajó (para absB) o subió (para absS) desde el nivel
    const penAbs = Math.abs(pen);
    if (penAbs > entry.maxPen) entry.maxPen = penAbs;

    // Flujo contra/pasivo: venta agresiva contra bid, compra agresiva contra ask
    if (t.m){
      entry.flowAgainst += v;   // venta agresiva
    } else {
      entry.flowWith += v;      // compra agresiva
    }
  }
}

/**
 * Absorción por nivel (no por desplazamiento global).
 * - absorbedB: venta agresiva acumulada, precio no penetró >1 tick
 * - absorbedS: compra agresiva acumulada, precio no penetró >1 tick
 */
function detectAbsorptionByLevel(buy, sell, bucket, cursorMs, lo, hi, avgSideVol){
  const absorbedB = new Map();
  const absorbedS = new Map();
  const minFlow = Math.max(state.minUSD, avgSideVol * CONFIG.ABSORPTION_MIN_VOL_FACTOR);

  for (const [idx, entry] of absorptionTracker){
    if (idx < lo - 1 || idx > hi + 1) continue;

    const b = buy.get(idx) || 0;
    const s = sell.get(idx) || 0;

    // Bid absorbiendo: flujo contra (ventas) >> flujo pasivo (compras), sin penetrar >1 tick
    if (entry.flowAgainst >= minFlow && entry.flowAgainst > entry.flowWith * 1.4 && entry.maxPen <= bucket * 1.0){
      absorbedB.set(idx, true);
    }
    // Ask absorbiendo: flujo con (compras) >> pasivo, sin penetrar >1 tick
    if (entry.flowWith >= minFlow && entry.flowWith > entry.flowAgainst * 1.4 && entry.maxPen <= bucket * 1.0){
      absorbedS.set(idx, true);
    }
  }

  return { absorbedB, absorbedS };
}

/* Absorción sostenida: muro con edad suficiente y penetración mínima */
function computeAbsSustained(absorbedB, absorbedS, cursorMs){
  const set = new Set();
  for (const idx of absorbedB.keys()){
    const entry = absorptionTracker.get(idx);
    const wall = wallTracker.get(idx);
    if (!entry || !wall) continue;
    const age = cursorMs - wall.firstSeen;
    const ratio = entry.flowWith > 0 ? entry.flowAgainst / entry.flowWith : entry.flowAgainst;
    if (age >= CONFIG.ABS_SUSTAINED_MIN_MS &&
        entry.maxPen <= CONFIG.ABS_SUSTAINED_MIN_PEN &&
        ratio >= CONFIG.ABS_SUSTAINED_MIN_RATIO){
      set.add(idx);
    }
  }
  for (const idx of absorbedS.keys()){
    const entry = absorptionTracker.get(idx);
    const wall = wallTracker.get(idx);
    if (!entry || !wall) continue;
    const age = cursorMs - wall.firstSeen;
    const ratio = entry.flowAgainst > 0 ? entry.flowWith / entry.flowAgainst : entry.flowWith;
    if (age >= CONFIG.ABS_SUSTAINED_MIN_MS &&
        entry.maxPen <= CONFIG.ABS_SUSTAINED_MIN_PEN &&
        ratio >= CONFIG.ABS_SUSTAINED_MIN_RATIO){
      set.add(idx);
    }
  }
  return set;
}

/* ============================================================================
   9. ZONE CONTEXT (muro dominante)
   ============================================================================ */
function computeZoneContext(buy, sell, lo, hi, lastPrice, bucket, wallStates, absorbedB, absorbedS, cursorMs, avgSideVol){
  let dominant = null;
  let maxVol = 0;

  for (let idx = lo; idx <= hi; idx++){
    const b = buy.get(idx) || 0;
    const s = sell.get(idx) || 0;
    const wall = wallTracker.get(idx);
    if (!wall) continue;

    const vol = wall.side === "buy" ? b : s;
    if (vol <= maxVol) continue;

    const state = wallStates.get(idx);
    let type = "support";
    if (wall.side === "buy"){
      if (state === "vanished") type = "spoof-bid";
      else if (absorbedB.has(idx)) type = "absorption-bid";
      else type = "support";
    } else {
      if (state === "vanished") type = "spoof-ask";
      else if (absorbedS.has(idx)) type = "absorption-ask";
      else type = "resistance";
    }

    maxVol = vol;
    dominant = {
      idx,
      side: wall.side,
      type,
      vol,
      wallState: state,
      ageMs: cursorMs - wall.firstSeen,
      ratioContra: 0,
      penetrationTicks: 0,
      delta: b - s,
      absorption: absorbedB.has(idx) || absorbedS.has(idx)
    };
  }

  if (!dominant) return { dominantWall: null, vetoActive: false };

  // Rellenar ratio y penetración desde el tracker de absorción
  const abs = absorptionTracker.get(dominant.idx);
  if (abs){
    const isBid = dominant.side === "buy";
    const contra = isBid ? abs.flowAgainst : abs.flowWith;
    const pasivo = isBid ? abs.flowWith : abs.flowAgainst;
    dominant.ratioContra = pasivo > 0 ? contra / pasivo : (contra > 0 ? 999 : 0);
    dominant.penetrationTicks = Math.round(abs.maxPen / bucket);
  }

  return { dominantWall: dominant, vetoActive: false };
}

/* ============================================================================
   10. SEÑALES: MOTORES A/B + ESTRUCTURAL + REGLAS A/B/E/F
   ============================================================================ */

/**
 * Regla E: veto contra muro dominante.
 * Si side=long y hay un wall-sell creciente/estable en el precio → veto.
 * Si side=short y hay un wall-buy creciente/estable en el precio → veto.
 */
function vetoAgainstWall(side, buy, sell, lastIdx, bucket, wallStates, wallThreshold){
  for (const [idx, state] of wallStates){
    if (state === "vanished") continue;
    if (Math.abs(idx - lastIdx) > 1) continue;

    const b = buy.get(idx) || 0;
    const s = sell.get(idx) || 0;

    if (side === "long" && s >= wallThreshold && state !== "vanished"){
      return true;
    }
    if (side === "short" && b >= wallThreshold && state !== "vanished"){
      return true;
    }
  }
  return false;
}

/**
 * Regla F: validación direccional de TP.
 */
function validateTP(side, entry, tp){
  if (side === "long" && tp <= entry) return false;
  if (side === "short" && tp >= entry) return false;
  return true;
}

function findTargetWall(sideMap, startIdx, stepDir, maxSteps, avgSideVol, entryPrice, bucket){
  const wallThreshold = Math.max(CONFIG.SIGNAL_TP_WALL_USD * 0.5, avgSideVol * CONFIG.WALL_MULTIPLIER);
  let bestIdx = null;
  let bestVol = 0;

  for (let step = 2; step <= maxSteps; step++){
    const idx = startIdx + step * stepDir;
    const vol = sideMap.get(idx) || 0;
    if (vol >= wallThreshold && vol > bestVol){
      bestVol = vol;
      bestIdx = idx;
      break;
    }
  }

  if (bestIdx != null) return bestIdx * bucket;

  for (let step = 3; step <= maxSteps; step++){
    const idx = startIdx + step * stepDir;
    const vol = sideMap.get(idx) || 0;
    if (vol > bestVol){
      bestVol = vol;
      bestIdx = idx;
    }
  }

  if (bestIdx != null) return bestIdx * bucket;
  return null;
}

/**
 * Motor A: caza-reversiones (absorción + giro Δ inmediato).
 */
function computeMotorA(buy, sell, absB, absS, trades, cursorMs, bucket, lastIdx, lastPrice, avgSideVol){
  const dInst = instantDelta(trades, cursorMs, 250);
  const pressure = computePressure(trades, bucket, cursorMs);

  for (const idx of absB.keys()){
    if (Math.abs(idx - lastIdx) > 1) continue;
    if (dInst <= 0) continue;
    if (pressure.aggressive < 0.12) continue;
    if (pressure.exhaustion) continue;

    const entryPrice = Math.max(lastPrice, (idx + 1) * bucket);
    const slPrice = (idx - CONFIG.SIGNAL_SL_EXTRA_TICKS) * bucket;
    const tpPrice = findTargetWall(sell, lastIdx, 1, 35, avgSideVol, entryPrice, bucket);
    if (tpPrice == null) continue;

    const risk = Math.abs(entryPrice - slPrice);
    const reward = Math.abs(tpPrice - entryPrice);
    if (risk <= 0 || reward / risk < CONFIG.SIGNAL_MIN_RR) continue;

    return {
      side: "long", entry: entryPrice, sl: slPrice, initialSl: slPrice,
      tp: tpPrice, motor: "A", tick: idx, createdAt: cursorMs, trailMoved: false
    };
  }

  for (const idx of absS.keys()){
    if (Math.abs(idx - lastIdx) > 1) continue;
    if (dInst >= 0) continue;
    if (pressure.aggressive > -0.12) continue;
    if (pressure.exhaustion) continue;

    const entryPrice = Math.min(lastPrice, idx * bucket);
    const slPrice = (idx + 1 + CONFIG.SIGNAL_SL_EXTRA_TICKS) * bucket;
    const tpPrice = findTargetWall(buy, lastIdx, -1, 35, avgSideVol, entryPrice, bucket);
    if (tpPrice == null) continue;

    const risk = Math.abs(slPrice - entryPrice);
    const reward = Math.abs(entryPrice - tpPrice);
    if (risk <= 0 || reward / risk < CONFIG.SIGNAL_MIN_RR) continue;

    return {
      side: "short", entry: entryPrice, sl: slPrice, initialSl: slPrice,
      tp: tpPrice, motor: "A", tick: idx, createdAt: cursorMs, trailMoved: false
    };
  }

  return null;
}

/**
 * Motor B: surfista de tendencia (stacked imbalance cercano + impulso Δ).
 */
function computeMotorB(buy, sell, stB, stS, trades, cursorMs, bucket, lastIdx, lastPrice, avgSideVol){
  const dInst = instantDelta(trades, cursorMs, 250);
  const pressure = computePressure(trades, bucket, cursorMs);

  if (stB.size >= CONFIG.STACKED_N){
    const near = Array.from(stB).filter(idx => Math.abs(idx - lastIdx) <= 4);
    if (near.length >= CONFIG.STACKED_N){
      const topIdx = Math.max(...near);
      const bottomIdx = Math.min(...near);
      const minDeltaSurge = Math.max(35000, avgSideVol * 0.25);

      if (dInst > minDeltaSurge && pressure.aggressive > 0.28){
        const entryPrice = lastPrice;
        const slPrice = (bottomIdx - CONFIG.SIGNAL_SL_EXTRA_TICKS) * bucket;
        const tpPrice = findTargetWall(sell, lastIdx, 1, 40, avgSideVol, entryPrice, bucket);
        if (tpPrice == null) return null;

        const risk = Math.abs(entryPrice - slPrice);
        const reward = Math.abs(tpPrice - entryPrice);
        if (validateTP("long", entryPrice, tpPrice) && risk > 0 && reward / risk >= CONFIG.SIGNAL_MIN_RR){
          return {
            side: "long", entry: entryPrice, sl: slPrice, initialSl: slPrice,
            tp: tpPrice, motor: "B", tick: topIdx, createdAt: cursorMs, trailMoved: false
          };
        }
      }
    }
  }

  if (stS.size >= CONFIG.STACKED_N){
    const near = Array.from(stS).filter(idx => Math.abs(idx - lastIdx) <= 4);
    if (near.length >= CONFIG.STACKED_N){
      const bottomIdx = Math.min(...near);
      const topIdx = Math.max(...near);
      const minDeltaSurge = Math.max(35000, avgSideVol * 0.25);

      if (dInst < -minDeltaSurge && pressure.aggressive < -0.28){
        const entryPrice = lastPrice;
        const slPrice = (topIdx + 1 + CONFIG.SIGNAL_SL_EXTRA_TICKS) * bucket;
        const tpPrice = findTargetWall(buy, lastIdx, -1, 40, avgSideVol, entryPrice, bucket);
        if (tpPrice == null) return null;

        const risk = Math.abs(slPrice - entryPrice);
        const reward = Math.abs(entryPrice - tpPrice);
        if (validateTP("short", entryPrice, tpPrice) && risk > 0 && reward / risk >= CONFIG.SIGNAL_MIN_RR){
          return {
            side: "short", entry: entryPrice, sl: slPrice, initialSl: slPrice,
            tp: tpPrice, motor: "B", tick: bottomIdx, createdAt: cursorMs, trailMoved: false
          };
        }
      }
    }
  }

  return null;
}

/**
 * Regla A: absorción sostenida → long en bid absorbente, short en ask absorbente.
 */
function computeRuleA(absSustained, buy, sell, bucket, cursorMs, lo, hi, wallStates, avgSideVol, lastIdx, lastPrice){
  for (const idx of absSustained){
    const wall = wallTracker.get(idx);
    if (!wall) continue;
    const state = wallStates.get(idx);
    if (state === "vanished") continue;

    if (wall.side === "buy"){
      const entryPrice = Math.max(lastPrice, (idx + 1) * bucket);
      const slPrice = (idx - CONFIG.SIGNAL_SL_EXTRA_TICKS) * bucket;
      const tpPrice = findTargetWall(sell, lastIdx, 1, 40, avgSideVol, entryPrice, bucket);
      if (tpPrice == null) continue;
      const risk = Math.abs(entryPrice - slPrice);
      const reward = Math.abs(tpPrice - entryPrice);
      if (risk <= 0 || reward / risk < CONFIG.SIGNAL_MIN_RR) continue;
      if (!validateTP("long", entryPrice, tpPrice)) continue;

      return {
        side: "long", entry: entryPrice, sl: slPrice, initialSl: slPrice,
        tp: tpPrice, motor: "ABS", tick: idx, createdAt: cursorMs, trailMoved: false
      };
    }

    if (wall.side === "sell"){
      const entryPrice = Math.min(lastPrice, idx * bucket);
      const slPrice = (idx + 1 + CONFIG.SIGNAL_SL_EXTRA_TICKS) * bucket;
      const tpPrice = findTargetWall(buy, lastIdx, -1, 40, avgSideVol, entryPrice, bucket);
      if (tpPrice == null) continue;
      const risk = Math.abs(slPrice - entryPrice);
      const reward = Math.abs(entryPrice - tpPrice);
      if (risk <= 0 || reward / risk < CONFIG.SIGNAL_MIN_RR) continue;
      if (!validateTP("short", entryPrice, tpPrice)) continue;

      return {
        side: "short", entry: entryPrice, sl: slPrice, initialSl: slPrice,
        tp: tpPrice, motor: "ABS", tick: idx, createdAt: cursorMs, trailMoved: false
      };
    }
  }
  return null;
}

/**
 * Regla B: ruptura de muro retirado → long si cruzó wall-sell al alza, short si cruzó wall-buy a la baja.
 */
function computeRuleB(buy, sell, bucket, cursorMs, wallStates, lastIdx, lastPrice, avgSideVol){
  for (const [idx, wall] of wallTracker){
    const state = wallStates.get(idx);
    if (state !== "vanished") continue;
    if (cursorMs - wall.lastSeen > CONFIG.SPOOF_WINDOW_MS) continue;
    if (wall.peakVol < CONFIG.SPOOF_MIN_PEAK_USD) continue;

    const levelPrice = idx * bucket;
    if (wall.side === "sell" && lastPrice > levelPrice && Math.abs(lastIdx - idx) <= 2){
      const entryPrice = lastPrice;
      const slPrice = (idx - CONFIG.SIGNAL_SL_EXTRA_TICKS) * bucket;
      const tpPrice = findTargetWall(sell, lastIdx, 1, 40, avgSideVol, entryPrice, bucket);
      if (tpPrice == null) continue;
      const risk = Math.abs(entryPrice - slPrice);
      const reward = Math.abs(tpPrice - entryPrice);
      if (risk <= 0 || reward / risk < CONFIG.SIGNAL_MIN_RR) continue;
      if (!validateTP("long", entryPrice, tpPrice)) continue;

      return {
        side: "long", entry: entryPrice, sl: slPrice, initialSl: slPrice,
        tp: tpPrice, motor: "SPOOF", tick: idx, createdAt: cursorMs, trailMoved: false
      };
    }

    if (wall.side === "buy" && lastPrice < levelPrice && Math.abs(lastIdx - idx) <= 2){
      const entryPrice = lastPrice;
      const slPrice = (idx + 1 + CONFIG.SIGNAL_SL_EXTRA_TICKS) * bucket;
      const tpPrice = findTargetWall(buy, lastIdx, -1, 40, avgSideVol, entryPrice, bucket);
      if (tpPrice == null) continue;
      const risk = Math.abs(slPrice - entryPrice);
      const reward = Math.abs(entryPrice - tpPrice);
      if (risk <= 0 || reward / risk < CONFIG.SIGNAL_MIN_RR) continue;
      if (!validateTP("short", entryPrice, tpPrice)) continue;

      return {
        side: "short", entry: entryPrice, sl: slPrice, initialSl: slPrice,
        tp: tpPrice, motor: "SPOOF", tick: idx, createdAt: cursorMs, trailMoved: false
      };
    }
  }
  return null;
}

/**
 * Señal estructural (fallback): POC / absorción / stacked cercano.
 * SIEMPRE valida dirección de TP (regla F) y veta contra muro dominante (regla E).
 */
function computeStructuralSignal(buy, sell, stB, stS, absB, absS, wallStates, wallThreshold, lastPrice, bucket, avgSideVol, cursorMs){
  const lastIdx = Math.floor(lastPrice / bucket);
  let bestAnchor = null;
  let bestVol = 0;

  for (const idx of absB.keys()){
    if (Math.abs(idx - lastIdx) <= 6){
      const b = buy.get(idx) || 0;
      if (b > bestVol){ bestVol = b; bestAnchor = { idx, side: "long" }; }
    }
  }
  for (const idx of absS.keys()){
    if (Math.abs(idx - lastIdx) <= 6){
      const s = sell.get(idx) || 0;
      if (s > bestVol){ bestVol = s; bestAnchor = { idx, side: "short" }; }
    }
  }

  if (!bestAnchor && stB.size > 0){
    const nearB = Array.from(stB).filter(idx => Math.abs(idx - lastIdx) <= 6);
    if (nearB.length) bestAnchor = { idx: Math.max(...nearB), side: "long" };
  }
  if (!bestAnchor && stS.size > 0){
    const nearS = Array.from(stS).filter(idx => Math.abs(idx - lastIdx) <= 6);
    if (nearS.length) bestAnchor = { idx: Math.min(...nearS), side: "short" };
  }

  if (!bestAnchor){
    let pocIdx = null, pocVol = 0;
    for (let i = lastIdx - 12; i <= lastIdx + 12; i++){
      const v = (buy.get(i) || 0) + (sell.get(i) || 0);
      if (v > pocVol){ pocVol = v; pocIdx = i; }
    }
    if (pocIdx == null) return null;
    bestAnchor = { idx: pocIdx, side: pocIdx <= lastIdx ? "long" : "short" };
  }

  const { idx, side } = bestAnchor;
  const entry = lastPrice;
  let sl, tp;

  if (side === "long"){
    sl = Math.min(idx - CONFIG.SIGNAL_SL_EXTRA_TICKS, lastIdx - 2) * bucket;
    tp = findTargetWall(sell, lastIdx, 1, 30, avgSideVol, entry, bucket);
  } else {
    sl = Math.max(idx + CONFIG.SIGNAL_SL_EXTRA_TICKS, lastIdx + 2) * bucket;
    tp = findTargetWall(buy, lastIdx, -1, 30, avgSideVol, entry, bucket);
  }

  if (tp == null) return null;
  if (!validateTP(side, entry, tp)) return null;
  if (vetoAgainstWall(side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)) return null;

  return {
    side, entry, sl, initialSl: sl, tp,
    motor: "S", tick: idx, createdAt: cursorMs, trailMoved: false
  };
}

/**
 * Aplica trailing stop progresivo.
 */
function trailSignal(signal, lastPrice, bucket){
  if (!signal) return signal;
  const move = signal.side === "long"
    ? (lastPrice - signal.entry) / bucket
    : (signal.entry - lastPrice) / bucket;

  if (move >= CONFIG.SIGNAL_TRAIL_STEP * 3){
    if (signal.side === "long" && signal.sl < signal.entry){
      signal.sl = signal.entry; signal.trailMoved = true;
    } else if (signal.side === "short" && signal.sl > signal.entry){
      signal.sl = signal.entry; signal.trailMoved = true;
    }
  }

  if (move >= CONFIG.SIGNAL_TRAIL_STEP * 6){
    if (signal.side === "long"){
      const newSl = signal.entry + 3 * bucket;
      if (newSl > signal.sl && newSl < signal.tp){ signal.sl = newSl; signal.trailMoved = true; }
    } else {
      const newSl = signal.entry - 3 * bucket;
      if (newSl < signal.sl && newSl > signal.tp){ signal.sl = newSl; signal.trailMoved = true; }
    }
  }

  if (move >= CONFIG.SIGNAL_TRAIL_STEP * 10){
    if (signal.side === "long"){
      const dynamicSl = (Math.floor(lastPrice / bucket) - 4) * bucket;
      if (dynamicSl > signal.sl && dynamicSl < signal.tp){ signal.sl = dynamicSl; signal.trailMoved = true; }
    } else {
      const dynamicSl = (Math.ceil(lastPrice / bucket) + 4) * bucket;
      if (dynamicSl < signal.sl && dynamicSl > signal.tp){ signal.sl = dynamicSl; signal.trailMoved = true; }
    }
  }

  return signal;
}

/**
 * Resuelve el ciclo de vida de la señal:
 * - live: muta activeSignalLive con trailing
 * - hist: determinista, no muta entre llamadas
 */
function resolveSignalLifecycle(isLive, buy, sell, stB, stS, absB, absS, absSustained, wallStates, wallThreshold, trades, cursorMs, bucket, avgSideVol){
  if (!state.lines){
    if (isLive) state.activeSignalLive = null;
    else state.activeSignalHist = null;
    return null;
  }

  const lastPrice = trades[trades.length - 1].p;
  const lastIdx = Math.floor(lastPrice / bucket);

  // 1. Live + señal bloqueada: devolver la bloqueada con trailing
  if (isLive && state.signalLocked && state.lockedSignalLive){
    trailSignal(state.lockedSignalLive, lastPrice, bucket);
    return state.lockedSignalLive;
  }

  // 2. Hist: si está bloqueada, devolver la bloqueada sin mutar
  if (!isLive && state.signalLocked && state.lockedSignalHist){
    return state.lockedSignalHist;
  }

  // 3. Live: señal activa vigente → validar SL/TP/expiración
  let current = isLive ? state.activeSignalLive : null;
  if (current && isLive && (current.motor === "A" || current.motor === "B" || current.motor === "ABS" || current.motor === "SPOOF")){
    const age = Math.abs(cursorMs - current.createdAt);
    const hitSL = current.side === "long" ? lastPrice <= current.sl : lastPrice >= current.sl;
    const hitTP = current.side === "long" ? lastPrice >= current.tp : lastPrice <= current.tp;
    const expired = age > CONFIG.SIGNAL_MAX_AGE_MS && !current.trailMoved;

    if (hitSL || hitTP || expired){
      current = null;
      state.activeSignalLive = null;
    } else {
      trailSignal(current, lastPrice, bucket);
      return current;
    }
  }

  // 4. Regla E: veto contra muro dominante
  //    (se evalúa antes de emitir cualquier señal nueva)
  //    Se aplica dentro de las funciones de cada regla.

  // 5. Hist: recalcular siempre desde cero (determinista, sin mutar entre llamadas)
  //    Usa una copia del estado de señal histórica para evitar acumulación
  if (!isLive){
    const fresh = computeFreshSignal(buy, sell, stB, stS, absB, absS, absSustained, wallStates, wallThreshold, trades, cursorMs, bucket, avgSideVol);
    return fresh;
  }

  // 6. Live: emitir nueva señal (prioridad A > B > ABS > SPOOF > Estructural)
  const absSig = computeRuleA(absSustained, buy, sell, bucket, cursorMs, -Infinity, Infinity, wallStates, avgSideVol, lastIdx, lastPrice);
  if (absSig && !vetoAgainstWall(absSig.side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)){
    state.activeSignalLive = absSig;
    return absSig;
  }

  const spoofSig = computeRuleB(buy, sell, bucket, cursorMs, wallStates, lastIdx, lastPrice, avgSideVol);
  if (spoofSig && !vetoAgainstWall(spoofSig.side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)){
    state.activeSignalLive = spoofSig;
    return spoofSig;
  }

  const motorA = computeMotorA(buy, sell, absB, absS, trades, cursorMs, bucket, lastIdx, lastPrice, avgSideVol);
  if (motorA && !vetoAgainstWall(motorA.side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)){
    state.activeSignalLive = motorA;
    return motorA;
  }

  const motorB = computeMotorB(buy, sell, stB, stS, trades, cursorMs, bucket, lastIdx, lastPrice, avgSideVol);
  if (motorB && !vetoAgainstWall(motorB.side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)){
    state.activeSignalLive = motorB;
    return motorB;
  }

  const structural = computeStructuralSignal(buy, sell, stB, stS, absB, absS, wallStates, wallThreshold, lastPrice, bucket, avgSideVol, cursorMs);
  state.activeSignalLive = structural;
  return structural;
}

/**
 * Cálculo determinista de la señal en un instante dado (para histórico).
 * No muta estado. Cada snapshot produce el mismo resultado para el mismo cursorMs.
 */
function computeFreshSignal(buy, sell, stB, stS, absB, absS, absSustained, wallStates, wallThreshold, trades, cursorMs, bucket, avgSideVol){
  if (!trades.length) return null;
  const lastPrice = trades[trades.length - 1].p;
  const lastIdx = Math.floor(lastPrice / bucket);

  // Regla A: absorción sostenida
  const a = computeRuleA(absSustained, buy, sell, bucket, cursorMs, -Infinity, Infinity, wallStates, avgSideVol, lastIdx, lastPrice);
  if (a && !vetoAgainstWall(a.side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)){
    trailSignal(a, lastPrice, bucket);
    return a;
  }

  // Regla B: ruptura de muro retirado
  const b = computeRuleB(buy, sell, bucket, cursorMs, wallStates, lastIdx, lastPrice, avgSideVol);
  if (b && !vetoAgainstWall(b.side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)){
    trailSignal(b, lastPrice, bucket);
    return b;
  }

  // Motor A
  const aM = computeMotorA(buy, sell, absB, absS, trades, cursorMs, bucket, lastIdx, lastPrice, avgSideVol);
  if (aM && !vetoAgainstWall(aM.side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)){
    trailSignal(aM, lastPrice, bucket);
    return aM;
  }

  // Motor B
  const bM = computeMotorB(buy, sell, stB, stS, trades, cursorMs, bucket, lastIdx, lastPrice, avgSideVol);
  if (bM && !vetoAgainstWall(bM.side, buy, sell, lastIdx, bucket, wallStates, wallThreshold)){
    trailSignal(bM, lastPrice, bucket);
    return bM;
  }

  // Estructural
  const s = computeStructuralSignal(buy, sell, stB, stS, absB, absS, wallStates, wallThreshold, lastPrice, bucket, avgSideVol, cursorMs);
  if (s){
    trailSignal(s, lastPrice, bucket);
    return s;
  }

  return null;
}

/* ============================================================================
   11. DELTA Y PRESIÓN
   ============================================================================ */
function instantDelta(trades, cursorMs, windowMs){
  if (windowMs == null) windowMs = 1000;
  let d = 0;
  const cutoff = cursorMs - windowMs;
  for (let i = trades.length - 1; i >= 0; i--){
    const t = trades[i];
    if (t.T < cutoff) break;
    const v = t.p * t.q;
    d += t.m ? -v : v;
  }
  return d;
}

function computePressure(trades, bucket, cursorMs){
  if (!trades.length) return { aggressive: 0, displacement: 0, exhaustion: false };
  const lastPrice = trades[trades.length - 1].p;

  const cutoffAgg = cursorMs - 3000;
  let aggDelta = 0, aggTotal = 0;
  for (let i = trades.length - 1; i >= 0; i--){
    const t = trades[i];
    if (t.T < cutoffAgg) break;
    const v = t.p * t.q;
    aggTotal += v;
    aggDelta += t.m ? -v : v;
  }
  const aggressive = aggTotal > 0 ? Math.max(-1, Math.min(1, aggDelta / aggTotal)) : 0;

  const cutoffDisp = cursorMs - 10000;
  let price10 = lastPrice;
  for (let i = trades.length - 1; i >= 0; i--){
    if (trades[i].T < cutoffDisp) break;
    price10 = trades[i].p;
  }
  const rawMove = (lastPrice - price10) / bucket;
  const displacement = Math.max(-1, Math.min(1, rawMove / 5));

  const exhaustion = Math.abs(aggressive) > 0.32 && Math.abs(displacement) < 0.12;

  return { aggressive, displacement, exhaustion };
}

function computePOCs(buy, sell){
  let pocVolIdx = null, pocVolVal = -1;
  let pocDeltaIdx = null, pocDeltaVal = -1;
  const allIdx = new Set([...buy.keys(), ...sell.keys()]);
  for (const idx of allIdx){
    const b = buy.get(idx) || 0;
    const s = sell.get(idx) || 0;
    const totalVol = b + s;
    if (totalVol > pocVolVal){ pocVolVal = totalVol; pocVolIdx = idx; }
    const absDelta = Math.abs(b - s);
    if (absDelta > pocDeltaVal){ pocDeltaVal = absDelta; pocDeltaIdx = idx; }
  }
  return { pocVolIdx, pocDeltaIdx };
}

/* ============================================================================
   12. REST API
   ============================================================================ */
async function restFetch(params, signal){
  const maxAttempts = 6;
  for (let attempt = 0; attempt < maxAttempts; attempt++){
    if (signal && signal.aborted) throw new DOMException("aborted", "AbortError");
    try {
      const base = CONFIG.REST_BASES[restBaseIdx % CONFIG.REST_BASES.length];
      const qs = new URLSearchParams(params).toString();
      const timeoutSignal = AbortSignal.timeout(CONFIG.FETCH_TIMEOUT_MS);
      const combined = signal
        ? AbortSignal.any([signal, timeoutSignal])
        : timeoutSignal;
      const res = await fetch(`${base}/api/v3/aggTrades?${qs}`, { signal: combined });
      if (res.status === 200){
        restNote = "";
        return await res.json();
      }
      if (res.status === 429 || res.status === 418){
        const ra = parseInt(res.headers.get("Retry-After") || "5", 10);
        restNote = `rate-limit ${ra}s`;
        await new Promise(r => setTimeout(r, ra * 1000 + 500));
        continue;
      }
      if (res.status === 451 || res.status >= 500){
        restBaseIdx++;
        restNote = "rotando endpoint";
        await new Promise(r => setTimeout(r, 800 * (attempt + 1)));
        continue;
      }
      throw new Error("HTTP " + res.status);
    } catch (ex){
      if (ex.name === "AbortError") throw ex;
      restNote = "red: " + ex.message;
      await new Promise(r => setTimeout(r, 800 * (attempt + 1)));
      if (attempt >= 2) restBaseIdx++;
    }
  }
  throw new Error("reintentos agotados");
}

async function restLoadRange(startMs, endMs, onProgress, signal){
  const out = [];
  let page = await restFetch({
    symbol: CONFIG.SYMBOL,
    startTime: startMs,
    endTime: endMs,
    limit: CONFIG.PAGE_LIMIT
  }, signal);

  while (page && page.length){
    for (const d of page){
      if (d.T > endMs) break;
      out.push({ T: d.T, a: d.a, p: +d.p, q: +d.q, m: !!d.m });
    }
    if (onProgress){
      const frac = (page[page.length - 1].T - startMs) / Math.max(1, endMs - startMs);
      onProgress(Math.min(1, Math.max(0, frac)), out.length);
    }
    if (page.length < CONFIG.PAGE_LIMIT || page[page.length - 1].T >= endMs) break;
    page = await restFetch({
      symbol: CONFIG.SYMBOL,
      fromId: page[page.length - 1].a + 1,
      limit: CONFIG.PAGE_LIMIT
    }, signal);
  }
  return out;
}

/* ============================================================================
   13. WEBSOCKET LIVE FEED (watchdog corregido)
   ============================================================================ */
class LiveFeed {
  constructor(){
    this.ws = null;
    this.stopped = true;
    this.baseIdx = 0;
    this.backoff = 1;
    this.lastMsg = 0;
    this.lastT = 0;
    this.reconnectTimer = null;
    this.watchdogId = null;
    this.connectTimeoutId = null;
    this.statusText = "desconectado";
  }
  getStatus(){ return this.statusText; }
  url(){
    return CONFIG.WS_BASES[this.baseIdx % CONFIG.WS_BASES.length]
      + "/ws/" + CONFIG.SYMBOL.toLowerCase() + "@aggTrade";
  }
  start(){
    if (!this.stopped) return;
    this.stopped = false;
    this.backoff = 1;
    this.connect();
    if (!this.watchdogId) this.watchdogId = setInterval(() => this.watchdog(), 5000);
  }
  connect(){
    if (this.stopped) return;
    this.gapFill();
    try {
      this.ws = new WebSocket(this.url());
      this.lastMsg = Date.now();
      this.connectTimeoutId = setTimeout(() => {
        if (this.ws && this.ws.readyState !== WebSocket.OPEN){
          this.setStatus("timeout de conexión · reconectando");
          try { this.ws.close(); } catch(_){}
        }
      }, CONFIG.WS_CONNECT_TIMEOUT_MS);
      this.ws.onopen = () => {
        clearTimeout(this.connectTimeoutId);
        this.connectTimeoutId = null;
        this.setStatus("EN VIVO");
        this.lastMsg = Date.now();
        this.backoff = 1;
      };
      this.ws.onmessage = (ev) => {
        try {
          const d = JSON.parse(ev.data);
          if (d.e === "aggTrade"){
            const trade = { T: d.T, a: d.a, p: +d.p, q: +d.q, m: !!d.m };
            storeAdd(trade);
            this.lastMsg = Date.now();
            if (trade.T > this.lastT) this.lastT = trade.T;
            this.setStatus("EN VIVO");
          } else if (d.e === "serverShutdown"){
            this.setStatus("mantenimiento · reconectando");
            try { this.ws.close(); } catch(_){}
          }
        } catch(_){}
      };
      this.ws.onerror = () => this.setStatus("ws error");
      this.ws.onclose = () => {
        clearTimeout(this.connectTimeoutId);
        this.connectTimeoutId = null;
        if (this.stopped) return;
        this.setStatus("desconectado · reconectando…");
        this.scheduleReconnect();
      };
    } catch (ex){
      this.setStatus("ws: " + ex.message);
      this.scheduleReconnect();
    }
  }
  scheduleReconnect(){
    if (this.reconnectTimer) return;
    this.baseIdx++;
    const wait = this.backoff * 1000;
    this.setStatus(`reconectando en ${this.backoff}s…`);
    this.reconnectTimer = setTimeout(() => {
      this.reconnectTimer = null;
      this.backoff = Math.min(this.backoff * 2, 15);
      this.connect();
    }, wait);
  }
  async gapFill(){
    if (!this.lastT) return;
    const now = Date.now();
    if (now - this.lastT < 1500) return;
    this.setStatus("rellenando hueco…");
    try {
      const gap = await restLoadRange(this.lastT + 1, now);
      storeAddMany(gap);
      if (gap.length) this.lastT = Math.max(this.lastT, gap[gap.length - 1].T);
    } catch(_){}
  }
  watchdog(){
    if (this.stopped) return;
    if (!this.lastMsg){
      this.lastMsg = Date.now();
      return;
    }
    if (Date.now() - this.lastMsg > 20000 && this.ws){
      this.setStatus("sin datos >20s · reconectando");
      try { this.ws.close(); } catch(_){}
    }
  }
  setStatus(txt){ this.statusText = txt; }
  stop(){
    this.stopped = true;
    clearTimeout(this.reconnectTimer); this.reconnectTimer = null;
    clearTimeout(this.connectTimeoutId); this.connectTimeoutId = null;
    if (this.watchdogId){ clearInterval(this.watchdogId); this.watchdogId = null; }
    try { if (this.ws) this.ws.close(); } catch(_){}
    this.setStatus("desconectado");
  }
}

const feed = new LiveFeed();

/* ============================================================================
   14. BUILD SNAPSHOT
   ============================================================================ */
function buildSnapshot(trades, cursorMs, isLive){
  if (!trades.length){
    return {
      trades: [], cursorMs, bucket: state.bucket, windowMin: state.windowMin,
      tb: 0, ts: 0, total: 0, delta: 0,
      instantDelta: 0, instantDeltaShort: 0,
      pressure: { aggressive: 0, displacement: 0, exhaustion: false },
      buy: new Map(), sell: new Map(),
      imbB: new Map(), imbS: new Map(),
      alB: new Map(), alS: new Map(),
      absB: new Map(), absS: new Map(),
      weakB: new Map(), weakS: new Map(),
      stB: new Set(), stS: new Set(),
      imbPctB: new Map(), imbPctS: new Map(),
      wallState: new Map(), absSustained: new Set(),
      zoneContext: { dominantWall: null, vetoActive: false },
      maxVol: 1, avgSideVol: 0, lo: 0, hi: 0, center: 0,
      pocVolIdx: null, pocDeltaIdx: null,
      lastPrice: null, maxAcumRef: 100000, maxInstRef: 50000,
      signal: null, events: []
    };
  }

  const { buy, sell, tb, ts } = aggregate(trades, state.bucket);
  const total = tb + ts;
  const delta = tb - ts;
  const lastPrice = trades[trades.length - 1].p;
  const center = Math.floor(lastPrice / state.bucket);
  const half = Math.floor(CONFIG.ROWS / 2);
  const hi = center + half;
  const lo = center - half;

  const { pocVolIdx, pocDeltaIdx } = computePOCs(buy, sell);

  // Umbrales
  const stats0 = computeVisibleStats(buy, sell, lo, hi, []);
  const umbrales = computeUmbrales(stats0);
  const { imbB, imbS, alB, alS, weakB, weakS, imbRatios, imbPctB, imbPctS } = computeImbalances(buy, sell, lo, hi, umbrales);

  // Recalcular stats con los ratios reales para p80imb
  const stats = computeVisibleStats(buy, sell, lo, hi, imbRatios);
  const avgSideVol = stats.avgSideVol;
  const maxVol = stats.maxVol;

  const stB = stackedSet(alB, lo, hi, CONFIG.STACKED_N);
  const stS = stackedSet(alS, lo, hi, CONFIG.STACKED_N);

  // Tracking de muros
  const wallThreshold = Math.max(avgSideVol * CONFIG.WALL_MULTIPLIER, 250000);
  updateWallTracker(buy, sell, lo, hi, cursorMs, wallThreshold);
  const wallStates = computeWallStates(cursorMs);

  // Tracking de absorción
  updateAbsorptionTracker(trades, buy, sell, state.bucket, cursorMs, lo, hi, avgSideVol);
  const { absorbedB, absorbedS } = detectAbsorptionByLevel(buy, sell, state.bucket, cursorMs, lo, hi, avgSideVol);
  const absSustained = computeAbsSustained(absorbedB, absorbedS, cursorMs);

  // Zone context
  const zoneContext = computeZoneContext(buy, sell, lo, hi, lastPrice, state.bucket, wallStates, absorbedB, absorbedS, cursorMs, avgSideVol);

  const dInst = instantDelta(trades, cursorMs, 1000);
  const dInstShort = instantDelta(trades, cursorMs, 250);
  const pressure = computePressure(trades, state.bucket, cursorMs);

  const maxAcumRef = Math.max(Math.abs(delta), Math.max(100000, avgSideVol * 2));
  let maxInstRef = 10000;
  for (let i = trades.length - 1; i >= 0; i--){
    const t = trades[i];
    if (t.T < cursorMs - 10000) break;
    const v = t.p * t.q;
    if (v > maxInstRef) maxInstRef = v;
  }
  maxInstRef *= 1.5;

  // Señal
  const signal = resolveSignalLifecycle(
    isLive, buy, sell, stB, stS, absorbedB, absorbedS, absSustained,
    wallStates, wallThreshold, trades, cursorMs, state.bucket, avgSideVol
  );

  return {
    trades, cursorMs, bucket: state.bucket, windowMin: state.windowMin,
    tb, ts, total, delta,
    instantDelta: dInst, instantDeltaShort: dInstShort, pressure,
    buy, sell, imbB, imbS, alB, alS,
    absB: absorbedB, absS: absorbedS,
    weakB, weakS, stB, stS,
    imbPctB, imbPctS,
    wallState: wallStates,
    absSustained,
    zoneContext,
    wallThreshold,
    maxVol, avgSideVol, lo, hi, center,
    pocVolIdx, pocDeltaIdx, lastPrice,
    maxAcumRef, maxInstRef,
    signal, events: []
  };
}

function getLiveSnapshot(){
  const now = nowMs();
  const maxRetentionMs = Math.max(...CONFIG.WINDOW_OPTIONS) * 60 * 1000;
  storePrune(now - maxRetentionMs - 5000);
  const activeStart = now - state.windowMin * 60 * 1000;
  const trades = storeWindow(activeStart, now);
  return buildSnapshot(trades, now, true);
}

function getHistSnapshot(cursorMs){
  const activeStart = cursorMs - state.windowMin * 60 * 1000;
  const trades = storeWindow(activeStart, cursorMs);

  // IMPORTANTE: para histórico, reseteamos los trackers al inicio de la ventana
  // para que el resultado sea determinista e independiente del orden de visita.
  // Guardamos el estado previo y lo restauramos tras calcular.
  const prevWall = new Map(wallTracker);
  const prevAbs = new Map(absorptionTracker);

  wallTracker.clear();
  absorptionTracker.clear();

  const snap = buildSnapshot(trades, cursorMs, false);
  snap.events = detectEvents(trades, state.bucket, activeStart, cursorMs, snap.avgSideVol);

  // Restaurar trackers live
  wallTracker.clear();
  absorptionTracker.clear();
  for (const [k, v] of prevWall) wallTracker.set(k, v);
  for (const [k, v] of prevAbs) absorptionTracker.set(k, v);

  return snap;
}

/* ============================================================================
   15. DETECCIÓN DE EVENTOS (timeline)
   ============================================================================ */
function detectEvents(trades, bucket, startMs, endMs, avgSideVol){
  const events = [];
  if (!trades.length) return events;

  const step = 5000;
  const volThreshold = Math.max(400000, (avgSideVol || 100000) * 3);
  const minSide = Math.max(state.minUSD, (avgSideVol || 0) * CONFIG.DYNAMIC_MIN_FACTOR);
  const weakBase = Math.max(CONFIG.WEAK_BASE_USD, (avgSideVol || 0) * 0.04);

  const wallThresholdLocal = Math.max((avgSideVol || 0) * CONFIG.WALL_MULTIPLIER, 250000);
  const localWallTracker = new Map();

  let left = 0;
  const n = trades.length;

  for (let t = startMs; t <= endMs; t += step){
    while (left < n && trades[left].T < t) left++;
    let right = left;
    while (right < n && trades[right].T < t + step) right++;

    if (left >= right) continue;

    const buy = new Map(), sell = new Map();
    let total = 0;
    let lo = Infinity, hi = -Infinity;

    for (let i = left; i < right; i++){
      const tr = trades[i];
      const idx = Math.floor(tr.p / bucket);
      const v = tr.p * tr.q;
      total += v;
      if (idx < lo) lo = idx;
      if (idx > hi) hi = idx;
      if (tr.m) sell.set(idx, (sell.get(idx) || 0) + v);
      else      buy.set(idx, (buy.get(idx) || 0) + v);
    }

    if (total > volThreshold){
      events.push({ t: t + step / 2, type: "volume" });
    }

    // WALL-FORMED
    for (let idx = lo; idx <= hi; idx++){
      const b = buy.get(idx) || 0;
      const s = sell.get(idx) || 0;
      const isBuy = b >= wallThresholdLocal;
      const isSell = s >= wallThresholdLocal;
      if (!isBuy && !isSell) continue;

      const side = isBuy ? "buy" : "sell";
      const vol = isBuy ? b : s;
      const prev = localWallTracker.get(idx);

      if (!prev){
        localWallTracker.set(idx, { side, peakVol: vol });
        events.push({ t: t + step / 2, type: "wall-formed" });
      } else {
        if (prev.side !== side){
          localWallTracker.set(idx, { side, peakVol: vol });
          events.push({ t: t + step / 2, type: "wall-formed" });
        } else if (vol > prev.peakVol) {
          prev.peakVol = vol;
        } else if (vol < prev.peakVol * CONFIG.WALL_VANISH_RATIO){
          events.push({ t: t + step / 2, type: "wall-vanished" });
          localWallTracker.delete(idx);
        }
      }
    }

    const alB = new Map(), alS = new Map();
    for (const [idx, v] of buy){
      const den = state.imbMode === "diagonal" ? (sell.get(idx - 1) || 0) : (sell.get(idx) || 0);
      const umbrales = { threshold: state.threshold, minUSD: minSide, weakBase, minRelativeToImb: false };
      const [, al] = sideImb(v, den, umbrales);
      alB.set(idx, al);
    }
    for (const [idx, v] of sell){
      const den = state.imbMode === "diagonal" ? (buy.get(idx + 1) || 0) : (buy.get(idx) || 0);
      const umbrales = { threshold: state.threshold, minUSD: minSide, weakBase, minRelativeToImb: false };
      const [, al] = sideImb(v, den, umbrales);
      alS.set(idx, al);
    }

    const stB = stackedSet(alB, lo, hi, CONFIG.STACKED_N);
    const stS = stackedSet(alS, lo, hi, CONFIG.STACKED_N);
    if (stB.size + stS.size >= CONFIG.STACKED_N){
      events.push({ t: t + step / 2, type: "stack" });
    }
  }

  return events;
}

/* ============================================================================
   16. HISTÓRICO
   ============================================================================ */
let histAbort = null;

async function ensureHistLoaded(cursorMs, onProgress){
  const now = Date.now();
  const maxWin = Math.max(state.windowMin, CONFIG.WINDOW_MIN);
  const start = Math.max(CONFIG.LISTING_MS, cursorMs - maxWin * 60 * 1000);
  const end = Math.min(cursorMs, now);
  if (start > end) return;

  const gaps = coverageMissing(start, end);
  if (!gaps.length) return;

  if (histAbort) histAbort.abort();
  histAbort = new AbortController();

  for (const [gs, ge] of gaps){
    const s2 = Math.max(CONFIG.LISTING_MS, gs - CONFIG.PAD_MS);
    const e2 = Math.min(now, ge + CONFIG.PAD_MS);
    const s2c = Math.max(CONFIG.LISTING_MS, s2);
    const e2c = Math.min(now, e2);
    try {
      const data = await restLoadRange(s2c, e2c, (frac, count) => {
        if (onProgress){
          onProgress(`Cargando ${msToLocal(s2c)} → ${msToLocal(e2c)} … ${(frac * 100).toFixed(0)}% (${count.toLocaleString("en-US")})`);
        }
      }, histAbort.signal);
      storeAddMany(data);
      coverageAdd(s2c, e2c);
    } catch (ex){
      if (ex.name !== "AbortError") restNote = "hist: " + ex.message;
    }
  }
}

/* ============================================================================
   17. START LIVE
   ============================================================================ */
let liveStarted = false;

async function startLive(){
  if (liveStarted) return;
  liveStarted = true;
  feed.start();
  try {
    const now = Date.now();
    const maxRetentionMs = Math.max(...CONFIG.WINDOW_OPTIONS) * 60 * 1000;
    const data = await restLoadRange(now - maxRetentionMs, now);
    storeAddMany(data);
  } catch (ex){
    restNote = "inicial: " + ex.message;
  }
}

/* ============================================================================
   18. MUTADORES DE CONFIGURACIÓN
   ============================================================================ */
function nextWindow(){
  const i = CONFIG.WINDOW_OPTIONS.indexOf(state.windowMin);
  state.windowMin = CONFIG.WINDOW_OPTIONS[(i + 1) % CONFIG.WINDOW_OPTIONS.length];
}
function nextBucket(){
  const i = CONFIG.BUCKETS.indexOf(state.bucket);
  state.bucket = CONFIG.BUCKETS[(i + 1) % CONFIG.BUCKETS.length];
}
function nextImbMode(){
  const modes = ["diagonal", "nivel", "media", "percentil", "compuesto"];
  const i = modes.indexOf(state.imbMode);
  state.imbMode = modes[(i + 1) % modes.length];
}
function thrDelta(d){
  state.threshold = Math.max(100, Math.min(5000, state.threshold + d));
}
function clearActiveSignals(){
  state.activeSignalLive = null;
  state.activeSignalHist = null;
  state.lockedSignalLive = null;
  state.lockedSignalHist = null;
  state.signalLocked = false;
  wallTracker.clear();
  absorptionTracker.clear();
}

/* Lock real: copia inmutable de la señal actual */
function lockCurrentSignal(){
  if (state.mode === "live" && state.activeSignalLive){
    state.lockedSignalLive = JSON.parse(JSON.stringify(state.activeSignalLive));
    state.signalLocked = true;
    return true;
  }
  if (state.mode === "hist"){
    // El histórico no guarda señal activa persistente; usamos la del último snapshot
    // app.js debería llamar con el snapshot disponible. Fallback: bloquear lo que haya.
    state.signalLocked = true;
    return true;
  }
  state.signalLocked = true;
  return false;
}

function unlockSignal(){
  state.lockedSignalLive = null;
  state.lockedSignalHist = null;
  state.signalLocked = false;
}

function setSignalLock(locked){
  if (locked) lockCurrentSignal();
  else unlockSignal();
}

/* ============================================================================
   19. API PÚBLICA
   ============================================================================ */
function getRestNote(){ return restNote; }
function getFeed(){ return feed; }

window.FP = {
  CONFIG, state, store, coverage,
  wallTracker, absorptionTracker,
  nextWindow, nextBucket, nextImbMode, thrDelta,
  clearActiveSignals, lockCurrentSignal, unlockSignal, setSignalLock,
  getLiveSnapshot, getHistSnapshot, ensureHistLoaded, coverageRatio,
  startLive, getRestNote, getFeed,
  aggregate, computeVisibleStats, sideImb, stackedSet,
  detectAbsorptionByLevel, computeAbsSustained,
  updateWallTracker, computeWallStates, computeZoneContext,
  instantDelta, computePOCs, computePressure,
  computeMotorA, computeMotorB, computeRuleA, computeRuleB,
  computeStructuralSignal, vetoAgainstWall, validateTP,
  trailSignal, resolveSignalLifecycle, computeFreshSignal,
  detectEvents, percentile
};

})();
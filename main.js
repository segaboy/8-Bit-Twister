// --- SUPER GUARD: block browser's default file-open/download on drop anywhere ---
(function superGuardDnD(){
  const cancel = (e) => {
    const dt = e.dataTransfer;
    const isFile = dt && (dt.files?.length || (dt.types && [...dt.types].includes('Files')));
    if (isFile) {
      e.preventDefault();                // stop navigation/download
      try { dt.dropEffect = 'copy'; } catch {}
    }
  };
  ['dragenter','dragover','dragleave','drop'].forEach(type => {
    window.addEventListener(type, cancel,   { capture: true, passive: false });
    document.addEventListener(type, cancel, { capture: true, passive: false });
  });
})();

// ===== 8-Bit Twister (core logic) =====

// Helpers
const $ = sel => document.querySelector(sel);
const sleep = ms => new Promise(r => setTimeout(r, ms));

// Ensure JSNES is available
if (!window.jsnes) {
  alert('JSNES failed to load. Ensure jsnes.min.js is included BEFORE main.js in index.html.');
}

// Key pool (KeyboardEvent.code)
const KEY_CODES = [
  'KeyQ','KeyW','KeyE','KeyR','KeyT','KeyY','KeyU','KeyI','KeyO','KeyP',
  'KeyA','KeyS','KeyD','KeyF','KeyG','KeyH','KeyJ','KeyK','KeyL',
  'KeyZ','KeyX','KeyC','KeyV','KeyB','KeyN','KeyM',
  'Digit1','Digit2','Digit3','Digit4','Digit5','Digit6','Digit7','Digit8','Digit9','Digit0',
  'Semicolon','Comma','Period','Slash','Backslash','Minus','Equal'
];
const CODE_LABEL = { Semicolon:';', Comma:',', Period:'.', Slash:'/', Backslash:'\\', Minus:'-', Equal:'=' };
const labelFor = code =>
  CODE_LABEL[code] || (code.startsWith('Key') ? code.slice(3) : code.startsWith('Digit') ? code.slice(5) : code);

// NES buttons (order shown in legend)
const NES_BTNS = [
  ['UP',    jsnes.Controller.BUTTON_UP],
  ['DOWN',  jsnes.Controller.BUTTON_DOWN],
  ['LEFT',  jsnes.Controller.BUTTON_LEFT],
  ['RIGHT', jsnes.Controller.BUTTON_RIGHT],
  ['A',     jsnes.Controller.BUTTON_A],
  ['B',     jsnes.Controller.BUTTON_B],
  ['START', jsnes.Controller.BUTTON_START],
  ['SELECT',jsnes.Controller.BUTTON_SELECT],
];

// ---- State
let nes1, nes2;
let loopId1 = null, loopId2 = null;
let running = false;
let gameBytes = null;  // Uint8Array of ROM
let endAt = 0;
let timerId = null;
let resultsShown = false;
const keymapP1 = new Map(); // code -> btn (for emulator #1, controller 1)
const keymapP2 = new Map(); // code -> btn (for emulator #2, controller 1)
let frames1 = 0, frames2 = 0; // debug counters

// ---- Audio: single mixer with ring buffers (fast, stable) ----
let audioCtx = null;
function getAudioCtx() {
  if (!audioCtx) {
    try {
      // Prefer system default rate (often 48000) to minimize resampling
      audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    } catch {
      audioCtx = new (window.AudioContext || window.webkitAudioContext)({ sampleRate: 44100 });
    }
  }
  return audioCtx;
}

// O(1) FIFO ring buffer for audio samples
class RingBuffer {
  constructor(capacity) {
    this.buf = new Float32Array(capacity);
    this.capacity = capacity;
    this.read = 0; this.write = 0; this.size = 0;
  }
  push(x) {
    if (this.size < this.capacity) {
      this.buf[this.write] = x;
      this.write = (this.write + 1) % this.capacity;
      this.size++;
    } else { // overwrite oldest to bound latency
      this.buf[this.write] = x;
      this.write = (this.write + 1) % this.capacity;
      this.read = (this.read + 1) % this.capacity;
    }
  }
  shift() {
    if (this.size === 0) return 0;
    const x = this.buf[this.read];
    this.read = (this.read + 1) % this.capacity;
    this.size--;
    return x;
  }
}

class NesMixer {
  constructor(ctx, bufferSize = 2048) {
    this.ctx = ctx;
    this.inputs = []; // { left: RingBuffer, right: RingBuffer, gain: number, muted: bool }
    this.node = ctx.createScriptProcessor(bufferSize, 0, 2);
    this.master = ctx.createGain();
    this.master.gain.value = 0.8; // headroom to avoid clipping

    this.node.onaudioprocess = (e) => {
      const L = e.outputBuffer.getChannelData(0);
      const R = e.outputBuffer.getChannelData(1);
      const n = L.length;
      for (let i = 0; i < n; i++) {
        let mixL = 0, mixR = 0, active = 0;
        for (const ch of this.inputs) {
          if (ch.muted) continue;
          mixL += ch.left.shift() * ch.gain;
          mixR += ch.right.shift() * ch.gain;
          active++;
        }
        if (active > 1) { mixL *= 0.7; mixR *= 0.7; } // attenuate when both loud
        // soft clip
        L[i] = Math.max(-1, Math.min(1, mixL));
        R[i] = Math.max(-1, Math.min(1, mixR));
      }
    };
    this.node.connect(this.master);
    this.master.connect(ctx.destination);
  }

  createInput(initialGain = 0.45) {
    // ~2 seconds of headroom per channel to ride out brief hiccups
    const cap = Math.max(16384, (this.ctx.sampleRate * 2) | 0);
    const ch = { left: new RingBuffer(cap), right: new RingBuffer(cap), gain: initialGain, muted: false };
    this.inputs.push(ch);
    return ch;
  }
}

// ---- NES + render
function makeNes(canvasSel, audioInput) {
  const canvas = $(canvasSel);
  const ctx = canvas.getContext('2d');
  const imageData = ctx.createImageData(256,240);

  const nes = new jsnes.NES({
    onFrame: frame => {
      for (let i=0;i<256*240;i++) {
        const j=i*4, c=frame[i];
        imageData.data[j  ] =  c & 0xFF;
        imageData.data[j+1] = (c>> 8) & 0xFF;
        imageData.data[j+2] = (c>>16) & 0xFF;
        imageData.data[j+3] = 0xFF;
      }
      ctx.putImageData(imageData,0,0);
      if (nes === nes1) frames1++; else frames2++;
    },
    onAudioSample: (l, r) => {
      if (!audioInput) return;
      audioInput.left.push(l);
      audioInput.right.push(r);
    },
  });

  // Fill black immediately
  ctx.fillStyle = '#000';
  ctx.fillRect(0,0,256,240);

  return nes;
}

function startLoops() {
  const step1 = () => { if (nes1) nes1.frame(); loopId1 = requestAnimationFrame(step1); };
  const step2 = () => { if (nes2) nes2.frame(); loopId2 = requestAnimationFrame(step2); };
  if (!loopId1) step1();
  if (!loopId2) step2();
}
function stopLoops() {
  if (loopId1) { cancelAnimationFrame(loopId1); loopId1 = null; }
  if (loopId2) { cancelAnimationFrame(loopId2); loopId2 = null; }
}

// ---- Key randomization + legend
function pickUnique(pool, count, taken = new Set()) {
  const avail = pool.filter(c => !taken.has(c));
  for (let i = avail.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random()*(i+1));
    [avail[i],avail[j]] = [avail[j],avail[i]];
  }
  return avail.slice(0, count);
}
function randomizeKeybinds() {
  keymapP1.clear(); keymapP2.clear();
  const used = new Set();
  const p1 = pickUnique(KEY_CODES, NES_BTNS.length, used); p1.forEach(c => used.add(c));
  const p2 = pickUnique(KEY_CODES, NES_BTNS.length, used);

  NES_BTNS.forEach(([,btn], i) => keymapP1.set(p1[i], btn));
  NES_BTNS.forEach(([,btn], i) => keymapP2.set(p2[i], btn));

  const renderTable = (codes, el) => {
    let html = '<table>';
    NES_BTNS.forEach(([label], i) => { html += `<tr><td>${label}</td><td><b>${labelFor(codes[i])}</b></td></tr>`; });
    html += '</table>';
    el.innerHTML = html;
  };
  renderTable(p1, $('#keys1'));
  renderTable(p2, $('#keys2'));
}

// ---- Keyboard → NES
function handleKey(e, down) {
  const code = e.code;
  let handled = false;

  // Emulator #1 uses controller 1
  if (keymapP1.has(code)) {
    const btn = keymapP1.get(code);
    down ? nes1.buttonDown(1, btn) : nes1.buttonUp(1, btn);
    handled = true;
  }
  // Emulator #2 uses controller 1 (separate instance)
  if (keymapP2.has(code)) {
    const btn = keymapP2.get(code);
    down ? nes2.buttonDown(1, btn) : nes2.buttonUp(1, btn);
    handled = true;
  }
  if (handled) e.preventDefault();
}
addEventListener('keydown', e => running && handleKey(e, true));
addEventListener('keyup',   e => running && handleKey(e, false));

// ---- ROM load helpers
function u8ToBinaryString(u8) {
  const CHUNK = 0x8000;
  let s = '';
  for (let i = 0; i < u8.length; i += CHUNK) {
    s += String.fromCharCode.apply(null, u8.subarray(i, i + CHUNK));
  }
  return s;
}
function isINes(u8) {
  return u8[0]===0x4E && u8[1]===0x45 && u8[2]===0x53 && u8[3]===0x1A; // "NES<EOF>"
}

async function loadRomFromFile(file) {
  const buf = await file.arrayBuffer();
  const u8  = new Uint8Array(buf);
  if (!isINes(u8)) {
    alert('This does not look like a valid .nes ROM (missing NES header).');
    return;
  }
  gameBytes = u8;

  const romString = u8ToBinaryString(u8); // preferred for JSNES
  try {
    nes1.loadROM(romString);
    nes2.loadROM(romString);
  } catch (err) {
    console.error('loadROM threw:', err);
    alert('Failed to load ROM (exception). See console.');
    return;
  }

  // Draw one frame immediately
  nes1.frame(); nes2.frame();

  randomizeKeybinds();
  if (!running) startMatch();
  console.log('ROM loaded:', file.name, 'bytes:', u8.length);
}

// ---- DnD guards + dropzone + click-to-choose
function setupDnD() {
  const dz = document.querySelector('.dropzone');
  if (!dz) return;

  const onOver = (e) => {
    e.preventDefault();
    dz.classList.add('dragging');
    try { if (e.dataTransfer) e.dataTransfer.dropEffect = 'copy'; } catch {}
  };
  const onLeave = (e) => {
    e.preventDefault();
    dz.classList.remove('dragging');
  };

  dz.addEventListener('dragenter', onOver);
  dz.addEventListener('dragover',  onOver);
  dz.addEventListener('dragleave', onLeave);

  dz.addEventListener('drop', async (e) => {
    e.preventDefault();
    dz.classList.remove('dragging');
    const file = e.dataTransfer?.files?.[0];
    if (!file) return;

    // 🔊 resume audio on user gesture
    const ctx = getAudioCtx();
    if (ctx && ctx.state !== 'running') { try { await ctx.resume(); } catch {} }

    await loadRomFromFile(file);
  });

  // Optional convenience: allow drop anywhere on the page
  window.addEventListener('drop', async (e) => {
    const file = e.dataTransfer?.files?.[0];
    if (!file) return;

    const ctx = getAudioCtx();
    if (ctx && ctx.state !== 'running') { try { await ctx.resume(); } catch {} }

    await loadRomFromFile(file);
  }, { passive:false });
}

function setupChooserFallback() {
  const input = document.createElement('input');
  input.type = 'file';
  input.accept = '.nes';
  input.style.display = 'none';
  document.body.appendChild(input);

  input.addEventListener('change', async () => {
    if (input.files[0]) {
      const ctx = getAudioCtx();
      if (ctx && ctx.state !== 'running') { try { await ctx.resume(); } catch {} }
      await loadRomFromFile(input.files[0]);
      input.value = '';
    }
  });

  const dz = document.querySelector('.dropzone');
  if (dz) {
    dz.style.cursor = 'pointer';
    dz.title = 'Click to choose a .nes file';
    dz.addEventListener('click', () => input.click());
  }
}

// ---- Timer / modal
function fmt(s){ const m=Math.floor(s/60), r=s%60; return `${String(m).padStart(2,'0')}:${String(r).padStart(2,'0')}`; }
function startTimer(seconds) {
  endAt = Date.now() + seconds*1000;
  $('#timer').textContent = fmt(seconds);

  if (timerId) { clearInterval(timerId); timerId = null; }
  resultsShown = false;

  timerId = setInterval(() => {
    const left = Math.max(0, Math.ceil((endAt - Date.now())/1000));
    $('#timer').textContent = fmt(left);
    if (left <= 0) {
      clearInterval(timerId);
      timerId = null;
      if (!resultsShown) {
        stopMatch();
        showResults();
        resultsShown = true;
      }
    }
  }, 200);
}
function showResults(){ $('#results').classList.add('show'); }
function hideResults(){ $('#results').classList.remove('show'); }

// ---- Match controls
function startMatch() {
  if (!gameBytes) { alert('Drop a .nes ROM first.'); return; }

  // 🔊 Ensure audio is unlocked on user gesture
  const ctx = getAudioCtx();
  if (ctx && ctx.state !== 'running') { ctx.resume(); }

  if (!running) {
    running = true;
    startLoops();
    startTimer(parseInt($('#duration').value, 10));

    // Debug: check frames are advancing
    frames1 = 0; frames2 = 0;
    setTimeout(() => console.log('FPS ~1s:', { p1: frames1, p2: frames2 }), 1000);
  }
}
function stopMatch() {
  running = false;
  stopLoops();
  if (timerId) { clearInterval(timerId); timerId = null; }
}

// ---- Bootstrap
function init() {
  setupChooserFallback();
  setupDnD();

  const ctx = getAudioCtx();                 // one shared context
  const mixer = new NesMixer(ctx, 2048);     // raise to 4096 if your CPU is slow
  const chan1 = mixer.createInput(0.45);
  const chan2 = mixer.createInput(0.45);

  nes1 = makeNes('#screen1', chan1);
  nes2 = makeNes('#screen2', chan2);

  randomizeKeybinds();

  // Buttons
  $('#randomize').onclick = () => randomizeKeybinds();
  $('#start').onclick     = () => startMatch();
  $('#stop').onclick      = () => stopMatch();
  $('#newRound').onclick  = async () => { hideResults(); randomizeKeybinds(); await sleep(50); startMatch(); };
  $('#close').onclick     = () => hideResults();
}
document.addEventListener('DOMContentLoaded', init);

// --- HARD GUARD: block the browser's default file-open/download on drop anywhere ---
(function hardBlockDefaultDnD(){
  const cancel = (e) => {
    // Always prevent default so the browser never navigates/downloads
    if (e && e.dataTransfer) {
      e.preventDefault();
      // make the cursor show "copy" when dragging files
      try { e.dataTransfer.dropEffect = 'copy'; } catch {}
    }
  };
  ['dragenter','dragover','dragleave','drop'].forEach(type => {
    // Capture phase so we beat any other listener
    window.addEventListener(type, cancel,   { capture: true, passive: false });
    document.addEventListener(type, cancel, { capture: true, passive: false });
  });
})();


// ---- Audio: single mixer for both emulators ----
let audioCtx = null;
function getAudioCtx() {
  if (!audioCtx) {
    // Try to match NES core output rate (often ~44100)
    try {
      audioCtx = new (window.AudioContext || window.webkitAudioContext)({ sampleRate: 44100 });
    } catch {
      audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    }
  }
  return audioCtx;
}

class NesMixer {
  constructor(ctx, bufferSize = 1024) {
    this.ctx = ctx;
    this.inputs = []; // { left:[], right:[], gain: number, muted: bool }
    this.node = ctx.createScriptProcessor(bufferSize, 0, 2);
    this.master = ctx.createGain();
    this.master.gain.value = 0.9;

    this.node.onaudioprocess = (e) => {
      const L = e.outputBuffer.getChannelData(0);
      const R = e.outputBuffer.getChannelData(1);
      const n = L.length;
      for (let i = 0; i < n; i++) {
        let mixL = 0, mixR = 0, active = 0;
        for (const ch of this.inputs) {
          if (ch.muted) continue;
          const sl = ch.left.length ? ch.left.shift() : 0;
          const sr = ch.right.length ? ch.right.shift() : 0;
          mixL += sl * ch.gain;
          mixR += sr * ch.gain;
          active++;
        }
        // gentle limiting/attenuation (avoid clipping when both are loud)
        // -6 dB per two inputs; tweak if you like
        if (active > 1) { mixL *= 0.7; mixR *= 0.7; }
        // soft clip to [-1,1]
        L[i] = Math.max(-1, Math.min(1, mixL));
        R[i] = Math.max(-1, Math.min(1, mixR));
      }
      // Keep queues bounded (~1s safety)
      for (const ch of this.inputs) {
        const MAX = this.ctx.sampleRate;
        if (ch.left.length > MAX)  ch.left.splice(0, ch.left.length - MAX);
        if (ch.right.length > MAX) ch.right.splice(0, ch.right.length - MAX);
      }
    };

    this.node.connect(this.master);
    this.master.connect(ctx.destination);
  }

  createInput(initialGain = 0.5) {
    const ch = { left: [], right: [], gain: initialGain, muted: false };
    this.inputs.push(ch);
    return ch;
  }
}

class NesAudio {
  constructor(ctx, initialVol = 0.6) {
    this.ctx = ctx;
    this.volume = initialVol;
    this.muted = false;

    this.gain = ctx.createGain();
    this.gain.gain.value = initialVol;

    // ScriptProcessor: simplest cross-browser way (AudioWorklet is nicer but heavier)
    this.node = ctx.createScriptProcessor(2048, 0, 2);
    this.left = [];
    this.right = [];
    this.node.onaudioprocess = (e) => {
      const L = e.outputBuffer.getChannelData(0);
      const R = e.outputBuffer.getChannelData(1);
      for (let i = 0; i < L.length; i++) {
        L[i] = this.left.length ? this.left.shift() : 0;
        R[i] = this.right.length ? this.right.shift() : 0;
      }
      // keep queues bounded so they don’t grow forever if tab throttles
      const MAX = 44100; // ~1s of audio
      if (this.left.length > MAX)  this.left.splice(0, this.left.length - MAX);
      if (this.right.length > MAX) this.right.splice(0, this.right.length - MAX);
    };

    this.node.connect(this.gain);
    this.gain.connect(ctx.destination);
  }
  push(l, r) {
    // JSNES gives floats -1..1
    this.left.push(l);
    this.right.push(r);
  }
  setVolume(v) {
    this.volume = v;
    if (!this.muted) this.gain.gain.value = v;
  }
  setMuted(m) {
    this.muted = m;
    this.gain.gain.value = m ? 0 : this.volume;
  }
}


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
const keymapP1 = new Map(); // code -> btn (for emulator #1, controller 1)
const keymapP2 = new Map(); // code -> btn (for emulator #2, controller 1)
let frames1 = 0, frames2 = 0; // debug counters

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
    if (typeof getAudioCtx === 'function') {
      const ctx = getAudioCtx();
      if (ctx && ctx.state !== 'running') { try { await ctx.resume(); } catch {} }
    }
    await loadRomFromFile(file);
  });

  // Optional convenience: allow drop anywhere on the page
  window.addEventListener('drop', async (e) => {
    const file = e.dataTransfer?.files?.[0];
    if (!file) return;
    if (typeof getAudioCtx === 'function') {
      const ctx = getAudioCtx();
      if (ctx && ctx.state !== 'running') { try { await ctx.resume(); } catch {} }
    }
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
      await loadRomFromFile(input.files[0]);
      input.value = '';
    }
  });

  const dz = document.querySelector('.dropzone');
  dz.style.cursor = 'pointer';
  dz.title = 'Click to choose a .nes file';
  dz.addEventListener('click', () => input.click());
}

// ---- Timer / modal
let timerId = null;
let resultsShown = false;   // <-- add this
function fmt(s){ const m=Math.floor(s/60), r=s%60; return `${String(m).padStart(2,'0')}:${String(r).padStart(2,'0')}`; }
function startTimer(seconds) {
  endAt = Date.now() + seconds * 1000;
  $('#timer').textContent = fmt(seconds);

  if (timerId) { clearInterval(timerId); timerId = null; }
  resultsShown = false;  // new round -> not shown yet

  timerId = setInterval(() => {
    const left = Math.max(0, Math.ceil((endAt - Date.now()) / 1000));
    $('#timer').textContent = fmt(left);

    if (left <= 0) {
      clearInterval(timerId);   // <-- stop the ticker
      timerId = null;

      if (!resultsShown) {      // <-- only once
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

  // 🔊 Unlock/resume Web Audio (autoplay policy requires a user gesture)
  if (typeof getAudioCtx === 'function') {
    const ctx = getAudioCtx();
    if (ctx && ctx.state !== 'running') { ctx.resume(); }
  }

  if (!running) {
    running = true;
    startLoops();
    startTimer(parseInt($('#duration').value, 10));

    // Debug: check frames are advancing
    frames1 = 0; frames2 = 0;
    setTimeout(() => console.log('FPS ~1s:', { p1: frames1, p2: frames2 }), 1000);
  }
}

function stopMatch() { running = false; stopLoops(); }

// ---- Bootstrap
function init() {
  setupChooserFallback();
  setupDnD();

  const ctx = getAudioCtx();                    // one shared context
  const mixer = new NesMixer(ctx);              // one shared mixer
  const chan1 = mixer.createInput(0.6);         // P1 audio channel
  const chan2 = mixer.createInput(0.6);         // P2 audio channel

  nes1 = makeNes('#screen1', chan1);
  nes2 = makeNes('#screen2', chan2);

  // Hook your existing volume/mute UI (if you added it)
  const vol1 = $('#vol1'), vol2 = $('#vol2');
  const mute1 = $('#mute1'), mute2 = $('#mute2');
  if (vol1) vol1.addEventListener('input', e => chan1.gain = parseFloat(e.target.value));
  if (vol2) vol2.addEventListener('input', e => chan2.gain = parseFloat(e.target.value));
  if (mute1) mute1.addEventListener('click', () => {
    chan1.muted = !chan1.muted; mute1.textContent = chan1.muted ? '🔇' : '🔊';
  });
  if (mute2) mute2.addEventListener('click', () => {
    chan2.muted = !chan2.muted; mute2.textContent = chan2.muted ? '🔇' : '🔊';
  });

  randomizeKeybinds();

  // Buttons
  $('#randomize').onclick = () => randomizeKeybinds();
  $('#start').onclick     = () => startMatch();
  $('#stop').onclick      = () => stopMatch();
  $('#newRound').onclick  = async () => { hideResults(); randomizeKeybinds(); await sleep(50); startMatch(); };
  $('#close').onclick     = () => hideResults();
}

document.addEventListener('DOMContentLoaded', init);

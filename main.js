// --- HARD GUARD: stop the browser from opening/downloading files on drop anywhere ---
(function hardBlockDefaultDnD(){
  const guard = (e) => {
    const dt = e.dataTransfer;
    const isFile = dt && (dt.files?.length || (dt.types && [...dt.types].includes('Files')));
    if (isFile) e.preventDefault(); // don't stopPropagation; let our handlers run
  };
  ['dragenter','dragover','dragleave','drop'].forEach(type => {
    window.addEventListener(type, guard, { capture: true, passive: false });
    document.addEventListener(type, guard, { capture: true, passive: false });
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
const keymapP1 = new Map(); // code -> btn (for emulator #1, controller 1)
const keymapP2 = new Map(); // code -> btn (for emulator #2, controller 1)
let frames1 = 0, frames2 = 0; // debug counters

// ---- NES + render
function makeNes(canvasSel) {
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
  ['dragenter','dragover'].forEach(ev => {
    dz.addEventListener(ev, e => { e.preventDefault(); dz.classList.add('dragging'); });
  });
  ['dragleave','drop'].forEach(ev => {
    dz.addEventListener(ev, e => { e.preventDefault(); dz.classList.remove('dragging'); });
  });
  dz.addEventListener('drop', async e => {
    const file = e.dataTransfer.files?.[0];
    if (file) await loadRomFromFile(file);
  });

  // Accept drop anywhere too (convenience)
  window.addEventListener('drop', async (e) => {
    const file = e.dataTransfer?.files?.[0];
    if (file) await loadRomFromFile(file);
  });
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
  if (!running) {
    running = true;
    startLoops();
    startTimer(parseInt($('#duration').value, 10));

    // Debug: check frames are advancing
    frames1 = 0; frames2 = 0;
    setTimeout(() => {
      console.log('FPS ~1s:', { p1: frames1, p2: frames2 });
      frames1 = 0; frames2 = 0;
    }, 1000);
  }
}
function stopMatch() { running = false; stopLoops(); }

// ---- Bootstrap
function init() {
  setupChooserFallback();
  setupDnD();

  nes1 = makeNes('#screen1');
  nes2 = makeNes('#screen2');

  randomizeKeybinds();

  // Buttons
  $('#randomize').onclick = () => randomizeKeybinds();
  $('#start').onclick     = () => startMatch();
  $('#stop').onclick      = () => stopMatch();
  $('#newRound').onclick  = async () => { hideResults(); randomizeKeybinds(); await sleep(50); startMatch(); };
  $('#close').onclick     = () => hideResults();
}
document.addEventListener('DOMContentLoaded', init);

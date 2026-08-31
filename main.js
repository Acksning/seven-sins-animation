/* ── INTP 七宗罪 · 傲慢 ↔ 怠惰 · 雷达 + 3D 沙漏 ── */

const PRIDE_IDX = 0;
const SLOTH_IDX = 4;
const RADAR_ROT = -15 * Math.PI / 180;

const SINS = [
  { label: '傲慢', angle: -Math.PI / 2, key: 'pride' },
  { label: '嫉妒', angle: -Math.PI / 2 + (2 * Math.PI / 7) * 1 },
  { label: '贪婪', angle: -Math.PI / 2 + (2 * Math.PI / 7) * 2 },
  { label: '色欲', angle: -Math.PI / 2 + (2 * Math.PI / 7) * 3 },
  { label: '怠惰', angle: -Math.PI / 2 + (2 * Math.PI / 7) * 4, key: 'sloth' },
  { label: '暴食', angle: -Math.PI / 2 + (2 * Math.PI / 7) * 5 },
  { label: '暴怒', angle: -Math.PI / 2 + (2 * Math.PI / 7) * 6 },
];

let pulsePhase = 0;

const radarCanvas = document.getElementById('radarCanvas');
const radarCtx = radarCanvas.getContext('2d');
let radarSize = 0;
let radarCenter = { x: 0, y: 0 };
let radarRadius = 0;

function resizeRadar() {
  const rect = radarCanvas.getBoundingClientRect();
  const dpr = window.devicePixelRatio || 1;
  radarCanvas.width = rect.width * dpr;
  radarCanvas.height = rect.height * dpr;
  radarCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
  radarSize = rect.width;
  radarCenter = { x: rect.width / 2, y: rect.height / 2 };
  radarRadius = rect.width * 0.36;
}

function drawRadar(t) {
  const hg = window.Hourglass3D?.getState?.();
  const sourceIsPride = hg?.sourceIsPride ?? false;
  const sourceIsSloth = hg?.sourceIsSloth ?? false;
  const flipDeg = hg?.flipDeg ?? 0;
  const flipRad = (flipDeg * Math.PI) / 180;

  const ctx = radarCtx;
  const { x: cx, y: cy } = radarCenter;
  const r = radarRadius;
  pulsePhase = t * 0.002;

  ctx.clearRect(0, 0, radarSize, radarSize);

  // 中心微光，锚定视觉焦点
  const coreGlow = ctx.createRadialGradient(cx, cy, 0, cx, cy, r * 0.55);
  coreGlow.addColorStop(0, 'rgba(168, 85, 247, 0.04)');
  coreGlow.addColorStop(0.6, 'rgba(109, 40, 217, 0.015)');
  coreGlow.addColorStop(1, 'rgba(0, 0, 0, 0)');
  ctx.fillStyle = coreGlow;
  ctx.fillRect(0, 0, radarSize, radarSize);

  ctx.save();
  ctx.translate(cx, cy);
  ctx.rotate(RADAR_ROT);
  ctx.translate(-cx, -cy);

  ctx.lineJoin = 'round';

  for (let lv = 1; lv <= 5; lv++) {
    const lr = (r * lv) / 5;
    const isOuter = lv === 5;
    ctx.beginPath();
    for (let i = 0; i <= 7; i++) {
      const angle = -Math.PI / 2 + (2 * Math.PI / 7) * i;
      const px = cx + Math.cos(angle) * lr;
      const py = cy + Math.sin(angle) * lr;
      i === 0 ? ctx.moveTo(px, py) : ctx.lineTo(px, py);
    }
    if (isOuter) {
      ctx.shadowColor = 'rgba(192, 132, 252, 0.55)';
      ctx.shadowBlur = 6;
    }
    ctx.strokeStyle = `rgba(192, 132, 252, ${0.1 + lv * 0.038})`;
    ctx.lineWidth = isOuter ? 1.15 : 0.75 + lv * 0.05;
    ctx.stroke();
    ctx.shadowBlur = 0;
  }

  for (let i = 0; i < 7; i++) {
    const angle = -Math.PI / 2 + (2 * Math.PI / 7) * i;
    const isKey = i === PRIDE_IDX || i === SLOTH_IDX;
    ctx.beginPath();
    ctx.moveTo(cx, cy);
    ctx.lineTo(cx + Math.cos(angle) * r, cy + Math.sin(angle) * r);
    ctx.strokeStyle = isKey
      ? 'rgba(216, 180, 254, 0.28)'
      : 'rgba(216, 180, 254, 0.14)';
    ctx.lineWidth = isKey ? 1.05 : 0.7;
    if (isKey) {
      ctx.shadowColor = 'rgba(192, 132, 252, 0.4)';
      ctx.shadowBlur = 5;
    }
    ctx.stroke();
    ctx.shadowBlur = 0;
  }

  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  for (let i = 0; i < SINS.length; i++) {
    const sin = SINS[i];
    const isKey = sin.key === 'pride' || sin.key === 'sloth';
    const labelR = isKey ? r + 32 : r + 28;
    const lx = cx + Math.cos(sin.angle) * labelR;
    const ly = cy + Math.sin(sin.angle) * labelR;
    const isActive = (sin.key === 'pride' && sourceIsPride) || (sin.key === 'sloth' && sourceIsSloth);

    ctx.save();
    ctx.translate(lx, ly);
    ctx.rotate(-RADAR_ROT - flipRad);

    if (isKey) {
      const pulse = isActive ? 0.75 + Math.sin(pulsePhase * 2.2) * 0.25 : 0.55;
      ctx.font = '700 21px "Songti SC", "Noto Serif SC", serif';

      // 背后柔光圆盘：与字形分离，避免 shadowBlur 糊字
      const haloR = isActive ? 32 : 26;
      const halo = ctx.createRadialGradient(0, 0, 0, 0, 0, haloR);
      halo.addColorStop(0, `rgba(216, 180, 254, ${0.32 * pulse})`);
      halo.addColorStop(0.5, `rgba(168, 85, 247, ${0.14 * pulse})`);
      halo.addColorStop(1, 'rgba(124, 58, 237, 0)');
      ctx.fillStyle = halo;
      ctx.beginPath();
      ctx.arc(0, 0, haloR, 0, Math.PI * 2);
      ctx.fill();

      ctx.shadowBlur = 0;
      ctx.lineJoin = 'round';
      ctx.strokeStyle = 'rgba(36, 8, 58, 0.9)';
      ctx.lineWidth = 3;
      ctx.strokeText(sin.label, 0, 0);
      ctx.fillStyle = sin.key === 'pride'
        ? 'rgba(252, 248, 255, 0.98)'
        : 'rgba(245, 235, 255, 0.96)';
      ctx.fillText(sin.label, 0, 0);
      ctx.strokeStyle = `rgba(192, 132, 252, ${0.4 + pulse * 0.3})`;
      ctx.lineWidth = 0.75;
      ctx.strokeText(sin.label, 0, 0);
    } else {
      ctx.shadowBlur = 0;
      ctx.fillStyle = 'rgba(216,180,254,0.32)';
      ctx.font = '400 14px "Songti SC", "Noto Serif SC", serif';
      ctx.fillText(sin.label, 0, 0);
    }
    ctx.restore();
  }
  ctx.restore();
}

function animate(t) {
  drawRadar(t);
  requestAnimationFrame(animate);
}

function start() {
  resizeRadar();
  requestAnimationFrame(animate);
}

window.addEventListener('resize', resizeRadar);
window.addEventListener('hourglass-ready', start);
if (window.Hourglass3D) start();

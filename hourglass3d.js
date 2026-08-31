/**
 * 简化版 Hourglass_Fable5 — Three.js + Rapier
 * 核心：等效参考系翻转（rig 旋转 + 重力同步），漏完自动 flip
 * @see https://github.com/khanmjk/Hourglass_Fable5
 */
import * as THREE from 'three';
import * as RAPIER_NS from '@dimforge/rapier3d-simd-compat';

const RAPIER = RAPIER_NS.default ?? RAPIER_NS;

/* ── 玻璃轮廓（Lathe 旋转体 + 物理碰撞墙共用同一 profileR）
 *    改形状：主要调 BULB_R / NECK_R / CAP_R / H / WAIST_Y
 *    · 整体更「细瘦」→ 减小 BULB_R、CAP_R
 *    · 颈部更细      → 减小 NECK_R（漏沙会变慢、易堵）
 *    · 更高/更矮     → 改 H
 *    · 腰线上下比例  → 改 WAIST_Y（默认 0.62*H） ── */
const G = 75;              // 重力强度；翻转时按角度分解到 x/y
const H = 15.5;            // 玻璃半高（中心到顶/底），越大沙漏越高
const BULB_R = 5;          // 球泡最宽处内径；减小→上下室更窄
const NECK_R = 0.6;        // 颈部最窄处内径；减小→颈更细、流更慢
const CAP_R = 4;           // 球泡与顶/底收口处内径；减小→整体更修长
const WAIST_Y = 0.9 * H;  // 腰线高度：控制细颈到球泡的过渡位置
const THROAT_H = 0.2;      // 颈部区域半高（漏沙通道的竖直范围）

/* ── 沙粒（最常改的三项） ── */
const GRAINS_N = 10000;     // 沙粒总数（上室+下室）；越多越密、越耗性能
const GRAIN_R = 0.2;       // 单粒半径：同时控制 3D 显示大小与 Rapier 碰撞球
const GRAIN_COLOR = 0xc084fc;       // --purple-400，3D 下比文字色更饱和才不发灰
const GRAIN_COLOR_PRIDE = 0xd8b4fe; // 傲慢室：偏暖
const GRAIN_COLOR_SLOTH = 0xc084fc; // 怠惰室：略冷
const GRAIN_EMISSIVE = 0xc084fc;
const GRAIN_EMISSIVE_INTENSITY = 1.0; // 强度烘焙进 emissive 颜色
const GRAIN_EMISSIVE_STRENGTH = 0.52;

/* ── 玻璃边缘辉光（shell shader，无 transmission / PMREM） ── */
const RIM_GLOW_COLOR = 0xc084fc;
const RIM_GLOW_COLOR_B = 0x9333ea;
const RIM_BASE_INTENSITY = 1.0;
const RIM_FLIP_BOOST = 0.45;
const HALO_INTENSITY = 0.68;
const INNER_RIM_INTENSITY = 0.58;

/* 与 main.js radarRadius = width * 0.36 对齐；略缩小以贴七边形内缘 */
const HEPTAGON_RADIUS_RATIO = 0.36;
const HOURGLASS_VIEW_SCALE = 0.90;

/* ── 物理步进 ── */
const DT = 1 / 120;        // 物理仿真步长（秒/步），120Hz
const MAX_STEPS = 3;       // 每帧最多补算几步，防止卡顿后物理爆炸
const V_MAX = 60;          // 单粒最大速度上限，防止穿透玻璃
const SLEEP_SP2 = 0.25;    // 低于此速度² 且持续数帧则强制休眠，省性能

/* ── 漏沙计量（freeze-plug 控制面） ── */
const TRANSIT_S = 0.9;     // 沙粒从颈部落到底部的估计耗时，用于排程
const REL_CAP = 90;        // 每帧最多释放几粒过颈部，防卡顿后一次性喷涌
const BANDS = 12;          // 同帧多粒释放时，在颈部下方错开落点层数

/* ── 循环时序 ── */
const BASE_DRAIN_SEC = 36;       // 上室满沙时，漏完一整室的基础时长（秒）
const FLIP_MS = 1400;            // 翻转动画时长（rig 旋转 + 重力同步）
const FLIP_SETTLE_MS = 700;      // 翻转后等待沙堆稳定的时长
const PAUSE_BEFORE_FLIP_MS = 500; // 上室漏空后、自动翻转前的停驻

function profileR(u) {
  const smooth = (t) => t * t * (3 - 2 * t);
  if (u <= WAIST_Y) return NECK_R + (BULB_R - NECK_R) * smooth(u / WAIST_Y);
  const t = Math.min(1, (u - WAIST_Y) / (H - WAIST_Y));
  return BULB_R + (CAP_R - BULB_R) * smooth(t);
}

/* ── 由 GRAIN_R / NECK_R 推导的颈部几何（一般随 GRAIN_R 自动生效） ── */
const Y_HOLD = THROAT_H + GRAIN_R * 1.4;   // 低于此线的未释放沙粒会被冻结（plug）
const HOLD_R2 = (NECK_R * 1.9) ** 2;       // 颈部柱形冻结区的水平半径²
const FEED_Y = THROAT_H + GRAIN_R * 9;     // 唤醒上方喂料区的纵向范围
const FEED_R2 = (NECK_R * 2.2) ** 2;       // 喂料区中心柱半径²

let canvas, renderer, scene, camera, rig, glassShellMat, glassInnerShellMat, glassHaloMat, grainMesh, coreLayer, hourglassLayer;
let world, bodies = [];
let N = 0;

const posCache = new Float32Array(GRAINS_N * 3);
const frozen = new Uint8Array(GRAINS_N);
const released = new Uint8Array(GRAINS_N);
const grainType = new Uint8Array(GRAINS_N); // 0=傲慢 1=怠惰
const slowFrames = new Uint8Array(GRAINS_N);
let frozenList = [];

const _m = new THREE.Matrix4();
const _q = new THREE.Quaternion();
const _v = new THREE.Vector3();
const _s = new THREE.Vector3(1, 1, 1);

let state = 'boot';
let effDuration = BASE_DRAIN_SEC;
let startStamp = 0;
let elapsedMs = 0;
let releasedCount = 0;
let topStart = 0;
let orientation = 1;
let thetaBase = 0;
let displayTheta = 0;
let flipPhase = null;
let flipT0 = 0;
let flipSettleT0 = 0;
let autoFlipAt = 0;
let acc = 0;
let lastT = 0;
let settle = null;
let ready = false;
let flipGlowBoost = 0;

const publicState = {
  pride: 0.5,
  sloth: 0.5,
  flipDeg: 0,
  flipping: false,
  sourceIsPride: true,
  sourceIsSloth: false,
};

function setGravity(gx, gy) {
  world.gravity.x = gx;
  world.gravity.y = gy;
  world.gravity.z = 0;
}

function freeze(i) {
  bodies[i].setBodyType(RAPIER.RigidBodyType.Fixed, false);
  frozen[i] = 1;
  frozenList.push(i);
}

function unfreeze(i, wake) {
  bodies[i].setBodyType(RAPIER.RigidBodyType.Dynamic, wake);
  frozen[i] = 0;
}

function unfreezeAll() {
  for (let i = 0; i < N; i++) if (frozen[i]) unfreeze(i, true);
  frozenList = [];
}

function freezePass() {
  for (let i = 0; i < N; i++) {
    if (frozen[i] || released[i]) continue;
    const yo = posCache[i * 3 + 1] * orientation;
    if (yo > Y_HOLD) continue;
    const x = posCache[i * 3];
    const z = posCache[i * 3 + 2];
    if (x * x + z * z < HOLD_R2) freeze(i);
  }
}

function dropThroughNeck(i, burstIdx) {
  const band = burstIdx % BANDS;
  const a = Math.random() * Math.PI * 2;
  const rr = Math.random() * NECK_R * 0.4;
  if (frozen[i]) unfreeze(i, true);
  bodies[i].setTranslation({
    x: Math.cos(a) * rr,
    y: -(THROAT_H + GRAIN_R * 1.6 + band * GRAIN_R * 2.2) * orientation,
    z: Math.sin(a) * rr,
  }, true);
  bodies[i].setLinvel({
    x: (Math.random() - 0.5) * 1.5,
    y: -3 * orientation,
    z: (Math.random() - 0.5) * 1.5,
  }, true);
  bodies[i].setAngvel({ x: 0, y: 0, z: 0 }, false);
  released[i] = 1;
  releasedCount++;
}

function wakeFeedZone() {
  for (let i = 0; i < N; i++) {
    if (frozen[i] || released[i]) continue;
    const yo = posCache[i * 3 + 1] * orientation;
    if (yo < 0) continue;
    const x = posCache[i * 3];
    const z = posCache[i * 3 + 2];
    if (yo < FEED_Y || x * x + z * z < FEED_R2) bodies[i].wakeUp();
  }
}

function meter(now, complete = false) {
  if (!complete) elapsedMs = now - startStamp;
  const p = complete ? 1 : Math.min(1, (elapsedMs / 1000) / Math.max(0.5, effDuration - TRANSIT_S));
  const target = complete ? topStart : Math.round(topStart * p);
  let need = Math.min(REL_CAP, target - releasedCount);
  let releasedNow = 0;
  if (need > 0) {
    while (need > 0 && frozenList.length) {
      const i = frozenList.pop();
      if (released[i] || !frozen[i]) continue;
      dropThroughNeck(i, releasedNow);
      need--;
      releasedNow++;
    }
    if (need > 0) {
      const cands = [];
      for (let i = 0; i < N; i++) if (!released[i]) cands.push(i);
      cands.sort((a, b) => posCache[a * 3 + 1] * orientation - posCache[b * 3 + 1] * orientation);
      for (let k = 0; k < cands.length && need > 0; k++) {
        dropThroughNeck(cands[k], releasedNow);
        need--;
        releasedNow++;
      }
    }
    if (releasedNow > 0) wakeFeedZone();
  }
}

function postStep(force = false) {
  let dirty = false;
  const maxSq = V_MAX * V_MAX;
  for (let i = 0; i < N; i++) {
    const b = bodies[i];
    if (!force && (frozen[i] || b.isSleeping())) continue;
    const t = b.translation();
    const r = b.rotation();
    posCache[i * 3] = t.x;
    posCache[i * 3 + 1] = t.y;
    posCache[i * 3 + 2] = t.z;
    if (!frozen[i]) {
      const v = b.linvel();
      const sq = v.x * v.x + v.y * v.y + v.z * v.z;
      if (sq > maxSq) {
        const s = V_MAX / Math.sqrt(sq);
        b.setLinvel({ x: v.x * s, y: v.y * s, z: v.z * s }, true);
        slowFrames[i] = 0;
      } else if (!force && sq < SLEEP_SP2 && state !== 'settling' && !flipPhase) {
        if (++slowFrames[i] >= 4) { b.sleep(); slowFrames[i] = 0; }
      } else {
        slowFrames[i] = 0;
      }
      const rxz = Math.hypot(t.x, t.z);
      if (rxz > profileR(Math.min(Math.abs(t.y), H)) + GRAIN_R * 2 || Math.abs(t.y) > H + 1.5) {
        const yc = THREE.MathUtils.clamp(t.y, -H + 1, H - 1);
        const rSafe = Math.max(0.1, profileR(Math.abs(yc)) * 0.5);
        const sc = rxz > 1e-4 ? rSafe / rxz : 0;
        b.setTranslation({ x: t.x * sc, y: yc, z: t.z * sc }, true);
        b.setLinvel({ x: 0, y: 0, z: 0 }, true);
      }
    }
    _v.set(t.x, t.y, t.z);
    _q.set(r.x, r.y, r.z, r.w);
    _m.compose(_v, _q, _s);
    grainMesh.setMatrixAt(i, _m);
    dirty = true;
  }
  if (dirty) grainMesh.instanceMatrix.needsUpdate = true;
  updatePublicState();
}

function countUpperUnreleased() {
  let n = 0;
  for (let i = 0; i < N; i++) {
    if (released[i]) continue;
    const yo = posCache[i * 3 + 1] * orientation;
    if (yo > 0.15) n++;
  }
  return n;
}

function countUpperUnreleasedByType(type) {
  let n = 0;
  for (let i = 0; i < N; i++) {
    if (released[i] || grainType[i] !== type) continue;
    const yo = posCache[i * 3 + 1] * orientation;
    if (yo > 0.15) n++;
  }
  return n;
}

function setCoreRotation(thetaRad) {
  displayTheta = thetaRad;
  if (!coreLayer) return;
  coreLayer.style.transform = `rotate(${THREE.MathUtils.radToDeg(thetaRad)}deg)`;
}

function updatePublicState() {
  const half = GRAINS_N / 2;
  let upperPride = 0;
  let lowerSloth = 0;
  for (let i = 0; i < N; i++) {
    const yo = posCache[i * 3 + 1] * orientation;
    if (grainType[i] === 0 && yo > 0.15) upperPride++;
    if (grainType[i] === 1 && yo < -0.15) lowerSloth++;
  }
  publicState.pride = Math.min(1, upperPride / half);
  publicState.sloth = Math.min(1, lowerSloth / half);
  publicState.flipping = !!flipPhase;
  publicState.flipDeg = THREE.MathUtils.radToDeg(displayTheta);
  const upperFlow = countUpperUnreleased();
  publicState.sourceIsPride = orientation > 0 && countUpperUnreleasedByType(0) > 6;
  publicState.sourceIsSloth = orientation < 0 && countUpperUnreleasedByType(1) > 6;
  if (!publicState.sourceIsPride && !publicState.sourceIsSloth) {
    publicState.sourceIsPride = orientation > 0 && upperFlow > 6;
    publicState.sourceIsSloth = orientation < 0 && upperFlow > 6;
  }
}

function buildStaticColliders() {
  const fixed = world.createRigidBody(RAPIER.RigidBodyDesc.fixed());
  const WBANDS = 30;
  const SEGS = 26;
  const WALL_T = 0.9;
  const q = new THREE.Quaternion();
  const basis = new THREE.Matrix4();
  const xA = new THREE.Vector3();
  const yA = new THREE.Vector3();
  const zA = new THREE.Vector3();
  for (let b = 0; b < WBANDS; b++) {
    const y0 = -H + (2 * H * b) / WBANDS;
    const y1 = -H + (2 * H * (b + 1)) / WBANDS;
    const r0 = profileR(Math.abs(y0));
    const r1 = profileR(Math.abs(y1));
    const ym = (y0 + y1) / 2;
    const rm = (r0 + r1) / 2;
    const dr = r1 - r0;
    const dy = y1 - y0;
    const L = Math.hypot(dr, dy);
    const nu = dy / L;
    const ny = -dr / L;
    const cu = rm + nu * (WALL_T / 2);
    const cy = ym + ny * (WALL_T / 2);
    const chord = (2 * Math.PI * Math.max(cu, 0.4)) / SEGS;
    for (let s = 0; s < SEGS; s++) {
      const a = (s / SEGS) * Math.PI * 2;
      const ca = Math.cos(a);
      const sa = Math.sin(a);
      yA.set((dr / L) * ca, dy / L, (dr / L) * sa);
      xA.set(-sa, 0, ca);
      zA.crossVectors(xA, yA).normalize();
      basis.makeBasis(xA, yA, zA);
      q.setFromRotationMatrix(basis);
      world.createCollider(
        RAPIER.ColliderDesc.cuboid(chord * 0.62, L / 2 + 0.12, WALL_T / 2)
          .setTranslation(cu * ca, cy, cu * sa)
          .setRotation({ x: q.x, y: q.y, z: q.z, w: q.w })
          .setFriction(0.55).setRestitution(0.02),
        fixed,
      );
    }
  }
  for (const s of [-1, 1]) {
    world.createCollider(
      RAPIER.ColliderDesc.cylinder(0.5, CAP_R + 1.2)
        .setTranslation(0, s * (H + 0.48), 0)
        .setFriction(0.55).setCollisionGroups(0xffffffff),
      fixed,
    );
  }
}

function seedPositions(count, chamber) {
  const out = [];
  const jit = () => (Math.random() - 0.5) * GRAIN_R * 0.6;
  const spacing = GRAIN_R * 1.96;
  const yMin = chamber === 'top' ? THROAT_H + GRAIN_R : -H + 1.2;
  const yMax = chamber === 'top' ? H - 1.2 : -THROAT_H - GRAIN_R;
  for (let y = yMin; y < yMax && out.length < count; y += GRAIN_R * 1.75) {
    const rMax = profileR(Math.abs(y)) - GRAIN_R - 0.15;
    if (rMax <= 0) continue;
    out.push([jit() * 0.4, y, jit() * 0.4]);
    const a0 = y * 3.7;
    for (let rr = spacing; rr <= rMax && out.length < count; rr += spacing) {
      const n = Math.max(3, Math.floor((Math.PI * 2 * rr) / spacing));
      for (let k = 0; k < n && out.length < count; k++) {
        const a = a0 + (k / n) * Math.PI * 2;
        out.push([Math.cos(a) * rr + jit(), y + jit() * 0.4, Math.sin(a) * rr + jit()]);
      }
    }
  }
  return out;
}

function applyGrainColors() {
  if (!grainMesh.instanceColor) {
    grainMesh.instanceColor = new THREE.InstancedBufferAttribute(new Float32Array(GRAINS_N * 3), 3);
  }
  const prideBase = new THREE.Color(GRAIN_COLOR_PRIDE);
  const slothBase = new THREE.Color(GRAIN_COLOR_SLOTH);
  const tmp = new THREE.Color();
  for (let i = 0; i < N; i++) {
    const base = grainType[i] === 0 ? prideBase : slothBase;
    tmp.copy(base);
    tmp.r = THREE.MathUtils.clamp(tmp.r + (Math.random() - 0.5) * 0.06, 0.58, 0.82);
    tmp.g = THREE.MathUtils.clamp(tmp.g + (Math.random() - 0.5) * 0.06, 0.34, 0.62);
    tmp.b = THREE.MathUtils.clamp(tmp.b + (Math.random() - 0.5) * 0.04, 0.78, 1.0);
    const shade = 0.84 + Math.random() * 0.16;
    tmp.r *= shade;
    tmp.g *= shade;
    tmp.b *= shade;
    grainMesh.setColorAt(i, tmp);
  }
  grainMesh.instanceColor.needsUpdate = true;
}

function buildSand() {
  bodies = [];
  const topPts = seedPositions(GRAINS_N / 2, 'top');
  const botPts = seedPositions(GRAINS_N / 2, 'bottom');
  const pts = [...topPts, ...botPts];
  N = pts.length;

  for (let i = 0; i < N; i++) {
    const [x, y, z] = pts[i];
    grainType[i] = i < GRAINS_N / 2 ? 0 : 1;
    released[i] = i >= GRAINS_N / 2 ? 1 : 0;
    const body = world.createRigidBody(
      RAPIER.RigidBodyDesc.dynamic().setTranslation(x, y, z)
        .setLinearDamping(0.3).setAngularDamping(0.8)
        .setSoftCcdPrediction(GRAIN_R * 4),
    );
    world.createCollider(
      RAPIER.ColliderDesc.ball(GRAIN_R)
        .setFriction(0.55).setRestitution(0).setDensity(1.4),
      body,
    );
    bodies.push(body);
    posCache[i * 3] = x;
    posCache[i * 3 + 1] = y;
    posCache[i * 3 + 2] = z;
  }
  grainMesh.count = N;
}


const GLASS_RIM_VERT = /* glsl */`
  varying vec3 vNormal;
  varying vec3 vView;
  varying vec3 vWorldPos;
  void main() {
    vec4 mvPosition = modelViewMatrix * vec4(position, 1.0);
    vNormal = normalize(normalMatrix * normal);
    vView = normalize(-mvPosition.xyz);
    vWorldPos = (modelMatrix * vec4(position, 1.0)).xyz;
    gl_Position = projectionMatrix * mvPosition;
  }
`;

const GLASS_SHELL_FRAG = /* glsl */`
  uniform vec3 uColor;
  uniform vec3 uColorB;
  uniform vec3 uLightDir;
  uniform float uTime;
  uniform float uIntensity;
  uniform float uFlipBoost;
  uniform float uWaistBand;
  varying vec3 vNormal;
  varying vec3 vView;
  varying vec3 vWorldPos;
  void main() {
    vec3 n = normalize(vNormal);
    vec3 v = normalize(vView);
    float ndv = max(dot(n, v), 0.0);

    // 双带 Fresnel：锐边 + 宽晕；正面 (ndv→1) 仍趋近 0，不会铺白膜
    float edgeSharp = pow(1.0 - ndv, 4.8);
    float edgeSoft  = pow(1.0 - ndv, 2.0) * 0.24;
    float edge = edgeSharp + edgeSoft;

    float flow = sin(uTime * 1.35 + vWorldPos.y * 0.55 + vWorldPos.x * 0.38) * 0.5 + 0.5;
    vec3 edgeTint = mix(uColor, uColorB, flow);

    vec3 l = normalize(uLightDir);
    vec3 h = normalize(l + v);
    float spec = pow(max(dot(n, h), 0.0), 110.0);

    // 细腰结构线：只在侧视时显现
    float waistBand = exp(-pow(vWorldPos.y / max(uWaistBand, 0.01), 2.0));
    waistBand *= pow(1.0 - ndv, 2.2) * 0.42;

    float pulse = 0.92 + 0.08 * sin(uTime * 2.0);
    float boost = uIntensity + uFlipBoost;
    float edgeA = (edge + waistBand) * boost * pulse;
    // 高光仅锁在锐边，避免中间出现灰白膜
    float specA = spec * edgeSharp * 0.58;
    float alpha = edgeA + specA;
    if (alpha < 0.005) discard;

    vec3 col = edgeTint * edgeA + mix(edgeTint, vec3(1.0), 0.55) * specA;
    gl_FragColor = vec4(col, clamp(alpha, 0.0, 0.92));
  }
`;

const GLASS_INNER_SHELL_FRAG = /* glsl */`
  uniform vec3 uColor;
  uniform float uTime;
  uniform float uIntensity;
  uniform float uFlipBoost;
  varying vec3 vNormal;
  varying vec3 vView;
  void main() {
    float ndv = max(dot(normalize(vNormal), normalize(vView)), 0.0);
    float edge = pow(1.0 - ndv, 5.8);
    float pulse = 0.94 + 0.06 * sin(uTime * 1.8);
    float alpha = edge * (uIntensity + uFlipBoost * 0.55) * pulse;
    if (alpha < 0.004) discard;
    gl_FragColor = vec4(uColor, clamp(alpha, 0.0, 0.72));
  }
`;

const GLASS_HALO_FRAG = /* glsl */`
  uniform vec3 uColor;
  uniform float uTime;
  uniform float uIntensity;
  uniform float uFlipBoost;
  uniform float uHalfH;
  varying vec3 vNormal;
  varying vec3 vView;
  varying vec3 vWorldPos;
  void main() {
    float ndv = max(dot(normalize(vNormal), normalize(vView)), 0.0);
    float edge = pow(1.0 - ndv, 2.05);
    float bulbZone = smoothstep(uHalfH * 0.08, uHalfH * 0.52, abs(vWorldPos.y));
    float pulse = 0.9 + 0.1 * sin(uTime * 1.6 + vWorldPos.y * 0.3);
    float alpha = edge * (0.5 + edge * 0.5) * (uIntensity + uFlipBoost * 0.9);
    alpha *= pulse * (0.8 + bulbZone * 0.42);
    if (alpha < 0.004) discard;
    gl_FragColor = vec4(uColor, clamp(alpha, 0.0, 0.68));
  }
`;

function buildScene() {
  renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.setClearColor(0x000000, 0);
  renderer.toneMapping = THREE.ACESFilmicToneMapping;
  renderer.toneMappingExposure = 0.96;

  scene = new THREE.Scene();
  scene.add(new THREE.HemisphereLight(0xe9d5ff, 0x5b21b6, 0.55));

  camera = new THREE.PerspectiveCamera(34, 1, 0.5, 500);

  const keyLight = new THREE.DirectionalLight(0xe9d5ff, 1.0);
  keyLight.position.set(18, 28, 22);
  scene.add(keyLight);
  const rimLight = new THREE.DirectionalLight(0xc084fc, 0.45);
  rimLight.position.set(-12, 8, -18);
  scene.add(rimLight);

  rig = new THREE.Group();
  scene.add(rig);

  const lathePts = [new THREE.Vector2(0.15, -H)];
  for (let i = 0; i <= 72; i++) {
    const y = -H + (2 * H * i) / 72;
    lathePts.push(new THREE.Vector2(profileR(Math.abs(y)) + 0.12, y));
  }
  lathePts.push(new THREE.Vector2(0.15, H));
  const glassGeo = new THREE.LatheGeometry(lathePts, 64);

  glassShellMat = new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    blending: THREE.NormalBlending,
    side: THREE.FrontSide,
    uniforms: {
      uColor: { value: new THREE.Color(RIM_GLOW_COLOR) },
      uColorB: { value: new THREE.Color(RIM_GLOW_COLOR_B) },
      uLightDir: { value: new THREE.Vector3(0.35, 0.65, 0.45) },
      uTime: { value: 0 },
      uIntensity: { value: RIM_BASE_INTENSITY },
      uFlipBoost: { value: 0 },
      uWaistBand: { value: THROAT_H * 1.6 },
      uHalfH: { value: H },
    },
    vertexShader: GLASS_RIM_VERT,
    fragmentShader: GLASS_SHELL_FRAG,
  });
  const glassShell = new THREE.Mesh(glassGeo, glassShellMat);
  glassShell.renderOrder = 3;
  rig.add(glassShell);

  glassInnerShellMat = new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    blending: THREE.NormalBlending,
    side: THREE.FrontSide,
    uniforms: {
      uColor: { value: new THREE.Color(0x9333ea) },
      uTime: { value: 0 },
      uIntensity: { value: INNER_RIM_INTENSITY },
      uFlipBoost: { value: 0 },
    },
    vertexShader: GLASS_RIM_VERT,
    fragmentShader: GLASS_INNER_SHELL_FRAG,
  });
  const glassInnerShell = new THREE.Mesh(glassGeo, glassInnerShellMat);
  glassInnerShell.scale.setScalar(0.987);
  glassInnerShell.renderOrder = 3;
  rig.add(glassInnerShell);

  glassHaloMat = new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    blending: THREE.AdditiveBlending,
    side: THREE.FrontSide,
    uniforms: {
      uColor: { value: new THREE.Color(0xc084fc) },
      uTime: { value: 0 },
      uIntensity: { value: HALO_INTENSITY },
      uFlipBoost: { value: 0 },
      uHalfH: { value: H },
    },
    vertexShader: GLASS_RIM_VERT,
    fragmentShader: GLASS_HALO_FRAG,
  });
  const glassHalo = new THREE.Mesh(glassGeo, glassHaloMat);
  glassHalo.scale.setScalar(1.006);
  glassHalo.renderOrder = 3;
  rig.add(glassHalo);

  const grainGeo = new THREE.IcosahedronGeometry(GRAIN_R, 1);
  const grainEmissive = new THREE.Color(GRAIN_EMISSIVE).multiplyScalar(GRAIN_EMISSIVE_STRENGTH);
  const grainMat = new THREE.MeshLambertMaterial({
    color: GRAIN_COLOR,
    flatShading: true,
    vertexColors: true,
    emissive: grainEmissive,
    emissiveIntensity: GRAIN_EMISSIVE_INTENSITY,
  });
  grainMesh = new THREE.InstancedMesh(grainGeo, grainMat, GRAINS_N);
  grainMesh.instanceColor = new THREE.InstancedBufferAttribute(new Float32Array(GRAINS_N * 3), 3);
  grainMesh.renderOrder = 1;
  grainMesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
  grainMesh.frustumCulled = false;
  rig.add(grainMesh);
}

function fitCamera(w, h) {
  const halfH = H + 0.35;
  const halfW = BULB_R + 1.4;
  const targetDiameterRatio = HEPTAGON_RADIUS_RATIO * 2 * HOURGLASS_VIEW_SCALE;
  const fovRad = (camera.fov * Math.PI) / 180;
  const tanHalfFov = Math.tan(fovRad / 2);
  const distV = halfH / (targetDiameterRatio * tanHalfFov);
  const distH = halfW / (targetDiameterRatio * tanHalfFov * camera.aspect);
  camera.position.set(0, 0, Math.max(distV, distH));
  camera.lookAt(0, 0, 0);
}

function resize() {
  if (!canvas || !renderer || !camera) return;
  const rect = canvas.parentElement.getBoundingClientRect();
  const w = Math.max(1, rect.width);
  const h = Math.max(1, rect.height);
  renderer.setSize(w, h, false);
  camera.aspect = w / h;
  camera.updateProjectionMatrix();
  fitCamera(w, h);
}

function beginSettle() {
  state = 'settling';
  settle = { steps: 0 };
}

function settleTick(gap) {
  const n = Math.max(8, Math.min(120, Math.round(gap / DT) + 4));
  for (let k = 0; k < n; k++) {
    world.step();
    settle.steps++;
    if (settle.steps % 7 === 0) { postStep(); freezePass(); }
  }
  postStep();
  freezePass();
  if (settle.steps < 200) return;
  let maxV = 0;
  for (let i = 0; i < N; i++) {
    if (frozen[i] || bodies[i].isSleeping()) continue;
    const v = bodies[i].linvel();
    maxV = Math.max(maxV, v.x * v.x + v.y * v.y + v.z * v.z);
  }
  if (maxV < 0.8 || settle.steps > 700) {
    settle = null;
    enterReady(true);
  }
}

function enterReady(autoRun = false) {
  state = 'ready';
  releasedCount = 0;
  elapsedMs = 0;
  topStart = countUpperUnreleased();
  effDuration = Math.max(8, BASE_DRAIN_SEC * (topStart / Math.max(1, GRAINS_N / 2)));
  postStep(true);
  freezePass();
  ready = true;
  if (autoRun && topStart > 0) beginRun();
}

function beginRun() {
  topStart = countUpperUnreleased();
  if (topStart <= 0) return;
  effDuration = Math.max(8, BASE_DRAIN_SEC * (topStart / Math.max(1, GRAINS_N / 2)));
  startStamp = performance.now();
  releasedCount = 0;
  autoFlipAt = 0;
  state = 'running';
}

function finishRun() {
  state = 'done';
  autoFlipAt = performance.now() + PAUSE_BEFORE_FLIP_MS;
}

function startFlip() {
  if (flipPhase || state === 'settling' || state === 'boot') return;
  flipPhase = 'turn';
  flipT0 = performance.now();
  autoFlipAt = 0;
  coreLayer?.classList.add('is-flipping');
  hourglassLayer?.classList.add('is-flipping');
  unfreezeAll();
  for (let i = 0; i < N; i++) bodies[i].wakeUp();
  if (state === 'running' || state === 'done') state = 'ready';
}

function flipTick(now) {
  if (flipPhase === 'turn') {
    const t = Math.min(1, (now - flipT0) / FLIP_MS);
    const e = t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
    const theta = thetaBase + e * Math.PI;
    setCoreRotation(theta);
    setGravity(-G * Math.sin(theta), -G * Math.cos(theta));
    if ((now - flipT0) % 200 < 34) {
      for (let i = 0; i < N; i++) bodies[i].wakeUp();
    }
    if (t >= 1) {
      thetaBase = (thetaBase + Math.PI) % (2 * Math.PI);
      setCoreRotation(thetaBase);
      orientation = Math.abs(thetaBase) < 0.1 ? 1 : -1;
      setGravity(0, -G * orientation);
      flipPhase = 'settle';
      flipSettleT0 = now;
    }
  } else if (flipPhase === 'settle') {
    if (now - flipSettleT0 < FLIP_SETTLE_MS) return;
    flipPhase = null;
    coreLayer?.classList.remove('is-flipping');
    hourglassLayer?.classList.remove('is-flipping');
    for (let i = 0; i < N; i++) {
      const yo = posCache[i * 3 + 1] * orientation;
      released[i] = yo > 0.2 ? 0 : 1;
    }
    topStart = countUpperUnreleased();
    releasedCount = 0;
    if (topStart <= 0) {
      state = 'ready';
      return;
    }
    effDuration = Math.max(8, BASE_DRAIN_SEC * (topStart / Math.max(1, GRAINS_N / 2)));
    beginRun();
  }
}

function loop(now) {
  requestAnimationFrame(loop);
  const gap = lastT ? (now - lastT) / 1000 : 0.016;
  const dtReal = Math.min(0.05, gap);
  lastT = now;

  if (state === 'settling' && settle) {
    settleTick(gap);
  } else if (state !== 'paused' && state !== 'boot') {
    if (flipPhase) flipTick(now);
    acc += dtReal;
    let steps = 0;
    while (acc >= DT && steps < MAX_STEPS) {
      world.step();
      acc -= DT;
      steps++;
    }
    if (acc > DT) acc = 0;
    postStep();
    if (!flipPhase) {
      freezePass();
      if (state === 'running') {
        meter(now);
        if (elapsedMs / 1000 >= effDuration || countUpperUnreleased() <= 2) {
          meter(now, true);
          finishRun();
        }
      } else if (state === 'done') {
        meter(now, true);
        if (autoFlipAt && now >= autoFlipAt && countUpperUnreleased() <= 2) {
          startFlip();
        }
      }
    }
  }

  const tSec = now * 0.001;
  const targetBoost = flipPhase ? RIM_FLIP_BOOST : 0;
  flipGlowBoost += (targetBoost - flipGlowBoost) * 0.07;
  if (glassHaloMat) {
    glassHaloMat.uniforms.uTime.value = tSec;
    glassHaloMat.uniforms.uFlipBoost.value = flipGlowBoost;
  }
  if (glassShellMat) {
    glassShellMat.uniforms.uTime.value = tSec;
    glassShellMat.uniforms.uFlipBoost.value = flipGlowBoost;
  }
  if (glassInnerShellMat) {
    glassInnerShellMat.uniforms.uTime.value = tSec;
    glassInnerShellMat.uniforms.uFlipBoost.value = flipGlowBoost;
  }

  renderer.render(scene, camera);
}

export function getState() {
  return publicState;
}

export function canFlip() {
  return !flipPhase && state !== 'settling' && state !== 'boot';
}

export function flipHourglass() {
  if (!canFlip()) return false;
  autoFlipAt = 0;
  startFlip();
  return true;
}

export async function initHourglass(el, coreEl) {
  canvas = el;
  coreLayer = coreEl ?? document.getElementById('coreLayer');
  hourglassLayer = document.getElementById('hourglassLayer');
  hourglassLayer?.classList.add('is-glowing');
  buildScene();
  resize();
  setCoreRotation(thetaBase);
  window.addEventListener('resize', resize);

  await RAPIER.init();
  world = new RAPIER.World({ x: 0, y: -G, z: 0 });
  world.timestep = DT;
  buildStaticColliders();
  buildSand();
  applyGrainColors();
  postStep(true);
  beginSettle();
  requestAnimationFrame(loop);
  return publicState;
}

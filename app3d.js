"use strict";
/* ============================================================
   3D mode: Three.js scene + D3Q19 lattice-Boltzmann CFD.
   The 3D solver is PRECOMPUTED (single-threaded JS cannot run
   ~110k-cell D3Q19 in real time), then a recorded tracer-particle
   animation plays on a loop. The canvas is locked during compute.
   ============================================================ */
(function () {
const $ = id => document.getElementById(id);
const toast = msg => (window.toast ? window.toast(msg) : console.log(msg));

/* ---------- module state ---------- */
let inited = false;
let renderer, scene, camera, cv3, wrap3;
let camPos, camQ, camHomePos, camHomeQ;
let objects = [];                 // THREE.Mesh with userData.kind
let selectedObj = null;
let category = 'shapes';          // 'shapes' | 'terrain'
let terra = null;                 // {n, hg, extentM, hRange, mesh, name}
let shapesGroup, terrainGroup, windArrow;

/* compute / playback */
let computing = false, cancelReq = false;
let frames = [], playT = 0, playing = false;
let pointsObj = null, pointsGeo = null;
const P = 3000;                   // tracer particles
let ppos = null, pspd = null;     // particle state (lattice units)

/* ---------- free-drawing domain (feet) ---------- */
const DX = 36, DY = 16, DZ = 24, CELL = 0.5;   // 72 x 32 x 48 lattice

/* ---------- D3Q19 ---------- */
const CQ = [[0,0,0],
  [1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1],
  [1,1,0],[-1,-1,0],[1,-1,0],[-1,1,0],
  [1,0,1],[-1,0,-1],[1,0,-1],[-1,0,1],
  [0,1,1],[0,-1,-1],[0,1,-1],[0,-1,1]];
const WQ = [1/3, 1/18,1/18,1/18,1/18,1/18,1/18,
  1/36,1/36,1/36,1/36, 1/36,1/36,1/36,1/36, 1/36,1/36,1/36,1/36];
const OPPQ = [0,2,1,4,3,6,5,8,7,10,9,12,11,14,13,16,15,18,17];
const TAU3 = 0.56, OM3 = 1/TAU3;
let LX = 0, LY = 0, LZ = 0, N3 = 0;
let f3 = [], g3 = [], solid3 = null;
let VX = null, VY = null, VZ = null;
let OFF = null;                   // per-direction index offsets
let sceneScale = 1, sceneOffX = 0, sceneOffZ = 0;   // lattice -> scene units

/* wind (3D controls) */
const mph3 = () => parseFloat($('spd3').value);
const u03 = () => 0.03 + (mph3()/30) * 0.07;
function windVec3() {
  const a = parseFloat($('dir3').value) * Math.PI/180, u = u03();
  return [u*Math.cos(a), 0, u*Math.sin(a)];
}

/* color LUT (blue -> red by speed) */
const LUT3 = [];
for (let i = 0; i < 32; i++) {
  const t = i/31, h = 225*(1-t)/360;
  const c = new (function(){ this.r=0;this.g=0;this.b=0; })();
  // hsl to rgb (s=0.85, l=0.45+0.15t)
  const s = 0.85, l = 0.45 + 0.15*t;
  const a2 = s*Math.min(l,1-l);
  const f2 = n => { const k=(n+h*12)%12; return l - a2*Math.max(-1,Math.min(k-3,9-k,1)); };
  c.r = f2(0); c.g = f2(8); c.b = f2(4);
  LUT3.push(c);
}
const lut3 = t => LUT3[Math.max(0, Math.min(31, (t*31)|0))];

/* ============================================================
   Init & render loop
   ============================================================ */
window.init3D = function () {
  if (inited) { onResize(); return; }
  if (typeof THREE === 'undefined') { toast('Three.js failed to load — check your connection.'); return; }
  inited = true;
  cv3 = $('cv3d'); wrap3 = $('wrap3d');
  renderer = new THREE.WebGLRenderer({canvas: cv3, antialias: true});
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  scene = new THREE.Scene();
  scene.background = new THREE.Color(0x0a0d12);
  camera = new THREE.PerspectiveCamera(55, 1, 0.1, 100000);
  camPos = new THREE.Vector3(); camQ = new THREE.Quaternion();
  camHomePos = new THREE.Vector3(); camHomeQ = new THREE.Quaternion();

  scene.add(new THREE.HemisphereLight(0x8899bb, 0x223344, 0.9));
  const sun = new THREE.DirectionalLight(0xffeedd, 0.9);
  sun.position.set(60, 100, 40);
  scene.add(sun);

  shapesGroup = new THREE.Group();
  terrainGroup = new THREE.Group();
  scene.add(shapesGroup, terrainGroup);
  buildShapesEnv();
  terrainGroup.visible = false;

  windArrow = new THREE.ArrowHelper(new THREE.Vector3(1,0,0), new THREE.Vector3(-DX/2, DY*0.9, -DZ/2), 6, 0x4da3ff, 2, 1.2);
  scene.add(windArrow);

  bindUI();
  camGoHome(true);
  onResize();
  new ResizeObserver(onResize).observe(wrap3);
  requestAnimationFrame(loop3);
};

function onResize() {
  if (!renderer) return;
  const w = Math.max(50, wrap3.clientWidth), h = Math.max(50, wrap3.clientHeight);
  renderer.setSize(w, h, false);
  camera.aspect = w/h;
  camera.updateProjectionMatrix();
}

function loop3(now) {
  requestAnimationFrame(loop3);
  if (!document.body.classList.contains('mode-3d')) return;
  if (playing && frames.length) {
    playT += 24/60;                            // ~24 recorded fps
    applyFrame(frames[(playT|0) % frames.length]);
  }
  camera.position.copy(camPos);
  camera.quaternion.copy(camQ);
  renderer.render(scene, camera);
}

/* ============================================================
   Camera: pitch / roll / yaw / move
   ============================================================ */
const _q = () => new THREE.Quaternion();
function camYaw(a)   { camQ.premultiply(_q().setFromAxisAngle(new THREE.Vector3(0,1,0), a)); }
function camPitch(a) { camQ.multiply(_q().setFromAxisAngle(new THREE.Vector3(1,0,0), a)); }
function camRoll(a)  { camQ.multiply(_q().setFromAxisAngle(new THREE.Vector3(0,0,1), a)); }
function camMove(dx, dy, dz) {
  camPos.add(new THREE.Vector3(dx, dy, dz).applyQuaternion(camQ));
}
function moveStep() { return category === 'terrain' && terra ? terra.extentM/30 : 2.5; }
function camGoHome(recompute) {
  if (recompute) {
    if (category === 'terrain' && terra) {
      const e = terra.extentM;
      camera.position.set(e*0.65, terra.hRange + e*0.45, e*0.85);
      camera.lookAt(0, terra.hRange*0.3, 0);
    } else {
      camera.position.set(DX*0.85, DY*1.3, DZ*1.7);
      camera.lookAt(0, DY*0.25, 0);
    }
    camHomePos.copy(camera.position);
    camHomeQ.copy(camera.quaternion);
  }
  camPos.copy(camHomePos);
  camQ.copy(camHomeQ);
}

/* ============================================================
   Scene: free-drawing environment & objects
   ============================================================ */
function buildShapesEnv() {
  const grid = new THREE.GridHelper(Math.max(DX, DZ), Math.max(DX, DZ)/2, 0x2a3242, 0x1d2431);
  shapesGroup.add(grid);
  const box = new THREE.LineSegments(
    new THREE.EdgesGeometry(new THREE.BoxGeometry(DX, DY, DZ)),
    new THREE.LineBasicMaterial({color: 0x2a3242})
  );
  box.position.y = DY/2;
  shapesGroup.add(box);
  const ground = new THREE.Mesh(new THREE.PlaneGeometry(400, 400), new THREE.MeshBasicMaterial({visible: false}));
  ground.rotation.x = -Math.PI/2;
  ground.userData.isGround = true;
  shapesGroup.add(ground);
}

const OBJ_DEF = {
  box:    { make: () => new THREE.BoxGeometry(4, 4, 4),           test: p => Math.abs(p.x)<=2 && Math.abs(p.y)<=2 && Math.abs(p.z)<=2 },
  sphere: { make: () => new THREE.SphereGeometry(2, 24, 16),      test: p => p.lengthSq() <= 4 },
  cyl:    { make: () => new THREE.CylinderGeometry(1.5, 1.5, 5, 24), test: p => Math.abs(p.y)<=2.5 && (p.x*p.x + p.z*p.z) <= 2.25 }
};
function addObj3(kind) {
  if (computing) return;
  const def = OBJ_DEF[kind];
  const mesh = new THREE.Mesh(def.make(), new THREE.MeshStandardMaterial({color: 0x3a465c, roughness: 0.7, metalness: 0.1}));
  mesh.userData.kind = kind;
  mesh.position.set(Math.random()*8-4, kind === 'cyl' ? 2.5 : 2, Math.random()*6-3);
  shapesGroup.add(mesh);
  objects.push(mesh);
  select3(mesh);
  invalidate();
}
function select3(m) {
  if (selectedObj) selectedObj.material.emissive.setHex(0);
  selectedObj = m;
  if (m) {
    m.material.emissive.setHex(0x1a4a7a);
    $('xformSec').style.display = '';
    syncSliders();
  } else $('xformSec').style.display = 'none';
}
function syncSliders() {
  const m = selectedObj; if (!m) return;
  const d = THREE.MathUtils.radToDeg;
  $('t3px').value = m.position.x; $('t3py').value = m.position.y; $('t3pz').value = m.position.z;
  $('t3rx').value = d(m.rotation.x); $('t3ry').value = d(m.rotation.y); $('t3rz').value = d(m.rotation.z);
  $('t3sx').value = m.scale.x; $('t3sy').value = m.scale.y; $('t3sz').value = m.scale.z;
}
function applySliders() {
  const m = selectedObj; if (!m || computing) return;
  const r = THREE.MathUtils.degToRad;
  m.position.set(+$('t3px').value, +$('t3py').value, +$('t3pz').value);
  m.rotation.set(r(+$('t3rx').value), r(+$('t3ry').value), r(+$('t3rz').value));
  m.scale.set(+$('t3sx').value, +$('t3sy').value, +$('t3sz').value);
  invalidate();
}

/* ============================================================
   Terrain: geocode (Nominatim) + elevation (terrarium tiles)
   ============================================================ */
async function loadTerrain(name) {
  const st = $('terrStatus');
  try {
    st.textContent = 'Geocoding "' + name + '"…';
    const gr = await fetch('https://nominatim.openstreetmap.org/search?format=json&limit=1&q=' + encodeURIComponent(name));
    const gj = await gr.json();
    if (!gj.length) { st.textContent = 'Location not found. Try another name.'; return; }
    const lat = +gj[0].lat, lon = +gj[0].lon;
    st.textContent = 'Fetching elevation tiles…';
    const z = 14;
    const n2 = Math.pow(2, z);
    const xt = (lon + 180)/360 * n2;
    const yt = (1 - Math.log(Math.tan(lat*Math.PI/180) + 1/Math.cos(lat*Math.PI/180))/Math.PI)/2 * n2;
    const x0 = Math.max(0, Math.floor(xt - 1)), y0 = Math.max(0, Math.floor(yt - 1));
    const cnv = document.createElement('canvas'); cnv.width = 512; cnv.height = 512;
    const cctx = cnv.getContext('2d');
    await Promise.all([0,1,2,3].map(i => new Promise((res, rej) => {
      const img = new Image();
      img.crossOrigin = 'anonymous';
      img.onload = () => { cctx.drawImage(img, (i%2)*256, (i>>1)*256); res(); };
      img.onerror = () => rej(new Error('tile fetch failed'));
      img.src = `https://s3.amazonaws.com/elevation-tiles-prod/terrarium/${z}/${x0 + i%2}/${y0 + (i>>1)}.png`;
    })));
    const px = cctx.getImageData(0, 0, 512, 512).data;
    const elevAt = (ix, iy) => {
      const o = (Math.min(511, iy)*512 + Math.min(511, ix))*4;
      return (px[o]*256 + px[o+1] + px[o+2]/256) - 32768;
    };
    const n = 65;
    const hg = new Float32Array(n*n);
    let minE = 1e9, maxE = -1e9;
    for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) {
      let e = elevAt(Math.round(i/(n-1)*511), Math.round(j/(n-1)*511));
      if (e < 0) e = 0;                       // sea level floor
      hg[j*n+i] = e;
      minE = Math.min(minE, e); maxE = Math.max(maxE, e);
    }
    for (let i = 0; i < n*n; i++) hg[i] -= minE;
    const spanM = 40075016.686 * Math.cos(lat*Math.PI/180) / n2;
    const extentM = spanM * 2;
    terra = { n, hg, extentM, hRange: Math.max(10, maxE - minE), name: gj[0].display_name.split(',')[0] };
    buildTerrainMesh();
    camGoHome(true);
    invalidate();
    st.textContent = `${terra.name} · ${(extentM/1000).toFixed(1)} km × ${(extentM/1000).toFixed(1)} km · relief ${Math.round(terra.hRange)} m`;
  } catch (err) {
    st.textContent = 'Failed to load terrain (' + err.message + '). Check connection and try again.';
  }
}
function buildTerrainMesh() {
  while (terrainGroup.children.length) terrainGroup.remove(terrainGroup.children[0]);
  const { n, hg, extentM, hRange } = terra;
  const pos = new Float32Array(n*n*3), col = new Float32Array(n*n*3);
  for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) {
    const k = j*n+i, h = hg[k];
    pos[k*3]   = (i/(n-1) - 0.5)*extentM;
    pos[k*3+1] = h;
    pos[k*3+2] = (j/(n-1) - 0.5)*extentM;
    const t = h/hRange;
    let r, g2, b;
    if (h < 0.5) { r=0.10; g2=0.30; b=0.55; }                       // water/beach
    else if (t < 0.5) { const u=t*2;   r=0.16+0.24*u; g2=0.38-0.05*u; b=0.16+0.06*u; }
    else              { const u=(t-0.5)*2; r=0.40+0.5*u; g2=0.33+0.55*u; b=0.22+0.7*u; }
    col[k*3]=r; col[k*3+1]=g2; col[k*3+2]=b;
  }
  const idx = [];
  for (let j = 0; j < n-1; j++) for (let i = 0; i < n-1; i++) {
    const a=j*n+i, b=a+1, c=a+n, d=c+1;
    idx.push(a,c,b, b,c,d);
  }
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(pos, 3));
  geo.setAttribute('color', new THREE.BufferAttribute(col, 3));
  geo.setIndex(idx);
  geo.computeVertexNormals();
  terra.mesh = new THREE.Mesh(geo, new THREE.MeshLambertMaterial({vertexColors: true, side: THREE.DoubleSide}));
  terrainGroup.add(terra.mesh);
}
function terrainHeight(wx, wz) {               // world meters -> height above base
  const { n, hg, extentM } = terra;
  let gx = (wx/extentM + 0.5)*(n-1), gz = (wz/extentM + 0.5)*(n-1);
  gx = Math.max(0, Math.min(n-1.001, gx)); gz = Math.max(0, Math.min(n-1.001, gz));
  const i = gx|0, j = gz|0, fx = gx-i, fz = gz-j;
  return hg[j*n+i]*(1-fx)*(1-fz) + hg[j*n+i+1]*fx*(1-fz) + hg[(j+1)*n+i]*(1-fx)*fz + hg[(j+1)*n+i+1]*fx*fz;
}

/* ============================================================
   D3Q19 LBM
   ============================================================ */
function alloc3() {
  N3 = LX*LY*LZ;
  f3 = []; g3 = [];
  for (let k = 0; k < 19; k++) { f3.push(new Float32Array(N3)); g3.push(new Float32Array(N3)); }
  solid3 = new Uint8Array(N3);
  VX = new Float32Array(N3); VY = new Float32Array(N3); VZ = new Float32Array(N3);
  OFF = CQ.map(c => c[0] + LX*(c[1] + LY*c[2]));
}
function setEq3(arr, i, rho, ux, uy, uz) {
  const usq = 1.5*(ux*ux + uy*uy + uz*uz);
  for (let k = 0; k < 19; k++) {
    const eu = 3*(CQ[k][0]*ux + CQ[k][1]*uy + CQ[k][2]*uz);
    arr[k][i] = WQ[k]*rho*(1 + eu + 0.5*eu*eu - usq);
  }
}
function buildSolid() {
  solid3.fill(0);
  if (category === 'terrain' && terra) {
    const cellM = terra.extentM/LX;
    for (let z = 0; z < LZ; z++) for (let x = 0; x < LX; x++) {
      const h = terrainHeight((x+0.5-LX/2)*cellM, (z+0.5-LZ/2)*cellM);
      const top = Math.min(LY, Math.ceil(h/cellM));
      for (let y = 0; y <= Math.max(0, top-1); y++) solid3[x + LX*(y + LY*z)] = 1;
      solid3[x + LX*(0 + LY*z)] = 1;
    }
  } else {
    for (let z = 0; z < LZ; z++) for (let x = 0; x < LX; x++) solid3[x + LX*(0 + LY*z)] = 1;  // ground
    const v = new THREE.Vector3();
    const invs = objects.map(m => {
      m.updateMatrixWorld(true);
      return { inv: new THREE.Matrix4().copy(m.matrixWorld).invert(), test: OBJ_DEF[m.userData.kind].test };
    });
    for (let z = 1; z < LZ-1; z++) for (let y = 1; y < LY-1; y++) for (let x = 1; x < LX-1; x++) {
      const wx = (x+0.5)*CELL - DX/2, wy = (y+0.5)*CELL, wz = (z+0.5)*CELL - DZ/2;
      for (const o of invs) {
        v.set(wx, wy, wz).applyMatrix4(o.inv);
        if (o.test(v)) { solid3[x + LX*(y + LY*z)] = 1; break; }
      }
    }
  }
}
function initFluid3() {
  const [ux, uy, uz] = windVec3();
  for (let i = 0; i < N3; i++) { setEq3(f3, i, 1, ux, uy, uz); VX[i] = ux; VY[i] = uy; VZ[i] = uz; }
}
function lbm3Step() {
  const [u0x, u0y, u0z] = windVec3();
  /* stream (pull) with bounce-back */
  for (let z = 1; z < LZ-1; z++) {
    for (let y = 1; y < LY-1; y++) {
      const row = LX*(y + LY*z);
      for (let x = 1; x < LX-1; x++) {
        const i = row + x;
        if (solid3[i]) continue;
        for (let k = 0; k < 19; k++) {
          const si = i - OFF[k];
          g3[k][i] = solid3[si] ? f3[OPPQ[k]][i] : f3[k][si];
        }
      }
    }
  }
  /* collide (BGK) */
  for (let z = 1; z < LZ-1; z++) {
    for (let y = 1; y < LY-1; y++) {
      const row = LX*(y + LY*z);
      for (let x = 1; x < LX-1; x++) {
        const i = row + x;
        if (solid3[i]) { VX[i]=0; VY[i]=0; VZ[i]=0; continue; }
        let rho = 0, mx = 0, my = 0, mz = 0;
        for (let k = 0; k < 19; k++) {
          const v = g3[k][i];
          rho += v; mx += CQ[k][0]*v; my += CQ[k][1]*v; mz += CQ[k][2]*v;
        }
        if (rho <= 0 || !isFinite(rho)) { setEq3(g3, i, 1, u0x, u0y, u0z); rho = 1; mx = u0x; my = u0y; mz = u0z; }
        let ux = mx/rho, uy = my/rho, uz = mz/rho;
        const sp = Math.sqrt(ux*ux + uy*uy + uz*uz);
        if (sp > 0.24) { const q = 0.24/sp; ux*=q; uy*=q; uz*=q; }
        VX[i]=ux; VY[i]=uy; VZ[i]=uz;
        const usq = 1.5*(ux*ux + uy*uy + uz*uz);
        for (let k = 0; k < 19; k++) {
          const eu = 3*(CQ[k][0]*ux + CQ[k][1]*uy + CQ[k][2]*uz);
          const feq = WQ[k]*rho*(1 + eu + 0.5*eu*eu - usq);
          g3[k][i] += OM3*(feq - g3[k][i]);
        }
      }
    }
  }
  /* boundary faces: equilibrium free-stream (x/z sides + top) */
  for (let z = 0; z < LZ; z++) for (let y = 0; y < LY; y++) {
    const a = 0 + LX*(y + LY*z), b = (LX-1) + LX*(y + LY*z);
    if (!solid3[a]) { setEq3(g3, a, 1, u0x, u0y, u0z); VX[a]=u0x; VY[a]=u0y; VZ[a]=u0z; }
    if (!solid3[b]) { setEq3(g3, b, 1, u0x, u0y, u0z); VX[b]=u0x; VY[b]=u0y; VZ[b]=u0z; }
  }
  for (let x = 0; x < LX; x++) for (let y = 0; y < LY; y++) {
    const a = x + LX*(y + 0), b = x + LX*(y + LY*(LZ-1));
    if (!solid3[a]) { setEq3(g3, a, 1, u0x, u0y, u0z); VX[a]=u0x; VY[a]=u0y; VZ[a]=u0z; }
    if (!solid3[b]) { setEq3(g3, b, 1, u0x, u0y, u0z); VX[b]=u0x; VY[b]=u0y; VZ[b]=u0z; }
  }
  for (let x = 0; x < LX; x++) for (let z = 0; z < LZ; z++) {
    const a = x + LX*((LY-1) + LY*z);
    if (!solid3[a]) { setEq3(g3, a, 1, u0x, u0y, u0z); VX[a]=u0x; VY[a]=u0y; VZ[a]=u0z; }
  }
  const t = f3; f3 = g3; g3 = t;
}
function sampleV3(x, y, z, out) {
  x = Math.max(0, Math.min(LX-1.001, x-0.5)); y = Math.max(0, Math.min(LY-1.001, y-0.5)); z = Math.max(0, Math.min(LZ-1.001, z-0.5));
  const i0=x|0, j0=y|0, k0=z|0, fx=x-i0, fy=y-j0, fz=z-k0;
  let vx=0, vy=0, vz=0;
  for (let dz = 0; dz <= 1; dz++) for (let dy = 0; dy <= 1; dy++) for (let dx = 0; dx <= 1; dx++) {
    const w = (dx?fx:1-fx)*(dy?fy:1-fy)*(dz?fz:1-fz);
    const i = (i0+dx) + LX*((j0+dy) + LY*(k0+dz));
    vx += VX[i]*w; vy += VY[i]*w; vz += VZ[i]*w;
  }
  out[0]=vx; out[1]=vy; out[2]=vz;
}

/* ============================================================
   Tracer particles & recorded animation
   ============================================================ */
function seedParticle(i) {
  const [ux,,uz] = windVec3();
  if (Math.abs(ux) >= Math.abs(uz)) {
    ppos[i*3]   = ux > 0 ? 1.5 + Math.random()*2 : LX - 3.5 + Math.random()*2;
    ppos[i*3+1] = 1 + Math.random()*(LY-3);
    ppos[i*3+2] = 1 + Math.random()*(LZ-3);
  } else {
    ppos[i*3]   = 1 + Math.random()*(LX-3);
    ppos[i*3+1] = 1 + Math.random()*(LY-3);
    ppos[i*3+2] = uz > 0 ? 1.5 + Math.random()*2 : LZ - 3.5 + Math.random()*2;
  }
}
function initParticles() {
  ppos = new Float32Array(P*3); pspd = new Float32Array(P);
  for (let i = 0; i < P; i++) {
    if (Math.random() < 0.35) {               // some seeded mid-domain for instant structure
      ppos[i*3] = 1 + Math.random()*(LX-3);
      ppos[i*3+1] = 1 + Math.random()*(LY-3);
      ppos[i*3+2] = 1 + Math.random()*(LZ-3);
    } else seedParticle(i);
  }
}
function advect() {
  const v = [0,0,0];
  const k = 0.9/u03();
  for (let i = 0; i < P; i++) {
    let x = ppos[i*3], y = ppos[i*3+1], z = ppos[i*3+2];
    sampleV3(x, y, z, v);
    x += v[0]*k; y += v[1]*k; z += v[2]*k;
    const ii = (x|0) + LX*((y|0) + LY*(z|0));
    if (x < 1 || x > LX-2 || y < 1 || y > LY-2 || z < 1 || z > LZ-2 || solid3[ii]) { seedParticle(i); pspd[i] = 1; continue; }
    ppos[i*3]=x; ppos[i*3+1]=y; ppos[i*3+2]=z;
    pspd[i] = Math.sqrt(v[0]*v[0]+v[1]*v[1]+v[2]*v[2]) / u03();
  }
}
function recordFrame() {
  const fr = new Float32Array(P*4);
  for (let i = 0; i < P; i++) {
    fr[i*4]   = ppos[i*3]  *sceneScale + sceneOffX;
    fr[i*4+1] = ppos[i*3+1]*sceneScale;
    fr[i*4+2] = ppos[i*3+2]*sceneScale + sceneOffZ;
    fr[i*4+3] = pspd[i];
  }
  frames.push(fr);
  applyFrame(fr);                              // live preview while computing
}
function ensurePoints() {
  if (pointsObj) { scene.remove(pointsObj); pointsGeo.dispose(); pointsObj.material.dispose(); }
  pointsGeo = new THREE.BufferGeometry();
  pointsGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(P*3), 3));
  pointsGeo.setAttribute('color', new THREE.BufferAttribute(new Float32Array(P*3), 3));
  const size = category === 'terrain' && terra ? terra.extentM/LX*0.9 : 0.3;
  pointsObj = new THREE.Points(pointsGeo, new THREE.PointsMaterial({size, vertexColors: true, transparent: true, opacity: 0.95}));
  scene.add(pointsObj);
}
function applyFrame(fr) {
  if (!pointsGeo) return;
  const pa = pointsGeo.attributes.position.array, ca = pointsGeo.attributes.color.array;
  for (let i = 0; i < P; i++) {
    pa[i*3] = fr[i*4]; pa[i*3+1] = fr[i*4+1]; pa[i*3+2] = fr[i*4+2];
    const c = lut3(Math.min(1, fr[i*4+3]/1.6));
    ca[i*3] = c.r; ca[i*3+1] = c.g; ca[i*3+2] = c.b;
  }
  pointsGeo.attributes.position.needsUpdate = true;
  pointsGeo.attributes.color.needsUpdate = true;
}

/* ============================================================
   Simulate: precompute with progress + locked canvas
   ============================================================ */
function simulate3() {
  if (computing) return;
  if (category === 'terrain' && !terra) { toast('Load a terrain location first.'); return; }
  invalidate();
  /* lattice setup */
  if (category === 'terrain') {
    LX = 64; LZ = 64;
    const cellM = terra.extentM/LX;
    LY = Math.max(16, Math.min(32, Math.ceil((terra.hRange*1.4 + 250)/cellM)));
    sceneScale = cellM; sceneOffX = -terra.extentM/2; sceneOffZ = -terra.extentM/2;
  } else {
    LX = 72; LY = 32; LZ = 48;
    sceneScale = CELL; sceneOffX = -DX/2; sceneOffZ = -DZ/2;
  }
  alloc3();
  buildSolid();
  initFluid3();
  initParticles();
  ensurePoints();
  frames = []; playing = false; playT = 0;
  $('st3grid').textContent = `${LX}×${LY}×${LZ} (${Math.round(N3/1000)}k cells)`;
  const total = category === 'terrain' ? 360 : 440;
  const SAMPLE = 4;
  let step = 0, msSum = 0, msN = 0, verdictDone = false;
  computing = true; cancelReq = false;
  lock(true);
  $('st3state').textContent = 'computing';
  const chunk = () => {
    if (cancelReq) { finish(true); return; }
    const budget = performance.now() + 30;
    while (performance.now() < budget && step < total) {
      const t0 = performance.now();
      lbm3Step();
      advect();
      msSum += performance.now() - t0; msN++;
      if (step % SAMPLE === 0) recordFrame();
      step++;
    }
    const msStep = msSum/msN;
    if (!verdictDone && msN >= 12) {
      verdictDone = true;
      $('st3ms').textContent = msStep.toFixed(1);
      $('st3rt').textContent = msStep < 3 ? 'yes (borderline)' : 'no → precompute';
    }
    const remain = (total - step)*msStep/1000;
    $('pfill').style.width = (step/total*100).toFixed(1) + '%';
    $('ovEta').textContent = `step ${step} / ${total} · ${msStep.toFixed(1)} ms/step · ~${Math.max(0, remain).toFixed(0)}s remaining`;
    if (step < total) requestAnimationFrame(chunk);
    else finish(false);
  };
  const finish = (cancelled) => {
    computing = false;
    lock(false);
    if (cancelled && frames.length < 10) {
      frames = []; $('st3state').textContent = 'cancelled';
      if (pointsObj) pointsObj.visible = false;
      return;
    }
    playing = true; playT = 0;
    $('st3state').textContent = cancelled ? 'playing (partial)' : 'playing animation';
    toast(`3D CFD done — looping ${frames.length} recorded frames.`);
  };
  requestAnimationFrame(chunk);
}
function lock(on) {
  $('ov3d').classList.toggle('show', on);
  for (const id of ['sim3Btn','locGo','cat3Shapes','cat3Terrain','del3']) $(id).disabled = on;
}
function invalidate() {                        // any edit voids the recorded animation
  frames = []; playing = false;
  if (pointsObj) pointsObj.visible = false;
  if ($('st3state').textContent.startsWith('playing')) $('st3state').textContent = 'idle (edited — re-simulate)';
}

/* ============================================================
   UI bindings & pointer controls
   ============================================================ */
function bindUI() {
  for (const pal of document.querySelectorAll('.pal3d'))
    pal.addEventListener('click', () => { if (category === 'shapes') addObj3(pal.dataset.obj); });
  for (const id of ['t3px','t3py','t3pz','t3rx','t3ry','t3rz','t3sx','t3sy','t3sz'])
    $(id).addEventListener('input', applySliders);
  $('del3').addEventListener('click', () => {
    if (!selectedObj || computing) return;
    shapesGroup.remove(selectedObj);
    objects = objects.filter(o => o !== selectedObj);
    select3(null);
    invalidate();
  });
  $('cat3Shapes').addEventListener('click', () => setCategory('shapes'));
  $('cat3Terrain').addEventListener('click', () => setCategory('terrain'));
  $('locGo').addEventListener('click', () => { if (!computing) loadTerrain($('locName').value.trim() || 'Mussel Rock'); });
  $('locName').addEventListener('keydown', e => { if (e.key === 'Enter') $('locGo').click(); });
  $('dir3').addEventListener('input', () => {
    $('dir3Val').textContent = $('dir3').value + '°';
    const a = parseFloat($('dir3').value)*Math.PI/180;
    windArrow.setDirection(new THREE.Vector3(Math.cos(a), 0, Math.sin(a)));
    invalidate();
  });
  $('spd3').addEventListener('input', () => {
    $('spd3Val').textContent = $('spd3').value + ' MPH';
    windArrow.setLength(3 + mph3()*0.25, 2, 1.2);
    invalidate();
  });
  $('sim3Btn').addEventListener('click', simulate3);
  $('stop3Btn').addEventListener('click', () => {
    if (computing) { cancelReq = true; return; }
    playing = false;
    if (pointsObj) pointsObj.visible = false;
    $('st3state').textContent = 'idle';
  });
  $('ovCancel').addEventListener('click', () => { cancelReq = true; });
  /* camera buttons */
  const A = 0.12;
  $('cYawL').addEventListener('click', () => camYaw(A));
  $('cYawR').addEventListener('click', () => camYaw(-A));
  $('cPitchU').addEventListener('click', () => camPitch(A));
  $('cPitchD').addEventListener('click', () => camPitch(-A));
  $('cRollL').addEventListener('click', () => camRoll(A));
  $('cRollR').addEventListener('click', () => camRoll(-A));
  $('cIn').addEventListener('click', () => camMove(0, 0, -moveStep()*2));
  $('cOut').addEventListener('click', () => camMove(0, 0, moveStep()*2));
  $('cHome').addEventListener('click', () => camGoHome(false));
  /* keyboard */
  window.addEventListener('keydown', e => {
    if (!document.body.classList.contains('mode-3d')) return;
    if (/INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName)) return;
    const s = moveStep();
    const map = {
      w: () => camMove(0,0,-s), s: () => camMove(0,0,s),
      a: () => camMove(-s,0,0), d: () => camMove(s,0,0),
      r: () => camMove(0,s,0),  f: () => camMove(0,-s,0),
      q: () => camRoll(0.08),   e: () => camRoll(-0.08)
    };
    const fn = map[e.key.toLowerCase()];
    if (fn) { fn(); e.preventDefault(); }
  });
  /* pointer: orbit / pan / object drag / pinch */
  const ptrs = new Map();
  let drag = null, moved = false, pinch3 = null;
  const ray = new THREE.Raycaster();
  const ndc = e => {
    const r = cv3.getBoundingClientRect();
    return new THREE.Vector2(((e.clientX - r.left)/r.width)*2 - 1, -((e.clientY - r.top)/r.height)*2 + 1);
  };
  cv3.addEventListener('contextmenu', e => e.preventDefault());
  cv3.addEventListener('pointerdown', e => {
    if (computing) return;
    cv3.setPointerCapture(e.pointerId);
    ptrs.set(e.pointerId, {x: e.clientX, y: e.clientY});
    if (ptrs.size === 2) {
      const [a, b] = [...ptrs.values()];
      pinch3 = { d0: Math.hypot(a.x-b.x, a.y-b.y) || 1, mx: (a.x+b.x)/2, my: (a.y+b.y)/2 };
      drag = null;
      return;
    }
    moved = false;
    camera.position.copy(camPos); camera.quaternion.copy(camQ); camera.updateMatrixWorld();
    if (e.button === 2) { drag = {mode: 'pan', x: e.clientX, y: e.clientY}; return; }
    if (category === 'shapes' && objects.length) {
      ray.setFromCamera(ndc(e), camera);
      const hit = ray.intersectObjects(objects)[0];
      if (hit) {
        select3(hit.object);
        drag = {mode: 'obj', planeY: hit.object.position.y};
        return;
      }
    }
    drag = {mode: 'orbit', x: e.clientX, y: e.clientY};
  });
  cv3.addEventListener('pointermove', e => {
    if (computing) return;
    if (ptrs.has(e.pointerId)) ptrs.set(e.pointerId, {x: e.clientX, y: e.clientY});
    if (pinch3 && ptrs.size >= 2) {
      const [a, b] = [...ptrs.values()];
      const d = Math.hypot(a.x-b.x, a.y-b.y) || 1;
      camMove(0, 0, (pinch3.d0 - d)*moveStep()*0.02);
      pinch3.d0 = d;
      const mx = (a.x+b.x)/2, my = (a.y+b.y)/2;
      camMove(-(mx-pinch3.mx)*moveStep()*0.01, (my-pinch3.my)*moveStep()*0.01, 0);
      pinch3.mx = mx; pinch3.my = my;
      return;
    }
    if (!drag) return;
    moved = true;
    if (drag.mode === 'orbit') {
      camYaw(-(e.clientX - drag.x)*0.005);
      camPitch(-(e.clientY - drag.y)*0.005);
      drag.x = e.clientX; drag.y = e.clientY;
    } else if (drag.mode === 'pan') {
      const s = moveStep()*0.02;
      camMove(-(e.clientX - drag.x)*s, (e.clientY - drag.y)*s, 0);
      drag.x = e.clientX; drag.y = e.clientY;
    } else if (drag.mode === 'obj' && selectedObj) {
      camera.position.copy(camPos); camera.quaternion.copy(camQ); camera.updateMatrixWorld();
      ray.setFromCamera(ndc(e), camera);
      const pt = new THREE.Vector3();
      if (ray.ray.intersectPlane(new THREE.Plane(new THREE.Vector3(0,1,0), -drag.planeY), pt)) {
        selectedObj.position.x = Math.max(-DX/2+1, Math.min(DX/2-1, pt.x));
        selectedObj.position.z = Math.max(-DZ/2+1, Math.min(DZ/2-1, pt.z));
        syncSliders();
        invalidate();
      }
    }
  });
  const endPtr = e => {
    ptrs.delete(e.pointerId);
    if (ptrs.size < 2) pinch3 = null;
    if (drag && drag.mode === 'orbit' && !moved && category === 'shapes') select3(null);
    drag = null;
  };
  cv3.addEventListener('pointerup', endPtr);
  cv3.addEventListener('pointercancel', endPtr);
  cv3.addEventListener('wheel', e => {
    e.preventDefault();
    if (computing) return;
    camMove(0, 0, (e.deltaY > 0 ? 1 : -1)*moveStep());
  }, {passive: false});
}
function setCategory(cat) {
  if (computing) return;
  category = cat;
  $('cat3Shapes').classList.toggle('active', cat === 'shapes');
  $('cat3Terrain').classList.toggle('active', cat === 'terrain');
  $('pal3wrap').style.display = cat === 'shapes' ? '' : 'none';
  $('terrWrap').style.display = cat === 'terrain' ? '' : 'none';
  shapesGroup.visible = cat === 'shapes';
  terrainGroup.visible = cat === 'terrain';
  select3(null);
  invalidate();
  if (cat === 'terrain' && terra) camGoHome(true);
  if (cat === 'shapes') camGoHome(true);
  /* wind arrow anchor */
  if (cat === 'terrain' && terra) {
    windArrow.position.set(-terra.extentM/2, terra.hRange*1.3, -terra.extentM/2);
    windArrow.setLength(terra.extentM*0.08, terra.extentM*0.02, terra.extentM*0.012);
  } else {
    windArrow.position.set(-DX/2, DY*0.9, -DZ/2);
    windArrow.setLength(3 + mph3()*0.25, 2, 1.2);
  }
}
})();

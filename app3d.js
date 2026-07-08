"use strict";
/* ============================================================
   3D mode: Three.js + D3Q19 lattice-Boltzmann CFD (precomputed).
   - Terrain: satellite imagery (Esri World Imagery) draped over
     AWS/Mapzen elevation tiles -> Google-Earth-style rendering.
     (Google's own Photorealistic 3D Tiles / Elevation APIs require
     an API key + billing, so key-less open equivalents are used.)
   - Location search: Photon (OSM) autocomplete, no key.
   - Flow display: ADAPTIVE-MESH wind arrows (finer where terrain is
     complex / near objects), animated from recorded CFD frames.
     Magenta arrows = rotor (recirculating, reversed-flow) area.
   ============================================================ */
(function () {
const $ = id => document.getElementById(id);
const toast = msg => (window.toast ? window.toast(msg) : console.log(msg));

/* ---------- module state ---------- */
let inited = false;
let renderer, scene, camera, cv3, wrap3;
let camPos, camQ, camHomePos, camHomeQ;
let objects = [];
let selectedObj = null;
let category = 'shapes';
let terra = null;                 // {n, hg, extentM, hRange, mesh, name, tex}
let shapesGroup, terrainGroup, windArrow;

/* compute / playback */
let computing = false, cancelReq = false;
let frames = [], rotorVols = [], playT = 0, playing = false;

/* adaptive arrow field */
let arrowPts = null;              // Float32Array(A*3) lattice coords
let arrowLen = null;              // Float32Array(A) max length (lattice units)
let A = 0;
let lineObj = null, lineGeo = null;

/* pilot tools */
let liftObj = null, sliceObj = null, markersGroup = null;
let FAC = null;                   // log wind-gradient factor per lattice level

/* ---------- preset flying sites (paraglider/hang glider launches) ---------- */
const SITES = {
  mussel: { name: 'Mussel Rock, CA', lat: 37.67302, lon: -122.49418, markers: [
    { name: 'LZ (dirt lot)',  lat: 37.669190670816974, lon: -122.49405521827042, kind: 'lz' },
    { name: 'Walker launch',  lat: 37.67270434204596,  lon: -122.49368503332906, kind: 'launch' },
    { name: 'Coyote launch',  lat: 37.671749417451814, lon: -122.49356699947602, kind: 'launch' },
    { name: 'Soaring cliff',  lat: 37.6784365329671,   lon: -122.49539527331778, kind: 'poi' }
  ]},
  edlevin: { name: 'Ed Levin Park, CA', lat: 37.46393, lon: -121.86317, markers: [
    { name: 'LZ',              lat: 37.458163624785364, lon: -121.86668950429737, kind: 'lz' },
    { name: '1750 ft launch',  lat: 37.47530461981,     lon: -121.86087789291778, kind: 'launch' },
    { name: '300 ft foothill', lat: 37.46107421138769,  lon: -121.86459985121138, kind: 'launch' },
    { name: '600 ft foothill', lat: 37.46118788768288,  lon: -121.860526001938,   kind: 'launch' }
  ]}
};
const DIRN = ['N','NE','E','SE','S','SW','W','NW'];
function compassFrom(aDeg) {       // slider angle -> meteorological "wind from" degrees
  const a = aDeg*Math.PI/180;
  return (Math.atan2(-Math.cos(a), Math.sin(a))*180/Math.PI + 360) % 360;
}

/* ---------- free-drawing domain (feet) ---------- */
const DX = 36, DY = 16, DZ = 24;
let CELL = 0.5;                   // ft per lattice cell (varies w/ granularity)

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
let OFF = null;
let sceneScale = 1, sceneOffX = 0, sceneOffZ = 0;

/* mesh granularity presets */
const GRAN = {
  coarse: { sx: 56, sy: 24, sz: 36, tHoriz: 56, minW: 9 },
  medium: { sx: 72, sy: 32, sz: 48, tHoriz: 72, minW: 6 },
  fine:   { sx: 88, sy: 40, sz: 60, tHoriz: 96, minW: 4 }
};
const gran = () => GRAN[$('mesh3Res').value] || GRAN.medium;

/* wind */
const mph3 = () => parseFloat($('spd3').value);
const u03 = () => 0.03 + (mph3()/30) * 0.07;
function windVec3() {
  const a = parseFloat($('dir3').value) * Math.PI/180, u = u03();
  return [u*Math.cos(a), 0, u*Math.sin(a)];
}

/* color LUT */
const LUT3 = [];
for (let i = 0; i < 32; i++) {
  const t = i/31, h = 225*(1-t)/360, s = 0.85, l = 0.45 + 0.15*t;
  const a2 = s*Math.min(l, 1-l);
  const f2 = n => { const k = (n + h*12) % 12; return l - a2*Math.max(-1, Math.min(k-3, 9-k, 1)); };
  LUT3.push({r: f2(0), g: f2(8), b: f2(4)});
}
const lut3 = t => LUT3[Math.max(0, Math.min(31, (t*31)|0))];
const ROTOR_C = {r: 1.0, g: 0.30, b: 0.85};

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
  camera = new THREE.PerspectiveCamera(55, 1, 0.1, 200000);
  camPos = new THREE.Vector3(); camQ = new THREE.Quaternion();
  camHomePos = new THREE.Vector3(); camHomeQ = new THREE.Quaternion();

  scene.add(new THREE.HemisphereLight(0xbdc7d8, 0x30383f, 1.0));
  const sun = new THREE.DirectionalLight(0xfff2dd, 0.8);
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

function loop3() {
  requestAnimationFrame(loop3);
  if (!document.body.classList.contains('mode-3d')) return;
  if (playing && frames.length) {
    playT += 24/60;
    const idx = (playT|0) % frames.length;
    applyFrame(idx);
  }
  camera.position.copy(camPos);
  camera.quaternion.copy(camQ);
  renderer.render(scene, camera);
}

/* ============================================================
   Camera
   ============================================================ */
const _q = () => new THREE.Quaternion();
function camYaw(a)   { camQ.premultiply(_q().setFromAxisAngle(new THREE.Vector3(0,1,0), a)); }
function camPitch(a) { camQ.multiply(_q().setFromAxisAngle(new THREE.Vector3(1,0,0), a)); }
function camRoll(a)  { camQ.multiply(_q().setFromAxisAngle(new THREE.Vector3(0,0,1), a)); }
function camMove(dx, dy, dz) { camPos.add(new THREE.Vector3(dx, dy, dz).applyQuaternion(camQ)); }
function moveStep() { return category === 'terrain' && terra ? terra.extentM/30 : 2.5; }
function camGoHome(recompute) {
  if (recompute) {
    if (category === 'terrain' && terra) {
      const e = terra.extentM;
      camera.position.set(e*0.6, terra.hRange + e*0.4, e*0.8);
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
   Free-drawing environment & objects
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
  box:    { make: () => new THREE.BoxGeometry(4, 4, 4),              test: p => Math.abs(p.x)<=2 && Math.abs(p.y)<=2 && Math.abs(p.z)<=2 },
  sphere: { make: () => new THREE.SphereGeometry(2, 24, 16),         test: p => p.lengthSq() <= 4 },
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
   Location autocomplete (Photon / OSM) + terrain loading
   ============================================================ */
let sugTimer = null, chosenLoc = null;
function bindAutocomplete() {
  const inp = $('locName'), box = $('locSug');
  const hide = () => { box.style.display = 'none'; };
  inp.addEventListener('input', () => {
    chosenLoc = null;
    clearTimeout(sugTimer);
    const q = inp.value.trim();
    if (q.length < 3) { hide(); return; }
    sugTimer = setTimeout(async () => {
      try {
        const r = await fetch('https://photon.komoot.io/api/?limit=6&q=' + encodeURIComponent(q));
        const j = await r.json();
        box.innerHTML = '';
        if (!j.features || !j.features.length) { hide(); return; }
        for (const ft of j.features) {
          const p = ft.properties;
          const label = [p.name, p.state || p.city, p.country].filter(Boolean).join(', ');
          const div = document.createElement('div');
          div.className = 'sugitem';
          div.textContent = label;
          div.addEventListener('pointerdown', e => {
            e.preventDefault();
            inp.value = label;
            chosenLoc = { lat: ft.geometry.coordinates[1], lon: ft.geometry.coordinates[0], label: p.name || label };
            hide();
            loadTerrainAt(chosenLoc);
          });
          box.appendChild(div);
        }
        box.style.display = 'block';
      } catch (e) { hide(); }
    }, 350);
  });
  inp.addEventListener('blur', () => setTimeout(hide, 250));
  inp.addEventListener('keydown', e => {
    if (e.key === 'Escape') hide();
    if (e.key === 'Enter') { hide(); $('locGo').click(); }
  });
}
async function geocode(q) {
  const r = await fetch('https://photon.komoot.io/api/?limit=1&q=' + encodeURIComponent(q));
  const j = await r.json();
  if (!j.features || !j.features.length) return null;
  const ft = j.features[0];
  return { lat: ft.geometry.coordinates[1], lon: ft.geometry.coordinates[0], label: ft.properties.name || q };
}
function loadSite(key) {
  const s = SITES[key];
  if (!s) return;
  $('locName').value = s.name;
  loadTerrainAt({ lat: s.lat, lon: s.lon, label: s.name, site: key });
}
async function loadTerrainAt(loc) {
  const st = $('terrStatus');
  try {
    invalidate();
    const { lat, lon, label } = loc;
    $('siteSel').value = loc.site || '';
    st.textContent = 'Fetching elevation…';
    const z = 14, n2 = Math.pow(2, z);
    const xt = (lon + 180)/360 * n2;
    const yt = (1 - Math.log(Math.tan(lat*Math.PI/180) + 1/Math.cos(lat*Math.PI/180))/Math.PI)/2 * n2;
    const x0 = Math.max(0, Math.floor(xt - 1)), y0 = Math.max(0, Math.floor(yt - 1));
    const loadImg = src => new Promise((res, rej) => {
      const img = new Image();
      img.crossOrigin = 'anonymous';
      img.onload = () => res(img);
      img.onerror = () => rej(new Error('tile failed'));
      img.src = src;
    });
    /* --- elevation: prefer USGS 3DEP 1 m lidar (US, keyless), fall back to Mapzen terrarium (~10 m) --- */
    const t2lon = xx => xx/n2*360 - 180;
    const t2lat = yy => Math.atan(Math.sinh(Math.PI*(1 - 2*yy/n2)))*180/Math.PI;
    let n, hg, demSrc;
    try {
      if (typeof Lerc === 'undefined') throw new Error('lerc lib not loaded');
      if (Lerc.load) await Lerc.load();
      n = 513;                                     // ~7.6 m grid from 1 m source
      const url3dep = `https://elevation.nationalmap.gov/arcgis/rest/services/3DEPElevation/ImageServer/exportImage` +
        `?bbox=${t2lon(x0)},${t2lat(y0+2)},${t2lon(x0+2)},${t2lat(y0)}&bboxSR=4326&imageSR=4326` +
        `&size=${n},${n}&format=lerc&pixelType=F32&noDataInterpretation=esriNoDataMatchAny` +
        `&interpolation=RSP_BilinearInterpolation&f=image`;
      let buf = null;                              // USGS service can fail on cold start — retry
      for (let att = 0; att < 3 && !buf; att++) {
        try { buf = await (await fetch(url3dep)).arrayBuffer(); }
        catch (efetch) { if (att === 2) throw efetch; await new Promise(rs => setTimeout(rs, 900)); }
      }
      const dec = Lerc.decode(buf);
      const data = dec.pixels[0];
      if (dec.width !== n || data.length < n*n) throw new Error('unexpected raster');
      hg = new Float32Array(n*n);
      let valid = 0;
      for (let i = 0; i < n*n; i++) {
        let e = data[i];
        if (isFinite(e) && e > -100 && e < 9000) valid++; else e = 0;
        hg[i] = Math.max(0, e);
      }
      if (valid < n*n*0.5) throw new Error('no 1 m lidar coverage here');
      demSrc = 'USGS 3DEP 1 m lidar';
    } catch (e3dep) {
      /* terrarium fallback: 4x4 tiles @ z15 (max zoom) -> 1024px */
      n = 257;
      const ecnv = document.createElement('canvas'); ecnv.width = 1024; ecnv.height = 1024;
      const ectx = ecnv.getContext('2d');
      await Promise.all(Array.from({length: 16}, (_, i) => (async () => {
        const xi = 2*x0 + (i%4), yi = 2*y0 + (i>>2);
        const img = await loadImg(`https://s3.amazonaws.com/elevation-tiles-prod/terrarium/${z+1}/${xi}/${yi}.png`);
        ectx.drawImage(img, (i%4)*256, (i>>2)*256);
      })()));
      const px = ectx.getImageData(0, 0, 1024, 1024).data;
      const elevAt = (ix, iy) => {
        const o = (Math.min(1023, iy)*1024 + Math.min(1023, ix))*4;
        return (px[o]*256 + px[o+1] + px[o+2]/256) - 32768;
      };
      hg = new Float32Array(n*n);
      for (let j = 0; j < n; j++) for (let i = 0; i < n; i++)
        hg[j*n+i] = Math.max(0, elevAt(Math.round(i/(n-1)*1023), Math.round(j/(n-1)*1023)));
      demSrc = 'Mapzen/AWS (~10 m)';
    }
    let minE = 1e9, maxE = -1e9;
    const sm = new Float32Array(n*n);
    for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) {
      let s = 0, c = 0;
      for (let dj = -1; dj <= 1; dj++) for (let di = -1; di <= 1; di++) {
        const jj = j+dj, ii = i+di;
        if (jj < 0 || jj >= n || ii < 0 || ii >= n) continue;
        s += hg[jj*n+ii]; c++;
      }
      sm[j*n+i] = s/c;
    }
    hg = sm;
    for (let i = 0; i < n*n; i++) { minE = Math.min(minE, hg[i]); maxE = Math.max(maxE, hg[i]); }
    for (let i = 0; i < n*n; i++) hg[i] -= minE;
    const spanM = 40075016.686 * Math.cos(lat*Math.PI/180) / n2;
    const extentM = spanM * 2;
    /* satellite imagery 8x8 @ z16 -> 2048px (Esri World Imagery), per-tile fault tolerance */
    st.textContent = 'Fetching satellite imagery…';
    let tex = null;
    try {
      const icnv = document.createElement('canvas'); icnv.width = 2048; icnv.height = 2048;
      const ictx = icnv.getContext('2d');
      let failed = 0;
      await Promise.all(Array.from({length: 64}, (_, i) => (async () => {
        const xi = 4*x0 + (i%8), yi = 4*y0 + (i>>3);
        try {
          const img = await loadImg(`https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/${z+2}/${yi}/${xi}`);
          ictx.drawImage(img, (i%8)*256, (i>>3)*256);
        } catch (e) {
          failed++;
          ictx.fillStyle = '#3a4048';
          ictx.fillRect((i%8)*256, (i>>3)*256, 256, 256);
        }
      })()));
      if (failed < 20) {
        tex = new THREE.CanvasTexture(icnv);
        if (renderer.capabilities.getMaxAnisotropy) tex.anisotropy = renderer.capabilities.getMaxAnisotropy();
      }
    } catch (e) { tex = null; }   // fall back to elevation colors
    terra = { n, hg, extentM, hRange: Math.max(10, maxE - minE), name: label, tex,
              lat, lon, x0, y0, z, spanM, site: loc.site || null, markers: [] };
    buildTerrainMesh();
    buildMarkers();
    camGoHome(true);
    setCategory('terrain');
    st.textContent = `${label} · ${(extentM/1000).toFixed(1)} × ${(extentM/1000).toFixed(1)} km · relief ${Math.round(terra.hRange)} m · ${(extentM/(n-1)).toFixed(1)} m grid from ${demSrc}` +
      (tex ? ' · imagery © Esri/Maxar' : ' · (imagery unavailable — elevation colors)');
  } catch (err) {
    st.textContent = 'Failed to load terrain (' + err.message + '). Check connection and try again.';
  }
}
function buildTerrainMesh() {
  while (terrainGroup.children.length) terrainGroup.remove(terrainGroup.children[0]);
  const { n, hg, extentM, hRange, tex } = terra;
  /* render mesh at <=257 verts/side for perf; CFD + markers still use the full-res hg grid */
  const step = Math.max(1, Math.round((n-1)/256));
  const m = (n-1)/step + 1;
  const pos = new Float32Array(m*m*3), col = new Float32Array(m*m*3), uv = new Float32Array(m*m*2);
  for (let j = 0; j < m; j++) for (let i = 0; i < m; i++) {
    const k = j*m+i, h = hg[(j*step)*n + i*step];
    pos[k*3]   = (i/(m-1) - 0.5)*extentM;
    pos[k*3+1] = h;
    pos[k*3+2] = (j/(m-1) - 0.5)*extentM;
    uv[k*2] = i/(m-1); uv[k*2+1] = 1 - j/(m-1);
    const t = h/hRange;
    let r, g2, b;
    if (h < 0.5) { r=0.10; g2=0.30; b=0.55; }
    else if (t < 0.5) { const u=t*2;     r=0.16+0.24*u; g2=0.38-0.05*u; b=0.16+0.06*u; }
    else              { const u=(t-0.5)*2; r=0.40+0.5*u; g2=0.33+0.55*u; b=0.22+0.7*u; }
    col[k*3]=r; col[k*3+1]=g2; col[k*3+2]=b;
  }
  const idx = [];
  for (let j = 0; j < m-1; j++) for (let i = 0; i < m-1; i++) {
    const a=j*m+i, b=a+1, c=a+m, d=c+1;
    idx.push(a,c,b, b,c,d);
  }
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(pos, 3));
  geo.setAttribute('color', new THREE.BufferAttribute(col, 3));
  geo.setAttribute('uv', new THREE.BufferAttribute(uv, 2));
  geo.setIndex(idx);
  geo.computeVertexNormals();
  const mat = tex
    ? new THREE.MeshLambertMaterial({map: tex})
    : new THREE.MeshLambertMaterial({vertexColors: true, side: THREE.DoubleSide});
  terra.mesh = new THREE.Mesh(geo, mat);
  terrainGroup.add(terra.mesh);
}
function terrainHeight(wx, wz) {
  const { n, hg, extentM } = terra;
  let gx = (wx/extentM + 0.5)*(n-1), gz = (wz/extentM + 0.5)*(n-1);
  gx = Math.max(0, Math.min(n-1.001, gx)); gz = Math.max(0, Math.min(n-1.001, gz));
  const i = gx|0, j = gz|0, fx = gx-i, fz = gz-j;
  return hg[j*n+i]*(1-fx)*(1-fz) + hg[j*n+i+1]*fx*(1-fz) + hg[(j+1)*n+i]*(1-fx)*fz + hg[(j+1)*n+i+1]*fx*fz;
}

/* ---------- site markers (LZ / launches) ---------- */
function ll2scene(lat, lon) {
  const n2 = Math.pow(2, terra.z);
  const xt = (lon + 180)/360 * n2;
  const yt = (1 - Math.log(Math.tan(lat*Math.PI/180) + 1/Math.cos(lat*Math.PI/180))/Math.PI)/2 * n2;
  return { x: (xt - (terra.x0 + 1))*terra.spanM, z: (yt - (terra.y0 + 1))*terra.spanM };
}
function makeLabel(text, color) {
  const c = document.createElement('canvas'); c.width = 512; c.height = 128;
  const x = c.getContext('2d');
  x.font = 'bold 52px sans-serif'; x.textAlign = 'center'; x.textBaseline = 'middle';
  x.strokeStyle = 'rgba(0,0,0,0.85)'; x.lineWidth = 10; x.strokeText(text, 256, 64);
  x.fillStyle = '#' + color.toString(16).padStart(6, '0'); x.fillText(text, 256, 64);
  const t = new THREE.CanvasTexture(c);
  return new THREE.Sprite(new THREE.SpriteMaterial({map: t, transparent: true, depthTest: false}));
}
function buildMarkers() {
  if (markersGroup) terrainGroup.remove(markersGroup);
  markersGroup = new THREE.Group();
  terrainGroup.add(markersGroup);
  terra.markers = [];
  const sel = $('sliceSel');
  sel.innerHTML = '<option value="-1">None</option>';
  if (!terra.site || !SITES[terra.site]) return;
  const e = terra.extentM;
  for (const d of SITES[terra.site].markers) {
    const p = ll2scene(d.lat, d.lon);
    if (Math.abs(p.x) > e/2 || Math.abs(p.z) > e/2) continue;
    const y = terrainHeight(p.x, p.z);
    const col = d.kind === 'lz' ? 0x39d353 : d.kind === 'launch' ? 0xffa657 : 0x4da3ff;
    const poleH = e*0.02;
    const pole = new THREE.Mesh(
      new THREE.CylinderGeometry(e*0.0012, e*0.0012, poleH, 6),
      new THREE.MeshBasicMaterial({color: col})
    );
    pole.position.set(p.x, y + poleH/2, p.z);
    markersGroup.add(pole);
    const spr = makeLabel(d.name, col);
    spr.position.set(p.x, y + poleH*1.3, p.z);
    spr.scale.set(e*0.12, e*0.03, 1);
    markersGroup.add(spr);
    terra.markers.push({ name: d.name, kind: d.kind, x: p.x, z: p.z, y });
    const o = document.createElement('option');
    o.value = String(terra.markers.length - 1);
    o.textContent = d.name;
    sel.appendChild(o);
  }
  const li = terra.markers.findIndex(m => m.kind === 'launch');
  if (li >= 0) sel.value = String(li);
}
/* ---------- live wind (Open-Meteo, keyless) ---------- */
async function liveWind() {
  if (!terra || terra.lat === undefined) { toast('Load a terrain / site first.'); return; }
  try {
    const r = await fetch(`https://api.open-meteo.com/v1/forecast?latitude=${terra.lat}&longitude=${terra.lon}&current=wind_speed_10m,wind_direction_10m,wind_gusts_10m&wind_speed_unit=mph`);
    const j = await r.json();
    const c = j.current;
    $('spd3').value = Math.max(1, Math.min(30, Math.round(c.wind_speed_10m)));
    const D = c.wind_direction_10m*Math.PI/180;
    $('dir3').value = Math.round((Math.atan2(Math.cos(D), -Math.sin(D))*180/Math.PI + 360) % 360);
    $('dir3').dispatchEvent(new Event('input'));
    $('spd3').dispatchEvent(new Event('input'));
    toast(`Live wind: ${Math.round(c.wind_speed_10m)} mph, gusting ${Math.round(c.wind_gusts_10m)}, from ${Math.round(c.wind_direction_10m)}° ${DIRN[Math.round(c.wind_direction_10m/45) % 8]}`, 4000);
  } catch (e) { toast('Live wind unavailable (' + e.message + ')'); }
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
    for (let z = 0; z < LZ; z++) for (let x = 0; x < LX; x++) solid3[x + LX*(0 + LY*z)] = 1;
    const v = new THREE.Vector3();
    const invs = objects.map(m => {
      m.updateMatrixWorld(true);
      return { inv: new THREE.Matrix4().copy(m.matrixWorld).invert(), test: OBJ_DEF[m.userData.kind].test };
    });
    if (invs.length) {
      for (let z = 1; z < LZ-1; z++) for (let y = 1; y < LY-1; y++) for (let x = 1; x < LX-1; x++) {
        const wx = (x+0.5)*CELL - DX/2, wy = (y+0.5)*CELL, wz = (z+0.5)*CELL - DZ/2;
        for (const o of invs) {
          v.set(wx, wy, wz).applyMatrix4(o.inv);
          if (o.test(v)) { solid3[x + LX*(y + LY*z)] = 1; break; }
        }
      }
    }
  }
}
function initFluid3() {
  const [u0x, , u0z] = windVec3();
  for (let z = 0; z < LZ; z++) for (let y = 0; y < LY; y++) {
    const fy = FAC ? FAC[y] : 1;
    const ux = u0x*fy, uz = u0z*fy;
    const row = LX*(y + LY*z);
    for (let x = 0; x < LX; x++) {
      const i = row + x;
      setEq3(f3, i, 1, ux, 0, uz);
      VX[i] = ux; VY[i] = 0; VZ[i] = uz;
    }
  }
}
function lbm3Step() {
  const [u0x, u0y, u0z] = windVec3();
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
  for (let z = 0; z < LZ; z++) for (let y = 0; y < LY; y++) {
    const fy = FAC ? FAC[y] : 1, ux = u0x*fy, uz = u0z*fy;
    const a = 0 + LX*(y + LY*z), b = (LX-1) + LX*(y + LY*z);
    if (!solid3[a]) { setEq3(g3, a, 1, ux, 0, uz); VX[a]=ux; VY[a]=0; VZ[a]=uz; }
    if (!solid3[b]) { setEq3(g3, b, 1, ux, 0, uz); VX[b]=ux; VY[b]=0; VZ[b]=uz; }
  }
  for (let x = 0; x < LX; x++) for (let y = 0; y < LY; y++) {
    const fy = FAC ? FAC[y] : 1, ux = u0x*fy, uz = u0z*fy;
    const a = x + LX*(y + 0), b = x + LX*(y + LY*(LZ-1));
    if (!solid3[a]) { setEq3(g3, a, 1, ux, 0, uz); VX[a]=ux; VY[a]=0; VZ[a]=uz; }
    if (!solid3[b]) { setEq3(g3, b, 1, ux, 0, uz); VX[b]=ux; VY[b]=0; VZ[b]=uz; }
  }
  {
    const fy = FAC ? FAC[LY-1] : 1, ux = u0x*fy, uz = u0z*fy;
    for (let x = 0; x < LX; x++) for (let z = 0; z < LZ; z++) {
      const a = x + LX*((LY-1) + LY*z);
      if (!solid3[a]) { setEq3(g3, a, 1, ux, 0, uz); VX[a]=ux; VY[a]=0; VZ[a]=uz; }
    }
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
   Adaptive arrow mesh (quadtree: finer where terrain is complex
   or near objects), animated from recorded velocity frames
   ============================================================ */
function buildArrowField() {
  const pts = [], lens = [];
  const minW = gran().minW;
  const cellM = category === 'terrain' && terra ? terra.extentM/LX : CELL;
  /* complexity test for a horizontal cell [x..x+w) x [z..z+w) */
  const complex = (x, z, w) => {
    if (category === 'terrain' && terra) {
      let hmin = 1e9, hmax = -1e9;
      for (let j = 0; j <= 2; j++) for (let i = 0; i <= 2; i++) {
        const h = terrainHeight((x + w*i/2 - LX/2)*cellM, (z + w*j/2 - LZ/2)*cellM);
        hmin = Math.min(hmin, h); hmax = Math.max(hmax, h);
      }
      return (hmax - hmin) > 0.22 * w * cellM;          // steep relief -> refine
    }
    /* shapes: refine near object bounding boxes */
    const bb = new THREE.Box3();
    for (const m of objects) {
      bb.setFromObject(m);
      const x0 = (bb.min.x + DX/2)/CELL - 2, x1 = (bb.max.x + DX/2)/CELL + 2;
      const z0 = (bb.min.z + DZ/2)/CELL - 2, z1 = (bb.max.z + DZ/2)/CELL + 2;
      if (x + w > x0 && x < x1 && z + w > z0 && z < z1) return true;
    }
    return false;
  };
  const leaf = (x, z, w) => {
    const cx2 = x + w/2, cz2 = z + w/2;
    let surf = 1;                                        // lattice y of local surface
    if (category === 'terrain' && terra)
      surf = Math.min(LY-3, terrainHeight((cx2 - LX/2)*cellM, (cz2 - LZ/2)*cellM)/cellM);
    const room = LY - 1.5 - surf;
    const levels = [surf + Math.max(1.2, room*0.08), surf + room*0.35, surf + room*0.68];
    for (const ly of levels) {
      const ii = (cx2|0) + LX*((ly|0) + LY*(cz2|0));
      if (solid3[ii]) continue;
      pts.push(cx2, ly, cz2);
      lens.push(Math.min(w, 12)*0.62);
    }
  };
  const rec = (x, z, w, depth) => {
    if ((depth < 3) || (w > minW && depth < 7 && complex(x, z, w))) {
      const h = w/2;
      rec(x, z, h, depth+1);     rec(x+h, z, h, depth+1);
      rec(x, z+h, h, depth+1);   rec(x+h, z+h, h, depth+1);
    } else leaf(x, z, w);
  };
  const size = Math.max(LX, LZ);
  rec(0, 0, size, 0);
  /* drop leaves outside the domain (size may exceed LZ) */
  const fp = [], fl = [];
  for (let i = 0; i < lens.length; i++) {
    const x = pts[i*3], z = pts[i*3+2];
    if (x >= 1 && x <= LX-1 && z >= 1 && z <= LZ-1) { fp.push(pts[i*3], pts[i*3+1], pts[i*3+2]); fl.push(lens[i]); }
  }
  arrowPts = new Float32Array(fp);
  arrowLen = new Float32Array(fl);
  A = fl.length;
  $('st3arrows').textContent = A.toLocaleString();
}
function ensureArrowObject() {
  if (lineObj) { scene.remove(lineObj); lineGeo.dispose(); lineObj.material.dispose(); }
  lineGeo = new THREE.BufferGeometry();
  lineGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(A*6*3), 3));
  lineGeo.setAttribute('color', new THREE.BufferAttribute(new Float32Array(A*6*3), 3));
  lineObj = new THREE.LineSegments(lineGeo, new THREE.LineBasicMaterial({vertexColors: true}));
  lineObj.frustumCulled = false;
  scene.add(lineObj);
}
function recordFrame() {
  const fr = new Float32Array(A*4);
  const v = [0,0,0];
  for (let i = 0; i < A; i++) {
    sampleV3(arrowPts[i*3], arrowPts[i*3+1], arrowPts[i*3+2], v);
    fr[i*4] = v[0]; fr[i*4+1] = v[1]; fr[i*4+2] = v[2];
    fr[i*4+3] = Math.sqrt(v[0]*v[0] + v[1]*v[1] + v[2]*v[2]) / u03();
  }
  frames.push(fr);
  /* rotor volume: count reversed-flow fluid cells */
  const [wx,,wz] = windVec3();
  const wm = Math.hypot(wx, wz), wnx = wx/wm, wnz = wz/wm, thr = -0.03*wm;
  let cnt = 0;
  for (let i = 0; i < N3; i++) {
    if (!solid3[i] && (VX[i]*wnx + VZ[i]*wnz) < thr) cnt++;
  }
  const cellL = category === 'terrain' && terra ? terra.extentM/LX : CELL;
  rotorVols.push(cnt * cellL*cellL*cellL);
  applyFrame(frames.length - 1);               // live preview
}
function fmtVol(v) {
  const unit = category === 'terrain' ? 'm³' : 'ft³';
  if (v >= 1e6) return (v/1e6).toFixed(2) + 'M ' + unit;
  if (v >= 1e3) return (v/1e3).toFixed(1) + 'k ' + unit;
  return Math.round(v) + ' ' + unit;
}
function applyFrame(idx) {
  if (!lineGeo || !frames[idx]) return;
  const fr = frames[idx];
  const pa = lineGeo.attributes.position.array, ca = lineGeo.attributes.color.array;
  const [wx,,wz] = windVec3();
  const wm = Math.hypot(wx, wz), wnx = wx/wm, wnz = wz/wm, thr = -0.03*wm;
  for (let i = 0; i < A; i++) {
    const vx = fr[i*4], vy = fr[i*4+1], vz = fr[i*4+2], t = fr[i*4+3];
    const sp = Math.sqrt(vx*vx + vy*vy + vz*vz);
    const bx = arrowPts[i*3]*sceneScale + sceneOffX;
    const by = arrowPts[i*3+1]*sceneScale;
    const bz = arrowPts[i*3+2]*sceneScale + sceneOffZ;
    let o = i*18;
    if (sp < 1e-6) { for (let k = 0; k < 18; k++) pa[o+k] = 0; continue; }
    const dx = vx/sp, dy = vy/sp, dz = vz/sp;
    const len = arrowLen[i]*(0.35 + 0.65*Math.min(1, t/1.6)) * sceneScale;
    const tx = bx + dx*len, ty = by + dy*len, tz = bz + dz*len;
    /* head basis: perpendicular to dir */
    let hx = -dz, hy = 0, hz = dx;
    const hm = Math.hypot(hx, hz) || 1;
    hx /= hm; hz /= hm;
    const hl = len*0.32;
    pa[o]   = bx; pa[o+1] = by; pa[o+2] = bz;
    pa[o+3] = tx; pa[o+4] = ty; pa[o+5] = tz;
    pa[o+6] = tx; pa[o+7] = ty; pa[o+8] = tz;
    pa[o+9] = tx - dx*hl + hx*hl*0.55; pa[o+10] = ty - dy*hl; pa[o+11] = tz - dz*hl + hz*hl*0.55;
    pa[o+12] = tx; pa[o+13] = ty; pa[o+14] = tz;
    pa[o+15] = tx - dx*hl - hx*hl*0.55; pa[o+16] = ty - dy*hl; pa[o+17] = tz - dz*hl - hz*hl*0.55;
    const rotor = (vx*wnx + vz*wnz) < thr;
    const c = rotor ? ROTOR_C : lut3(Math.min(1, t/1.6));
    for (let k = 0; k < 6; k++) { ca[o + k*3] = c.r; ca[o + k*3 + 1] = c.g; ca[o + k*3 + 2] = c.b; }
  }
  lineGeo.attributes.position.needsUpdate = true;
  lineGeo.attributes.color.needsUpdate = true;
  if (rotorVols[idx] !== undefined) $('st3rotor').textContent = fmtVol(rotorVols[idx]);
}

/* ============================================================
   Pilot tools: lift band, cross-section slice, launch verdicts
   ============================================================ */
function clearObj(o) {
  if (!o) return;
  scene.remove(o);
  if (o.geometry) o.geometry.dispose();
  if (o.material) { if (o.material.map) o.material.map.dispose(); o.material.dispose(); }
}
const sinkThr = () => parseFloat($('sinkRate').value);
const vRefMs = () => mph3()*0.44704;                 // slider mph -> m/s (or ft-domain equivalent)
/* green cloud of every cell where updraft >= glider sink rate */
function buildLiftBand() {
  clearObj(liftObj); liftObj = null;
  if (!frames.length || !VY) return;
  const Vref = vRefMs(), u0 = u03(), thr = sinkThr();
  const pts = [];
  for (let z = 1; z < LZ-1; z++) for (let y = 1; y < LY-1; y++) {
    const row = LX*(y + LY*z);
    for (let x = 1; x < LX-1; x++) {
      const i = row + x;
      if (solid3[i]) continue;
      if (VY[i]/u0*Vref >= thr)
        pts.push((x+0.5)*sceneScale + sceneOffX, (y+0.5)*sceneScale, (z+0.5)*sceneScale + sceneOffZ);
    }
  }
  if (!pts.length) return;
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(pts), 3));
  liftObj = new THREE.Points(g, new THREE.PointsMaterial({
    color: 0x37e08a, size: sceneScale*0.95, transparent: true, opacity: 0.32, depthWrite: false
  }));
  liftObj.visible = $('showLift').checked;
  scene.add(liftObj);
}
/* vertical slice through a launch, along the wind line (textbook lift-band diagram) */
function buildSlice() {
  clearObj(sliceObj); sliceObj = null;
  const sel = +$('sliceSel').value;
  if (sel < 0 || !frames.length || category !== 'terrain' || !terra || !terra.markers[sel]) return;
  const m = terra.markers[sel];
  const a = parseFloat($('dir3').value)*Math.PI/180, ca = Math.cos(a), sa = Math.sin(a);
  const Vref = vRefMs(), u0 = u03(), thr = sinkThr();
  const cellM = terra.extentM/LX;
  const W2 = 256, H2 = 96;
  const c = document.createElement('canvas'); c.width = W2; c.height = H2;
  const x2 = c.getContext('2d');
  const img = x2.createImageData(W2, H2);
  const planeLen = terra.extentM, planeH = LY*cellM;
  const v = [0,0,0];
  for (let py = 0; py < H2; py++) for (let px2 = 0; px2 < W2; px2++) {
    const s = (px2/(W2-1) - 0.5)*planeLen;
    const wxp = m.x + ca*s, wzp = m.z + sa*s;
    const ym = (1 - py/(H2-1))*planeH;
    const lxr = (wxp + terra.extentM/2)/cellM, lzr = (wzp + terra.extentM/2)/cellM, lyr = ym/cellM;
    const o = (py*W2 + px2)*4;
    if (lxr < 1 || lxr >= LX-1 || lzr < 1 || lzr >= LZ-1 || lyr >= LY-1) { img.data[o+3] = 0; continue; }
    const ii = (lxr|0) + LX*((lyr|0) + LY*(lzr|0));
    if (solid3[ii]) { img.data[o]=20; img.data[o+1]=24; img.data[o+2]=32; img.data[o+3]=235; continue; }
    sampleV3(lxr, lyr, lzr, v);
    const w = v[1]/u0*Vref;
    if (w >= thr)        { img.data[o]=40;  img.data[o+1]=225; img.data[o+2]=120; img.data[o+3]=190; }
    else if (w > 0.15)   { img.data[o]=60;  img.data[o+1]=140; img.data[o+2]=90;  img.data[o+3]=130; }
    else if (w < -thr)   { img.data[o]=70;  img.data[o+1]=90;  img.data[o+2]=230; img.data[o+3]=170; }
    else if (w < -0.15)  { img.data[o]=70;  img.data[o+1]=90;  img.data[o+2]=180; img.data[o+3]=105; }
    else                 { img.data[o]=150; img.data[o+1]=150; img.data[o+2]=150; img.data[o+3]=40;  }
  }
  x2.putImageData(img, 0, 0);
  const tex = new THREE.CanvasTexture(c);
  tex.magFilter = THREE.LinearFilter;
  sliceObj = new THREE.Mesh(
    new THREE.PlaneGeometry(planeLen, planeH),
    new THREE.MeshBasicMaterial({map: tex, transparent: true, side: THREE.DoubleSide, depthWrite: false})
  );
  sliceObj.position.set(m.x, planeH/2, m.z);
  sliceObj.rotation.y = -a;
  scene.add(sliceObj);
}
/* per-launch go/no-go assessment */
function updateVerdicts() {
  const el = $('verdicts');
  if (!frames.length || category !== 'terrain' || !terra || !terra.markers.length) { el.innerHTML = ''; return; }
  const Vref = vRefMs(), u0 = u03(), thr = sinkThr();
  const cellM = terra.extentM/LX;
  const [wx,, wz] = windVec3();
  const wm = Math.hypot(wx, wz), wnx = wx/wm, wnz = wz/wm;
  let html = '<b style="color:#dbe2ee">Launch assessment</b><br>';
  for (const m of terra.markers) {
    const lx = Math.round((m.x + terra.extentM/2)/cellM), lz = Math.round((m.z + terra.extentM/2)/cellM);
    if (lx < 1 || lx >= LX-1 || lz < 1 || lz >= LZ-1) continue;
    let surf = 1;
    for (let y = 1; y < LY-1; y++) if (!solid3[lx + LX*(y + LY*lz)]) { surf = y; break; }
    let maxW = -99, top = -1;
    for (let y = surf; y < LY-1; y++) {
      const w = VY[lx + LX*(y + LY*lz)]/u0*Vref;
      if (w > maxW) maxW = w;
      if (w >= thr) top = y;
    }
    const iw = lx + LX*(Math.min(LY-2, surf+1) + LY*lz);
    const wind = Math.sqrt(VX[iw]*VX[iw] + VY[iw]*VY[iw] + VZ[iw]*VZ[iw])/u0*mph3();
    let rotor = false;
    for (let dz2 = -2; dz2 <= 2 && !rotor; dz2++) for (let dx2 = -2; dx2 <= 2 && !rotor; dx2++)
      for (let y = surf; y < Math.min(LY-1, surf+4); y++) {
        const xx = lx+dx2, zz = lz+dz2;
        if (xx < 1 || xx >= LX-1 || zz < 1 || zz >= LZ-1) continue;
        const i = xx + LX*(y + LY*zz);
        if (!solid3[i] && (VX[i]*wnx + VZ[i]*wnz) < -0.03*wm) { rotor = true; break; }
      }
    const liftFt = top > surf ? Math.round((top - surf)*cellM*3.281) : 0;
    const ico = m.kind === 'lz' ? '🟩' : m.kind === 'launch' ? '🟧' : '🟦';
    html += `${ico} <b style="color:#dbe2ee">${m.name}</b>: ${wind.toFixed(0)} mph` +
      (liftFt > 0 ? ` · lift to ~${liftFt} ft AGL (max +${maxW.toFixed(1)} m/s)` : ' · no soarable lift') +
      (rotor ? ' · <span style="color:#ff5ad2">rotor nearby ⚠</span>' : ' · <span style="color:#5fc3ff">clean ✓</span>') +
      (wind > 22 ? ' · <span style="color:#ffab5f">strong — blow-back risk!</span>' : '') + '<br>';
  }
  el.innerHTML = html;
}

/* ============================================================
   Simulate: precompute with progress + locked canvas
   ============================================================ */
function simulate3() {
  if (computing) return;
  if (category === 'terrain' && !terra) { toast('Load a terrain location first.'); return; }
  invalidate();
  const G = gran();
  if (category === 'terrain') {
    LX = G.tHoriz; LZ = G.tHoriz;
    const cellM = terra.extentM/LX;
    LY = Math.max(14, Math.min(40, Math.ceil((terra.hRange*1.4 + 250)/cellM)));
    sceneScale = cellM; sceneOffX = -terra.extentM/2; sceneOffZ = -terra.extentM/2;
  } else {
    LX = G.sx; LY = G.sy; LZ = G.sz;
    CELL = DX/LX;
    sceneScale = CELL; sceneOffX = -DX/2; sceneOffZ = -DZ/2;
  }
  /* logarithmic wind-gradient profile: slider speed = wind at 10 m AGL */
  {
    const stepM = category === 'terrain' ? terra.extentM/LX : CELL*0.3048;
    const z0 = 0.05, ln0 = Math.log(10/z0);
    FAC = new Float32Array(LY);
    for (let y = 0; y < LY; y++) {
      const zm = Math.max(0.6, (y + 0.5)*stepM);
      FAC[y] = Math.min(1.6, Math.max(0.25, Math.log(zm/z0)/ln0));
    }
  }
  alloc3();
  buildSolid();
  initFluid3();
  buildArrowField();
  ensureArrowObject();
  lineObj.visible = true;
  frames = []; rotorVols = []; playing = false; playT = 0;
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
      frames = []; rotorVols = [];
      $('st3state').textContent = 'cancelled';
      if (lineObj) lineObj.visible = false;
      return;
    }
    playing = true; playT = 0;
    $('st3state').textContent = cancelled ? 'playing (partial)' : 'playing animation';
    buildLiftBand();
    buildSlice();
    updateVerdicts();
    toast(`3D CFD done — green = lift band (soarable), magenta arrows = rotor.`);
  };
  requestAnimationFrame(chunk);
}
function lock(on) {
  $('ov3d').classList.toggle('show', on);
  for (const id of ['sim3Btn','locGo','cat3Shapes','cat3Terrain','del3','mesh3Res','siteSel','liveWindBtn','sliceSel']) $(id).disabled = on;
}
function invalidate() {
  frames = []; rotorVols = []; playing = false;
  if (lineObj) lineObj.visible = false;
  clearObj(liftObj); liftObj = null;
  clearObj(sliceObj); sliceObj = null;
  $('st3rotor').textContent = '–';
  $('verdicts').innerHTML = '';
  if ($('st3state').textContent.startsWith('playing')) $('st3state').textContent = 'idle (edited — re-simulate)';
}

/* ============================================================
   UI bindings & pointer controls
   ============================================================ */
function bindUI() {
  bindAutocomplete();
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
  $('cat3Shapes').addEventListener('click', () => { if (!computing) setCategory('shapes'); });
  $('cat3Terrain').addEventListener('click', () => { if (!computing) setCategory('terrain'); });
  $('locGo').addEventListener('click', async () => {
    if (computing) return;
    if (chosenLoc) { loadTerrainAt(chosenLoc); return; }
    const q = $('locName').value.trim() || 'Mussel Rock';
    $('terrStatus').textContent = 'Searching "' + q + '"…';
    const loc = await geocode(q);
    if (!loc) { $('terrStatus').textContent = 'Location not found. Try another name.'; return; }
    loadTerrainAt(loc);
  });
  $('mesh3Res').addEventListener('input', () => {
    invalidate();
    const G = gran();
    $('st3grid').textContent = category === 'terrain'
      ? `${G.tHoriz}×~24×${G.tHoriz} (next run)`
      : `${G.sx}×${G.sy}×${G.sz} (next run)`;
  });
  /* pilot tools */
  $('siteSel').addEventListener('input', () => { if (!computing && $('siteSel').value) loadSite($('siteSel').value); });
  $('liveWindBtn').addEventListener('click', () => { if (!computing) liveWind(); });
  $('sinkRate').addEventListener('input', () => {
    $('sinkVal').textContent = (+$('sinkRate').value).toFixed(2) + ' m/s';
    if (frames.length) { buildLiftBand(); buildSlice(); updateVerdicts(); }
  });
  $('showLift').addEventListener('input', () => { if (liftObj) liftObj.visible = $('showLift').checked; });
  $('sliceSel').addEventListener('input', () => { if (frames.length) buildSlice(); });
  const dirLabel = () => {
    const D = Math.round(compassFrom(parseFloat($('dir3').value)));
    $('dir3Val').textContent = `from ${D}° ${DIRN[Math.round(D/45) % 8]}`;
  };
  $('dir3').addEventListener('input', () => {
    dirLabel();
    const a = parseFloat($('dir3').value)*Math.PI/180;
    windArrow.setDirection(new THREE.Vector3(Math.cos(a), 0, Math.sin(a)));
    invalidate();
  });
  dirLabel();
  $('spd3').addEventListener('input', () => {
    $('spd3Val').textContent = $('spd3').value + ' MPH';
    invalidate();
  });
  $('sim3Btn').addEventListener('click', simulate3);
  $('stop3Btn').addEventListener('click', () => {
    if (computing) { cancelReq = true; return; }
    playing = false;
    if (lineObj) lineObj.visible = false;
    $('st3state').textContent = 'idle';
  });
  $('ovCancel').addEventListener('click', () => { cancelReq = true; });
  const Aang = 0.12;
  $('cYawL').addEventListener('click', () => camYaw(Aang));
  $('cYawR').addEventListener('click', () => camYaw(-Aang));
  $('cPitchU').addEventListener('click', () => camPitch(Aang));
  $('cPitchD').addEventListener('click', () => camPitch(-Aang));
  $('cRollL').addEventListener('click', () => camRoll(Aang));
  $('cRollR').addEventListener('click', () => camRoll(-Aang));
  $('cIn').addEventListener('click', () => camMove(0, 0, -moveStep()*2));
  $('cOut').addEventListener('click', () => camMove(0, 0, moveStep()*2));
  $('cHome').addEventListener('click', () => camGoHome(false));
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
  category = cat;
  $('cat3Shapes').classList.toggle('active', cat === 'shapes');
  $('cat3Terrain').classList.toggle('active', cat === 'terrain');
  $('pal3wrap').style.display = cat === 'shapes' ? '' : 'none';
  $('terrWrap').style.display = cat === 'terrain' ? '' : 'none';
  shapesGroup.visible = cat === 'shapes';
  terrainGroup.visible = cat === 'terrain';
  select3(null);
  invalidate();
  camGoHome(true);
  if (cat === 'terrain' && terra) {
    windArrow.position.set(-terra.extentM/2, terra.hRange*1.3, -terra.extentM/2);
    windArrow.setLength(terra.extentM*0.08, terra.extentM*0.02, terra.extentM*0.012);
  } else {
    windArrow.position.set(-DX/2, DY*0.9, -DZ/2);
    windArrow.setLength(3 + mph3()*0.25, 2, 1.2);
  }
}
})();

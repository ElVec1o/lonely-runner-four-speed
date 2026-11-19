// four_wp0: certificate generator + checker for the n = 4 (four-speed, theta = 1/4) transference tree.
// Written 2026-11-16. Exact integers only (i64/i128); NO floats anywhere.
// Format name: cert4 v1.
//   depth-1 node  T1 : sorted nonneg primitive h, 9|h|^2 < 148, |h|^2 >= 2  (15 nodes)
//   child step       : t in Z^3 (coordinates b_j . y), canonical +-t, filters F1..F5 (MID = frozen), one leaf per t
//   leaf             : L2 = Z h + Z y ; non-critical (strict witness c2 > 1/4) or critical (K2 inside a critical torus)
//   lines            : primitive v in K2 = L2^perp, window tests, global time list, residual list T5
use std::collections::HashSet;
use std::env;
use std::fs;

type V = [i64; 4];

pub fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
pub fn isqrt(n: i128) -> i128 {
    if n <= 0 {
        return 0;
    }
    let mut x = n;
    let mut y = (x + 1) / 2;
    while y < x {
        x = y;
        y = (x + n / x) / 2;
    }
    x
}
fn dot(a: &V, b: &V) -> i64 {
    (0..4).map(|i| a[i] * b[i]).sum()
}
fn wmin(x: &V, w: i64) -> i64 {
    let mut m = i64::MAX;
    for i in 0..4 {
        let r = x[i].rem_euclid(w);
        m = m.min(r.min(w - r));
    }
    m
}

// ---------------- signed permutations (g v)_i = eps_i * v[sigma_i] ----------------
fn all_sp() -> Vec<([usize; 4], [i64; 4])> {
    let mut o = vec![];
    for a in 0..4 {
        for b in 0..4 {
            for c in 0..4 {
                for d in 0..4 {
                    if a != b && a != c && a != d && b != c && b != d && c != d {
                        for s in 0..16 {
                            let e = [(s & 1) as i64 * -2 + 1, ((s >> 1) & 1) as i64 * -2 + 1, ((s >> 2) & 1) as i64 * -2 + 1, ((s >> 3) & 1) as i64 * -2 + 1];
                            o.push(([a, b, c, d], e));
                        }
                    }
                }
            }
        }
    }
    o
}
fn sp_act(g: &([usize; 4], [i64; 4]), v: &V) -> V {
    [g.1[0] * v[g.0[0]], g.1[1] * v[g.0[1]], g.1[2] * v[g.0[2]], g.1[3] * v[g.0[3]]]
}
// critical torus equations E_ck u = 0: ck=0: u1=2u0,u2=3u0 ; ck=1: u2=u0+u1, u3=2u0+u1
fn crit_eq(ck: i64, u: &V) -> bool {
    if ck == 0 {
        u[1] == 2 * u[0] && u[2] == 3 * u[0]
    } else {
        u[2] == u[0] + u[1] && u[3] == 2 * u[0] + u[1]
    }
}

// ---------------- unimodular column reduction ----------------
type M4 = [[i64; 4]; 4];
fn ident() -> M4 {
    let mut m = [[0; 4]; 4];
    for i in 0..4 {
        m[i][i] = 1;
    }
    m
}
// returns (V, Vinv) with rows*V lower triangular (pivot (r,r)), V unimodular
fn colreduce(rows: &[V]) -> (M4, M4) {
    let mut vm = ident();
    let mut vi = ident();
    let hc = |vm: &M4, r: usize, c: usize| -> i64 { (0..4).map(|k| rows[r][k] * vm[k][c]).sum() };
    for r in 0..rows.len() {
        loop {
            let mut best: Option<usize> = None;
            for c in r..4 {
                let x = hc(&vm, r, c);
                if x != 0 && best.map_or(true, |b| x.abs() < hc(&vm, r, b).abs()) {
                    best = Some(c);
                }
            }
            let p = best.expect("rank deficient");
            if p != r {
                for k in 0..4 {
                    let t = vm[k][r];
                    vm[k][r] = vm[k][p];
                    vm[k][p] = t;
                }
                vi.swap(r, p);
            }
            let piv = hc(&vm, r, r);
            let mut done = true;
            for c in r + 1..4 {
                let x = hc(&vm, r, c);
                if x != 0 {
                    let f = x.div_euclid(piv);
                    for k in 0..4 {
                        vm[k][c] -= f * vm[k][r];
                    }
                    for k in 0..4 {
                        vi[r][k] += f * vi[c][k];
                    }
                    if hc(&vm, r, c) != 0 {
                        done = false;
                    }
                }
            }
            if done {
                break;
            }
        }
        if hc(&vm, r, r) < 0 {
            for k in 0..4 {
                vm[k][r] = -vm[k][r];
                vi[r][k] = -vi[r][k];
            }
        }
    }
    (vm, vi)
}
fn col(m: &M4, c: usize) -> V {
    [m[0][c], m[1][c], m[2][c], m[3][c]]
}

// ---------------- derived data of a depth-1 node ----------------
#[derive(Clone)]
pub struct T1 {
    pub h: V,
    pub x1: V,
    pub w1: i64,
    pub b: [V; 3],
    pub r: [V; 3],
    pub s: V,
}
pub struct NodeD {
    pub g1: i64,
    pub adj: [[i64; 3]; 3],
    pub det: i64,
    pub a1: i64, // 4 wmin - W1
    pub bn: i128,
    pub bd: i128,
    pub tmax: [i64; 3],
}
fn gram3(b: &[V; 3]) -> [[i64; 3]; 3] {
    let mut a = [[0; 3]; 3];
    for i in 0..3 {
        for j in 0..3 {
            a[i][j] = dot(&b[i], &b[j]);
        }
    }
    a
}
fn node_d(n: &T1) -> NodeD {
    let a = gram3(&n.b);
    let mut adj = [[0i64; 3]; 3];
    for i in 0..3 {
        for j in 0..3 {
            let (i1, i2) = ((i + 1) % 3, (i + 2) % 3);
            let (j1, j2) = ((j + 1) % 3, (j + 2) % 3);
            adj[j][i] = a[i1][j1] * a[i2][j2] - a[i1][j2] * a[i2][j1]; // cofactor (i,j) transposed; symmetric anyway
        }
    }
    let det = a[0][0] * adj[0][0] + a[0][1] * adj[1][0] + a[0][2] * adj[2][0];
    let wm = wmin(&n.x1, n.w1);
    let a1 = 4 * wm - n.w1;
    let bn = 28 * (n.w1 as i128) * (n.w1 as i128);
    let bd = 3 * (a1 as i128) * (a1 as i128);
    let mut tmax = [0; 3];
    for j in 0..3 {
        tmax[j] = isqrt(bn * (a[j][j] as i128) / bd) as i64;
    }
    NodeD { g1: dot(&n.h, &n.h), adj, det, a1, bn, bd, tmax }
}
fn qform(nd: &NodeD, t: &[i64; 3]) -> i64 {
    let mut s = 0;
    for i in 0..3 {
        for j in 0..3 {
            s += t[i] * nd.adj[i][j] * t[j];
        }
    }
    s
}

// ---------------- t-pass filters (the frozen MID spec) ----------------
#[derive(Default, Clone, Copy)]
pub struct Funnel {
    pub box_pts: u64,
    pub canon: u64,
    pub radius: u64,
    pub prim: u64,
    pub noei: u64,
    pub greedy: u64, // only meaningful when greedy requested
    pub k0: u64,
    pub ratio: u64,
}
#[derive(Clone, Copy, PartialEq)]
pub enum Var {
    Mid,
    Full,
    Mini,
}
fn greedy_ok(h: &V, y: &V) -> bool {
    // h shortest nonzero vector of Zh+Zy (Gauss reduction)
    let mut b = [*h, *y];
    loop {
        if dot(&b[0], &b[0]) > dot(&b[1], &b[1]) {
            b.swap(0, 1);
        }
        let n0 = dot(&b[0], &b[0]) as i128;
        let tt = dot(&b[0], &b[1]) as i128;
        let m = (2 * tt + n0).div_euclid(2 * n0);
        if m == 0 {
            break;
        }
        for k in 0..4 {
            b[1][k] -= (m as i64) * b[0][k];
        }
    }
    dot(&b[0], &b[0]) >= dot(h, h)
}
fn lift(n: &T1, t: &[i64; 3]) -> V {
    let mut y = [0i64; 4];
    for j in 0..3 {
        for k in 0..4 {
            y[k] += t[j] * n.r[j][k];
        }
    }
    y
}
fn passes(n: &T1, nd: &NodeD, t: &[i64; 3], var: Var, f: &mut Funnel) -> bool {
    f.box_pts += 1;
    let first = t.iter().find(|&&x| x != 0);
    match first {
        Some(&x) if x > 0 => {}
        _ => return false,
    }
    f.canon += 1;
    let g2 = qform(nd, t);
    if !((g2 as i128) * nd.bd < nd.bn * (nd.det as i128)) {
        return false;
    }
    f.radius += 1;
    if gcd(gcd(t[0], t[1]), t[2]) != 1 {
        return false;
    }
    f.prim += 1;
    for i in 0..4 {
        let e = [n.b[0][i], n.b[1][i], n.b[2][i]];
        let c0 = e[1] * t[2] - e[2] * t[1];
        let c1 = e[2] * t[0] - e[0] * t[2];
        let c2 = e[0] * t[1] - e[1] * t[0];
        if c0 == 0 && c1 == 0 && c2 == 0 {
            return false;
        }
    }
    f.noei += 1;
    if var == Var::Full {
        let y = lift(n, t);
        if !greedy_ok(&n.h, &y) {
            return false;
        }
    }
    f.greedy += 1;
    if var != Var::Mini {
        let g1 = nd.g1 as i128;
        let g2 = g2 as i128;
        if !(3 * g1 * g2 < 12 * g2 + 28 * g1 * g1) {
            return false;
        }
        f.k0 += 1;
        if 4 * g2 < 3 * g1 * g1 {
            return false;
        }
        f.ratio += 1;
    }
    true
}

// ---------------- leaf record ----------------
#[derive(Clone)]
pub struct Leaf {
    pub t: [i64; 3],
    pub y: V,
    pub kind: i64, // 0 noncritical, 1 critical
    pub x2: V,
    pub w2: i64,
    pub k: [V; 2],
    pub q: [V; 2],
    pub p: [[i64; 2]; 4],
    pub ck: i64,
    pub sg: [i64; 4],
    pub ep: [i64; 4],
}
pub const LEAF_N: usize = 46;
fn leaf_to_ints(l: &Leaf) -> Vec<i32> {
    let mut v: Vec<i64> = vec![];
    v.extend_from_slice(&l.t);
    v.extend_from_slice(&l.y);
    v.push(l.kind);
    v.extend_from_slice(&l.x2);
    v.push(l.w2);
    v.extend_from_slice(&l.k[0]);
    v.extend_from_slice(&l.k[1]);
    v.extend_from_slice(&l.q[0]);
    v.extend_from_slice(&l.q[1]);
    for a in 0..4 {
        v.push(l.p[a][0]);
        v.push(l.p[a][1]);
    }
    v.push(l.ck);
    v.extend_from_slice(&l.sg);
    v.extend_from_slice(&l.ep);
    assert_eq!(v.len(), LEAF_N);
    v.into_iter().map(|x| i32::try_from(x).expect("field exceeds i32")).collect()
}
fn leaf_from_ints(v: &[i32]) -> Leaf {
    let g = |i: usize| v[i] as i64;
    let v4 = |i: usize| [g(i), g(i + 1), g(i + 2), g(i + 3)];
    Leaf {
        t: [g(0), g(1), g(2)],
        y: v4(3),
        kind: g(7),
        x2: v4(8),
        w2: g(12),
        k: [v4(13), v4(17)],
        q: [v4(21), v4(25)],
        p: [[g(29), g(30)], [g(31), g(32)], [g(33), g(34)], [g(35), g(36)]],
        ck: g(37),
        sg: v4(38),
        ep: v4(42),
    }
}

// M(L2) by grid: max over (u,w) in (1/D)Z^2, D <= Dmax of min_i ||l_i . (u,w)||, witness x = k0 U + k1 V, W = D
fn m2_grid(k: &[V; 2]) -> (i64, i64, V, i64) {
    let mut maxl = 1i64;
    let mut maxminor = 1i64;
    for i in 0..4 {
        maxl = maxl.max(k[0][i].abs()).max(k[1][i].abs());
        for j in i + 1..4 {
            maxminor = maxminor.max((k[0][i] * k[1][j] - k[0][j] * k[1][i]).abs());
        }
    }
    let dmax = (2 * maxl).max(3 * maxminor) + 2;
    let (mut bn, mut bdn) = (0i64, 1i64);
    let mut bw = (0i64, 0i64, 1i64);
    for d in 2..=dmax {
        for u in 0..d {
            for v in 0..d {
                let mut mn = i64::MAX;
                let mut ok = true;
                for i in 0..4 {
                    let s = (k[0][i] * u + k[1][i] * v).rem_euclid(d);
                    let m = s.min(d - s);
                    // need m/d > bn/bdn  to improve; prune if m*bdn <= bn*d
                    if m * bdn <= bn * d {
                        ok = false;
                        break;
                    }
                    mn = mn.min(m);
                }
                if ok {
                    bn = mn;
                    bdn = d;
                    bw = (u, v, d);
                }
            }
        }
    }
    let x = [0, 1, 2, 3].map(|i| k[0][i] * bw.0 + k[1][i] * bw.1);
    (bn, bdn, x, bw.2)
}

fn build_leaf(n: &T1, t: &[i64; 3], sps: &Vec<([usize; 4], [i64; 4])>) -> (Leaf, i64, i64) {
    let y = lift(n, t);
    let (vm, vi) = colreduce(&[n.h, y]);
    // S = rows*V first two columns, lower triangular unimodular; P = V[:, :2] S^{-1}
    let hv = |r: usize, c: usize| -> i64 { (0..4).map(|k| [n.h, y][r][k] * vm[k][c]).sum() };
    let (s00, s10, s11) = (hv(0, 0), hv(1, 0), hv(1, 1));
    assert!(s00 == 1 && s11 == 1 && hv(0, 1) == 0, "L2 not saturated");
    // S = [[1,0],[s10,1]] ; S^-1 = [[1,0],[-s10,1]]
    let mut p = [[0i64; 2]; 4];
    for a in 0..4 {
        p[a][0] = vm[a][0] - vm[a][1] * s10;
        p[a][1] = vm[a][1];
    }
    let mut k = [col(&vm, 2), col(&vm, 3)];
    let mut q = [vi[2], vi[3]];
    // Gauss reduction of (k0,k1) with unimodular tracking: k'_i = sum_m M[i][m] k_m
    let mut mt = [[1i64, 0], [0, 1]];
    loop {
        if dot(&k[0], &k[0]) > dot(&k[1], &k[1]) {
            k.swap(0, 1);
            mt.swap(0, 1);
        }
        let n0 = dot(&k[0], &k[0]) as i128;
        let tt = dot(&k[0], &k[1]) as i128;
        let m = ((2 * tt + n0).div_euclid(2 * n0)) as i64;
        if m == 0 {
            break;
        }
        for c in 0..4 {
            k[1][c] -= m * k[0][c];
        }
        for c in 0..2 {
            mt[1][c] -= m * mt[0][c];
        }
    }
    // Q' = M^{-T} Q ; M unimodular: M^{-1} = adj/det
    let det = mt[0][0] * mt[1][1] - mt[0][1] * mt[1][0];
    assert!(det == 1 || det == -1);
    let mi = [[mt[1][1] * det, -mt[0][1] * det], [-mt[1][0] * det, mt[0][0] * det]];
    // Q'[i] = sum_m (M^{-1})[m][i] Q[m]
    let qo = q;
    for i in 0..2 {
        for c in 0..4 {
            q[i][c] = mi[0][i] * qo[0][c] + mi[1][i] * qo[1][c];
        }
    }
    // identity check B Q + P H = I
    for a in 0..4 {
        for c in 0..4 {
            let v = k[0][a] * q[0][c] + k[1][a] * q[1][c] + p[a][0] * n.h[c] + p[a][1] * y[c];
            assert_eq!(v, if a == c { 1 } else { 0 }, "B Q + P H != I");
        }
    }
    // critical identification
    let mut leaf = Leaf { t: *t, y, kind: 0, x2: [0; 4], w2: 1, k, q, p, ck: 0, sg: [0, 1, 2, 3], ep: [1, 1, 1, 1] };
    'outer: for ck in 0..2 {
        for g in sps.iter() {
            if crit_eq(ck, &sp_act(g, &k[0])) && crit_eq(ck, &sp_act(g, &k[1])) {
                leaf.kind = 1;
                leaf.ck = ck;
                leaf.sg = [g.0[0] as i64, g.0[1] as i64, g.0[2] as i64, g.0[3] as i64];
                leaf.ep = g.1;
                break 'outer;
            }
        }
    }
    let (mn, md, x, w) = m2_grid(&k);
    if leaf.kind == 0 {
        assert!(4 * mn > md, "noncritical leaf with M2 <= 1/4: {:?}", t);
        leaf.x2 = x;
        leaf.w2 = w;
        assert_eq!(wmin(&x, w) * md, mn * w);
    } else {
        assert!(4 * mn == md, "critical leaf with M2 != 1/4 ({}/{})", mn, md);
    }
    (leaf, mn, md)
}

// ---------------- lines ----------------
pub fn time_list(qmax: i64) -> Vec<(i64, i64)> {
    let mut o = vec![];
    for q in 2..=qmax {
        for a in 1..=q / 2 {
            if gcd(a, q) == 1 {
                o.push((a, q));
            }
        }
    }
    o
}
fn time_ok(v: &V, a: i64, q: i64) -> bool {
    for i in 0..4 {
        let r = (v[i].abs() * a).rem_euclid(q);
        if 4 * r.min(q - r) < q {
            return false;
        }
    }
    true
}
pub fn ml_max(v: &V) -> (i64, i64) {
    // exact ML = max over t = k/L, L = |v_i|+|v_j|, ALL k, of min_i ||v_i t|| ; returns (num, den)
    let a: Vec<i64> = v.iter().map(|x| x.abs()).collect();
    let (mut bn, mut bd) = (0i64, 1i64);
    for i in 0..4 {
        for j in i..4 {
            let l = a[i] + a[j];
            for k in 0..l {
                let mut m = i64::MAX;
                for t in 0..4 {
                    let r = (a[t] * k).rem_euclid(l);
                    m = m.min(r.min(l - r));
                }
                if m * bd > bn * l {
                    bn = m;
                    bd = l;
                }
            }
        }
    }
    (bn, bd)
}
pub struct Win {
    pub g1: i128,
    pub g2: i128,
    pub w1: i128,
    pub a1: i128,
    pub w2: i128,
    pub a2: i128,
}
static PLANT_LO: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(0);
static PLANT_HI: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);
fn window_ok(w: &Win, n: i128) -> bool {
    let lo_n: i128 = if PLANT_LO.load(std::sync::atomic::Ordering::Relaxed) == 1 { 9 } else { 3 };
    let lo_d: i128 = if PLANT_LO.load(std::sync::atomic::Ordering::Relaxed) == 1 { 10 } else { 4 };
    let hi_f = PLANT_HI.load(std::sync::atomic::Ordering::Relaxed) as i128;
    lo_d * w.g1 * n >= lo_n * w.g2 * w.g2 * 4 / 4
        && w.a2 * w.a2 * n * hi_f < 4 * w.w2 * w.w2 * w.g2
        && w.a1 * w.a1 * w.g2 * n < 4 * w.w1 * w.w1 * (w.g1 * n + w.g2 * w.g2)
        && w.g1 * w.g2 * n < 4 * (w.g2 * n + w.g1 * w.g1 * n + w.g1 * w.g2 * w.g2)
}
#[derive(Default, Clone)]
pub struct LineStats {
    pub box_iters: u64,
    pub prim: u64,
    pub in_window: u64,
    pub nonzero: u64,
    pub checked: u64, // nonzero + distinct abs
    pub witnessed: u64,
    pub resid: u64,
}
// enumerate lines of one noncritical leaf; call f(sorted abs tuple, is_witnessed)
fn leaf_lines(nd: &NodeD, n1: &T1, l: &Leaf, tl: &[(i64, i64)], st: &mut LineStats, mut f: impl FnMut(V, bool)) {
    let g1 = nd.g1 as i128;
    let y = &l.y;
    let p = dot(&n1.h, y) as i128;
    let g2 = g1 * (dot(y, y) as i128) - p * p;
    let wm2 = wmin(&l.x2, l.w2);
    let w = Win { g1, g2, w1: n1.w1 as i128, a1: nd.a1 as i128, w2: l.w2 as i128, a2: (4 * wm2 - l.w2) as i128 };
    assert!(w.a2 > 0);
    let a = dot(&l.k[0], &l.k[0]) as i128;
    let b = dot(&l.k[0], &l.k[1]) as i128;
    let d = dot(&l.k[1], &l.k[1]) as i128;
    let dd = a * d - b * b;
    assert!(dd > 0);
    let nmax = (4 * w.w2 * w.w2 * w.g2 - 1) / (w.a2 * w.a2);
    let zb = isqrt(a * nmax / dd) as i64;
    let xb = isqrt(d * nmax / dd) as i64;
    for z in 0..=zb {
        let (xlo, xhi) = if z == 0 { (1, 1) } else { (-xb, xb) };
        for x in xlo..=xhi {
            st.box_iters += 1;
            if gcd(x, z) != 1 {
                continue;
            }
            st.prim += 1;
            let nn = a * (x as i128) * (x as i128) + 2 * b * (x as i128) * (z as i128) + d * (z as i128) * (z as i128);
            if !window_ok(&w, nn) {
                continue;
            }
            st.in_window += 1;
            let v: V = [0, 1, 2, 3].map(|i| x * l.k[0][i] + z * l.k[1][i]);
            if v.iter().any(|&e| e == 0) {
                continue;
            }
            st.nonzero += 1;
            let mut ab = [v[0].abs(), v[1].abs(), v[2].abs(), v[3].abs()];
            ab.sort();
            if ab[0] == ab[1] || ab[1] == ab[2] || ab[2] == ab[3] {
                continue;
            }
            st.checked += 1;
            let ok = tl.iter().any(|&(a, q)| time_ok(&ab, a, q));
            if ok {
                st.witnessed += 1;
            } else {
                st.resid += 1;
            }
            f(ab, ok);
        }
    }
}

// ---------------- T5 ----------------
#[derive(Clone)]
pub struct T5 {
    pub v: V,
    pub kind: i64,
    pub a: i64,
    pub q: i64,
    pub mln: i64,
    pub mld: i64,
}
fn make_t5(v: V) -> T5 {
    let (mn, md) = ml_max(&v);
    if 4 * mn < md {
        T5 { v, kind: 0, a: 0, q: 1, mln: mn, mld: md }
    } else {
        // ML >= 1/4: exhibit a time (reduced a/q, q up to 2000)
        for q in 2..=2000 {
            for a in 1..=q / 2 {
                if gcd(a, q) == 1 && time_ok(&v, a, q) {
                    return T5 { v, kind: 1, a, q, mln: mn, mld: md };
                }
            }
        }
        panic!("no extra time found for {:?}", v);
    }
}

// ---------------- I/O ----------------
fn write_ints(path: &str, v: &[i32]) {
    let mut b = Vec::with_capacity(v.len() * 4);
    for x in v {
        b.extend_from_slice(&x.to_le_bytes());
    }
    fs::write(path, b).unwrap();
}
fn read_ints(path: &str) -> Vec<i32> {
    let b = fs::read(path).unwrap();
    b.chunks(4).map(|c| i32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect()
}
fn t1_to_ints(n: &T1) -> Vec<i32> {
    let mut v: Vec<i64> = vec![];
    v.extend_from_slice(&n.h);
    v.extend_from_slice(&n.x1);
    v.push(n.w1);
    for j in 0..3 {
        v.extend_from_slice(&n.b[j]);
    }
    for j in 0..3 {
        v.extend_from_slice(&n.r[j]);
    }
    v.extend_from_slice(&n.s);
    assert_eq!(v.len(), 37);
    v.into_iter().map(|x| x as i32).collect()
}
fn t1_from_ints(v: &[i32]) -> T1 {
    let g = |i: usize| v[i] as i64;
    let v4 = |i: usize| [g(i), g(i + 1), g(i + 2), g(i + 3)];
    T1 { h: v4(0), x1: v4(4), w1: g(8), b: [v4(9), v4(13), v4(17)], r: [v4(21), v4(25), v4(29)], s: v4(33) }
}
fn t5_to_ints(t: &T5) -> Vec<i32> {
    let mut v: Vec<i32> = t.v.iter().map(|&x| x as i32).collect();
    v.extend_from_slice(&[t.kind as i32, t.a as i32, t.q as i32, t.mln as i32, t.mld as i32]);
    v
}
fn t5_from_ints(v: &[i32]) -> T5 {
    T5 { v: [v[0] as i64, v[1] as i64, v[2] as i64, v[3] as i64], kind: v[4] as i64, a: v[5] as i64, q: v[6] as i64, mln: v[7] as i64, mld: v[8] as i64 }
}

// ---------------- depth-1 list ----------------
fn t1_candidates() -> Vec<V> {
    let mut o = vec![];
    for a0 in 0..=4i64 {
        for a1 in a0..=4 {
            for a2 in a1..=4 {
                for a3 in a2..=4 {
                    let h = [a0, a1, a2, a3];
                    let g = dot(&h, &h);
                    if g >= 2 && 9 * g < 148 && gcd(gcd(a0, a1), gcd(a2, a3)) == 1 {
                        o.push(h);
                    }
                }
            }
        }
    }
    o
}
fn short_basis(h: &V) -> [V; 3] {
    // shortest triple of vectors (entries in [-5,5]) in h^perp spanning the saturated lattice
    let mut cand: Vec<V> = vec![];
    for a in -5..=5i64 {
        for b in -5..=5i64 {
            for c in -5..=5i64 {
                for d in -5..=5i64 {
                    let u = [a, b, c, d];
                    if (a, b, c, d) != (0, 0, 0, 0) && dot(&u, h) == 0 {
                        cand.push(u);
                    }
                }
            }
        }
    }
    cand.sort_by_key(|u| (dot(u, u), *u));
    let n = cand.len().min(120);
    let mut best: Option<([V; 3], i64)> = None;
    for i in 0..n {
        for j in i + 1..n {
            for k in j + 1..n {
                let tot = dot(&cand[i], &cand[i]) + dot(&cand[j], &cand[j]) + dot(&cand[k], &cand[k]);
                if best.as_ref().map_or(false, |b| tot >= b.1) {
                    continue;
                }
                // gcd of 3x3 minors == 1  <=> saturated rank 3
                let m = [cand[i], cand[j], cand[k]];
                let mut g = 0;
                for skip in 0..4 {
                    let cols: Vec<usize> = (0..4).filter(|&c| c != skip).collect();
                    let det = m[0][cols[0]] * (m[1][cols[1]] * m[2][cols[2]] - m[1][cols[2]] * m[2][cols[1]])
                        - m[0][cols[1]] * (m[1][cols[0]] * m[2][cols[2]] - m[1][cols[2]] * m[2][cols[0]])
                        + m[0][cols[2]] * (m[1][cols[0]] * m[2][cols[1]] - m[1][cols[1]] * m[2][cols[0]]);
                    g = gcd(g, det);
                }
                if g == 1 {
                    best = Some((m, tot));
                }
            }
        }
    }
    best.expect("no short basis").0
}
fn build_t1(h: V) -> T1 {
    let l1: i64 = h.iter().map(|x| x.abs()).sum();
    let (x1, w1) = if l1 % 2 == 0 { ([1, 1, 1, 1], 2) } else { ([l1 - 1; 4], 2 * l1) };
    let (vm, _) = colreduce(&[h]);
    let s = col(&vm, 0);
    assert_eq!(dot(&h, &s), 1);
    let b = short_basis(&h);
    // right inverse of b via column reduction: b V2 = [S 0]; r = V2[:, :3] S^{-1}
    let (v2, _) = colreduce(&b);
    let sm = |i: usize, j: usize| -> i64 { (0..4).map(|k| b[i][k] * v2[k][j]).sum() };
    // S lower triangular 3x3 with unit diagonal; invert by forward substitution
    let mut si = [[0i64; 3]; 3];
    for c in 0..3 {
        for i in 0..3 {
            let mut acc = if i == c { 1 } else { 0 };
            for j in 0..i {
                acc -= sm(i, j) * si[j][c];
            }
            assert_eq!(sm(i, i), 1);
            si[i][c] = acc;
        }
    }
    let mut r = [[0i64; 4]; 3];
    for c in 0..3 {
        for a in 0..4 {
            r[c][a] = (0..3).map(|j| v2[a][j] * si[j][c]).sum();
        }
    }
    for i in 0..3 {
        for k in 0..3 {
            assert_eq!(dot(&b[i], &r[k]), if i == k { 1 } else { 0 });
        }
        assert_eq!(dot(&b[i], &h), 0);
    }
    T1 { h, x1, w1, b, r, s }
}

// ---------------- generator ----------------
struct Plant {
    rad_div: i128,
    lo90: bool,
    c37: bool,
}
fn gen(dir: &str, var: Var, qmax: i64, plant: &str) {
    let _ = Plant { rad_div: 1, lo90: false, c37: false };
    fs::create_dir_all(dir).unwrap();
    let sps = all_sp();
    let mut reps = t1_candidates();
    if plant == "t1drop" {
        reps.remove(3);
    }
    if plant == "c37" {
        reps.retain(|h| 9 * dot(h, h) < 100); // wrong constant: bound 100/9 instead of 148/9
    }
    println!("depth1 reps: {}", reps.len());
    let nodes: Vec<T1> = reps.iter().map(|h| build_t1(*h)).collect();
    let mut t1ints = vec![];
    for n in &nodes {
        t1ints.extend(t1_to_ints(n));
    }
    write_ints(&format!("{}/t1.bin", dir), &t1ints);
    let tl = time_list(qmax);
    let mut tot = Funnel::default();
    let mut leaves_total = 0u64;
    let mut crit = 0u64;
    let mut min_margin = (1i64, 1i64); // M2 - 1/4 as fraction over non-critical leaves
    let mut st = LineStats::default();
    let mut unw: HashSet<V> = HashSet::new();
    let mut per_node = vec![];
    let mut perleaf: Vec<(u64, u64)> = vec![]; // (checked lines, box iters) of noncritical leaves in stream order
    let mut fmax = vec![0i64; LEAF_N];
    let mut t1max = 0i64;
    for (ni, n) in nodes.iter().enumerate() {
        let nd = node_d(n);
        assert_eq!(nd.det, nd.g1, "det Gram(b) != |h|^2");
        let mut f = Funnel::default();
        let mut ints: Vec<i32> = vec![];
        let mut cnt = 0u64;
        let mut ncrit = 0u64;
        for t0 in -nd.tmax[0]..=nd.tmax[0] {
            for t1 in -nd.tmax[1]..=nd.tmax[1] {
                for t2 in -nd.tmax[2]..=nd.tmax[2] {
                    let t = [t0, t1, t2];
                    let mut pass = passes(n, &nd, &t, var, &mut f);
                    if plant == "rad20" && pass {
                        let g2 = qform(&nd, &t) as i128;
                        if !(g2 * nd.bd * 20 < nd.bn * (nd.det as i128)) {
                            pass = false;
                        }
                    }
                    if !pass {
                        continue;
                    }
                    let (mut leaf, mn, md) = build_leaf(n, &t, &sps);
                    cnt += 1;
                    if leaf.kind == 1 {
                        ncrit += 1;
                    } else {
                        // margin M2 - 1/4 = (4 mn - md)/(4 md)
                        let (a, b) = (4 * mn - md, 4 * md);
                        if a * min_margin.1 < min_margin.0 * b {
                            min_margin = (a, b);
                        }
                        if plant == "lo90" {
                            // wrong: nothing in the record changes; the planted fault is in the line stage below
                        }
                        let mut stl = LineStats::default();
                        leaf_lines(&nd, n, &leaf, &tl, &mut stl, |ab, ok| {
                            if !ok {
                                unw.insert(ab);
                            }
                        });
                        if plant == "lo90" {
                            // drop residual tuples found only in the lower tenth of the window: emulate by removing nothing here
                        }
                        perleaf.push((stl.checked, stl.box_iters));
                        st.box_iters += stl.box_iters;
                        st.prim += stl.prim;
                        st.in_window += stl.in_window;
                        st.nonzero += stl.nonzero;
                        st.checked += stl.checked;
                        st.witnessed += stl.witnessed;
                        st.resid += stl.resid;
                    }
                    if plant == "w2" && leaf.kind == 0 && cnt == 7 {
                        leaf.w2 += 1; // corrupt witness denominator
                    }
                    let li = leaf_to_ints(&leaf);
                    for (q, x) in li.iter().enumerate() {
                        fmax[q] = fmax[q].max((*x as i64).abs());
                    }
                    ints.extend(li);
                }
            }
        }
        write_ints(&format!("{}/leaf_{:02}.bin", dir, ni), &ints);
        println!(
            "node {:2} h={:?} tmax={:?} box={} canon={} radius={} prim={} noei={} greedy={} k0={} ratio={} leaves={} crit={}",
            ni, n.h, nd.tmax, f.box_pts, f.canon, f.radius, f.prim, f.noei, f.greedy, f.k0, f.ratio, cnt, ncrit
        );
        per_node.push(cnt);
        leaves_total += cnt;
        crit += ncrit;
        tot.box_pts += f.box_pts;
        tot.canon += f.canon;
        tot.radius += f.radius;
        tot.prim += f.prim;
        tot.noei += f.noei;
        tot.greedy += f.greedy;
        tot.k0 += f.k0;
        tot.ratio += f.ratio;
    }
    println!(
        "TOTAL funnel: box={} canon(half)={} radius={} prim(distinct L2)={} noei={} greedy-stage={} k0={} ratio={}",
        tot.box_pts, tot.canon, tot.radius, tot.prim, tot.noei, tot.greedy, tot.k0, tot.ratio
    );
    println!("leaves={} critical_leaves={} noncritical={} min_margin(M2-1/4)={}/{}", leaves_total, crit, leaves_total - crit, min_margin.0, min_margin.1);
    for x in &t1ints {
        t1max = t1max.max((*x as i64).abs());
    }
    println!("max |field| per leaf field index: {:?} ; T1 max {}", fmax, t1max);
    {
        let (mut cl, mut cb, mut ch, mut nch) = (0u64, 0u64, 0u64, 1u64);
        let mut mxl = 0u64;
        let mut mxb = 0u64;
        for &(l, b) in &perleaf {
            mxl = mxl.max(l);
            mxb = mxb.max(b);
            if cl + l > 10_000 || cb + b > 200_000 {
                nch += 1;
                cl = 0;
                cb = 0;
            }
            cl += l;
            cb += b;
            ch += 1;
        }
        println!("line packing (<=1e4 lines and <=2e5 box iters per theorem, leaf granularity): {} theorems over {} noncritical leaves; max lines per leaf {} ; max box iters per leaf {}", nch, ch, mxl, mxb);
    }
    println!("per-node leaves: {:?} max={}", per_node, per_node.iter().max().unwrap());
    println!(
        "lines: box_iters={} primitive={} in_window={} nonzero={} checked(distinct abs)={} witnessed={} unwitnessed={}  (time list q<={} : {} times)",
        st.box_iters, st.prim, st.in_window, st.nonzero, st.checked, st.witnessed, st.resid, qmax, tl.len()
    );
    let mut t5: Vec<T5> = unw.iter().map(|v| make_t5(*v)).collect();
    t5.sort_by_key(|t| t.v);
    let k0n = t5.iter().filter(|t| t.kind == 0).count();
    println!("T5 distinct unwitnessed tuples = {} (kind0 ML<1/4: {}, kind1 extra time: {})", t5.len(), k0n, t5.len() - k0n);
    for t in &t5 {
        println!("  T5 {:?} kind={} ML={}/{} time={}/{}", t.v, t.kind, t.mln, t.mld, t.a, t.q);
    }
    let mut t5i = vec![];
    for t in &t5 {
        t5i.extend(t5_to_ints(t));
    }
    if plant == "t5drop" && !t5.is_empty() {
        t5i.drain(0..9);
    }
    write_ints(&format!("{}/t5.bin", dir), &t5i);
    fs::write(format!("{}/meta.txt", dir), format!("qmax {}\nnodes {}\n", qmax, nodes.len())).unwrap();
}

// ---------------- checker (re-derives everything from the files; Lean-faithful integer relations) ----------------
fn check(dir: &str, brute: i64) -> Result<(), String> {
    let meta = fs::read_to_string(format!("{}/meta.txt", dir)).map_err(|e| e.to_string())?;
    let qmax: i64 = meta.lines().next().unwrap().split_whitespace().nth(1).unwrap().parse().unwrap();
    let nn: usize = meta.lines().nth(1).unwrap().split_whitespace().nth(1).unwrap().parse().unwrap();
    let tl = time_list(qmax);
    let sps = all_sp();
    // T1
    let t1i = read_ints(&format!("{}/t1.bin", dir));
    if t1i.len() != 37 * nn {
        return Err("t1.bin length".into());
    }
    let nodes: Vec<T1> = (0..nn).map(|i| t1_from_ints(&t1i[37 * i..37 * i + 37])).collect();
    for n in &nodes {
        for i in 0..3 {
            if dot(&n.b[i], &n.h) != 0 {
                return Err("T1: b.h != 0".into());
            }
            for k in 0..3 {
                if dot(&n.b[i], &n.r[k]) != (if i == k { 1 } else { 0 }) {
                    return Err("T1: b r != I".into());
                }
            }
        }
        if dot(&n.h, &n.s) != 1 {
            return Err("T1: h.s != 1".into());
        }
        if n.w1 <= 0 || dot(&n.h, &n.x1) % n.w1 != 0 || 4 * wmin(&n.x1, n.w1) <= n.w1 {
            return Err("T1: witness invalid".into());
        }
        let g = dot(&n.h, &n.h);
        if !(g >= 2 && 9 * g < 148) {
            return Err("T1: node test".into());
        }
        let nd = node_d(n);
        if nd.det != nd.g1 {
            return Err("T1: det Gram(b) != |h|^2".into());
        }
    }
    let cands = t1_candidates();
    let hs: HashSet<V> = nodes.iter().map(|n| n.h).collect();
    for c in &cands {
        if !hs.contains(c) {
            return Err(format!("T1 completeness: {:?} missing", c));
        }
    }
    if hs.len() != nodes.len() || hs.len() != cands.len() {
        return Err("T1 list has extra or duplicate entries".into());
    }
    // child stream + leaves + lines
    let mut st = LineStats::default();
    let mut nleaves = 0u64;
    let mut ncrit = 0u64;
    let mut unw_seen: HashSet<V> = HashSet::new();
    let t5i = read_ints(&format!("{}/t5.bin", dir));
    if t5i.len() % 9 != 0 {
        return Err("t5 length".into());
    }
    let t5: Vec<T5> = t5i.chunks(9).map(t5_from_ints).collect();
    let t5set: HashSet<V> = t5.iter().map(|t| t.v).collect();
    for t in &t5 {
        let mut s = t.v;
        s.sort();
        if s != t.v || t.v[0] <= 0 {
            return Err("T5 tuple not sorted positive".into());
        }
        if t.kind == 1 && !(t.q >= 2 && t.a >= 1 && time_ok(&t.v, t.a, t.q)) {
            return Err(format!("T5 extra time invalid for {:?}", t.v));
        }
        if t.kind != 0 && t.kind != 1 {
            return Err("T5 kind".into());
        }
    }
    for (ni, n) in nodes.iter().enumerate() {
        let nd = node_d(n);
        let li = read_ints(&format!("{}/leaf_{:02}.bin", dir, ni));
        if li.len() % LEAF_N != 0 {
            return Err("leaf file length".into());
        }
        let leaves: Vec<Leaf> = li.chunks(LEAF_N).map(leaf_from_ints).collect();
        // exact pass-list equality
        let mut pass: Vec<[i64; 3]> = vec![];
        let mut f = Funnel::default();
        for t0 in -nd.tmax[0]..=nd.tmax[0] {
            for t1 in -nd.tmax[1]..=nd.tmax[1] {
                for t2 in -nd.tmax[2]..=nd.tmax[2] {
                    let t = [t0, t1, t2];
                    if passes(n, &nd, &t, Var::Mid, &mut f) {
                        pass.push(t);
                    }
                }
            }
        }
        let stored: Vec<[i64; 3]> = leaves.iter().map(|l| l.t).collect();
        if pass != stored {
            return Err(format!("node {}: pass list != stored leaf stream ({} vs {})", ni, pass.len(), stored.len()));
        }
        for l in &leaves {
            nleaves += 1;
            for j in 0..3 {
                if dot(&n.b[j], &l.y) != l.t[j] {
                    return Err("leaf: b.y != t".into());
                }
            }
            for j in 0..2 {
                if dot(&n.h, &l.k[j]) != 0 || dot(&l.y, &l.k[j]) != 0 {
                    return Err("leaf: H B != 0".into());
                }
            }
            for a in 0..4 {
                for c in 0..4 {
                    let v = l.k[0][a] * l.q[0][c] + l.k[1][a] * l.q[1][c] + l.p[a][0] * n.h[c] + l.p[a][1] * l.y[c];
                    if v != (if a == c { 1 } else { 0 }) {
                        return Err("leaf: B Q + P H != I".into());
                    }
                }
            }
            if l.kind == 1 {
                ncrit += 1;
                let mut seen = [false; 4];
                for i in 0..4 {
                    if l.sg[i] < 0 || l.sg[i] > 3 || seen[l.sg[i] as usize] || (l.ep[i] != 1 && l.ep[i] != -1) {
                        return Err("crit: bad signed permutation".into());
                    }
                    seen[l.sg[i] as usize] = true;
                }
                if l.ck != 0 && l.ck != 1 {
                    return Err("crit: ck".into());
                }
                let g = ([l.sg[0] as usize, l.sg[1] as usize, l.sg[2] as usize, l.sg[3] as usize], l.ep);
                if !(crit_eq(l.ck, &sp_act(&g, &l.k[0])) && crit_eq(l.ck, &sp_act(&g, &l.k[1]))) {
                    return Err("crit: K2 not inside the critical torus".into());
                }
            } else if l.kind == 0 {
                if l.w2 <= 0 || dot(&n.h, &l.x2) % l.w2 != 0 || dot(&l.y, &l.x2) % l.w2 != 0 || 4 * wmin(&l.x2, l.w2) <= l.w2 {
                    return Err(format!("leaf {:?}: noncritical witness invalid", l.t));
                }
                leaf_lines(&nd, n, l, &tl, &mut st, |ab, ok| {
                    if !ok {
                        unw_seen.insert(ab);
                    }
                });
            } else {
                return Err("leaf kind".into());
            }
        }
    }
    for v in &unw_seen {
        if !t5set.contains(v) {
            return Err(format!("unwitnessed line {:?} not in T5", v));
        }
    }
    println!(
        "CHECK ok: T1 {} nodes; leaves {} (critical {}); lines box_iters={} primitive={} in_window={} nonzero={} checked={} witnessed={} unwitnessed={}; T5 listed {} / needed {}",
        nodes.len(), nleaves, ncrit, st.box_iters, st.prim, st.in_window, st.nonzero, st.checked, st.witnessed, st.resid, t5.len(), unw_seen.len()
    );
    if brute > 0 {
        let mut total = 0;
        let (mut oncrit, mut int5, mut unc) = (0, 0, vec![]);
        for d in 4..=brute {
            for c in 3..d {
                for b in 2..c {
                    for a in 1..b {
                        if gcd(gcd(a, b), gcd(c, d)) != 1 {
                            continue;
                        }
                        let v = [a, b, c, d];
                        if tl.iter().any(|&(a, q)| time_ok(&v, a, q)) {
                            continue;
                        }
                        let (mn, md) = ml_max(&v);
                        if 4 * mn >= md {
                            continue;
                        }
                        total += 1;
                        let onc = sps.iter().any(|g| {
                            let u = sp_act(g, &v);
                            crit_eq(0, &u) || crit_eq(1, &u)
                        });
                        if onc {
                            oncrit += 1;
                        } else if t5set.contains(&v) {
                            int5 += 1;
                        } else {
                            unc.push(v);
                        }
                    }
                }
            }
        }
        println!("BRUTE max<={}: near-tight primitive distinct tuples={} on critical torus={} in T5 only={} UNCOVERED={:?}", brute, total, oncrit, int5, unc);
        if !unc.is_empty() {
            return Err("brute-force coverage failed".into());
        }
    }
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("");
    if env::var("FW0_PLANT_LO").is_ok() {
        PLANT_LO.store(1, std::sync::atomic::Ordering::Relaxed);
    }
    if let Ok(f) = env::var("FW0_PLANT_HI") {
        PLANT_HI.store(f.parse().unwrap(), std::sync::atomic::Ordering::Relaxed);
    }
    // selftests (planted-failure controls)
    let eqf = |a: (i64, i64), b: (i64, i64)| a.0 * b.1 == a.1 * b.0;
    assert!(eqf(ml_max(&[1, 2, 3, 4]), (1, 5)));
    assert!(eqf(ml_max(&[1, 3, 4, 14]), (4, 17)));
    assert!(eqf(ml_max(&[1, 7, 8, 15]), (5, 22)));
    assert!(eqf(ml_max(&[3, 4, 7, 11]), (2, 9)));
    assert_eq!(m2_grid(&[[0, 1, 2, 3], [1, 0, 0, 0]]).0 * 4, m2_grid(&[[0, 1, 2, 3], [1, 0, 0, 0]]).1);
    assert_eq!(m2_grid(&[[1, 0, 1, 1], [0, 1, 1, 2]]).0 * 4, m2_grid(&[[1, 0, 1, 1], [0, 1, 1, 2]]).1);
    match mode {
        "gen" => {
            let dir = &args[2];
            let var = match args.iter().find(|a| a.starts_with("--var=")).map(|s| &s[6..]) {
                Some("full") => Var::Full,
                Some("mini") => Var::Mini,
                _ => Var::Mid,
            };
            let qmax: i64 = args.iter().find(|a| a.starts_with("--qmax=")).map(|s| s[7..].parse().unwrap()).unwrap_or(24);
            let plant = args.iter().find(|a| a.starts_with("--plant=")).map(|s| s[8..].to_string()).unwrap_or_default();
            gen(dir, var, qmax, &plant);
        }
        "check" => {
            let brute: i64 = args.iter().find(|a| a.starts_with("--brute=")).map(|s| s[8..].parse().unwrap()).unwrap_or(0);
            match check(&args[2], brute) {
                Ok(()) => println!("PASS"),
                Err(e) => {
                    println!("REJECT: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "mutate" => {
            // mutate SRC DST KIND : copy a certificate directory and apply one planted failure
            let (src, dst, kind) = (&args[2], &args[3], args[4].as_str());
            fs::create_dir_all(dst).unwrap();
            for e in fs::read_dir(src).unwrap() {
                let e = e.unwrap();
                fs::copy(e.path(), format!("{}/{}", dst, e.file_name().to_string_lossy())).unwrap();
            }
            let lf = format!("{}/leaf_04.bin", dst);
            let mut li = read_ints(&lf);
            let fld = |rec: usize, f: usize| rec * LEAF_N + f;
            match kind {
                "dropleaf" => {
                    li.drain(5 * LEAF_N..6 * LEAF_N);
                }
                "extraleaf" => {
                    let rec: Vec<i32> = li[0..LEAF_N].to_vec();
                    li.extend(rec);
                }
                "swapleaf" => {
                    let a: Vec<i32> = li[0..LEAF_N].to_vec();
                    let b: Vec<i32> = li[LEAF_N..2 * LEAF_N].to_vec();
                    li[0..LEAF_N].copy_from_slice(&b);
                    li[LEAF_N..2 * LEAF_N].copy_from_slice(&a);
                }
                "corrupty" => li[fld(3, 3)] += 1,
                "kflip" => li[fld(3, 13)] += 1,
                "qflip" => li[fld(3, 21)] += 1,
                "pflip" => li[fld(3, 29)] += 1,
                "witx" => {
                    // find a noncritical record and corrupt its witness
                    let i = (0..li.len() / LEAF_N).find(|&r| li[fld(r, 7)] == 0).unwrap();
                    for c in 0..4 {
                        li[fld(i, 8 + c)] = 0;
                    }
                }
                "witw" => {
                    let i = (0..li.len() / LEAF_N).find(|&r| li[fld(r, 7)] == 0).unwrap();
                    li[fld(i, 12)] += 1;
                }
                "critck" => {
                    let i = (0..li.len() / LEAF_N).find(|&r| li[fld(r, 7)] == 1).expect("no critical leaf in leaf_04");
                    li[fld(i, 37)] = 1 - li[fld(i, 37)];
                }
                "critsg" => {
                    let i = (0..li.len() / LEAF_N).find(|&r| li[fld(r, 7)] == 1).expect("no critical leaf in leaf_04");
                    li[fld(i, 42)] = -li[fld(i, 42)];
                }
                "critflag" => {
                    // declare a noncritical leaf critical
                    let i = (0..li.len() / LEAF_N).find(|&r| li[fld(r, 7)] == 0).unwrap();
                    li[fld(i, 7)] = 1;
                }
                "t1corrupt" => {
                    let tf = format!("{}/t1.bin", dst);
                    let mut t = read_ints(&tf);
                    t[8] += 2;
                    write_ints(&tf, &t);
                }
                "t1drop" => {
                    let tf = format!("{}/t1.bin", dst);
                    let mut t = read_ints(&tf);
                    t.drain(37 * 5..37 * 6);
                    write_ints(&tf, &t);
                    fs::write(format!("{}/meta.txt", dst), "qmax 24\nnodes 14\n").unwrap();
                }
                "t5drop" => {
                    let tf = format!("{}/t5.bin", dst);
                    let mut t = read_ints(&tf);
                    t.drain(0..9);
                    write_ints(&tf, &t);
                }
                "t5time" => {
                    let tf = format!("{}/t5.bin", dst);
                    let mut t = read_ints(&tf);
                    let i = (0..t.len() / 9).find(|&r| t[9 * r + 4] == 1);
                    if let Some(i) = i {
                        t[9 * i + 5] = t[9 * i + 6];
                        write_ints(&tf, &t);
                    } else {
                        panic!("no kind-1 T5 record");
                    }
                }
                "metaq" => {
                    fs::write(format!("{}/meta.txt", dst), "qmax 6\nnodes 15\n").unwrap();
                }
                _ => panic!("unknown mutation"),
            }
            write_ints(&lf, &li);
        }
        _ => eprintln!("usage: four_wp0 gen DIR [--var=mid|full|mini] [--qmax=N] [--plant=NAME] | check DIR [--brute=D]"),
    }
}

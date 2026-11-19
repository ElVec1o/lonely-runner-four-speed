// recount: independent exact recount of the n = 4 tree (own code: shares nothing with four_lean or four_wp0).
// Differences of method: (a) children enumerated as ambient y in a box, reduced mod h, lattice identity by the
// projection-matrix key N = A adj(A^T A) A^T (basis free), e_i exclusion by N_ii = G2; (b) leaf classes by the
// minimum of N over the 384 signed permutations; (c) M(L2) by exact tight-triple vertex enumeration (u,w,c) of
// the three-form systems, feasibility tested in integers; (d) K2 by brute-force kernel search + covolume test.
// Variants: eng (radius + e_i + greedy, k=2 window only), full (greedy + k0 + ratio + all window tests, hull),
// mini (no greedy, k=2 window only). Exact integers (i64/i128), no floats.
use std::collections::{HashMap, HashSet};
use std::env;

type V = [i64; 4];
fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
fn dot(a: &V, b: &V) -> i64 {
    (0..4).map(|i| a[i] * b[i]).sum()
}
fn isq(n: i128) -> i128 {
    if n <= 0 {
        return 0;
    }
    let (mut lo, mut hi) = (0i128, 1i128 << 62);
    while lo < hi {
        let m = (lo + hi + 1) / 2;
        if m * m <= n {
            lo = m
        } else {
            hi = m - 1
        }
    }
    lo
}
// plane matrix N = A adj(A^T A) A^T for A = [h y] (4x2); adj of 2x2 [[a,b],[b,d]] = [[d,-b],[-b,a]]
fn plane(h: &V, y: &V) -> [[i64; 4]; 4] {
    let (a, b, d) = (dot(h, h), dot(h, y), dot(y, y));
    let mut n = [[0i64; 4]; 4];
    for i in 0..4 {
        for j in 0..4 {
            n[i][j] = d * h[i] * h[j] - b * (h[i] * y[j] + y[i] * h[j]) + a * y[i] * y[j];
        }
    }
    n
}
fn sps() -> Vec<([usize; 4], [i64; 4])> {
    let mut o = vec![];
    let mut p = [0usize, 1, 2, 3];
    fn rec(k: usize, p: &mut [usize; 4], o: &mut Vec<[usize; 4]>) {
        if k == 4 {
            o.push(*p);
            return;
        }
        for i in k..4 {
            p.swap(k, i);
            rec(k + 1, p, o);
            p.swap(k, i);
        }
    }
    let mut ps = vec![];
    rec(0, &mut p, &mut ps);
    for q in ps {
        for s in 0..16u32 {
            let e = [0, 1, 2, 3].map(|i| if (s >> i) & 1 == 1 { -1i64 } else { 1 });
            o.push((q, e));
        }
    }
    o
}
fn key(n: &[[i64; 4]; 4], g: &Vec<([usize; 4], [i64; 4])>) -> [i64; 16] {
    let mut best: Option<[i64; 16]> = None;
    for (s, e) in g {
        let mut k = [0i64; 16];
        for i in 0..4 {
            for j in 0..4 {
                k[4 * i + j] = e[i] * e[j] * n[s[i]][s[j]];
            }
        }
        if best.map_or(true, |b| k < b) {
            best = Some(k);
        }
    }
    best.unwrap()
}
// exact ML (num,den) via candidates k/L, L = |v_i|+|v_j|, all k
fn ml(v: &V) -> (i64, i64) {
    let a = [v[0].abs(), v[1].abs(), v[2].abs(), v[3].abs()];
    let (mut bn, mut bd) = (0, 1);
    for i in 0..4 {
        for j in i..4 {
            let l = a[i] + a[j];
            for k in 0..l {
                let mut m = i64::MAX;
                for t in 0..4 {
                    let r = (a[t] * k) % l;
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
fn ge_q(v: &V) -> bool {
    let a = [v[0].abs(), v[1].abs(), v[2].abs(), v[3].abs()];
    for i in 0..4 {
        for j in i..4 {
            let l = a[i] + a[j];
            'k: for k in 0..l {
                for t in 0..4 {
                    let r = (a[t] * k) % l;
                    if 4 * r.min(l - r) < l {
                        continue 'k;
                    }
                }
                return true;
            }
        }
    }
    false
}
// kernel basis of {h,y}: rows of the Hodge-dual matrix of h^y span K2 (saturated); Euclid row reduction, Gauss reduction
fn kernel(h: &V, y: &V, g2: i64) -> [V; 2] {
    let p = |i: usize, j: usize| h[i] * y[j] - h[j] * y[i];
    let mut q = [[0i64; 4]; 4];
    q[0][1] = p(2, 3);
    q[0][2] = -p(1, 3);
    q[0][3] = p(1, 2);
    q[1][2] = p(0, 3);
    q[1][3] = -p(0, 2);
    q[2][3] = p(0, 1);
    for i in 0..4 {
        for j in 0..i {
            q[i][j] = -q[j][i];
        }
    }
    let mut rows: Vec<V> = q.to_vec();
    for r in &rows {
        assert!(dot(r, h) == 0 && dot(r, y) == 0);
    }
    // Euclid reduction over the 4 rows to get 2 nonzero rows
    let mut basis: Vec<V> = vec![];
    for c in 0..4 {
        loop {
            let nz: Vec<usize> = (0..rows.len()).filter(|&i| rows[i][c] != 0).collect();
            if nz.len() <= 1 {
                if let Some(&i) = nz.first() {
                    basis.push(rows.remove(i));
                }
                break;
            }
            let m = *nz.iter().min_by_key(|&&i| rows[i][c].abs()).unwrap();
            for &i in &nz {
                if i != m {
                    let f = rows[i][c] / rows[m][c];
                    for k in 0..4 {
                        let v = rows[m][k];
                        rows[i][k] -= f * v;
                    }
                }
            }
        }
    }
    assert!(basis.len() == 2, "kernel rank");
    let mut b = [basis[0], basis[1]];
    loop {
        if dot(&b[0], &b[0]) > dot(&b[1], &b[1]) {
            b.swap(0, 1);
        }
        let n0 = dot(&b[0], &b[0]);
        let m = (2 * dot(&b[0], &b[1]) + n0).div_euclid(2 * n0);
        if m == 0 {
            break;
        }
        for k in 0..4 {
            b[1][k] -= m * b[0][k];
        }
    }
    let d = dot(&b[0], &b[0]) * dot(&b[1], &b[1]) - dot(&b[0], &b[1]).pow(2);
    assert_eq!(d, g2, "covolume identity");
    b
}
// M(L2): max over 2-torus of min_i ||k0_i u + k1_i w||; tight-triple vertices. Returns (num,den) exact.
fn mtorus(k: &[V; 2]) -> (i64, i64) {
    let l: Vec<[i64; 2]> = (0..4).map(|i| [k[0][i], k[1][i]]).collect();
    let s: Vec<i64> = l.iter().map(|x| x[0].abs() + x[1].abs() + 1).collect();
    let (mut bn, mut bd) = (0i64, 1i64);
    let tri = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]];
    for t in tri {
        for signs in 0..8u32 {
            let sg = [0, 1, 2].map(|q| if (signs >> q) & 1 == 1 { -1i64 } else { 1 });
            for m0 in -s[t[0]]..=s[t[0]] {
                for m1 in -s[t[1]]..=s[t[1]] {
                    for m2 in -s[t[2]]..=s[t[2]] {
                        // l_i . (u,w) - sg_i * c = m_i  (i in triple)
                        let r = [[l[t[0]][0], l[t[0]][1], -sg[0]], [l[t[1]][0], l[t[1]][1], -sg[1]], [l[t[2]][0], l[t[2]][1], -sg[2]]];
                        let rhs = [m0, m1, m2];
                        let det3 = |a: [[i64; 3]; 3]| -> i64 {
                            a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1]) - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0]) + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
                        };
                        let d = det3(r);
                        if d == 0 {
                            continue;
                        }
                        let mut cr = r;
                        let mut ur = r;
                        let mut wr = r;
                        for q in 0..3 {
                            ur[q][0] = rhs[q];
                            wr[q][1] = rhs[q];
                            cr[q][2] = rhs[q];
                        }
                        let (du, dw, dc) = (det3(ur), det3(wr), det3(cr));
                        let (dd, du, dw, dc) = if d < 0 { (-d, -du, -dw, -dc) } else { (d, du, dw, dc) };
                        // c = dc/dd must satisfy 0 < c <= 1/2 and beat best
                        if dc <= 0 || 2 * dc > dd || dc * bd <= bn * dd {
                            continue;
                        }
                        // feasibility: all four forms at (du/dd, dw/dd) have ||f|| >= dc/dd
                        let mut ok = true;
                        for q in 0..4 {
                            let rr = (l[q][0] * du + l[q][1] * dw).rem_euclid(dd);
                            if rr.min(dd - rr) < dc {
                                ok = false;
                                break;
                            }
                        }
                        if ok {
                            bn = dc;
                            bd = dd;
                        }
                    }
                }
            }
        }
    }
    (bn, bd)
}
struct Leaf {
    h: V,
    g1: i128,
    g2: i128,
    l1: i64,
    cls: usize,
}
struct Cls {
    k: [V; 2],
    m2: (i64, i64),
    lo: Option<(i128, i128)>, // hull lo as fraction num/den of n (None = 0 start)
    hi: Option<(i128, i128)>,
    count: u64,
    lo_set: bool,
}
fn fr_lt(a: (i128, i128), b: (i128, i128)) -> bool {
    a.0 * b.1 < b.0 * a.1
}
fn main() {
    let args: Vec<String> = env::args().collect();
    let var = args.get(1).map(|s| s.as_str()).unwrap_or("eng");
    let dmax: i64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let full = var == "full";
    let greedy_on = var != "mini";
    let g384 = sps();
    assert_eq!(g384.len(), 384);
    // depth-1 reps
    let mut reps: Vec<V> = vec![];
    for a in 0..=4i64 {
        for b in 0..=4 {
            for c in 0..=4 {
                for d in 0..=4 {
                    let h = [a, b, c, d];
                    if a <= b && b <= c && c <= d && gcd(gcd(a, b), gcd(c, d)) == 1 && dot(&h, &h) >= 2 && 9 * dot(&h, &h) < 148 {
                        reps.push(h);
                    }
                }
            }
        }
    }
    println!("depth1 reps {} : {:?}", reps.len(), reps);
    let mut leaves: Vec<Leaf> = vec![];
    let mut classes: Vec<Cls> = vec![];
    let mut cmap: HashMap<[i64; 16], usize> = HashMap::new();
    let mut fun = [0u64; 7]; // box, radius, sat, distinct, noei, greedy, final
    for h in &reps {
        let g1 = dot(h, h);
        let l1: i64 = h.iter().sum();
        let even = l1 % 2 == 0;
        // mu2^2 < 7/(12 m1m^2); |y|^2 <= mu2^2 + G1/4 ; use generous integer bound on the box
        let r2num: i128 = if even { 7 * 16 } else { 7 * 16 * (l1 as i128) * (l1 as i128) }; // 12*m1m^2 = 3/4 or 3(l1-2)^2/(4 l1^2)
        let r2den: i128 = if even { 12 } else { 12 * ((l1 - 2) as i128) * ((l1 - 2) as i128) };
        // mu2^2 < 7/(12 m1m^2) = r2num/(r2den) (up to the exact test below); box bound
        let yb = (r2num / r2den + (g1 as i128) / 4 + 2) as i128;
        let bm = isq(yb) as i64 + 1;
        let mut seen: HashSet<[[i64; 4]; 4]> = HashSet::new();
        for y0 in -bm..=bm {
            for y1 in -bm..=bm {
                for y2 in -bm..=bm {
                    for y3 in -bm..=bm {
                        let y = [y0, y1, y2, y3];
                        let t = dot(h, &y);
                        if !(-g1 < 2 * t && 2 * t <= g1) {
                            continue;
                        }
                        let g2 = g1 * dot(&y, &y) - t * t;
                        if g2 <= 0 {
                            continue;
                        }
                        fun[0] += 1;
                        // radius: 12 m1m^2 g2 < 7 g1
                        let lhs = if even { 3 * (g2 as i128) } else { 3 * ((l1 - 2) as i128).pow(2) * (g2 as i128) };
                        let rhs = if even { 28 * (g1 as i128) } else { 28 * (g1 as i128) * (l1 as i128).pow(2) };
                        if lhs >= rhs {
                            continue;
                        }
                        fun[1] += 1;
                        let mut mg = 0;
                        for i in 0..4 {
                            for j in i + 1..4 {
                                mg = gcd(mg, h[i] * y[j] - h[j] * y[i]);
                            }
                        }
                        if mg != 1 {
                            continue;
                        }
                        fun[2] += 1;
                        let n = plane(h, &y);
                        if !seen.insert(n) {
                            continue;
                        }
                        fun[3] += 1;
                        if (0..4).any(|i| n[i][i] == g2) {
                            continue;
                        }
                        fun[4] += 1;
                        if greedy_on {
                            // shortest vector of Zh+Zy: Lagrange-Gauss
                            let mut b = [*h, y];
                            loop {
                                if dot(&b[0], &b[0]) > dot(&b[1], &b[1]) {
                                    b.swap(0, 1);
                                }
                                let q = 2 * dot(&b[0], &b[1]) + dot(&b[0], &b[0]);
                                let m = q.div_euclid(2 * dot(&b[0], &b[0]));
                                if m == 0 {
                                    break;
                                }
                                for c in 0..4 {
                                    b[1][c] -= m * b[0][c];
                                }
                            }
                            if dot(&b[0], &b[0]) < g1 {
                                continue;
                            }
                        }
                        fun[5] += 1;
                        if full {
                            let (g1i, g2i) = (g1 as i128, g2 as i128);
                            // k0: 1/4 < 1/g1 + (7/3) g1/g2 ; ratio 4 g2 >= 3 g1^2
                            if !(3 * g1i * g2i < 12 * g2i + 28 * g1i * g1i) || 4 * g2i < 3 * g1i * g1i {
                                continue;
                            }
                        }
                        fun[6] += 1;
                        let kk = key(&n, &g384);
                        let ci = *cmap.entry(kk).or_insert_with(|| {
                            let kb = kernel(h, &y, g2);
                            let m2 = mtorus(&kb);
                            classes.push(Cls { k: kb, m2, lo: None, hi: None, count: 0, lo_set: false });
                            classes.len() - 1
                        });
                        leaves.push(Leaf { h: *h, g1: g1 as i128, g2: g2 as i128, l1, cls: ci });
                    }
                }
            }
        }
    }
    println!("funnel (box, radius, saturated, distinct L2, no e_i, greedy, final) = {:?}", fun);
    println!("leaves {} classes {}", leaves.len(), classes.len());
    // criticals, margin
    let mut crit_leaves = 0;
    let mut crit_cls: Vec<i128> = vec![];
    let mut fault = 0;
    let mut mg: (i64, i64) = (1, 1);
    for (ci, c) in classes.iter().enumerate() {
        let _ = ci;
        let (a, b) = c.m2;
        if 4 * a < b {
            fault += 1;
        }
    }
    for l in &leaves {
        let c = &mut classes[l.cls];
        c.count += 1;
        let (a, b) = c.m2;
        if 4 * a == b {
            crit_leaves += 1;
        }
    }
    for c in classes.iter() {
        let (a, b) = c.m2;
        if 4 * a == b {
            let g2 = dot(&c.k[0], &c.k[0]) * dot(&c.k[1], &c.k[1]) - dot(&c.k[0], &c.k[1]).pow(2);
            crit_cls.push(g2 as i128);
        } else {
            // margin (4a - b)/(4b)
            let m = (4 * a - b, 4 * b);
            if m.0 * mg.1 < mg.0 * m.1 {
                mg = m;
            }
        }
    }
    println!("critical leaves {} ; critical classes {} covol^2 {:?} ; classes with M2<1/4: {} ; min margin M2-1/4 = {}/{}", crit_leaves, crit_cls.len(), crit_cls, fault, mg.0, mg.1);
    // windows (hull per class) as fractions of n
    for l in &leaves {
        let c = &mut classes[l.cls];
        let (a, b) = c.m2;
        if 4 * a == b {
            continue;
        }
        // m2m = (4a-b)/(4b): hi from k=2: n < g2 / (4 m2m^2) = g2 * 4 b^2 / (4a-b)^2
        let da = (4 * a - b) as i128;
        let mut hi = (l.g2 * 4 * (b as i128) * (b as i128), da * da);
        if full {
            // k=1: den1 = 4 m1m^2 - g1/g2 ; 4 m1m^2 = (l1-2)^2/(4 l1^2) odd or 1/4 even; mu3^-2 > den1 -> n < g2/den1 if den1>0
            let (pn, pd): (i128, i128) = if l.l1 % 2 == 0 { (1, 4) } else { (((l.l1 - 2) as i128).pow(2), 4 * (l.l1 as i128).pow(2)) };
            // den1 = pn/pd - g1/g2 = (pn g2 - g1 pd)/(pd g2)
            let dn = pn * l.g2 - l.g1 * pd;
            if dn > 0 {
                let cand = (l.g2 * pd * l.g2, dn);
                if fr_lt(cand, hi) {
                    hi = cand;
                }
            }
            // k=0: den0 = 1/4 - 1/g1 - g1/g2 = (g1 g2 - 4 g2 - 4 g1^2)/(4 g1 g2)
            let d0 = l.g1 * l.g2 - 4 * l.g2 - 4 * l.g1 * l.g1;
            if d0 > 0 {
                let cand = (l.g2 * 4 * l.g1 * l.g2, d0);
                if fr_lt(cand, hi) {
                    hi = cand;
                }
            }
        }
        let lo = if full { (3 * l.g2 * l.g2, 4 * l.g1) } else { (0, 1) };
        match c.lo {
            None => c.lo = Some(lo),
            Some(x) => {
                if fr_lt(lo, x) {
                    c.lo = Some(lo)
                }
            }
        }
        match c.hi {
            None => c.hi = Some(hi),
            Some(x) => {
                if fr_lt(x, hi) {
                    c.hi = Some(hi)
                }
            }
        }
        c.lo_set = true;
    }
    // lines per class (hull window, strict hi, nonstrict lo), noncritical only
    let mut lines = 0u64;
    let mut lines_d = 0u64;
    let mut nodedupe = 0u64;
    let mut near: HashSet<V> = HashSet::new();
    for c in classes.iter() {
        if !c.lo_set || 4 * c.m2.0 == c.m2.1 {
            continue;
        }
        let (lo, hi) = (c.lo.unwrap(), c.hi.unwrap());
        let a = dot(&c.k[0], &c.k[0]) as i128;
        let bb = dot(&c.k[0], &c.k[1]) as i128;
        let d = dot(&c.k[1], &c.k[1]) as i128;
        let dd = a * d - bb * bb;
        let hif = hi.0 / hi.1 + 1;
        let zb = isq(a * hif / dd) + 1;
        let xb = isq(d * hif / dd) + 1;
        let mut here = 0u64;
        for z in 0..=zb as i64 {
            for x in -(xb as i64)..=(xb as i64) {
                if z == 0 && x != 1 {
                    continue;
                }
                if gcd(x, z) != 1 {
                    continue;
                }
                let n = a * (x as i128).pow(2) + 2 * bb * (x as i128) * (z as i128) + d * (z as i128).pow(2);
                // lo <= n < hi (fractions)
                if (n * lo.1 < lo.0) || !(n * hi.1 < hi.0) {
                    continue;
                }
                let v = [0, 1, 2, 3].map(|i| x * c.k[0][i] + z * c.k[1][i]);
                if v.iter().any(|&e| e == 0) {
                    continue;
                }
                here += 1;
                let mut ab = v.map(|e| e.abs());
                ab.sort();
                if ab[0] != ab[1] && ab[1] != ab[2] && ab[2] != ab[3] {
                    lines_d += 1;
                }
                if !ge_q(&v) {
                    near.insert(ab);
                }
            }
        }
        lines += here;
        nodedupe += here * c.count;
    }
    println!("lines (class-deduped, nonzero entries, in hull window) {} distinct-abs {} ; without class dedupe {}", lines, lines_d, nodedupe);
    let mut nl: Vec<V> = near.iter().cloned().collect();
    nl.sort();
    println!("near-tight tuples (ML<1/4) on noncritical leaf lines: {} : {:?}", nl.len(), nl);
    // classification of those against the critical tori
    let gs = &g384;
    let on_crit = |v: &V| -> bool {
        gs.iter().any(|(s, e)| {
            let u = [0, 1, 2, 3].map(|i| e[i] * v[s[i]]);
            (u[1] == 2 * u[0] && u[2] == 3 * u[0]) || (u[2] == u[0] + u[1] && u[3] == 2 * u[0] + u[1])
        })
    };
    let off: Vec<&V> = nl.iter().filter(|v| !on_crit(v)).collect();
    let u1 = nl.iter().filter(|v| gs.iter().any(|(s, e)| { let u = [0, 1, 2, 3].map(|i| e[i] * v[s[i]]); u[1] == 2 * u[0] && u[2] == 3 * u[0] })).count();
    println!("  of which on U^1: {} ; on U^2 only: {} ; off both tori: {:?}", u1, nl.len() - u1 - off.len(), off);
    // brute force
    let mut bf: Vec<V> = vec![];
    for d in 4..=dmax {
        for c in 3..d {
            for b in 2..c {
                for a in 1..b {
                    if gcd(gcd(a, b), gcd(c, d)) == 1 && !ge_q(&[a, b, c, d]) {
                        bf.push([a, b, c, d]);
                    }
                }
            }
        }
    }
    let nset: HashSet<V> = nl.iter().filter(|v| v[3] <= dmax).cloned().collect();
    let bset: HashSet<V> = bf.iter().cloned().collect();
    let bf_off: Vec<&V> = bf.iter().filter(|v| !on_crit(v)).collect();
    println!("BRUTE max<={}: near-tight tuples {} ; on a critical torus {} ; off both tori {:?}", dmax, bf.len(), bf.len() - bf_off.len(), bf_off);
    println!("  tree(noncrit-leaf lines, max<={}) {} ; missing from tree among off-torus brute {} ; tree tuples not in brute {}", dmax, nset.len(), bf_off.iter().filter(|v| !nset.contains(**v)).count(), nset.iter().filter(|v| !bset.contains(*v)).count());
    // negative control: the planted M2 failure (pretend every class M2 = 0) must change the critical count
    let _ = ml(&[1, 2, 3, 4]);
}

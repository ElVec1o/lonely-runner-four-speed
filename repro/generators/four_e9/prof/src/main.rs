// four_e9 prof: per-record profile of the E9 line loop (exact i128), independent re-typing of Lean `leafLinesB`/`lineB`.
// usage: prof CERT_DIR OUT_TSV   (CERT_DIR = four_wp0/cert_final)
// Per noncritical leaf record: loop box (Z,X), iterations, lines passing the conjuncts of `lineB` (gcd=1, WinInt, nonzero,
// distinct), TL entries scanned (kernel `List.any` stops at the first hit), T5 hits (no TL witness).
use std::fs;
use std::io::Write;

fn read_ints(p: &str) -> Vec<i32> {
    let b = fs::read(p).unwrap();
    b.chunks(4).map(|c| i32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect()
}
fn isqrt(n: i128) -> i128 {
    if n <= 0 {
        return 0;
    }
    let mut x = (n as f64).sqrt() as i128;
    while x * x > n {
        x -= 1;
    }
    while (x + 1) * (x + 1) <= n {
        x += 1;
    }
    x
}
fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
fn wmin(x: &[i128], w: i128) -> i128 {
    let mut m = i128::MAX;
    for &xi in x {
        let r = xi.rem_euclid(w);
        m = m.min(r.min(w - r));
    }
    m
}
fn dot(a: &[i128], b: &[i128]) -> i128 {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}
fn time_ok(u: &[i128; 4], a: i128, q: i128) -> bool {
    if q <= 0 {
        return false;
    }
    for i in 0..4 {
        let r = (u[i].abs() * a).rem_euclid(q);
        if q > 4 * r.min(q - r) {
            return false;
        }
    }
    true
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let dir = &a[1];
    let mut out = fs::File::create(&a[2]).unwrap();
    let t1 = read_ints(&format!("{}/t1.bin", dir));
    let t5 = read_ints(&format!("{}/t5.bin", dir));
    let t5v: Vec<[i128; 4]> = t5.chunks(9).map(|r| [r[0] as i128, r[1] as i128, r[2] as i128, r[3] as i128]).collect();
    // time list exactly as Lean `TL`
    let mut tl: Vec<(i128, i128)> = vec![];
    for k in 0..49i128 {
        let q = k + 2;
        for aa in 0..((k + 2) / 2) {
            let a1 = aa + 1;
            if gcd(a1, q) == 1 {
                tl.push((a1, q));
            }
        }
    }
    eprintln!("TL length {}", tl.len());
    writeln!(out, "node\trec\tkind\ta\tb\td\tD\tG2\tA2\tnmax\tZ\tX\titers\tcond\ttlscan\tt5\tmaxm").unwrap();
    let (mut tot_it, mut tot_cond, mut tot_t5, mut tot_rec, mut tot_tl) = (0i128, 0i128, 0i128, 0i128, 0i128);
    let mut tot_t5_distinct: Vec<[i128; 4]> = vec![];
    for node in 0..15 {
        let r = &t1[node * 37..(node + 1) * 37];
        let h: Vec<i128> = r[0..4].iter().map(|&x| x as i128).collect();
        let x1: Vec<i128> = r[4..8].iter().map(|&x| x as i128).collect();
        let w1 = r[8] as i128;
        let g1 = dot(&h, &h);
        let a1 = 4 * wmin(&x1, w1) - w1;
        let leaf = read_ints(&format!("{}/leaf_{:02}.bin", dir, node));
        let n = leaf.len() / 46;
        for rec in 0..n {
            let f: Vec<i128> = leaf[rec * 46..(rec + 1) * 46].iter().map(|&x| x as i128).collect();
            let kind = f[7];
            if kind != 0 {
                continue;
            }
            let y: Vec<i128> = f[3..7].to_vec();
            let x2: Vec<i128> = f[8..12].to_vec();
            let w2 = f[12];
            let k0: Vec<i128> = f[13..17].to_vec();
            let k1: Vec<i128> = f[17..21].to_vec();
            let aa = dot(&k0, &k0);
            let bb = dot(&k0, &k1);
            let dd = dot(&k1, &k1);
            let dcap = aa * dd - bb * bb;
            let g2 = g1 * dot(&y, &y) - dot(&h, &y).pow(2);
            let a2 = 4 * wmin(&x2, w2) - w2;
            assert!(dcap > 0 && a2 > 0, "D or A2 not positive");
            let nmax = (4 * w2 * w2 * g2 - 1).div_euclid(a2 * a2);
            let zz = isqrt((aa * nmax).div_euclid(dcap));
            let xx = isqrt((dd * nmax).div_euclid(dcap));
            let mut iters = 0i128;
            let mut cond = 0i128;
            let mut tlscan = 0i128;
            let mut t5c = 0i128;
            let mut maxm = 0i128;
            for z in 0..=zz {
                let xs: Vec<i128> = if z == 0 { vec![1] } else { (-xx..=xx).collect() };
                for &x in &xs {
                    iters += 1;
                    if gcd(x, z) != 1 {
                        continue;
                    }
                    let mut u = [0i128; 4];
                    for i in 0..4 {
                        u[i] = x * k0[i] + z * k1[i];
                    }
                    let m: i128 = u.iter().map(|v| v * v).sum();
                    let win = 3 * g2 * g2 <= 4 * g1 * m
                        && a2 * a2 * m < 4 * w2 * w2 * g2
                        && a1 * a1 * g2 * m < 4 * w1 * w1 * (g1 * m + g2 * g2)
                        && g1 * g2 * m < 4 * (g2 * m + g1 * g1 * m + g1 * g2 * g2);
                    if !win {
                        continue;
                    }
                    if u.iter().any(|&v| v == 0) {
                        continue;
                    }
                    let mut dis = true;
                    for i in 0..4 {
                        for j in 0..4 {
                            if i != j && u[i].abs() == u[j].abs() {
                                dis = false;
                            }
                        }
                    }
                    if !dis {
                        continue;
                    }
                    cond += 1;
                    maxm = maxm.max(m);
                    let mut found = false;
                    for &(ta, tq) in &tl {
                        tlscan += 1;
                        if time_ok(&u, ta, tq) {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        let mut s = [u[0].abs(), u[1].abs(), u[2].abs(), u[3].abs()];
                        s.sort();
                        let hit = t5v.iter().any(|v| *v == s);
                        assert!(hit, "line with no time and not in T5: node {} rec {} x {} z {}", node, rec, x, z);
                        t5c += 1;
                        if !tot_t5_distinct.contains(&s) {
                            tot_t5_distinct.push(s);
                        }
                    }
                }
            }
            tot_it += iters;
            tot_cond += cond;
            tot_t5 += t5c;
            tot_tl += tlscan;
            tot_rec += 1;
            writeln!(out, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", node, rec, kind, aa, bb, dd, dcap, g2, a2, nmax, zz, xx, iters, cond, tlscan, t5c, maxm).unwrap();
        }
    }
    eprintln!("noncritical records {} loop iterations {} lines in window with nonzero distinct {} (T5 lines {}) TL entries scanned {} distinct T5 tuples {:?}", tot_rec, tot_it, tot_cond, tot_t5, tot_tl, tot_t5_distinct);
}

// ctlbox: why a corrupted record or a wrong node record makes the line-loop kernel run explode.
// For a leaf record: original loop box (D, Z, X, iterations), the box after k0[0] += 1, and the box of the same leaf under another node record.
use std::fs;
fn read_ints(p: &str) -> Vec<i128> {
    let b = fs::read(p).unwrap();
    b.chunks(4).map(|c| i32::from_le_bytes([c[0], c[1], c[2], c[3]]) as i128).collect()
}
fn isqrt(n: i128) -> i128 {
    if n <= 0 { return 0; }
    let mut x = (n as f64).sqrt() as i128;
    while x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}
fn wmin(x: &[i128], w: i128) -> i128 {
    let mut m = i128::MAX;
    for &xi in x { let r = xi.rem_euclid(w); m = m.min(r.min(w - r)); }
    m
}
fn dot(a: &[i128], b: &[i128]) -> i128 { a.iter().zip(b).map(|(x, y)| x * y).sum() }
// returns (D, A2, nmax, Z, X, iterations) ; None when D <= 0 or A2 <= 0 (leafLinesB = false at once)
fn bx(h: &[i128], f: &[i128]) -> Option<(i128, i128, i128, i128, i128, i128)> {
    let g1 = dot(h, h);
    let y = &f[3..7]; let x2 = &f[8..12]; let w2 = f[12];
    let k0 = &f[13..17]; let k1 = &f[17..21];
    let (a, b, d) = (dot(k0, k0), dot(k0, k1), dot(k1, k1));
    let dc = a * d - b * b;
    let g2 = g1 * dot(y, y) - dot(h, y).pow(2);
    let a2 = 4 * wmin(x2, w2) - w2;
    if dc <= 0 || a2 <= 0 { return None; }
    let nmax = (4 * w2 * w2 * g2 - 1).div_euclid(a2 * a2);
    let z = isqrt((a * nmax).div_euclid(dc));
    let x = isqrt((d * nmax).div_euclid(dc));
    Some((dc, a2, nmax, z, x, (z + 1) * (2 * x + 1)))
}
fn gcd(a: i128, b: i128) -> i128 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn time_ok(u: &[i128;4], a: i128, q: i128) -> bool { (0..4).all(|i| { let r = (u[i].abs()*a).rem_euclid(q); q <= 4*r.min(q-r) }) }
fn main() {
    second();
    let dir = "reference/cert_final";
    let t1 = read_ints(&format!("{}/t1.bin", dir));
    let h_of = |n: usize| t1[n * 37..n * 37 + 4].to_vec();
    for (node, rec) in [(1usize, 10usize), (1, 11), (0, 5), (4, 5), (7, 3)] {
        let leaf = read_ints(&format!("{}/leaf_{:02}.bin", dir, node));
        let f = leaf[rec * 46..(rec + 1) * 46].to_vec();
        println!("node {} rec {} original      : {:?}", node, rec, bx(&h_of(node), &f));
        for fld in [13usize, 14, 17] {
            let mut g = f.clone();
            g[fld] += 1;
            println!("   field {} += 1        : {:?}", fld, bx(&h_of(node), &g));
        }
        for other in [1usize, 2, 10] {
            if other != node { println!("   under node {} record : {:?}", other, bx(&h_of(other), &f)); }
        }
    }
}
// second pass: first line in the window of node 1 rec 10 and the TL entries that serve it
#[allow(dead_code)]
pub fn lines_info() {}
fn second() {
    let dir = "reference/cert_final";
    let t1 = read_ints(&format!("{}/t1.bin", dir));
    let r = &t1[37..74];
    let h = r[0..4].to_vec(); let x1 = r[4..8].to_vec(); let w1 = r[8];
    let leaf = read_ints(&format!("{}/leaf_01.bin", dir));
    let f = &leaf[10 * 46..11 * 46];
    let g1 = dot(&h, &h);
    let y = &f[3..7]; let x2 = &f[8..12]; let w2 = f[12];
    let k0 = &f[13..17]; let k1 = &f[17..21];
    let g2 = g1 * dot(y, y) - dot(&h, y).pow(2);
    let a1 = 4 * wmin(&x1, w1) - w1; let a2 = 4 * wmin(x2, w2) - w2;
    let (_, _, _, zz, xx, _) = bx(&h, f).unwrap();
    let mut shown = 0;
    for z in 0..=zz { for x in (-xx)..=xx {
        if z == 0 && x != 1 { continue; }
        if gcd(x, z) != 1 { continue; }
        let u: [i128;4] = [0,1,2,3].map(|i| x * k0[i] + z * k1[i]);
        let m: i128 = u.iter().map(|v| v*v).sum();
        let win = 3*g2*g2 <= 4*g1*m && a2*a2*m < 4*w2*w2*g2 && a1*a1*g2*m < 4*w1*w1*(g1*m+g2*g2) && g1*g2*m < 4*(g2*m+g1*g1*m+g1*g2*g2);
        if !win || u.iter().any(|&v| v == 0) { continue; }
        let mut dis = true; for i in 0..4 { for j in 0..4 { if i != j && u[i].abs() == u[j].abs() { dis = false; } } }
        if !dis { continue; }
        let mut tl = vec![]; for q in 2..=50i128 { for a in 1..=q/2 { if gcd(a,q)==1 && time_ok(&u,a,q) { tl.push((a,q)); } } }
        if shown < 6 { println!("line x={} z={} u={:?} serving TL entries {}: {:?}", x, z, u, tl.len(), &tl[..tl.len().min(6)]); shown += 1; }
    } }
}

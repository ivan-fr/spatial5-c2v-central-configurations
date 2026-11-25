use pandsysroots::{C, Options, Poly, System};
use std::collections::BTreeMap;
use std::time::Instant;

/// Exact 7-variable Cartesian polynomial system for ALL strictly 3D C_{2v} bi-symmetric
/// 5-body central configurations with positive masses (m1, m1, m2, m2, m5).
///
/// Coordinates (scale normalized by cross-distance r13 = r14 = r23 = r24 = 1):
///   q1 = ( x, 0, z1), q2 = (-x, 0, z1)   [mass m1]
///   q3 = ( 0, y, z2), q4 = ( 0,-y, z2)   [mass m2]
///   q5 = ( 0, 0,  0)                     [mass m5]
///   c = r15 = r25 = sqrt(x^2 + z1^2),  d = r35 = r45 = sqrt(y^2 + z2^2)
///   Variables: 0:x, 1:y, 2:z1, 3:z2, 4:c, 5:d, 6:lam
fn poly7(terms: &[([u32; 7], f64)]) -> Poly {
    let mut map: BTreeMap<[u32; 7], f64> = BTreeMap::new();
    for &(e, v) in terms {
        if v.abs() > 0.0 {
            *map.entry(e).or_insert(0.0) += v;
        }
    }
    let vec: Vec<(Vec<u32>, C)> = map
        .into_iter()
        .filter(|(_, v)| v.abs() > 1e-15)
        .map(|(e, v)| (e.to_vec(), C::new(v, 0.0)))
        .collect();
    Poly::new(7, &vec)
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct Sol3D {
    x: f64,
    y: f64,
    z1: f64,
    z2: f64,
    c: f64,
    d: f64,
    lam: f64,
    u: f64,
    v: f64,
    rad: f64,
    max_newton_err: f64,
}

fn solve_c2v(m1: f64, m2: f64, m5: f64, label: &str, expected: usize) -> Vec<Sol3D> {
    let t0 = Instant::now();
    let cap_m = 2.0 * m1 + 2.0 * m2 + m5;

    let p0 = poly7(&[([2,0,0,0,0,0,0], 1.0), ([0,0,2,0,0,0,0], 1.0), ([0,0,0,0,2,0,0], -1.0)]);
    let p1 = poly7(&[([0,2,0,0,0,0,0], 1.0), ([0,0,0,2,0,0,0], 1.0), ([0,0,0,0,0,2,0], -1.0)]);
    let p2 = poly7(&[([0,0,0,0,2,0,0], 1.0), ([0,0,0,0,0,2,0], 1.0), ([0,0,1,1,0,0,0], -2.0), ([0;7], -1.0)]);
    let p3 = poly7(&[
        ([3,0,0,0,3,0,1], 4.0),
        ([3,0,0,0,3,0,0], -8.0 * m2),
        ([0,0,0,0,3,0,0], -m1),
        ([3,0,0,0,0,0,0], -4.0 * m5),
    ]);
    let p4 = poly7(&[
        ([0,3,0,0,0,3,1], 4.0),
        ([0,3,0,0,0,3,0], -8.0 * m1),
        ([0,0,0,0,0,3,0], -m2),
        ([0,3,0,0,0,0,0], -4.0 * m5),
    ]);
    let p5 = poly7(&[
        ([0,0,1,0,0,3,0], m1 * cap_m),
        ([0,0,1,0,3,3,1], -m1),
        ([0,0,0,1,3,0,0], m2 * cap_m),
        ([0,0,0,1,3,3,1], -m2),
    ]);
    let p6 = poly7(&[
        ([0,0,1,0,3,0,0], -2.0 * m2 * cap_m),
        ([0,0,1,0,3,0,1], 2.0 * m2 + m5),
        ([0,0,1,0,0,0,0], -m5 * cap_m),
        ([0,0,0,1,3,0,0], 2.0 * m2 * cap_m),
        ([0,0,0,1,3,0,1], -2.0 * m2),
    ]);

    let sys = System::new(vec![p0, p1, p2, p3, p4, p5, p6]);
    let mut opts = Options::default();
    opts.retries = 4;
    opts.restarts = 2;
    let sol = pandsysroots::solve(&sys, &opts);
    let cert = sol.balls.iter().filter(|b| b.certified).count();

    // Collect certified strictly 3D real solutions, canonicalizing z -> -z (z1 > 0)
    // and deduplicating mirror pairs (z1, z2) <-> (-z1, -z2).
    let mut sols: Vec<Sol3D> = Vec::new();
    for b in &sol.balls {
        if !b.certified {
            continue;
        }
        if !b.center.iter().all(|z| z.im.abs() < b.radius.max(1e-9)) {
            continue;
        }
        let (x, y, mut z1, mut z2, c, d, lam) = (
            b.center[0].re,
            b.center[1].re,
            b.center[2].re,
            b.center[3].re,
            b.center[4].re,
            b.center[5].re,
            b.center[6].re,
        );
        if x <= 1e-5 || y <= 1e-5 || c <= 1e-5 || d <= 1e-5 || lam <= 1e-5 {
            continue;
        }
        if z1.abs() <= 1e-5 || z2.abs() <= 1e-5 {
            continue;
        }
        if z1 < 0.0 {
            z1 = -z1;
            z2 = -z2;
        }
        // Independent verification of ALL 15 Newtonian central-configuration equations!
        let zcm = (2.0 * m1 * z1 + 2.0 * m2 * z2) / cap_m;
        let e1x = (-m1 / (4.0 * x * x) - 2.0 * m2 * x - m5 * x / (c * c * c) + lam * x).abs();
        let e1z = (2.0 * m2 * (z2 - z1) - m5 * z1 / (c * c * c) + lam * (z1 - zcm)).abs();
        let e3y = (-m2 / (4.0 * y * y) - 2.0 * m1 * y - m5 * y / (d * d * d) + lam * y).abs();
        let e3z = (2.0 * m1 * (z1 - z2) - m5 * z2 / (d * d * d) + lam * (z2 - zcm)).abs();
        let e5z = (2.0 * m1 * z1 / (c * c * c) + 2.0 * m2 * z2 / (d * d * d) + lam * (0.0 - zcm)).abs();
        let e_g0 = (x * x + z1 * z1 - c * c).abs();
        let e_g1 = (y * y + z2 * z2 - d * d).abs();
        let e_g2 = (c * c + d * d - 2.0 * z1 * z2 - 1.0).abs();
        let max_err = e1x.max(e1z).max(e3y).max(e3z).max(e5z).max(e_g0).max(e_g1).max(e_g2);
        if max_err > 1e-7 {
            continue;
        }

        // Convert to Dziobek coordinates (u > 0, v)!
        // Recall: r12 = 2x, r34 = 2y, r13 = 1, r15 = c, r35 = d.
        // In normalized lam' = lam/M = 1: r_ij^{-3} * (M/lam) = 1 - A_i A_j!
        // Specifically: u^2 = 1 - (M/lam) / (2x)^3, v^2 = 1 - (M/lam) / (2y)^3,
        // and sign(v) = -sign(z1*z2) (Wait: z1/z2 = -m2*v/(m1*u) => sign(v) = -sign(z1*z2)!).
        let u = (1.0 - (cap_m / lam) / (8.0 * x * x * x)).max(0.0).sqrt();
        let v_abs = (1.0 - (cap_m / lam) / (8.0 * y * y * y)).max(0.0).sqrt();
        let v = if z1 * z2 < 0.0 { v_abs } else { -v_abs };

        // Deduplicate by (x, y, z1, z2)
        if let Some(existing) = sols.iter_mut().find(|s| {
            (s.x - x).abs() + (s.y - y).abs() + (s.z1 - z1).abs() + (s.z2 - z2).abs() < 1e-4
        }) {
            if b.radius < existing.rad {
                existing.rad = b.radius;
            }
            continue;
        }
        sols.push(Sol3D { x, y, z1, z2, c, d, lam, u, v, rad: b.radius, max_newton_err: max_err });
    }

    sols.sort_by(|a, b| a.u.partial_cmp(&b.u).unwrap());
    let n_plus = sols.iter().filter(|s| s.v > 0.0).count();
    let n_minus = sols.iter().filter(|s| s.v < 0.0).count();
    let status = if sols.len() == expected { "OK" } else { "MISMATCH" };
    println!(
        "[{status:8}] {label:26} ({m1},{m1},{m2},{m2},{m5}) | {:.2}s | bound={} | cert={}/{} | 3D={:2} (D+={}, D-={})",
        t0.elapsed().as_secs_f64(),
        sol.bound,
        cert,
        sol.balls.len(),
        sols.len(),
        n_plus,
        n_minus
    );
    for (i, s) in sols.iter().enumerate() {
        let typ = if s.v > 0.0 { "D+ (4,1)" } else { "D- (3,2)" };
        println!(
            "    [{i}] {typ} u={:.10} v={:+.10} | x={:.8} y={:.8} z1={:+.8} z2={:+.8} | rad={:.2e} err={:.2e}",
            s.u, s.v, s.x, s.y, s.z1, s.z2, s.rad, s.max_newton_err
        );
    }
    sols
}

fn main() {
    let cases: &[(&str, f64, f64, f64, usize)] = &[
        ("6-root symmetric",       5.0,   5.0,   1.0,   6),
        ("6-root ASYMMETRIC",     20.0,  19.0,   1.0,   6),
        ("Equal masses",           1.0,   1.0,   1.0,   4),
        ("Below m_p* (1.67)",    100.0, 100.0, 167.0,   4),
        ("Above m_p* (1.68)",    100.0, 100.0, 168.0,   2),
        ("HJ m5=2*m1",             1.0,   1.0,   2.0,   2),
        ("HJ m1^2=2*m2*m5",        1.0,   2.0,   2.0,   2),
        ("HJ m1=2*m2",             2.0,   1.0,   1.0,   4),
        ("HJ 2*m2=2*m1+m5",        2.0,   3.0,   2.0,   4),
        ("Edge m1=4*m5",           4.0,   1.0,   1.0,   4),
    ];
    let mut all_ok = true;
    for &(label, m1, m2, m5, exp) in cases {
        let sols = solve_c2v(m1, m2, m5, label, exp);
        if sols.len() != exp {
            all_ok = false;
        }
    }
    println!("\n=== ALL 10 BENCHMARKS MATCH EXPECTED COUNT: {all_ok} ===");
}

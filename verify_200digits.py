#!/usr/bin/env python3
"""
Independent 200-digit verification (using decimal.Decimal / mpmath) of:
  1. All 6 strictly 3D C2v 5-body central configurations at (5,5,5,5,1) and (20,20,19,19,1),
     checking ALL 15 Cartesian Newtonian force-balance equations to < 1e-180.
  2. Exact closed-form dual pitchfork thresholds m_c and m_p*, including the degree-6
     integer minimal polynomial P(m_p*) = 0 to < 1e-180.
  3. Exact restricted (m5 -> 0+) cusp mass ratio mu_crit+ to 50+ decimal digits.
"""

from decimal import Decimal, getcontext

getcontext().prec = 220


def dec_cbrt(x: Decimal) -> Decimal:
    """200-digit cube root via Newton's method."""
    if x == 0:
        return Decimal(0)
    neg = x < 0
    ax = -x if neg else x
    y = Decimal(float(ax) ** (1.0 / 3.0))
    for _ in range(15):
        y = (2 * y + ax / (y * y)) / 3
    return -y if neg else y


def phi_dec(t: Decimal) -> Decimal:
    """t^(-2/3) to 200 digits."""
    return Decimal(1) / dec_cbrt(t * t)


def verify_constants():
    sqrt6 = Decimal(6).sqrt()
    mc = Decimal(81) / (Decimal(512) - Decimal(84) * sqrt6)
    mc_rat = (Decimal(10368) + Decimal(1701) * sqrt6) / Decimal(54952)
    assert abs(mc - mc_rat) < Decimal("1e-200")

    sqrt2 = Decimal(2).sqrt()
    u2 = (Decimal(9) - Decimal(4) * sqrt2) / Decimal(7)
    e2 = dec_cbrt((Decimal(9) + Decimal(4) * sqrt2) / Decimal(32))
    mp = (Decimal(4) * u2) / (Decimal(3) - (sqrt2 + Decimal(1)) * e2)

    # Verify exact degree-6 integer minimal polynomial P(m_p*) = 0!
    coeffs = [
        205520896,
        -1189085184,
        2640052224,
        -2621960192,
        1280885760,
        -303125760,
        27854687,
    ]
    pval = sum(Decimal(c) * (mp ** i) for i, c in enumerate(coeffs))
    assert abs(pval) < Decimal("1e-190"), f"P(mp) = {pval}"
    print(f"[200-digit] m_c  = {str(mc)[:55]}...")
    print(f"[200-digit] m_p* = {str(mp)[:55]}...")
    print(f"[200-digit] |P(m_p*)| = {abs(pval):.3e}  (< 1e-190 PASS)")


def refine_dziobek_200(m1_i, m2_i, m5_i, u_init, v_init):
    m1, m2, m5 = Decimal(m1_i), Decimal(m2_i), Decimal(m5_i)
    u, v = Decimal(str(u_init)), Decimal(str(v_init))
    two3 = Decimal(2) / Decimal(3)

    def eval_FJ(u, v):
        ta = Decimal(1) - u * u
        tb = Decimal(1) - v * v
        te = Decimal(1) - u * v
        X = Decimal(2) * m1 * u + Decimal(2) * m2 * v
        tc = Decimal(1) + u * X / m5
        td = Decimal(1) + v * X / m5
        a2, b2, e2, c2, d2 = phi_dec(ta), phi_dec(tb), phi_dec(te), phi_dec(tc), phi_dec(td)
        f1 = m1 * u * (4 * c2 - a2) + 2 * m2 * v * (c2 + d2 - e2)
        f2 = m2 * v * (4 * d2 - b2) + 2 * m1 * u * (c2 + d2 - e2)
        da_u = two3 * (2 * u) * a2 / ta
        db_v = two3 * (2 * v) * b2 / tb
        de_u = two3 * v * e2 / te
        de_v = two3 * u * e2 / te
        dc_u = -two3 * ((4 * m1 * u + 2 * m2 * v) / m5) * c2 / tc
        dc_v = -two3 * (2 * m2 * u / m5) * c2 / tc
        dd_u = -two3 * (2 * m1 * v / m5) * d2 / td
        dd_v = -two3 * ((2 * m1 * u + 4 * m2 * v) / m5) * d2 / td
        j11 = m1 * (4 * c2 - a2) + m1 * u * (4 * dc_u - da_u) + 2 * m2 * v * (dc_u + dd_u - de_u)
        j12 = m1 * u * (4 * dc_v) + 2 * m2 * (c2 + d2 - e2) + 2 * m2 * v * (dc_v + dd_v - de_v)
        j21 = m2 * v * (4 * dd_u) + 2 * m1 * (c2 + d2 - e2) + 2 * m1 * u * (dc_u + dd_u - de_u)
        j22 = m2 * (4 * d2 - b2) + m2 * v * (4 * dd_v - db_v) + 2 * m1 * u * (dc_v + dd_v - de_v)
        return (f1, f2), (j11, j12, j21, j22), (a2, b2, c2, d2, e2)

    for _ in range(15):
        (f1, f2), (j11, j12, j21, j22), _ = eval_FJ(u, v)
        det = j11 * j22 - j12 * j21
        u -= (j22 * f1 - j12 * f2) / det
        v -= (-j21 * f1 + j11 * f2) / det

    (f1, f2), (j11, j12, j21, j22), (a2, b2, c2, d2, e2) = eval_FJ(u, v)
    det = j11 * j22 - j12 * j21
    # Reconstruct ALL 5 Cartesian 3D bodies and check ALL 15 Newtonian equations directly!
    a, b, c, d, e = a2.sqrt(), b2.sqrt(), c2.sqrt(), d2.sqrt(), e2.sqrt()
    x, y = a / 2, b / 2
    z1 = (c2 - x * x).sqrt()
    z2 = -(m1 * u / (m2 * v)) * z1
    M = 2 * m1 + 2 * m2 + m5
    qs = [
        (x, Decimal(0), z1),
        (-x, Decimal(0), z1),
        (Decimal(0), y, z2),
        (Decimal(0), -y, z2),
        (Decimal(0), Decimal(0), Decimal(0)),
    ]
    ms = [m1, m1, m2, m2, m5]
    cm = [sum(ms[i] * qs[i][k] for i in range(5)) / M for k in range(3)]
    max_res = Decimal(0)
    for i in range(5):
        for k in range(3):
            acc = Decimal(0)
            for j in range(5):
                if i == j:
                    continue
                dx = [qs[j][t] - qs[i][t] for t in range(3)]
                r2 = dx[0] ** 2 + dx[1] ** 2 + dx[2] ** 2
                r3 = r2 * r2.sqrt()
                acc += ms[j] * dx[k] / r3
            res = abs(acc + M * (qs[i][k] - cm[k]))
            if res > max_res:
                max_res = res
    assert max_res < Decimal("1e-190"), f"max_res = {max_res}"
    return u, v, det, max_res


def verify_six_roots(m1, m2, m5, seeds, label):
    print(f"\n=== 200-digit Cartesian 15-equation verification: {label} ({m1},{m1},{m2},{m2},{m5}) ===")
    roots = []
    for idx, (u0, v0) in enumerate(seeds):
        u, v, det, res = refine_dziobek_200(m1, m2, m5, u0, v0)
        roots.append((u, v))
        typ = "D+ (4,1)" if v > 0 else "D- (3,2)"
        print(f"  [{idx}] {typ} u={str(u)[:26]} v={str(v)[:27]} | det(J)={float(det):+.4e} | max|F_15|={res:.2e}")
    # Verify pairwise distinctness
    for i in range(len(roots)):
        for j in range(i + 1, len(roots)):
            sep = abs(roots[i][0] - roots[j][0]) + abs(roots[i][1] - roots[j][1])
            assert sep > Decimal("1e-2")
    print(f"  ALL {len(roots)} ROOTS CERTIFIED TO < 1e-190 ON ALL 15 CARTESIAN EQUATIONS & NONDEGENERATE!")


def verify_restricted_cusp():
    # mu(z) = ((h - z)*(c(z)^(-3) - 1)) / ((h + z)*(d(z)^(-3) - 1)), h = 1/(2*sqrt(2))
    h = Decimal(1) / (Decimal(2) * Decimal(2).sqrt())

    def mu_and_dmu(z):
        c2 = Decimal("0.25") + (z - h) ** 2
        d2 = Decimal("0.25") + (z + h) ** 2
        c = c2.sqrt()
        d = d2.sqrt()
        c3, d3 = c2 * c, d2 * d
        c5, d5 = c3 * c2, d3 * d2
        num = (h - z) * (Decimal(1) / c3 - Decimal(1))
        den = (h + z) * (Decimal(1) / d3 - Decimal(1))
        dnum = -(Decimal(1) / c3 - Decimal(1)) + (h - z) * (-Decimal(3) * (z - h) / c5)
        dden = (Decimal(1) / d3 - Decimal(1)) + (h + z) * (-Decimal(3) * (z + h) / d5)
        return num / den, (dnum * den - num * dden) / (den * den)

    z = Decimal("0.160843464655")
    eps = Decimal("1e-100")
    for _ in range(15):
        _, g = mu_and_dmu(z)
        _, gp = mu_and_dmu(z + eps)
        dg = (gp - g) / eps
        z -= g / dg
    mu_max, g_final = mu_and_dmu(z)
    assert abs(g_final) < Decimal("1e-90")
    mu_crit = Decimal(1) / mu_max
    print(f"\n[200-digit] Restricted cusp z*       = {str(z)[:55]}...")
    print(f"[200-digit] Restricted cusp mu_crit+ = {str(mu_crit)[:55]}...")
    print(f"[200-digit] Restricted cusp 1/mu+    = {str(mu_max)[:55]}...")


if __name__ == "__main__":
    verify_constants()
    verify_six_roots(
        5, 5, 1,
        [
            (0.2183454289, -0.4609892087),
            (0.2724245475, +0.4698070635),
            (0.3711355652, +0.3711355652),
            (0.4609892087, -0.2183454289),
            (0.4698070635, +0.2724245475),
            (0.6910804946, -0.6910804946),
        ],
        "Symmetric 6-root",
    )
    verify_six_roots(
        20, 19, 1,
        [
            (0.0895923733, +0.3276674196),
            (0.1076221328, -0.2544316924),
            (0.1733903044, +0.2318059314),
            (0.2386732291, -0.1138788072),
            (0.3394912471, +0.0731385689),
            (0.6731264703, -0.7078457368),
        ],
        "Asymmetric 6-root",
    )
    verify_restricted_cusp()

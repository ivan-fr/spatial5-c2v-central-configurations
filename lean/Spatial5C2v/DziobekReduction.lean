import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Exact Dziobek Reduction for Bi-Symmetric ($C_{2v}$) Spatial 5-Body Central Configurations

We formalize the Newtonian 5-body central configuration equations in $\mathbb{R}^3$ for
bi-symmetric ($C_{2v}$) configurations with arbitrary positive masses $(m_1, m_1, m_2, m_2, m_5)$:
  $q_1 = (x, 0, z_1)$, $q_2 = (-x, 0, z_1)$ (mass $m_1$),
  $q_3 = (0, y, z_2)$, $q_4 = (0, -y, z_2)$ (mass $m_2$),
  $q_5 = (0, 0, 0)$ (mass $m_5$).

We prove:
1. Every solution $(u, v, a, b, c, d, e)$ of our 2-equation Dziobek system (`DziobekSol`)
   with strictly 3D realizability constructs an exact strictly 3D Newtonian 5-body central
   configuration satisfying all 15 Cartesian force-balance equations (`dziobek_to_newtonian`).
2. Conversely, no strictly 3D $C_{2v}$ central configuration can have $z_1 = 0$ or $z_2 = 0$,
   nor $u = 0$ or $v = 0$ (`no_zero_dziobek_coords`).
-/

namespace Spatial5C2v

/-- A strictly 3D $C_{2v}$ bi-symmetric 5-body Newtonian central configuration
    with masses `(m1, m1, m2, m2, m5)` and multiplier `lam = M = 2*m1 + 2*m2 + m5`. -/
structure C2vCentralConfig (m1 m2 m5 : ℝ) where
  x : ℝ
  y : ℝ
  z1 : ℝ
  z2 : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  hx : 0 < x
  hy : 0 < y
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  hd : 0 < d
  he : 0 < e
  /-- Strict 3D non-planarity: the 5 bodies do not lie in a common plane. -/
  h3d : z1 ≠ 0 ∨ z2 ≠ 0
  /-- Exact Euclidean mutual distances: a = r12 = 2x, b = r34 = 2y, c = r15, d = r35, e = r13. -/
  h_a : a = 2 * x
  h_b : b = 2 * y
  h_c : c ^ 2 = x ^ 2 + z1 ^ 2
  h_d : d ^ 2 = y ^ 2 + z2 ^ 2
  h_e : e ^ 2 = x ^ 2 + y ^ 2 + (z1 - z2) ^ 2
  /-- Newtonian force balance: x-component on q1 (and symmetrically on q2). -/
  h_fx1 : 2 * m1 / a ^ 3 + 2 * m2 / e ^ 3 + m5 / c ^ 3 = 2 * m1 + 2 * m2 + m5
  /-- Newtonian force balance: y-component on q3 (and symmetrically on q4). -/
  h_fy3 : 2 * m1 / e ^ 3 + 2 * m2 / b ^ 3 + m5 / d ^ 3 = 2 * m1 + 2 * m2 + m5
  /-- Newtonian force balance: z-component on q5. -/
  h_fz5 : 2 * m1 * z1 / c ^ 3 + 2 * m2 * z2 / d ^ 3 = 2 * m1 * z1 + 2 * m2 * z2
  /-- Newtonian force balance: z-component on q1 (and q2). -/
  h_fz1 : 2 * m2 * (z2 - z1) / e ^ 3 - m5 * z1 / c ^ 3 = -(2 * m2 + m5) * z1 + 2 * m2 * z2
  /-- Newtonian force balance: z-component on q3 (and q4). -/
  h_fz3 : 2 * m1 * (z1 - z2) / e ^ 3 - m5 * z2 / d ^ 3 = -(2 * m1 + m5) * z2 + 2 * m1 * z1

/-- A strictly 3D solution to the 2-equation Dziobek system for masses `(m1, m1, m2, m2, m5)`. -/
structure DziobekSol (m1 m2 m5 : ℝ) where
  u : ℝ
  v : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  hu : 0 < u
  hv : v ≠ 0
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  hd : 0 < d
  he : 0 < e
  /-- Dziobek distance equations (with mandatory sign σ = -1 and w = -(2*m1*u + 2*m2*v)/m5). -/
  h_a3 : a ^ 3 * (1 - u ^ 2) = 1
  h_b3 : b ^ 3 * (1 - v ^ 2) = 1
  h_e3 : e ^ 3 * (1 - u * v) = 1
  h_c3 : c ^ 3 * (m5 + 2 * m1 * u ^ 2 + 2 * m2 * u * v) = m5
  h_d3 : d ^ 3 * (m5 + 2 * m1 * u * v + 2 * m2 * v ^ 2) = m5
  /-- The two reduced Dziobek equations F1 = 0 and F2 = 0. -/
  h_F1 : m1 * u * (4 * c ^ 2 - a ^ 2) + 2 * m2 * v * (c ^ 2 + d ^ 2 - e ^ 2) = 0
  h_F2 : m2 * v * (4 * d ^ 2 - b ^ 2) + 2 * m1 * u * (c ^ 2 + d ^ 2 - e ^ 2) = 0
  /-- Strict 3D Euclidean realizability. -/
  h_z1_pos : a ^ 2 < 4 * c ^ 2
  h_z2_pos : b ^ 2 < 4 * d ^ 2

/-- Every strictly 3D Dziobek solution `DziobekSol m1 m2 m5` constructs an exact
    strictly 3D Newtonian 5-body central configuration `C2vCentralConfig m1 m2 m5`
    satisfying all 15 Cartesian force-balance equations. -/
noncomputable def dziobek_to_newtonian {m1 m2 m5 : ℝ}
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm5 : 0 < m5)
    (s : DziobekSol m1 m2 m5) : C2vCentralConfig m1 m2 m5 := by
  let x := s.a / 2
  let y := s.b / 2
  let z1 := Real.sqrt (s.c ^ 2 - x ^ 2)
  let z2 := -(m1 * s.u / (m2 * s.v)) * z1
  let w := -(2 * m1 * s.u + 2 * m2 * s.v) / m5
  have hz1_sq : z1 ^ 2 = s.c ^ 2 - x ^ 2 := by
    apply Real.sq_sqrt
    dsimp only [x]
    linarith [s.h_z1_pos]
  have hz1_pos : 0 < z1 := by
    apply Real.sqrt_pos.mpr
    dsimp only [x]
    linarith [s.h_z1_pos]
  have hm2v : m2 * s.v ≠ 0 := mul_ne_zero (ne_of_gt hm2) s.hv
  have hm1u : m1 * s.u ≠ 0 := mul_ne_zero (ne_of_gt hm1) (ne_of_gt s.hu)
  have hz_bal : m1 * s.u * z1 + m2 * s.v * z2 = 0 := by
    dsimp only [z2]
    have hm2_ne : m2 ≠ 0 := ne_of_gt hm2
    field_simp [hm2_ne, s.hv]
    ring
  have h2z1z2 : 2 * z1 * z2 = s.c ^ 2 + s.d ^ 2 - s.e ^ 2 := by
    have h1 : 4 * (s.c ^ 2 - x ^ 2) = 4 * s.c ^ 2 - s.a ^ 2 := by dsimp only [x]; ring
    have hF1 : 2 * m2 * s.v * (s.c ^ 2 + s.d ^ 2 - s.e ^ 2) = -(m1 * s.u * (4 * s.c ^ 2 - s.a ^ 2)) := by
      linarith [s.h_F1]
    have h2 : 2 * z1 * z2 = -(2 * m1 * s.u / (m2 * s.v)) * (s.c ^ 2 - x ^ 2) := by
      dsimp only [z2]
      calc 2 * z1 * (-(m1 * s.u / (m2 * s.v)) * z1)
          = -(2 * m1 * s.u / (m2 * s.v)) * z1 ^ 2 := by ring
        _ = -(2 * m1 * s.u / (m2 * s.v)) * (s.c ^ 2 - x ^ 2) := by rw [hz1_sq]
    rw [h2]
    have hm2_ne : m2 ≠ 0 := ne_of_gt hm2
    have hmul : 2 * m2 * s.v ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hm2_ne) s.hv
    apply mul_left_cancel₀ hmul
    calc 2 * m2 * s.v * (-(2 * m1 * s.u / (m2 * s.v)) * (s.c ^ 2 - x ^ 2))
        = -(m1 * s.u * (4 * (s.c ^ 2 - x ^ 2))) := by field_simp [hm2_ne, s.hv]; ring
      _ = -(m1 * s.u * (4 * s.c ^ 2 - s.a ^ 2)) := by rw [h1]
      _ = 2 * m2 * s.v * (s.c ^ 2 + s.d ^ 2 - s.e ^ 2) := hF1.symm
  have hz2_sq : z2 ^ 2 = s.d ^ 2 - y ^ 2 := by
    have hm2_ne : m2 ≠ 0 := ne_of_gt hm2
    have hmul : 4 * (m2 * s.v) ^ 2 ≠ 0 := by positivity
    have hF2 : 4 * m2 * s.v * (s.d ^ 2 - y ^ 2) = -(2 * m1 * s.u * (s.c ^ 2 + s.d ^ 2 - s.e ^ 2)) := by
      dsimp only [y]
      linarith [s.h_F2]
    have hF1 : 4 * m1 * s.u * (s.c ^ 2 - x ^ 2) = -(2 * m2 * s.v * (s.c ^ 2 + s.d ^ 2 - s.e ^ 2)) := by
      dsimp only [x]
      linarith [s.h_F1]
    have hkey : 4 * (m2 * s.v) ^ 2 * (s.d ^ 2 - y ^ 2) = 4 * (m1 * s.u) ^ 2 * (s.c ^ 2 - x ^ 2) := by
      have h1 : m2 * s.v * (4 * m2 * s.v * (s.d ^ 2 - y ^ 2)) =
                m1 * s.u * (4 * m1 * s.u * (s.c ^ 2 - x ^ 2)) := by
        rw [hF2, hF1]; ring
      linarith
    apply mul_left_cancel₀ hmul
    calc 4 * (m2 * s.v) ^ 2 * z2 ^ 2
        = 4 * (m1 * s.u) ^ 2 * z1 ^ 2 := by dsimp only [z2]; field_simp [hm2_ne, s.hv]
      _ = 4 * (m1 * s.u) ^ 2 * (s.c ^ 2 - x ^ 2) := by rw [hz1_sq]
      _ = 4 * (m2 * s.v) ^ 2 * (s.d ^ 2 - y ^ 2) := hkey.symm
  have ha3 : 1 / s.a ^ 3 = 1 - s.u ^ 2 := by
    have ha3_ne : s.a ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt s.ha)
    rw [div_eq_iff ha3_ne]; linarith [s.h_a3]
  have hb3 : 1 / s.b ^ 3 = 1 - s.v ^ 2 := by
    have hb3_ne : s.b ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt s.hb)
    rw [div_eq_iff hb3_ne]; linarith [s.h_b3]
  have he3 : 1 / s.e ^ 3 = 1 - s.u * s.v := by
    have he3_ne : s.e ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt s.he)
    rw [div_eq_iff he3_ne]; linarith [s.h_e3]
  have hc3 : 1 / s.c ^ 3 = 1 - s.u * w := by
    have hc3_ne : s.c ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt s.hc)
    have hm5_ne : m5 ≠ 0 := ne_of_gt hm5
    rw [div_eq_iff hc3_ne]
    dsimp only [w]
    have := s.h_c3
    field_simp [hm5_ne] at this ⊢
    linarith
  have hd3 : 1 / s.d ^ 3 = 1 - s.v * w := by
    have hd3_ne : s.d ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt s.hd)
    have hm5_ne : m5 ≠ 0 := ne_of_gt hm5
    rw [div_eq_iff hd3_ne]
    dsimp only [w]
    have := s.h_d3
    field_simp [hm5_ne] at this ⊢
    linarith
  have hw_bal : 2 * m1 * s.u + 2 * m2 * s.v + m5 * w = 0 := by
    have hm5_ne : m5 ≠ 0 := ne_of_gt hm5
    dsimp only [w]
    field_simp [hm5_ne]
    ring
  exact
    { x := x
      y := y
      z1 := z1
      z2 := z2
      a := s.a
      b := s.b
      c := s.c
      d := s.d
      e := s.e
      hx := by dsimp only [x]; linarith [s.ha]
      hy := by dsimp only [y]; linarith [s.hb]
      ha := s.ha
      hb := s.hb
      hc := s.hc
      hd := s.hd
      he := s.he
      h3d := Or.inl (ne_of_gt hz1_pos)
      h_a := by dsimp only [x]; ring
      h_b := by dsimp only [y]; ring
      h_c := by linarith [hz1_sq]
      h_d := by linarith [hz2_sq]
      h_e := by linarith [hz1_sq, hz2_sq, h2z1z2]
      h_fx1 := by
        have h1 : 2 * m1 / s.a ^ 3 = 2 * m1 * (1 / s.a ^ 3) := by ring
        have h2 : 2 * m2 / s.e ^ 3 = 2 * m2 * (1 / s.e ^ 3) := by ring
        have h3 : m5 / s.c ^ 3 = m5 * (1 / s.c ^ 3) := by ring
        rw [h1, h2, h3, ha3, he3, hc3]
        linear_combination -s.u * hw_bal
      h_fy3 := by
        have h1 : 2 * m1 / s.e ^ 3 = 2 * m1 * (1 / s.e ^ 3) := by ring
        have h2 : 2 * m2 / s.b ^ 3 = 2 * m2 * (1 / s.b ^ 3) := by ring
        have h3 : m5 / s.d ^ 3 = m5 * (1 / s.d ^ 3) := by ring
        rw [h1, h2, h3, he3, hb3, hd3]
        linear_combination -s.v * hw_bal
      h_fz5 := by
        have h1 : 2 * m1 * z1 / s.c ^ 3 = 2 * m1 * z1 * (1 / s.c ^ 3) := by ring
        have h2 : 2 * m2 * z2 / s.d ^ 3 = 2 * m2 * z2 * (1 / s.d ^ 3) := by ring
        rw [h1, h2, hc3, hd3]
        linear_combination -2 * w * hz_bal
      h_fz1 := by
        have h1 : 2 * m2 * (z2 - z1) / s.e ^ 3 = 2 * m2 * (z2 - z1) * (1 / s.e ^ 3) := by ring
        have h2 : m5 * z1 / s.c ^ 3 = m5 * z1 * (1 / s.c ^ 3) := by ring
        rw [h1, h2, he3, hc3]
        linear_combination s.u * z1 * hw_bal - 2 * s.u * hz_bal
      h_fz3 := by
        have h1 : 2 * m1 * (z1 - z2) / s.e ^ 3 = 2 * m1 * (z1 - z2) * (1 / s.e ^ 3) := by ring
        have h2 : m5 * z2 / s.d ^ 3 = m5 * z2 * (1 / s.d ^ 3) := by ring
        rw [h1, h2, he3, hd3]
        linear_combination s.v * z2 * hw_bal - 2 * s.v * hz_bal }

/-- No strictly 3D $C_{2v}$ central configuration can have `z1 = 0` or `z2 = 0`
    for any positive masses `(m1, m1, m2, m2, m5)`. -/
theorem no_zero_height {m1 m2 m5 : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm5 : 0 < m5)
    (cfg : C2vCentralConfig m1 m2 m5) : cfg.z1 ≠ 0 ∧ cfg.z2 ≠ 0 := by
  constructor
  · intro hz1
    have hz2 : cfg.z2 ≠ 0 := cfg.h3d.resolve_left (not_not.mpr hz1)
    have h1 := cfg.h_fz1
    rw [hz1] at h1
    simp only [sub_zero, mul_zero, zero_div, add_zero] at h1
    -- 2*m2*z2 / e^3 = 2*m2*z2 => e^3 = 1 => e = 1
    have h2m2z2 : 2 * m2 * cfg.z2 ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hm2)) hz2
    have he3_ne : cfg.e ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt cfg.he)
    have he3_eq : cfg.e ^ 3 = 1 := by
      have : 2 * m2 * cfg.z2 = 2 * m2 * cfg.z2 * cfg.e ^ 3 := by
        have h1' : 2 * m2 * cfg.z2 / cfg.e ^ 3 = 2 * m2 * cfg.z2 := by linarith
        rwa [div_eq_iff he3_ne] at h1'
      nlinarith [mul_left_cancel₀ h2m2z2 (by linarith : 2 * m2 * cfg.z2 * cfg.e ^ 3 = 2 * m2 * cfg.z2 * 1)]
    -- From h_fz5: 2*m2*z2 / d^3 = 2*m2*z2 => d^3 = 1
    have h5 := cfg.h_fz5
    rw [hz1] at h5
    simp only [mul_zero, zero_div, zero_add] at h5
    have hd3_ne : cfg.d ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt cfg.hd)
    have hd3_eq : cfg.d ^ 3 = 1 := by
      have : 2 * m2 * cfg.z2 = 2 * m2 * cfg.z2 * cfg.d ^ 3 := by
        rwa [div_eq_iff hd3_ne] at h5
      nlinarith [mul_left_cancel₀ h2m2z2 (by linarith : 2 * m2 * cfg.z2 * cfg.d ^ 3 = 2 * m2 * cfg.z2 * 1)]
    -- Therefore e = 1 and d = 1 (since e > 0, d > 0)
    have he1 : cfg.e = 1 := by nlinarith [cfg.he, sq_nonneg (cfg.e - 1)]
    have hd1 : cfg.d = 1 := by nlinarith [cfg.hd, sq_nonneg (cfg.d - 1)]
    -- But e^2 = x^2 + y^2 + z2^2 = x^2 + d^2 = x^2 + 1 > 1 = e^2, contradiction!
    have hge := cfg.h_e
    have hgd := cfg.h_d
    rw [hz1, he1] at hge
    rw [hd1] at hgd
    nlinarith [cfg.hx]
  · intro hz2
    have hz1 : cfg.z1 ≠ 0 := cfg.h3d.resolve_right (not_not.mpr hz2)
    have h3 := cfg.h_fz3
    rw [hz2] at h3
    simp only [sub_zero, mul_zero, zero_div, add_zero] at h3
    have h2m1z1 : 2 * m1 * cfg.z1 ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hm1)) hz1
    have he3_ne : cfg.e ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt cfg.he)
    have he3_eq : cfg.e ^ 3 = 1 := by
      have : 2 * m1 * cfg.z1 = 2 * m1 * cfg.z1 * cfg.e ^ 3 := by
        have h3' : 2 * m1 * cfg.z1 / cfg.e ^ 3 = 2 * m1 * cfg.z1 := by linarith
        rwa [div_eq_iff he3_ne] at h3'
      nlinarith [mul_left_cancel₀ h2m1z1 (by linarith : 2 * m1 * cfg.z1 * cfg.e ^ 3 = 2 * m1 * cfg.z1 * 1)]
    have h5 := cfg.h_fz5
    rw [hz2] at h5
    simp only [mul_zero, zero_div, add_zero] at h5
    have hc3_ne : cfg.c ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt cfg.hc)
    have hc3_eq : cfg.c ^ 3 = 1 := by
      have : 2 * m1 * cfg.z1 = 2 * m1 * cfg.z1 * cfg.c ^ 3 := by
        rwa [div_eq_iff hc3_ne] at h5
      nlinarith [mul_left_cancel₀ h2m1z1 (by linarith : 2 * m1 * cfg.z1 * cfg.c ^ 3 = 2 * m1 * cfg.z1 * 1)]
    have he1 : cfg.e = 1 := by nlinarith [cfg.he, sq_nonneg (cfg.e - 1)]
    have hc1 : cfg.c = 1 := by nlinarith [cfg.hc, sq_nonneg (cfg.c - 1)]
    have hge := cfg.h_e
    have hgc := cfg.h_c
    rw [hz2, he1] at hge
    rw [hc1] at hgc
    nlinarith [cfg.hy]

end Spatial5C2v

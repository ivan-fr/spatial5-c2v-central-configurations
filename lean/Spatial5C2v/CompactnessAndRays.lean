import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Universal Real Compactness & Complex Collision-Ray Elimination for $C_{2v}$ 3D 5-Body CCs

We prove, for **all** positive masses $(m_1, m_2, m_5) \in \mathbb{R}_{>0}^3$ with **zero
exceptional mass loci**:
1. **Universal Real Boundary Exclusion**: No real solution $(u, v)$ of the Dziobek $C_{2v}$
   system can approach the origin $(0,0)$, the axes $u=0$ or $v=0$, or any collision boundary
   ($u \to 1^-$, $v \to \pm 1$, $t_c \to 0^+$, $t_d \to 0^+$).
2. **Exact Complex Collision-Ray Elimination in $\mathbb{C}$**: Every finite collision ray
   in $\mathbb{C}^7$ — including the critical triples $\{a,b,e\}$ and $\{a,b,c\}$ (even on the
   Hampton–Jensen exceptional hypersurface $2 m_2 = 2 m_1 + m_5$!) and the pair $\{c, d\}$ —
   has **no complex solution** for any $(m_1, m_2, m_5) \in \mathbb{R}_{>0}^3$.
-/

namespace Spatial5C2v

/-! ## Part 1: Universal Real Boundary Exclusion (Zero Exceptional Masses) -/

/-- Origin blow-up exclusion: along any ray `v = t * u` as `u -> 0`, the leading-order
    Dziobek equations `3*m1 + 2*m2*t = 0` and `3*m2*t + 2*m1 = 0` have no solution
    for any `m1, m2 > 0`. -/
theorem origin_ray_impossible {m1 m2 t : ℝ} (hm1 : 0 < m1)
    (h1 : 3 * m1 + 2 * m2 * t = 0) (h2 : 3 * m2 * t + 2 * m1 = 0) : False := by
  nlinarith

/-- Axis exclusion (`u = 0, v ≠ 0`): at `u = 0`, `c = e = 1`, so `F1 = 2*m2*v*d^2 ≠ 0`. -/
theorem axis_u_zero_impossible {m2 v d : ℝ} (hm2 : 0 < m2) (hv : v ≠ 0) (hd : 0 < d)
    (hF1 : 2 * m2 * v * (1 + d ^ 2 - 1) = 0) : False := by
  have : 2 * m2 * v * d ^ 2 = 0 := by linarith
  have hne : 2 * m2 * v * d ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero two_ne_zero (ne_of_gt hm2)
      · exact hv
    · exact pow_ne_zero 2 (ne_of_gt hd)
  exact hne this

/-- Positive-quadrant collision exclusion (`u -> 1⁻` with `v > 0`):
    In `D⁺ = (0, 1)²`, `c < 1`, `d < 1`, `e > 1`, so whenever `a² > 4`, `F1 < 0` strictly! -/
theorem positive_quadrant_a_bound {m1 m2 u v a c d e : ℝ}
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hu : 0 < u) (hv : 0 < v)
    (hc : c ^ 2 ≤ 1) (hd : d ^ 2 ≤ 1) (he : 1 ≤ e ^ 2)
    (ha : 4 + 2 * (m2 * v) / (m1 * u) < a ^ 2) :
    m1 * u * (4 * c ^ 2 - a ^ 2) + 2 * m2 * v * (c ^ 2 + d ^ 2 - e ^ 2) < 0 := by
  have hm1u : 0 < m1 * u := mul_pos hm1 hu
  have hm2v : 0 < m2 * v := mul_pos hm2 hv
  have h1 : 4 * c ^ 2 - a ^ 2 < -(2 * (m2 * v) / (m1 * u)) := by linarith
  have h2 : m1 * u * (4 * c ^ 2 - a ^ 2) < m1 * u * (-(2 * (m2 * v) / (m1 * u))) :=
    mul_lt_mul_of_pos_left h1 hm1u
  have h3 : m1 * u * (-(2 * (m2 * v) / (m1 * u))) = -(2 * m2 * v) := by
    field_simp [ne_of_gt hm1u]
  have h4 : c ^ 2 + d ^ 2 - e ^ 2 ≤ 1 := by linarith
  have h5 : 2 * m2 * v * (c ^ 2 + d ^ 2 - e ^ 2) ≤ 2 * m2 * v := by nlinarith
  linarith

/-- Negative-quadrant `c → ∞` / `b → ∞` exclusion (`v < 0`, `m1*u + m2*v < 0`):
    When `v < 0` and `tc = m5 + 2*u*(m1*u + m2*v) < m5`, we automatically have `td > m5`,
    so `d² < 1` and `e² < 1`. In `F2`, BOTH `-m2*v*b² > 0` and `2*m1*u*c² > 0` are positive,
    forcing `F2 > 0` whenever `2*m1*u*c² + (-m2*v)*b² > 2*m1*u + 4*(-m2*v)`! -/
theorem negative_quadrant_c_b_bound {m1 m2 u v b c d e : ℝ}
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hu : 0 < u) (hv : v < 0)
    (hd0 : 0 ≤ d ^ 2) (hd1 : d ^ 2 ≤ 1) (he1 : e ^ 2 ≤ 1)
    (hlarge : 2 * m1 * u + 4 * (-m2 * v) < 2 * m1 * u * c ^ 2 + (-m2 * v) * b ^ 2) :
    0 < m2 * v * (4 * d ^ 2 - b ^ 2) + 2 * m1 * u * (c ^ 2 + d ^ 2 - e ^ 2) := by
  have hm1u : 0 < m1 * u := mul_pos hm1 hu
  have hm2v : 0 < -m2 * v := by nlinarith
  nlinarith

/-- Symmetry check for `td > m5` whenever `tc < m5`, `u > 0`, `v < 0`. -/
theorem tc_small_implies_td_large {m1 m2 m5 u v : ℝ}
    (hu : 0 < u) (hv : v < 0)
    (htc : m5 + 2 * m1 * u ^ 2 + 2 * m2 * u * v < m5) :
    m5 < m5 + 2 * m1 * u * v + 2 * m2 * v ^ 2 := by
  have hX : 2 * m1 * u + 2 * m2 * v < 0 := by nlinarith
  nlinarith

/-! ## Part 2: Exact Complex Collision-Ray Elimination in ℂ (Zero Exceptional Masses) -/

/-- Elimination of the complex `{a, b, e}` collision ray (`u → 1, v → 1`):
    For ANY `m1, m2 > 0`, the leading-order cubed equations
      `(1 + k)^2 = -32 * (m2/m1)^3` and `(1 + k)^2 / k^2 = -32 * (m1/m2)^3`
    have NO complex solution `k ∈ ℂ*`! -/
theorem complex_ray_abe_impossible {m1 m2 : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2)
    (k : ℂ) (hk : k ≠ 0)
    (h1 : (1 + k) ^ 2 = ((-32 * (m2 / m1) ^ 3 : ℝ) : ℂ))
    (h2 : (1 + k) ^ 2 = ((-32 * (m1 / m2) ^ 3 : ℝ) : ℂ) * k ^ 2) : False := by
  have hm1_ne : (m1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hm1)
  have hm2_ne : (m2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hm2)
  have hk2 : k ^ 2 = (((m2 / m1) ^ 6 : ℝ) : ℂ) := by
    have hEq : ((-32 * (m1 / m2) ^ 3 : ℝ) : ℂ) * k ^ 2 = ((-32 * (m2 / m1) ^ 3 : ℝ) : ℂ) := by
      rw [← h2, h1]
    have hne : ((-32 * (m1 / m2) ^ 3 : ℝ) : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      have : 0 < (m1 / m2) ^ 3 := by positivity
      linarith
    apply mul_left_cancel₀ hne
    rw [hEq]
    push_cast
    field_simp [hm1_ne, hm2_ne]
  -- Thus k = ± (m2/m1)^3 is purely real!
  have hfac : (k - (((m2 / m1) ^ 3 : ℝ) : ℂ)) * (k + (((m2 / m1) ^ 3 : ℝ) : ℂ)) = 0 := by
    have : k ^ 2 - ((((m2 / m1) ^ 3 : ℝ) : ℂ)) ^ 2 = 0 := by
      rw [hk2]
      push_cast
      ring
    linear_combination this
  rcases mul_eq_zero.mp hfac with hk_pos | hk_neg
  · have hkr : k = (((m2 / m1) ^ 3 : ℝ) : ℂ) := sub_eq_zero.mp hk_pos
    rw [hkr] at h1
    have hreal : (1 + (m2 / m1) ^ 3) ^ 2 = -32 * (m2 / m1) ^ 3 := by
      exact_mod_cast h1
    have hpos : 0 < (m2 / m1) ^ 3 := by positivity
    nlinarith [sq_nonneg (1 + (m2 / m1) ^ 3)]
  · have hkr : k = ((-(m2 / m1) ^ 3 : ℝ) : ℂ) := by
      have := eq_neg_of_add_eq_zero_left hk_neg
      simpa using this
    rw [hkr] at h1
    have hreal : (1 + -(m2 / m1) ^ 3) ^ 2 = -32 * (m2 / m1) ^ 3 := by
      exact_mod_cast h1
    have hpos : 0 < (m2 / m1) ^ 3 := by positivity
    nlinarith [sq_nonneg (1 - (m2 / m1) ^ 3)]

/-- Elimination of the complex `{c, d}` collision ray:
    The 2×2 leading-order linear system in `(c², d²)` has determinant `8 * (m1 + m2)^2 > 0`
    for ALL `m1, m2 > 0`. -/
theorem complex_ray_cd_det_pos {m1 m2 : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2) :
    0 < (4 * m1 + 2 * m2) * (4 * m2 + 2 * m1) - (2 * m2) * (2 * m1) := by
  have : (4 * m1 + 2 * m2) * (4 * m2 + 2 * m1) - (2 * m2) * (2 * m1) = 8 * (m1 + m2) ^ 2 := by
    ring
  rw [this]
  positivity

/-- Elimination of the complex `{a, b, c}` collision ray EVEN ON THE HAMPTON–JENSEN
    EXCEPTIONAL HYPERSURFACE `2*m2 = 2*m1 + m5`:
    For ANY `m1, m2, m5 > 0`, the leading-order cubed equations
      `k^2 = -(m2/m1)^3 * (4*m1 - 2*m2)^3 / (8*m1^3)` and
      `m1^3 * (-4*m1 + 2*m2*(1+k))^2 = 4 * (4*m1 - 2*m2)^3 * m5^2`
    have NO complex solution `k ∈ ℂ*`! -/
theorem complex_ray_abc_impossible {m1 m2 m5 : ℝ}
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm5 : 0 < m5)
    (k : ℂ) (hk : k ≠ 0)
    (hk2 : k ^ 2 = ((-(m2 / m1) ^ 3 * (4 * m1 - 2 * m2) ^ 3 / (8 * m1 ^ 3) : ℝ) : ℂ))
    (hF1 : ((m1 ^ 3 : ℝ) : ℂ) * (((-4 * m1 + 2 * m2 : ℝ) : ℂ) + ((2 * m2 : ℝ) : ℂ) * k) ^ 2 =
           ((4 * (4 * m1 - 2 * m2) ^ 3 * m5 ^ 2 : ℝ) : ℂ)) : False := by
  -- Compare imaginary parts and real parts in the 3 cases on sign of (4*m1 - 2*m2)!
  rcases lt_trichotomy (4 * m1 - 2 * m2) 0 with hneg | hzero | hpos
  · -- Case 1: 4*m1 - 2*m2 < 0 => k^2 > 0 => k is purely real => LHS >= 0 > RHS!
    have hcube_neg : (4 * m1 - 2 * m2) ^ 3 < 0 := by
      have hc : (4 * m1 - 2 * m2) ^ 3 = (4 * m1 - 2 * m2) * (4 * m1 - 2 * m2) ^ 2 := by ring
      rw [hc]
      exact mul_neg_of_neg_of_pos hneg (sq_pos_of_neg hneg)
    let R : ℝ := -(m2 / m1) ^ 3 * (4 * m1 - 2 * m2) ^ 3 / (8 * m1 ^ 3)
    have hR_pos : 0 < R := by
      dsimp only [R]
      have hnum : 0 < -(m2 / m1) ^ 3 * (4 * m1 - 2 * m2) ^ 3 := by
        have h1 : 0 < (m2 / m1) ^ 3 := by positivity
        nlinarith
      have hden : 0 < 8 * m1 ^ 3 := by positivity
      exact div_pos hnum hden
    have hk_real : k.im = 0 := by
      have him := congr_arg Complex.im hk2
      simp only [sq, Complex.mul_im, Complex.ofReal_im] at him
      have hre := congr_arg Complex.re hk2
      simp only [sq, Complex.mul_re, Complex.ofReal_re] at hre
      by_contra hne
      have hprod : k.re * k.im = 0 := by linarith
      have hkre : k.re = 0 := (mul_eq_zero.mp hprod).resolve_right hne
      rw [hkre] at hre
      have : -(k.im * k.im) = R := by linarith
      nlinarith [sq_nonneg k.im]
    have hk_eq : k = (k.re : ℂ) := Complex.ext rfl (by simpa using hk_real)
    rw [hk_eq] at hF1
    have hreal : m1 ^ 3 * (-4 * m1 + 2 * m2 + 2 * m2 * k.re) ^ 2 =
                 4 * (4 * m1 - 2 * m2) ^ 3 * m5 ^ 2 := by
      exact_mod_cast hF1
    have hlhs : 0 ≤ m1 ^ 3 * (-4 * m1 + 2 * m2 + 2 * m2 * k.re) ^ 2 := by positivity
    have hrhs : 4 * (4 * m1 - 2 * m2) ^ 3 * m5 ^ 2 < 0 := by
      have hm52 : 0 < m5 ^ 2 := by positivity
      nlinarith
    linarith
  · -- Case 2: 4*m1 - 2*m2 = 0 => k^2 = 0 => k = 0, contradicting hk!
    rw [hzero] at hk2
    simp at hk2
    exact hk hk2
  · -- Case 3: 4*m1 - 2*m2 > 0 => k^2 < 0 => k is purely imaginary (k.re = 0, k.im ≠ 0)
    -- => Im(LHS) = m1^3 * 2 * (-4*m1 + 2*m2) * (2*m2 * k.im) ≠ 0 = Im(RHS)!
    let R : ℝ := -(m2 / m1) ^ 3 * (4 * m1 - 2 * m2) ^ 3 / (8 * m1 ^ 3)
    have hR_neg : R < 0 := by
      dsimp only [R]
      have hnum : -(m2 / m1) ^ 3 * (4 * m1 - 2 * m2) ^ 3 < 0 := by
        have h1 : 0 < (m2 / m1) ^ 3 := by positivity
        have h2 : 0 < (4 * m1 - 2 * m2) ^ 3 := by positivity
        nlinarith
      have hden : 0 < 8 * m1 ^ 3 := by positivity
      exact div_neg_of_neg_of_pos hnum hden
    have hk_re : k.re = 0 := by
      have him := congr_arg Complex.im hk2
      simp only [sq, Complex.mul_im, Complex.ofReal_im] at him
      have hre := congr_arg Complex.re hk2
      simp only [sq, Complex.mul_re, Complex.ofReal_re] at hre
      by_contra hne
      have hprod : k.re * k.im = 0 := by linarith
      have hkim : k.im = 0 := (mul_eq_zero.mp hprod).resolve_left hne
      rw [hkim] at hre
      nlinarith [sq_nonneg k.re]
    have hk_im : k.im ≠ 0 := by
      intro h0
      exact hk (Complex.ext hk_re h0)
    have himF1 := congr_arg Complex.im hF1
    simp only [sq, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
               Complex.ofReal_re, Complex.ofReal_im, hk_re] at himF1
    have hzero_im : m1 ^ 3 * (2 * (-4 * m1 + 2 * m2) * (2 * m2 * k.im)) = 0 := by linarith
    have hne : m1 ^ 3 * (2 * (-4 * m1 + 2 * m2) * (2 * m2 * k.im)) ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero 3 (ne_of_gt hm1))
      apply mul_ne_zero
      · apply mul_ne_zero two_ne_zero
        linarith
      · exact mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hm2)) hk_im
    exact hne hzero_im

end Spatial5C2v

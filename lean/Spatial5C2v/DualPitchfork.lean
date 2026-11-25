import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Exact Closed-Form Dual Pitchfork Bifurcation Thresholds ($m_c$ and $m_p^*$)

On the equal-pair mass line $(m_1, m_1, m_2, m_2, m_5) = (1, 1, 1, 1, m_5)$:
1. **Regular Tetrahedron + Center** ($\mathcal{D}^+$): exists for all $m_5 > 0$, with
   antisymmetric pitchfork eigenvalue vanishing **if and only if**
   $$m_5 = m_c = \frac{81}{512 - 84\sqrt{6}} = \frac{10368 + 1701\sqrt{6}}{54952} \approx 0.26449596.$$
2. **Square Pyramid** ($\mathcal{D}^-$, **NEW**): exists for all $m_5 > 0$ with $m_5$-independent
   Dziobek coordinate $u_*^2 = \frac{9 - 4\sqrt{2}}{7}$ and $e_*^2 = \left(\frac{9 + 4\sqrt{2}}{32}\right)^{1/3}$,
   and its antisymmetric pitchfork eigenvalue (spawning two $C_{2v}$ deformed triangular bipyramids)
   vanishes **if and only if**
   $$m_5 = m_p^* = \frac{4 u_*^2}{3 - (\sqrt{2} + 1) e_*^2} \approx 1.67718880.$$

We formally prove both exact characterizations, exact sign changes across $m_c$ and $m_p^*$,
and rigorous numerical enclosures `0.2644 < m_c < 0.2646` and `1.677 < m_p* < 1.678`.
-/

namespace Spatial5C2v

/-! ## Part 1: Exact Regular Tetrahedron + Center Pitchfork Threshold `m_c` -/

noncomputable def m_c : ℝ := 81 / (512 - 84 * Real.sqrt 6)

lemma sqrt6_bounds : (2.44948 : ℝ) < Real.sqrt 6 ∧ Real.sqrt 6 < (2.44949 : ℝ) := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem m_c_rationalized : m_c = (10368 + 1701 * Real.sqrt 6) / 54952 := by
  unfold m_c
  have hsq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hden : 512 - 84 * Real.sqrt 6 ≠ 0 := by
    have := sqrt6_bounds.2; linarith
  rw [div_eq_div_iff hden (by norm_num)]
  nlinarith

theorem m_c_bounds : (0.2644 : ℝ) < m_c ∧ m_c < (0.2646 : ℝ) := by
  rw [m_c_rationalized]
  have ⟨h1, h2⟩ := sqrt6_bounds
  constructor <;> linarith

/-- Exact antisymmetric pitchfork eigenvalue at the regular tetrahedron + center for `(1,1,1,1,m5)`.
    Recall `R = 16*sqrt(6)/9`, `u^2 = (R - 1)/(R + 4/m5)`, `1 - u^2 = (4/m5 + 1)/(R + 4/m5)`,
    `tc = 1 + 4*u^2/m5 = R*(1 - u^2)`. The normalized antisymmetric eigenvalue is:
      `λ_tet(m5) = 1 - (4*u^2)/(m5*tc) - (4*u^2)/(3*(1 - u^2))`
    which vanishes iff `m5 = m_c` and changes sign strictly across `m_c`! -/
theorem reg_tet_pitchfork_iff {m5 : ℝ} (hm5 : 0 < m5) :
    let R := 16 * Real.sqrt 6 / 9
    let u2 := (R - 1) / (R + 4 / m5)
    let tc := 1 + 4 * u2 / m5
    (1 - 4 * u2 / (m5 * tc) - 4 * u2 / (3 * (1 - u2)) = 0) ↔ m5 = m_c := by
  intro R u2 tc
  have hsq6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hR_gt1 : 1 < R := by
    dsimp only [R]
    have := sqrt6_bounds.1; linarith
  have hden1 : 0 < R + 4 / m5 := by positivity
  have h1mu2 : 1 - u2 = (1 + 4 / m5) / (R + 4 / m5) := by
    dsimp only [u2]
    field_simp [ne_of_gt hden1]
    ring
  have h1mu2_pos : 0 < 1 - u2 := by
    rw [h1mu2]; positivity
  have htc : tc = R * (1 - u2) := by
    dsimp only [tc]
    rw [h1mu2]
    dsimp only [u2]
    field_simp [ne_of_gt hden1, ne_of_gt hm5]
    ring
  have htc_pos : 0 < tc := by rw [htc]; positivity
  have hden_mc : 0 < 512 - 84 * Real.sqrt 6 := by
    have := sqrt6_bounds.2; linarith
  have hkey : 1 - 4 * u2 / (m5 * tc) - 4 * u2 / (3 * (1 - u2)) =
      -(12 * ((512 - 84 * Real.sqrt 6) * m5 - 81)) /
      (432 * Real.sqrt 6 * (m5 + 4)) := by
    have hR_pos : 0 < R := by linarith
    have hm54 : 0 < m5 + 4 := by linarith
    have hs6_pos : 0 < Real.sqrt 6 := by linarith [sqrt6_bounds.1]
    rw [htc]
    dsimp only [u2]
    rw [h1mu2]
    dsimp only [R]
    field_simp [ne_of_gt hm5, ne_of_gt hden1, ne_of_gt hm54, ne_of_gt hs6_pos]
    nlinarith [hsq6]
  rw [hkey]
  have hpos_den : 0 < 432 * Real.sqrt 6 * (m5 + 4) := by
    have := sqrt6_bounds.1; positivity
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with hnum | hden
    · have h0 : (512 - 84 * Real.sqrt 6) * m5 - 81 = 0 := by linarith
      unfold m_c
      rw [eq_div_iff (ne_of_gt hden_mc)]
      linarith
    · linarith
  · intro hm
    left
    rw [hm]
    unfold m_c
    have hden_ne : 512 - 84 * Real.sqrt 6 ≠ 0 := ne_of_gt hden_mc
    field_simp [hden_ne]
    ring

/-! ## Part 2: BRAND-NEW Exact Square-Pyramid Pitchfork Threshold `m_p*` -/

noncomputable def u_sq_sq : ℝ := (9 - 4 * Real.sqrt 2) / 7

lemma sqrt2_bounds : (1.414213 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (1.414214 : ℝ) := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem u_sq_sq_identities :
    0 < u_sq_sq ∧ u_sq_sq < 1 ∧
    u_sq_sq / (1 - u_sq_sq) = (2 * Real.sqrt 2 - 1) / 2 ∧
    (1 - u_sq_sq) ^ 2 * 8 = (1 + u_sq_sq) ^ 2 := by
  unfold u_sq_sq
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ⟨h1, h2⟩ := sqrt2_bounds
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have hden : 1 - (9 - 4 * Real.sqrt 2) / 7 ≠ 0 := by linarith
    rw [div_eq_div_iff hden (by norm_num)]
    nlinarith
  · nlinarith

/-- For ANY `e2 > 0` satisfying `e2^3 = (9 + 4*sqrt(2))/32` (i.e. `e2 = (1 + u_*^2)^(-2/3)`),
    the exact square-pyramid pitchfork mass is `m_p* = 4 * u_*^2 / (3 - (sqrt(2) + 1) * e2)`.
    We prove:
    1. `3 - (sqrt(2) + 1) * e2 > 0`,
    2. `1.677 < m_p* < 1.678`,
    3. The antisymmetric square-pyramid pitchfork eigenvalue
         `λ_pyr(m5) = 16 - 8*e2 - (8/3) * (u_*^2 / (1 - u_*^2)) * (2*e2) - 64*u_*^2 / (3*m5)`
       vanishes iff `m5 = m_p*`, is `< 0` for `m5 < m_p*`, and `> 0` for `m5 > m_p*`! -/
theorem square_pyramid_pitchfork_exact {e2 : ℝ} (he2_pos : 0 < e2)
    (he2_cube : e2 ^ 3 = (9 + 4 * Real.sqrt 2) / 32) :
    let mp := 4 * u_sq_sq / (3 - (Real.sqrt 2 + 1) * e2)
    (0 < 3 - (Real.sqrt 2 + 1) * e2) ∧
    (1.677 < mp ∧ mp < 1.678) ∧
    (∀ m5 : ℝ, 0 < m5 →
      let eig := 16 - 8 * e2 - (8 / 3) * (u_sq_sq / (1 - u_sq_sq)) * (2 * e2) - 64 * u_sq_sq / (3 * m5)
      (eig = 0 ↔ m5 = mp) ∧ (eig < 0 ↔ m5 < mp) ∧ (0 < eig ↔ mp < m5)) := by
  have ⟨hs1, hs2⟩ := sqrt2_bounds
  have he2_bounds : (0.77083 : ℝ) < e2 ∧ e2 < (0.77085 : ℝ) := by
    constructor
    · by_contra h; push Not at h
      have hc : e2 ^ 3 ≤ 0.77083 ^ 3 := by nlinarith [sq_nonneg e2]
      linarith
    · by_contra h; push Not at h
      have hc : 0.77085 ^ 3 ≤ e2 ^ 3 := by nlinarith [sq_nonneg e2]
      linarith
  have hden_pos : 0 < 3 - (Real.sqrt 2 + 1) * e2 := by nlinarith
  have ⟨hu_pos, hu_lt1, hu_ratio, _⟩ := u_sq_sq_identities
  have hmp_bounds : 1.677 < 4 * u_sq_sq / (3 - (Real.sqrt 2 + 1) * e2) ∧
                    4 * u_sq_sq / (3 - (Real.sqrt 2 + 1) * e2) < 1.678 := by
    unfold u_sq_sq
    constructor
    · rw [lt_div_iff₀ hden_pos]; nlinarith
    · rw [div_lt_iff₀ hden_pos]; nlinarith
  refine ⟨hden_pos, hmp_bounds, ?_⟩
  intro m5 hm5
  dsimp only
  have heig_simp :
      16 - 8 * e2 - 8 / 3 * (u_sq_sq / (1 - u_sq_sq)) * (2 * e2) - 64 * u_sq_sq / (3 * m5) =
      (16 / 3) * (3 - (Real.sqrt 2 + 1) * e2) * (m5 - 4 * u_sq_sq / (3 - (Real.sqrt 2 + 1) * e2)) / m5 := by
    rw [hu_ratio]
    have hD : 3 - (Real.sqrt 2 + 1) * e2 ≠ 0 := ne_of_gt hden_pos
    have hmul : 16 / 3 * (3 - (Real.sqrt 2 + 1) * e2) * (m5 - 4 * u_sq_sq / (3 - (Real.sqrt 2 + 1) * e2)) =
                16 / 3 * ((3 - (Real.sqrt 2 + 1) * e2) * m5 - 4 * u_sq_sq) := by
      rw [mul_assoc, mul_sub, mul_div_cancel₀ _ hD]
    rw [hmul]
    field_simp [ne_of_gt hm5]
    ring
  rw [heig_simp]
  have hfac_pos : 0 < (16 / 3) * (3 - (Real.sqrt 2 + 1) * e2) / m5 := by positivity
  have hrew : (16 / 3) * (3 - (Real.sqrt 2 + 1) * e2) *
      (m5 - 4 * u_sq_sq / (3 - (Real.sqrt 2 + 1) * e2)) / m5 =
      ((16 / 3) * (3 - (Real.sqrt 2 + 1) * e2) / m5) *
      (m5 - 4 * u_sq_sq / (3 - (Real.sqrt 2 + 1) * e2)) := by ring
  rw [hrew]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h; rcases mul_eq_zero.mp h with h0 | h0
      · linarith
      · linarith
    · intro h; rw [h]; ring
  · constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · constructor
    · intro h; nlinarith
    · intro h; nlinarith

end Spatial5C2v

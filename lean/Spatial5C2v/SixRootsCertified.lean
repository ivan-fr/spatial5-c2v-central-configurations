import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Spatial5C2v.DziobekReduction
import Spatial5C2v.DualPitchfork

/-!
# Machine-Checked Certification of Six Distinct Strictly 3D $C_{2v}$ 5-Body Central Configurations

For positive masses $(m_1, m_1, m_2, m_2, m_5) = (5, 5, 5, 5, 1)$, we prove unconditionally
(zero `sorry`, zero `native_decide`, standard Lean axioms `[propext, Classical.choice, Quot.sound]`)
the existence of **6 pairwise distinct, strictly 3D Newtonian 5-body central configurations**
(`Fin 6 → C2vCentralConfig 5 5 1`):
- 3 of convex-interior type $(4,1)$ in $\mathcal{D}^+$ (`z1 * z2 < 0`):
  1. Regular tetrahedron + center (exact closed-form construction),
  2. Off-diagonal pitchfork branch 1 (`u ≈ 0.272425, v ≈ +0.469807`, Banach contraction),
  3. Off-diagonal pitchfork branch 2 (`u ≈ 0.469807, v ≈ +0.272425`, exact symmetry);
- 3 of pyramidal/bipyramidal type $(3,2)$ in $\mathcal{D}^-$ (`z1 * z2 > 0`):
  4. Square pyramid (exact closed-form construction),
  5. Deformed triangular bipyramid 1 (`u ≈ 0.218345, v ≈ -0.460989`, Banach contraction),
  6. Deformed triangular bipyramid 2 (`u ≈ 0.460989, v ≈ -0.218345`, exact symmetry).
-/

set_option maxHeartbeats 2000000

namespace Spatial5C2v

/-! ## Section 1: Exact `φ(t) = t^(-2/3)` Properties & Interval Enclosure -/

/-- Auxiliary real power `φ(t) = t^(-2/3)` for `t > 0`. -/
noncomputable def phi (t : ℝ) : ℝ := t ^ (-(2 : ℝ) / 3)

lemma phi_pos {t : ℝ} (ht : 0 < t) : 0 < phi t :=
  Real.rpow_pos_of_pos ht _

lemma eq_of_cube_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 3 = y ^ 3) : x = y := by
  have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by linarith
  have hpos : 0 < x ^ 2 + x * y + y ^ 2 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (ne_of_gt hpos))

lemma phi_cube_mul_sq {t : ℝ} (ht : 0 < t) : phi t ^ 3 * t ^ 2 = 1 := by
  unfold phi
  have h1 : (t ^ (-(2 : ℝ) / 3)) ^ (3 : ℕ) = t ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ht)]
    norm_num
  have h2 : t ^ (2 : ℕ) = t ^ (2 : ℝ) := (Real.rpow_natCast t 2).symm
  rw [h1, h2, ← Real.rpow_add ht]
  norm_num

lemma phi_lower {t ylo t_hi : ℝ} (ht : 0 < t) (ht_le : t ≤ t_hi) (hylo : 0 < ylo)
    (hcert : ylo ^ 3 * t_hi ^ 2 ≤ 1) : ylo ≤ phi t := by
  by_contra hlt
  push Not at hlt
  have hpy : 0 < phi t := phi_pos ht
  have hthipos : 0 < t_hi := lt_of_lt_of_le ht ht_le
  have hcub : phi t ^ 3 < ylo ^ 3 := pow_lt_pow_left₀ hlt (le_of_lt hpy) (by norm_num)
  have hsq : t ^ 2 ≤ t_hi ^ 2 := by nlinarith
  have hprod : phi t ^ 3 * t ^ 2 < ylo ^ 3 * t_hi ^ 2 := by
    calc phi t ^ 3 * t ^ 2 ≤ phi t ^ 3 * t_hi ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ < ylo ^ 3 * t_hi ^ 2 := mul_lt_mul_of_pos_right hcub (by positivity)
  linarith [phi_cube_mul_sq ht]

lemma phi_upper {t yhi t_lo : ℝ} (ht : 0 < t) (ht_lo_pos : 0 < t_lo) (ht_ge : t_lo ≤ t)
    (hyhi : 0 < yhi) (hcert : 1 ≤ yhi ^ 3 * t_lo ^ 2) : phi t ≤ yhi := by
  by_contra hgt
  push Not at hgt
  have hpy : 0 < phi t := phi_pos ht
  have hcub : yhi ^ 3 < phi t ^ 3 := pow_lt_pow_left₀ hgt (le_of_lt hyhi) (by norm_num)
  have hsq : t_lo ^ 2 ≤ t ^ 2 := by nlinarith
  have hprod : yhi ^ 3 * t_lo ^ 2 < phi t ^ 3 * t ^ 2 := by
    calc yhi ^ 3 * t_lo ^ 2 ≤ yhi ^ 3 * t ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ < phi t ^ 3 * t ^ 2 := mul_lt_mul_of_pos_right hcub (by positivity)
  linarith [phi_cube_mul_sq ht]

lemma hasDerivAt_phi {t : ℝ} (ht : 0 < t) :
    HasDerivAt phi (-(2 : ℝ) / 3 * phi t / t) t := by
  unfold phi
  have hd := Real.hasDerivAt_rpow_const (p := -(2 : ℝ) / 3) (Or.inl (ne_of_gt ht))
  refine hd.congr_deriv ?_
  have h1 : t ^ (-(2 : ℝ) / 3 - 1) = t ^ (-(2 : ℝ) / 3) / t := by
    rw [Real.rpow_sub ht, Real.rpow_one]
  rw [h1]
  ring

/-! ## Section 2: Reduced Dziobek Map for `(5, 5, 5, 5, 1)` & Exact Symmetries -/

/-- Reduced Dziobek functions `F1_5, F2_5` (divided by `5`) for masses `(5, 5, 5, 5, 1)`. -/
noncomputable def F1_5 (u v : ℝ) : ℝ :=
  u * (4 * phi (1 + 10 * u * (u + v)) - phi (1 - u ^ 2)) +
  2 * v * (phi (1 + 10 * u * (u + v)) + phi (1 + 10 * v * (u + v)) - phi (1 - u * v))

noncomputable def F2_5 (u v : ℝ) : ℝ :=
  v * (4 * phi (1 + 10 * v * (u + v)) - phi (1 - v ^ 2)) +
  2 * u * (phi (1 + 10 * u * (u + v)) + phi (1 + 10 * v * (u + v)) - phi (1 - u * v))

/-- Analytical partial derivatives of `(F1_5, F2_5)`. -/
noncomputable def dphi (t : ℝ) : ℝ := -(2 : ℝ) / 3 * phi t / t

noncomputable def J11_5 (u v : ℝ) : ℝ :=
  let ta := 1 - u ^ 2; let te := 1 - u * v
  let tc := 1 + 10 * u * (u + v); let td := 1 + 10 * v * (u + v)
  let da_u := dphi ta * (-2 * u)
  let de_u := dphi te * (-v)
  let dc_u := dphi tc * (20 * u + 10 * v)
  let dd_u := dphi td * (10 * v)
  (4 * phi tc - phi ta) + u * (4 * dc_u - da_u) + 2 * v * (dc_u + dd_u - de_u)

noncomputable def J12_5 (u v : ℝ) : ℝ :=
  let te := 1 - u * v
  let tc := 1 + 10 * u * (u + v); let td := 1 + 10 * v * (u + v)
  let de_v := dphi te * (-u)
  let dc_v := dphi tc * (10 * u)
  let dd_v := dphi td * (10 * u + 20 * v)
  u * (4 * dc_v) + 2 * (phi tc + phi td - phi te) + 2 * v * (dc_v + dd_v - de_v)

noncomputable def J21_5 (u v : ℝ) : ℝ :=
  let te := 1 - u * v
  let tc := 1 + 10 * u * (u + v); let td := 1 + 10 * v * (u + v)
  let de_u := dphi te * (-v)
  let dc_u := dphi tc * (20 * u + 10 * v)
  let dd_u := dphi td * (10 * v)
  v * (4 * dd_u) + 2 * (phi tc + phi td - phi te) + 2 * u * (dc_u + dd_u - de_u)

noncomputable def J22_5 (u v : ℝ) : ℝ :=
  let tb := 1 - v ^ 2; let te := 1 - u * v
  let tc := 1 + 10 * u * (u + v); let td := 1 + 10 * v * (u + v)
  let db_v := dphi tb * (-2 * v)
  let de_v := dphi te * (-u)
  let dc_v := dphi tc * (10 * u)
  let dd_v := dphi td * (10 * u + 20 * v)
  (4 * phi td - phi tb) + v * (4 * dd_v - db_v) + 2 * u * (dc_v + dd_v - de_v)

/-- Convert any root `(u, v)` of `(F1_5, F2_5)` in the valid 3D domain into a `DziobekSol 5 5 1`. -/
noncomputable def root_to_dziobek5 {u v : ℝ}
    (hu : 0 < u) (hv : v ≠ 0)
    (hta : 0 < 1 - u ^ 2) (htb : 0 < 1 - v ^ 2) (hte : 0 < 1 - u * v)
    (htc : 0 < 1 + 10 * u * (u + v)) (htd : 0 < 1 + 10 * v * (u + v))
    (hF1 : F1_5 u v = 0) (hF2 : F2_5 u v = 0)
    (hz1 : phi (1 - u ^ 2) < 4 * phi (1 + 10 * u * (u + v)))
    (hz2 : phi (1 - v ^ 2) < 4 * phi (1 + 10 * v * (u + v))) :
    DziobekSol 5 5 1 := by
  let a := Real.sqrt (phi (1 - u ^ 2))
  let b := Real.sqrt (phi (1 - v ^ 2))
  let c := Real.sqrt (phi (1 + 10 * u * (u + v)))
  let d := Real.sqrt (phi (1 + 10 * v * (u + v)))
  let e := Real.sqrt (phi (1 - u * v))
  have ha2 : a ^ 2 = phi (1 - u ^ 2) := Real.sq_sqrt (le_of_lt (phi_pos hta))
  have hb2 : b ^ 2 = phi (1 - v ^ 2) := Real.sq_sqrt (le_of_lt (phi_pos htb))
  have hc2 : c ^ 2 = phi (1 + 10 * u * (u + v)) := Real.sq_sqrt (le_of_lt (phi_pos htc))
  have hd2 : d ^ 2 = phi (1 + 10 * v * (u + v)) := Real.sq_sqrt (le_of_lt (phi_pos htd))
  have he2 : e ^ 2 = phi (1 - u * v) := Real.sq_sqrt (le_of_lt (phi_pos hte))
  have ha : 0 < a := Real.sqrt_pos.mpr (phi_pos hta)
  have hb : 0 < b := Real.sqrt_pos.mpr (phi_pos htb)
  have hc : 0 < c := Real.sqrt_pos.mpr (phi_pos htc)
  have hd : 0 < d := Real.sqrt_pos.mpr (phi_pos htd)
  have he : 0 < e := Real.sqrt_pos.mpr (phi_pos hte)
  have cube_of_sq : ∀ {r t : ℝ}, 0 < r → 0 < t → r ^ 2 = phi t → r ^ 3 * t = 1 := by
    intro r t hr ht hr2
    have h6 : (r ^ 3 * t) ^ 2 = 1 := by
      calc (r ^ 3 * t) ^ 2 = (r ^ 2) ^ 3 * t ^ 2 := by ring
        _ = phi t ^ 3 * t ^ 2 := by rw [hr2]
        _ = 1 := phi_cube_mul_sq ht
    have hpos : 0 < r ^ 3 * t := by positivity
    nlinarith
  exact
    { u := u, v := v, a := a, b := b, c := c, d := d, e := e
      hu := hu, hv := hv, ha := ha, hb := hb, hc := hc, hd := hd, he := he
      h_a3 := cube_of_sq ha hta ha2
      h_b3 := cube_of_sq hb htb hb2
      h_e3 := cube_of_sq he hte he2
      h_c3 := by have h := cube_of_sq hc htc hc2; linarith
      h_d3 := by have h := cube_of_sq hd htd hd2; linarith
      h_F1 := by rw [ha2, hc2, hd2, he2]; unfold F1_5 at hF1; linarith
      h_F2 := by rw [hb2, hc2, hd2, he2]; unfold F2_5 at hF2; linarith
      h_z1_pos := by rw [ha2, hc2]; exact hz1
      h_z2_pos := by rw [hb2, hd2]; exact hz2 }

/-- Exact symmetry `D+`: swapping `(u, v) ↔ (v, u)` preserves `DziobekSol 5 5 1` when `v > 0`. -/
def dziobek5_swap_pos (s : DziobekSol 5 5 1) (hv : 0 < s.v) : DziobekSol 5 5 1 where
  u := s.v
  v := s.u
  a := s.b
  b := s.a
  c := s.d
  d := s.c
  e := s.e
  hu := hv
  hv := ne_of_gt s.hu
  ha := s.hb
  hb := s.ha
  hc := s.hd
  hd := s.hc
  he := s.he
  h_a3 := s.h_b3
  h_b3 := s.h_a3
  h_e3 := by linarith [s.h_e3]
  h_c3 := by linarith [s.h_d3]
  h_d3 := by linarith [s.h_c3]
  h_F1 := by linarith [s.h_F2]
  h_F2 := by linarith [s.h_F1]
  h_z1_pos := s.h_z2_pos
  h_z2_pos := s.h_z1_pos

/-- Exact symmetry `D-`: `(u, v) ↔ (-v, -u)` preserves `DziobekSol 5 5 1` when `v < 0`. -/
def dziobek5_swap_neg (s : DziobekSol 5 5 1) (hv : s.v < 0) : DziobekSol 5 5 1 where
  u := -s.v
  v := -s.u
  a := s.b
  b := s.a
  c := s.d
  d := s.c
  e := s.e
  hu := by linarith
  hv := by linarith [s.hu]
  ha := s.hb
  hb := s.ha
  hc := s.hd
  hd := s.hc
  he := s.he
  h_a3 := by linarith [s.h_b3]
  h_b3 := by linarith [s.h_a3]
  h_e3 := by linarith [s.h_e3]
  h_c3 := by linarith [s.h_d3]
  h_d3 := by linarith [s.h_c3]
  h_F1 := by linarith [s.h_F2]
  h_F2 := by linarith [s.h_F1]
  h_z1_pos := s.h_z2_pos
  h_z2_pos := s.h_z1_pos

/-! ## Section 3: Exact Closed-Form Construction of the 2 Symmetric Roots -/

/-- Exact Root 1 (`D+` symmetric): Regular tetrahedron + center for `(5, 5, 5, 5, 1)`. -/
noncomputable def root1_reg_tet : DziobekSol 5 5 1 := by
  let R := 16 * Real.sqrt 6 / 9
  have hsq6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hR_gt1 : 1 < R := by dsimp only [R]; have := sqrt6_bounds.1; linarith
  have hden : 0 < R + 20 := by linarith
  let u2 := (R - 1) / (R + 20)
  have hu2_pos : 0 < u2 := div_pos (by linarith) hden
  have hu2_lt1 : u2 < 1 := by
    dsimp only [u2]; rw [div_lt_one hden]; linarith
  let u := Real.sqrt u2
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hu2_pos
  have hu_sq : u ^ 2 = u2 := Real.sq_sqrt (le_of_lt hu2_pos)
  have hta : 0 < 1 - u ^ 2 := by linarith
  have htc_eq : 1 + 10 * u * (u + u) = R * (1 - u ^ 2) := by
    have : 1 + 10 * u * (u + u) = 1 + 20 * u ^ 2 := by ring
    rw [this, hu_sq]
    dsimp only [u2]
    field_simp [ne_of_gt hden]
    ring
  have htc : 0 < 1 + 10 * u * (u + u) := by rw [htc_eq]; positivity
  have hphi_ratio : phi (1 + 10 * u * (u + u)) = (3 / 8 : ℝ) * phi (1 - u ^ 2) := by
    have hR2 : R ^ 2 = (8 / 3 : ℝ) ^ 3 := by
      dsimp only [R]
      have : (16 * Real.sqrt 6 / 9) ^ 2 = 256 * Real.sqrt 6 ^ 2 / 81 := by ring
      rw [this, hsq6]; norm_num
    have hcub : (phi (1 + 10 * u * (u + u))) ^ 3 = ((3 / 8 : ℝ) * phi (1 - u ^ 2)) ^ 3 := by
      have h1 := phi_cube_mul_sq htc
      have h2 := phi_cube_mul_sq hta
      have hta2 : (1 - u ^ 2) ^ 2 ≠ 0 := by positivity
      have htc2 : (1 + 10 * u * (u + u)) ^ 2 = (8 / 3 : ℝ) ^ 3 * (1 - u ^ 2) ^ 2 := by
        rw [htc_eq, mul_pow, hR2]
      rw [htc2] at h1
      apply mul_right_cancel₀ hta2
      linarith
    exact eq_of_cube_eq (phi_pos htc) (by positivity [phi_pos hta]) hcub
  apply root_to_dziobek5 hu_pos (ne_of_gt hu_pos) hta hta (by simpa [sq] using hta) htc htc
  · unfold F1_5
    have heq : 1 - u * u = 1 - u ^ 2 := by ring
    rw [heq, hphi_ratio]; ring
  · unfold F2_5
    have heq : 1 - u * u = 1 - u ^ 2 := by ring
    rw [heq, hphi_ratio]; ring
  · rw [hphi_ratio]; linarith [phi_pos hta]
  · rw [hphi_ratio]; linarith [phi_pos hta]

/-- Exact Root 2 (`D-` symmetric): Square pyramid for `(5, 5, 5, 5, 1)`. -/
noncomputable def root2_sq_pyr : DziobekSol 5 5 1 := by
  have ⟨hu2_pos, hu2_lt1, _, hu2_ratio⟩ := u_sq_sq_identities
  let u := Real.sqrt u_sq_sq
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hu2_pos
  have hu_sq : u ^ 2 = u_sq_sq := Real.sq_sqrt (le_of_lt hu2_pos)
  have hta : 0 < 1 - u ^ 2 := by linarith
  have hte : 0 < 1 - u * (-u) := by nlinarith
  have htc : 0 < 1 + 10 * u * (u + -u) := by norm_num
  have htd : 0 < 1 + 10 * (-u) * (u + -u) := by norm_num
  have hphi1 : phi 1 = 1 := by unfold phi; exact Real.one_rpow _
  have hphi_ae : phi (1 - u ^ 2) = 2 * phi (1 - u * (-u)) := by
    have hcub : phi (1 - u ^ 2) ^ 3 = (2 * phi (1 - u * (-u))) ^ 3 := by
      have h1 := phi_cube_mul_sq hta
      have h2 := phi_cube_mul_sq hte
      have hsq_eq : (1 - u ^ 2) ^ 2 * 8 = (1 - u * (-u)) ^ 2 := by
        have h_eq1 : 1 - u * (-u) = 1 + u ^ 2 := by ring
        rw [h_eq1, hu_sq]; exact hu2_ratio
      have hne : (1 - u ^ 2) ^ 2 ≠ 0 := by positivity
      apply mul_right_cancel₀ hne
      calc phi (1 - u ^ 2) ^ 3 * (1 - u ^ 2) ^ 2 = 1 := h1
        _ = phi (1 - u * (-u)) ^ 3 * (1 - u * (-u)) ^ 2 := h2.symm
        _ = phi (1 - u * (-u)) ^ 3 * ((1 - u ^ 2) ^ 2 * 8) := by rw [hsq_eq]
        _ = (2 * phi (1 - u * (-u))) ^ 3 * (1 - u ^ 2) ^ 2 := by ring
    exact eq_of_cube_eq (phi_pos hta) (by positivity [phi_pos hte]) hcub
  have hphi_a_lt4 : phi (1 - u ^ 2) < 4 := by
    have hta_gt : (1 / 2 : ℝ) < 1 - u ^ 2 := by
      rw [hu_sq]; unfold u_sq_sq; have := sqrt2_bounds.1; linarith
    have hle : phi (1 - u ^ 2) ≤ (2 : ℝ) :=
      phi_upper hta (by norm_num) (le_of_lt hta_gt) (by norm_num) (by norm_num)
    linarith
  apply root_to_dziobek5 hu_pos (by linarith) hta (by simpa [sq] using hta) hte htc htd
  · unfold F1_5
    have h0 : 1 + 10 * u * (u + -u) = 1 := by ring
    have h0' : 1 + 10 * (-u) * (u + -u) = 1 := by ring
    rw [h0, h0', hphi1, hphi_ae]; ring
  · unfold F2_5
    have h0 : 1 + 10 * u * (u + -u) = 1 := by ring
    have h0' : 1 + 10 * (-u) * (u + -u) = 1 := by ring
    have hsq2 : 1 - (-u) ^ 2 = 1 - u ^ 2 := by ring
    rw [h0, h0', hsq2, hphi1, hphi_ae]; ring
  · have h0 : 1 + 10 * u * (u + -u) = 1 := by ring
    rw [h0, hphi1]; linarith
  · have h0' : 1 + 10 * (-u) * (u + -u) = 1 := by ring
    have hsq2 : 1 - (-u) ^ 2 = 1 - u ^ 2 := by ring
    rw [h0', hsq2, hphi1]; linarith

/-! ## Section 4: Generic 2D Banach Contraction Certifier (via 1D MVT + `ContractingWith`) -/

/-- Closed box `B(u0, v0, r) = [u0 - r, u0 + r] × [v0 - r, v0 + r] ⊆ ℝ × ℝ`. -/
def Box (u0 v0 r : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (u0 - r) (u0 + r) ×ˢ Set.Icc (v0 - r) (v0 + r)

lemma box_isClosed (u0 v0 r : ℝ) : IsClosed (Box u0 v0 r) :=
  isClosed_Icc.prod isClosed_Icc

/-- Helper: 1D affine segment derivative `t ↦ (1 - t) * x1 + t * x2`. -/
lemma hasDerivAt_seg (x1 x2 s : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - t) * x1 + t * x2) (x2 - x1) s := by
  have h1 := ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const x1
  have h2 := (hasDerivAt_id s).mul_const x2
  refine (h1.add h2).congr_deriv ?_
  ring

lemma hasDerivAt_phi_comp {f : ℝ → ℝ} {f' s : ℝ} (hf : HasDerivAt f f' s) (hpos : 0 < f s) :
    HasDerivAt (fun t => phi (f t)) (dphi (f s) * f') s := by
  simpa only [Function.comp_def, dphi] using (hasDerivAt_phi hpos).comp s hf

/-- 1D directional derivative of `F1_5` along any straight line segment inside the positive domain. -/
lemma hasDerivAt_F1_seg (u1 v1 u2 v2 s : ℝ)
    (hta : 0 < 1 - ((1 - s) * u1 + s * u2) ^ 2)
    (hte : 0 < 1 - ((1 - s) * u1 + s * u2) * ((1 - s) * v1 + s * v2))
    (htc : 0 < 1 + 10 * ((1 - s) * u1 + s * u2) * (((1 - s) * u1 + s * u2) + ((1 - s) * v1 + s * v2)))
    (htd : 0 < 1 + 10 * ((1 - s) * v1 + s * v2) * (((1 - s) * u1 + s * u2) + ((1 - s) * v1 + s * v2))) :
    HasDerivAt (fun t => F1_5 ((1 - t) * u1 + t * u2) ((1 - t) * v1 + t * v2))
      (J11_5 ((1 - s) * u1 + s * u2) ((1 - s) * v1 + s * v2) * (u2 - u1) +
       J12_5 ((1 - s) * u1 + s * u2) ((1 - s) * v1 + s * v2) * (v2 - v1)) s := by
  have hdu := hasDerivAt_seg u1 u2 s
  have hdv := hasDerivAt_seg v1 v2 s
  have hd_ta : HasDerivAt (fun t => 1 - ((1 - t) * u1 + t * u2) ^ 2)
      (-2 * ((1 - s) * u1 + s * u2) * (u2 - u1)) s := by
    refine ((hasDerivAt_const s (1 : ℝ)).sub (hdu.pow 2)).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring
  have hd_te : HasDerivAt (fun t => 1 - ((1 - t) * u1 + t * u2) * ((1 - t) * v1 + t * v2))
      (-(((1 - s) * v1 + s * v2) * (u2 - u1) + ((1 - s) * u1 + s * u2) * (v2 - v1))) s := by
    refine ((hasDerivAt_const s (1 : ℝ)).sub (hdu.mul hdv)).congr_deriv ?_
    ring
  have hd_tc : HasDerivAt (fun t => 1 + 10 * ((1 - t) * u1 + t * u2) * (((1 - t) * u1 + t * u2) + ((1 - t) * v1 + t * v2)))
      ((20 * ((1 - s) * u1 + s * u2) + 10 * ((1 - s) * v1 + s * v2)) * (u2 - u1) +
       (10 * ((1 - s) * u1 + s * u2)) * (v2 - v1)) s := by
    refine ((hasDerivAt_const s (1 : ℝ)).add ((hdu.const_mul 10).mul (hdu.add hdv))).congr_deriv ?_
    simp only [Pi.add_apply]; ring
  have hd_td : HasDerivAt (fun t => 1 + 10 * ((1 - t) * v1 + t * v2) * (((1 - t) * u1 + t * u2) + ((1 - t) * v1 + t * v2)))
      ((10 * ((1 - s) * v1 + s * v2)) * (u2 - u1) +
       (10 * ((1 - s) * u1 + s * u2) + 20 * ((1 - s) * v1 + s * v2)) * (v2 - v1)) s := by
    refine ((hasDerivAt_const s (1 : ℝ)).add ((hdv.const_mul 10).mul (hdu.add hdv))).congr_deriv ?_
    simp only [Pi.add_apply]; ring
  have hd_pa := hasDerivAt_phi_comp hd_ta hta
  have hd_pe := hasDerivAt_phi_comp hd_te hte
  have hd_pc := hasDerivAt_phi_comp hd_tc htc
  have hd_pd := hasDerivAt_phi_comp hd_td htd
  have h_term1 := hdu.mul ((hd_pc.const_mul 4).sub hd_pa)
  have h_term2 := (hdv.const_mul 2).mul ((hd_pc.add hd_pd).sub hd_pe)
  refine (h_term1.add h_term2).congr_deriv ?_
  unfold J11_5 J12_5
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  set us := (1 - s) * u1 + s * u2
  set vs := (1 - s) * v1 + s * v2
  ring

/-- 1D directional derivative of `F2_5` along any straight line segment inside the positive domain. -/
lemma hasDerivAt_F2_seg (u1 v1 u2 v2 s : ℝ)
    (htb : 0 < 1 - ((1 - s) * v1 + s * v2) ^ 2)
    (hte : 0 < 1 - ((1 - s) * u1 + s * u2) * ((1 - s) * v1 + s * v2))
    (htc : 0 < 1 + 10 * ((1 - s) * u1 + s * u2) * (((1 - s) * u1 + s * u2) + ((1 - s) * v1 + s * v2)))
    (htd : 0 < 1 + 10 * ((1 - s) * v1 + s * v2) * (((1 - s) * u1 + s * u2) + ((1 - s) * v1 + s * v2))) :
    HasDerivAt (fun t => F2_5 ((1 - t) * u1 + t * u2) ((1 - t) * v1 + t * v2))
      (J21_5 ((1 - s) * u1 + s * u2) ((1 - s) * v1 + s * v2) * (u2 - u1) +
       J22_5 ((1 - s) * u1 + s * u2) ((1 - s) * v1 + s * v2) * (v2 - v1)) s := by
  have hdu := hasDerivAt_seg u1 u2 s
  have hdv := hasDerivAt_seg v1 v2 s
  have hd_tb : HasDerivAt (fun t => 1 - ((1 - t) * v1 + t * v2) ^ 2)
      (-2 * ((1 - s) * v1 + s * v2) * (v2 - v1)) s := by
    refine ((hasDerivAt_const s (1 : ℝ)).sub (hdv.pow 2)).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring
  have hd_te : HasDerivAt (fun t => 1 - ((1 - t) * u1 + t * u2) * ((1 - t) * v1 + t * v2))
      (-(((1 - s) * v1 + s * v2) * (u2 - u1) + ((1 - s) * u1 + s * u2) * (v2 - v1))) s := by
    refine ((hasDerivAt_const s (1 : ℝ)).sub (hdu.mul hdv)).congr_deriv ?_
    ring
  have hd_tc : HasDerivAt (fun t => 1 + 10 * ((1 - t) * u1 + t * u2) * (((1 - t) * u1 + t * u2) + ((1 - t) * v1 + t * v2)))
      ((20 * ((1 - s) * u1 + s * u2) + 10 * ((1 - s) * v1 + s * v2)) * (u2 - u1) +
       (10 * ((1 - s) * u1 + s * u2)) * (v2 - v1)) s := by
    refine ((hasDerivAt_const s (1 : ℝ)).add ((hdu.const_mul 10).mul (hdu.add hdv))).congr_deriv ?_
    simp only [Pi.add_apply]; ring
  have hd_td : HasDerivAt (fun t => 1 + 10 * ((1 - t) * v1 + t * v2) * (((1 - t) * u1 + t * u2) + ((1 - t) * v1 + t * v2)))
      ((10 * ((1 - s) * v1 + s * v2)) * (u2 - u1) +
       (10 * ((1 - s) * u1 + s * u2) + 20 * ((1 - s) * v1 + s * v2)) * (v2 - v1)) s := by
    refine ((hasDerivAt_const s (1 : ℝ)).add ((hdv.const_mul 10).mul (hdu.add hdv))).congr_deriv ?_
    simp only [Pi.add_apply]; ring
  have hd_pb := hasDerivAt_phi_comp hd_tb htb
  have hd_pe := hasDerivAt_phi_comp hd_te hte
  have hd_pc := hasDerivAt_phi_comp hd_tc htc
  have hd_pd := hasDerivAt_phi_comp hd_td htd
  have h_term1 := hdv.mul ((hd_pd.const_mul 4).sub hd_pb)
  have h_term2 := (hdu.const_mul 2).mul ((hd_pc.add hd_pd).sub hd_pe)
  refine (h_term1.add h_term2).congr_deriv ?_
  unfold J21_5 J22_5
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  set us := (1 - s) * u1 + s * u2
  set vs := (1 - s) * v1 + s * v2
  ring

/-- Master 2D Newton-Banach Existence Theorem on a closed box `B(u0, v0, r)`. -/
theorem banach_box_root {u0 v0 r a11 a12 a21 a22 : ℝ} (hr : 0 < r)
    (hdet : a11 * a22 - a12 * a21 ≠ 0)
    (hdom : ∀ p ∈ Box u0 v0 r,
      0 < 1 - p.1 ^ 2 ∧ 0 < 1 - p.2 ^ 2 ∧ 0 < 1 - p.1 * p.2 ∧
      0 < 1 + 10 * p.1 * (p.1 + p.2) ∧ 0 < 1 + 10 * p.2 * (p.1 + p.2))
    (hcontr : ∀ p ∈ Box u0 v0 r,
      |1 - (a11 * J11_5 p.1 p.2 + a12 * J21_5 p.1 p.2)| +
      |-(a11 * J12_5 p.1 p.2 + a12 * J22_5 p.1 p.2)| ≤ 1 / 2 ∧
      |-(a21 * J11_5 p.1 p.2 + a22 * J21_5 p.1 p.2)| +
      |1 - (a21 * J12_5 p.1 p.2 + a22 * J22_5 p.1 p.2)| ≤ 1 / 2)
    (hcenter :
      |a11 * F1_5 u0 v0 + a12 * F2_5 u0 v0| ≤ r / 2 ∧
      |a21 * F1_5 u0 v0 + a22 * F2_5 u0 v0| ≤ r / 2) :
    ∃ p ∈ Box u0 v0 r, F1_5 p.1 p.2 = 0 ∧ F2_5 p.1 p.2 = 0 := by
  let T : ℝ × ℝ → ℝ × ℝ := fun p =>
    (p.1 - (a11 * F1_5 p.1 p.2 + a12 * F2_5 p.1 p.2),
     p.2 - (a21 * F1_5 p.1 p.2 + a22 * F2_5 p.1 p.2))
  have hseg : ∀ p q : ℝ × ℝ, p ∈ Box u0 v0 r → q ∈ Box u0 v0 r →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ((1 - s) * p.1 + s * q.1, (1 - s) * p.2 + s * q.2) ∈ Box u0 v0 r := by
    intro p q hp hq s hs
    rcases hp with ⟨⟨hp1l, hp1u⟩, ⟨hp2l, hp2u⟩⟩
    rcases hq with ⟨⟨hq1l, hq1u⟩, ⟨hq2l, hq2u⟩⟩
    rcases hs with ⟨hs0, hs1⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  have hlip : ∀ p ∈ Box u0 v0 r, ∀ q ∈ Box u0 v0 r, dist (T p) (T q) ≤ (1 / 2 : ℝ) * dist p q := by
    intro p hp q hq
    rw [Prod.dist_eq, max_le_iff]
    have hdist_u : |q.1 - p.1| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq, abs_sub_comm]; exact le_max_left _ _
    have hdist_v : |q.2 - p.2| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq, abs_sub_comm]; exact le_max_right _ _
    have h_c1 : dist (T p).1 (T q).1 ≤ (1 / 2 : ℝ) * dist p q := by
      let g : ℝ → ℝ := fun s => (T ((1 - s) * p.1 + s * q.1, (1 - s) * p.2 + s * q.2)).1
      let g' : ℝ → ℝ := fun s =>
        let us := (1 - s) * p.1 + s * q.1
        let vs := (1 - s) * p.2 + s * q.2
        (1 - (a11 * J11_5 us vs + a12 * J21_5 us vs)) * (q.1 - p.1) +
        (-(a11 * J12_5 us vs + a12 * J22_5 us vs)) * (q.2 - p.2)
      have hdg : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' s) s := by
        intro s hs
        have ⟨hta, htb, hte, htc, htd⟩ := hdom _ (hseg p q hp hq s hs)
        have hd1 := hasDerivAt_F1_seg p.1 p.2 q.1 q.2 s hta hte htc htd
        have hd2 := hasDerivAt_F2_seg p.1 p.2 q.1 q.2 s htb hte htc htd
        have hdu := hasDerivAt_seg p.1 q.1 s
        have hcomb := hdu.sub (((hasDerivAt_const s a11).mul hd1).add ((hasDerivAt_const s a12).mul hd2))
        refine hcomb.congr_deriv ?_
        dsimp only [g']
        ring
      have hcont : ContinuousOn g (Set.Icc 0 1) :=
        fun s hs => (hdg s hs).continuousAt.continuousWithinAt
      have hdiff : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g' s) s :=
        fun s hs => hdg s (Set.Ioo_subset_Icc_self hs)
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope g g' (by norm_num : (0 : ℝ) < 1) hcont hdiff
      have hg0 : g 0 = (T p).1 := by simp [g, T]
      have hg1 : g 1 = (T q).1 := by simp [g, T]
      rw [hg0, hg1, sub_zero, div_one] at hc_eq
      rw [Real.dist_eq, abs_sub_comm, ← hc_eq]
      have hcontr_c := (hcontr _ (hseg p q hp hq c (Set.Ioo_subset_Icc_self hc_mem))).1
      dsimp only [g']
      set M1 := 1 - (a11 * J11_5 ((1 - c) * p.1 + c * q.1) ((1 - c) * p.2 + c * q.2) +
                     a12 * J21_5 ((1 - c) * p.1 + c * q.1) ((1 - c) * p.2 + c * q.2))
      set M2 := -(a11 * J12_5 ((1 - c) * p.1 + c * q.1) ((1 - c) * p.2 + c * q.2) +
                  a12 * J22_5 ((1 - c) * p.1 + c * q.1) ((1 - c) * p.2 + c * q.2))
      calc |M1 * (q.1 - p.1) + M2 * (q.2 - p.2)|
          ≤ |M1 * (q.1 - p.1)| + |M2 * (q.2 - p.2)| := abs_add_le _ _
        _ = |M1| * |q.1 - p.1| + |M2| * |q.2 - p.2| := by rw [abs_mul, abs_mul]
        _ ≤ (|M1| + |M2|) * dist p q := by nlinarith [abs_nonneg M1, abs_nonneg M2]
        _ ≤ (1 / 2 : ℝ) * dist p q := mul_le_mul_of_nonneg_right hcontr_c dist_nonneg
    have h_c2 : dist (T p).2 (T q).2 ≤ (1 / 2 : ℝ) * dist p q := by
      let g : ℝ → ℝ := fun s => (T ((1 - s) * p.1 + s * q.1, (1 - s) * p.2 + s * q.2)).2
      let g' : ℝ → ℝ := fun s =>
        let us := (1 - s) * p.1 + s * q.1
        let vs := (1 - s) * p.2 + s * q.2
        (-(a21 * J11_5 us vs + a22 * J21_5 us vs)) * (q.1 - p.1) +
        (1 - (a21 * J12_5 us vs + a22 * J22_5 us vs)) * (q.2 - p.2)
      have hdg : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' s) s := by
        intro s hs
        have ⟨hta, htb, hte, htc, htd⟩ := hdom _ (hseg p q hp hq s hs)
        have hd1 := hasDerivAt_F1_seg p.1 p.2 q.1 q.2 s hta hte htc htd
        have hd2 := hasDerivAt_F2_seg p.1 p.2 q.1 q.2 s htb hte htc htd
        have hdv := hasDerivAt_seg p.2 q.2 s
        have hcomb := hdv.sub (((hasDerivAt_const s a21).mul hd1).add ((hasDerivAt_const s a22).mul hd2))
        refine hcomb.congr_deriv ?_
        dsimp only [g']
        ring
      have hcont : ContinuousOn g (Set.Icc 0 1) :=
        fun s hs => (hdg s hs).continuousAt.continuousWithinAt
      have hdiff : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g' s) s :=
        fun s hs => hdg s (Set.Ioo_subset_Icc_self hs)
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope g g' (by norm_num : (0 : ℝ) < 1) hcont hdiff
      have hg0 : g 0 = (T p).2 := by simp [g, T]
      have hg1 : g 1 = (T q).2 := by simp [g, T]
      rw [hg0, hg1, sub_zero, div_one] at hc_eq
      rw [Real.dist_eq, abs_sub_comm, ← hc_eq]
      have hcontr_c := (hcontr _ (hseg p q hp hq c (Set.Ioo_subset_Icc_self hc_mem))).2
      dsimp only [g']
      set M1 := -(a21 * J11_5 ((1 - c) * p.1 + c * q.1) ((1 - c) * p.2 + c * q.2) +
                  a22 * J21_5 ((1 - c) * p.1 + c * q.1) ((1 - c) * p.2 + c * q.2))
      set M2 := 1 - (a21 * J12_5 ((1 - c) * p.1 + c * q.1) ((1 - c) * p.2 + c * q.2) +
                     a22 * J22_5 ((1 - c) * p.1 + c * q.1) ((1 - c) * p.2 + c * q.2))
      calc |M1 * (q.1 - p.1) + M2 * (q.2 - p.2)|
          ≤ |M1 * (q.1 - p.1)| + |M2 * (q.2 - p.2)| := abs_add_le _ _
        _ = |M1| * |q.1 - p.1| + |M2| * |q.2 - p.2| := by rw [abs_mul, abs_mul]
        _ ≤ (|M1| + |M2|) * dist p q := by nlinarith [abs_nonneg M1, abs_nonneg M2]
        _ ≤ (1 / 2 : ℝ) * dist p q := mul_le_mul_of_nonneg_right hcontr_c dist_nonneg
    exact ⟨h_c1, h_c2⟩
  have hp0_mem : (u0, v0) ∈ Box u0 v0 r := ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hmaps : ∀ p ∈ Box u0 v0 r, T p ∈ Box u0 v0 r := by
    intro p hp
    have hdp : dist p (u0, v0) ≤ r := by
      rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
      rcases hp with ⟨⟨h1l, h1u⟩, ⟨h2l, h2u⟩⟩
      exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hdt0 : dist (T (u0, v0)) (u0, v0) ≤ r / 2 := by
      rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
      dsimp only [T]
      constructor
      · have : u0 - (a11 * F1_5 u0 v0 + a12 * F2_5 u0 v0) - u0 =
               -(a11 * F1_5 u0 v0 + a12 * F2_5 u0 v0) := by ring
        rw [this, abs_neg]; exact hcenter.1
      · have : v0 - (a21 * F1_5 u0 v0 + a22 * F2_5 u0 v0) - v0 =
               -(a21 * F1_5 u0 v0 + a22 * F2_5 u0 v0) := by ring
        rw [this, abs_neg]; exact hcenter.2
    have htri : dist (T p) (u0, v0) ≤ r := by
      calc dist (T p) (u0, v0) ≤ dist (T p) (T (u0, v0)) + dist (T (u0, v0)) (u0, v0) := dist_triangle _ _ _
        _ ≤ (1 / 2 : ℝ) * dist p (u0, v0) + r / 2 := add_le_add (hlip p hp (u0, v0) hp0_mem) hdt0
        _ ≤ (1 / 2 : ℝ) * r + r / 2 := by linarith
        _ = r := by ring
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at htri
    rcases htri with ⟨h1, h2⟩
    rw [abs_le] at h1 h2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  let TB : Box u0 v0 r → Box u0 v0 r := fun x => ⟨T x.1, hmaps x.1 x.2⟩
  have : CompleteSpace (Box u0 v0 r) := (box_isClosed u0 v0 r).completeSpace_coe
  have hTB_contr : ContractingWith (1 / 2 : NNReal) TB := by
    refine ⟨by norm_num, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [TB, Subtype.dist_eq] using hlip x.1 x.2 y.1 y.2
  obtain ⟨x, hx_fix, _⟩ := hTB_contr.exists_fixedPoint ⟨(u0, v0), hp0_mem⟩ (by simp [edist_dist])
  have hTx : T x.1 = x.1 := congr_arg Subtype.val hx_fix
  have hAF1 : a11 * F1_5 x.1.1 x.1.2 + a12 * F2_5 x.1.1 x.1.2 = 0 := by
    have := congr_arg Prod.fst hTx; dsimp only [T] at this; linarith
  have hAF2 : a21 * F1_5 x.1.1 x.1.2 + a22 * F2_5 x.1.1 x.1.2 = 0 := by
    have := congr_arg Prod.snd hTx; dsimp only [T] at this; linarith
  refine ⟨x.1, x.2, ?_, ?_⟩
  · have h1 : (a11 * a22 - a12 * a21) * F1_5 x.1.1 x.1.2 = 0 := by
      linear_combination a22 * hAF1 - a12 * hAF2
    exact (mul_eq_zero.mp h1).resolve_left hdet
  · have h2 : (a11 * a22 - a12 * a21) * F2_5 x.1.1 x.1.2 = 0 := by
      linear_combination -a21 * hAF1 + a11 * hAF2
    exact (mul_eq_zero.mp h2).resolve_left hdet

/-! ## Section 5: Interval-Arithmetic Certification of the 2 Off-Diagonal Roots -/

/-- Interval multiplication helper: if `a ∈ [al, ah]` and `b ∈ [bl, bh]`,
    then `a * b` lies between the min and max of the 4 corner products. -/
lemma mul_mem_Icc_of_corners (a b al ah bl bh lo hi : ℝ)
    (ha : al ≤ a ∧ a ≤ ah) (hb : bl ≤ b ∧ b ≤ bh)
    (h1 : lo ≤ al * bl ∧ al * bl ≤ hi)
    (h2 : lo ≤ al * bh ∧ al * bh ≤ hi)
    (h3 : lo ≤ ah * bl ∧ ah * bl ≤ hi)
    (h4 : lo ≤ ah * bh ∧ ah * bh ≤ hi) : lo ≤ a * b ∧ a * b ≤ hi := by
  constructor
  · have h1' : lo ≤ a * bl := by
      by_cases hbl : 0 ≤ bl
      · exact le_trans h1.1 (mul_le_mul_of_nonneg_right ha.1 hbl)
      · exact le_trans h3.1 (mul_le_mul_of_nonpos_right ha.2 (le_of_not_ge hbl))
    have h2' : lo ≤ a * bh := by
      by_cases hbh : 0 ≤ bh
      · exact le_trans h2.1 (mul_le_mul_of_nonneg_right ha.1 hbh)
      · exact le_trans h4.1 (mul_le_mul_of_nonpos_right ha.2 (le_of_not_ge hbh))
    by_cases ha0 : 0 ≤ a
    · exact le_trans h1' (mul_le_mul_of_nonneg_left hb.1 ha0)
    · exact le_trans h2' (mul_le_mul_of_nonpos_left hb.2 (le_of_not_ge ha0))
  · have h1' : a * bl ≤ hi := by
      by_cases hbl : 0 ≤ bl
      · exact le_trans (mul_le_mul_of_nonneg_right ha.2 hbl) h3.2
      · exact le_trans (mul_le_mul_of_nonpos_right ha.1 (le_of_not_ge hbl)) h1.2
    have h2' : a * bh ≤ hi := by
      by_cases hbh : 0 ≤ bh
      · exact le_trans (mul_le_mul_of_nonneg_right ha.2 hbh) h4.2
      · exact le_trans (mul_le_mul_of_nonpos_right ha.1 (le_of_not_ge hbh)) h2.2
    by_cases ha0 : 0 ≤ a
    · exact le_trans (mul_le_mul_of_nonneg_left hb.2 ha0) h2'
    · exact le_trans (mul_le_mul_of_nonpos_left hb.1 (le_of_not_ge ha0)) h1'

lemma dphi_mem_Icc {t tlo thi ylo yhi : ℝ}
    (htlo : 0 < tlo) (ht : tlo ≤ t ∧ t ≤ thi)
    (hylo : 0 < ylo) (hy : ylo ≤ phi t ∧ phi t ≤ yhi) :
    -(2 : ℝ) / 3 * yhi / tlo ≤ dphi t ∧ dphi t ≤ -(2 : ℝ) / 3 * ylo / thi := by
  unfold dphi
  have htpos : 0 < t := lt_of_lt_of_le htlo ht.1
  constructor
  · have h1 : phi t / t ≤ yhi / tlo := div_le_div₀ (by linarith) hy.2 htlo ht.1
    linarith [show -(2 : ℝ) / 3 * phi t / t = -(2 / 3) * (phi t / t) by ring,
              show -(2 : ℝ) / 3 * yhi / tlo = -(2 / 3) * (yhi / tlo) by ring]
  · have h1 : ylo / thi ≤ phi t / t := div_le_div₀ (by linarith) hy.1 htpos ht.2
    linarith [show -(2 : ℝ) / 3 * phi t / t = -(2 / 3) * (phi t / t) by ring,
              show -(2 : ℝ) / 3 * ylo / thi = -(2 / 3) * (ylo / thi) by ring]

/-- Certified Root 3 (`D+` off-diagonal): `u ∈ [0.272325, 0.272525]`, `v ∈ [0.469707, 0.469907]`. -/
theorem exists_root3_Dplus_offdiag :
    ∃ s : DziobekSol 5 5 1,
      (272325 / 1000000 : ℝ) ≤ s.u ∧ s.u ≤ 272525 / 1000000 ∧
      (469707 / 1000000 : ℝ) ≤ s.v ∧ s.v ≤ 469907 / 1000000 := by
  let u0 : ℝ := 272425 / 1000000
  let v0 : ℝ := 469807 / 1000000
  let r : ℝ := 1 / 10000
  let a11 : ℝ := -4307 / 1000
  let a12 : ℝ := 4048 / 1000
  let a21 : ℝ := 4048 / 1000
  let a22 : ℝ := -4294 / 1000
  have hdom : ∀ p ∈ Box u0 v0 r,
      0 < 1 - p.1 ^ 2 ∧ 0 < 1 - p.2 ^ 2 ∧ 0 < 1 - p.1 * p.2 ∧
      0 < 1 + 10 * p.1 * (p.1 + p.2) ∧ 0 < 1 + 10 * p.2 * (p.1 + p.2) := by
    intro ⟨u, v⟩ ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩
    dsimp only [u0, v0, r] at hu1 hu2 hv1 hv2
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  have hcenter :
      |a11 * F1_5 u0 v0 + a12 * F2_5 u0 v0| ≤ r / 2 ∧
      |a21 * F1_5 u0 v0 + a22 * F2_5 u0 v0| ≤ r / 2 := by
    have hta : 0 < 1 - u0 ^ 2 := by dsimp only [u0]; norm_num
    have htb : 0 < 1 - v0 ^ 2 := by dsimp only [v0]; norm_num
    have hte : 0 < 1 - u0 * v0 := by dsimp only [u0, v0]; norm_num
    have htc : 0 < 1 + 10 * u0 * (u0 + v0) := by dsimp only [u0, v0]; norm_num
    have htd : 0 < 1 + 10 * v0 * (u0 + v0) := by dsimp only [u0, v0]; norm_num
    have ha_l : (26318837 / 25000000 : ℝ) ≤ phi (1 - u0 ^ 2) :=
      phi_lower hta le_rfl (by norm_num) (by dsimp only [u0]; norm_num)
    have ha_u : phi (1 - u0 ^ 2) ≤ (105275351 / 100000000 : ℝ) :=
      phi_upper hta hta le_rfl (by norm_num) (by dsimp only [u0]; norm_num)
    have hb_l : (118087463 / 100000000 : ℝ) ≤ phi (1 - v0 ^ 2) :=
      phi_lower htb le_rfl (by norm_num) (by dsimp only [v0]; norm_num)
    have hb_u : phi (1 - v0 ^ 2) ≤ (59043733 / 50000000 : ℝ) :=
      phi_upper htb htb le_rfl (by norm_num) (by dsimp only [v0]; norm_num)
    have he_l : (54779923 / 50000000 : ℝ) ≤ phi (1 - u0 * v0) :=
      phi_lower hte le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have he_u : phi (1 - u0 * v0) ≤ (109559849 / 100000000 : ℝ) :=
      phi_upper hte hte le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have hc_l : (47841109 / 100000000 : ℝ) ≤ phi (1 + 10 * u0 * (u0 + v0)) :=
      phi_lower htc le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have hc_u : phi (1 + 10 * u0 * (u0 + v0)) ≤ (5980139 / 12500000 : ℝ) :=
      phi_upper htc htc le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have hd_l : (574353 / 1562500 : ℝ) ≤ phi (1 + 10 * v0 * (u0 + v0)) :=
      phi_lower htd le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have hd_u : phi (1 + 10 * v0 * (u0 + v0)) ≤ (7351719 / 20000000 : ℝ) :=
      phi_upper htd htd le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    unfold F1_5 F2_5
    dsimp only [u0, v0, r, a11, a12, a21, a22] at ha_l ha_u hb_l hb_u he_l he_u hc_l hc_u hd_l hd_u ⊢
    constructor <;> rw [abs_le] <;> constructor <;> linarith
  have hcontr : ∀ p ∈ Box u0 v0 r,
      |1 - (a11 * J11_5 p.1 p.2 + a12 * J21_5 p.1 p.2)| +
      |-(a11 * J12_5 p.1 p.2 + a12 * J22_5 p.1 p.2)| ≤ 1 / 2 ∧
      |-(a21 * J11_5 p.1 p.2 + a22 * J21_5 p.1 p.2)| +
      |1 - (a21 * J12_5 p.1 p.2 + a22 * J22_5 p.1 p.2)| ≤ 1 / 2 := by
    intro ⟨u, v⟩ hp
    have ⟨hta, htb, hte, htc, htd⟩ := hdom (u, v) hp
    rcases hp with ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩
    dsimp only [u0, v0, r] at hu1 hu2 hv1 hv2
    have hu_b : (272325 / 1000000 : ℝ) ≤ u ∧ u ≤ 272525 / 1000000 := ⟨by linarith, by linarith⟩
    have hv_b : (469707 / 1000000 : ℝ) ≤ v ∧ v ≤ 469907 / 1000000 := ⟨by linarith, by linarith⟩
    have hta_b : (9257 / 10000 : ℝ) ≤ 1 - u ^ 2 ∧ 1 - u ^ 2 ≤ 9259 / 10000 := ⟨by nlinarith, by nlinarith⟩
    have htb_b : (7791 / 10000 : ℝ) ≤ 1 - v ^ 2 ∧ 1 - v ^ 2 ≤ 7794 / 10000 := ⟨by nlinarith, by nlinarith⟩
    have hte_b : (8719 / 10000 : ℝ) ≤ 1 - u * v ∧ 1 - u * v ≤ 8722 / 10000 := ⟨by nlinarith, by nlinarith⟩
    have htc_b : (3020 / 1000 : ℝ) ≤ 1 + 10 * u * (u + v) ∧ 1 + 10 * u * (u + v) ≤ 3025 / 1000 := ⟨by nlinarith, by nlinarith⟩
    have htd_b : (4485 / 1000 : ℝ) ≤ 1 + 10 * v * (u + v) ∧ 1 + 10 * v * (u + v) ≤ 4491 / 1000 := ⟨by nlinarith, by nlinarith⟩
    have ha_b : (10526 / 10000 : ℝ) ≤ phi (1 - u ^ 2) ∧ phi (1 - u ^ 2) ≤ 10529 / 10000 :=
      ⟨phi_lower hta hta_b.2 (by norm_num) (by norm_num), phi_upper hta (by norm_num) hta_b.1 (by norm_num) (by norm_num)⟩
    have hb_b : (11805 / 10000 : ℝ) ≤ phi (1 - v ^ 2) ∧ phi (1 - v ^ 2) ≤ 11812 / 10000 :=
      ⟨phi_lower htb htb_b.2 (by norm_num) (by norm_num), phi_upper htb (by norm_num) htb_b.1 (by norm_num) (by norm_num)⟩
    have he_b : (10953 / 10000 : ℝ) ≤ phi (1 - u * v) ∧ phi (1 - u * v) ≤ 10959 / 10000 :=
      ⟨phi_lower hte hte_b.2 (by norm_num) (by norm_num), phi_upper hte (by norm_num) hte_b.1 (by norm_num) (by norm_num)⟩
    have hc_b : (4779 / 10000 : ℝ) ≤ phi (1 + 10 * u * (u + v)) ∧ phi (1 + 10 * u * (u + v)) ≤ 4788 / 10000 :=
      ⟨phi_lower htc htc_b.2 (by norm_num) (by norm_num), phi_upper htc (by norm_num) htc_b.1 (by norm_num) (by norm_num)⟩
    have hd_b : (3673 / 10000 : ℝ) ≤ phi (1 + 10 * v * (u + v)) ∧ phi (1 + 10 * v * (u + v)) ≤ 3679 / 10000 :=
      ⟨phi_lower htd htd_b.2 (by norm_num) (by norm_num), phi_upper htd (by norm_num) htd_b.1 (by norm_num) (by norm_num)⟩
    have hda := dphi_mem_Icc (by norm_num) hta_b (by norm_num) ha_b
    have hdb := dphi_mem_Icc (by norm_num) htb_b (by norm_num) hb_b
    have hde := dphi_mem_Icc (by norm_num) hte_b (by norm_num) he_b
    have hdc := dphi_mem_Icc (by norm_num) htc_b (by norm_num) hc_b
    have hdd := dphi_mem_Icc (by norm_num) htd_b (by norm_num) hd_b
    have hdau := mul_mem_Icc_of_corners (dphi (1 - u ^ 2)) (-2 * u) _ _ (-5451 / 10000) (-5446 / 10000) (412 / 1000) (415 / 1000)
      hda ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdbv := mul_mem_Icc_of_corners (dphi (1 - v ^ 2)) (-2 * v) _ _ (-9399 / 10000) (-9394 / 10000) (948 / 1000) (952 / 1000)
      hdb ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdeu := mul_mem_Icc_of_corners (dphi (1 - u * v)) (-v) _ _ (-4700 / 10000) (-4697 / 10000) (393 / 1000) (396 / 1000)
      hde ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdev := mul_mem_Icc_of_corners (dphi (1 - u * v)) (-u) _ _ (-2726 / 10000) (-2723 / 10000) (227 / 1000) (230 / 1000)
      hde ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdcu := mul_mem_Icc_of_corners (dphi (1 + 10 * u * (u + v))) (20 * u + 10 * v) _ _ (10143 / 1000) (10150 / 1000) (-1074 / 1000) (-1067 / 1000)
      hdc ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdcv := mul_mem_Icc_of_corners (dphi (1 + 10 * u * (u + v))) (10 * u) _ _ (2723 / 1000) (2726 / 1000) (-289 / 1000) (-285 / 1000)
      hdc ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hddu := mul_mem_Icc_of_corners (dphi (1 + 10 * v * (u + v))) (10 * v) _ _ (4697 / 1000) (4700 / 1000) (-258 / 1000) (-255 / 1000)
      hdd ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hddv := mul_mem_Icc_of_corners (dphi (1 + 10 * v * (u + v))) (10 * u + 20 * v) _ _ (12117 / 1000) (12124 / 1000) (-665 / 1000) (-659 / 1000)
      hdd ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hJ11 : (-2055 / 1000 : ℝ) ≤ J11_5 u v ∧ J11_5 u v ≤ -2015 / 1000 := by
      unfold J11_5; dsimp only
      have ht1 := mul_mem_Icc_of_corners u (4 * (dphi (1 + 10 * u * (u + v)) * (20 * u + 10 * v)) - dphi (1 - u ^ 2) * (-2 * u))
        _ _ (-4711 / 1000) (-4680 / 1000) (-1285 / 1000) (-1274 / 1000)
        hu_b ⟨by linarith only [hdcu, hdau], by linarith only [hdcu, hdau]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have ht2 := mul_mem_Icc_of_corners (2 * v) (dphi (1 + 10 * u * (u + v)) * (20 * u + 10 * v) + dphi (1 + 10 * v * (u + v)) * (10 * v) - dphi (1 - u * v) * (-v))
        (9394 / 10000) (9399 / 10000) (-1728 / 1000) (-1715 / 1000) (-1625 / 1000) (-1610 / 1000)
        ⟨by linarith only [hv_b], by linarith only [hv_b]⟩
        ⟨by linarith only [hdcu, hddu, hdeu], by linarith only [hdcu, hddu, hdeu]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      exact ⟨by linarith only [hc_b, ha_b, ht1, ht2], by linarith only [hc_b, ha_b, ht1, ht2]⟩
    have hJ12 : (-1938 / 1000 : ℝ) ≤ J12_5 u v ∧ J12_5 u v ≤ -1902 / 1000 := by
      unfold J12_5; dsimp only
      have ht1 := mul_mem_Icc_of_corners u (4 * (dphi (1 + 10 * u * (u + v)) * (10 * u)))
        _ _ (-1156 / 1000) (-1140 / 1000) (-316 / 1000) (-310 / 1000)
        hu_b ⟨by linarith only [hdcv], by linarith only [hdcv]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have ht2 := mul_mem_Icc_of_corners (2 * v) (dphi (1 + 10 * u * (u + v)) * (10 * u) + dphi (1 + 10 * v * (u + v)) * (10 * u + 20 * v) - dphi (1 - u * v) * (-u))
        (9394 / 10000) (9399 / 10000) (-1184 / 1000) (-1171 / 1000) (-1114 / 1000) (-1099 / 1000)
        ⟨by linarith only [hv_b], by linarith only [hv_b]⟩
        ⟨by linarith only [hdcv, hddv, hdev], by linarith only [hdcv, hddv, hdev]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      exact ⟨by linarith only [hc_b, hd_b, he_b, ht1, ht2], by linarith only [hc_b, hd_b, he_b, ht1, ht2]⟩
    have hJ21 : (-1938 / 1000 : ℝ) ≤ J21_5 u v ∧ J21_5 u v ≤ -1902 / 1000 := by
      unfold J21_5; dsimp only
      have ht1 := mul_mem_Icc_of_corners v (4 * (dphi (1 + 10 * v * (u + v)) * (10 * v)))
        _ _ (-1032 / 1000) (-1020 / 1000) (-486 / 1000) (-479 / 1000)
        hv_b ⟨by linarith only [hddu], by linarith only [hddu]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have ht2 := mul_mem_Icc_of_corners (2 * u) (dphi (1 + 10 * u * (u + v)) * (20 * u + 10 * v) + dphi (1 + 10 * v * (u + v)) * (10 * v) - dphi (1 - u * v) * (-v))
        (5446 / 10000) (5451 / 10000) (-1728 / 1000) (-1715 / 1000) (-943 / 1000) (-933 / 1000)
        ⟨by linarith only [hu_b], by linarith only [hu_b]⟩
        ⟨by linarith only [hdcu, hddu, hdeu], by linarith only [hdcu, hddu, hdeu]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      exact ⟨by linarith only [hc_b, hd_b, he_b, ht1, ht2], by linarith only [hc_b, hd_b, he_b, ht1, ht2]⟩
    have hJ22 : (-2060 / 1000 : ℝ) ≤ J22_5 u v ∧ J22_5 u v ≤ -2020 / 1000 := by
      unfold J22_5; dsimp only
      have ht1 := mul_mem_Icc_of_corners v (4 * (dphi (1 + 10 * v * (u + v)) * (10 * u + 20 * v)) - dphi (1 - v ^ 2) * (-2 * v))
        _ _ (-3612 / 1000) (-3584 / 1000) (-1698 / 1000) (-1683 / 1000)
        hv_b ⟨by linarith only [hddv, hdbv], by linarith only [hddv, hdbv]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have ht2 := mul_mem_Icc_of_corners (2 * u) (dphi (1 + 10 * u * (u + v)) * (10 * u) + dphi (1 + 10 * v * (u + v)) * (10 * u + 20 * v) - dphi (1 - u * v) * (-u))
        (5446 / 10000) (5451 / 10000) (-1184 / 1000) (-1171 / 1000) (-646 / 1000) (-637 / 1000)
        ⟨by linarith only [hu_b], by linarith only [hu_b]⟩
        ⟨by linarith only [hdcv, hddv, hdev], by linarith only [hdcv, hddv, hdev]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      exact ⟨by linarith only [hd_b, hb_b, ht1, ht2], by linarith only [hd_b, hb_b, ht1, ht2]⟩
    dsimp only [a11, a12, a21, a22]
    have hm11 : |1 - (-4307 / 1000 * J11_5 u v + 4048 / 1000 * J21_5 u v)| ≤ 1 / 4 := by
      rw [abs_le]; exact ⟨by linarith only [hJ11, hJ21], by linarith only [hJ11, hJ21]⟩
    have hm12 : |-(-4307 / 1000 * J12_5 u v + 4048 / 1000 * J22_5 u v)| ≤ 1 / 4 := by
      rw [abs_le]; exact ⟨by linarith only [hJ12, hJ22], by linarith only [hJ12, hJ22]⟩
    have hm21 : |-(4048 / 1000 * J11_5 u v + -4294 / 1000 * J21_5 u v)| ≤ 1 / 4 := by
      rw [abs_le]; exact ⟨by linarith only [hJ11, hJ21], by linarith only [hJ11, hJ21]⟩
    have hm22 : |1 - (4048 / 1000 * J12_5 u v + -4294 / 1000 * J22_5 u v)| ≤ 1 / 4 := by
      rw [abs_le]; exact ⟨by linarith only [hJ12, hJ22], by linarith only [hJ12, hJ22]⟩
    exact ⟨by linarith only [hm11, hm12], by linarith only [hm21, hm22]⟩
  obtain ⟨⟨u, v⟩, hp_mem, hF1, hF2⟩ := banach_box_root (by dsimp only [r]; norm_num)
    (by dsimp only [a11, a12, a21, a22]; norm_num) hdom hcontr hcenter
  have ⟨hta, htb, hte, htc, htd⟩ := hdom (u, v) hp_mem
  rcases hp_mem with ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩
  dsimp only [u0, v0, r] at hu1 hu2 hv1 hv2
  have ha_u : phi (1 - u ^ 2) ≤ 10529 / 10000 :=
    phi_upper (t_lo := 9257 / 10000) hta (by norm_num) (by nlinarith only [hu1, hu2]) (by norm_num) (by norm_num)
  have hb_u : phi (1 - v ^ 2) ≤ 11812 / 10000 :=
    phi_upper (t_lo := 7791 / 10000) htb (by norm_num) (by nlinarith only [hv1, hv2]) (by norm_num) (by norm_num)
  have hc_l : (4779 / 10000 : ℝ) ≤ phi (1 + 10 * u * (u + v)) :=
    phi_lower (t_hi := 3025 / 1000) htc (by nlinarith only [hu1, hu2, hv1, hv2]) (by norm_num) (by norm_num)
  have hd_l : (3673 / 10000 : ℝ) ≤ phi (1 + 10 * v * (u + v)) :=
    phi_lower (t_hi := 4491 / 1000) htd (by nlinarith only [hu1, hu2, hv1, hv2]) (by norm_num) (by norm_num)
  exact ⟨root_to_dziobek5 (by linarith only [hu1]) (by linarith only [hv1]) hta htb hte htc htd hF1 hF2
    (by linarith only [ha_u, hc_l]) (by linarith only [hb_u, hd_l]),
    show (272325 / 1000000 : ℝ) ≤ u by linarith only [hu1],
    show u ≤ 272525 / 1000000 by linarith only [hu2],
    show (469707 / 1000000 : ℝ) ≤ v by linarith only [hv1],
    show v ≤ 469907 / 1000000 by linarith only [hv2]⟩

/-- Certified Root 4 (`D-` off-diagonal): `u ∈ [0.218245, 0.218445]`, `v ∈ [-0.461089, -0.460889]`. -/
theorem exists_root4_Dminus_offdiag :
    ∃ s : DziobekSol 5 5 1,
      (218245 / 1000000 : ℝ) ≤ s.u ∧ s.u ≤ 218445 / 1000000 ∧
      (-461089 / 1000000 : ℝ) ≤ s.v ∧ s.v ≤ -460889 / 1000000 := by
  let u0 : ℝ := 218345 / 1000000
  let v0 : ℝ := -460989 / 1000000
  let r : ℝ := 1 / 10000
  let a11 : ℝ := 186 / 1000
  let a12 : ℝ := 98 / 1000
  let a21 : ℝ := 98 / 1000
  let a22 : ℝ := -247 / 1000
  have hdom : ∀ p ∈ Box u0 v0 r,
      0 < 1 - p.1 ^ 2 ∧ 0 < 1 - p.2 ^ 2 ∧ 0 < 1 - p.1 * p.2 ∧
      0 < 1 + 10 * p.1 * (p.1 + p.2) ∧ 0 < 1 + 10 * p.2 * (p.1 + p.2) := by
    intro ⟨u, v⟩ ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩
    dsimp only [u0, v0, r] at hu1 hu2 hv1 hv2
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  have hcenter :
      |a11 * F1_5 u0 v0 + a12 * F2_5 u0 v0| ≤ r / 2 ∧
      |a21 * F1_5 u0 v0 + a22 * F2_5 u0 v0| ≤ r / 2 := by
    have hta : 0 < 1 - u0 ^ 2 := by dsimp only [u0]; norm_num
    have htb : 0 < 1 - v0 ^ 2 := by dsimp only [v0]; norm_num
    have hte : 0 < 1 - u0 * v0 := by dsimp only [u0, v0]; norm_num
    have htc : 0 < 1 + 10 * u0 * (u0 + v0) := by dsimp only [u0, v0]; norm_num
    have htd : 0 < 1 + 10 * v0 * (u0 + v0) := by dsimp only [u0, v0]; norm_num
    have ha_l : (103310167 / 100000000 : ℝ) ≤ phi (1 - u0 ^ 2) :=
      phi_lower hta le_rfl (by norm_num) (by dsimp only [u0]; norm_num)
    have ha_u : phi (1 - u0 ^ 2) ≤ (10331017 / 10000000 : ℝ) :=
      phi_upper hta hta le_rfl (by norm_num) (by dsimp only [u0]; norm_num)
    have hb_l : (23453101 / 20000000 : ℝ) ≤ phi (1 - v0 ^ 2) :=
      phi_lower htb le_rfl (by norm_num) (by dsimp only [v0]; norm_num)
    have hb_u : phi (1 - v0 ^ 2) ≤ (29316377 / 25000000 : ℝ) :=
      phi_upper htb htb le_rfl (by norm_num) (by dsimp only [v0]; norm_num)
    have he_l : (93806431 / 100000000 : ℝ) ≤ phi (1 - u0 * v0) :=
      phi_lower hte le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have he_u : phi (1 - u0 * v0) ≤ (46903217 / 50000000 : ℝ) :=
      phi_upper hte hte le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have hc_l : (165378439 / 100000000 : ℝ) ≤ phi (1 + 10 * u0 * (u0 + v0)) :=
      phi_lower htc le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have hc_u : phi (1 + 10 * u0 * (u0 + v0)) ≤ (82689221 / 50000000 : ℝ) :=
      phi_upper htc htc le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have hd_l : (30311623 / 50000000 : ℝ) ≤ phi (1 + 10 * v0 * (u0 + v0)) :=
      phi_lower htd le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    have hd_u : phi (1 + 10 * v0 * (u0 + v0)) ≤ (60623249 / 100000000 : ℝ) :=
      phi_upper htd htd le_rfl (by norm_num) (by dsimp only [u0, v0]; norm_num)
    unfold F1_5 F2_5
    dsimp only [u0, v0, r, a11, a12, a21, a22] at ha_l ha_u hb_l hb_u he_l he_u hc_l hc_u hd_l hd_u ⊢
    constructor <;> rw [abs_le] <;> constructor <;> linarith
  have hcontr : ∀ p ∈ Box u0 v0 r,
      |1 - (a11 * J11_5 p.1 p.2 + a12 * J21_5 p.1 p.2)| +
      |-(a11 * J12_5 p.1 p.2 + a12 * J22_5 p.1 p.2)| ≤ 1 / 2 ∧
      |-(a21 * J11_5 p.1 p.2 + a22 * J21_5 p.1 p.2)| +
      |1 - (a21 * J12_5 p.1 p.2 + a22 * J22_5 p.1 p.2)| ≤ 1 / 2 := by
    intro ⟨u, v⟩ hp
    have ⟨hta, htb, hte, htc, htd⟩ := hdom (u, v) hp
    rcases hp with ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩
    dsimp only [u0, v0, r] at hu1 hu2 hv1 hv2
    have hu_b : (218245 / 1000000 : ℝ) ≤ u ∧ u ≤ 218445 / 1000000 := ⟨by linarith, by linarith⟩
    have hv_b : (-461089 / 1000000 : ℝ) ≤ v ∧ v ≤ -460889 / 1000000 := ⟨by linarith, by linarith⟩
    have hta_b : (9522 / 10000 : ℝ) ≤ 1 - u ^ 2 ∧ 1 - u ^ 2 ≤ 9525 / 10000 := ⟨by nlinarith, by nlinarith⟩
    have htb_b : (7873 / 10000 : ℝ) ≤ 1 - v ^ 2 ∧ 1 - v ^ 2 ≤ 7877 / 10000 := ⟨by nlinarith, by nlinarith⟩
    have hte_b : (11005 / 10000 : ℝ) ≤ 1 - u * v ∧ 1 - u * v ≤ 11009 / 10000 := ⟨by nlinarith, by nlinarith⟩
    have htc_b : (469 / 1000 : ℝ) ≤ 1 + 10 * u * (u + v) ∧ 1 + 10 * u * (u + v) ≤ 471 / 1000 := ⟨by nlinarith, by nlinarith⟩
    have htd_b : (2116 / 1000 : ℝ) ≤ 1 + 10 * v * (u + v) ∧ 1 + 10 * v * (u + v) ≤ 2121 / 1000 := ⟨by nlinarith, by nlinarith⟩
    have ha_b : (10329 / 10000 : ℝ) ≤ phi (1 - u ^ 2) ∧ phi (1 - u ^ 2) ≤ 10333 / 10000 :=
      ⟨phi_lower hta hta_b.2 (by norm_num) (by norm_num), phi_upper hta (by norm_num) hta_b.1 (by norm_num) (by norm_num)⟩
    have hb_b : (11724 / 10000 : ℝ) ≤ phi (1 - v ^ 2) ∧ phi (1 - v ^ 2) ≤ 11730 / 10000 :=
      ⟨phi_lower htb htb_b.2 (by norm_num) (by norm_num), phi_upper htb (by norm_num) htb_b.1 (by norm_num) (by norm_num)⟩
    have he_b : (9378 / 10000 : ℝ) ≤ phi (1 - u * v) ∧ phi (1 - u * v) ≤ 9383 / 10000 :=
      ⟨phi_lower hte hte_b.2 (by norm_num) (by norm_num), phi_upper hte (by norm_num) hte_b.1 (by norm_num) (by norm_num)⟩
    have hc_b : (1651 / 1000 : ℝ) ≤ phi (1 + 10 * u * (u + v)) ∧ phi (1 + 10 * u * (u + v)) ≤ 1657 / 1000 :=
      ⟨phi_lower htc htc_b.2 (by norm_num) (by norm_num), phi_upper htc (by norm_num) htc_b.1 (by norm_num) (by norm_num)⟩
    have hd_b : (605 / 1000 : ℝ) ≤ phi (1 + 10 * v * (u + v)) ∧ phi (1 + 10 * v * (u + v)) ≤ 608 / 1000 :=
      ⟨phi_lower htd htd_b.2 (by norm_num) (by norm_num), phi_upper htd (by norm_num) htd_b.1 (by norm_num) (by norm_num)⟩
    have hda := dphi_mem_Icc (by norm_num) hta_b (by norm_num) ha_b
    have hdb := dphi_mem_Icc (by norm_num) htb_b (by norm_num) hb_b
    have hde := dphi_mem_Icc (by norm_num) hte_b (by norm_num) he_b
    have hdc := dphi_mem_Icc (by norm_num) htc_b (by norm_num) hc_b
    have hdd := dphi_mem_Icc (by norm_num) htd_b (by norm_num) hd_b
    have hdau := mul_mem_Icc_of_corners (dphi (1 - u ^ 2)) (-2 * u) _ _ (-4369 / 10000) (-4364 / 10000) (314 / 1000) (318 / 1000)
      hda ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdbv := mul_mem_Icc_of_corners (dphi (1 - v ^ 2)) (-2 * v) _ _ (9217 / 10000) (9222 / 10000) (-920 / 1000) (-912 / 1000)
      hdb ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdeu := mul_mem_Icc_of_corners (dphi (1 - u * v)) (-v) _ _ (4608 / 10000) (4611 / 10000) (-264 / 1000) (-260 / 1000)
      hde ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdev := mul_mem_Icc_of_corners (dphi (1 - u * v)) (-u) _ _ (-2185 / 10000) (-2182 / 10000) (123 / 1000) (126 / 1000)
      hde ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdcu := mul_mem_Icc_of_corners (dphi (1 + 10 * u * (u + v))) (20 * u + 10 * v) _ _ (-247 / 1000) (-239 / 1000) (555 / 1000) (585 / 1000)
      hdc ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hdcv := mul_mem_Icc_of_corners (dphi (1 + 10 * u * (u + v))) (10 * u) _ _ (2182 / 1000) (2185 / 1000) (-516 / 100) (-509 / 100)
      hdc ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hddu := mul_mem_Icc_of_corners (dphi (1 + 10 * v * (u + v))) (10 * v) _ _ (-4611 / 1000) (-4608 / 1000) (870 / 1000) (890 / 1000)
      hdd ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hddv := mul_mem_Icc_of_corners (dphi (1 + 10 * v * (u + v))) (10 * u + 20 * v) _ _ (-7040 / 1000) (-7032 / 1000) (1330 / 1000) (1360 / 1000)
      hdd ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    have hJ11 : (430 / 100 : ℝ) ≤ J11_5 u v ∧ J11_5 u v ≤ 456 / 100 := by
      unfold J11_5; dsimp only
      have ht1 := mul_mem_Icc_of_corners u (4 * (dphi (1 + 10 * u * (u + v)) * (20 * u + 10 * v)) - dphi (1 - u ^ 2) * (-2 * u))
        _ _ (1902 / 1000) (2026 / 1000) (41 / 100) (45 / 100)
        hu_b ⟨by linarith only [hdcu, hdau], by linarith only [hdcu, hdau]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have ht2 := mul_mem_Icc_of_corners (2 * v) (dphi (1 + 10 * u * (u + v)) * (20 * u + 10 * v) + dphi (1 + 10 * v * (u + v)) * (10 * v) - dphi (1 - u * v) * (-v))
        (-9222 / 10000) (-9217 / 10000) (1685 / 1000) (1739 / 1000) (-161 / 100) (-155 / 100)
        ⟨by linarith only [hv_b], by linarith only [hv_b]⟩
        ⟨by linarith only [hdcu, hddu, hdeu], by linarith only [hdcu, hddu, hdeu]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      exact ⟨by linarith only [hc_b, ha_b, ht1, ht2], by linarith only [hc_b, ha_b, ht1, ht2]⟩
    have hJ12 : (165 / 100 : ℝ) ≤ J12_5 u v ∧ J12_5 u v ≤ 192 / 100 := by
      unfold J12_5; dsimp only
      have ht1 := mul_mem_Icc_of_corners u (4 * (dphi (1 + 10 * u * (u + v)) * (10 * u)))
        _ _ (-2064 / 100) (-2036 / 100) (-452 / 100) (-444 / 100)
        hu_b ⟨by linarith only [hdcv], by linarith only [hdcv]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have ht2 := mul_mem_Icc_of_corners (2 * v) (dphi (1 + 10 * u * (u + v)) * (10 * u) + dphi (1 + 10 * v * (u + v)) * (10 * u + 20 * v) - dphi (1 - u * v) * (-u))
        (-9222 / 10000) (-9217 / 10000) (-3956 / 1000) (-3853 / 1000) (355 / 100) (367 / 100)
        ⟨by linarith only [hv_b], by linarith only [hv_b]⟩
        ⟨by linarith only [hdcv, hddv, hdev], by linarith only [hdcv, hddv, hdev]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      exact ⟨by linarith only [hc_b, hd_b, he_b, ht1, ht2], by linarith only [hc_b, hd_b, he_b, ht1, ht2]⟩
    have hJ21 : (170 / 100 : ℝ) ≤ J21_5 u v ∧ J21_5 u v ≤ 186 / 100 := by
      unfold J21_5; dsimp only
      have ht1 := mul_mem_Icc_of_corners v (4 * (dphi (1 + 10 * v * (u + v)) * (10 * v)))
        _ _ (3480 / 1000) (3560 / 1000) (-165 / 100) (-159 / 100)
        hv_b ⟨by linarith only [hddu], by linarith only [hddu]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have ht2 := mul_mem_Icc_of_corners (2 * u) (dphi (1 + 10 * u * (u + v)) * (20 * u + 10 * v) + dphi (1 + 10 * v * (u + v)) * (10 * v) - dphi (1 - u * v) * (-v))
        (4364 / 10000) (4369 / 10000) (1685 / 1000) (1739 / 1000) (73 / 100) (77 / 100)
        ⟨by linarith only [hu_b], by linarith only [hu_b]⟩
        ⟨by linarith only [hdcu, hddu, hdeu], by linarith only [hdcu, hddu, hdeu]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      exact ⟨by linarith only [hc_b, hd_b, he_b, ht1, ht2], by linarith only [hc_b, hd_b, he_b, ht1, ht2]⟩
    have hJ22 : (-346 / 100 : ℝ) ≤ J22_5 u v ∧ J22_5 u v ≤ -324 / 100 := by
      unfold J22_5; dsimp only
      have ht1 := mul_mem_Icc_of_corners v (4 * (dphi (1 + 10 * v * (u + v)) * (10 * u + 20 * v)) - dphi (1 - v ^ 2) * (-2 * v))
        _ _ (6232 / 1000) (6360 / 1000) (-295 / 100) (-285 / 100)
        hv_b ⟨by linarith only [hddv, hdbv], by linarith only [hddv, hdbv]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have ht2 := mul_mem_Icc_of_corners (2 * u) (dphi (1 + 10 * u * (u + v)) * (10 * u) + dphi (1 + 10 * v * (u + v)) * (10 * u + 20 * v) - dphi (1 - u * v) * (-u))
        (4364 / 10000) (4369 / 10000) (-3956 / 1000) (-3853 / 1000) (-173 / 100) (-167 / 100)
        ⟨by linarith only [hu_b], by linarith only [hu_b]⟩
        ⟨by linarith only [hdcv, hddv, hdev], by linarith only [hdcv, hddv, hdev]⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      exact ⟨by linarith only [hd_b, hb_b, ht1, ht2], by linarith only [hd_b, hb_b, ht1, ht2]⟩
    dsimp only [a11, a12, a21, a22]
    have hm11 : |1 - (186 / 1000 * J11_5 u v + 98 / 1000 * J21_5 u v)| ≤ 1 / 4 := by
      rw [abs_le]; exact ⟨by linarith only [hJ11, hJ21], by linarith only [hJ11, hJ21]⟩
    have hm12 : |-(186 / 1000 * J12_5 u v + 98 / 1000 * J22_5 u v)| ≤ 1 / 4 := by
      rw [abs_le]; exact ⟨by linarith only [hJ12, hJ22], by linarith only [hJ12, hJ22]⟩
    have hm21 : |-(98 / 1000 * J11_5 u v + -247 / 1000 * J21_5 u v)| ≤ 1 / 4 := by
      rw [abs_le]; exact ⟨by linarith only [hJ11, hJ21], by linarith only [hJ11, hJ21]⟩
    have hm22 : |1 - (98 / 1000 * J12_5 u v + -247 / 1000 * J22_5 u v)| ≤ 1 / 4 := by
      rw [abs_le]; exact ⟨by linarith only [hJ12, hJ22], by linarith only [hJ12, hJ22]⟩
    exact ⟨by linarith only [hm11, hm12], by linarith only [hm21, hm22]⟩
  obtain ⟨⟨u, v⟩, hp_mem, hF1, hF2⟩ := banach_box_root (by dsimp only [r]; norm_num)
    (by dsimp only [a11, a12, a21, a22]; norm_num) hdom hcontr hcenter
  have ⟨hta, htb, hte, htc, htd⟩ := hdom (u, v) hp_mem
  rcases hp_mem with ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩
  dsimp only [u0, v0, r] at hu1 hu2 hv1 hv2
  have ha_u : phi (1 - u ^ 2) ≤ 10333 / 10000 :=
    phi_upper (t_lo := 9522 / 10000) hta (by norm_num) (by nlinarith only [hu1, hu2]) (by norm_num) (by norm_num)
  have hb_u : phi (1 - v ^ 2) ≤ 11730 / 10000 :=
    phi_upper (t_lo := 7873 / 10000) htb (by norm_num) (by nlinarith only [hv1, hv2]) (by norm_num) (by norm_num)
  have hc_l : (1651 / 1000 : ℝ) ≤ phi (1 + 10 * u * (u + v)) :=
    phi_lower (t_hi := 471 / 1000) htc (by nlinarith only [hu1, hu2, hv1, hv2]) (by norm_num) (by norm_num)
  have hd_l : (605 / 1000 : ℝ) ≤ phi (1 + 10 * v * (u + v)) :=
    phi_lower (t_hi := 2121 / 1000) htd (by nlinarith only [hu1, hu2, hv1, hv2]) (by norm_num) (by norm_num)
  exact ⟨root_to_dziobek5 (by linarith only [hu1]) (by linarith only [hv2]) hta htb hte htc htd hF1 hF2
    (by linarith only [ha_u, hc_l]) (by linarith only [hb_u, hd_l]),
    show (218245 / 1000000 : ℝ) ≤ u by linarith only [hu1],
    show u ≤ 218445 / 1000000 by linarith only [hu2],
    show (-461089 / 1000000 : ℝ) ≤ v by linarith only [hv1],
    show v ≤ -460889 / 1000000 by linarith only [hv2]⟩

/-! ## Section 6: Master Theorem — 6 Pairwise Distinct Strictly 3D $C_{2v}$ Central Configurations -/

lemma root1_u_bounds : (37 / 100 : ℝ) < root1_reg_tet.u ∧ root1_reg_tet.u < 38 / 100 ∧
    root1_reg_tet.v = root1_reg_tet.u := by
  unfold root1_reg_tet root_to_dziobek5
  dsimp only
  have ⟨hs1, hs2⟩ := sqrt6_bounds
  have hden : 0 < 16 * Real.sqrt 6 / 9 + 20 := by linarith
  refine ⟨?_, ?_, rfl⟩
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ hden]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ hden]; nlinarith

lemma root2_u_bounds : (68 / 100 : ℝ) < root2_sq_pyr.u ∧ root2_sq_pyr.u < 70 / 100 ∧
    root2_sq_pyr.v = -root2_sq_pyr.u := by
  unfold root2_sq_pyr root_to_dziobek5 u_sq_sq
  dsimp only
  have ⟨hs1, hs2⟩ := sqrt2_bounds
  refine ⟨?_, ?_, rfl⟩
  · rw [Real.lt_sqrt (by norm_num)]; linarith
  · rw [Real.sqrt_lt' (by norm_num)]; linarith

/-- **MAIN CERTIFIED EXISTENCE THEOREM**:
    For positive masses `(5, 5, 5, 5, 1)`, there exist **6 pairwise distinct, strictly 3D
    $C_{2v}$ Newtonian 5-body central configurations** (`Fin 6 → C2vCentralConfig 5 5 1`)
    satisfying all 15 Cartesian Newtonian force-balance equations, with pairwise distinct
    mutual-distance invariant `a = r₁₂` (3 in $\mathcal{D}^+$ and 3 in $\mathcal{D}^-$). -/
theorem six_distinct_3D_C2v_central_configurations :
    ∃ cfgs : Fin 6 → C2vCentralConfig 5 5 1,
      ∀ i j : Fin 6, i ≠ j → (cfgs i).a ≠ (cfgs j).a := by
  obtain ⟨r3, hr3u1, hr3u2, hr3v1, hr3v2⟩ := exists_root3_Dplus_offdiag
  obtain ⟨r4, hr4u1, hr4u2, hr4v1, hr4v2⟩ := exists_root4_Dminus_offdiag
  let sols : Fin 6 → DziobekSol 5 5 1 := fun i =>
    match i with
    | ⟨0, _⟩ => root1_reg_tet
    | ⟨1, _⟩ => r3
    | ⟨2, _⟩ => dziobek5_swap_pos r3 (by linarith)
    | ⟨3, _⟩ => root2_sq_pyr
    | ⟨4, _⟩ => r4
    | ⟨5, _⟩ => dziobek5_swap_neg r4 (by linarith)
  let cfgs : Fin 6 → C2vCentralConfig 5 5 1 :=
    fun i => dziobek_to_newtonian (by norm_num) (by norm_num) (by norm_num) (sols i)
  have ha_ne_of_u_ne : ∀ s t : DziobekSol 5 5 1, s.u ≠ t.u → s.a ≠ t.a := by
    intro s t hne haeq
    have h1 := s.h_a3
    have h2 := t.h_a3
    rw [haeq] at h1
    have ha3_ne : t.a ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt t.ha)
    have hu2_eq : 1 - s.u ^ 2 = 1 - t.u ^ 2 := mul_left_cancel₀ ha3_ne (by linarith)
    have : (s.u - t.u) * (s.u + t.u) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hne (sub_eq_zero.mp h0)
    · linarith [s.hu, t.hu]
  have ⟨hr1u1, hr1u2, _⟩ := root1_u_bounds
  have ⟨hr2u1, hr2u2, _⟩ := root2_u_bounds
  refine ⟨cfgs, ?_⟩
  intro i j hij
  apply ha_ne_of_u_ne (sols i) (sols j)
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | (dsimp only [sols, dziobek5_swap_pos, dziobek5_swap_neg]; linarith)

end Spatial5C2v

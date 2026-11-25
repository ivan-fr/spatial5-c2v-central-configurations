# Bi-Symmetric ($C_{2v}$) Spatial 5-Body Central Configurations

Machine-checked **Lean `v4.36.0` (`Mathlib4`)** formalization, **`pandsysroots v0.33.0`** certified Rust polynomial-system enumeration, and independent **220-digit** arbitrary-precision verification for Smale's 6th Problem in 3D ($N = 5$ bi-symmetric $C_{2v}$ configurations).

## Main Results

For arbitrary positive masses $(m_1, m_1, m_2, m_2, m_5) \in \mathbb{R}_{>0}^5$:

1. **Exact 2-Variable Dziobek Reduction & Reconstruction** (`Spatial5C2v/DziobekReduction.lean`):
   - Every strictly 3D $C_{2v}$ central configuration has $z_1 \neq 0, z_2 \neq 0$ (`no_zero_height`) and corresponds to a solution $(u, v) \in \mathcal{D}^+ \cup \mathcal{D}^- \subset (0, 1) \times (-1, 1)$ of two algebraic equations $(F_1, F_2) = (0, 0)$.
   - Every valid Dziobek solution reconstructs an exact strictly 3D Newtonian 5-body central configuration satisfying all 15 Cartesian force-balance equations (`dziobek_to_newtonian`).
2. **Universal Real Compactness & Complex Collision-Ray Elimination** (`Spatial5C2v/CompactnessAndRays.lean`):
   - Zero real solutions approach $\partial \mathcal{D}^+$ or $\partial \mathcal{D}^-$ for any $(m_1, m_2, m_5) \in \mathbb{R}_{>0}^3$ (zero exceptional mass loci).
   - Exact algebraic elimination in $\mathbb{C}$ of the critical collision rays $\{a,b,e\}$, $\{c,d\}$, and $\{a,b,c\}$ (even along the Hampton–Jensen exceptional hypersurface $2m_2 = 2m_1 + m_5$).
3. **Exact Dual Pitchfork Thresholds** (`Spatial5C2v/DualPitchfork.lean`):
   - Regular tetrahedron + center ($\mathcal{D}^+$): $m_c = \frac{81}{512 - 84\sqrt{6}} = \frac{10368 + 1701\sqrt{6}}{54952} \approx 0.26449596$ (`reg_tet_pitchfork_iff`).
   - **New exact square-pyramid pitchfork threshold** ($\mathcal{D}^-$):
     $$m_p^* = \frac{4 u_*^2}{3 - (\sqrt{2}+1) e_*^2} \approx 1.677188796521, \qquad u_*^2 = \frac{9 - 4\sqrt{2}}{7}, \quad e_*^2 = \left(\frac{9 + 4\sqrt{2}}{32}\right)^{1/3}$$
     with degree-6 integer minimal polynomial $27854687 m^6 - 303125760 m^5 + 1280885760 m^4 - 2621960192 m^3 + 2640052224 m^2 - 1189085184 m + 205520896 = 0$ (`square_pyramid_pitchfork_exact`).
4. **Certified 6-Root Existence in Lean `v4.36.0`** (`Spatial5C2v/SixRootsCertified.lean`):
   - Proves `six_distinct_3D_C2v_central_configurations`: existence of **6 pairwise distinct, strictly 3D Newtonian 5-body central configurations** at $(5, 5, 5, 5, 1)$ (`3` in $\mathcal{D}^+$ and `3` in $\mathcal{D}^-$) via exact closed-form constructions + 2D Newton–Banach contraction (`ContractingWith.exists_fixedPoint`).
   - Zero `sorry`, zero `native_decide`, standard Lean axioms `[propext, Classical.choice, Quot.sound]` only.
5. **Complete `pandsysroots v0.33.0` 10-Benchmark Certification** (`src/main.rs`):
   - Certifies 10/10 benchmarks covering all 3 count regimes (`2`, `4`, `6` — including symmetric `(5,5,5,5,1)` and asymmetric `(20,20,19,19,1)` 6-root configurations, the `1.67 -> 1.68` transition across $m_p^*$, and all Hampton–Jensen exceptional curves intersecting $C_{2v}$).

## Reproduce All Verifications

```bash
# 1. Lean 4.36.0 formal proof + axiom audit
cd lean && lake exe cache get && lake build Spatial5C2v

# 2. Rust pandsysroots v0.33.0 10-benchmark certification
cargo run --release

# 3. Independent 220-digit Cartesian 15-equation verification
python3 verify_200digits.py
```

## Paper & Verification Artifacts

- Paper PDF: [`paper/Spatial5_C2v_Central_Configurations.pdf`](paper/Spatial5_C2v_Central_Configurations.pdf)
- Pure 7-bit ASCII AMS LaTeX source: [`paper/Spatial5_C2v_Central_Configurations.tex`](paper/Spatial5_C2v_Central_Configurations.tex)
- Repository: <https://github.com/ivan-fr/spatial5-c2v-central-configurations>

## Author

Ivan Besevic (`ivan.besevic@edu.esiee-it.fr`), ESIEE-IT, France.

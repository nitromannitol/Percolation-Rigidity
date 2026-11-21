import Rigidity.Proofs.Regularity.ClusterQuadratic

/-!
# Polynomial comparison for quadratic functions on cluster balls

The excess over the affine functions of a quadratic function `a + ⟪p, x⟫ + q_M(x)` on the cluster
ball `C ∩ B_ρ(z)` is at most `d m ρ²` (`ballExcess_clusterQuadratic_le`), `m` the largest entry of
the symmetric part of `M`. Under a lower bound `κ > 0` on the density of the cluster in triadic
cubes it is also at least `c m ρ²` for large `ρ` (`le_ballExcess_clusterQuadratic`): if the affine
approximation `ℓ` were too good, its slope would be at most `4 d m ρ / √δ` (by the cap density),
the second difference of `q_M - ℓ` at `z, z ± (ρ/8) e` (with `|q_M(e)| ≥ m`) is `2 (ρ/8)² q_M(e)`,
so `|q_M - ℓ| ≥ m ρ² / 128` at one of these points, hence `≥ m ρ² / 256` on the cluster points of a
triadic cube near it, which carry a fixed fraction of the ball. This gives `PolynomialComparison`
for the quadratic functions over the affine functions with degree `2`
(`polynomialComparison_clusterQuadratic`), the property of `Ā_1 ≤ Ā_2` used in the case `k = 1`
of Armstrong–Dario, Lemma 7.2 (arXiv:1609.09431v2), on cluster balls.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The cap fraction `κ / (120 √d)^d` of `clusterBallCapDensity_of_clusterCubeDensity`. -/
noncomputable def capFraction (d : ℕ) (κ : ℝ) : ℝ := κ / (5 * (24 * Real.sqrt d)) ^ d

/-- The slope constant `L = 3 d / 2 + 4 d / √δ`. -/
noncomputable def quadSlopeConst (d : ℕ) (δ : ℝ) : ℝ := 3 * d / 2 + 4 * d / Real.sqrt δ

/-- The locality `Λ = 768 L √d` of the cubes used for quadratic functions. -/
noncomputable def quadLocality (d : ℕ) (δ : ℝ) : ℝ := 768 * quadSlopeConst d δ * Real.sqrt d

/-- The fraction `κ / (5 Λ)^d` of a cluster ball carried by a cube of size about `ρ / Λ`. -/
noncomputable def quadFraction (d : ℕ) (κ δ : ℝ) : ℝ := κ / (5 * quadLocality d δ) ^ d

/-- The constant `min d (√(quadFraction) / 256)` of the lower bound. -/
noncomputable def quadLowerConst (d : ℕ) (κ δ : ℝ) : ℝ :=
  min d (Real.sqrt (quadFraction d κ δ) / 256)

/-- **Second difference**: one of `z₀`, `z₀ ± t e` carries `|F| ≥ t² m / 2` for
`F(y) = c + ⟪p, y - z₀⟫ + q_M(y - z₀)` when `|q_M(e)| ≥ m` and `‖e‖ ≤ 2`. -/
theorem exists_second_difference_point (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (p z₀ e : EuclideanSpace ℝ (Fin d)) {m t : ℝ} (ht : 0 < t) (he : ‖e‖ ≤ 2)
    (hqe : m ≤ |quadForm M e|) :
    ∃ y : EuclideanSpace ℝ (Fin d), ‖y - z₀‖ ≤ 2 * t ∧
      t ^ 2 * m / 2 ≤ |c + inner ℝ p (y - z₀) + quadForm M (y - z₀)| := by
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun y => c + inner ℝ p (y - z₀) + quadForm M (y - z₀)
    with hFdef
  have hq0 : quadForm M 0 = 0 := by simp [quadForm]
  have hF0 : F z₀ = c := by simp only [hFdef, sub_self, inner_zero_right, hq0]; ring
  have hF1 : F (z₀ + t • e) = c + t * inner ℝ p e + t ^ 2 * quadForm M e := by
    simp only [hFdef, add_sub_cancel_left, real_inner_smul_right, quadForm_smul]
  have hF2 : F (z₀ + (-t) • e) = c - t * inner ℝ p e + t ^ 2 * quadForm M e := by
    simp only [hFdef, add_sub_cancel_left, real_inner_smul_right, quadForm_smul, neg_sq]
    ring
  have hnorm : ∀ s : ℝ, |s| = t → ‖z₀ + s • e - z₀‖ ≤ 2 * t := by
    intro s hs
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hs, mul_comm]
    exact mul_le_mul_of_nonneg_right he ht.le
  show ∃ y, ‖y - z₀‖ ≤ 2 * t ∧ t ^ 2 * m / 2 ≤ |F y|
  by_cases h0 : t ^ 2 * m / 2 ≤ |F z₀|
  · exact ⟨z₀, by rw [sub_self, norm_zero]; positivity, h0⟩
  by_cases h1 : t ^ 2 * m / 2 ≤ |F (z₀ + t • e)|
  · exact ⟨z₀ + t • e, hnorm t (abs_of_pos ht), h1⟩
  refine ⟨z₀ + (-t) • e, hnorm (-t) (by rw [abs_neg, abs_of_pos ht]), ?_⟩
  push Not at h0 h1
  have hid : F (z₀ + t • e) + F (z₀ + (-t) • e) - 2 * F z₀ = 2 * t ^ 2 * quadForm M e := by
    rw [hF0, hF1, hF2]; ring
  have ht2 : (0 : ℝ) < 2 * t ^ 2 := by positivity
  have h3 : 2 * t ^ 2 * m ≤ |2 * t ^ 2 * quadForm M e| := by
    rw [abs_mul, abs_of_pos ht2]
    exact mul_le_mul_of_nonneg_left hqe ht2.le
  rw [← hid] at h3
  have h4 : |F (z₀ + t • e) + F (z₀ + (-t) • e) - 2 * F z₀| ≤
      |F (z₀ + t • e)| + |F (z₀ + (-t) • e)| + 2 * |F z₀| := by
    have h5 := abs_sub (F (z₀ + t • e) + F (z₀ + (-t) • e)) (2 * F z₀)
    have h6 := abs_add_le (F (z₀ + t • e)) (F (z₀ + (-t) • e))
    rw [abs_mul, abs_two] at h5
    linarith
  linarith

/-- The perturbation `⟪p, u⟫ + q_M(u) + polar(u, v)` of a quadratic function on a small cube. -/
theorem abs_affine_quad_perturb_le (M : Matrix (Fin d) (Fin d) ℝ) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ i j, |symEntry M i j| ≤ m) (p u v : EuclideanSpace ℝ (Fin d)) {S r s : ℝ}
    (hS : ‖p‖ ≤ S) (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ s) :
    |inner ℝ p u + quadForm M u + quadPolar M u v| ≤ S * r + d * m * r ^ 2 + 2 * d * m * r * s := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hu
  have hS0 : 0 ≤ S := (norm_nonneg _).trans hS
  have hdm : 0 ≤ (d : ℝ) * m := by positivity
  have b1 : |inner ℝ p u| ≤ S * r :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hS hu (norm_nonneg _) hS0)
  have b2 : |quadForm M u| ≤ d * m * r ^ 2 := by
    refine (abs_quadForm_le M hm0 hm u).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu 2) hdm
  have b3 : |quadPolar M u v| ≤ 2 * d * m * r * s := by
    refine (abs_quadPolar_le M hm0 hm u v).trans ?_
    have h2 : 0 ≤ 2 * (d : ℝ) * m := by positivity
    calc 2 * d * m * ‖u‖ * ‖v‖ = (2 * d * m) * (‖u‖ * ‖v‖) := by ring
      _ ≤ (2 * d * m) * (r * s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hu hv (norm_nonneg _) hr0) h2
      _ = 2 * d * m * r * s := by ring
  calc |inner ℝ p u + quadForm M u + quadPolar M u v|
      ≤ |inner ℝ p u + quadForm M u| + |quadPolar M u v| := abs_add_le _ _
    _ ≤ |inner ℝ p u| + |quadForm M u| + |quadPolar M u v| := by
        linarith [abs_add_le (inner ℝ p u) (quadForm M u)]
    _ ≤ _ := by linarith

/-- A subset of the cluster ball of radius `ρ ≥ 1` carrying `κ 3^{d m'}` points with
`ρ ≤ Λ 3^{m'}` and `|g| ≥ μ` on it gives `‖g‖ ≥ √(κ / (5 Λ)^d) μ`. -/
theorem le_componentBallL2_of_cube_count (C : OpenComponent ω) (z : Vertex d) {ρ κ μ Λ : ℝ}
    {m' : ℕ} (hκ : 0 < κ) (hρ1 : 1 ≤ ρ) (hΛ0 : 0 < Λ) (hρΛ : ρ ≤ Λ * 3 ^ m') (hμ : 0 ≤ μ)
    {g : C → ℝ} {S : Finset C} (hS : S ⊆ componentEuclideanBall C z ρ)
    (hSg : ∀ x ∈ S, μ ≤ |g x|) (hcount : κ * 3 ^ (d * m') ≤ S.card) :
    Real.sqrt (κ / (5 * Λ) ^ d) * μ ≤ componentBallL2 C z ρ g := by
  have hρ0 : 0 < ρ := by linarith
  have hball : κ / (5 * Λ) ^ d * ((componentEuclideanBall C z ρ).card : ℝ) ≤ κ * 3 ^ (d * m') := by
    have h1 : ((componentEuclideanBall C z ρ).card : ℝ) ≤ (5 * ρ) ^ d :=
      (card_componentEuclideanBall_le C z hρ0.le).trans
        (pow_le_pow_left₀ (by linarith) (by linarith) d)
    have h2 : κ / (5 * Λ) ^ d * (5 * ρ) ^ d = κ * (ρ / Λ) ^ d := by
      rw [div_mul_eq_mul_div, mul_div_assoc, ← div_pow]
      congr 2
      field_simp
    have h3 : (ρ / Λ) ^ d ≤ (3 : ℝ) ^ (d * m') := by
      rw [show d * m' = m' * d from mul_comm d m', pow_mul]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ hΛ0]; linarith
    calc κ / (5 * Λ) ^ d * ((componentEuclideanBall C z ρ).card : ℝ)
        ≤ κ / (5 * Λ) ^ d * (5 * ρ) ^ d := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = κ * (ρ / Λ) ^ d := h2
      _ ≤ κ * 3 ^ (d * m') := mul_le_mul_of_nonneg_left h3 hκ.le
  have hcardpos : 0 < (componentEuclideanBall C z ρ).card := by
    have h1 : (0 : ℝ) < κ * 3 ^ (d * m') := by positivity
    have h2 := h1.trans_le (hcount.trans (Nat.cast_le.2 (Finset.card_le_card hS)))
    exact_mod_cast h2
  exact le_componentBallL2_of_subset C z ρ hμ (by positivity) hcardpos hS hSg (hball.trans hcount)

/-- **The small-slope case.** If `g = c + ⟪p, x - z⟫ + q_M(x - z)` on the cluster with
`‖p‖ ≤ 4 d m ρ / √δ`, `|q_M(e)| ≥ m`, `‖e‖ ≤ 2`, then the cube density at the locality
`768 L √d`, `L = 3d/2 + 4d/√δ`, gives `‖g‖_{L̲²(C ∩ B_ρ(z))} ≥ √(κ / (5 Λ)^d) (ρ/8)² m / 4`. -/
theorem le_componentBallL2_quadratic_of_slope (C : OpenComponent ω) (z : Vertex d)
    {ℓ κ δ ρ L : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hδ : 0 < δ)
    (hL : 3 * d / 2 + 4 * d / Real.sqrt δ = L)
    (hcube : ClusterCubeDensity C z (768 * L * Real.sqrt d) ℓ κ)
    (hρ : 768 * L * Real.sqrt d * max ℓ 1 ≤ ρ)
    {c : ℝ} {p'' : EuclideanSpace ℝ (Fin d)} {M : Matrix (Fin d) (Fin d) ℝ} {m : ℝ}
    (hm0 : 0 ≤ m) (hm : ∀ i j, |symEntry M i j| ≤ m) {e : EuclideanSpace ℝ (Fin d)}
    (he : ‖e‖ ≤ 2) (hqe : m ≤ |quadForm M e|) {g : C → ℝ}
    (hrep : ∀ x : C, g x =
      c + inner ℝ p'' (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z) +
        quadForm M (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z))
    (hslope : ‖p''‖ ≤ 4 * d * m * ρ / Real.sqrt δ) :
    Real.sqrt (κ / (5 * (768 * L * Real.sqrt d)) ^ d) * ((ρ / 8) ^ 2 * m / 4) ≤
      componentBallL2 C z ρ g := by
  classical
  set z₀ := latticeEuclideanEmbedding z with hz₀
  set Λ := 768 * L * Real.sqrt d with hΛ
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hLd : (d : ℝ) ≤ L := by
    rw [← hL]; have : 0 ≤ 4 * (d : ℝ) / Real.sqrt δ := by positivity
    linarith
  have hL1 : 1 ≤ L := hd1.trans hLd
  have hL0 : 0 < L := by linarith
  have hLs : 1 ≤ L * Real.sqrt d := one_le_mul_of_one_le_of_one_le hL1 hsd1
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  have hmax1 : 1 ≤ max ℓ 1 := le_max_right _ _
  have hρΛ : Λ ≤ ρ := le_trans (le_mul_of_one_le_right hΛ0.le hmax1) hρ
  have hρ1 : 1 ≤ ρ := by rw [hΛ] at hρΛ; linarith
  have hρ0 : 0 < ρ := by linarith
  -- the second difference at `z`, `z ± t e`
  set t := ρ / 8 with ht
  have ht0 : 0 < t := by positivity
  obtain ⟨y, hyz, hFy⟩ := exists_second_difference_point M c p'' z₀ e ht0 he hqe
  -- the cube near `y`
  have hx : 1 ≤ ρ / (256 * L * Real.sqrt d) := by
    rw [le_div_iff₀ (by positivity)]
    have : 768 * L * Real.sqrt d ≤ ρ := hρΛ
    have : 0 < L * Real.sqrt d := by positivity
    linarith
  obtain ⟨m', hm1, hm2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3)
  have h3pos : (0 : ℝ) < 3 ^ m' := by positivity
  have h3a : Real.sqrt d * 3 ^ m' ≤ ρ / (256 * L) := by
    rw [le_div_iff₀ (by positivity)] at hm1
    rw [le_div_iff₀ (by positivity)]
    calc Real.sqrt d * 3 ^ m' * (256 * L) = 3 ^ m' * (256 * L * Real.sqrt d) := by ring
      _ ≤ ρ := hm1
  have h3b : ρ ≤ Λ * 3 ^ m' := by
    rw [pow_succ, div_lt_iff₀ (by positivity)] at hm2
    calc ρ ≤ 3 ^ m' * 3 * (256 * L * Real.sqrt d) := hm2.le
      _ = 768 * L * Real.sqrt d * 3 ^ m' := by ring
  have hℓ : ℓ ≤ 3 ^ m' := by
    have h1 : Λ * max ℓ 1 ≤ Λ * 3 ^ m' := hρ.trans h3b
    exact (le_max_left _ _).trans (le_of_mul_le_mul_left h1 hΛ0)
  have hr1 : Real.sqrt d * 3 ^ m' ≤ ρ / 256 := by
    refine h3a.trans (div_le_div_of_nonneg_left hρ0.le (by norm_num) ?_)
    linarith
  have hwc : dist y z₀ + Real.sqrt d * 3 ^ m' < ρ := by
    rw [dist_eq_norm]; linarith
  set r := Real.sqrt d * 3 ^ m' with hr
  have hr0 : 0 ≤ r := by positivity
  have hrρ : r ≤ ρ := hr1.trans (by linarith)
  -- the size of the perturbation on the cube
  have htot : 4 * d * m * ρ / Real.sqrt δ * r + d * m * r ^ 2 + 2 * d * m * r * (2 * t) ≤
      t ^ 2 * m / 4 := by
    have e1 : 4 * d * m * ρ / Real.sqrt δ * r + d * m * r ^ 2 + 2 * d * m * r * (2 * t) =
        m * r * (4 * d / Real.sqrt δ * ρ + d * r + d * ρ / 2) := by rw [ht]; ring
    have h1 : m * r * (4 * d / Real.sqrt δ * ρ + d * r + d * ρ / 2) ≤
        m * r * (4 * d / Real.sqrt δ * ρ + d * ρ + d * ρ / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_left hrρ (Nat.cast_nonneg (α := ℝ) d)
      linarith
    have e2 : m * r * (4 * d / Real.sqrt δ * ρ + d * ρ + d * ρ / 2) = m * ρ * L * r := by
      rw [← hL]; ring
    have h2 : m * ρ * L * r ≤ m * ρ * L * (ρ / (256 * L)) :=
      mul_le_mul_of_nonneg_left h3a (by positivity)
    have e3 : m * ρ * L * (ρ / (256 * L)) = t ^ 2 * m / 4 := by
      rw [ht]; field_simp; ring
    rw [e1]; linarith
  have hP : ∀ x : C, dist (latticeEuclideanEmbedding x.val) y ≤ r →
      t ^ 2 * m / 4 ≤ |g x| := by
    intro x hxy
    rw [dist_eq_norm] at hxy
    have huv : latticeEuclideanEmbedding x.val - z₀ =
        (latticeEuclideanEmbedding x.val - y) + (y - z₀) := by abel
    have hdiff : g x - (c + inner ℝ p'' (y - z₀) + quadForm M (y - z₀)) =
        inner ℝ p'' (latticeEuclideanEmbedding x.val - y) +
          quadForm M (latticeEuclideanEmbedding x.val - y) +
          quadPolar M (latticeEuclideanEmbedding x.val - y) (y - z₀) := by
      rw [hrep x, huv, quadForm_add, inner_add_right]
      ring
    have hb := abs_affine_quad_perturb_le M hm0 hm p'' (latticeEuclideanEmbedding x.val - y)
      (y - z₀) hslope hxy hyz
    rw [← hdiff] at hb
    have := abs_sub_abs_le_abs_sub (c + inner ℝ p'' (y - z₀) + quadForm M (y - z₀)) (g x)
    rw [abs_sub_comm] at this
    linarith
  have hcount := le_card_filter_of_clusterCubeDensity C z hcube hℓ hwc h3b
    (fun x => t ^ 2 * m / 4 ≤ |g x|) hP
  have hlow := le_componentBallL2_of_cube_count C z hκ hρ1 hΛ0 h3b (by positivity)
    (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.1 hx).2) hcount
  rw [ht] at hlow
  exact hlow

/-- **Lower bound for the excess of a quadratic function over the affine functions** on cluster
balls, from the density of the cluster in cubes. -/
theorem le_ballExcess_clusterQuadratic (C : OpenComponent ω) (z : Vertex d) {ℓ κ ρ : ℝ}
    (hd : 0 < d) (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C z (quadLocality d (capFraction d κ)) ℓ κ)
    (hρ : quadLocality d (capFraction d κ) * max ℓ 1 ≤ ρ)
    {w : C → ℝ} {a : ℝ} {p : EuclideanSpace ℝ (Fin d)} {M : Matrix (Fin d) (Fin d) ℝ}
    (hw : ∀ x, w x = a + inner ℝ p (latticeEuclideanEmbedding x.val) +
      quadForm M (latticeEuclideanEmbedding x.val))
    {m : ℝ} (hm : ∀ i j, |symEntry M i j| ≤ m) {i₀ j₀ : Fin d}
    (hm₀ : |symEntry M i₀ j₀| = m) :
    quadLowerConst d κ (capFraction d κ) * m * ρ ^ 2 ≤
      ballExcess (componentBallSeminorm C z) (clusterAffine C) ρ w := by
  classical
  set δ := capFraction d κ with hδdef
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
  have hδ : 0 < δ := by rw [hδdef, capFraction]; positivity
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  set L := quadSlopeConst d δ with hLdef
  have hL : 3 * d / 2 + 4 * d / Real.sqrt δ = L := by rw [hLdef, quadSlopeConst]
  have hL0 : 0 < L := by rw [← hL]; positivity
  have hLd : (d : ℝ) ≤ L := by
    rw [← hL]; have : 0 ≤ 4 * (d : ℝ) / Real.sqrt δ := by positivity
    linarith
  set Λ := quadLocality d δ with hΛdef
  have hΛ : Λ = 768 * L * Real.sqrt d := by rw [hΛdef, quadLocality]
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  have hΛ24 : 24 * Real.sqrt d ≤ Λ := by rw [hΛ]; nlinarith
  have hmax1 : 1 ≤ max ℓ 1 := le_max_right _ _
  have hρΛ : Λ ≤ ρ := le_trans (le_mul_of_one_le_right hΛ0.le hmax1) hρ
  have hρ0 : 0 < ρ := hΛ0.trans_le hρΛ
  have hm0 : 0 ≤ m := hm₀ ▸ abs_nonneg _
  -- the cap density at the radius `ρ`
  have hcap := clusterBallCapDensity_of_clusterCubeDensity C z ρ hd hκ (hcube.of_le C z hΛ24)
  have hcapρ : 24 * Real.sqrt d * max ℓ 1 ≤ ρ :=
    le_trans (mul_le_mul_of_nonneg_right hΛ24 (by linarith)) hρ
  set z₀ := latticeEuclideanEmbedding z with hz₀
  apply le_ballExcess
  rintro g ⟨b, p', hg⟩
  rw [componentBallSeminorm_apply]
  -- the representation `w - g = c + ⟪p'', x - z⟫ + q_M(x - z)`
  set c := a - b + inner ℝ (p - p') z₀ + quadForm M z₀ with hc
  set p'' := p - p' + polarVec M z₀ with hp''
  have hrep : ∀ x : C, (w - g) x = c + inner ℝ p'' (latticeEuclideanEmbedding x.val - z₀) +
      quadForm M (latticeEuclideanEmbedding x.val - z₀) := by
    intro x
    rw [Pi.sub_apply, hw, hg, quadForm_eq_sub M _ z₀, hc, hp'']
    simp only [inner_add_left, inner_sub_left, inner_sub_right]
    rw [real_inner_comm (polarVec M z₀) (latticeEuclideanEmbedding x.val),
      real_inner_comm (polarVec M z₀) z₀]
    ring
  set A : C → ℝ := fun x => c + inner ℝ p'' (latticeEuclideanEmbedding x.val - z₀) with hA
  set Qf : C → ℝ := fun x => quadForm M (latticeEuclideanEmbedding x.val - z₀) with hQf
  have hsplit : w - g = A + Qf := funext fun x => by rw [hrep]; rfl
  have hQ : componentBallL2 C z ρ Qf ≤ d * m * ρ ^ 2 := by
    apply componentBallL2_le_of_abs_le C z ρ (by positivity)
    intro x hx
    rw [mem_componentEuclideanBall, dist_eq_norm] at hx
    refine (abs_quadForm_le M hm0 hm _).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hx.le 2
    have h0 : 0 ≤ (d : ℝ) * m := by positivity
    nlinarith
  have hc₂d : quadLowerConst d κ δ ≤ d := min_le_left _ _
  have hc₂f : quadLowerConst d κ δ ≤ Real.sqrt (quadFraction d κ δ) / 256 := min_le_right _ _
  have hρ2 : 0 ≤ m * ρ ^ 2 := by positivity
  by_cases hbig : 2 * (d * m * ρ ^ 2) < componentBallL2 C z ρ A
  · -- the affine part is large
    have htri : componentBallL2 C z ρ A ≤ componentBallL2 C z ρ (w - g) +
        componentBallL2 C z ρ Qf := by
      have := map_sub_le_add (componentBallSeminorm C z ρ) (w - g) Qf
      rw [hsplit, add_sub_cancel_right] at this
      simpa only [componentBallSeminorm_apply, ← hsplit] using this
    have : (d : ℝ) * m * ρ ^ 2 ≤ componentBallL2 C z ρ (w - g) := by linarith
    calc quadLowerConst d κ δ * m * ρ ^ 2 = quadLowerConst d κ δ * (m * ρ ^ 2) := by ring
      _ ≤ d * (m * ρ ^ 2) := mul_le_mul_of_nonneg_right hc₂d hρ2
      _ = d * m * ρ ^ 2 := by ring
      _ ≤ _ := this
  push Not at hbig
  -- the slope of the affine part is controlled
  have haff : Real.sqrt δ * ((|c| + ‖p''‖ * ρ) / 2) ≤ componentBallL2 C z ρ A :=
    le_componentBallL2_affine C z hδ hcap hcapρ le_rfl hρ0 c p''
  have hslope : ‖p''‖ ≤ 4 * d * m * ρ / Real.sqrt δ := by
    have h1 : Real.sqrt δ * (‖p''‖ * ρ) ≤ 4 * (d * m * ρ ^ 2) := by
      have := abs_nonneg c
      have h2 : Real.sqrt δ * (‖p''‖ * ρ) ≤ 2 * (Real.sqrt δ * ((|c| + ‖p''‖ * ρ) / 2)) := by
        have := mul_nonneg hsδ.le this
        nlinarith
      linarith
    rw [le_div_iff₀ hsδ]
    have h3 : ‖p''‖ * Real.sqrt δ * ρ ≤ 4 * d * m * ρ * ρ := by nlinarith
    exact le_of_mul_le_mul_right h3 hρ0
  obtain ⟨e, he, hqe⟩ := exists_le_abs_quadForm M i₀ j₀
  rw [hm₀] at hqe
  have hlow := le_componentBallL2_quadratic_of_slope C z hd hκ hδ hL hcube hρ
    hm0 hm he hqe (g := w - g) hrep hslope
  have hfrac : κ / (5 * (768 * L * Real.sqrt d)) ^ d = quadFraction d κ δ := by
    rw [quadFraction, ← hΛ, ← hΛdef]
  rw [hfrac] at hlow
  calc quadLowerConst d κ δ * m * ρ ^ 2 = quadLowerConst d κ δ * (m * ρ ^ 2) := by ring
    _ ≤ Real.sqrt (quadFraction d κ δ) / 256 * (m * ρ ^ 2) :=
        mul_le_mul_of_nonneg_right hc₂f hρ2
    _ = Real.sqrt (quadFraction d κ δ) * ((ρ / 8) ^ 2 * m / 4) := by ring
    _ ≤ _ := hlow

end Rigidity.Proofs.Regularity

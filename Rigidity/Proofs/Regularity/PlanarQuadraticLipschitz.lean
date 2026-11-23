import Rigidity.Proofs.Regularity.PlanarCoarseTransfer
import Rigidity.Proofs.Regularity.LatticeHarmonicCubic

/-!
# The slope of a quadratic polynomial on the balls of a planar cluster

For `W(y) = a + ⟪p, y⟫ + q_M(y)` on `ℤ²` and `|xᵢ|, |yᵢ| ≤ ρ`,
`|W(y) - W(x)| ≤ Λ (|y₀ - x₀| + |y₁ - x₁|)` with
`Λ = |p₀| + |p₁| + 2 (|M₀₀| + |M₀₁ + M₁₀| + |M₁₁|) ρ` (`abs_quadratic_sub_le`). Under the density
of the cluster in cubes, the cluster ball of radius `R` controls these coefficients:
`(|p₀| + |p₁|) R + (|M₀₀| + |M₀₁ + M₁₀| + |M₁₁|) R² ≤ C ‖W - c‖_{L̲²(C ∩ B_R)}` for every constant
`c` (`coeff_le_componentBallL2_sub_const`), the bound (7.23) of the proof of Lemma 7.3 of Armstrong
and Dario (arXiv:1609.09431v2) for the harmonic quadratic polynomials. The cluster balls carry at
least `κ R² / 72` points (`le_card_componentEuclideanBall`), so that `‖·‖_{L̲²(C ∩ B_R)}` is at
most `√72 / √κ` times `R^{-1} ‖·‖_{ℓ²(C ∩ B_R)}`.

The lattice harmonic quadratic functions restrict to the harmonic quadratic polynomials of the
cluster (`mem_clusterHarmonicQuadratic_of_mem_latticeHarmonicQuadratic`), and the harmonic quadratic
polynomials of the cluster extend to lattice harmonic quadratic functions
(`mem_latticeHarmonicQuadratic_of_trace_eq_zero`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {ω : Configuration 2}

/-- The quadratic polynomial `a + ⟪p, y⟫ + q_M(y)` on `ℤ²`. -/
noncomputable def latticeQuadFun (a : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    (M : Matrix (Fin 2) (Fin 2) ℝ) (y : Vertex 2) : ℝ :=
  a + inner ℝ p (latticeEuclideanEmbedding y) + quadForm M (latticeEuclideanEmbedding y)

theorem latticeQuadFun_eq (a : ℝ) (p : EuclideanSpace ℝ (Fin 2)) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (y : Vertex 2) :
    latticeQuadFun a p M y = a + p 0 * y 0 + p 1 * y 1 + M 0 0 * y 0 ^ 2 +
      (M 0 1 + M 1 0) * y 0 * y 1 + M 1 1 * y 1 ^ 2 := by
  rw [latticeQuadFun, inner_latticeEuclideanEmbedding_two, quadForm_latticeEuclideanEmbedding_two]
  ring

theorem latticeLaplacian_latticeQuadFun (a : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    (M : Matrix (Fin 2) (Fin 2) ℝ) (y : Vertex 2) :
    latticeLaplacian (latticeQuadFun a p M) y = 2 * M.trace := by
  have h : ∀ y : Vertex 2, latticeQuadFun a p M y = a + p 0 * y 0 + p 1 * y 1 + M 0 0 * y 0 ^ 2 +
      (M 0 1 + M 1 0) * y 0 * y 1 + M 1 1 * y 1 ^ 2 + 0 * y 0 ^ 3 + 0 * y 0 ^ 2 * y 1 +
      0 * y 0 * y 1 ^ 2 + 0 * y 1 ^ 3 := fun y => by rw [latticeQuadFun_eq]; ring
  rw [latticeLaplacian_eq_of_cubic h, Matrix.trace_fin_two]
  ring

/-- A harmonic quadratic polynomial of the cluster extends to a lattice harmonic quadratic
function. -/
theorem mem_latticeHarmonicQuadratic_of_trace_eq_zero (a : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.trace = 0) :
    (fun x : latticeComponent 2 => latticeQuadFun a p M x.val) ∈ latticeHarmonicQuadratic 2 :=
  ⟨⟨a, p, M, fun _ => rfl⟩, fun y => by
    show latticeLaplacian (latticeQuadFun a p M) y = 0
    rw [latticeLaplacian_latticeQuadFun, hM, mul_zero]⟩

/-- A lattice harmonic quadratic function restricts to a harmonic quadratic polynomial of the
cluster. -/
theorem mem_clusterHarmonicQuadratic_of_mem_latticeHarmonicQuadratic (C : OpenComponent ω)
    {w : latticeComponent 2 → ℝ} (hw : w ∈ latticeHarmonicQuadratic 2) :
    ∃ (a : ℝ) (p : EuclideanSpace ℝ (Fin 2)) (M : Matrix (Fin 2) (Fin 2) ℝ),
      (∀ x, w x = latticeQuadFun a p M x.val) ∧
      (fun x : C => latticeQuadFun a p M x.val) ∈ clusterHarmonicQuadratic C := by
  obtain ⟨⟨a, p, M, hw'⟩, hΔ⟩ := hw
  have hext : latticeExt w = latticeQuadFun a p M := by
    funext y; exact hw' _
  have htr : M.trace = 0 := by
    have := hΔ 0
    rw [hext, latticeLaplacian_latticeQuadFun] at this
    linarith
  exact ⟨a, p, M, fun x => hw' x, ⟨a, p, M, htr, fun _ => rfl⟩⟩

/-- **The slope of a quadratic polynomial on a box.** -/
theorem abs_quadratic_sub_le (a : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    (M : Matrix (Fin 2) (Fin 2) ℝ) {ρ : ℝ} {x y : Vertex 2}
    (hx : ∀ i, |(x i : ℝ)| ≤ ρ) (hy : ∀ i, |(y i : ℝ)| ≤ ρ) :
    |latticeQuadFun a p M y - latticeQuadFun a p M x| ≤
      (|p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * ρ) *
        (|((y 0 - x 0 : ℤ) : ℝ)| + |((y 1 - x 1 : ℤ) : ℝ)|) := by
  rw [latticeQuadFun_eq, latticeQuadFun_eq]
  set x₀ : ℝ := (x 0 : ℝ)
  set x₁ : ℝ := (x 1 : ℝ)
  set y₀ : ℝ := (y 0 : ℝ)
  set y₁ : ℝ := (y 1 : ℝ)
  have h0 : ((y 0 - x 0 : ℤ) : ℝ) = y₀ - x₀ := by push_cast; ring
  have h1 : ((y 1 - x 1 : ℤ) : ℝ) = y₁ - x₁ := by push_cast; ring
  rw [h0, h1]
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hx 0)
  have e : (a + p 0 * y₀ + p 1 * y₁ + M 0 0 * y₀ ^ 2 + (M 0 1 + M 1 0) * y₀ * y₁ + M 1 1 * y₁ ^ 2) -
      (a + p 0 * x₀ + p 1 * x₁ + M 0 0 * x₀ ^ 2 + (M 0 1 + M 1 0) * x₀ * x₁ + M 1 1 * x₁ ^ 2) =
      (p 0 + M 0 0 * (y₀ + x₀) + (M 0 1 + M 1 0) * y₁) * (y₀ - x₀) +
        (p 1 + M 1 1 * (y₁ + x₁) + (M 0 1 + M 1 0) * x₀) * (y₁ - x₁) := by ring
  rw [e]
  have hx0 := hx 0
  have hx1 := hx 1
  have hy0 := hy 0
  have hy1 := hy 1
  have hA : |p 0 + M 0 0 * (y₀ + x₀) + (M 0 1 + M 1 0) * y₁| ≤
      |p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * ρ := by
    have h1 : |M 0 0 * (y₀ + x₀)| ≤ |M 0 0| * (2 * ρ) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left
        ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)
    have h2 : |(M 0 1 + M 1 0) * y₁| ≤ |M 0 1 + M 1 0| * ρ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy1 (abs_nonneg _)
    have h3 := abs_add_le (p 0 + M 0 0 * (y₀ + x₀)) ((M 0 1 + M 1 0) * y₁)
    have h4 := abs_add_le (p 0) (M 0 0 * (y₀ + x₀))
    have := abs_nonneg (p 1)
    have := abs_nonneg (M 1 1)
    have := abs_nonneg (M 0 1 + M 1 0)
    nlinarith
  have hB : |p 1 + M 1 1 * (y₁ + x₁) + (M 0 1 + M 1 0) * x₀| ≤
      |p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * ρ := by
    have h1 : |M 1 1 * (y₁ + x₁)| ≤ |M 1 1| * (2 * ρ) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left
        ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)
    have h2 : |(M 0 1 + M 1 0) * x₀| ≤ |M 0 1 + M 1 0| * ρ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx0 (abs_nonneg _)
    have h3 := abs_add_le (p 1 + M 1 1 * (y₁ + x₁)) ((M 0 1 + M 1 0) * x₀)
    have h4 := abs_add_le (p 1) (M 1 1 * (y₁ + x₁))
    have := abs_nonneg (p 0)
    have := abs_nonneg (M 0 0)
    have := abs_nonneg (M 0 1 + M 1 0)
    nlinarith
  calc |(p 0 + M 0 0 * (y₀ + x₀) + (M 0 1 + M 1 0) * y₁) * (y₀ - x₀) +
        (p 1 + M 1 1 * (y₁ + x₁) + (M 0 1 + M 1 0) * x₀) * (y₁ - x₁)|
      ≤ |p 0 + M 0 0 * (y₀ + x₀) + (M 0 1 + M 1 0) * y₁| * |y₀ - x₀| +
          |p 1 + M 1 1 * (y₁ + x₁) + (M 0 1 + M 1 0) * x₀| * |y₁ - x₁| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_right hA (abs_nonneg (y₀ - x₀)),
          mul_le_mul_of_nonneg_right hB (abs_nonneg (y₁ - x₁))]

/-- **Cluster balls carry a fixed fraction of the points of the disc.** -/
theorem le_card_componentEuclideanBall (C : OpenComponent ω) {ℓ κ R : ℝ} (hκ : 0 ≤ κ)
    (hcube : ClusterCubeDensity C 0 (24 * Real.sqrt ((2 : ℕ) : ℝ)) ℓ κ)
    (hR : 6 * Real.sqrt ((2 : ℕ) : ℝ) * max ℓ 1 ≤ R) :
    κ * R ^ 2 / 72 ≤ ((componentEuclideanBall C 0 R).card : ℝ) := by
  classical
  have hs2 : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
  have hR' : 6 * Real.sqrt 2 * max ℓ 1 ≤ R := by rw [← hs2]; exact hR
  have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hmax : 1 ≤ max ℓ 1 := le_max_right _ _
  have hR0 : 0 < R := by nlinarith [hR', hsq, hmax]
  have hx : 1 ≤ R / (2 * Real.sqrt 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [hR']
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3)
  have h3n : (0 : ℝ) < 3 ^ n := by positivity
  have hn3 : R / (6 * Real.sqrt 2) < 3 ^ n := by
    rw [pow_succ] at hn2
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn2
    nlinarith
  have hℓ : ℓ ≤ 3 ^ n := by
    have : ℓ ≤ R / (6 * Real.sqrt 2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [le_max_left ℓ 1, hR']
    linarith
  have hw : dist (latticeEuclideanEmbedding (0 : Vertex 2)) (latticeEuclideanEmbedding 0) +
      Real.sqrt ((2 : ℕ) : ℝ) * 3 ^ n < R := by
    rw [dist_self, zero_add, hs2]
    rw [le_div_iff₀ (by positivity)] at hn1
    nlinarith
  have hρR : R ≤ 24 * Real.sqrt ((2 : ℕ) : ℝ) * 3 ^ n := by
    rw [hs2]
    rw [div_lt_iff₀ (by positivity)] at hn3
    nlinarith
  have h := le_card_filter_of_clusterCubeDensity C 0 hcube hℓ hw hρR
    (fun _ => True) (fun _ _ => trivial)
  rw [Finset.filter_true] at h
  have h9 : (R / (6 * Real.sqrt 2)) ^ 2 ≤ ((3 : ℝ) ^ n) ^ 2 :=
    pow_le_pow_left₀ (div_pos hR0 (by positivity)).le hn3.le 2
  have e : (R / (6 * Real.sqrt 2)) ^ 2 = R ^ 2 / 72 := by
    rw [div_pow, mul_pow, hsq2]; ring
  rw [e] at h9
  have e2 : ((3 : ℝ) ^ n) ^ 2 = 3 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  rw [e2] at h9
  have e3 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  calc κ * R ^ 2 / 72 = κ * (R ^ 2 / 72) := by ring
    _ ≤ κ * 3 ^ (2 * n) := mul_le_mul_of_nonneg_left h9 hκ
    _ ≤ _ := h

/-- **The coefficients of a harmonic quadratic polynomial are bounded by its oscillation on the
cluster ball.** -/
theorem coeff_le_componentBallL2_sub_const (C : OpenComponent ω) {ℓ κ X R' ρ : ℝ}
    (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C 0 (quadLocality 2 (capFraction 2 κ)) ℓ κ)
    (hρq : quadLocality 2 (capFraction 2 κ) * max ℓ 1 ≤ ρ)
    (hcap : ClusterBallCapDensity C 0 X R' (capFraction 2 κ)) (hXρ : X ≤ ρ) (hρR : ρ ≤ R')
    (hρ0 : 0 < ρ) (a : ℝ) (p : EuclideanSpace ℝ (Fin 2)) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) :
    (|p 0| + |p 1|) * ρ + (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * ρ ^ 2 ≤
      (4 / Real.sqrt (capFraction 2 κ) * (1 + 4 / quadLowerConst 2 κ (capFraction 2 κ)) +
          4 / quadLowerConst 2 κ (capFraction 2 κ)) *
        componentBallL2 C 0 ρ (fun x => latticeQuadFun a p M x.val - c) := by
  classical
  have hδ : 0 < capFraction 2 κ := capFraction_pos (by norm_num) hκ
  have hq : 0 < quadLowerConst 2 κ (capFraction 2 κ) := quadLowerConst_pos (by norm_num) hκ hδ
  set N := componentBallL2 C 0 ρ (fun x => latticeQuadFun a p M x.val - c) with hN
  have hN0 : 0 ≤ N := componentBallL2_nonneg _ _ _ _
  -- the quadratic part
  have hne : (Finset.univ : Finset (Fin 2 × Fin 2)).Nonempty := ⟨(0, 0), Finset.mem_univ _⟩
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun ij : Fin 2 × Fin 2 => |symEntry M ij.1 ij.2|) hne
  set m := |symEntry M i₀ j₀| with hmdef
  have hm : ∀ i j, |symEntry M i j| ≤ m := fun i j => hmax (i, j) (Finset.mem_univ _)
  have hexcess := le_ballExcess_clusterQuadratic C 0 (by norm_num) hκ hcube hρq
    (w := fun x => latticeQuadFun a p M x.val - c) (a := a - c) (p := p) (M := M)
    (fun x => by rw [latticeQuadFun]; ring) hm hmdef.symm
  have hexN : ballExcess (componentBallSeminorm C 0) (clusterAffine C) ρ
      (fun x => latticeQuadFun a p M x.val - c) ≤ N := by
    have := ballExcess_le (componentBallSeminorm C 0) (clusterAffine C) (s := ρ)
      (u := fun x => latticeQuadFun a p M x.val - c) (clusterAffine C).zero_mem
    rw [sub_zero, componentBallSeminorm_apply] at this
    exact this
  have hmN : m * ρ ^ 2 ≤ N / quadLowerConst 2 κ (capFraction 2 κ) := by
    rw [le_div_iff₀ hq]; nlinarith [hexcess.trans hexN]
  have hsym : |M 0 0| + |M 0 1 + M 1 0| + |M 1 1| ≤ 4 * m := by
    have h00 := hm 0 0
    have h01 := hm 0 1
    have h11 := hm 1 1
    simp only [symEntry] at h00 h01 h11
    have e1 : |(M 0 0 + M 0 0) / 2| = |M 0 0| := by
      rw [show (M 0 0 + M 0 0) / 2 = M 0 0 by ring]
    have e2 : |(M 0 1 + M 1 0) / 2| = |M 0 1 + M 1 0| / 2 := by
      rw [abs_div, abs_two]
    have e3 : |(M 1 1 + M 1 1) / 2| = |M 1 1| := by
      rw [show (M 1 1 + M 1 1) / 2 = M 1 1 by ring]
    rw [e1] at h00; rw [e2] at h01; rw [e3] at h11
    linarith
  -- the affine part
  have haff := le_componentBallL2_affine C 0 hδ hcap hXρ hρR hρ0 (a - c) p
  simp only [latticeEuclideanEmbedding_zero, sub_zero] at haff
  have hquad_sup : componentBallL2 C 0 ρ (fun x => quadForm M (latticeEuclideanEmbedding x.val))
      ≤ 4 * m * ρ ^ 2 := by
    apply componentBallL2_le_of_abs_le _ _ _ (by positivity)
    intro x hx
    rw [quadForm_latticeEuclideanEmbedding_two]
    have hd := (mem_componentEuclideanBall _ _ _ _).1 hx
    have hc0 := (abs_sub_le_dist_latticeEuclideanEmbedding x.val 0 0).trans hd.le
    have hc1 := (abs_sub_le_dist_latticeEuclideanEmbedding x.val 0 1).trans hd.le
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at hc0 hc1
    have hp0 : |(x.val 0 : ℝ)| ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc0 2
    have hp1 : |(x.val 1 : ℝ)| ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc1 2
    have hp01 : |(x.val 0 : ℝ)| * |(x.val 1 : ℝ)| ≤ ρ ^ 2 := by
      nlinarith [abs_nonneg ((x.val 0 : ℝ)), abs_nonneg ((x.val 1 : ℝ))]
    calc |M 0 0 * (x.val 0 : ℝ) ^ 2 + (M 0 1 + M 1 0) * x.val 0 * x.val 1 +
          M 1 1 * (x.val 1 : ℝ) ^ 2|
        ≤ |M 0 0| * |(x.val 0 : ℝ)| ^ 2 + |M 0 1 + M 1 0| * (|(x.val 0 : ℝ)| * |(x.val 1 : ℝ)|) +
            |M 1 1| * |(x.val 1 : ℝ)| ^ 2 := by
          have e1 : |M 0 0 * (x.val 0 : ℝ) ^ 2| = |M 0 0| * |(x.val 0 : ℝ)| ^ 2 := by
            rw [abs_mul, abs_pow]
          have e2 : |(M 0 1 + M 1 0) * x.val 0 * x.val 1| =
              |M 0 1 + M 1 0| * (|(x.val 0 : ℝ)| * |(x.val 1 : ℝ)|) := by
            rw [abs_mul, abs_mul]; ring
          have e3 : |M 1 1 * (x.val 1 : ℝ) ^ 2| = |M 1 1| * |(x.val 1 : ℝ)| ^ 2 := by
            rw [abs_mul, abs_pow]
          calc _ ≤ |M 0 0 * (x.val 0 : ℝ) ^ 2 + (M 0 1 + M 1 0) * x.val 0 * x.val 1| +
                |M 1 1 * (x.val 1 : ℝ) ^ 2| := abs_add_le _ _
            _ ≤ |M 0 0 * (x.val 0 : ℝ) ^ 2| + |(M 0 1 + M 1 0) * x.val 0 * x.val 1| +
                |M 1 1 * (x.val 1 : ℝ) ^ 2| := add_le_add (abs_add_le _ _) le_rfl
            _ = _ := by rw [e1, e2, e3]
      _ ≤ |M 0 0| * ρ ^ 2 + |M 0 1 + M 1 0| * ρ ^ 2 + |M 1 1| * ρ ^ 2 := by
          gcongr
      _ = (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * ρ ^ 2 := by ring
      _ ≤ 4 * m * ρ ^ 2 := mul_le_mul_of_nonneg_right hsym (sq_nonneg _)
  have htri : componentBallL2 C 0 ρ (fun x => a - c + inner ℝ p (latticeEuclideanEmbedding x.val))
      ≤ N + 4 * m * ρ ^ 2 := by
    have e : (fun x : C => a - c + inner ℝ p (latticeEuclideanEmbedding x.val)) =
        (fun x => latticeQuadFun a p M x.val - c) -
          fun x => quadForm M (latticeEuclideanEmbedding x.val) := by
      funext x; simp only [Pi.sub_apply, latticeQuadFun]; ring
    have h := map_sub_le_add (componentBallSeminorm C 0 ρ)
      (fun x => latticeQuadFun a p M x.val - c)
      (fun x => quadForm M (latticeEuclideanEmbedding x.val))
    rw [← e, componentBallSeminorm_apply, componentBallSeminorm_apply,
      componentBallSeminorm_apply] at h
    linarith
  have hp : ‖p‖ * ρ ≤ 2 / Real.sqrt (capFraction 2 κ) * (N + 4 * m * ρ ^ 2) := by
    have hsδ : 0 < Real.sqrt (capFraction 2 κ) := Real.sqrt_pos.2 hδ
    have h := haff.trans htri
    rw [div_mul_eq_mul_div, le_div_iff₀ hsδ]
    nlinarith [mul_nonneg hsδ.le (abs_nonneg (a - c)), mul_nonneg (norm_nonneg p) hρ0.le]
  have hp01 : |p 0| + |p 1| ≤ 2 * ‖p‖ := by
    have h0 := PiLp.norm_apply_le p 0
    have h1 := PiLp.norm_apply_le p 1
    rw [Real.norm_eq_abs] at h0 h1
    linarith
  have hm0 : 0 ≤ m := abs_nonneg _
  have hcoef : 0 ≤ 4 / Real.sqrt (capFraction 2 κ) := by positivity
  have hcoef2 : 0 ≤ 4 / quadLowerConst 2 κ (capFraction 2 κ) := by positivity
  have hmρ : 4 * m * ρ ^ 2 ≤ 4 / quadLowerConst 2 κ (capFraction 2 κ) * N := by
    have := mul_le_mul_of_nonneg_left hmN (by norm_num : (0 : ℝ) ≤ 4)
    calc 4 * m * ρ ^ 2 = 4 * (m * ρ ^ 2) := by ring
      _ ≤ 4 * (N / quadLowerConst 2 κ (capFraction 2 κ)) := this
      _ = _ := by ring
  calc (|p 0| + |p 1|) * ρ + (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * ρ ^ 2
      ≤ 2 * ‖p‖ * ρ + 4 * m * ρ ^ 2 := by
        have := mul_le_mul_of_nonneg_right hp01 hρ0.le
        have := mul_le_mul_of_nonneg_right hsym (sq_nonneg ρ)
        nlinarith
    _ ≤ 2 * (2 / Real.sqrt (capFraction 2 κ) * (N + 4 * m * ρ ^ 2)) + 4 * m * ρ ^ 2 := by
        linarith
    _ = 4 / Real.sqrt (capFraction 2 κ) * (N + 4 * m * ρ ^ 2) + 4 * m * ρ ^ 2 := by ring
    _ ≤ 4 / Real.sqrt (capFraction 2 κ) * (N + 4 / quadLowerConst 2 κ (capFraction 2 κ) * N) +
          4 / quadLowerConst 2 κ (capFraction 2 κ) * N := by
        gcongr
    _ = _ := by ring

end Rigidity.Proofs.Regularity

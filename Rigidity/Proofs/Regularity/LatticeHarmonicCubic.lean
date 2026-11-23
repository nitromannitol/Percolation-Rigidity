import Rigidity.Proofs.Regularity.LatticeHarmonicExcessTwo

/-!
# Harmonic cubic polynomials on `ℤ²`

The cubic polynomials in the coordinates `y₀, y₁` of `ℤ²` (`IsLatticeCubic`) are closed under the
group operations and under translations (`IsLatticeCubic.comp_sub`), and the lattice Laplacian
of such a polynomial is the continuum one,
`Δ F = 2 c₃ + 2 c₅ + (6 c₆ + 2 c₈) y₀ + (2 c₇ + 6 c₉) y₁`
(`latticeLaplacian_eq_of_cubic`), the lattice Laplacian being exact on polynomials of degree at
most three. The lattice harmonic cubic polynomials `Ā_3` on the lattice component
(`latticeHarmonicCubic`) contain the lattice harmonic quadratic functions.

For the third-order expansion of a lattice harmonic function at a point `c`, the cubic part
`cubicPart t c` with coefficients `t = (t₀, t₁, t₂, t₃)` has the constant third forward differences
`D_a D_b D_e (cubicPart t c) = t_{a + b + e}` (`fwd_fwd_fwd_cubicPart`) and Laplacian
`(t₀ + t₂) (y₀ - c₀) + (t₁ + t₃) (y₁ - c₁)` (`latticeLaplacian_cubicPart`), which the correction
`cubicCorr σ c = (σ₀ (y₀ - c₀) + σ₁ (y₁ - c₁)) |y - c|² / 8` removes
(`latticeLaplacian_cubicCorr`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

/-- The functions on `ℤ²` that are cubic polynomials in the coordinates. -/
def IsLatticeCubic (F : (Fin 2 → ℤ) → ℝ) : Prop :=
  ∃ c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ, ∀ y : Fin 2 → ℤ,
    F y = c₀ + c₁ * y 0 + c₂ * y 1 + c₃ * y 0 ^ 2 + c₄ * y 0 * y 1 + c₅ * y 1 ^ 2 +
      c₆ * y 0 ^ 3 + c₇ * y 0 ^ 2 * y 1 + c₈ * y 0 * y 1 ^ 2 + c₉ * y 1 ^ 3

theorem IsLatticeCubic.add {F G : (Fin 2 → ℤ) → ℝ} (hF : IsLatticeCubic F)
    (hG : IsLatticeCubic G) : IsLatticeCubic fun y => F y + G y := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hF⟩ := hF
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, hG⟩ := hG
  exact ⟨a₀ + b₀, a₁ + b₁, a₂ + b₂, a₃ + b₃, a₄ + b₄, a₅ + b₅, a₆ + b₆, a₇ + b₇, a₈ + b₈,
    a₉ + b₉, fun y => by simp only [hF, hG]; ring⟩

theorem IsLatticeCubic.neg {F : (Fin 2 → ℤ) → ℝ} (hF : IsLatticeCubic F) :
    IsLatticeCubic fun y => -F y := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hF⟩ := hF
  exact ⟨-a₀, -a₁, -a₂, -a₃, -a₄, -a₅, -a₆, -a₇, -a₈, -a₉, fun y => by simp only [hF]; ring⟩

theorem IsLatticeCubic.sub {F G : (Fin 2 → ℤ) → ℝ} (hF : IsLatticeCubic F)
    (hG : IsLatticeCubic G) : IsLatticeCubic fun y => F y - G y := by
  have := hF.add hG.neg
  simpa only [← sub_eq_add_neg] using this

theorem isLatticeCubic_zero : IsLatticeCubic fun _ => 0 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, fun _ => by ring⟩

/-- **Translation of a cubic polynomial.** -/
theorem IsLatticeCubic.comp_sub {F : (Fin 2 → ℤ) → ℝ} (hF : IsLatticeCubic F)
    (t : Fin 2 → ℤ) : IsLatticeCubic fun y => F (y - t) := by
  obtain ⟨c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hF⟩ := hF
  set a : ℝ := (t 0 : ℝ)
  set b : ℝ := (t 1 : ℝ)
  refine ⟨c₀ - c₁ * a - c₂ * b + c₃ * a ^ 2 + c₄ * a * b + c₅ * b ^ 2 - c₆ * a ^ 3 -
      c₇ * a ^ 2 * b - c₈ * a * b ^ 2 - c₉ * b ^ 3,
    c₁ - 2 * c₃ * a - c₄ * b + 3 * c₆ * a ^ 2 + 2 * c₇ * a * b + c₈ * b ^ 2,
    c₂ - c₄ * a - 2 * c₅ * b + c₇ * a ^ 2 + 2 * c₈ * a * b + 3 * c₉ * b ^ 2,
    c₃ - 3 * c₆ * a - c₇ * b, c₄ - 2 * c₇ * a - 2 * c₈ * b, c₅ - c₈ * a - 3 * c₉ * b,
    c₆, c₇, c₈, c₉, fun y => ?_⟩
  show F (y - t) = _
  rw [hF]
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

@[simp] theorem unit_two_zero_zero : (unit 0 : Fin 2 → ℤ) 0 = 1 := by simp [unit]

@[simp] theorem unit_two_zero_one : (unit 0 : Fin 2 → ℤ) 1 = 0 := by simp [unit]

@[simp] theorem unit_two_one_zero : (unit 1 : Fin 2 → ℤ) 0 = 0 := by simp [unit]

@[simp] theorem unit_two_one_one : (unit 1 : Fin 2 → ℤ) 1 = 1 := by simp [unit]

@[simp] theorem add_unit_zero_apply_zero (y : Fin 2 → ℤ) : (y + unit 0 : Fin 2 → ℤ) 0 = y 0 + 1 := by
  simp [unit]

@[simp] theorem add_unit_zero_apply_one (y : Fin 2 → ℤ) : (y + unit 0 : Fin 2 → ℤ) 1 = y 1 := by
  simp [unit]

@[simp] theorem add_unit_one_apply_zero (y : Fin 2 → ℤ) : (y + unit 1 : Fin 2 → ℤ) 0 = y 0 := by
  simp [unit]

@[simp] theorem add_unit_one_apply_one (y : Fin 2 → ℤ) : (y + unit 1 : Fin 2 → ℤ) 1 = y 1 + 1 := by
  simp [unit]

@[simp] theorem sub_unit_zero_apply_zero (y : Fin 2 → ℤ) : (y - unit 0 : Fin 2 → ℤ) 0 = y 0 - 1 := by
  simp [unit]

@[simp] theorem sub_unit_zero_apply_one (y : Fin 2 → ℤ) : (y - unit 0 : Fin 2 → ℤ) 1 = y 1 := by
  simp [unit]

@[simp] theorem sub_unit_one_apply_zero (y : Fin 2 → ℤ) : (y - unit 1 : Fin 2 → ℤ) 0 = y 0 := by
  simp [unit]

@[simp] theorem sub_unit_one_apply_one (y : Fin 2 → ℤ) : (y - unit 1 : Fin 2 → ℤ) 1 = y 1 - 1 := by
  simp [unit]

/-- **The lattice Laplacian of a cubic polynomial** is its continuum Laplacian. -/
theorem latticeLaplacian_eq_of_cubic {F : (Fin 2 → ℤ) → ℝ}
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ}
    (hF : ∀ y : Fin 2 → ℤ, F y = c₀ + c₁ * y 0 + c₂ * y 1 + c₃ * y 0 ^ 2 + c₄ * y 0 * y 1 +
      c₅ * y 1 ^ 2 + c₆ * y 0 ^ 3 + c₇ * y 0 ^ 2 * y 1 + c₈ * y 0 * y 1 ^ 2 + c₉ * y 1 ^ 3)
    (y : Fin 2 → ℤ) :
    latticeLaplacian F y =
      2 * c₃ + 2 * c₅ + (6 * c₆ + 2 * c₈) * y 0 + (2 * c₇ + 6 * c₉) * y 1 := by
  simp only [latticeLaplacian, Fin.sum_univ_two, hF, add_unit_zero_apply_zero,
    add_unit_zero_apply_one, add_unit_one_apply_zero, add_unit_one_apply_one,
    sub_unit_zero_apply_zero, sub_unit_zero_apply_one, sub_unit_one_apply_zero,
    sub_unit_one_apply_one]
  push_cast
  ring

/-- The lattice harmonic cubic polynomials, `Ā_3` on the lattice component of `ℤ²`. -/
def latticeHarmonicCubic : AddSubgroup (latticeComponent 2 → ℝ) where
  carrier := {v | IsLatticeCubic (latticeExt v) ∧ ∀ y : Fin 2 → ℤ,
    latticeLaplacian (latticeExt v) y = 0}
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    have e : latticeExt (v + w) = fun y => latticeExt v y + latticeExt w y := rfl
    refine ⟨e ▸ hv.add hw, fun y => ?_⟩
    rw [e, latticeLaplacian_add, hv' y, hw' y, add_zero]
  zero_mem' := ⟨isLatticeCubic_zero, fun y => by simp [latticeExt, latticeLaplacian]⟩
  neg_mem' := by
    rintro v ⟨hv, hv'⟩
    have e : latticeExt (-v) = fun y => -latticeExt v y := rfl
    refine ⟨e ▸ hv.neg, fun y => ?_⟩
    rw [e, latticeLaplacian_neg, hv' y, neg_zero]

theorem inner_latticeEuclideanEmbedding_two (p : EuclideanSpace ℝ (Fin 2)) (y : Fin 2 → ℤ) :
    inner ℝ p (latticeEuclideanEmbedding y) = p 0 * y 0 + p 1 * y 1 := by
  rw [inner_eq_sum, Fin.sum_univ_two]
  rfl

theorem quadForm_latticeEuclideanEmbedding_two (M : Matrix (Fin 2) (Fin 2) ℝ)
    (y : Fin 2 → ℤ) :
    quadForm M (latticeEuclideanEmbedding y) =
      M 0 0 * y 0 ^ 2 + (M 0 1 + M 1 0) * y 0 * y 1 + M 1 1 * y 1 ^ 2 := by
  simp only [quadForm, Fin.sum_univ_two]
  change M 0 0 * (y 0 : ℝ) * y 0 + M 0 1 * y 0 * y 1 + (M 1 0 * y 1 * y 0 + M 1 1 * y 1 * y 1) = _
  ring

theorem isLatticeCubic_of_mem_clusterQuadratic {v : latticeComponent 2 → ℝ}
    (hv : v ∈ clusterQuadratic (latticeComponent 2)) : IsLatticeCubic (latticeExt v) := by
  obtain ⟨a, p, M, hv⟩ := hv
  refine ⟨a, p 0, p 1, M 0 0, M 0 1 + M 1 0, M 1 1, 0, 0, 0, 0, fun y => ?_⟩
  rw [latticeExt, hv, inner_latticeEuclideanEmbedding_two, quadForm_latticeEuclideanEmbedding_two]
  ring

theorem latticeHarmonicQuadratic_le_latticeHarmonicCubic :
    latticeHarmonicQuadratic 2 ≤ latticeHarmonicCubic :=
  fun _ hv => ⟨isLatticeCubic_of_mem_clusterQuadratic hv.1, hv.2⟩

/-- The coefficient `t_k` of the third differences of `cubicPart`. -/
def cubicCoeff (t₀ t₁ t₂ t₃ : ℝ) : ℕ → ℝ
  | 0 => t₀
  | 1 => t₁
  | 2 => t₂
  | _ => t₃

/-- The cubic `(t₀ v₀³ + 3 t₁ v₀² v₁ + 3 t₂ v₀ v₁² + t₃ v₁³) / 6`, `v = y - c`. -/
noncomputable def cubicPart (t₀ t₁ t₂ t₃ : ℝ) (c y : Fin 2 → ℤ) : ℝ :=
  (t₀ * ((y 0 - c 0 : ℤ) : ℝ) ^ 3 + 3 * t₁ * ((y 0 - c 0 : ℤ) : ℝ) ^ 2 * ((y 1 - c 1 : ℤ) : ℝ) +
    3 * t₂ * ((y 0 - c 0 : ℤ) : ℝ) * ((y 1 - c 1 : ℤ) : ℝ) ^ 2 +
    t₃ * ((y 1 - c 1 : ℤ) : ℝ) ^ 3) / 6

/-- The correction `(σ₀ v₀ + σ₁ v₁) (v₀² + v₁²) / 8`, `v = y - c`. -/
noncomputable def cubicCorr (σ₀ σ₁ : ℝ) (c y : Fin 2 → ℤ) : ℝ :=
  (σ₀ * ((y 0 - c 0 : ℤ) : ℝ) + σ₁ * ((y 1 - c 1 : ℤ) : ℝ)) *
    (((y 0 - c 0 : ℤ) : ℝ) ^ 2 + ((y 1 - c 1 : ℤ) : ℝ) ^ 2) / 8

theorem isLatticeCubic_cubicPart (t₀ t₁ t₂ t₃ : ℝ) (c : Fin 2 → ℤ) :
    IsLatticeCubic (cubicPart t₀ t₁ t₂ t₃ c) := by
  have h : IsLatticeCubic fun y : Fin 2 → ℤ => (t₀ * (y 0 : ℝ) ^ 3 +
      3 * t₁ * (y 0 : ℝ) ^ 2 * y 1 + 3 * t₂ * (y 0 : ℝ) * (y 1 : ℝ) ^ 2 + t₃ * (y 1 : ℝ) ^ 3) / 6 :=
    ⟨0, 0, 0, 0, 0, 0, t₀ / 6, t₁ / 2, t₂ / 2, t₃ / 6, fun y => by ring⟩
  have := h.comp_sub c
  convert this using 2 with y
  simp only [cubicPart, Pi.sub_apply]

theorem isLatticeCubic_cubicCorr (σ₀ σ₁ : ℝ) (c : Fin 2 → ℤ) :
    IsLatticeCubic (cubicCorr σ₀ σ₁ c) := by
  have h : IsLatticeCubic fun y : Fin 2 → ℤ =>
      (σ₀ * (y 0 : ℝ) + σ₁ * (y 1 : ℝ)) * ((y 0 : ℝ) ^ 2 + (y 1 : ℝ) ^ 2) / 8 :=
    ⟨0, 0, 0, 0, 0, 0, σ₀ / 8, σ₁ / 8, σ₀ / 8, σ₁ / 8, fun y => by ring⟩
  have := h.comp_sub c
  convert this using 2 with y
  simp only [cubicCorr, Pi.sub_apply]

/-- **Third differences of the cubic part.** -/
theorem fwd_fwd_fwd_cubicPart (t₀ t₁ t₂ t₃ : ℝ) (c : Fin 2 → ℤ) (a b e : Fin 2)
    (y : Fin 2 → ℤ) :
    fwd a (fwd b (fwd e (cubicPart t₀ t₁ t₂ t₃ c))) y =
      cubicCoeff t₀ t₁ t₂ t₃ (a.val + b.val + e.val) := by
  fin_cases a <;> fin_cases b <;> fin_cases e <;>
    simp [fwd, cubicPart, cubicCoeff] <;> ring

/-- **The Laplacian of the cubic part.** -/
theorem latticeLaplacian_cubicPart (t₀ t₁ t₂ t₃ : ℝ) (c y : Fin 2 → ℤ) :
    latticeLaplacian (cubicPart t₀ t₁ t₂ t₃ c) y =
      (t₀ + t₂) * ((y 0 - c 0 : ℤ) : ℝ) + (t₁ + t₃) * ((y 1 - c 1 : ℤ) : ℝ) := by
  simp only [latticeLaplacian, Fin.sum_univ_two, cubicPart, add_unit_zero_apply_zero,
    add_unit_zero_apply_one, add_unit_one_apply_zero, add_unit_one_apply_one,
    sub_unit_zero_apply_zero, sub_unit_zero_apply_one, sub_unit_one_apply_zero,
    sub_unit_one_apply_one]
  push_cast
  ring

/-- **The Laplacian of the correction.** -/
theorem latticeLaplacian_cubicCorr (σ₀ σ₁ : ℝ) (c y : Fin 2 → ℤ) :
    latticeLaplacian (cubicCorr σ₀ σ₁ c) y =
      σ₀ * ((y 0 - c 0 : ℤ) : ℝ) + σ₁ * ((y 1 - c 1 : ℤ) : ℝ) := by
  simp only [latticeLaplacian, Fin.sum_univ_two, cubicCorr, add_unit_zero_apply_zero,
    add_unit_zero_apply_one, add_unit_one_apply_zero, add_unit_one_apply_one,
    sub_unit_zero_apply_zero, sub_unit_zero_apply_one, sub_unit_one_apply_zero,
    sub_unit_one_apply_one]
  push_cast
  ring

/-- The correction is at most `(|σ₀| + |σ₁|) S³ / 4` on the points with `|yᵢ - cᵢ| ≤ S`. -/
theorem abs_cubicCorr_le (σ₀ σ₁ : ℝ) {c y : Fin 2 → ℤ} {S : ℝ}
    (hy : ∀ i, |((y i - c i : ℤ) : ℝ)| ≤ S) :
    |cubicCorr σ₀ σ₁ c y| ≤ (|σ₀| + |σ₁|) * S ^ 3 / 4 := by
  have hS : 0 ≤ S := (abs_nonneg _).trans (hy 0)
  set v₀ : ℝ := ((y 0 - c 0 : ℤ) : ℝ)
  set v₁ : ℝ := ((y 1 - c 1 : ℤ) : ℝ)
  have h0 : |v₀| ≤ S := hy 0
  have h1 : |v₁| ≤ S := hy 1
  have hq : |v₀ ^ 2 + v₁ ^ 2| ≤ 2 * S ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have := sq_le_sq' (abs_le.1 h0).1 (abs_le.1 h0).2
    have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
    linarith
  have hl : |σ₀ * v₀ + σ₁ * v₁| ≤ (|σ₀| + |σ₁|) * S := by
    calc |σ₀ * v₀ + σ₁ * v₁| ≤ |σ₀| * |v₀| + |σ₁| * |v₁| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |σ₀| * S + |σ₁| * S := add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
      _ = (|σ₀| + |σ₁|) * S := by ring
  have : cubicCorr σ₀ σ₁ c y = (σ₀ * v₀ + σ₁ * v₁) * (v₀ ^ 2 + v₁ ^ 2) / 8 := rfl
  rw [this, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  have := mul_le_mul hl hq (abs_nonneg _) (by positivity)
  calc |σ₀ * v₀ + σ₁ * v₁| * |v₀ ^ 2 + v₁ ^ 2| / 8 ≤ (|σ₀| + |σ₁|) * S * (2 * S ^ 2) / 8 :=
        div_le_div_of_nonneg_right this (by norm_num)
    _ = (|σ₀| + |σ₁|) * S ^ 3 / 4 := by ring

end Rigidity.Proofs.Regularity

import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Sums of a nonnegative planar quadratic form over two bases

A function `g` on `ℝ²` is quadratic when `g (a r + b s) = a² g r + b² g s + a b (g (r + s) - g r - g s)`.
If moreover `g ≥ 0`, then by the parallelogram identity `g q ≤ 2 |q|² (g e₀ + g e₁)`. Applied to
`g ∘ B` for an invertible matrix `B` with `B hᵢ = eᵢ`, this compares the sums of `g` over the bases
`(eᵢ)` and `(B eᵢ)`:

`g e₀ + g e₁ ≤ 2 (|h₀|² + |h₁|²) (g (B e₀) + g (B e₁))`.

These are the comparisons of traces used in Step 1 of the proof of Lemma 5.10 of Armstrong and
Dario (for the quadratic forms `E[μ(□_{n+1}, ·)] - E[μ(□_n, ·)]` and `E[ν(□_n, ·)] - E[ν(□_{n+1}, ·)]`
and the bases `(ā_{□_n} eᵢ)` and `(ā⁻¹ eᵢ)`).
-/

open scoped Matrix

namespace Rigidity.Percolation

/-- A quadratic function on the plane. -/
def IsPlanarQuadratic (g : (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ (r s : Fin 2 → ℝ) (a b : ℝ),
    g (a • r + b • s) = a ^ 2 * g r + b ^ 2 * g s + a * b * (g (r + s) - g r - g s)

theorem IsPlanarQuadratic.add_reflect {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (r s : Fin 2 → ℝ) (a b : ℝ) :
    g (a • r + b • s) + g (a • r + (-b) • s) = 2 * (a ^ 2 * g r + b ^ 2 * g s) := by
  rw [hg, hg]
  ring

/-- **A nonnegative quadratic form is controlled by its values at the unit vectors.** -/
theorem IsPlanarQuadratic.le_of_nonneg {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (h0 : ∀ q, 0 ≤ g q) (q : Fin 2 → ℝ) :
    g q ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) * (g (Pi.single 0 1) + g (Pi.single 1 1)) := by
  have hq : q = q 0 • (Pi.single 0 1 : Fin 2 → ℝ) + q 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> simp
  have hpar := hg.add_reflect (Pi.single 0 1) (Pi.single 1 1) (q 0) (q 1)
  rw [← hq] at hpar
  have hr := h0 (q 0 • (Pi.single 0 1 : Fin 2 → ℝ) + (-q 1) • (Pi.single 1 1 : Fin 2 → ℝ))
  have he0 := h0 (Pi.single 0 1)
  have he1 := h0 (Pi.single 1 1)
  have a1 : q 0 ^ 2 * g (Pi.single 0 1) ≤ (q 0 ^ 2 + q 1 ^ 2) * g (Pi.single 0 1) := by
    nlinarith [sq_nonneg (q 1)]
  have a2 : q 1 ^ 2 * g (Pi.single 1 1) ≤ (q 0 ^ 2 + q 1 ^ 2) * g (Pi.single 1 1) := by
    nlinarith [sq_nonneg (q 0)]
  nlinarith

/-- Quadratic functions are stable under composition with matrices. -/
theorem IsPlanarQuadratic.comp_mulVec {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (B : Matrix (Fin 2) (Fin 2) ℝ) : IsPlanarQuadratic fun q => g (B *ᵥ q) := by
  intro r s a b
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  exact hg _ _ a b

/-- **Comparison of the sums of a nonnegative quadratic form over two bases.** -/
theorem IsPlanarQuadratic.sum_single_le {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (h0 : ∀ q, 0 ≤ g q) (B : Matrix (Fin 2) (Fin 2) ℝ) {h₀ h₁ : Fin 2 → ℝ}
    (hh₀ : B *ᵥ h₀ = Pi.single 0 1) (hh₁ : B *ᵥ h₁ = Pi.single 1 1) :
    g (Pi.single 0 1) + g (Pi.single 1 1) ≤
      2 * ((h₀ 0 ^ 2 + h₀ 1 ^ 2) + (h₁ 0 ^ 2 + h₁ 1 ^ 2)) *
        (g (B *ᵥ Pi.single 0 1) + g (B *ᵥ Pi.single 1 1)) := by
  have hB := hg.comp_mulVec B
  have hB0 : ∀ q, 0 ≤ g (B *ᵥ q) := fun q => h0 _
  have k0 := hB.le_of_nonneg hB0 h₀
  have k1 := hB.le_of_nonneg hB0 h₁
  simp only [hh₀, hh₁] at k0 k1
  linarith

end Rigidity.Percolation

import Rigidity.Proofs.Green.LazyHeatKernel
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The mass of the heat kernel of the lazy walk

The lazy kernel `Q(x, z) = 1/D` for `z ∼ x`, `Q(x, x) = 1 - deg x / D` is stochastic, so every
power `Qⁿ(x, ·)` has total mass one (`hasSum_lazyPow`), and so has the heat kernel
`p_t(x, ·) = Σ_n e^{-Dt} (Dt)^n / n! · Qⁿ(x, ·)` for `t ≥ 0` (`tsum_ofReal_vsrwHeat`).
-/

open scoped Classical
open Finset Filter

namespace Rigidity.Green

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

/-- **The lazy kernel is stochastic**: `Σ_y Qⁿ(x, y) = 1`. -/
theorem hasSum_lazyPow (hD : 0 < D) (n : ℕ) (x : V) :
    HasSum (fun y => lazyPow G D n x y) 1 := by
  induction n generalizing x with
  | zero =>
    have e : (fun y => lazyPow G D 0 x y) = fun y => if y = x then (1 : ℝ) else 0 := by
      funext y
      rw [lazyPow_zero]
      by_cases hxy : x = y
      · subst hxy
        simp
      · rw [if_neg hxy, if_neg (Ne.symm hxy)]
    rw [e]
    exact hasSum_ite_eq x 1
  | succ n ih =>
    have h1 := (ih x).mul_left (1 - (G.degree x : ℝ) / D)
    have h2 := (hasSum_sum fun z (_ : z ∈ G.neighborFinset x) => ih z).mul_left (1 / (D : ℝ))
    have h := h1.add h2
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have hval : (1 - (G.degree x : ℝ) / D) * 1 + 1 / (D : ℝ) * ∑ _z ∈ G.neighborFinset x, (1 : ℝ) =
        1 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, G.card_neighborFinset_eq_degree]
      field_simp
      ring
    rw [hval] at h
    have e : (fun y => lazyPow G D (n + 1) x y) = fun y =>
        (1 - (G.degree x : ℝ) / D) * lazyPow G D n x y +
          1 / (D : ℝ) * ∑ z ∈ G.neighborFinset x, lazyPow G D n z y := by
      funext y
      rw [lazyPow_succ]
    rw [e]
    exact h

/-- **The heat kernel has mass one**: `Σ_y p_t(x, y) = 1` for `t ≥ 0`. -/
theorem tsum_ofReal_vsrwHeat (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    (x : V) : ∑' y, ENNReal.ofReal (vsrwHeat G D t x y) = 1 := by
  have hterm : ∀ y, ENNReal.ofReal (vsrwHeat G D t x y) =
      ∑' n, ENNReal.ofReal (poissonWeight D t n * lazyPow G D n x y) := fun y =>
    ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (poissonWeight_nonneg ht n)
      (lazyPow_mem_Icc hD hdeg n x y).1) (summable_vsrwHeat hD hdeg t x y)
  simp only [hterm]
  rw [ENNReal.tsum_comm]
  have hrow : ∀ n, ∑' y, ENNReal.ofReal (poissonWeight D t n * lazyPow G D n x y) =
      ENNReal.ofReal (poissonWeight D t n) := by
    intro n
    simp_rw [ENNReal.ofReal_mul (poissonWeight_nonneg ht n)]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
      (fun y => (lazyPow_mem_Icc hD hdeg n x y).1) (hasSum_lazyPow hD n x).summable,
      (hasSum_lazyPow hD n x).tsum_eq, ENNReal.ofReal_one, mul_one]
  simp only [hrow]
  rw [← ENNReal.ofReal_tsum_of_nonneg (poissonWeight_nonneg ht) (hasSum_poissonWeight t).summable,
    (hasSum_poissonWeight t).tsum_eq, ENNReal.ofReal_one]

end Rigidity.Green

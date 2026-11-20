import Rigidity.Percolation.SlabRadiusCrossing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential absorption of polynomial factors

Polynomial prefactors in slab estimates are absorbed by any smaller positive
exponential rate at sufficiently large scales.
-/

namespace Rigidity.Percolation

open Filter Asymptotics
open scoped Topology

/-- Any nonnegative multiple of a power is eventually bounded by a positive
exponential. -/
theorem eventually_mul_pow_le_exp (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, A * x ^ k ≤ Real.exp (b * x) := by
  have hA1 : 0 < A + 1 := by linarith
  have hsmall := (isLittleO_pow_exp_pos_mul_atTop k hb).bound (inv_pos.mpr hA1)
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hpow : 0 ≤ x ^ k := pow_nonneg hx0 k
  have he : 0 ≤ Real.exp (b * x) := Real.exp_nonneg _
  rw [Real.norm_of_nonneg hpow, Real.norm_of_nonneg he] at hx
  have hcoef : A * (A + 1)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hA1]
    linarith
  calc
    A * x ^ k ≤ A * ((A + 1)⁻¹ * Real.exp (b * x)) := mul_le_mul_of_nonneg_left hx hA
    _ = (A * (A + 1)⁻¹) * Real.exp (b * x) := by ring
    _ ≤ 1 * Real.exp (b * x) := mul_le_mul_of_nonneg_right hcoef he
    _ = _ := one_mul _

/-- A polynomial times an exponential is eventually dominated by the same
exponential with half its rate. -/
theorem eventually_mul_pow_mul_exp_le (A a : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, A * x ^ k * Real.exp (-(a * x)) ≤
      Real.exp (-((a / 2) * x)) := by
  filter_upwards [eventually_mul_pow_le_exp A (a / 2) hA (by positivity) k] with x hx
  calc
    A * x ^ k * Real.exp (-(a * x)) ≤
        Real.exp ((a / 2) * x) * Real.exp (-(a * x)) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)
    _ = Real.exp (-((a / 2) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Rigidity.Percolation

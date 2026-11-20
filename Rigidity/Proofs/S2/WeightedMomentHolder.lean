import Rigidity.Proofs.S2.PlanarPowerVariance

/-!
# Hölder control of weighted moments

A nonnegative `Lⁿ` weight and a bounded random variable yield the moment estimate used in the
spectral-gap iteration.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory
open scoped ENNReal

/-- Hölder's inequality for a bounded variable and a nonnegative `Lⁿ` weight. -/
theorem weighted_moment_holder {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X W : Ω → ℝ) (hXm : Measurable X)
    (hX : ∀ ω, |X ω| ≤ 1) (hW0 : ∀ ω, 0 ≤ W ω)
    (n : ℕ) (hn : 2 ≤ n) (hW : MemLp W n P) :
    (∫ ω, |X ω| ^ (2 * (n - 1)) * W ω ∂P) ≤
      (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) * lpNorm W n P := by
  let p : ℝ := (n : ℝ) / ((n : ℝ) - 1)
  let q : ℝ := n
  let Z (ω : Ω) := |X ω| ^ (2 * (n - 1))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hn0 : 0 < (n : ℝ) := by linarith
  have hp1 : 1 < p := by dsimp [p]; exact (lt_div_iff₀ hn1).2 (by linarith)
  have hpq : p.HolderConjugate q := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hp1, ?_⟩
    dsimp [p, q]
    field_simp
    ring
  have hZm : Measurable Z := hXm.abs.pow_const _
  have hZ : MemLp Z (ENNReal.ofReal p) P := by
    refine MemLp.of_bound hZm.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_one₀ (abs_nonneg _) (hX ω)
  have hW' : MemLp W (ENNReal.ofReal q) P := by simpa [q] using hW
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) _)
    (Filter.Eventually.of_forall hW0) hZ hW'
  have hexponent : ((2 * (n - 1) : ℕ) : ℝ) * p = ((2 * n : ℕ) : ℝ) := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    simp only [Nat.cast_mul, Nat.cast_ofNat, hcast]
    dsimp [p]
    field_simp
  have hZp (ω : Ω) : Z ω ^ p = |X ω| ^ (2 * n) := by
    dsimp only [Z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hexponent, Real.rpow_natCast]
  have hinv : 1 / p = ((n : ℝ) - 1) / n := by
    dsimp [p]
    field_simp
  have hWnorm : lpNorm W n P = (∫ ω, W ω ^ q ∂P) ^ (1 / q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast (show n ≠ 0 by omega))
      (ENNReal.natCast_ne_top n) hW.aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_of_nonneg (hW0 _), q, one_div]
  have hEqInt : (∫ ω, Z ω ^ p ∂P) = ∫ ω, |X ω| ^ (2 * n) ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hZp
  rw [hEqInt, hinv, ← hWnorm] at hh
  exact hh

end Rigidity.Proofs.S2

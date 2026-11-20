import Rigidity.Proofs.Percolation.PlanarWellConnectedGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Planar well-connectedness tails

The good-cube estimate is summed over the finitely many relevant subcubes.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Percolation

/-- A relevant subcube radius has square root at least half the outer radius to power `1/800`. -/
theorem relevantSubcube_sqrt_lower {R M : ℕ}
    (hM : (R : ℝ) ^ (1 / 400 : ℝ) / 2 ≤ M) :
    (R : ℝ) ^ (1 / 800 : ℝ) / 2 ≤ (M : ℝ) ^ (1 / 2 : ℝ) := by
  let t : ℝ := (R : ℝ) ^ (1 / 800 : ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg R) _
  have hsq : t ^ 2 = (R : ℝ) ^ (1 / 400 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg R)]
    norm_num
  rw [← Real.sqrt_eq_rpow]
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, hsq]
  nlinarith

/-- A union bound for the failures of well-connectedness at a fixed outer radius. -/
theorem wellConnected_failure_bound_raw (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (R : ℕ), 1 ≤ R →
      (R : ℝ) ^ (1 / 400 : ℝ) ≤ R / 100 →
      latticeBondLaw 2 p {ω | ¬ IsWellConnected ω x R} ≤
        ((((4 * R + 1) ^ 2 * (R + 1) + 1 : ℕ) : ℝ≥0∞)) *
          ENNReal.ofReal (C * Real.exp (-(c * (R : ℝ) ^ (1 / 800 : ℝ)))) := by
  obtain ⟨C, c, hC, hc, hgood⟩ := goodSubcube_failure_bound p hp
  refine ⟨C, c / 2, hC, by positivity, fun x R hR hpower => ?_⟩
  let A : ℝ := C * Real.exp (-(c / 2 * (R : ℝ) ^ (1 / 800 : ℝ)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hmain : latticeBondLaw 2 p {ω | ¬ IsGoodSubcube ω x R} ≤ ENNReal.ofReal A := by
    refine (hgood x R).trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : (R : ℝ) ^ (1 / 800 : ℝ) ≤ (R : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hRreal (by norm_num)
    dsimp [A]
    gcongr
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg R) (1 / 800 : ℝ)]
  have hsub : ∀ q ∈ relevantSubcubes x R,
      latticeBondLaw 2 p {ω | ¬ IsGoodSubcube ω q.1 q.2} ≤ ENNReal.ofReal A := by
    intro q hq
    have hM := (Finset.mem_filter.mp hq).2
    have hroot := relevantSubcube_sqrt_lower hM
    refine (hgood q.1 q.2).trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp [A]
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsum : latticeBondLaw 2 p
      (⋃ q ∈ relevantSubcubes x R, {ω | ¬ IsGoodSubcube ω q.1 q.2}) ≤
      ((relevantSubcubes x R).card : ℝ≥0∞) * ENNReal.ofReal A := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc
      _ ≤ ∑ _q ∈ relevantSubcubes x R, ENNReal.ofReal A := Finset.sum_le_sum hsub
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ latticeBondLaw 2 p {ω | ¬ IsGoodSubcube ω x R} +
        latticeBondLaw 2 p (⋃ q ∈ relevantSubcubes x R, {ω | ¬ IsGoodSubcube ω q.1 q.2}) :=
      (measure_mono (not_wellConnected_subset x R hpower)).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal A + ((relevantSubcubes x R).card : ℝ≥0∞) * ENNReal.ofReal A :=
      add_le_add hmain hsum
    _ = (((relevantSubcubes x R).card + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal A := by
      push_cast
      ring
    _ ≤ ((((4 * R + 1) ^ 2 * (R + 1) + 1 : ℕ) : ℝ≥0∞)) * ENNReal.ofReal A := by
      gcongr
      exact_mod_cast card_relevantSubcubes_le x R

end Rigidity.Percolation

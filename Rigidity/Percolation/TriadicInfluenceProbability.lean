import Rigidity.Percolation.TriadicInfluenceCount
import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Probability bounds for stable cubes

A union bound transfers scale-dependent bounds on bad cubes to the stable
subcollection. The deterministic influence count supplies the factor `19 ^ d`.
-/

namespace Rigidity.Percolation

open MeasureTheory
open scoped ENNReal

/-- The probability that a cube is not stable is bounded by the sum of the
per-scale bad-cube bounds multiplied by the number of influenced cubes. -/
theorem TriadicCube.measure_not_mem_stableGood_le {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (p : ℕ → ℝ≥0∞) (hprob : ∀ R : TriadicCube d, μ {ω | R ∉ G ω} ≤ p R.scale)
    (Q : TriadicCube d) :
    μ {ω | Q ∉ stableGood (G ω)} ≤ ∑' n : ℕ, (19 ^ d : ℝ≥0∞) * p (Q.scale + n) := by
  classical
  let cubes : ℕ → Finset (TriadicCube d) := fun n => (Q.finite_influence_at_scale (Q.scale + n)).1.toFinset
  let bad : TriadicCube d → Set Ω := fun R => {ω | R ∉ G ω}
  have hsubset : {ω | Q ∉ stableGood (G ω)} ⊆ ⋃ n, ⋃ R ∈ cubes n, bad R := by
    intro ω hω
    simp only [stableGood, Set.mem_setOf_eq, Set.not_subset] at hω
    obtain ⟨R, hR, hbad⟩ := hω
    refine Set.mem_iUnion.mpr ⟨R.scale - Q.scale, Set.mem_iUnion.mpr ⟨R, ?_⟩⟩
    refine Set.mem_iUnion.mpr ⟨?_, hbad⟩
    simp only [cubes, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨hR, by have := scale_le_of_mem_influence hR; omega⟩
  calc
    μ {ω | Q ∉ stableGood (G ω)} ≤ μ (⋃ n, ⋃ R ∈ cubes n, bad R) := measure_mono hsubset
    _ ≤ ∑' n, μ (⋃ R ∈ cubes n, bad R) := measure_iUnion_le _
    _ ≤ ∑' n, (19 ^ d : ℝ≥0∞) * p (Q.scale + n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        μ (⋃ R ∈ cubes n, bad R) ≤ ∑ R ∈ cubes n, μ (bad R) := measure_biUnion_finset_le _ _
        _ ≤ ∑ _R ∈ cubes n, p (Q.scale + n) := by
          apply Finset.sum_le_sum
          intro R hR
          have hscale : R.scale = Q.scale + n := by
            simp only [cubes, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hR
            exact hR.2
          simpa only [bad, hscale] using hprob R
        _ = (cubes n).card * p (Q.scale + n) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (19 ^ d : ℝ≥0∞) * p (Q.scale + n) := by
          gcongr
          have hc : (cubes n).card ≤ 19 ^ d := by
            change (Q.finite_influence_at_scale (Q.scale + n)).1.toFinset.card ≤ 19 ^ d
            have hc' := (Q.finite_influence_at_scale (Q.scale + n)).2
            rw [Set.ncard_eq_toFinset_card _ (Q.finite_influence_at_scale (Q.scale + n)).1] at hc'
            exact hc'
          exact_mod_cast hc

end Rigidity.Percolation

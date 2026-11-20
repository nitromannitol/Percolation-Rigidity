import Rigidity.Percolation.TriadicGoodCubes
import Rigidity.Percolation.TriadicStoppingSize
import Rigidity.Percolation.TriadicLocalizationFinal

/-!
# Partitions from well-connected cubes

Exponential well-connectedness estimates yield a maximal stopping partition
with uniformly controlled size and a quantitative localization estimate.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- Under a uniform well-connectedness estimate, the associated good-cube
stopping partition exists almost surely, has uniformly bounded exponential
moments, and is localized with exponentially high probability. -/
theorem TriadicCube.wellConnected_partition_estimates {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Set (TriadicCube d))
    (hWm : ∀ Q : TriadicCube d, MeasurableSet {ω | Q ∈ W ω})
    (C : ℝ≥0∞) (hC : C ≠ ∞) (c : ℝ) (hc : 0 < c)
    (hW : ∀ Q : TriadicCube d,
      μ {ω | Q ∉ W ω} ≤ C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ Q.scale))) :
    let G : Ω → Set (TriadicCube d) := fun ω => goodOfWellConnected (W ω)
    (∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (stoppingSize (G ω) x / θ)) μ ∧
      (∫ ω, Real.exp (stoppingSize (G ω) x / θ) ∂μ) ≤ 2) ∧
    (∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube d) (n : ℕ),
      μ {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
          R.IsMaximalStopping (localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) *
          Real.exp (-k * (3 : ℝ) ^ n))) := by
  let G : Ω → Set (TriadicCube d) := fun ω => goodOfWellConnected (W ω)
  let B : ℝ≥0∞ := max (ENNReal.ofReal (Real.exp (c / 3))) ((1 + 3 ^ d) * C)
  have hB : B ≠ ∞ := by
    apply ne_of_lt
    apply max_lt_iff.mpr
    exact ⟨ENNReal.ofReal_lt_top, lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top (by simp) hC)⟩
  have hc' : 0 < c / 3 := by positivity
  have hGm : ∀ Q : TriadicCube d, MeasurableSet {ω | Q ∈ G ω} :=
    fun Q => measurableSet_mem_goodOfWellConnected W hWm Q
  have hG : ∀ Q : TriadicCube d,
      μ {ω | Q ∉ G ω} ≤ B * ENNReal.ofReal (Real.exp (-(c / 3) * (3 : ℝ) ^ Q.scale)) :=
    measure_not_mem_goodOfWellConnected_le μ W C c hc hW
  have hGside : ∀ Q : TriadicCube d,
      μ {ω | Q ∉ G ω} ≤ B * ENNReal.ofReal
        (Real.exp (-(c / 3) * ((3 : ℝ) ^ Q.scale) ^ (1 : ℝ))) := by
    intro Q
    simpa only [Real.rpow_one] using hG Q
  refine ⟨?_, ?_, ?_⟩
  · exact ae_existsUnique_maximal_stopping_of_side_stretched μ G B hB 1 (c / 3)
      (by norm_num) hc' hGside
  · obtain ⟨θ, hθ, hθm⟩ := uniform_stoppingSize_exp_moment μ G hGm B hB 1 (c / 3)
      (by norm_num) hc' hGside
    refine ⟨θ, hθ, ?_⟩
    intro x
    simpa only [Real.rpow_one] using hθm x
  · exact exists_measure_localGoodCentered_boundaryInterior_discrepancy_le hd μ G B hB
      3 (c / 3) (by norm_num) hc' hG

end Rigidity.Percolation

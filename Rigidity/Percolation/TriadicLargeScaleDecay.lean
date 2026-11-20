import Rigidity.Percolation.TriadicWellConnectedEstimates

/-!
# Extending large-scale probability bounds

An exponential estimate above a fixed triadic scale extends to all scales
under a probability measure after increasing its prefactor.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

/-- A probability bound valid from scale `n₀` extends to all scales by
increasing its prefactor. -/
theorem TriadicCube.measure_le_exp_of_large_scale {d : ℕ}
    (μ : Measure (Configuration d)) [IsProbabilityMeasure μ]
    (E : TriadicCube d → Set (Configuration d))
    (n₀ : ℕ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hlarge : ∀ Q : TriadicCube d, n₀ ≤ Q.scale →
      μ (E Q) ≤ ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale))) :
    ∀ Q : TriadicCube d, μ (E Q) ≤
      ENNReal.ofReal ((C + Real.exp (c * (3 : ℝ) ^ n₀)) *
        Real.exp (-c * (3 : ℝ) ^ Q.scale)) := by
  intro Q
  by_cases hn : n₀ ≤ Q.scale
  · calc
      μ (E Q) ≤ ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale)) := hlarge Q hn
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_nonneg _))
          (Real.exp_nonneg _)
  · have hp : (3 : ℝ) ^ Q.scale ≤ (3 : ℝ) ^ n₀ :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hexp : 1 ≤ Real.exp (c * (3 : ℝ) ^ n₀) *
        Real.exp (-c * (3 : ℝ) ^ Q.scale) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hreal : 1 ≤ (C + Real.exp (c * (3 : ℝ) ^ n₀)) *
        Real.exp (-c * (3 : ℝ) ^ Q.scale) := by
      calc
        1 ≤ Real.exp (c * (3 : ℝ) ^ n₀) * Real.exp (-c * (3 : ℝ) ^ Q.scale) := hexp
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (Real.exp_nonneg _)
    calc
      μ (E Q) ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      _ = ENNReal.ofReal 1 := by rw [ENNReal.ofReal_one]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal


/-- A large-scale well-connectedness estimate gives the almost sure stopping
partition, its exponential size moment, and its localization estimate. -/
theorem TriadicCube.partition_estimates_of_large_scale {d : ℕ} (hd : 0 < d)
    (μ : Measure (Configuration d)) [IsProbabilityMeasure μ]
    (interior : TriadicCube d → Set (Vertex d))
    (n₀ : ℕ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hlarge : ∀ Q : TriadicCube d, n₀ ≤ Q.scale →
      μ {ω | ¬ Q.wellConnectedIn (interior Q) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale))) :
    let G : Configuration d → Set (TriadicCube d) :=
      fun ω => goodOfWellConnected (wellConnectedFamily interior ω)
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
  let B := C + Real.exp (c * (3 : ℝ) ^ n₀)
  have hB : 0 ≤ B := add_nonneg hC (Real.exp_nonneg _)
  have hW : ∀ Q : TriadicCube d,
      μ {ω | ¬ Q.wellConnectedIn (interior Q) ω} ≤
        ENNReal.ofReal B * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ Q.scale)) := by
    intro Q
    rw [← ENNReal.ofReal_mul hB]
    exact TriadicCube.measure_le_exp_of_large_scale μ
      (fun Q => {ω | ¬ Q.wellConnectedIn (interior Q) ω}) n₀ C c hC hc hlarge Q
  exact wellConnectedIn_partition_estimates hd μ interior (ENNReal.ofReal B)
    ENNReal.ofReal_ne_top c hc hW

end Rigidity.Percolation

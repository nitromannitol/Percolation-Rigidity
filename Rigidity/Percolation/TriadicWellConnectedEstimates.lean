import Rigidity.Percolation.TriadicWellConnectedEvent
import Rigidity.Percolation.TriadicWellConnectedPartition

/-!
# Partition estimates from well-connectedness

A uniform exponential estimate for the well-connectedness events yields the
corresponding triadic partition, size moment, and localization bounds.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- The measurable well-connectedness family yields a stopping partition with
uniform size moments and a localization bound under an exponential estimate. -/
theorem TriadicCube.wellConnectedIn_partition_estimates {d : ℕ} (hd : 0 < d)
    (μ : Measure (Configuration d)) [IsProbabilityMeasure μ]
    (interior : TriadicCube d → Set (Vertex d))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (c : ℝ) (hc : 0 < c)
    (hW : ∀ Q : TriadicCube d,
      μ {ω | ¬ Q.wellConnectedIn (interior Q) ω} ≤
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ Q.scale))) :
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
  exact wellConnected_partition_estimates hd μ (wellConnectedFamily interior)
    (measurableSet_mem_wellConnectedFamily interior) C hC c hc hW

end Rigidity.Percolation

import Rigidity.Percolation.TriadicWellConnectedDecay
import Rigidity.Percolation.TriadicWellConnectedEstimates

/-!
# Partition estimates from local tests

Uniform exponential bounds on ambient crossings and local coalescence tests
imply the corresponding well-connected stopping partition estimates.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

/-- Uniform local crossing and coalescence estimates imply existence,
integrability, and localization for the well-connected stopping partition. -/
theorem TriadicCube.partition_estimates_of_local_tests {d : ℕ} (hd : 0 < d)
    (μ : Measure (Configuration d)) [IsProbabilityMeasure μ]
    (interior : TriadicCube d → Set (Vertex d)) (hinterior : ∀ Q, interior Q ⊆ Q.vertices)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hcross : ∀ Q : TriadicCube d, μ {ω | ¬ HasCrossingComponent ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i))} ≤
      ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale)))
    (htest : ∀ (Q : TriadicCube d) (R : IntegerCube d), R ∈ Q.testCubes (interior Q) →
      μ (Q.badCoalescenceTest R) ≤
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
  let B : ℝ := C * (1 + 2 * 7 ^ d * ((d + 1).factorial : ℝ) / (c / 2) ^ (d + 1))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hW : ∀ Q : TriadicCube d,
      μ {ω | ¬ Q.wellConnectedIn (interior Q) ω} ≤
        ENNReal.ofReal B * ENNReal.ofReal (Real.exp (-(c / 2) * (3 : ℝ) ^ Q.scale)) := by
    intro Q
    rw [← ENNReal.ofReal_mul hB]
    exact Q.measure_not_wellConnectedIn_le_exp (interior Q) (hinterior Q) μ C c hC hc
      (hcross Q) (htest Q)
  exact wellConnectedIn_partition_estimates hd μ interior (ENNReal.ofReal B)
    ENNReal.ofReal_ne_top (c / 2) (by positivity) hW

end Rigidity.Percolation

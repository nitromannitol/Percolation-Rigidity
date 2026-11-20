import Rigidity.Proofs.S2.GeometricTailStochasticBound
import Rigidity.Proofs.S2.ConditionalEnergyTail

/-!
# Stretched-exponential tails for conditional planar density energy

Conditional normalized energy satisfies an `O₁/₁₂` tail estimate at the inverse-volume scale.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Planar density resampling energy has an inverse-volume stretched-exponential tail. -/
theorem planar_conditional_density_energy_osBound (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2)
      (𝓜 : MeasurableSpace (Configuration 2 × Configuration 2)),
      @LatticeProb.OsBound (Configuration 2 × Configuration 2) Prod.instMeasurableSpace
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) (1 / 12 : ℝ)
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))
        (fun q => |MeasureTheory.condExp 𝓜
          ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))
          (planarDensityResamplingEnergy m k) q|) := by
  obtain ⟨C, hC, htail⟩ := planar_conditional_density_energy_tail p hp
  refine ⟨C * 4 ^ (12 : ℕ), by positivity, fun m k 𝓜 => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let X : Configuration 2 × Configuration 2 → ℝ := fun q =>
    |MeasureTheory.condExp 𝓜 μ (planarDensityResamplingEnergy m k) q|
  let v : ℝ := ((3 ^ m : ℕ) : ℝ)
  have hv : 0 < v := by dsimp [v]; positivity
  have hgrid (n : ℕ) (hn : 1 ≤ n) : μ {q | (C / v ^ 2) * (n : ℝ) ^ 12 ≤ X q} ≤
      (1 / 2 : ℝ≥0∞) ^ n := by
    have heq : (C / v ^ 2) * (n : ℝ) ^ 12 = C * (n : ℝ) ^ 12 / v ^ 2 := by ring
    simpa only [heq] using htail n hn m k 𝓜
  have h := @osBound_one_twelfth_of_geometric_tails (Configuration 2 × Configuration 2)
    Prod.instMeasurableSpace μ X (C / v ^ 2) (by positivity)
    (fun q => abs_nonneg _) hgrid
  have hscale : C / v ^ 2 * 4 ^ (12 : ℕ) = (C * 4 ^ (12 : ℕ)) / v ^ 2 := by ring
  simpa only [hscale] using h

end Rigidity.Proofs.S2

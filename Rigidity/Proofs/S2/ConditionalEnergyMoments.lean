import Rigidity.Proofs.S2.NormalizedEnergyOsMoment
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional moments of planar resampling energy

Conditional expectation preserves the inverse-volume moment bounds for the total squared
resampling influence.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Every conditional expectation of the planar resampling energy satisfies the same moment
bound as the energy itself. -/
theorem planar_conditional_density_energy_moments (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex 2)
      (𝓜 : MeasurableSpace (Configuration 2 × Configuration 2)),
      MemLp (MeasureTheory.condExp 𝓜 ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))
        (planarDensityResamplingEnergy m k)) r
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ∧
      lpNorm (MeasureTheory.condExp 𝓜 ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))
        (planarDensityResamplingEnergy m k)) r
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ≤
          C * (r : ℝ) ^ 12 / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hmoment⟩ := planar_normalized_density_energy_moments p hp
  refine ⟨C, hC, fun r hr m k 𝓜 => ?_⟩
  have hr' : (1 : ℝ≥0∞) ≤ r := by exact_mod_cast hr
  obtain ⟨_, hmem, hnorm⟩ := hmoment r hr m k
  change MemLp (planarDensityResamplingEnergy m k) r _ at hmem
  change lpNorm (planarDensityResamplingEnergy m k) r _ ≤ _ at hnorm
  exact ⟨hmem.condExp hr', (hmem.lpNorm_condExp_le_lpNorm hr').trans hnorm⟩

end Rigidity.Proofs.S2

import PercolationClusterHomogenization.Proofs.Density.StochasticBoundExponentialMoment
import Rigidity.Proofs.S2.NormalizedEnergyStochasticBound

/-!
# Exponential moment of planar density resampling energy

The normalized squared-influence sum has a uniform stretched-exponential moment at inverse-volume
scale under the two-copy bond law.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The normalized planar density resampling energy has a uniform half-exponential moment. -/
theorem planar_normalized_density_energy_exponential_moment (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      (∀ᵐ q : Configuration 2 × Configuration 2
          ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)),
        Summable (fun e : Bond 2 =>
          |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2)) ∧
      Integrable (fun q : Configuration 2 × Configuration 2 => Real.exp
        ((max (∑' e : Bond 2,
          |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2) 0 /
          (C / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 12 : ℝ) / 2))
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ∧
      (∫ q : Configuration 2 × Configuration 2, Real.exp
        ((max (∑' e : Bond 2,
          |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2) 0 /
          (C / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 12 : ℝ) / 2)
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ≤ Real.exp 2 := by
  obtain ⟨C, hC, htail⟩ := planar_normalized_density_energy_osBound p hp
  obtain ⟨D, hD, hmoment⟩ := planar_normalized_density_energy_moments p hp
  refine ⟨C, hC, fun m k => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let X (q : Configuration 2 × Configuration 2) : ℝ := ∑' e : Bond 2,
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ)| ^ 2
  let θ : ℝ := C / (((3 ^ m : ℕ) : ℝ) ^ 2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hXm : Measurable X := by
    apply Measurable.tsum
    intro e
    have hF := measurable_infiniteClusterCount_triadicCube m k
    have hRes := (measurePreserving_resampleBond 2 p e).measurable
    exact (((hF.comp measurable_fst).div_const _).sub
      ((hF.comp hRes).div_const _)).abs.pow_const 2
  have hInt := integrable_half_exponential_of_osBound μ X (1 / 12) θ (by norm_num) hθ hXm
    (htail m k)
  exact ⟨(hmoment 1 (by norm_num) m k).1, hInt⟩

end Rigidity.Proofs.S2

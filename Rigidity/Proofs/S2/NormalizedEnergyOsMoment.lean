import PercolationClusterHomogenization.Proofs.Density.RescaleExponentialMoment
import PercolationClusterHomogenization.Proofs.Density.NormalizedEnergyOsMoment
import Rigidity.Proofs.S2.NormalizedEnergyStochasticBound

/-!
# Planar density resampling energy with a unit exponential moment

The resampling energy obeys the exponential-moment convention for stochastic bounds, uniformly
at inverse-volume scale.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The planar density resampling energy satisfies an exponential `O₁/₁₂` estimate. -/
theorem planar_density_resampling_energy_expOs (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      (∀ᵐ q : Configuration 2 × Configuration 2
          ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)),
        Summable (fun e : Bond 2 =>
          |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2)) ∧
      Integrable (fun q => Real.exp ((max (planarDensityResamplingEnergy m k q) 0 /
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 12 : ℝ)))
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ∧
      (∫ q, Real.exp ((max (planarDensityResamplingEnergy m k q) 0 /
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 12 : ℝ))
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ≤ 2 := by
  obtain ⟨C, hC, htail⟩ := planar_normalized_density_energy_osBound p hp
  obtain ⟨D, hD, hmoment⟩ := planar_normalized_density_energy_moments p hp
  refine ⟨C * 16 ^ (12 : ℕ), by positivity, fun m k => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let X := planarDensityResamplingEnergy m k
  let θ : ℝ := C / (((3 ^ m : ℕ) : ℝ) ^ 2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hXm : Measurable X := by
    dsimp only [X, planarDensityResamplingEnergy]
    apply Measurable.tsum
    intro e
    have hF := measurable_infiniteClusterCount_triadicCube m k
    have hRes := (measurePreserving_resampleBond 2 p e).measurable
    exact (((hF.comp measurable_fst).div_const _).sub
      ((hF.comp hRes).div_const _)).abs.pow_const 2
  have hsmall := integrable_scaled_exponential_of_osBound μ X (1 / 12) θ (by norm_num) hθ hXm
    (htail m k)
  have hpow : ((16 : ℝ) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) = 16 := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast (x := (16 : ℝ)) (n := 12) (by norm_num) (by norm_num)
  have hEq (q : Configuration 2 × Configuration 2) :
      (max (X q) 0 / ((C * 16 ^ (12 : ℕ)) / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 12 : ℝ) =
        (max (X q) 0 / θ) ^ (1 / 12 : ℝ) / 16 := by
    have hscale : (C * 16 ^ (12 : ℕ)) / (((3 ^ m : ℕ) : ℝ) ^ 2) =
        θ * 16 ^ (12 : ℕ) := by dsimp [θ]; ring
    rw [hscale, div_mul_eq_div_div, Real.div_rpow (div_nonneg (le_max_right _ _) hθ.le)
      (by positivity), hpow]
  refine ⟨(hmoment 1 (by norm_num) m k).1, ?_⟩
  change Integrable (fun q => Real.exp ((max (X q) 0 /
      ((C * 16 ^ (12 : ℕ)) / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 12 : ℝ))) μ ∧
    (∫ q, Real.exp ((max (X q) 0 /
      ((C * 16 ^ (12 : ℕ)) / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 12 : ℝ)) ∂μ) ≤ 2
  simpa only [hEq] using hsmall

end Rigidity.Proofs.S2

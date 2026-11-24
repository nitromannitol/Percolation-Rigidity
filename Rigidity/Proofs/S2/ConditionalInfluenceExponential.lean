import Rigidity.Proofs.S2.IntegratedEnergySeries
import PercolationClusterHomogenization.Proofs.Density.ConditionalInfluenceExponential

/-!
# Exponential moments of averaged planar influences

The sum of the independent-copy averaged squared influences satisfies the exponential-moment
convention for stochastic bounds.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The averaged influence sum satisfies the exponential `O₁/₁₄` moment bound. -/
theorem planar_conditional_influence_sum_expOs (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      Integrable (fun ω => Real.exp ((max (planarConditionalInfluenceEnergy p m k ω) 0 /
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 14 : ℝ))) (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp ((max (planarConditionalInfluenceEnergy p m k ω) 0 /
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 14 : ℝ)) ∂(latticeBondLaw 2 p)) ≤ 2 := by
  obtain ⟨C, hC, htail⟩ := planar_conditional_influence_sum_osBound p hp
  refine ⟨C * 16 ^ (14 : ℕ), by positivity, fun m k => ?_⟩
  let μ := latticeBondLaw 2 p
  let X := planarConditionalInfluenceEnergy p m k
  let θ : ℝ := C / (((3 ^ m : ℕ) : ℝ) ^ 2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hXm : Measurable X := by
    dsimp only [X, planarConditionalInfluenceEnergy]
    apply Measurable.tsum
    intro e
    have hF := measurable_infiniteClusterCount_triadicCube m k
    have hRes := (measurePreserving_resampleBond 2 p e).measurable
    have hmeas := (((hF.comp measurable_fst).div_const ((triadicCube 2 m k).ncard : ℝ)).sub
      ((hF.comp hRes).div_const ((triadicCube 2 m k).ncard : ℝ))).abs.pow_const 2
    exact hmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hsmall := integrable_scaled_exponential_of_osBound μ X (1 / 14) θ (by norm_num) hθ hXm
    ((htail m k).2)
  have hpow : ((16 : ℝ) ^ (14 : ℕ)) ^ (1 / 14 : ℝ) = 16 := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast (x := (16 : ℝ)) (n := 14) (by norm_num) (by norm_num)
  have hEq (ω : Configuration 2) :
      (max (X ω) 0 / ((C * 16 ^ (14 : ℕ)) / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 14 : ℝ) =
        (max (X ω) 0 / θ) ^ (1 / 14 : ℝ) / 16 := by
    have hscale : (C * 16 ^ (14 : ℕ)) / (((3 ^ m : ℕ) : ℝ) ^ 2) =
        θ * 16 ^ (14 : ℕ) := by dsimp [θ]; ring
    rw [hscale, div_mul_eq_div_div, Real.div_rpow (div_nonneg (le_max_right _ _) hθ.le)
      (by positivity), hpow]
  change Integrable (fun ω => Real.exp ((max (X ω) 0 /
      ((C * 16 ^ (14 : ℕ)) / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 14 : ℝ))) μ ∧
    (∫ ω, Real.exp ((max (X ω) 0 /
      ((C * 16 ^ (14 : ℕ)) / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 14 : ℝ)) ∂μ) ≤ 2
  simpa only [hEq] using hsmall

end Rigidity.Proofs.S2

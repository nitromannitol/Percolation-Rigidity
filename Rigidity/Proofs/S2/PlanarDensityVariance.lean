import Rigidity.Proofs.S2.BondEfronStein
import Rigidity.Proofs.S2.ClusterDensityBounds

/-!
# Variance of planar cluster density

The countable Efron–Stein inequality and the resampling-energy estimate give the inverse-volume
variance bound for the normalized infinite-cluster count.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Planar triadic cluster-density fluctuations have inverse-volume variance. -/
theorem planar_cluster_density_variance (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      Integrable (fun ω : Configuration 2 =>
        ((infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) - theta 2 p) ^ 2) (latticeBondLaw 2 p) ∧
      (∫ ω : Configuration 2, (infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
        ((triadicCube 2 m k).ncard : ℝ) - theta 2 p ∂latticeBondLaw 2 p) = 0 ∧
      evariance (fun ω : Configuration 2 =>
        (infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) - theta 2 p) (latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) / 2 := by
  obtain ⟨C, hC, henergy⟩ := planar_normalized_density_resampling_energy_mean p hp
  refine ⟨C, hC, fun m k => ?_⟩
  let μ := latticeBondLaw 2 p
  let F (ω : Configuration 2) : ℝ :=
    (infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
      ((triadicCube 2 m k).ncard : ℝ) - theta 2 p
  have hFm : Measurable F :=
    ((measurable_infiniteClusterCount_triadicCube m k).div_const _).sub_const _
  have hF2 : Integrable (fun ω => F ω ^ 2) μ := by
    refine (integrable_const (1 : ℝ)).mono' (hFm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg (F ω)) (abs_centered_clusterDensity_le_one p m k ω) 2
    simpa only [sq_abs, one_pow] using h
  have hE := bond_evariance_le_resampling_energy 2 p F hFm hF2
  have hEq (q : Configuration 2 × Configuration 2) (e : Bond 2) :
      (F q.1 - F (resampleBond q.1 q.2 e)) ^ 2 =
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
            ((triadicCube 2 m k).ncard : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
            ((triadicCube 2 m k).ncard : ℝ)| ^ 2 := by
    rw [sq_abs]
    dsimp only [F]
    ring
  have hres : (∫⁻ q : Configuration 2 × Configuration 2, ∑' e : Bond 2,
      ENNReal.ofReal ((F q.1 - F (resampleBond q.1 q.2 e)) ^ 2) ∂(μ.prod μ)) ≤
        ENNReal.ofReal (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) := by
    simpa only [hEq] using (henergy m k).1
  exact ⟨hF2, integral_centered_clusterDensity p m k,
    hE.trans (ENNReal.div_le_div_right hres 2)⟩

end Rigidity.Proofs.S2

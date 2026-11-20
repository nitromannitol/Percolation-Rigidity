import Rigidity.Proofs.S2.SummableMomentNorms

/-!
# Moments of the planar density resampling energy

The total squared resampling influence is almost surely summable and has `Lʳ` norm at most a
constant times `r¹²` and the cube volume.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The planar resampling energy has all integer moment norms at the cube-volume scale. -/
theorem planar_density_resampling_energy_moments (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex 2),
      (∀ᵐ q : Configuration 2 × Configuration 2
          ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)),
        Summable (fun e : Bond 2 =>
          |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2)) ∧
      MemLp (fun q : Configuration 2 × Configuration 2 => ∑' e : Bond 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2)
        r ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ∧
      lpNorm (fun q : Configuration 2 × Configuration 2 => ∑' e : Bond 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2)
        r ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ≤
          C * (r : ℝ) ^ 12 * (((3 ^ m : ℕ) : ℝ) + 1) ^ 2 := by
  obtain ⟨C, hC, hroots⟩ := planar_density_influence_moment_roots_quantitative p hp
  refine ⟨C, hC, fun r hr m k => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let f (e : Bond 2) (q : Configuration 2 × Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2
  obtain ⟨hint, hsum, hbound⟩ := hroots r hr m k
  have hm (e : Bond 2) : Measurable (f e) := (measurable_count_influence m k e).pow_const 2
  have hnonneg (e : Bond 2) (q : Configuration 2 × Configuration 2) : 0 ≤ f e q := by
    dsimp [f]; positivity
  have hint' (e : Bond 2) : Integrable (fun q => f e q ^ r) μ := by
    simpa only [f, ← pow_mul] using hint e
  have hsum' : Summable (fun e : Bond 2 => (∫ q, f e q ^ r ∂μ) ^ (1 / (r : ℝ))) := by
    simpa only [f, ← pow_mul] using hsum
  obtain ⟨Y, hY, hYsum, hYnorm⟩ :=
    summable_nonnegative_moment_norms μ r hr f hm hnonneg hint' hsum'
  have hAE : (fun q => ∑' e, f e q) =ᵐ[μ] Y := by
    filter_upwards [hYsum] with q hq
    exact hq.tsum_eq
  have hMem : MemLp (fun q => ∑' e, f e q) r μ := by
    refine ⟨hY.aestronglyMeasurable.congr hAE.symm, ?_⟩
    rw [eLpNorm_congr_ae hAE]
    exact hY.2
  have hNorm : lpNorm (fun q => ∑' e, f e q) r μ = lpNorm Y r μ := by
    rw [← toReal_eLpNorm hMem.aestronglyMeasurable, ← toReal_eLpNorm hY.aestronglyMeasurable,
      eLpNorm_congr_ae hAE]
  refine ⟨?_, hMem, ?_⟩
  · filter_upwards [hYsum] with q hq
    exact hq.summable
  · rw [hNorm]
    exact hYnorm.trans (by simpa only [f, ← pow_mul] using hbound)

end Rigidity.Proofs.S2

import Rigidity.Proofs.S2.PlanarMomentRootRecursion

/-!
# Base moment for planar density

The variance bound supplies the second-moment base of the dyadic recursion.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The squared second-moment norm is bounded at inverse-volume scale. -/
theorem planar_density_moment_root_two (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      planarDensityMomentRoot p m k 2 ≤ C / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hmom⟩ := planar_conditional_influence_energy_moments p hp
  refine ⟨C, hC, fun m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let X := planarDensityRealObservable p m k
  let W := planarConditionalInfluenceEnergy p m k
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hWm : Measurable W := measurable_planarConditionalInfluenceEnergy p m k
  have hW0 (η : Configuration 2) : 0 ≤ W η := by
    apply tsum_nonneg
    intro e
    exact integral_nonneg fun _ => sq_nonneg _
  have hWnorm : lpNorm W 1 μ ≤ C / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
    simpa using (hmom 1 (by norm_num) m k).2
  have hWint : (∫ η, W η ∂μ) = lpNorm W 1 μ := by
    rw [lpNorm_one_eq_integral_norm hWm.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun η => (Real.norm_of_nonneg (hW0 η)).symm
  have hmap : (∫ ω, W (T ω) ∂P) = ∫ η, W η ∂μ := by
    have hm : AEStronglyMeasurable W (Measure.map T P) := by
      rw [hT.map_eq]
      exact hWm.aestronglyMeasurable
    have h := integral_map hT.measurable.aemeasurable hm
    rw [hT.map_eq] at h
    exact h.symm
  have hXprop := planar_density_real_observable_properties p m k
  have hV := planar_density_power_variance_le p hp m k 1
  dsimp only at hV
  have hVar : variance X P = ∫ ω, X ω ^ 2 ∂P := by
    rw [variance_eq_integral hXprop.1.aemeasurable, hXprop.2.2.2]
    simp only [sub_zero]
    rfl
  have hM : planarDensityMomentRoot p m k 2 = ∫ ω, X ω ^ 2 ∂P := by
    dsimp only [planarDensityMomentRoot]
    norm_num
    rfl
  rw [hM, ← hVar]
  calc
    _ ≤ ∫ ω, W (T ω) ∂P := by simpa [X, W, T, P] using hV
    _ = ∫ η, W η ∂μ := hmap
    _ = lpNorm W 1 μ := hWint
    _ ≤ _ := hWnorm

end Rigidity.Proofs.S2

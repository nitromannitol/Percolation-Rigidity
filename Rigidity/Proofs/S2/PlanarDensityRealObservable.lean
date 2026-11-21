import Rigidity.Proofs.S2.PlanarConditionalVarianceMoment

/-!
# The planar density observable in the real Bernoulli encoding

The encoded observable is bounded, integrable, and centered.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External

/-- The real-encoded planar density fluctuation is measurable, bounded, and centered. -/
theorem planar_density_real_observable_properties (p : unitInterval) (m : ℕ) (k : Vertex 2) :
    let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
    Measurable (planarDensityRealObservable p m k) ∧
      (∀ ω, |planarDensityRealObservable p m k ω| ≤ 1) ∧
      Integrable (planarDensityRealObservable p m k) P ∧
      (∫ ω, planarDensityRealObservable p m k ω ∂P) = 0 := by
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let F : Configuration 2 → ℝ := fun ω =>
    (infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
      ((triadicCube 2 m k).ncard : ℝ) - theta 2 p
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hFm : Measurable F := ((measurable_infiniteClusterCount_triadicCube m k).div_const _).sub_const _
  have hXm : Measurable (planarDensityRealObservable p m k) := hFm.comp hT.measurable
  have hbound (ω : Bond 2 → ℝ) : |planarDensityRealObservable p m k ω| ≤ 1 :=
    abs_centered_clusterDensity_le_one p m k (T ω)
  have hXi : Integrable (planarDensityRealObservable p m k) P := by
    refine (integrable_const (1 : ℝ)).mono' hXm.aestronglyMeasurable ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, norm_one] using hbound ω
  refine ⟨hXm, hbound, hXi, ?_⟩
  have hmap : (∫ ω, planarDensityRealObservable p m k ω ∂P) = ∫ η, F η ∂μ := by
    have hm : AEStronglyMeasurable F (Measure.map T P) := by
      rw [hT.map_eq]
      exact hFm.aestronglyMeasurable
    have h := integral_map hT.measurable.aemeasurable hm
    rw [hT.map_eq] at h
    exact h.symm
  rw [hmap]
  exact integral_centered_clusterDensity p m k

end Rigidity.Proofs.S2

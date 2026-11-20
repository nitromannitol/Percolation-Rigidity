import Rigidity.Proofs.S2.PlanarDensityRealObservable

/-!
# Transfer of planar density concentration between Bernoulli encodings

A stochastic exponential-moment estimate for the real encoding transfers to the Boolean bond
law.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External

/-- Transfer a planar density exponential-moment estimate from the real Bernoulli product. -/
theorem planar_density_isOsBond_of_real_encoding (p : unitInterval) (m : ℕ) (k : Vertex 2)
    (s θ : ℝ)
    (h : let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
      Integrable (fun ω => Real.exp ((max (|planarDensityRealObservable p m k ω| / θ) 0) ^ s)) P ∧
      (∫ ω, Real.exp ((max (|planarDensityRealObservable p m k ω| / θ) 0) ^ s) ∂P) ≤ 2) :
    IsOsBond 2 p
      (fun ω => |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
        ((triadicCube 2 m k).ncard : ℝ) - theta 2 p|) s θ := by
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let f : Configuration 2 → ℝ := fun ω => Real.exp ((max
    (|(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
      ((triadicCube 2 m k).ncard : ℝ) - theta 2 p| / θ) 0) ^ s)
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hf : Measurable f := by
    dsimp only [f]
    have hc := measurable_infiniteClusterCount_triadicCube m k
    exact (((((hc.div_const _).sub_const _).abs.div_const _).max measurable_const).pow_const _).exp
  have hi : Integrable f μ := by
    rw [← hT.map_eq]
    apply (integrable_map_measure hf.aestronglyMeasurable hT.measurable.aemeasurable).2
    exact h.1
  have heq : (∫ ω, f ω ∂μ) = ∫ ω, f (T ω) ∂P := by
    have hf' : AEStronglyMeasurable f (Measure.map T P) := by
      rw [hT.map_eq]
      exact hf.aestronglyMeasurable
    have hmap := integral_map hT.measurable.aemeasurable hf'
    rw [hT.map_eq] at hmap
    exact hmap
  exact ⟨hi, heq ▸ h.2⟩

end Rigidity.Proofs.S2

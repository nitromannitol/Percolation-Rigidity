import Rigidity.Proofs.S2.PlanarConditionalVariance

/-!
# Exponential moment of planar conditional variance

The conditional variance sum has the inverse-volume stochastic bound used in the density
concentration argument.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External

/-- Centered planar density in the real Bernoulli product encoding. -/
noncomputable def planarDensityRealObservable (p : unitInterval) (m : ℕ) (k : Vertex 2)
    (ω : Bond 2 → ℝ) : ℝ :=
  (infiniteClusterCount (triadicCube 2 m k) (bernoulliRealConfiguration ω) : ℝ) /
    ((triadicCube 2 m k).ncard : ℝ) - theta 2 p

/-- Sum of the squared one-bond conditional fluctuations of the planar density. -/
noncomputable def planarDensityConditionalVariance (p : unitInterval) (m : ℕ) (k : Vertex 2)
    (ω : Bond 2 → ℝ) : ℝ :=
  ∑' e : Bond 2, (planarDensityRealObservable p m k ω -
    MeasureTheory.condExp (coordAlg ({e}ᶜ : Set (Bond 2)))
      (Measure.infinitePi fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
      (planarDensityRealObservable p m k) ω) ^ 2

/-- The planar conditional variance has an exponential `O₁/₁₄` bound at inverse-volume scale. -/
theorem planar_density_conditional_variance_expOs (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
      (∀ᵐ ω ∂P, Summable (fun e : Bond 2 =>
        (planarDensityRealObservable p m k ω -
          MeasureTheory.condExp (coordAlg ({e}ᶜ : Set (Bond 2))) P
            (planarDensityRealObservable p m k) ω) ^ 2)) ∧
      Integrable (fun ω => Real.exp ((max (planarDensityConditionalVariance p m k ω) 0 /
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 14 : ℝ))) P ∧
      (∫ ω, Real.exp ((max (planarDensityConditionalVariance p m k ω) 0 /
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))) ^ (1 / 14 : ℝ)) ∂P) ≤ 2 := by
  obtain ⟨C, hC, hmoment⟩ := planar_conditional_influence_sum_expOs p hp
  refine ⟨C, hC, fun m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let X := planarDensityRealObservable p m k
  let V := planarDensityConditionalVariance p m k
  let W := planarConditionalInfluenceEnergy p m k
  let θ : ℝ := C / (((3 ^ m : ℕ) : ℝ) ^ 2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hXm : Measurable X := by
    dsimp only [X, planarDensityRealObservable]
    exact (((measurable_infiniteClusterCount_triadicCube m k).comp hT.measurable).div_const _).sub_const _
  have hVm : Measurable V := by
    dsimp only [V, planarDensityConditionalVariance]
    apply Measurable.tsum
    intro e
    have hc : Measurable (MeasureTheory.condExp (coordAlg ({e}ᶜ : Set (Bond 2))) P X) :=
      (stronglyMeasurable_condExp.mono (coordAlg_le _)).measurable
    exact (hXm.sub hc).pow_const 2
  have hcomp : ∀ᵐ ω ∂P, V ω ≤ W (T ω) := by
    filter_upwards [planar_density_conditional_variance_le_energy p hp m k] with ω hω
    exact hω.2
  have hmeas : Measurable (fun ω => Real.exp ((max (V ω) 0 / θ) ^ (1 / 14 : ℝ))) := by
    fun_prop
  have hbound : ∀ᵐ ω ∂P, Real.exp ((max (V ω) 0 / θ) ^ (1 / 14 : ℝ)) ≤
      Real.exp ((max (W (T ω)) 0 / θ) ^ (1 / 14 : ℝ)) := by
    filter_upwards [hcomp] with ω hω
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (div_nonneg (le_max_right _ _) hθ.le)
      (div_le_div_of_nonneg_right (max_le_max hω le_rfl) hθ.le) (by norm_num)
  have hmajor : Integrable (fun ω => Real.exp ((max (W (T ω)) 0 / θ) ^ (1 / 14 : ℝ))) P :=
    hT.integrable_comp_of_integrable (hmoment m k).1
  have hminor : Integrable (fun ω => Real.exp ((max (V ω) 0 / θ) ^ (1 / 14 : ℝ))) P := by
    refine hmajor.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hω
  refine ⟨?_, hminor, ?_⟩
  · filter_upwards [planar_density_conditional_variance_le_energy p hp m k] with ω hω
    exact hω.1
  · calc
      _ ≤ ∫ ω, Real.exp ((max (W (T ω)) 0 / θ) ^ (1 / 14 : ℝ)) ∂P :=
        integral_mono_ae hminor hmajor hbound
      _ = ∫ η, Real.exp ((max (W η) 0 / θ) ^ (1 / 14 : ℝ)) ∂μ :=
        by
          have hm : AEStronglyMeasurable
              (fun η => Real.exp ((max (W η) 0 / θ) ^ (1 / 14 : ℝ))) (Measure.map T P) := by
            rw [hT.map_eq]
            exact (hmoment m k).1.aestronglyMeasurable
          have h := integral_map hT.measurable.aemeasurable hm
          rw [hT.map_eq] at h
          exact h.symm
      _ ≤ 2 := (hmoment m k).2

end Rigidity.Proofs.S2

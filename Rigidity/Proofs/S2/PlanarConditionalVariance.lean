import Rigidity.Proofs.S2.ConditionalResamplingJensen
import Rigidity.Proofs.S2.ConditionalInfluenceExponential
import Rigidity.Proofs.S2.BernoulliRealEncoding
import Rigidity.Proofs.S2.ClusterDensityBounds

/-!
# Planar density conditional variance

The sum of squared coordinate fluctuations is controlled by the averaged resampling energy.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Conditional variance of the planar density is bounded by the averaged resampling energy. -/
theorem planar_density_conditional_variance_le_energy (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (m : ℕ) (k : Vertex 2) :
    let ν := bernoulliMeasure (1 : ℝ) 0 p
    let P := Measure.infinitePi (fun _ : Bond 2 => ν)
    let X : (Bond 2 → ℝ) → ℝ := fun ω =>
      (infiniteClusterCount (triadicCube 2 m k) (bernoulliRealConfiguration ω) : ℝ) /
        ((triadicCube 2 m k).ncard : ℝ) - theta 2 p
    ∀ᵐ ω ∂P,
      Summable (fun e : Bond 2 =>
        (X ω - MeasureTheory.condExp (coordAlg ({e}ᶜ : Set (Bond 2))) P X ω) ^ 2) ∧
      (∑' e : Bond 2,
        (X ω - MeasureTheory.condExp (coordAlg ({e}ᶜ : Set (Bond 2))) P X ω) ^ 2) ≤
          planarConditionalInfluenceEnergy p m k (bernoulliRealConfiguration ω) := by
  classical
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  let P := Measure.infinitePi (fun _ : Bond 2 => ν)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let X : (Bond 2 → ℝ) → ℝ := fun ω =>
    (infiniteClusterCount (triadicCube 2 m k) (T ω) : ℝ) /
      ((triadicCube 2 m k).ncard : ℝ) - theta 2 p
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hXm : Measurable X :=
    (((measurable_infiniteClusterCount_triadicCube m k).comp hT.measurable).div_const _).sub_const _
  have hXi : Integrable X P := by
    refine (integrable_const (1 : ℝ)).mono' hXm.aestronglyMeasurable ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, norm_one] using
      abs_centered_clusterDensity_le_one p m k (T ω)
  have hj : ∀ᵐ ω ∂P, ∀ e : Bond 2,
      ENNReal.ofReal ((X ω - MeasureTheory.condExp (coordAlg ({e}ᶜ : Set (Bond 2))) P X ω) ^ 2) ≤
        ∫⁻ η : Bond 2 → ℝ, ENNReal.ofReal ((X ω - X (Function.update ω e (η e))) ^ 2) ∂P :=
    ae_all_iff.mpr fun e => conditional_fluctuation_le_resampling ν X hXm hXi e
  have hs := hT.quasiMeasurePreserving.ae (planar_integrated_density_energy_series p hp m k)
  filter_upwards [hj, hs] with ω hω hseries
  let a (e : Bond 2) : ℝ :=
    (X ω - MeasureTheory.condExp (coordAlg ({e}ᶜ : Set (Bond 2))) P X ω) ^ 2
  let b (e : Bond 2) : ℝ := ∫ η : Configuration 2,
    |(infiniteClusterCount (triadicCube 2 m k) (T ω) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond (T ω) η e) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂μ
  have hle (e : Bond 2) : a e ≤ b e := by
    let g (η : Configuration 2) : ℝ :=
      |(infiniteClusterCount (triadicCube 2 m k) (T ω) : ℝ) /
            ((triadicCube 2 m k).ncard : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond (T ω) η e) : ℝ) /
            ((triadicCube 2 m k).ncard : ℝ)| ^ 2
    have hgm : Measurable g := by
      dsimp only [g]
      have hF := measurable_infiniteClusterCount_triadicCube m k
      have hRes := (measurePreserving_resampleBond 2 p e).measurable
      exact (measurable_const.sub ((hF.comp (hRes.comp (measurable_const.prodMk measurable_id))).div_const _)).abs.pow_const 2
    have hgeq (η : Bond 2 → ℝ) :
        (X ω - X (Function.update ω e (η e))) ^ 2 = g (T η) := by
      dsimp only [X, g, T]
      rw [bernoulliRealConfiguration_update]
      have he : resampleBond (bernoulliRealConfiguration ω) (bernoulliRealConfiguration η) e =
          Function.update (bernoulliRealConfiguration ω) e (bernoulliRealBit (η e)) := by
        funext f
        by_cases hf : f = e <;>
          simp [resampleBond, bernoulliRealConfiguration, hf]
      rw [he, sq_abs]
      ring
    have hmap : (∫⁻ η : Bond 2 → ℝ,
        ENNReal.ofReal ((X ω - X (Function.update ω e (η e))) ^ 2) ∂P) =
        ∫⁻ η : Configuration 2, ENNReal.ofReal (g η) ∂μ := by
      simp_rw [hgeq]
      exact hT.lintegral_comp hgm.ennreal_ofReal
    have hbpos : 0 ≤ b e := integral_nonneg fun η => sq_nonneg _
    apply (ENNReal.ofReal_le_ofReal_iff hbpos).mp
    calc
      ENNReal.ofReal (a e) ≤ ∫⁻ η : Bond 2 → ℝ,
          ENNReal.ofReal ((X ω - X (Function.update ω e (η e))) ^ 2) ∂P := hω e
      _ = ∫⁻ η : Configuration 2, ENNReal.ofReal (g η) ∂μ := hmap
      _ = ENNReal.ofReal (b e) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal (hseries.1 e) (Filter.Eventually.of_forall fun η => sq_nonneg _)
  have hsum : Summable b := hseries.2.1
  have hasum : Summable a := Summable.of_nonneg_of_le (fun e => sq_nonneg _) hle hsum
  refine ⟨hasum, ?_⟩
  exact (Summable.tsum_le_tsum hle hasum hsum)

end Rigidity.Proofs.S2

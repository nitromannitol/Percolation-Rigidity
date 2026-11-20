import Rigidity.Proofs.S2.WeightedResamplingTonelli
import Rigidity.Proofs.S2.PlanarVarianceMoments

/-!
# Total resampling energy of planar density

The extended energy of the real-encoded observable agrees almost surely with the sum of
Boolean resampling influences.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The total real-product resampling energy is the encoded planar averaged influence sum. -/
theorem planar_total_resampling_energy_eq (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (m : ℕ) (k : Vertex 2) :
    let ν := bernoulliMeasure (1 : ℝ) 0 p
    let P := Measure.infinitePi (fun _ : Bond 2 => ν)
    ∀ᵐ ω ∂P, totalResamplingEnergy ν (planarDensityRealObservable p m k) ω =
      ENNReal.ofReal (planarConditionalInfluenceEnergy p m k (bernoulliRealConfiguration ω)) := by
  classical
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  let P := Measure.infinitePi (fun _ : Bond 2 => ν)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let X := planarDensityRealObservable p m k
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hs := hT.quasiMeasurePreserving.ae (planar_integrated_density_energy_series p hp m k)
  filter_upwards [hs] with ω hseries
  let g (e : Bond 2) (η : Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) (T ω) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond (T ω) η e) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ)| ^ 2
  have hgm (e : Bond 2) : Measurable (g e) := by
    dsimp only [g]
    have hF := measurable_infiniteClusterCount_triadicCube m k
    have hRes := (measurePreserving_resampleBond 2 p e).measurable
    exact (measurable_const.sub ((hF.comp (hRes.comp (measurable_const.prodMk measurable_id))).div_const _)).abs.pow_const 2
  have hgeq (e : Bond 2) (η : Bond 2 → ℝ) :
      (X ω - X (Function.update ω e (η e))) ^ 2 = g e (T η) := by
    dsimp only [X, planarDensityRealObservable, g, T]
    rw [bernoulliRealConfiguration_update]
    have he : resampleBond (bernoulliRealConfiguration ω) (bernoulliRealConfiguration η) e =
        Function.update (bernoulliRealConfiguration ω) e (bernoulliRealBit (η e)) := by
      funext f
      by_cases hf : f = e <;> simp [resampleBond, bernoulliRealConfiguration, hf]
    rw [he, sq_abs]
    ring
  have heach (e : Bond 2) : (∫⁻ η : Bond 2 → ℝ,
      ENNReal.ofReal ((X ω - X (Function.update ω e (η e))) ^ 2) ∂P) =
      ENNReal.ofReal (∫ η, g e η ∂μ) := by
    simp_rw [hgeq]
    rw [hT.lintegral_comp (hgm e).ennreal_ofReal]
    exact (ofReal_integral_eq_lintegral_ofReal (hseries.1 e)
      (Filter.Eventually.of_forall fun η => sq_nonneg _)).symm
  change (∑' e : Bond 2, ∫⁻ η : Bond 2 → ℝ,
    ENNReal.ofReal ((X ω - X (Function.update ω e (η e))) ^ 2) ∂P) =
      ENNReal.ofReal (∑' e : Bond 2, ∫ η, g e η ∂μ)
  simp_rw [heach]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun e => integral_nonneg fun η => sq_nonneg _)
    hseries.2.1).symm

end Rigidity.Proofs.S2

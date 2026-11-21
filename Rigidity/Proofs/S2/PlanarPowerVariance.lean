import Rigidity.Proofs.S2.PlanarTotalResamplingEnergy

/-!
# Variance of powers of planar density

The variance of each power of the centered planar density is bounded by a weighted averaged
resampling energy.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- A power of the planar density has variance bounded by its weighted resampling energy. -/
theorem planar_density_power_variance_le (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (m : ℕ) (k : Vertex 2) (n : ℕ) :
    let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
    variance (fun ω => planarDensityRealObservable p m k ω ^ n) P ≤ (n : ℝ) ^ 2 *
      ∫ ω, |planarDensityRealObservable p m k ω| ^ (2 * (n - 1)) *
        planarConditionalInfluenceEnergy p m k (bernoulliRealConfiguration ω) ∂P := by
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  let P := Measure.infinitePi (fun _ : Bond 2 => ν)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let X := planarDensityRealObservable p m k
  let W := planarConditionalInfluenceEnergy p m k
  let H (ω : Bond 2 → ℝ) := |X ω| ^ (2 * (n - 1)) * W (T ω)
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hXm : Measurable X := (planar_density_real_observable_properties p m k).1
  have hXbound : ∀ ω, |X ω| ≤ 1 := (planar_density_real_observable_properties p m k).2.1
  have hXpow : Integrable (fun ω => (X ω ^ n) ^ 2) P := by
    refine (integrable_const (1 : ℝ)).mono' ((hXm.pow_const n).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 : |X ω| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) (hXbound ω)
    have h2 : (|X ω| ^ n) ^ 2 ≤ 1 := pow_le_one₀ (pow_nonneg (abs_nonneg _) _) h1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω ^ n))]
    rw [← abs_pow, sq_abs] at h2
    simpa only [norm_one] using h2
  have hXmem : MemLp (fun ω => X ω ^ n) 2 P :=
    (memLp_two_iff_integrable_sq (hXm.pow_const n).aestronglyMeasurable).2 hXpow
  obtain ⟨C, hC, hmom⟩ := planar_conditional_influence_energy_moments p hp
  have hWi : Integrable W μ := by
    have h := (hmom 1 (by norm_num) m k).1
    exact memLp_one_iff_integrable.mp (by simpa using h)
  have hWTi : Integrable (W ∘ T) P := hT.integrable_comp_of_integrable hWi
  have hW0 (η : Configuration 2) : 0 ≤ W η := by
    apply tsum_nonneg
    intro e
    exact integral_nonneg fun _ => sq_nonneg _
  have hHm : Measurable H := ((hXm.abs.pow_const _).mul
    ((measurable_planarConditionalInfluenceEnergy p m k).comp hT.measurable))
  have hHi : Integrable H P := by
    refine hWTi.mono' hHm.aestronglyMeasurable ?_
    filter_upwards with ω
    have hw : |X ω| ^ (2 * (n - 1)) ≤ 1 := pow_le_one₀ (abs_nonneg _) (hXbound ω)
    have h0 : 0 ≤ H ω := mul_nonneg (pow_nonneg (abs_nonneg _) _) (hW0 (T ω))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact (mul_le_mul_of_nonneg_right hw (hW0 (T ω))).trans_eq (one_mul _)
  have hE := evariance_pow_le_total_resampling ν X hXm n hXpow
  dsimp only at hE
  have hEnergy := planar_total_resampling_energy_eq p hp m k
  have hIntegral : (∫⁻ ω : Bond 2 → ℝ, ENNReal.ofReal (|X ω| ^ (2 * (n - 1))) *
      totalResamplingEnergy ν X ω ∂P) = ENNReal.ofReal (∫ ω, H ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hHi (Filter.Eventually.of_forall fun ω =>
      mul_nonneg (pow_nonneg (abs_nonneg _) _) (hW0 (T ω)))]
    apply lintegral_congr_ae
    filter_upwards [hEnergy] with ω hω
    rw [hω, ← ENNReal.ofReal_mul (by positivity)]
  rw [hIntegral, ← ENNReal.ofReal_mul (by positivity), ← ofReal_variance hXmem] at hE
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (integral_nonneg fun ω =>
    mul_nonneg (pow_nonneg (abs_nonneg _) _) (hW0 (T ω))))).mp
  exact hE

end Rigidity.Proofs.S2

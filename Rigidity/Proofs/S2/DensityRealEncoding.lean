import Rigidity.Proofs.S2.DensityResamplingEnergy
import Rigidity.Proofs.S2.BernoulliRealEncoding
import Rigidity.Proofs.S2.WeightedResamplingTonelli
import Rigidity.Proofs.S2.ClusterDensityBounds

/-!
# The triadic cluster density in the real Bernoulli encoding

The centered density of the infinite cluster in a triadic cube, read through the real encoding
of the bond configuration, is bounded and centered; its total resampling energy is the averaged
influence energy, and the variance of each of its powers is bounded by the Efron–Stein energy
weighted by the lower power.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

variable {d : ℕ} {β : ℕ}

/-- The centered triadic cluster density in the real Bernoulli product encoding. -/
noncomputable def densityRealObservable (p : unitInterval) (m : ℕ) (k : Vertex d)
    (ω : Bond d → ℝ) : ℝ :=
  (infiniteClusterCount (triadicCube d m k) (bernoulliRealConfiguration ω) : ℝ) /
    ((triadicCube d m k).ncard : ℝ) - theta d p

/-- The real-encoded density fluctuation is measurable, bounded by one, and centered. -/
theorem density_real_observable_properties (p : unitInterval) (m : ℕ) (k : Vertex d) :
    let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
    Measurable (densityRealObservable p m k) ∧
      (∀ ω, |densityRealObservable p m k ω| ≤ 1) ∧
      Integrable (densityRealObservable p m k) P ∧
      (∫ ω, densityRealObservable p m k ω ∂P) = 0 := by
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw d p
  let T := bernoulliRealConfiguration (d := d)
  let F : Configuration d → ℝ := fun ω =>
    (infiniteClusterCount (triadicCube d m k) ω : ℝ) /
      ((triadicCube d m k).ncard : ℝ) - theta d p
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration d p
  have hFm : Measurable F :=
    ((measurable_infiniteClusterCount_triadicCube m k).div_const _).sub_const _
  have hXm : Measurable (densityRealObservable p m k) := hFm.comp hT.measurable
  have hbound (ω : Bond d → ℝ) : |densityRealObservable p m k ω| ≤ 1 :=
    abs_centered_clusterDensity_le_one p m k (T ω)
  have hXi : Integrable (densityRealObservable p m k) P := by
    refine (integrable_const (1 : ℝ)).mono' hXm.aestronglyMeasurable ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, norm_one] using hbound ω
  refine ⟨hXm, hbound, hXi, ?_⟩
  have hmap : (∫ ω, densityRealObservable p m k ω ∂P) = ∫ η, F η ∂μ := by
    have hm : AEStronglyMeasurable F (Measure.map T P) := by
      rw [hT.map_eq]
      exact hFm.aestronglyMeasurable
    have h := integral_map hT.measurable.aemeasurable hm
    rw [hT.map_eq] at h
    exact h.symm
  rw [hmap]
  exact integral_centered_clusterDensity p m k

/-- An exponential-moment estimate for the real encoding transfers to the Boolean bond law. -/
theorem density_isOsBond_of_real_encoding (p : unitInterval) (m : ℕ) (k : Vertex d)
    (s θ : ℝ)
    (h : let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
      Integrable (fun ω => Real.exp ((max (|densityRealObservable p m k ω| / θ) 0) ^ s)) P ∧
      (∫ ω, Real.exp ((max (|densityRealObservable p m k ω| / θ) 0) ^ s) ∂P) ≤ 2) :
    IsOsBond d p
      (fun ω => |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
        ((triadicCube d m k).ncard : ℝ) - theta d p|) s θ := by
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw d p
  let T := bernoulliRealConfiguration (d := d)
  let f : Configuration d → ℝ := fun ω => Real.exp ((max
    (|(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
      ((triadicCube d m k).ncard : ℝ) - theta d p| / θ) 0) ^ s)
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration d p
  have hf : Measurable f := by
    dsimp only [f]
    have hc := measurable_infiniteClusterCount_triadicCube (d := d) m k
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

/-- The total real-product resampling energy of the encoded density is the averaged influence
energy, almost surely. -/
theorem density_total_resampling_energy_eq {p : unitInterval}
    (h : DensityInfluenceRootBound d p β) (m : ℕ) (k : Vertex d) :
    let ν := bernoulliMeasure (1 : ℝ) 0 p
    let P := Measure.infinitePi (fun _ : Bond d => ν)
    ∀ᵐ ω ∂P, totalResamplingEnergy ν (densityRealObservable p m k) ω =
      ENNReal.ofReal (densityConditionalInfluenceEnergy p m k (bernoulliRealConfiguration ω)) := by
  classical
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  let P := Measure.infinitePi (fun _ : Bond d => ν)
  let μ := latticeBondLaw d p
  let T := bernoulliRealConfiguration (d := d)
  let X := densityRealObservable p m k
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration d p
  have hs := hT.quasiMeasurePreserving.ae (density_integrated_energy_series h m k)
  filter_upwards [hs] with ω hseries
  let g (e : Bond d) (η : Configuration d) : ℝ :=
    |(infiniteClusterCount (triadicCube d m k) (T ω) : ℝ) /
          ((triadicCube d m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond (T ω) η e) : ℝ) /
          ((triadicCube d m k).ncard : ℝ)| ^ 2
  have hgm (e : Bond d) : Measurable (g e) := by
    dsimp only [g]
    have hF := measurable_infiniteClusterCount_triadicCube (d := d) m k
    have hRes := (measurePreserving_resampleBond d p e).measurable
    exact (measurable_const.sub ((hF.comp (hRes.comp
      (measurable_const.prodMk measurable_id))).div_const _)).abs.pow_const 2
  have hgeq (e : Bond d) (η : Bond d → ℝ) :
      (X ω - X (Function.update ω e (η e))) ^ 2 = g e (T η) := by
    dsimp only [X, densityRealObservable, g, T]
    rw [bernoulliRealConfiguration_update]
    have he : resampleBond (bernoulliRealConfiguration ω) (bernoulliRealConfiguration η) e =
        Function.update (bernoulliRealConfiguration ω) e (bernoulliRealBit (η e)) := by
      funext f
      by_cases hf : f = e <;> simp [resampleBond, bernoulliRealConfiguration, hf]
    rw [he, sq_abs]
    ring
  have heach (e : Bond d) : (∫⁻ η : Bond d → ℝ,
      ENNReal.ofReal ((X ω - X (Function.update ω e (η e))) ^ 2) ∂P) =
      ENNReal.ofReal (∫ η, g e η ∂μ) := by
    simp_rw [hgeq]
    rw [hT.lintegral_comp (hgm e).ennreal_ofReal]
    exact (ofReal_integral_eq_lintegral_ofReal (hseries.1 e)
      (Filter.Eventually.of_forall fun η => sq_nonneg _)).symm
  change (∑' e : Bond d, ∫⁻ η : Bond d → ℝ,
    ENNReal.ofReal ((X ω - X (Function.update ω e (η e))) ^ 2) ∂P) =
      ENNReal.ofReal (∑' e : Bond d, ∫ η, g e η ∂μ)
  simp_rw [heach]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun e => integral_nonneg fun η => sq_nonneg _)
    hseries.2.1).symm

/-- The variance of a power of the encoded density is bounded by its weighted averaged
influence energy. -/
theorem density_power_variance_le {p : unitInterval} (h : DensityInfluenceRootBound d p β)
    (m : ℕ) (k : Vertex d) (n : ℕ) :
    let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
    variance (fun ω => densityRealObservable p m k ω ^ n) P ≤ (n : ℝ) ^ 2 *
      ∫ ω, |densityRealObservable p m k ω| ^ (2 * (n - 1)) *
        densityConditionalInfluenceEnergy p m k (bernoulliRealConfiguration ω) ∂P := by
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  let P := Measure.infinitePi (fun _ : Bond d => ν)
  let μ := latticeBondLaw d p
  let T := bernoulliRealConfiguration (d := d)
  let X := densityRealObservable p m k
  let W := densityConditionalInfluenceEnergy p m k
  let H (ω : Bond d → ℝ) := |X ω| ^ (2 * (n - 1)) * W (T ω)
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration d p
  have hXm : Measurable X := (density_real_observable_properties p m k).1
  have hXbound : ∀ ω, |X ω| ≤ 1 := (density_real_observable_properties p m k).2.1
  have hXpow : Integrable (fun ω => (X ω ^ n) ^ 2) P := by
    refine (integrable_const (1 : ℝ)).mono'
      ((hXm.pow_const n).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 : |X ω| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) (hXbound ω)
    have h2 : (|X ω| ^ n) ^ 2 ≤ 1 := pow_le_one₀ (pow_nonneg (abs_nonneg _) _) h1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω ^ n))]
    rw [← abs_pow, sq_abs] at h2
    simpa only [norm_one] using h2
  have hXmem : MemLp (fun ω => X ω ^ n) 2 P :=
    (memLp_two_iff_integrable_sq (hXm.pow_const n).aestronglyMeasurable).2 hXpow
  obtain ⟨C, hC, hmom⟩ := density_conditional_influence_energy_moments h
  have hWi : Integrable W μ := by
    have h1 := (hmom 1 (by norm_num) m k).1
    exact memLp_one_iff_integrable.mp (by simpa using h1)
  have hWTi : Integrable (W ∘ T) P := hT.integrable_comp_of_integrable hWi
  have hW0 (η : Configuration d) : 0 ≤ W η := densityConditionalInfluenceEnergy_nonneg p m k η
  have hHm : Measurable H := ((hXm.abs.pow_const _).mul
    ((measurable_densityConditionalInfluenceEnergy p m k).comp hT.measurable))
  have hHi : Integrable H P := by
    refine hWTi.mono' hHm.aestronglyMeasurable ?_
    filter_upwards with ω
    have hw : |X ω| ^ (2 * (n - 1)) ≤ 1 := pow_le_one₀ (abs_nonneg _) (hXbound ω)
    have h0 : 0 ≤ H ω := mul_nonneg (pow_nonneg (abs_nonneg _) _) (hW0 (T ω))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact (mul_le_mul_of_nonneg_right hw (hW0 (T ω))).trans_eq (one_mul _)
  have hE := evariance_pow_le_total_resampling ν X hXm n hXpow
  dsimp only at hE
  have hEnergy := density_total_resampling_energy_eq h m k
  have hIntegral : (∫⁻ ω : Bond d → ℝ, ENNReal.ofReal (|X ω| ^ (2 * (n - 1))) *
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

import Rigidity.Proofs.S2.SummableMomentNorms
import Rigidity.Proofs.S2.ConditionalProductIntegral
import Rigidity.Proofs.S2.NonnegativeIntegralSeries

/-!
# Resampling energy of the triadic cluster density in every dimension

Suppose that the `L^{2r}` moments of the single-bond influences on the infinite-cluster count of a
triadic cube `□_m` have summable `r`-th roots, with sum at most `C r^β (3^m + 1)^d`. Then the total
squared resampling influence of the normalized density `|𝒞_∞ ∩ □_m| / |□_m|` has `L^r` norm at
most `C' r^β 3^{-dm}`, and so has its average over the resampled configuration.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

variable {d : ℕ} {p : unitInterval} {β : ℕ}

/-- The `r`-th roots of the `L^{2r}` moments of the single-bond influences on the infinite-cluster
count of a triadic cube of size `3^m` are summable over the bonds, with sum at most
`C r^β (3^m + 1)^d`. -/
def DensityInfluenceRootBound (d : ℕ) (p : unitInterval) (β : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex d),
    Summable (fun e : Bond d => (∫ q : Configuration d × Configuration d,
      |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ (2 * r)
      ∂((latticeBondLaw d p).prod (latticeBondLaw d p))) ^ (1 / (r : ℝ))) ∧
    (∑' e : Bond d, (∫ q : Configuration d × Configuration d,
      |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ (2 * r)
      ∂((latticeBondLaw d p).prod (latticeBondLaw d p))) ^ (1 / (r : ℝ))) ≤
      C * (r : ℝ) ^ β * (((3 ^ m : ℕ) : ℝ) + 1) ^ d

/-- The total squared resampling influence on the cluster count has `L^r` norm at most
`C r^β (3^m + 1)^d`. -/
theorem density_resampling_energy_moments (h : DensityInfluenceRootBound d p β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex d),
      (∀ᵐ q : Configuration d × Configuration d
          ∂((latticeBondLaw d p).prod (latticeBondLaw d p)),
        Summable (fun e : Bond d =>
          |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
            (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2)) ∧
      MemLp (fun q : Configuration d × Configuration d => ∑' e : Bond d,
        |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2)
        r ((latticeBondLaw d p).prod (latticeBondLaw d p)) ∧
      lpNorm (fun q : Configuration d × Configuration d => ∑' e : Bond d,
        |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2)
        r ((latticeBondLaw d p).prod (latticeBondLaw d p)) ≤
          C * (r : ℝ) ^ β * (((3 ^ m : ℕ) : ℝ) + 1) ^ d := by
  obtain ⟨C, hC, hroots⟩ := h
  refine ⟨C, hC, fun r hr m k => ?_⟩
  let μ := (latticeBondLaw d p).prod (latticeBondLaw d p)
  let f (e : Bond d) (q : Configuration d × Configuration d) : ℝ :=
    |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2
  obtain ⟨hsum, hbound⟩ := hroots r hr m k
  have hm (e : Bond d) : Measurable (f e) := (measurable_count_influence m k e).pow_const 2
  have hnonneg (e : Bond d) (q : Configuration d × Configuration d) : 0 ≤ f e q := by
    dsimp [f]; positivity
  have hint' (e : Bond d) : Integrable (fun q => f e q ^ r) μ := by
    simpa only [f, ← pow_mul] using integrable_count_influence_pow p m k e (2 * r)
  have hsum' : Summable (fun e : Bond d => (∫ q, f e q ^ r ∂μ) ^ (1 / (r : ℝ))) := by
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

/-- The total squared influence of the normalized triadic cluster density. -/
noncomputable def densityResamplingEnergy (m : ℕ) (k : Vertex d)
    (q : Configuration d × Configuration d) : ℝ :=
  ∑' e : Bond d,
    |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) /
          ((triadicCube d m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ) /
          ((triadicCube d m k).ncard : ℝ)| ^ 2

/-- The number of vertices of a triadic cube of size `3^m` is `(3^m)^d`. -/
theorem ncard_triadicCube_eq_pow (m : ℕ) (k : Vertex d) :
    ((triadicCube d m k).ncard : ℝ) = (((3 ^ m : ℕ) : ℝ)) ^ d := by
  rw [ncard_triadicCube]
  push_cast
  rw [show d * m = m * d by ring, pow_mul]

/-- The normalized resampling energy has `L^r` norm at most `C r^β 3^{-dm}`. -/
theorem density_normalized_energy_moments (h : DensityInfluenceRootBound d p β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex d),
      (∀ᵐ q : Configuration d × Configuration d
          ∂((latticeBondLaw d p).prod (latticeBondLaw d p)),
        Summable (fun e : Bond d =>
          |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) /
                ((triadicCube d m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ) /
                ((triadicCube d m k).ncard : ℝ)| ^ 2)) ∧
      MemLp (densityResamplingEnergy m k) r ((latticeBondLaw d p).prod (latticeBondLaw d p)) ∧
      lpNorm (densityResamplingEnergy m k) r ((latticeBondLaw d p).prod (latticeBondLaw d p)) ≤
        C * (r : ℝ) ^ β / (((3 ^ m : ℕ) : ℝ) ^ d) := by
  obtain ⟨C, hC, hraw⟩ := density_resampling_energy_moments h
  refine ⟨2 ^ d * C, by positivity, fun r hr m k => ?_⟩
  let μ := (latticeBondLaw d p).prod (latticeBondLaw d p)
  let v : ℝ := ((3 ^ m : ℕ) : ℝ)
  let V : ℝ := (triadicCube d m k).ncard
  let c : ℝ := 1 / V ^ 2
  let f (e : Bond d) (q : Configuration d × Configuration d) : ℝ :=
    |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2
  let g (e : Bond d) (q : Configuration d × Configuration d) : ℝ :=
    |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) / V -
      (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ) / V| ^ 2
  let F (q : Configuration d × Configuration d) : ℝ := ∑' e, f e q
  have hv1 : 1 ≤ v := by
    have h3 : 0 < (3 : ℕ) ^ m := by positivity
    change (1 : ℝ) ≤ ((3 ^ m : ℕ) : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt h3))
  have hv : 0 < v := zero_lt_one.trans_le hv1
  have hvd : 0 < v ^ d := pow_pos hv d
  have hV : V = v ^ d := ncard_triadicCube_eq_pow m k
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hfg (e : Bond d) (q : Configuration d × Configuration d) : g e q = c * f e q := by
    dsimp only [f, g, c]
    rw [← sub_div, abs_div, div_pow]
    simp only [sq_abs]
    ring
  have hGF : densityResamplingEnergy m k = fun q => c * F q := by
    funext q
    change (∑' e, g e q) = c * ∑' e, f e q
    simp_rw [hfg]
    exact tsum_mul_left
  obtain ⟨hSummable, hF, hFnorm⟩ := hraw r hr m k
  have hG : MemLp (densityResamplingEnergy m k) r μ := by
    rw [hGF]
    exact hF.const_mul c
  have hGnorm : lpNorm (densityResamplingEnergy m k) r μ = c * lpNorm F r μ := by
    rw [hGF]
    change lpNorm (c • F) r μ = _
    rw [lpNorm_const_smul]
    simp [Real.norm_eq_abs, abs_of_nonneg hc]
  have hdiv : (v + 1) ^ d / v ^ d ≤ 2 ^ d := by
    apply (div_le_iff₀ hvd).2
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hscale : c * (C * (r : ℝ) ^ β * (v + 1) ^ d) ≤
      (2 ^ d * C) * (r : ℝ) ^ β / v ^ d := by
    rw [show c = 1 / (v ^ d) ^ 2 by simp only [c, hV]]
    calc
      _ = (C * (r : ℝ) ^ β / v ^ d) * ((v + 1) ^ d / v ^ d) := by field_simp
      _ ≤ (C * (r : ℝ) ^ β / v ^ d) * 2 ^ d :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  refine ⟨?_, hG, ?_⟩
  · filter_upwards [hSummable] with q hq
    change Summable (fun e => g e q)
    simpa only [hfg] using hq.mul_left c
  · rw [hGnorm]
    exact (mul_le_mul_of_nonneg_left hFnorm hc).trans hscale

/-- Every conditional expectation of the normalized resampling energy satisfies the same moment
bound as the energy itself. -/
theorem density_conditional_energy_moments (h : DensityInfluenceRootBound d p β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex d)
      (𝓜 : MeasurableSpace (Configuration d × Configuration d)),
      MemLp (MeasureTheory.condExp 𝓜 ((latticeBondLaw d p).prod (latticeBondLaw d p))
        (densityResamplingEnergy m k)) r
        ((latticeBondLaw d p).prod (latticeBondLaw d p)) ∧
      lpNorm (MeasureTheory.condExp 𝓜 ((latticeBondLaw d p).prod (latticeBondLaw d p))
        (densityResamplingEnergy m k)) r
        ((latticeBondLaw d p).prod (latticeBondLaw d p)) ≤
          C * (r : ℝ) ^ β / (((3 ^ m : ℕ) : ℝ) ^ d) := by
  obtain ⟨C, hC, hmoment⟩ := density_normalized_energy_moments h
  refine ⟨C, hC, fun r hr m k 𝓜 => ?_⟩
  have hr' : (1 : ℝ≥0∞) ≤ r := by exact_mod_cast hr
  obtain ⟨_, hmem, hnorm⟩ := hmoment r hr m k
  exact ⟨hmem.condExp hr', (hmem.lpNorm_condExp_le_lpNorm hr').trans hnorm⟩

/-- The normalized single-bond influences are measurable functions of the two configurations. -/
theorem measurable_normalized_count_influence (p : unitInterval) (m : ℕ) (k : Vertex d)
    (e : Bond d) :
    Measurable fun q : Configuration d × Configuration d =>
      |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) /
          ((triadicCube d m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ) /
          ((triadicCube d m k).ncard : ℝ)| ^ 2 := by
  have hF := measurable_infiniteClusterCount_triadicCube m k
  have hRes := (measurePreserving_resampleBond d p e).measurable
  exact (((hF.comp measurable_fst).div_const _).sub
    ((hF.comp hRes).div_const _)).abs.pow_const 2

/-- The normalized resampling energy has finite mean in the extended sense. -/
theorem density_normalized_energy_lintegral_ne_top (h : DensityInfluenceRootBound d p β)
    (m : ℕ) (k : Vertex d) :
    (∫⁻ q : Configuration d × Configuration d,
      ∑' e : Bond d, ENNReal.ofReal
        (|(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) /
              ((triadicCube d m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ) /
              ((triadicCube d m k).ncard : ℝ)| ^ 2)
      ∂((latticeBondLaw d p).prod (latticeBondLaw d p))) ≠ ∞ := by
  obtain ⟨C, hC, hmoment⟩ := density_normalized_energy_moments h
  obtain ⟨hsum, hmem, -⟩ := hmoment 1 le_rfl m k
  have hint : Integrable (densityResamplingEnergy m k)
      ((latticeBondLaw d p).prod (latticeBondLaw d p)) :=
    memLp_one_iff_integrable.mp (by simpa using hmem)
  refine ne_of_lt (lt_of_eq_of_lt (lintegral_congr_ae ?_) hint.lintegral_lt_top)
  filter_upwards [hsum] with q hq
  exact (ENNReal.ofReal_tsum_of_nonneg (fun e => sq_nonneg _) hq).symm

/-- Individual normalized influences are integrable in the resampled configuration, and their
integrals sum to the averaged resampling energy, almost surely. -/
theorem density_integrated_energy_series (h : DensityInfluenceRootBound d p β)
    (m : ℕ) (k : Vertex d) :
    ∀ᵐ ω ∂(latticeBondLaw d p),
      (∀ e : Bond d, Integrable (fun η : Configuration d =>
        |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
              ((triadicCube d m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube d m k) (resampleBond ω η e) : ℝ) /
              ((triadicCube d m k).ncard : ℝ)| ^ 2) (latticeBondLaw d p)) ∧
      Summable (fun e : Bond d => ∫ η : Configuration d,
        |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
              ((triadicCube d m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube d m k) (resampleBond ω η e) : ℝ) /
              ((triadicCube d m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw d p)) ∧
      (∫ η, densityResamplingEnergy m k (ω, η) ∂(latticeBondLaw d p)) =
        ∑' e : Bond d, ∫ η : Configuration d,
          |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
                ((triadicCube d m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube d m k) (resampleBond ω η e) : ℝ) /
                ((triadicCube d m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw d p) := by
  let μ := latticeBondLaw d p
  let F (e : Bond d) (q : Configuration d × Configuration d) : ℝ :=
    |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) /
          ((triadicCube d m k).ncard : ℝ) -
      (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ) /
          ((triadicCube d m k).ncard : ℝ)| ^ 2
  let G (q : Configuration d × Configuration d) : ℝ≥0∞ := ∑' e, ENNReal.ofReal (F e q)
  have hFm (e : Bond d) : Measurable (F e) := measurable_normalized_count_influence p m k e
  have hGm : Measurable G := Measurable.tsum fun e => (hFm e).ennreal_ofReal
  have hfinite : (∫⁻ q, G q ∂(μ.prod μ)) ≠ ∞ := density_normalized_energy_lintegral_ne_top h m k
  have hslice : (∫⁻ ω, ∫⁻ η, G (ω, η) ∂μ ∂μ) ≠ ∞ := by
    rw [← lintegral_prod G hGm.aemeasurable]
    exact hfinite
  filter_upwards [ae_lt_top (hGm.lintegral_prod_right') hslice] with ω hω
  have hseries := integral_tsum_nonnegative μ (fun e η => F e (ω, η))
    (fun e => (hFm e).comp (measurable_const.prodMk measurable_id))
    (fun e η => sq_nonneg _) hω
  simpa only [F, G, densityResamplingEnergy] using hseries

/-- The sum of squared normalized resampling influences averaged over an independent
configuration. -/
noncomputable def densityConditionalInfluenceEnergy (p : unitInterval) (m : ℕ) (k : Vertex d)
    (ω : Configuration d) : ℝ :=
  ∑' e : Bond d, ∫ η : Configuration d,
    |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
          ((triadicCube d m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond ω η e) : ℝ) /
          ((triadicCube d m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw d p)

/-- The averaged influence energy is measurable. -/
theorem measurable_densityConditionalInfluenceEnergy (p : unitInterval) (m : ℕ)
    (k : Vertex d) : Measurable (densityConditionalInfluenceEnergy p m k) := by
  apply Measurable.tsum
  intro e
  exact (measurable_normalized_count_influence p m k e).stronglyMeasurable.integral_prod_right'
    |>.measurable

/-- The averaged influence energy is nonnegative. -/
theorem densityConditionalInfluenceEnergy_nonneg (p : unitInterval) (m : ℕ) (k : Vertex d)
    (ω : Configuration d) : 0 ≤ densityConditionalInfluenceEnergy p m k ω :=
  tsum_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

/-- The averaged influence energy has `L^r` norm at most `C r^β 3^{-dm}`. -/
theorem density_conditional_influence_energy_moments (h : DensityInfluenceRootBound d p β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex d),
      MemLp (densityConditionalInfluenceEnergy p m k) r (latticeBondLaw d p) ∧
      lpNorm (densityConditionalInfluenceEnergy p m k) r (latticeBondLaw d p) ≤
        C * (r : ℝ) ^ β / (((3 ^ m : ℕ) : ℝ) ^ d) := by
  obtain ⟨C, hC, hmom⟩ := density_conditional_energy_moments h
  obtain ⟨D, hD, henergy⟩ := density_normalized_energy_moments h
  refine ⟨C, hC, fun r hr m k => ?_⟩
  let μ := latticeBondLaw d p
  let P := μ.prod μ
  let X := densityResamplingEnergy (d := d) m k
  let W := densityConditionalInfluenceEnergy p m k
  let A : MeasurableSpace (Configuration d × Configuration d) :=
    MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Configuration d))
  letI : MeasurableSpace (Configuration d × Configuration d) := Prod.instMeasurableSpace
  let Y := MeasureTheory.condExp A P X
  have hXm : Measurable X := Measurable.tsum fun e => measurable_normalized_count_influence p m k e
  have hXi : Integrable X P := by
    have h1 := (henergy 1 (by norm_num) m k).2.1
    exact memLp_one_iff_integrable.mp (by simpa using h1)
  have hWm : Measurable W := measurable_densityConditionalInfluenceEnergy p m k
  have hYeq : (fun q : Configuration d × Configuration d => W q.1) =ᵐ[P] Y := by
    have heq := condExp_first_eq_integral μ μ X hXi hXm.stronglyMeasurable
    have hs := (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (density_integrated_energy_series h m k)
    filter_upwards [heq, hs] with q hq hs'
    calc
      W q.1 = ∫ η, X (q.1, η) ∂μ := hs'.2.2.symm
      _ = Y q := hq
  obtain ⟨hYm, hYnorm⟩ := hmom r hr m k A
  have hWprod : MemLp (W ∘ Prod.fst) r P := by
    refine ⟨hYm.1.congr hYeq.symm, ?_⟩
    change eLpNorm (fun q : Configuration d × Configuration d => W q.1) r P < ⊤
    rw [eLpNorm_congr_ae hYeq]
    exact hYm.2
  have hWmem : MemLp W r μ := by
    have hmap : AEStronglyMeasurable W (Measure.map Prod.fst P) := by
      rw [(measurePreserving_fst (μ := μ) (ν := μ)).map_eq]
      exact hWm.aestronglyMeasurable
    have h2 := (memLp_map_measure_iff hmap measurable_fst.aemeasurable).2 hWprod
    rwa [(measurePreserving_fst (μ := μ) (ν := μ)).map_eq] at h2
  have hNorm : lpNorm W r μ = lpNorm Y r P := by
    rw [← toReal_eLpNorm hWm.aestronglyMeasurable,
      ← toReal_eLpNorm hYm.aestronglyMeasurable]
    have hnormeq : eLpNorm (W ∘ Prod.fst) r P = eLpNorm Y r P :=
      eLpNorm_congr_ae hYeq
    rw [← eLpNorm_comp_measurePreserving hWm.aestronglyMeasurable
      (measurePreserving_fst (μ := μ) (ν := μ)), hnormeq]
  exact ⟨hWmem, hNorm.trans_le hYnorm⟩

end Rigidity.Proofs.S2

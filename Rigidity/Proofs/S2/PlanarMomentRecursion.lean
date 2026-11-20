import Rigidity.Proofs.S2.WeightedMomentHolder

/-!
# Moment recursion for planar density

The spectral-gap estimate and Hölder's inequality give a recursion between consecutive dyadic
moments of the centered density.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The planar density moments satisfy the spectral-gap power recursion. -/
theorem planar_density_moment_recursion (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m : ℕ) (k : Vertex 2),
      let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
      let X := planarDensityRealObservable p m k
      (∫ ω, |X ω| ^ (2 * n) ∂P) ≤ (∫ ω, |X ω| ^ n ∂P) ^ 2 +
        (C * (n : ℝ) ^ 14 / (((3 ^ m : ℕ) : ℝ) ^ 2)) *
          (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) := by
  obtain ⟨C, hC, hmom⟩ := planar_conditional_influence_energy_moments p hp
  refine ⟨C, hC, fun n hn m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let X := planarDensityRealObservable p m k
  let W := planarConditionalInfluenceEnergy p m k
  let Y : (Bond 2 → ℝ) → ℝ := W ∘ T
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hXprop := planar_density_real_observable_properties p m k
  have hXm : Measurable X := hXprop.1
  have hXb : ∀ ω, |X ω| ≤ 1 := hXprop.2.1
  have hWm : Measurable W := measurable_planarConditionalInfluenceEnergy p m k
  have hW0 (η : Configuration 2) : 0 ≤ W η := by
    apply tsum_nonneg
    intro e
    exact integral_nonneg fun _ => sq_nonneg _
  obtain ⟨hWmem, hWnorm⟩ := hmom n (by omega) m k
  have hYmem : MemLp Y n P := by
    have h : MemLp W n (Measure.map T P) := by rw [hT.map_eq]; exact hWmem
    exact h.comp_of_map hT.measurable.aemeasurable
  have hYnorm : lpNorm Y n P = lpNorm W n μ := by
    rw [← toReal_eLpNorm hYmem.aestronglyMeasurable,
      ← toReal_eLpNorm hWm.aestronglyMeasurable,
      eLpNorm_comp_measurePreserving hWm.aestronglyMeasurable hT]
  have hXnpow : MemLp (fun ω => X ω ^ n) 2 P := by
    refine MemLp.of_bound (hXm.pow_const n).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hXb ω)
  have hIntAbs : 0 ≤ ∫ ω, |X ω| ^ n ∂P := integral_nonneg fun _ => by positivity
  have hIntBound : |∫ ω, X ω ^ n ∂P| ≤ ∫ ω, |X ω| ^ n ∂P := by
    have h := norm_integral_le_integral_norm (μ := P) (fun ω => X ω ^ n)
    simpa only [Real.norm_eq_abs, abs_pow] using h
  have hIntSq : (∫ ω, X ω ^ n ∂P) ^ 2 ≤ (∫ ω, |X ω| ^ n ∂P) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hIntAbs).2 hIntBound
    simpa only [sq_abs] using h
  have hPowEq (ω) : (X ω ^ n) ^ 2 = |X ω| ^ (2 * n) := by
    rw [← sq_abs, abs_pow, ← pow_mul, show n * 2 = 2 * n by omega]
  have hVar := planar_density_power_variance_le p hp m k n
  dsimp only at hVar
  rw [variance_eq_sub hXnpow] at hVar
  have hIntEq : (∫ ω, (X ω ^ n) ^ 2 ∂P) = ∫ ω, |X ω| ^ (2 * n) ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hPowEq
  simp only [Pi.pow_apply] at hVar
  rw [hIntEq] at hVar
  change (∫ ω, |X ω| ^ (2 * n) ∂P) - (∫ ω, X ω ^ n ∂P) ^ 2 ≤
    (n : ℝ) ^ 2 * ∫ ω, |X ω| ^ (2 * (n - 1)) * Y ω ∂P at hVar
  have hHolder := weighted_moment_holder P X Y hXm hXb (fun ω => hW0 (T ω)) n hn hYmem
  have hM0 : 0 ≤ (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) :=
    Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  have hprod := mul_le_mul_of_nonneg_left (hYnorm ▸ hWnorm) hM0
  have hNN : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hest : (n : ℝ) ^ 2 * (∫ ω, |X ω| ^ (2 * (n - 1)) * Y ω ∂P) ≤
      (C * (n : ℝ) ^ 14 / (((3 ^ m : ℕ) : ℝ) ^ 2)) *
        (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) := by
    calc
      _ ≤ (n : ℝ) ^ 2 * ((∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) *
          lpNorm Y n P) := mul_le_mul_of_nonneg_left hHolder hNN
      _ ≤ (n : ℝ) ^ 2 * ((∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) *
          (C * (n : ℝ) ^ 12 / (((3 ^ m : ℕ) : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hprod hNN
      _ = _ := by ring
  change (∫ ω, |X ω| ^ (2 * n) ∂P) ≤ (∫ ω, |X ω| ^ n ∂P) ^ 2 +
    (C * (n : ℝ) ^ 14 / (((3 ^ m : ℕ) : ℝ) ^ 2)) *
      (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n)
  linarith

end Rigidity.Proofs.S2

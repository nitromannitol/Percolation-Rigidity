import Rigidity.Proofs.S2.InfluenceMomentRootQuantitative
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Countable sums with summable moment norms

A countable family of nonnegative random variables with summable `Lʳ` norms has an almost-surely
convergent sum in `Lʳ`, and the norm of the sum is bounded by the sum of the norms.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory
open scoped ENNReal

/-- A nonnegative random series with summable integer moment norms converges in `Lʳ`. -/
theorem summable_nonnegative_moment_norms {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (r : ℕ) (hr : 1 ≤ r) (f : ι → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i ω, 0 ≤ f i ω)
    (hint : ∀ i, Integrable (fun ω => f i ω ^ r) μ)
    (hsum : Summable (fun i => (∫ ω, f i ω ^ r ∂μ) ^ (1 / (r : ℝ)))) :
    ∃ Y : Ω → ℝ, MemLp Y r μ ∧
      (∀ᵐ ω ∂μ, HasSum (fun i => f i ω) (Y ω)) ∧
      lpNorm Y r μ ≤ ∑' i, (∫ ω, f i ω ^ r ∂μ) ^ (1 / (r : ℝ)) := by
  classical
  have hr0 : r ≠ 0 := by omega
  have hp0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast hr0
  letI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hmem (i : ι) : MemLp (f i) r μ := by
    apply (integrable_norm_rpow_iff (hf i).aestronglyMeasurable hp0 (ENNReal.natCast_ne_top r)).1
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (hnn i _)] using hint i
  let u (i : ι) : Lp ℝ r μ := (hmem i).toLp (f i)
  have hnorm (i : ι) : ‖u i‖ = (∫ ω, f i ω ^ r ∂μ) ^ (1 / (r : ℝ)) := by
    rw [Lp.norm_toLp, toReal_eLpNorm (hmem i).aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal hp0 (ENNReal.natCast_ne_top r)
        (hmem i).aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (hnn i _), one_div]
  have hunorm : Summable fun i => ‖u i‖ := by simpa only [hnorm] using hsum
  have hu : Summable u := hunorm.of_norm
  let U : Lp ℝ r μ := ∑' i, u i
  have hAe : ∀ᵐ ω ∂μ, HasSum (fun i => u i ω) (U ω) :=
    Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.2 hunorm)
  have hRep : ∀ᵐ ω ∂μ, ∀ i, u i ω = f i ω :=
    ae_all_iff.2 fun i => MemLp.coeFn_toLp (hmem i)
  refine ⟨U, Lp.memLp U, ?_, ?_⟩
  · filter_upwards [hAe, hRep] with ω hω hRepω
    simpa only [hRepω] using hω
  · rw [← toReal_eLpNorm (Lp.memLp U).aestronglyMeasurable, ← Lp.norm_def]
    exact (norm_tsum_le_tsum_norm hunorm).trans_eq (tsum_congr hnorm)

end Rigidity.Proofs.S2

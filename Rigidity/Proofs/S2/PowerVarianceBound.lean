import Rigidity.Proofs.S2.ResamplingPowerLIntegral

/-!
# Variance of powers under independent coordinates

The countable Efron–Stein inequality and resampling exchangeability bound the variance of a
power by its weighted squared influences.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal

/-- A single-coordinate resampling energy may use a full independent product copy. -/
theorem siteEnergy_eq_two_copy {ι : Type*} [DecidableEq ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (i : ι) :
    let P := Measure.infinitePi (fun _ : ι => ν)
    siteEnergy ν F i = ∫⁻ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      ((F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2) ∂(P.prod P) := by
  let P := Measure.infinitePi (fun _ : ι => ν)
  let T (q : (ι → ℝ) × (ι → ℝ)) := (q.1, q.2 i)
  have hT : MeasurePreserving T (P.prod P) (P.prod ν) :=
    (MeasurePreserving.id P).prod (measurePreserving_eval_infinitePi (fun _ : ι => ν) i)
  rw [siteEnergy_eq_lintegral_prod ν hF i]
  exact (hT.lintegral_comp (measurable_resampleDiff hF i)).symm

/-- The variance of `Fⁿ` is bounded by `n²` times the sum of weighted resampling energies. -/
theorem evariance_pow_le_weighted_resampling {ι : Type*} [DecidableEq ι] [Countable ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (n : ℕ) (hF2 : Integrable (fun ω => (F ω ^ n) ^ 2)
      (Measure.infinitePi fun _ : ι => ν)) :
    let P := Measure.infinitePi (fun _ : ι => ν)
    evariance (fun ω => F ω ^ n) P ≤ ENNReal.ofReal ((n : ℝ) ^ 2) *
      ∑' i : ι, ∫⁻ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
        (|F q.1| ^ (2 * (n - 1)) *
          (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2) ∂(P.prod P) := by
  let P := Measure.infinitePi (fun _ : ι => ν)
  let G : (ι → ℝ) → ℝ := fun ω => F ω ^ n
  let W (i : ι) : ℝ≥0∞ := ∫⁻ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
    (|F q.1| ^ (2 * (n - 1)) *
      (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2) ∂(P.prod P)
  have hGm : Measurable G := hF.pow_const n
  have hstep (i : ι) : siteEnergy ν G i ≤ ENNReal.ofReal (2 * (n : ℝ) ^ 2) * W i := by
    rw [siteEnergy_eq_two_copy ν G hGm i]
    exact lintegral_resampling_pow_le ν F hF i n
  have he := evariance_le_half_tsum_siteEnergy ν hGm hF2
  change evariance G P ≤ ENNReal.ofReal ((n : ℝ) ^ 2) * ∑' i, W i
  calc
    _ ≤ (∑' i, siteEnergy ν G i) / 2 := he
    _ ≤ (∑' i, ENNReal.ofReal (2 * (n : ℝ) ^ 2) * W i) / 2 :=
      ENNReal.div_le_div_right (ENNReal.tsum_le_tsum hstep) 2
    _ = ENNReal.ofReal ((n : ℝ) ^ 2) * ∑' i, W i := by
      rw [ENNReal.tsum_mul_left, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv]
      rw [show 2 * ENNReal.ofReal ((n : ℝ) ^ 2) * (∑' i, W i) * 2⁻¹ =
        (2 * 2⁻¹) * (ENNReal.ofReal ((n : ℝ) ^ 2) * ∑' i, W i) by ac_rfl,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

end Rigidity.Proofs.S2

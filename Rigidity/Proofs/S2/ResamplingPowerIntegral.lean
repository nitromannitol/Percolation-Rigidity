import Rigidity.Proofs.S2.ResamplingSymmetry
import Rigidity.Proofs.S2.PowerResamplingBound

/-!
# Resampling differences of powers

For a bounded function of independent coordinates, the squared resampling difference of a
power is controlled by one endpoint weight and the squared resampling difference.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb

/-- Squared power differences are bounded by a weighted resampling energy. -/
theorem integral_resampling_pow_le {ι : Type*} [DecidableEq ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (hbound : ∀ ω, |F ω| ≤ 1) (i : ι) (n : ℕ) :
    let P := Measure.infinitePi (fun _ : ι => ν)
    (∫ q : (ι → ℝ) × (ι → ℝ),
      (F q.1 ^ n - F (Function.update q.1 i (q.2 i)) ^ n) ^ 2 ∂(P.prod P)) ≤
      (2 * (n : ℝ) ^ 2) * ∫ q : (ι → ℝ) × (ι → ℝ),
        |F q.1| ^ (2 * (n - 1)) *
          (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2 ∂(P.prod P) := by
  classical
  let P := Measure.infinitePi (fun _ : ι => ν)
  let μ := P.prod P
  let A (q : (ι → ℝ) × (ι → ℝ)) := F q.1
  let B (q : (ι → ℝ) × (ι → ℝ)) := F (Function.update q.1 i (q.2 i))
  let D (q : (ι → ℝ) × (ι → ℝ)) := (A q - B q) ^ 2
  let L (q : (ι → ℝ) × (ι → ℝ)) := (A q ^ n - B q ^ n) ^ 2
  let U (q : (ι → ℝ) × (ι → ℝ)) := |A q| ^ (2 * (n - 1)) * D q
  let V (q : (ι → ℝ) × (ι → ℝ)) := |B q| ^ (2 * (n - 1)) * D q
  have hAm : Measurable A := hF.comp measurable_fst
  have hBm : Measurable B := by
    have hu : Measurable (fun q : (ι → ℝ) × (ι → ℝ) =>
        Function.update q.1 i (q.2 i)) :=
      (measurable_updateAt i).comp (measurable_fst.prodMk (measurable_pi_apply i |>.comp measurable_snd))
    exact hF.comp hu
  have hD0 (q) : 0 ≤ D q := sq_nonneg _
  have hD4 (q) : D q ≤ 4 := by
    have ha := hbound q.1
    have hb := hbound (Function.update q.1 i (q.2 i))
    have hd : |A q - B q| ≤ 2 := (abs_sub _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 hd
    rw [sq_abs] at hs
    norm_num at hs
    exact hs
  have hL4 (q) : L q ≤ 4 := by
    have ha : |A q ^ n| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hbound q.1)
    have hb : |B q ^ n| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hbound (Function.update q.1 i (q.2 i)))
    have hd : |A q ^ n - B q ^ n| ≤ 2 := (abs_sub _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 hd
    rw [sq_abs] at hs
    norm_num at hs
    exact hs
  have hU4 (q) : U q ≤ 4 := by
    have hw : |A q| ^ (2 * (n - 1)) ≤ 1 := pow_le_one₀ (abs_nonneg _) (hbound q.1)
    calc
      U q ≤ 1 * D q := mul_le_mul_of_nonneg_right hw (hD0 q)
      _ ≤ 4 := by simpa using hD4 q
  have hV4 (q) : V q ≤ 4 := by
    have hw : |B q| ^ (2 * (n - 1)) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (hbound (Function.update q.1 i (q.2 i)))
    calc
      V q ≤ 1 * D q := mul_le_mul_of_nonneg_right hw (hD0 q)
      _ ≤ 4 := by simpa using hD4 q
  have hLm : Measurable L := ((hAm.pow_const n).sub (hBm.pow_const n)).pow_const 2
  have hUm : Measurable U := (hAm.abs.pow_const _).mul ((hAm.sub hBm).pow_const 2)
  have hVm : Measurable V := (hBm.abs.pow_const _).mul ((hAm.sub hBm).pow_const 2)
  have hLi : Integrable L μ := by
    refine (integrable_const (4 : ℝ)).mono' hLm.aestronglyMeasurable ?_
    filter_upwards with q
    have h0 : 0 ≤ L q := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hL4 q
  have hUi : Integrable U μ := by
    refine (integrable_const (4 : ℝ)).mono' hUm.aestronglyMeasurable ?_
    filter_upwards with q
    have h0 : 0 ≤ U q := mul_nonneg (pow_nonneg (abs_nonneg _) _) (hD0 q)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hU4 q
  have hVi : Integrable V μ := by
    refine (integrable_const (4 : ℝ)).mono' hVm.aestronglyMeasurable ?_
    filter_upwards with q
    have h0 : 0 ≤ V q := mul_nonneg (pow_nonneg (abs_nonneg _) _) (hD0 q)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hV4 q
  have hpoint (q) : L q ≤ (n : ℝ) ^ 2 * (U q + V q) := by
    have h := sq_pow_sub_pow_le (A q) (B q) n
    dsimp only [L, U, V, D]
    nlinarith
  have heq : (∫ q, U q ∂μ) = ∫ q, V q ∂μ :=
    integral_resampling_endpoint_symmetry ν F hF i (2 * (n - 1))
  change (∫ q, L q ∂μ) ≤ (2 * (n : ℝ) ^ 2) * ∫ q, U q ∂μ
  calc
    _ ≤ ∫ q, (n : ℝ) ^ 2 * (U q + V q) ∂μ :=
      integral_mono hLi ((hUi.add hVi).const_mul _) hpoint
    _ = (n : ℝ) ^ 2 * ((∫ q, U q ∂μ) + ∫ q, V q ∂μ) := by
      rw [integral_const_mul, integral_add hUi hVi]
    _ = _ := by rw [← heq]; ring

end Rigidity.Proofs.S2

import Rigidity.Proofs.S2.ResamplingExchangeable
import Rigidity.Proofs.S2.PowerResamplingBound
import LatticeProb.Prob.EfronSteinCountable

/-!
# Extended integrals of power resampling differences

Endpoint exchangeability gives a power-resampling bound without an integrability assumption.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal

/-- The extended integral of a squared power difference is controlled by a weighted influence. -/
theorem lintegral_resampling_pow_le {ι : Type*} [DecidableEq ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (i : ι) (n : ℕ) :
    let P := Measure.infinitePi (fun _ : ι => ν)
    (∫⁻ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      ((F q.1 ^ n - F (Function.update q.1 i (q.2 i)) ^ n) ^ 2) ∂(P.prod P)) ≤
      ENNReal.ofReal (2 * (n : ℝ) ^ 2) *
        ∫⁻ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
          (|F q.1| ^ (2 * (n - 1)) *
            (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2) ∂(P.prod P) := by
  classical
  let P := Measure.infinitePi (fun _ : ι => ν)
  let μ := P.prod P
  let S (q : (ι → ℝ) × (ι → ℝ)) :=
    (Function.update q.1 i (q.2 i), Function.update q.2 i (q.1 i))
  let A (q : (ι → ℝ) × (ι → ℝ)) := F q.1
  let B (q : (ι → ℝ) × (ι → ℝ)) := F (Function.update q.1 i (q.2 i))
  let U (q : (ι → ℝ) × (ι → ℝ)) : ℝ≥0∞ := ENNReal.ofReal
    (|A q| ^ (2 * (n - 1)) * (A q - B q) ^ 2)
  let V (q : (ι → ℝ) × (ι → ℝ)) : ℝ≥0∞ := ENNReal.ofReal
    (|B q| ^ (2 * (n - 1)) * (A q - B q) ^ 2)
  have hS : MeasurePreserving S μ μ := measurePreserving_swap_coordinate ν i
  have hAm : Measurable A := hF.comp measurable_fst
  have hBm : Measurable B := by
    have hu : Measurable (fun q : (ι → ℝ) × (ι → ℝ) =>
        Function.update q.1 i (q.2 i)) :=
      (measurable_updateAt i).comp (measurable_fst.prodMk (measurable_pi_apply i |>.comp measurable_snd))
    exact hF.comp hu
  have hUm : Measurable U := ((hAm.abs.pow_const _).mul ((hAm.sub hBm).pow_const 2)).ennreal_ofReal
  have hVm : Measurable V := ((hBm.abs.pow_const _).mul ((hAm.sub hBm).pow_const 2)).ennreal_ofReal
  have hsym : (∫⁻ q, U q ∂μ) = ∫⁻ q, V q ∂μ := by
    calc
      _ = ∫⁻ q, U (S q) ∂μ := (hS.lintegral_comp hUm).symm
      _ = _ := by
        apply lintegral_congr
        intro q
        have hu : Function.update (Function.update q.1 i (q.2 i)) i
            ((Function.update q.2 i (q.1 i)) i) = q.1 := by simp
        dsimp only [U, V, A, B, S]
        rw [hu]
        congr 1
        ring
  have hpoint (q : (ι → ℝ) × (ι → ℝ)) : ENNReal.ofReal ((A q ^ n - B q ^ n) ^ 2) ≤
      ENNReal.ofReal ((n : ℝ) ^ 2) * (U q + V q) := by
    calc
      _ ≤ ENNReal.ofReal ((n : ℝ) ^ 2 *
          (|A q| ^ (2 * (n - 1)) * (A q - B q) ^ 2 +
            |B q| ^ (2 * (n - 1)) * (A q - B q) ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have h := sq_pow_sub_pow_le (A q) (B q) n
        nlinarith
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
  change (∫⁻ q, ENNReal.ofReal ((A q ^ n - B q ^ n) ^ 2) ∂μ) ≤
    ENNReal.ofReal (2 * (n : ℝ) ^ 2) * ∫⁻ q, U q ∂μ
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal ((n : ℝ) ^ 2) * (U q + V q) ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal ((n : ℝ) ^ 2) * ((∫⁻ q, U q ∂μ) + ∫⁻ q, V q ∂μ) := by
      change (∫⁻ q, ENNReal.ofReal ((n : ℝ) ^ 2) * (U + V) q ∂μ) = _
      rw [lintegral_const_mul'' _ (hUm.add hVm).aemeasurable]
      change ENNReal.ofReal ((n : ℝ) ^ 2) * (∫⁻ q, U q + V q ∂μ) = _
      rw [lintegral_add_left hUm]
    _ = _ := by
      rw [← hsym, ← two_mul, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [ENNReal.ofReal_ofNat]
      simp [mul_assoc, mul_left_comm]

end Rigidity.Proofs.S2

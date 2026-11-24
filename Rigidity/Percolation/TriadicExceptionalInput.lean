import PercolationClusterHomogenization.Percolation.TriadicExceptionalSupremum
import LatticeProb.Prob.FiniteTailMax

/-!
# Exceptional scales from exponential moments

Uniform stretched-exponential moments at decreasing scales control the
supremum of the exceptional triadic lengths.
-/

namespace Rigidity.Percolation

open LatticeProb MeasureTheory
open scoped ENNReal

/-- Exponential moments at scales `K * 3 ^ (-n * β)` imply a stretched
exponential moment for the supremum of indices where the variable reaches one. -/
theorem uniform_exceptionalScale_exp_moment_of_decaying_moments {Ω : Type*} [MeasurableSpace Ω]
    (K s β : ℝ) (hK : 0 < K) (hs : 0 < s) (hβ : 0 < β) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ),
      (∀ n, Measurable (X n)) →
      (∀ n, Integrable (fun ω => Real.exp ((X n ω / (K / ((3 : ℝ) ^ n) ^ β)) ^ s)) μ) →
      (∀ n, (∫ ω, Real.exp ((X n ω / (K / ((3 : ℝ) ^ n) ^ β)) ^ s) ∂μ) ≤ 2) →
      let E : ℕ → Set Ω := fun n => {ω | 1 ≤ X n ω}
      (∀ᵐ ω ∂μ, exceptionalScale E ω ≠ ∞) ∧
        Integrable (fun ω => Real.exp (((exceptionalScale E ω).toReal / θ) ^ (s * β))) μ ∧
        (∫ ω, Real.exp (((exceptionalScale E ω).toReal / θ) ^ (s * β)) ∂μ) ≤ 2 := by
  let c : ℝ := (K ^ s)⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.rpow_pos_of_pos hK s)
  have hsβ : 0 < s * β := mul_pos hs hβ
  obtain ⟨θ, hθ, hmoment⟩ := uniform_exceptionalScale_exp_moment (Ω := Ω)
    2 (by simp) (s * β) c hsβ hc
  refine ⟨θ, hθ, ?_⟩
  intro μ _ X hXm hInt hMom
  let E : ℕ → Set Ω := fun n => {ω | 1 ≤ X n ω}
  have hEm : ∀ n, MeasurableSet (E n) := fun n => measurableSet_le measurable_const (hXm n)
  have hE : ∀ n : ℕ, μ (E n) ≤ (2 : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ (s * β))) := by
    intro n
    have hn : 0 < ((3 : ℝ) ^ n) ^ β := Real.rpow_pos_of_pos (by positivity) β
    have ha : 0 < K / ((3 : ℝ) ^ n) ^ β := div_pos hK hn
    have ht := measure_ge_le_of_exp_rpow_moment μ (X n) (K / ((3 : ℝ) ^ n) ^ β) s
      ha hs (hInt n) (hMom n) (r := 1) (by norm_num)
    have heq : (1 / (K / ((3 : ℝ) ^ n) ^ β)) ^ s =
        c * ((3 : ℝ) ^ n) ^ (s * β) := by
      rw [one_div_div, Real.div_rpow hn.le hK.le, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 3 ^ n)]
      dsimp only [c]
      rw [mul_comm s β, div_eq_mul_inv, mul_comm]
    rw [heq] at ht
    calc
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(c * ((3 : ℝ) ^ n) ^ (s * β)))) := ht
      _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  refine ⟨?_, ?_⟩
  · apply ae_exceptionalScale_ne_top μ E 2 (by simp) ((3 : ℝ) ^ (s * β)) c
      (Real.one_lt_rpow (by norm_num) hsβ) hc
    intro n
    simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3)] using hE n
  · exact hmoment μ E hEm hE

/-- The exceptional scale has a finite stretched-exponential moment under
decaying exponential-moment estimates. -/
theorem exceptionalScale_exp_moment_of_decaying_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ n, Measurable (X n)) (K s β : ℝ) (hK : 0 < K) (hs : 0 < s) (hβ : 0 < β)
    (hInt : ∀ n, Integrable (fun ω => Real.exp ((X n ω / (K / ((3 : ℝ) ^ n) ^ β)) ^ s)) μ)
    (hMom : ∀ n, (∫ ω, Real.exp ((X n ω / (K / ((3 : ℝ) ^ n) ^ β)) ^ s) ∂μ) ≤ 2) :
    let E : ℕ → Set Ω := fun n => {ω | 1 ≤ X n ω}
    (∀ᵐ ω ∂μ, exceptionalScale E ω ≠ ∞) ∧
    ∃ θ : ℝ, 0 < θ ∧
      Integrable (fun ω => Real.exp (((exceptionalScale E ω).toReal / θ) ^ (s * β))) μ ∧
      (∫ ω, Real.exp (((exceptionalScale E ω).toReal / θ) ^ (s * β)) ∂μ) ≤ 2 := by
  obtain ⟨θ, hθ, h⟩ := uniform_exceptionalScale_exp_moment_of_decaying_moments
    (Ω := Ω) K s β hK hs hβ
  obtain ⟨hae, hi, hm⟩ := h μ X hXm hInt hMom
  exact ⟨hae, θ, hθ, hi, hm⟩

/-- The two usual expressions for a decreasing triadic scale agree. -/
theorem triadic_decaying_scale_eq (K β : ℝ) (n : ℕ) :
    K / ((3 : ℝ) ^ n) ^ β = K * (3 : ℝ) ^ (-(n : ℝ) * β) := by
  rw [neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  exact div_eq_mul_inv _ _

/-- Exponential moments at scales `K * 3 ^ (-nβ)` give a uniform
stretched-exponential moment for the supremum of exceptional scales. -/
theorem uniform_exceptionalScale_exp_moment_of_triadic_moments {Ω : Type*} [MeasurableSpace Ω]
    (K s β : ℝ) (hK : 0 < K) (hs : 0 < s) (hβ : 0 < β) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ),
      (∀ n, Measurable (X n)) →
      (∀ n, Integrable (fun ω => Real.exp ((X n ω / (K * (3 : ℝ) ^ (-(n : ℝ) * β))) ^ s)) μ) →
      (∀ n, (∫ ω, Real.exp ((X n ω / (K * (3 : ℝ) ^ (-(n : ℝ) * β))) ^ s) ∂μ) ≤ 2) →
      let E : ℕ → Set Ω := fun n => {ω | 1 ≤ X n ω}
      (∀ᵐ ω ∂μ, exceptionalScale E ω ≠ ∞) ∧
        Integrable (fun ω => Real.exp (((exceptionalScale E ω).toReal / θ) ^ (s * β))) μ ∧
        (∫ ω, Real.exp (((exceptionalScale E ω).toReal / θ) ^ (s * β)) ∂μ) ≤ 2 := by
  obtain ⟨θ, hθ, h⟩ := uniform_exceptionalScale_exp_moment_of_decaying_moments
    (Ω := Ω) K s β hK hs hβ
  refine ⟨θ, hθ, ?_⟩
  intro μ _ X hXm hInt hMom
  apply h μ X hXm
  · intro n
    simpa only [triadic_decaying_scale_eq] using hInt n
  · intro n
    simpa only [triadic_decaying_scale_eq] using hMom n

end Rigidity.Percolation

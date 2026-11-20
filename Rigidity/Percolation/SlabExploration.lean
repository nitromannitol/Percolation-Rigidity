import Rigidity.Percolation.SlabCube
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional decay for slab exploration

A nested sequence of events whose conditional probabilities are uniformly
bounded contracts geometrically. This is the iteration used in slab exploration.
-/

namespace Rigidity.Percolation

open MeasureTheory
open scoped MeasureTheory

/-- A conditional upper bound on a nested event yields a one-step measure bound. -/
theorem measureReal_le_mul_of_condExp_indicator_le {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {A B : Set Ω} (hA : MeasurableSet[m] A) (hB : @MeasurableSet Ω m₀ B)
    (hBA : B ⊆ A) (q : ℝ)
    (hcond : ∀ᵐ ω ∂μ.restrict A,
      μ[B.indicator (fun _ => (1 : ℝ)) | m] ω ≤ q) :
    μ.real B ≤ q * μ.real A := by
  have hInt : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hB
  have hbound := setIntegral_mono_ae_restrict
    (integrable_condExp.integrableOn) (integrable_const q).integrableOn hcond
  have heq := setIntegral_condExp hm hInt hA
  rw [heq] at hbound
  rw [setIntegral_indicator hB, Set.inter_eq_self_of_subset_right hBA,
    setIntegral_const, setIntegral_const] at hbound
  simpa only [smul_eq_mul, mul_one, one_mul, mul_comm] using hbound

/-- Iterating conditional upper bounds along decreasing events gives geometric
probability decay. -/
theorem measureReal_le_pow_of_condExp_indicator_le {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ n, m n ≤ m₀) (G : ℕ → Set Ω)
    (hG : ∀ n, MeasurableSet[m n] (G n))
    (hdecr : ∀ n, G (n + 1) ⊆ G n) (q : ℝ) (hq : 0 ≤ q)
    (hcond : ∀ n, ∀ᵐ ω ∂μ.restrict (G n),
      μ[(G (n + 1)).indicator (fun _ => (1 : ℝ)) | m n] ω ≤ q) :
    ∀ n, μ.real (G n) ≤ q ^ n := by
  intro n
  induction n with
  | zero => simpa only [pow_zero] using (measureReal_le_one (μ := μ) (s := G 0))
  | succ n ih =>
      have hstep := measureReal_le_mul_of_condExp_indicator_le μ (hm n) (hG n)
        (hm (n + 1) _ (hG (n + 1))) (hdecr n) q (hcond n)
      exact hstep.trans (by simpa only [pow_succ, mul_comm] using mul_le_mul_of_nonneg_left ih hq)

end Rigidity.Percolation

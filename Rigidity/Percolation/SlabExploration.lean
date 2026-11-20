import Rigidity.Percolation.SlabCube
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

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


/-- If a success event excludes survival, its conditional lower bound gives a
conditional upper bound for survival. -/
theorem condExp_indicator_le_one_sub_of_disjoint {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {A B C : Set Ω} (hB : @MeasurableSet Ω m₀ B) (hC : @MeasurableSet Ω m₀ C)
    (hBC : Disjoint B C) (δ : ℝ)
    (hcond : ∀ᵐ ω ∂μ.restrict A,
      δ ≤ μ[C.indicator (fun _ => (1 : ℝ)) | m] ω) :
    ∀ᵐ ω ∂μ.restrict A,
      μ[B.indicator (fun _ => (1 : ℝ)) | m] ω ≤ 1 - δ := by
  have hBint : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hB
  have hCint : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hC
  have hpoint : B.indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ]
      (fun _ => (1 : ℝ)) - C.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [] with ω
    by_cases hωB : ω ∈ B <;> by_cases hωC : ω ∈ C
    · exact (Set.disjoint_left.mp hBC hωB hωC).elim
    · simp [hωB, hωC]
    · simp [hωB, hωC]
    · simp [hωB, hωC]
  have hmono := condExp_mono (m := m) hBint ((integrable_const 1).sub hCint) hpoint
  have hsub := condExp_sub (integrable_const 1) hCint m
  have hone := condExp_const (μ := μ) hm (1 : ℝ)
  filter_upwards [ae_restrict_of_ae hmono, ae_restrict_of_ae hsub, hcond] with ω h₁ h₂ h₃
  rw [hone] at h₂
  simp only [Pi.sub_apply] at h₂
  linarith


/-- If each exploration step has a conditional chance of a success which
precludes survival, the survival probability decays geometrically. -/
theorem measureReal_le_pow_one_sub_of_condExp_success {Ω : Type*}
    [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (G C : ℕ → Set Ω) (hG : ∀ n, MeasurableSet[m n] (G n))
    (hC : ∀ n, @MeasurableSet Ω m₀ (C n))
    (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hdisj : ∀ n, Disjoint (G (n + 1)) (C n)) (δ : ℝ) (hδ : δ ≤ 1)
    (hcond : ∀ n, ∀ᵐ ω ∂μ.restrict (G n),
      δ ≤ μ[(C n).indicator (fun _ => (1 : ℝ)) | m n] ω) :
    ∀ n, μ.real (G n) ≤ (1 - δ) ^ n := by
  apply measureReal_le_pow_of_condExp_indicator_le μ m hm G hG hdecr (1 - δ) (sub_nonneg.mpr hδ)
  intro n
  exact condExp_indicator_le_one_sub_of_disjoint μ (hm n)
    (hm (n + 1) _ (hG (n + 1))) (hC n) (hdisj n) δ (hcond n)


/-- A past-measurable choice among countably many candidate events preserves a
uniform conditional lower bound on their probabilities. -/
theorem condExp_indicator_lower_of_measurable_selection {Ω ι : Type*} [Countable ι]
    [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) (A B : ι → Set Ω) {G C : Set Ω}
    (hA : ∀ i, MeasurableSet[m] (A i))
    (hB : ∀ i, @MeasurableSet Ω m₀ (B i)) (hC : @MeasurableSet Ω m₀ C)
    (hG : @MeasurableSet Ω m₀ G) (hcover : G ⊆ ⋃ i, A i)
    (hsubset : ∀ i, A i ∩ B i ⊆ C) (δ : ℝ)
    (hprob : ∀ i, ∀ᵐ ω ∂μ,
      δ ≤ μ[(B i).indicator (fun _ => (1 : ℝ)) | m] ω) :
    ∀ᵐ ω ∂μ.restrict G, δ ≤ μ[C.indicator (fun _ => (1 : ℝ)) | m] ω := by
  have hCint : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hC
  have hbound : ∀ i, ∀ᵐ ω ∂μ,
      ω ∈ A i → μ[(B i).indicator (fun _ => (1 : ℝ)) | m] ω ≤
        μ[C.indicator (fun _ => (1 : ℝ)) | m] ω := by
    intro i
    have hBi : Integrable ((B i).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const 1).indicator (hB i)
    have hpoint : (A i).indicator ((B i).indicator (fun _ => (1 : ℝ))) ≤ᵐ[μ]
        C.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [] with ω
      by_cases ha : ω ∈ A i <;> by_cases hb : ω ∈ B i <;> by_cases hc : ω ∈ C
      · simp [ha, hb, hc]
      · exact (hc (hsubset i ⟨ha, hb⟩)).elim
      · simp [ha, hb, hc]
      · simp [ha, hb, hc]
      · simp [ha, hc]
      · simp [ha, hc]
      · simp [ha, hc]
      · simp [ha, hc]
    have hmono := condExp_mono (m := m) (hBi.indicator (hm _ (hA i))) hCint hpoint
    have heq := condExp_indicator hBi (hA i)
    filter_upwards [hmono, heq] with ω h₁ h₂ ha
    rw [h₂] at h₁
    simpa only [Set.indicator_of_mem ha] using h₁
  filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr hbound),
    ae_restrict_of_ae (ae_all_iff.mpr hprob), ae_restrict_mem hG] with ω hb hp hω
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hω)
  exact (hp i).trans (hb i hi)

end Rigidity.Percolation

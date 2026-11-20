import Rigidity.Percolation.TriadicExceptionalMoment

/-!
# Supremum of exceptional triadic scales

The supremum of exceptional triadic lengths is measurable, finite almost
surely, and has a stretched-exponential moment.
-/

namespace Rigidity.Percolation

open MeasureTheory
open scoped ENNReal

/-- The supremum of the triadic lengths at which an exceptional event occurs. -/
noncomputable def exceptionalScale {Ω : Type*} (E : ℕ → Set Ω) (ω : Ω) : ℝ≥0∞ := by
  classical
  exact ⨆ n : ℕ, if ω ∈ E n then (3 : ℝ≥0∞) ^ n else 0

/-- The supremum of measurable exceptional scales is measurable. -/
theorem measurable_exceptionalScale {Ω : Type*} [MeasurableSpace Ω]
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n)) : Measurable (exceptionalScale E) := by
  classical
  unfold exceptionalScale
  apply Measurable.iSup
  intro n
  exact measurable_const.ite (hE n) measurable_const

/-- If no sufficiently large index is exceptional, the supremum is finite. -/
theorem exceptionalScale_ne_top_of_eventually_notMem {Ω : Type*} (E : ℕ → Set Ω)
    {ω : Ω} (h : ∀ᶠ n in Filter.atTop, ω ∉ E n) : exceptionalScale E ω ≠ ∞ := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  have hle : exceptionalScale E ω ≤ (3 : ℝ≥0∞) ^ N := by
    unfold exceptionalScale
    apply iSup_le
    intro n
    by_cases hn : n < N
    · split_ifs
      · exact pow_le_pow_right₀ (by norm_num) (by omega)
      · exact bot_le
    · have hnot := hN n (by omega)
      simp only [hnot, if_false]
      exact bot_le
  exact ne_top_of_le_ne_top (by simp) hle

/-- Exceptional scales have finite supremum almost surely under a
stretched-exponential event bound. -/
theorem ae_exceptionalScale_ne_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Set Ω) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hE : ∀ n, μ (E n) ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ n))) :
    ∀ᵐ ω ∂μ, exceptionalScale E ω ≠ ∞ := by
  filter_upwards [ae_eventually_notMem_of_stretched μ E C hC b c hb hc hE] with ω hω
  exact exceptionalScale_ne_top_of_eventually_notMem E hω

/-- The real supremum of exceptional lengths has a stretched-exponential
moment under a uniform stretched-exponential bound for their events. -/
theorem exceptionalScale_exp_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ℕ → Set Ω)
    (hEm : ∀ n, MeasurableSet (E n)) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hE : ∀ n : ℕ, μ (E n) ≤ C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s))) :
    ∃ θ : ℝ, 0 < θ ∧
      Integrable (fun ω => Real.exp (((exceptionalScale E ω).toReal / θ) ^ s)) μ ∧
      (∫ ω, Real.exp (((exceptionalScale E ω).toReal / θ) ^ s) ∂μ) ≤ 2 := by
  classical
  let M : Ω → ℝ := fun ω => (exceptionalScale E ω).toReal / 3
  have hMm : Measurable M := (ENNReal.measurable_toReal.comp (measurable_exceptionalScale E hEm)).div_const _
  have hM0 (ω : Ω) : 0 ≤ M ω := div_nonneg ENNReal.toReal_nonneg (by norm_num)
  have hbound (ω : Ω) (hM : 0 < M ω) : ∃ n : ℕ, ω ∈ E n ∧ M ω ≤ (3 : ℝ) ^ n := by
    have hpos : 0 < (exceptionalScale E ω).toReal := by dsimp [M] at hM; linarith
    have hfin : exceptionalScale E ω ≠ ∞ := ne_of_lt (ENNReal.toReal_pos_iff.mp hpos).2
    have hlt : ENNReal.ofReal (M ω) < exceptionalScale E ω := by
      rw [← ENNReal.ofReal_toReal hfin]
      apply (ENNReal.ofReal_lt_ofReal_iff hpos).2
      dsimp [M]
      linarith
    unfold exceptionalScale at hlt
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp hlt
    by_cases hmem : ω ∈ E n
    · refine ⟨n, hmem, ?_⟩
      rw [if_pos hmem] at hn
      have heq : (3 : ℝ≥0∞) ^ n = ENNReal.ofReal ((3 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      rw [heq] at hn
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hn)
    · rw [if_neg hmem] at hn
      exact (not_lt_zero hn).elim
  obtain ⟨θ, hθ, hi, hb⟩ := exp_moment_of_exceptional_scales μ E C hC s c hs hc hE
    M hMm hM0 hbound
  refine ⟨3 * θ, by positivity, ?_, ?_⟩
  · convert hi using 1
    funext ω
    dsimp only [M]
    congr 2
    ring
  · convert hb using 1
    congr 2
    funext ω
    dsimp only [M]
    congr 2
    ring

end Rigidity.Percolation

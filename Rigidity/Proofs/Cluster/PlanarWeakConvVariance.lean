import Rigidity.Proofs.Cluster.PlanarSwitchLocProb

/-!
# The variance step of Lemma 5.7 of Armstrong and Dario

If bounded random variables `X_i` (`i ∈ s`) are close in mean square to bounded random variables
`Y_i` which are pairwise independent, then the variance of each `X_{i₀}` is controlled by the
second moment of the sum: `Var[X_{i₀}] ≤ 4 E[(∑ X_i)²] + (4 |s| + 2) ∑ E[(X_i - Y_i)²]`
(`variance_le_of_pairwise_indep`). This is the chain of inequalities at the end of the proof of
Lemma 5.7: the variance of one term is at most the sum of the variances of the local versions,
which is the variance of their sum by independence.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem memLp_two_of_abs_le [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ ω, |f ω| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact h ω)

/-- `Var[A + B] ≤ 2 Var[A] + 2 E[B²]`. -/
theorem variance_add_le [IsProbabilityMeasure μ] {A B : Ω → ℝ} (hA : MemLp A 2 μ)
    (hB : MemLp B 2 μ) :
    variance (fun ω => A ω + B ω) μ ≤ 2 * variance A μ + 2 * ∫ ω, B ω ^ 2 ∂μ := by
  have hAi := hA.integrable one_le_two
  have hBi := hB.integrable one_le_two
  have hAB : MemLp (fun ω => A ω + B ω) 2 μ := hA.add hB
  have hVB : variance B μ ≤ ∫ ω, B ω ^ 2 ∂μ := variance_le_expectation_sq hB.aestronglyMeasurable
  rw [variance_eq_integral hAB.aemeasurable, variance_eq_integral hA.aemeasurable]
  rw [variance_eq_integral hB.aemeasurable] at hVB
  have hm : ∫ ω, (A ω + B ω) ∂μ = ∫ ω, A ω ∂μ + ∫ ω, B ω ∂μ := integral_add hAi hBi
  have i1 : Integrable (fun ω => (A ω + B ω - ∫ ω, (A ω + B ω) ∂μ) ^ 2) μ :=
    (hAB.sub (memLp_const _)).integrable_sq
  have i2 : Integrable (fun ω => (A ω - ∫ ω, A ω ∂μ) ^ 2) μ :=
    (hA.sub (memLp_const _)).integrable_sq
  have i3 : Integrable (fun ω => (B ω - ∫ ω, B ω ∂μ) ^ 2) μ :=
    (hB.sub (memLp_const _)).integrable_sq
  calc ∫ ω, (A ω + B ω - ∫ ω, (A ω + B ω) ∂μ) ^ 2 ∂μ
      ≤ ∫ ω, (2 * (A ω - ∫ ω, A ω ∂μ) ^ 2 + 2 * (B ω - ∫ ω, B ω ∂μ) ^ 2) ∂μ :=
        integral_mono i1 ((i2.const_mul 2).add (i3.const_mul 2)) fun ω => by
          rw [hm]
          nlinarith [sq_nonneg (A ω - ∫ ω, A ω ∂μ - (B ω - ∫ ω, B ω ∂μ))]
    _ = 2 * ∫ ω, (A ω - ∫ ω, A ω ∂μ) ^ 2 ∂μ + 2 * ∫ ω, (B ω - ∫ ω, B ω ∂μ) ^ 2 ∂μ := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by linarith

/-- **The variance step** of the proof of Lemma 5.7. -/
theorem variance_le_of_pairwise_indep [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (X Y : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hYm : ∀ i, Measurable (Y i)) {M : ℝ} (hX : ∀ i ω, |X i ω| ≤ M) (hY : ∀ i ω, |Y i ω| ≤ M)
    (hind : Set.Pairwise ↑s fun i j => IndepFun (Y i) (Y j) μ) :
    variance (X i₀) μ ≤ 4 * ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ +
      (4 * s.card + 2) * ∑ i ∈ s, ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ := by
  have hXL : ∀ i, MemLp (X i) 2 μ := fun i => memLp_two_of_abs_le (hXm i) (hX i)
  have hYL : ∀ i, MemLp (Y i) 2 μ := fun i => memLp_two_of_abs_le (hYm i) (hY i)
  have hDL : ∀ i, MemLp (fun ω => X i ω - Y i ω) 2 μ := fun i => (hXL i).sub (hYL i)
  have hDi : ∀ i, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ := fun i => (hDL i).integrable_sq
  have hD0 : ∀ i, 0 ≤ ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ := fun i =>
    integral_nonneg fun ω => sq_nonneg _
  -- the sums
  have hSXm : Measurable fun ω => ∑ i ∈ s, X i ω := Finset.measurable_sum s fun i _ => hXm i
  have hSYm : Measurable fun ω => ∑ i ∈ s, Y i ω := Finset.measurable_sum s fun i _ => hYm i
  have hSXL : MemLp (fun ω => ∑ i ∈ s, X i ω) 2 μ :=
    memLp_two_of_abs_le hSXm (C := s.card * M) fun ω =>
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        rw [← nsmul_eq_mul]
        exact Finset.sum_le_card_nsmul _ _ _ fun i _ => hX i ω)
  have hSDL : MemLp (fun ω => ∑ i ∈ s, Y i ω - ∑ i ∈ s, X i ω) 2 μ :=
    (memLp_two_of_abs_le hSYm (C := s.card * M) fun ω =>
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        rw [← nsmul_eq_mul]
        exact Finset.sum_le_card_nsmul _ _ _ fun i _ => hY i ω)).sub hSXL
  -- step 1
  have h1 : variance (X i₀) μ ≤ 2 * variance (Y i₀) μ + 2 * ∫ ω, (X i₀ ω - Y i₀ ω) ^ 2 ∂μ := by
    have e : X i₀ = fun ω => Y i₀ ω + (X i₀ ω - Y i₀ ω) := by funext ω; ring
    calc variance (X i₀) μ = variance (fun ω => Y i₀ ω + (X i₀ ω - Y i₀ ω)) μ := by rw [← e]
      _ ≤ _ := variance_add_le (hYL i₀) (hDL i₀)
  -- step 2
  have h2 : variance (Y i₀) μ ≤ variance (fun ω => ∑ i ∈ s, Y i ω) μ := by
    have hsum := IndepFun.variance_sum (fun i _ => hYL i) hind
    have e : (fun ω => ∑ i ∈ s, Y i ω) = ∑ i ∈ s, Y i := by
      funext ω
      rw [Finset.sum_apply]
    rw [e, hsum]
    exact Finset.single_le_sum (f := fun i => variance (Y i) μ)
      (fun i _ => variance_nonneg _ _) hi₀
  -- step 3
  have h3 : variance (fun ω => ∑ i ∈ s, Y i ω) μ ≤
      2 * ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ +
        2 * ∫ ω, (∑ i ∈ s, Y i ω - ∑ i ∈ s, X i ω) ^ 2 ∂μ := by
    have e : (fun ω => ∑ i ∈ s, Y i ω) =
        fun ω => (∑ i ∈ s, X i ω) + (∑ i ∈ s, Y i ω - ∑ i ∈ s, X i ω) := by
      funext ω; ring
    rw [e]
    refine (variance_add_le hSXL hSDL).trans ?_
    have := variance_le_expectation_sq (μ := μ) hSXL.aestronglyMeasurable
    simp only [Pi.pow_apply] at this
    linarith
  -- step 4
  have h4 : ∫ ω, (∑ i ∈ s, Y i ω - ∑ i ∈ s, X i ω) ^ 2 ∂μ ≤
      s.card * ∑ i ∈ s, ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ := by
    rw [← integral_finsetSum s fun i _ => hDi i, ← integral_const_mul]
    refine integral_mono hSDL.integrable_sq ((integrable_finsetSum s fun i _ => hDi i).const_mul _)
      fun ω => ?_
    have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => X i ω - Y i ω)
    have e : ∑ i ∈ s, Y i ω - ∑ i ∈ s, X i ω = -∑ i ∈ s, (X i ω - Y i ω) := by
      rw [Finset.sum_sub_distrib]; ring
    simp only
    rw [e, neg_sq]
    exact hcs
  -- step 5
  have h5 : ∫ ω, (X i₀ ω - Y i₀ ω) ^ 2 ∂μ ≤ ∑ i ∈ s, ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ :=
    Finset.single_le_sum (f := fun i => ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ) (fun i _ => hD0 i) hi₀
  have hS0 : 0 ≤ ∑ i ∈ s, ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ := Finset.sum_nonneg fun i _ => hD0 i
  have e : (4 * (s.card : ℝ) + 2) * ∑ i ∈ s, ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ =
      4 * (s.card * ∑ i ∈ s, ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ) +
        2 * ∑ i ∈ s, ∫ ω, (X i ω - Y i ω) ^ 2 ∂μ := by ring
  rw [e]
  linarith

end Rigidity.Proofs.Cluster

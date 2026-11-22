import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The exponential moment bound of Step 2 of the proof of Lemma 5.11 of Armstrong and Dario

Let `X_i`, `i ∈ s`, be random variables with values in `[0, A]` and expectations at most `ε`, each
independent of the sum of the others over every subset of `s`. Then for every `t`,

`P[∑_{i ∈ s} X_i ≥ |s| t] ≤ exp(-|s| (t - (e - 1) ε) / A)`.

This is the Chernoff bound of Step 2 of the proof of Lemma 5.11 of Armstrong and Dario (the
exponential moment of the sum is the product of the exponential moments by independence, and
`exp(x) ≤ 1 + (e - 1) x` for `x ∈ [0, 1]`, the inequalities `exp(s) ≤ 1 + C s` and
`log(1 + s) ≤ s` of the source, with `t = 1/A`). Independence of each variable from the sums of the
others is what local random variables on pairwise disjoint regions satisfy.
-/

open MeasureTheory ProbabilityTheory Real

namespace Rigidity.Proofs.Cluster

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `exp(x) ≤ 1 + (e - 1) x` for `x ∈ [0, 1]`, by convexity. -/
theorem exp_le_one_add_mul_of_mem_Icc {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    exp x ≤ 1 + (exp 1 - 1) * x := by
  have h := convexOn_exp.2 (Set.mem_univ 1) (Set.mem_univ 0) h0 (sub_nonneg.2 h1) (by ring)
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero, exp_zero] at h
  linarith

/-- **The exponential moment of a bounded nonnegative variable**:
`E[exp(X/A)] ≤ exp((e - 1) ε / A)` when `0 ≤ X ≤ A` and `E[X] ≤ ε`. -/
theorem mgf_le_exp_of_bounded [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {A ε : ℝ} (hA : 0 < A) (h0 : ∀ ω, 0 ≤ X ω) (h1 : ∀ ω, X ω ≤ A) (hε : ∫ ω, X ω ∂μ ≤ ε) :
    mgf X μ (1 / A) ≤ exp ((exp 1 - 1) * ε / A) := by
  have hXi : Integrable X μ := (integrable_const A).mono' hX.aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]; exact h1 ω)
  have he1 : 0 ≤ exp 1 - 1 := by
    have := add_one_le_exp (1 : ℝ)
    linarith
  have hpt : ∀ ω, exp (1 / A * X ω) ≤ 1 + (exp 1 - 1) * (X ω / A) := fun ω => by
    have h := exp_le_one_add_mul_of_mem_Icc (div_nonneg (h0 ω) hA.le) ((div_le_one hA).2 (h1 ω))
    rwa [one_div_mul_eq_div]
  have hexpm : Measurable fun ω => exp (1 / A * X ω) := (hX.const_mul _).exp
  have hexpi : Integrable (fun ω => exp (1 / A * X ω)) μ := by
    refine (integrable_const (exp 1)).mono' hexpm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    refine exp_le_exp.2 ?_
    rw [one_div_mul_eq_div]
    exact (div_le_one hA).2 (h1 ω)
  have hri : Integrable (fun ω => 1 + (exp 1 - 1) * (X ω / A)) μ :=
    (integrable_const _).add ((hXi.div_const A).const_mul _)
  calc mgf X μ (1 / A) = ∫ ω, exp (1 / A * X ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 + (exp 1 - 1) * (X ω / A)) ∂μ := integral_mono hexpi hri hpt
    _ = 1 + (exp 1 - 1) * ((∫ ω, X ω ∂μ) / A) := by
        rw [integral_add (integrable_const _) ((hXi.div_const A).const_mul _), integral_const,
          probReal_univ, one_smul, integral_const_mul, integral_div]
    _ ≤ 1 + (exp 1 - 1) * ε / A := by
        have : (∫ ω, X ω ∂μ) / A ≤ ε / A := div_le_div_of_nonneg_right hε hA.le
        have := mul_le_mul_of_nonneg_left this he1
        rw [mul_div_assoc]
        linarith
    _ ≤ exp ((exp 1 - 1) * ε / A) := by
        have := add_one_le_exp ((exp 1 - 1) * ε / A)
        linarith

/-- **The exponential moment of a sum of independent variables is the product.** -/
theorem mgf_sum_eq_prod_of_indepFun [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (X : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (t : ℝ)
    (hind : ∀ i ∈ s, ∀ T ⊆ s, i ∉ T → IndepFun (X i) (fun ω => ∑ j ∈ T, X j ω) μ) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ t = ∏ i ∈ s, mgf (X i) μ t := by
  suffices h : ∀ T ⊆ s, mgf (fun ω => ∑ i ∈ T, X i ω) μ t = ∏ i ∈ T, mgf (X i) μ t from
    h s subset_rfl
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.sum_empty, Finset.prod_empty]
      have h0 : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
      rw [h0, mgf_zero_fun, probReal_univ]
  | insert i T hi ih =>
      intro hsub
      have hiT : i ∈ s := hsub (Finset.mem_insert_self i T)
      have hTs : T ⊆ s := (Finset.subset_insert i T).trans hsub
      have e : (fun ω => ∑ j ∈ insert i T, X j ω) = X i + fun ω => ∑ j ∈ T, X j ω := by
        funext ω
        rw [Finset.sum_insert hi]
        rfl
      have hSm : Measurable fun ω => ∑ j ∈ T, X j ω := Finset.measurable_sum T fun j _ => hm j
      rw [e, (hind i hiT T hTs hi).mgf_add ((hm i).const_mul t).exp.aestronglyMeasurable
        (hSm.const_mul t).exp.aestronglyMeasurable, ih hTs, Finset.prod_insert hi]

/-- **The Chernoff bound of Step 2 of the proof of Lemma 5.11 of Armstrong and Dario**: for
variables with values in `[0, A]`, expectations at most `ε`, and each independent of the sums of
the others, `P[∑_{i ∈ s} X_i ≥ |s| t] ≤ exp(-|s| (t - (e - 1) ε) / A)`. -/
theorem measureReal_sum_ge_le_of_bounded [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i)) {A ε : ℝ} (hA : 0 < A)
    (h0 : ∀ i ω, 0 ≤ X i ω) (h1 : ∀ i ω, X i ω ≤ A) (hε : ∀ i ∈ s, ∫ ω, X i ω ∂μ ≤ ε)
    (hind : ∀ i ∈ s, ∀ T ⊆ s, i ∉ T → IndepFun (X i) (fun ω => ∑ j ∈ T, X j ω) μ) (t : ℝ) :
    μ.real {ω | (s.card : ℝ) * t ≤ ∑ i ∈ s, X i ω} ≤
      exp (-((s.card : ℝ) * (t - (exp 1 - 1) * ε)) / A) := by
  have hSm : Measurable fun ω => ∑ i ∈ s, X i ω := Finset.measurable_sum s fun i _ => hm i
  have hint : Integrable (fun ω => exp (1 / A * ∑ i ∈ s, X i ω)) μ := by
    refine (integrable_const (exp (s.card : ℝ))).mono' (hSm.const_mul _).exp.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    refine exp_le_exp.2 ?_
    have hsum : ∑ i ∈ s, X i ω ≤ (s.card : ℝ) * A := by
      calc ∑ i ∈ s, X i ω ≤ ∑ _i ∈ s, A := Finset.sum_le_sum fun i _ => h1 i ω
        _ = (s.card : ℝ) * A := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [one_div_mul_eq_div, div_le_iff₀ hA]
    exact hsum
  have hch := measure_ge_le_exp_mul_mgf ((s.card : ℝ) * t) (by positivity : (0 : ℝ) ≤ 1 / A) hint
  refine hch.trans ?_
  rw [mgf_sum_eq_prod_of_indepFun s X hm _ hind]
  have hprod : ∏ i ∈ s, mgf (X i) μ (1 / A) ≤ ∏ _i ∈ s, exp ((exp 1 - 1) * ε / A) :=
    Finset.prod_le_prod (fun i _ => mgf_nonneg) fun i hi =>
      mgf_le_exp_of_bounded (hm i) hA (h0 i) (h1 i) (hε i hi)
  rw [Finset.prod_const, ← Real.exp_nat_mul] at hprod
  calc exp (-(1 / A) * ((s.card : ℝ) * t)) * ∏ i ∈ s, mgf (X i) μ (1 / A)
      ≤ exp (-(1 / A) * ((s.card : ℝ) * t)) * exp ((s.card : ℝ) * ((exp 1 - 1) * ε / A)) :=
        mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp (-((s.card : ℝ) * (t - (exp 1 - 1) * ε)) / A) := by
        rw [← exp_add]
        congr 1
        ring

end Rigidity.Proofs.Cluster

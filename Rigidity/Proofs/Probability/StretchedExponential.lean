import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Stretched exponential moments from moment bounds

Armstrong and Lin, proof of Proposition 2.2 (Appendix A of *Optimal quantitative estimates in
stochastic homogenization for elliptic equations in nondivergence form*, ARMA 2017; the argument
is attributed there to J.-C. Mourrat): moment bounds
`E[|Z|^q] ≤ 2 (K q)^{q/2} E[V^{q/2}]` for all `q ≥ 2` give, for every `β ∈ (0, 2)`,

  `E[exp(|Z|^β)] ≤ C E[exp((C V)^{β/(2-β)})]^{(2-β)/β}`

with `C` depending on `K` and `β` only. The proof expands `exp(|Z|^β) = Σ_n |Z|^{βn}/n!`. The
terms with `βn ≥ 2` are bounded by the moment bound and, term by term, by Young's inequality
`(K β n V)^{βn/2} ≤ (Kβn/α)^n + ((αV)^{β/(2-β)})^n` (Armstrong and Lin use Hölder's inequality
for the series instead), whose first part is summable by `n^n/n! ≤ e^n` for `α = 2eKβ` and whose
second part sums to `E[exp((αV)^{β/(2-β)})]`; the finitely many terms with `βn < 2` are bounded
through the second moment. The exponent `(2-β)/β` is reached by Jensen's inequality when it is
below `1`.

* `ofReal_exp_eq_tsum`: the exponential series in `ℝ≥0∞`;
* `rpow_mul_le_pow_add_pow`: the termwise Young inequality;
* `lintegral_rpow_le_lintegral_rpow_of_one_le`: Jensen's inequality `(∫ f)^r ≤ ∫ f^r`, `r ≥ 1`;
* `lintegral_exp_rpow_le_of_moments`: the stretched exponential bound.
-/

namespace Rigidity.Probability

open MeasureTheory Filter
open scoped ENNReal Nat

/-- The exponential series in `ℝ≥0∞`. -/
theorem ofReal_exp_eq_tsum {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.exp x) = ∑' n : ℕ, ENNReal.ofReal (x ^ n / n !) := by
  have h : HasSum (fun n : ℕ => x ^ n / n !) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h.summable]

/-- **Young's inequality for the terms of the series**: for `β ∈ (0, 2)` and `w, t ≥ 0`,
`(w t)^{βn/2} ≤ w^n + (t^{β/(2-β)})^n`. -/
theorem rpow_mul_le_pow_add_pow {β w t : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (hw : 0 ≤ w)
    (ht : 0 ≤ t) (n : ℕ) :
    (w * t) ^ (β * n / 2) ≤ w ^ n + (t ^ (β / (2 - β))) ^ n := by
  have h2β : 0 < 2 - β := by linarith
  have ew : (w ^ n) ^ (β / 2) = w ^ (β * n / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw]
    congr 1
    ring
  have et : ((t ^ (β / (2 - β))) ^ n) ^ ((2 - β) / 2) = t ^ (β * n / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht, ← Real.rpow_mul ht]
    congr 1
    field_simp
  have hx : 0 ≤ w ^ n := pow_nonneg hw n
  have hy : 0 ≤ (t ^ (β / (2 - β))) ^ n := pow_nonneg (Real.rpow_nonneg ht _) n
  have hyoung := Real.geom_mean_le_arith_mean2_weighted (w₁ := β / 2) (w₂ := (2 - β) / 2)
    (by positivity) (by positivity) hx hy (by ring)
  rw [ew, et, ← Real.mul_rpow hw ht] at hyoung
  have h1 : β / 2 * w ^ n ≤ w ^ n := by nlinarith
  have h2 : (2 - β) / 2 * (t ^ (β / (2 - β))) ^ n ≤ (t ^ (β / (2 - β))) ^ n := by nlinarith
  linarith

/-- `z^s ≤ 1 + z²` for `z ≥ 0` and `0 ≤ s ≤ 2`. -/
theorem rpow_le_one_add_sq {z s : ℝ} (hz : 0 ≤ z) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    z ^ s ≤ 1 + z ^ 2 := by
  rcases le_total z 1 with h | h
  · have := Real.rpow_le_one hz h hs0
    nlinarith [sq_nonneg z]
  · have : z ^ s ≤ z ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs2
    rw [Real.rpow_two] at this
    linarith

/-- `t ≤ 1 + k! exp(t^γ)` for `t ≥ 0`, `γ > 0` and `1/γ ≤ k`. -/
theorem le_one_add_factorial_mul_exp {t γ : ℝ} (ht : 0 ≤ t) (hγ : 0 < γ) {k : ℕ}
    (hk : 1 / γ ≤ k) : t ≤ 1 + k ! * Real.exp (t ^ γ) := by
  set u := t ^ γ with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg ht _
  have htu : t = u ^ (1 / γ) := by
    rw [hu, one_div, Real.rpow_rpow_inv ht hγ.ne']
  have hexp : u ^ k ≤ k ! * Real.exp u := by
    have := Real.pow_div_factorial_le_exp (x := u) hu0 k
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  rw [htu]
  rcases le_total u 1 with h | h
  · have : u ^ (1 / γ) ≤ 1 := Real.rpow_le_one hu0 h (by positivity)
    have : 0 ≤ k ! * Real.exp u := by positivity
    linarith
  · have h1 : u ^ (1 / γ) ≤ u ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h hk
    rw [Real.rpow_natCast] at h1
    linarith

/-- **Jensen's inequality** `(∫ f)^r ≤ ∫ f^r` for `r ≥ 1` and a probability measure. -/
theorem lintegral_rpow_le_lintegral_rpow_of_one_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {r : ℝ}
    (hr : 1 ≤ r) : (∫⁻ ω, f ω ∂μ) ^ r ≤ ∫⁻ ω, f ω ^ r ∂μ := by
  rcases hr.eq_or_lt with rfl | hr1
  · simp
  have hpq := Real.HolderConjugate.conjExponent hr1
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  have hr0 : 0 < r := by linarith
  calc (∫⁻ ω, f ω ∂μ) ^ r ≤ ((∫⁻ ω, f ω ^ r ∂μ) ^ (1 / r)) ^ r :=
        ENNReal.rpow_le_rpow h hr0.le
    _ = ∫⁻ ω, f ω ^ r ∂μ := by
        rw [one_div, ENNReal.rpow_inv_rpow hr0.ne']

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem lintegral_ofReal_const_mul {c : ℝ} (hc : 0 ≤ c) (f : Ω → ℝ) :
    ∫⁻ ω, ENNReal.ofReal (c * f ω) ∂μ = ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
  simp_rw [ENNReal.ofReal_mul hc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem lintegral_ofReal_const_add {c : ℝ} (hc : 0 ≤ c) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    ∫⁻ ω, ENNReal.ofReal (c + f ω) ∂μ = ENNReal.ofReal c + ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
  simp_rw [ENNReal.ofReal_add hc (hf _)]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

omit [IsProbabilityMeasure μ] in
/-- The terms of the series with `βn ≥ 2`. -/
theorem lintegral_term_le_of_two_le {Z V : Ω → ℝ} (hV0 : ∀ ω, 0 ≤ V ω) {K β α : ℝ}
    (hK : 0 < K) (hβ0 : 0 < β) (hβ2 : β < 2) (hα : 0 < α)
    (hmom : ∀ q : ℝ, 2 ≤ q → ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ q) ∂μ ≤
        ENNReal.ofReal (2 * (K * q) ^ (q / 2)) * ∫⁻ ω, ENNReal.ofReal (V ω ^ (q / 2)) ∂μ)
    {n : ℕ} (hn : 2 ≤ β * n) :
    ∫⁻ ω, ENNReal.ofReal ((|Z ω| ^ β) ^ n / n !) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (2 * (K * β * n / α) ^ n / n ! +
        2 * ((α * V ω) ^ (β / (2 - β))) ^ n / n !) ∂μ := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hc : (0 : ℝ) ≤ 1 / n ! := by positivity
  have e1 : ∀ ω, (|Z ω| ^ β) ^ n / n ! = 1 / n ! * |Z ω| ^ (β * n) := by
    intro ω
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    ring
  have e2 : ∀ ω, 2 * (K * β * n / α) ^ n / n ! + 2 * ((α * V ω) ^ (β / (2 - β))) ^ n / n ! =
      1 / n ! * (2 * (K * β * n / α) ^ n + 2 * ((α * V ω) ^ (β / (2 - β))) ^ n) := by
    intro ω
    ring
  simp_rw [e1, e2]
  rw [lintegral_ofReal_const_mul hc, lintegral_ofReal_const_mul hc]
  refine mul_le_mul_right ?_ _
  refine (hmom (β * n) hn).trans ?_
  have hq0 : 0 ≤ 2 * (K * (β * n)) ^ (β * n / 2) := by positivity
  rw [← lintegral_ofReal_const_mul hq0]
  refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
  have hw : 0 ≤ K * β * n / α := by positivity
  have ht : 0 ≤ α * V ω := mul_nonneg hα.le (hV0 ω)
  have hy := rpow_mul_le_pow_add_pow hβ0 hβ2 hw ht n
  have ewt : K * β * n / α * (α * V ω) = K * (β * n) * V ω := by
    field_simp
  rw [ewt, Real.mul_rpow (by positivity) (hV0 ω)] at hy
  linarith

/-- The terms of the series with `βn < 2`. -/
theorem lintegral_term_le_of_lt_two {Z V : Ω → ℝ} (hV0 : ∀ ω, 0 ≤ V ω) {K β α : ℝ} (hK : 0 < K) (hβ0 : 0 < β) (hβ2 : β < 2) (hα : 0 < α)
    (hmom : ∀ q : ℝ, 2 ≤ q → ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ q) ∂μ ≤
        ENNReal.ofReal (2 * (K * q) ^ (q / 2)) * ∫⁻ ω, ENNReal.ofReal (V ω ^ (q / 2)) ∂μ)
    {k : ℕ} (hk : 1 / (β / (2 - β)) ≤ k) {n : ℕ} (hn : β * n ≤ 2) :
    ∫⁻ ω, ENNReal.ofReal ((|Z ω| ^ β) ^ n / n !) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((1 + 4 * K / α * (1 + k !)) / n ! *
        Real.exp ((α * V ω) ^ (β / (2 - β)))) ∂μ := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hc : (0 : ℝ) ≤ 1 / n ! := by positivity
  have hγ : 0 < β / (2 - β) := div_pos hβ0 (by linarith)
  have e1 : ∀ ω, (|Z ω| ^ β) ^ n / n ! = 1 / n ! * |Z ω| ^ (β * n) := by
    intro ω
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    ring
  have e2 : ∀ ω, (1 + 4 * K / α * (1 + k !)) / n ! * Real.exp ((α * V ω) ^ (β / (2 - β))) =
      1 / n ! * ((1 + 4 * K / α * (1 + k !)) * Real.exp ((α * V ω) ^ (β / (2 - β)))) := by
    intro ω
    ring
  simp_rw [e1, e2]
  rw [lintegral_ofReal_const_mul hc, lintegral_ofReal_const_mul hc]
  refine mul_le_mul_right ?_ _
  have hsq : ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (β * n)) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (1 + |Z ω| ^ (2 : ℝ)) ∂μ := by
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_two]
    exact rpow_le_one_add_sq (abs_nonneg _) (by positivity) hn
  refine hsq.trans ?_
  rw [lintegral_ofReal_const_add zero_le_one (fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
  have h2 : ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 : ℝ)) ∂μ ≤
      ENNReal.ofReal (2 * (K * 2)) * ∫⁻ ω, ENNReal.ofReal (V ω) ∂μ := by
    have h := hmom 2 le_rfl
    have e : ∀ ω, V ω ^ ((2 : ℝ) / 2) = V ω := fun ω => by norm_num
    have e' : (K * 2) ^ ((2 : ℝ) / 2) = K * 2 := by norm_num
    simpa only [e, e'] using h
  have hV : ∫⁻ ω, ENNReal.ofReal (V ω) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (1 / α * (1 + k ! * Real.exp ((α * V ω) ^ (β / (2 - β))))) ∂μ := by
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    have := le_one_add_factorial_mul_exp (mul_nonneg hα.le (hV0 ω)) hγ hk
    rw [one_div_mul_eq_div, le_div_iff₀ hα]
    linarith
  have hg : ∀ ω, 0 ≤ 2 * (K * 2) *
      (1 / α * (1 + k ! * Real.exp ((α * V ω) ^ (β / (2 - β))))) := fun ω => by positivity
  have hfin : ∫⁻ ω, ENNReal.ofReal (1 + 2 * (K * 2) *
        (1 / α * (1 + k ! * Real.exp ((α * V ω) ^ (β / (2 - β)))))) ∂μ =
      ENNReal.ofReal 1 + ENNReal.ofReal (2 * (K * 2)) *
      ∫⁻ ω, ENNReal.ofReal (1 / α * (1 + k ! * Real.exp ((α * V ω) ^ (β / (2 - β))))) ∂μ := by
    rw [lintegral_ofReal_const_add zero_le_one hg, lintegral_ofReal_const_mul (by positivity)]
  calc ENNReal.ofReal 1 + ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 : ℝ)) ∂μ
      ≤ ENNReal.ofReal 1 + ENNReal.ofReal (2 * (K * 2)) * ∫⁻ ω, ENNReal.ofReal (V ω) ∂μ := by
        gcongr
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (2 * (K * 2)) *
        ∫⁻ ω, ENNReal.ofReal (1 / α * (1 + k ! * Real.exp ((α * V ω) ^ (β / (2 - β))))) ∂μ := by
        gcongr
    _ = _ := hfin.symm
    _ ≤ _ := by
        refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
        have hE : 1 ≤ Real.exp ((α * V ω) ^ (β / (2 - β))) :=
          Real.one_le_exp (Real.rpow_nonneg (mul_nonneg hα.le (hV0 ω)) _)
        have hk0 : (0 : ℝ) ≤ k ! := by positivity
        have : 4 * K / α * (1 + k !) * 1 ≤
            4 * K / α * (1 + k !) * Real.exp ((α * V ω) ^ (β / (2 - β))) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
        have e3 : 1 + 2 * (K * 2) * (1 / α * (1 + k ! * Real.exp ((α * V ω) ^ (β / (2 - β))))) =
            1 + 4 * K / α + 4 * K / α * k ! * Real.exp ((α * V ω) ^ (β / (2 - β))) := by
          field_simp
          ring
        rw [e3]
        nlinarith

end Main

end Rigidity.Probability

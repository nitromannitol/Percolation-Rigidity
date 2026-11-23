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

/-- The bound on the `n`-th term of the series: for `n ≥ n₀` (where `βn ≥ 2`) the termwise Young
bound, below `n₀` the bound through the second moment. -/
noncomputable def seriesBound (K β α D : ℝ) (n₀ n : ℕ) (u : ℝ) : ℝ :=
  if n₀ ≤ n then 2 * (K * β * n / α) ^ n / n ! + 2 * u ^ n / n ! else D / n ! * Real.exp u

/-- `(K β n / α)^n / n! ≤ (1/2)^n` for `α = 2 e K β`, from `n^n/n! ≤ e^n`. -/
theorem pow_div_factorial_le_half_pow {K β : ℝ} (hK : 0 < K) (hβ : 0 < β) (n : ℕ) :
    (K * β * n / (2 * Real.exp 1 * K * β)) ^ n / n ! ≤ (1 / 2) ^ n := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have h1 : (n : ℝ) ^ n / n ! ≤ Real.exp 1 ^ n := by
    rw [Real.exp_one_pow]
    exact Real.pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg n) n
  have e : (K * β * n / (2 * Real.exp 1 * K * β)) ^ n / n ! =
      (1 / (2 * Real.exp 1)) ^ n * ((n : ℝ) ^ n / n !) := by
    rw [mul_div_assoc', ← mul_pow]
    congr 1
    congr 1
    field_simp
  rw [e]
  have h2 : (1 / (2 * Real.exp 1)) ^ n * Real.exp 1 ^ n = (1 / 2) ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The pointwise sum of the termwise bounds: `Σ_n seriesBound n u ≤ (4 + n₀ D + 2) e^u`. -/
theorem tsum_ofReal_seriesBound_le {K β D : ℝ} (hK : 0 < K) (hβ : 0 < β) (hD : 0 ≤ D)
    (n₀ : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ∑' n, ENNReal.ofReal (seriesBound K β (2 * Real.exp 1 * K * β) D n₀ n u) ≤
      ENNReal.ofReal ((4 + n₀ * D + 2) * Real.exp u) := by
  have hE : 1 ≤ Real.exp u := Real.one_le_exp hu
  set a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 * (1 / 2) ^ n)
  set b : ℕ → ℝ≥0∞ := fun n => if n < n₀ then ENNReal.ofReal D else 0
  set z : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (u ^ n / n !)
  have hle : ∀ n, ENNReal.ofReal (seriesBound K β (2 * Real.exp 1 * K * β) D n₀ n u) ≤
      a n + b n * ENNReal.ofReal (Real.exp u) + 2 * z n := by
    intro n
    have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    unfold seriesBound
    split_ifs with h
    · have hb : b n = 0 := by simp only [b]; rw [if_neg (by omega)]
      rw [hb, zero_mul, add_zero]
      have h1 := pow_div_factorial_le_half_pow hK hβ n
      have h2 : 2 * (K * β * n / (2 * Real.exp 1 * K * β)) ^ n / n ! ≤ 2 * (1 / 2) ^ n := by
        rw [mul_div_assoc]; linarith
      calc ENNReal.ofReal (2 * (K * β * n / (2 * Real.exp 1 * K * β)) ^ n / n ! +
            2 * u ^ n / n !)
          ≤ ENNReal.ofReal (2 * (1 / 2) ^ n + 2 * (u ^ n / n !)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [mul_div_assoc 2 (u ^ n)]
            linarith
        _ = a n + 2 * z n := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num)]
            simp [a, z]
    · have hb : b n = ENNReal.ofReal D := by simp only [b]; rw [if_pos (by omega)]
      rw [hb]
      have h1 : D / n ! * Real.exp u ≤ D * Real.exp u := by
        have h1n : (1 : ℝ) ≤ n ! := Nat.one_le_cast.mpr (Nat.factorial_pos n)
        have : D / n ! ≤ D := div_le_self hD h1n
        exact mul_le_mul_of_nonneg_right this (Real.exp_pos u).le
      calc ENNReal.ofReal (D / n ! * Real.exp u) ≤ ENNReal.ofReal (D * Real.exp u) :=
            ENNReal.ofReal_le_ofReal h1
        _ = ENNReal.ofReal D * ENNReal.ofReal (Real.exp u) := ENNReal.ofReal_mul hD
        _ ≤ a n + ENNReal.ofReal D * ENNReal.ofReal (Real.exp u) + 2 * z n := by
            rw [add_comm (a n)]
            exact le_add_right (le_add_right le_rfl)
  have hsa : ∑' n, a n = ENNReal.ofReal 4 := by
    simp only [a]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_two).mul_left 2), tsum_mul_left, tsum_geometric_two]
    norm_num
  have hsb : ∑' n, b n = (n₀ : ℝ≥0∞) * ENNReal.ofReal D := by
    rw [tsum_eq_sum (s := Finset.range n₀) (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp only [b]
      rw [if_neg (by omega)])]
    rw [Finset.sum_congr rfl (fun n hn => by
      simp only [Finset.mem_range] at hn
      simp only [b]
      rw [if_pos hn]), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsz : ∑' n, z n = ENNReal.ofReal (Real.exp u) := (ofReal_exp_eq_tsum hu).symm
  calc ∑' n, ENNReal.ofReal (seriesBound K β (2 * Real.exp 1 * K * β) D n₀ n u)
      ≤ ∑' n, (a n + b n * ENNReal.ofReal (Real.exp u) + 2 * z n) := ENNReal.tsum_le_tsum hle
    _ = ENNReal.ofReal 4 + (n₀ : ℝ≥0∞) * ENNReal.ofReal D * ENNReal.ofReal (Real.exp u) +
          2 * ENNReal.ofReal (Real.exp u) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
          hsa, hsb, hsz]
    _ ≤ ENNReal.ofReal ((4 + n₀ * D + 2) * Real.exp u) := by
        have h1 : (n₀ : ℝ≥0∞) * ENNReal.ofReal D * ENNReal.ofReal (Real.exp u) =
            ENNReal.ofReal (n₀ * D * Real.exp u) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
        have h2 : 2 * ENNReal.ofReal (Real.exp u) = ENNReal.ofReal (2 * Real.exp u) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [h1, h2, ← ENNReal.ofReal_add (by norm_num) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)

theorem continuous_seriesBound (K β α D : ℝ) (n₀ n : ℕ) :
    Continuous (seriesBound K β α D n₀ n) := by
  unfold seriesBound
  split_ifs <;> fun_prop

/-- **Raising the exponent to `1/γ`**: with `α' = α max(1, γ)^{1/γ}`,
`E[exp((αV)^γ)] ≤ E[exp((α'V)^γ)]^{1/γ}`; for `γ > 1` by Jensen's inequality, for `γ ≤ 1`
because the expectation is at least `1`. -/
theorem lintegral_exp_le_rpow {V : Ω → ℝ} (hV : AEMeasurable V μ) (hV0 : ∀ ω, 0 ≤ V ω)
    {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((α * V ω) ^ γ)) ∂μ ≤
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((α * max 1 γ ^ (1 / γ) * V ω) ^ γ)) ∂μ) ^ (1 / γ) := by
  have hΦ1 : 1 ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp ((α * V ω) ^ γ)) ∂μ := by
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂μ := by simp
      _ ≤ _ := lintegral_mono fun ω => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal
            (Real.one_le_exp (Real.rpow_nonneg (mul_nonneg hα.le (hV0 ω)) _))
  rcases le_or_gt γ 1 with h | h
  · rw [max_eq_left h, Real.one_rpow, mul_one]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((α * V ω) ^ γ)) ∂μ
        = (∫⁻ ω, ENNReal.ofReal (Real.exp ((α * V ω) ^ γ)) ∂μ) ^ (1 : ℝ) := by simp
      _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le hΦ1 (by rw [le_div_iff₀ hγ]; linarith)
  · rw [max_eq_right h.le]
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp ((α * V ω) ^ γ))) μ := by
      have : AEMeasurable (fun ω => α * V ω) μ := hV.const_mul α
      exact (Real.continuous_exp.measurable.comp_aemeasurable
        (this.pow_const γ)).ennreal_ofReal
    have hJ := lintegral_rpow_le_lintegral_rpow_of_one_le hmeas h.le
    have e : ∀ ω, ENNReal.ofReal (Real.exp ((α * V ω) ^ γ)) ^ γ =
        ENNReal.ofReal (Real.exp ((α * γ ^ (1 / γ) * V ω) ^ γ)) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hγ.le, ← Real.exp_mul]
      congr 2
      have hαV : 0 ≤ α * V ω := mul_nonneg hα.le (hV0 ω)
      rw [show α * γ ^ (1 / γ) * V ω = γ ^ (1 / γ) * (α * V ω) by ring,
        Real.mul_rpow (Real.rpow_nonneg hγ.le _) hαV, one_div,
        Real.rpow_inv_rpow hγ.le hγ.ne']
      ring
    simp_rw [e] at hJ
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((α * V ω) ^ γ)) ∂μ
        = ((∫⁻ ω, ENNReal.ofReal (Real.exp ((α * V ω) ^ γ)) ∂μ) ^ γ) ^ (1 / γ) := by
          rw [one_div, ENNReal.rpow_rpow_inv hγ.ne']
      _ ≤ _ := ENNReal.rpow_le_rpow hJ (by positivity)

end Main

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The stretched exponential bound** (Armstrong and Lin, Proposition 2.2, from the moment
inequality): if `E[|Z|^q] ≤ 2 (K q)^{q/2} E[V^{q/2}]` for every `q ≥ 2`, then for `β ∈ (0, 2)`,
`E[exp(|Z|^β)] ≤ C E[exp((C V)^{β/(2-β)})]^{(2-β)/β}` with `C` depending on `K` and `β` only. -/
theorem lintegral_exp_rpow_le_of_moments {K β : ℝ} (hK : 0 < K) (hβ0 : 0 < β) (hβ2 : β < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (Z V : Ω → ℝ),
      AEMeasurable Z μ → AEMeasurable V μ → (∀ ω, 0 ≤ V ω) →
      (∀ q : ℝ, 2 ≤ q → ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ q) ∂μ ≤
        ENNReal.ofReal (2 * (K * q) ^ (q / 2)) * ∫⁻ ω, ENNReal.ofReal (V ω ^ (q / 2)) ∂μ) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|Z ω| ^ β)) ∂μ ≤
        ENNReal.ofReal C *
          (∫⁻ ω, ENNReal.ofReal (Real.exp ((C * V ω) ^ (β / (2 - β)))) ∂μ) ^ ((2 - β) / β) := by
  have h2β : 0 < 2 - β := by linarith
  set γ := β / (2 - β) with hγ_def
  have hγ : 0 < γ := div_pos hβ0 h2β
  set α := 2 * Real.exp 1 * K * β with hα_def
  have hα : 0 < α := by positivity
  set n₀ : ℕ := ⌈2 / β⌉₊ with hn₀
  set k : ℕ := ⌈1 / γ⌉₊ with hk_def
  set D : ℝ := 1 + 4 * K / α * (1 + k !) with hD_def
  have hD : 0 ≤ D := by positivity
  set M : ℝ := 4 + n₀ * D + 2 with hM_def
  set α' : ℝ := α * max 1 γ ^ (1 / γ) with hα'_def
  set C : ℝ := max (max M α') 1 with hC_def
  have hC1 : 1 ≤ C := le_max_right _ _
  have hMC : M ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hα'C : α' ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨C, by linarith, ?_⟩
  intro μ _ Z V hZ hV hV0 hmom
  have hu0 : ∀ ω, 0 ≤ (α * V ω) ^ γ := fun ω => Real.rpow_nonneg (mul_nonneg hα.le (hV0 ω)) _
  have huM : AEMeasurable (fun ω => (α * V ω) ^ γ) μ := (hV.const_mul α).pow_const γ
  have hZm : ∀ n : ℕ, AEMeasurable (fun ω => ENNReal.ofReal ((|Z ω| ^ β) ^ n / n !)) μ := by
    intro n
    have : AEMeasurable (fun ω => |Z ω|) μ := continuous_abs.measurable.comp_aemeasurable hZ
    exact (((this.pow_const β).pow_const n).div_const _).ennreal_ofReal
  have hA : ∫⁻ ω, ENNReal.ofReal (Real.exp (|Z ω| ^ β)) ∂μ =
      ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal ((|Z ω| ^ β) ^ n / n !) ∂μ := by
    rw [← lintegral_tsum hZm]
    exact lintegral_congr fun ω => ofReal_exp_eq_tsum (Real.rpow_nonneg (abs_nonneg _) _)
  have hB : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal ((|Z ω| ^ β) ^ n / n !) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (seriesBound K β α D n₀ n ((α * V ω) ^ γ)) ∂μ := by
    intro n
    unfold seriesBound
    by_cases hn : n₀ ≤ n
    · simp only [if_pos hn]
      have h2n : 2 ≤ β * n := by
        have h1 : 2 / β ≤ n₀ := Nat.le_ceil _
        have h2 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
        have := le_trans h1 h2
        rw [div_le_iff₀ hβ0] at this
        linarith
      exact lintegral_term_le_of_two_le hV0 hK hβ0 hβ2 hα hmom h2n
    · simp only [if_neg hn]
      have hn' : β * n ≤ 2 := by
        have h1 : (n : ℝ) < 2 / β := (Nat.lt_ceil).1 (by omega)
        rw [lt_div_iff₀ hβ0] at h1
        linarith
      exact lintegral_term_le_of_lt_two hV0 hK hβ0 hβ2 hα hmom (Nat.le_ceil _) hn'
  have hsbm : ∀ n : ℕ, AEMeasurable
      (fun ω => ENNReal.ofReal (seriesBound K β α D n₀ n ((α * V ω) ^ γ))) μ := fun n =>
    ((continuous_seriesBound K β α D n₀ n).measurable.comp_aemeasurable huM).ennreal_ofReal
  have hF := lintegral_exp_le_rpow (μ := μ) hV hV0 hα hγ
  have hG : ∫⁻ ω, ENNReal.ofReal (Real.exp ((α' * V ω) ^ γ)) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp ((C * V ω) ^ γ)) ∂μ := by
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    have hα'0 : 0 ≤ α' := by positivity
    exact Real.exp_le_exp.2 (Real.rpow_le_rpow (mul_nonneg hα'0 (hV0 ω))
      (mul_le_mul_of_nonneg_right hα'C (hV0 ω)) hγ.le)
  have hexp : (2 - β) / β = 1 / γ := by rw [hγ_def, one_div_div]
  rw [hexp, hA]
  calc ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal ((|Z ω| ^ β) ^ n / n !) ∂μ
      ≤ ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal (seriesBound K β α D n₀ n ((α * V ω) ^ γ)) ∂μ :=
        ENNReal.tsum_le_tsum hB
    _ = ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal (seriesBound K β α D n₀ n ((α * V ω) ^ γ)) ∂μ :=
        (lintegral_tsum hsbm).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (M * Real.exp ((α * V ω) ^ γ)) ∂μ :=
        lintegral_mono fun ω => tsum_ofReal_seriesBound_le hK hβ0 hD n₀ (hu0 ω)
    _ = ENNReal.ofReal M * ∫⁻ ω, ENNReal.ofReal (Real.exp ((α * V ω) ^ γ)) ∂μ :=
        lintegral_ofReal_const_mul (by positivity) _
    _ ≤ ENNReal.ofReal C * (∫⁻ ω, ENNReal.ofReal (Real.exp ((α' * V ω) ^ γ)) ∂μ) ^ (1 / γ) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hMC) hF
    _ ≤ ENNReal.ofReal C * (∫⁻ ω, ENNReal.ofReal (Real.exp ((C * V ω) ^ γ)) ∂μ) ^ (1 / γ) := by
        gcongr

end Assembly

end Rigidity.Probability

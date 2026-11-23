import Rigidity.Proofs.Corrector.OsCalculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Moments and stretched-exponential moments (Dario, §5)

Two facts used in the proof of Dario's Theorem 1 (*Optimal corrector estimates on percolation
clusters*, §5).

* (est.exp.pol): if `X ≤ O_s(θ)`, then `E[X^q] ≤ 2 θ^q (q/s)^{q/s} e^{-q/s}` for every `q > 0`, from
  `y^a ≤ a^a e^{-a} e^y`. Dario prints the weaker factor `e^{q/s}`.
* Step 5 of the proof of Theorem 1: if `E[X^q] ≤ (A q^k)^q` for every `q ≥ 1`, then `X ≤ O_s(C)` for
  every `s < 1/k`, with `C` depending only on `A, k, s`. As printed, the exponential is expanded in
  its power series, `E[exp(X^s)] = Σ_l E[X^{sl}] / l!`; the moments of order `sl ≥ 1` are bounded by
  the hypothesis and those of order `sl < 1` by `1 + E[X]`, and the series converges since
  `l! ≥ l^l e^{-l}` and `sk < 1`. The normalization of the exponential moment is that of
  `isOsBond_of_integral_le` (the source rescales by an exponent `σ`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal Topology Nat

variable {d : ℕ} {p : unitInterval}

/-- `y^a ≤ a^a e^{-a} e^y` for `y ≥ 0` and `a > 0`. -/
theorem rpow_le_rpow_mul_exp {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    y ^ a ≤ a ^ a * Real.exp (-a) * Real.exp y := by
  rcases hy.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow ha.ne']
    positivity
  · have hlog : a * Real.log (y / a) ≤ y - a := by
      have := Real.log_le_sub_one_of_pos (div_pos hpos ha)
      have h2 : a * Real.log (y / a) ≤ a * (y / a - 1) := mul_le_mul_of_nonneg_left this ha.le
      have h3 : a * (y / a - 1) = y - a := by field_simp
      linarith
    rw [Real.log_div hpos.ne' ha.ne'] at hlog
    calc y ^ a = Real.exp (a * Real.log y) := by rw [Real.rpow_def_of_pos hpos, mul_comm]
      _ ≤ Real.exp (a * Real.log a + -a + y) := Real.exp_le_exp.mpr (by linarith)
      _ = a ^ a * Real.exp (-a) * Real.exp y := by
          rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos ha, mul_comm (Real.log a) a]

/-- **Dario, (est.exp.pol)**: `X ≤ O_s(θ)` gives `E[X^q] ≤ 2 θ^q (q/s)^{q/s} e^{-q/s}` for `q > 0`. -/
theorem IsOsBond.integral_rpow_le {X : Configuration d → ℝ} {s θ q : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hq : 0 < q) (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (h : IsOsBond d p X s θ) :
    Integrable (fun ω => X ω ^ q) (latticeBondLaw d p) ∧
      ∫ ω, X ω ^ q ∂latticeBondLaw d p ≤
        2 * θ ^ q * ((q / s) ^ (q / s) * Real.exp (-(q / s))) := by
  set a := q / s with ha
  have ha0 : 0 < a := div_pos hq hs
  have hpt : ∀ ω, X ω ^ q ≤ θ ^ q * (a ^ a * Real.exp (-a)) *
      Real.exp (Real.rpow (max (X ω / θ) 0) s) := by
    intro ω
    have hy : 0 ≤ max (X ω / θ) 0 := le_max_right _ _
    have hmax : max (X ω / θ) 0 = X ω / θ := max_eq_left (div_nonneg (hX0 ω) hθ.le)
    have h1 : (Real.rpow (max (X ω / θ) 0) s) ^ a ≤
        a ^ a * Real.exp (-a) * Real.exp (Real.rpow (max (X ω / θ) 0) s) :=
      rpow_le_rpow_mul_exp (Real.rpow_nonneg hy s) ha0
    have h2 : (Real.rpow (max (X ω / θ) 0) s) ^ a = X ω ^ q / θ ^ q := by
      change ((max (X ω / θ) 0) ^ s) ^ a = _
      rw [hmax, ← Real.rpow_mul (div_nonneg (hX0 ω) hθ.le), ha, mul_div_cancel₀ q hs.ne',
        Real.div_rpow (hX0 ω) hθ.le]
    rw [h2, div_le_iff₀ (Real.rpow_pos_of_pos hθ q)] at h1
    calc X ω ^ q ≤ a ^ a * Real.exp (-a) * Real.exp (Real.rpow (max (X ω / θ) 0) s) * θ ^ q := h1
      _ = _ := by ring
  have hint : Integrable (fun ω => X ω ^ q) (latticeBondLaw d p) := by
    refine Integrable.mono' (h.1.const_mul (θ ^ q * (a ^ a * Real.exp (-a))))
      (hX.pow_const q).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hX0 ω) q)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, X ω ^ q ∂latticeBondLaw d p
      ≤ ∫ ω, θ ^ q * (a ^ a * Real.exp (-a)) * Real.exp (Real.rpow (max (X ω / θ) 0) s)
          ∂latticeBondLaw d p := integral_mono hint (h.1.const_mul _) hpt
    _ = θ ^ q * (a ^ a * Real.exp (-a)) *
          ∫ ω, Real.exp (Real.rpow (max (X ω / θ) 0) s) ∂latticeBondLaw d p := integral_const_mul _ _
    _ ≤ θ ^ q * (a ^ a * Real.exp (-a)) * 2 := by
        gcongr
        exact h.2
    _ = _ := by ring

/-- The bound on the moment of order `s l` used in Step 5. -/
noncomputable def momentBound (A k s : ℝ) (l : ℕ) : ℝ :=
  (1 + A + (A * (s * l) ^ k) ^ (s * l)) / l !

theorem summable_momentBound {A k s : ℝ} (hA : 0 < A) (hs : 0 < s)
    (hsk : s * k < 1) : Summable (momentBound A k s) := by
  have h1 : Summable fun l : ℕ => (1 + A) / l ! := by
    refine ((Real.summable_pow_div_factorial 1).mul_left (1 + A)).congr fun l => ?_
    rw [one_pow]
    ring
  have h2 : Summable fun l : ℕ => (A * (s * l) ^ k) ^ (s * l) / l ! := by
    -- the ratio `A^s (s l)^{ks} e / l` tends to `0`
    set c : ℝ := A ^ s * s ^ (k * s) * Real.exp 1 with hc
    have hc0 : 0 < c := by positivity
    have hlim : Tendsto (fun l : ℕ => c * ((l : ℝ) ^ (k * s - 1))) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show 0 < 1 - k * s by nlinarith)).comp
        tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, neg_sub] using this.const_mul c
    have hev : ∀ᶠ l : ℕ in atTop, c * ((l : ℝ) ^ (k * s - 1)) ≤ 1 / 2 :=
      (hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
    refine Summable.of_norm_bounded_eventually_nat (summable_geometric_two) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with l hl hl1
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
    have hsl : 0 < s * l := mul_pos hs hl0
    have hfac : (l : ℝ) ^ l / l ! ≤ Real.exp l := Real.pow_div_factorial_le_exp (l : ℝ) hl0.le l
    have hfac' : (l : ℝ) ^ l / Real.exp 1 ^ l ≤ l ! := by
      rw [div_le_iff₀ (by positivity), ← Real.exp_nat_mul, mul_one]
      rw [div_le_iff₀ (by positivity)] at hfac
      linarith
    set Y : ℝ := (A * (s * l) ^ k) ^ s with hY
    have hY0 : 0 ≤ Y := by positivity
    have hpow : (A * (s * l) ^ k) ^ (s * l) = Y ^ l := by
      rw [hY, Real.rpow_mul (by positivity), Real.rpow_natCast]
    have hratio : Y * Real.exp 1 / l = c * ((l : ℝ) ^ (k * s - 1)) := by
      rw [hY, hc, Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul (by positivity),
        Real.mul_rpow hs.le hl0.le, Real.rpow_sub_one hl0.ne', mul_comm k s]
      field_simp
    rw [Real.norm_of_nonneg (by positivity), hpow]
    calc Y ^ l / l ! ≤ Y ^ l / ((l : ℝ) ^ l / Real.exp 1 ^ l) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hfac'
      _ = (Y * Real.exp 1 / l) ^ l := by
          rw [div_pow, mul_pow]
          field_simp
      _ = (c * ((l : ℝ) ^ (k * s - 1))) ^ l := by rw [hratio]
      _ ≤ (1 / 2) ^ l := pow_le_pow_left₀ (by positivity) hl l
  refine (h1.add h2).congr fun l => ?_
  rw [momentBound]
  ring

/-- **Dario, Step 5 of the proof of Theorem 1**: if `E[X^q] ≤ (A q^k)^q` for every `q ≥ 1`, then
`X ≤ O_s(C)` for every `s < 1/k`, with `C` depending only on `A, k, s`. -/
theorem isOsBond_of_moment_le {A k s : ℝ} (hA : 0 < A) (hs : 0 < s)
    (hsk : s * k < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : Configuration d → ℝ, Measurable X → (∀ ω, 0 ≤ X ω) →
      (∀ q : ℝ, 1 ≤ q → Integrable (fun ω => X ω ^ q) (latticeBondLaw d p) ∧
        ∫ ω, X ω ^ q ∂latticeBondLaw d p ≤ (A * q ^ k) ^ q) →
      IsOsBond d p X s C := by
  set S := ∑' l, momentBound A k s l with hSdef
  have hsum := summable_momentBound hA hs hsk
  set S' := max S 1 with hS'
  refine ⟨1 * S' ^ (1 / s), by positivity, fun X hX hX0 hmom => ?_⟩
  -- the moments of order `s l`
  have hmoml : ∀ l : ℕ, Integrable (fun ω => X ω ^ (s * l)) (latticeBondLaw d p) ∧
      ∫ ω, X ω ^ (s * l) ∂latticeBondLaw d p ≤ 1 + A + (A * (s * l) ^ k) ^ (s * l) := by
    intro l
    have hX1 := hmom 1 le_rfl
    simp only [Real.rpow_one, Real.one_rpow, mul_one] at hX1
    by_cases hl : 1 ≤ s * l
    · obtain ⟨hi, hb⟩ := hmom (s * l) hl
      refine ⟨hi, hb.trans ?_⟩
      have : 0 ≤ (A * (s * l) ^ k) ^ (s * l) := by positivity
      linarith
    · have hle : ∀ ω, X ω ^ (s * l) ≤ 1 + X ω := by
        intro ω
        rcases le_total (X ω) 1 with h1 | h1
        · have := Real.rpow_le_one (hX0 ω) h1 (by positivity : 0 ≤ s * l)
          linarith [hX0 ω]
        · have := Real.rpow_le_rpow_of_exponent_le h1 (not_le.1 hl).le
          rw [Real.rpow_one] at this
          linarith
      have hint : Integrable (fun ω => X ω ^ (s * l)) (latticeBondLaw d p) := by
        refine Integrable.mono' ((integrable_const 1).add hX1.1) (hX.pow_const _).aestronglyMeasurable
          (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (hX0 ω) _)]
        exact hle ω
      refine ⟨hint, ?_⟩
      calc ∫ ω, X ω ^ (s * l) ∂latticeBondLaw d p ≤ ∫ ω, (1 + X ω) ∂latticeBondLaw d p :=
            integral_mono hint ((integrable_const 1).add hX1.1) hle
        _ = 1 + ∫ ω, X ω ∂latticeBondLaw d p := by
            rw [integral_add (integrable_const 1) hX1.1]
            simp
        _ ≤ 1 + A := by linarith [hX1.2]
        _ ≤ 1 + A + (A * (s * l) ^ k) ^ (s * l) := by
            have : 0 ≤ (A * (s * l) ^ k) ^ (s * l) := by positivity
            linarith
  -- the exponential series
  have hexp : ∀ ω, Real.exp (Real.rpow (max (X ω / 1) 0) s) =
      ∑' l : ℕ, X ω ^ (s * l) / l ! := by
    intro ω
    rw [div_one, max_eq_left (hX0 ω)]
    have h := NormedSpace.expSeries_div_hasSum_exp (X ω ^ s)
    rw [← Real.exp_eq_exp_ℝ] at h
    refine h.tsum_eq.symm.trans ?_
    refine tsum_congr fun l => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hX0 ω)]
  have hmeas : ∀ l : ℕ, Measurable fun ω => X ω ^ (s * l) / l ! := fun l =>
    (hX.pow_const _).div_const _
  have hlin : ∫⁻ ω, ENNReal.ofReal (Real.exp (Real.rpow (max (X ω / 1) 0) s)) ∂latticeBondLaw d p ≤
      ENNReal.ofReal S := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (Real.rpow (max (X ω / 1) 0) s)) ∂latticeBondLaw d p
        = ∫⁻ ω, ∑' l : ℕ, ENNReal.ofReal (X ω ^ (s * l) / l !) ∂latticeBondLaw d p := by
          refine lintegral_congr fun ω => ?_
          rw [hexp ω, ENNReal.ofReal_tsum_of_nonneg (fun l => by
            have := Real.rpow_nonneg (hX0 ω) (s * l); positivity)]
          have h := NormedSpace.expSeries_div_hasSum_exp (X ω ^ s)
          refine (h.summable.congr fun l => ?_)
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hX0 ω)]
      _ = ∑' l : ℕ, ∫⁻ ω, ENNReal.ofReal (X ω ^ (s * l) / l !) ∂latticeBondLaw d p :=
          lintegral_tsum fun l => (hmeas l).ennreal_ofReal.aemeasurable
      _ ≤ ∑' l : ℕ, ENNReal.ofReal (momentBound A k s l) := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          obtain ⟨hi, hb⟩ := hmoml l
          have hi' : Integrable (fun ω => X ω ^ (s * l) / l !) (latticeBondLaw d p) := hi.div_const _
          rw [← ofReal_integral_eq_lintegral_ofReal hi' (Eventually.of_forall fun ω => by
            have := Real.rpow_nonneg (hX0 ω) (s * l); positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_div, momentBound]
          exact div_le_div_of_nonneg_right hb (by positivity)
      _ = ENNReal.ofReal S := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => by
            unfold momentBound; positivity) hsum]
  have hmeasE : Measurable fun ω => Real.exp (Real.rpow (max (X ω / 1) 0) s) :=
    measurable_exp_rpow_max_div s hX
  have hnn : 0 ≤ᵐ[latticeBondLaw d p] fun ω => Real.exp (Real.rpow (max (X ω / 1) 0) s) :=
    Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hint : Integrable (fun ω => Real.exp (Real.rpow (max (X ω / 1) 0) s))
      (latticeBondLaw d p) := by
    refine ⟨hmeasE.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hle : ∫ ω, Real.exp (Real.rpow (max (X ω / 1) 0) s) ∂latticeBondLaw d p ≤ S' := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeasE.aestronglyMeasurable]
    have hS0 : 0 ≤ S := tsum_nonneg fun l => by unfold momentBound; positivity
    exact (ENNReal.toReal_le_of_le_ofReal hS0 hlin).trans (le_max_left _ _)
  exact isOsBond_of_integral_le hs (le_max_right _ _) hint hle

end Rigidity.Corrector

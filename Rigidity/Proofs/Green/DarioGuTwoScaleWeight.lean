import Rigidity.Proofs.Green.DarioGuGaussian
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The weight of Proposition 4.3 of Dario–Gu

In the proof of Proposition 4.3 of Dario–Gu (lines 2241-2493 of the source) the equation of `w`
is tested against `ψ² w` with `ψ = exp(g(t, |· - y|)/C)`, where `g = dgShape` is the shape of the
exponent of `Φ_C` (the weight of `WeightedL2Le`). Two properties of `ψ` are used: (4.27),
`|∇ψ(· + h)| ≤ C̃ |∇ψ|` for `|h| ≤ 1`, and (4.41), `(∂_t ψ) ψ + ψ²/(4t) + C̃' |∇ψ|² ≤ C/t`.
Property (4.27) fails when `r = |x - y|` is large compared with `t`: the ratio of the derivatives
of `ψ` at `r + 1` and at `r` grows like `(r/t)^{1/C}`. The proof needs only the discrete form of
(4.41), in which `|∇ψ|²` is the square of the difference of the values of `ψ` at two points at
distance at most one, and this form holds for every `C` larger than a constant depending on
`C̃'` (`dgWeight_bound`): when `r > t` the term `(∂_t ψ) ψ = -(r/(C t)) ψ²` dominates the discrete
gradient.

* `dgShapeTimeDeriv t r` is the derivative of `g(·, r)` at `t` (`hasDerivAt_dgShape_time`).
* `dgShapeSlope t ρ` bounds the difference quotients of `g(t, ·)` below `ρ`
  (`dgShape_sub_le_slope`, `abs_dgShape_sub_le_slope`).
-/

namespace Rigidity.Green

/-- The derivative in time of the shape: `∂_t g(t, r) = -r²/t²` if `r ≤ t` and `-r/t` if
`r > t`. -/
noncomputable def dgShapeTimeDeriv (t r : ℝ) : ℝ :=
  if r ≤ t then -(r ^ 2 / t ^ 2) else -(r / t)

/-- The bound on the slope of the shape below `ρ`: `2ρ/t` if `ρ ≤ t` and `2 + ln(ρ/t)` if
`ρ > t`. -/
noncomputable def dgShapeSlope (t ρ : ℝ) : ℝ :=
  if ρ ≤ t then 2 * ρ / t else 2 + Real.log (ρ / t)

theorem dgShapeSlope_nonneg {t ρ : ℝ} (ht : 0 < t) (hρ : 0 ≤ ρ) : 0 ≤ dgShapeSlope t ρ := by
  unfold dgShapeSlope
  split_ifs with h
  · positivity
  · push Not at h
    have : 0 ≤ Real.log (ρ / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    linarith

theorem dgShapeSlope_mono {t ρ ρ' : ℝ} (ht : 0 < t) (h : ρ ≤ ρ') :
    dgShapeSlope t ρ ≤ dgShapeSlope t ρ' := by
  unfold dgShapeSlope
  split_ifs with h1 h2 h2
  · exact div_le_div_of_nonneg_right (by linarith) ht.le
  · push Not at h2
    have : 0 ≤ Real.log (ρ' / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    have : 2 * ρ / t ≤ 2 := by rw [div_le_iff₀ ht]; linarith
    linarith
  · exact absurd (h.trans h2) h1
  · push Not at h1
    have := Real.log_le_log (div_pos (by linarith) ht) (div_le_div_of_nonneg_right h ht.le)
    linarith

/-- `g(t, r') - g(t, r) ≤ (r' - r) G(t, r')` for `0 ≤ r ≤ r'`, with `G = dgShapeSlope`. -/
theorem dgShape_sub_le_slope {t r r' : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (hrr : r ≤ r') :
    dgShape t r' - dgShape t r ≤ (r' - r) * dgShapeSlope t r' := by
  unfold dgShape dgShapeSlope
  by_cases h' : r' ≤ t
  · have h : r ≤ t := hrr.trans h'
    simp only [if_pos h', if_pos h]
    have e : (r' - r) * (2 * r' / t) - (r' ^ 2 / t - r ^ 2 / t) = (r' - r) ^ 2 / t := by
      field_simp
      ring
    have : 0 ≤ (r' - r) ^ 2 / t := by positivity
    linarith
  · push Not at h'
    rw [if_neg (not_le.2 h'), if_neg (not_le.2 h')]
    have hL : Real.log (r' / t) ≤ r' / t - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith) ht)
    by_cases h : r ≤ t
    · rw [if_pos h]
      have h1 : r * Real.log (r' / t) ≤ r * (r' / t - 1) := mul_le_mul_of_nonneg_left hL hr
      have h2 : r * (r' / t) - r ^ 2 / t = r / t * (r' - r) := by ring
      have h3 : r / t * (r' - r) ≤ 1 * (r' - r) :=
        mul_le_mul_of_nonneg_right (by rw [div_le_one ht]; exact h) (by linarith)
      linarith
    · push Not at h
      rw [if_neg (not_le.2 h)]
      have hr0 : 0 < r := by linarith
      have hlog : Real.log (r' / t) - Real.log (r / t) ≤ r' / r - 1 := by
        rw [← Real.log_div (div_pos (by linarith) ht).ne' (div_pos hr0 ht).ne']
        have : r' / t / (r / t) = r' / r := by field_simp
        rw [this]
        exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hr0)
      have h2 : r * (Real.log (r' / t) - Real.log (r / t)) ≤ r' - r := by
        calc r * (Real.log (r' / t) - Real.log (r / t)) ≤ r * (r' / r - 1) :=
              mul_le_mul_of_nonneg_left hlog hr
          _ = r' - r := by field_simp
      linarith

/-- `|g(t, r') - g(t, r)| ≤ G(t, r + 1)` for `|r' - r| ≤ 1`. -/
theorem abs_dgShape_sub_le_slope {t r r' : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h : |r' - r| ≤ 1) : |dgShape t r' - dgShape t r| ≤ dgShapeSlope t (r + 1) := by
  have h1 := (abs_le.1 h).1
  have h2 := (abs_le.1 h).2
  rcases le_total r r' with hrr | hrr
  · rw [abs_of_nonneg (by linarith [dgShape_mono ht hr hrr])]
    calc dgShape t r' - dgShape t r ≤ (r' - r) * dgShapeSlope t r' := dgShape_sub_le_slope ht hr hrr
      _ ≤ 1 * dgShapeSlope t r' :=
          mul_le_mul_of_nonneg_right (by linarith) (dgShapeSlope_nonneg ht hr')
      _ ≤ dgShapeSlope t (r + 1) := by rw [one_mul]; exact dgShapeSlope_mono ht (by linarith)
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [dgShape_mono ht hr' hrr])]
    calc dgShape t r - dgShape t r' ≤ (r - r') * dgShapeSlope t r := dgShape_sub_le_slope ht hr' hrr
      _ ≤ 1 * dgShapeSlope t r :=
          mul_le_mul_of_nonneg_right (by linarith) (dgShapeSlope_nonneg ht hr)
      _ ≤ dgShapeSlope t (r + 1) := by rw [one_mul]; exact dgShapeSlope_mono ht (by linarith)

/-- `(e^b - e^a)² ≤ e^{2a} D² e^{2D}` for `|b - a| ≤ D`. -/
theorem sq_exp_sub_exp_le {a b D : ℝ} (h : |b - a| ≤ D) :
    (Real.exp b - Real.exp a) ^ 2 ≤ Real.exp a ^ 2 * (D ^ 2 * Real.exp D ^ 2) := by
  have h0 := abs_exp_neg_sub_exp_neg_le (-b) (-a)
  rw [neg_neg, neg_neg, show -b - -a = -(b - a) by ring, abs_neg] at h0
  have hD : 0 ≤ D := (abs_nonneg _).trans h
  have hmax : -min (-b) (-a) ≤ a + D := by
    rcases le_total (-b) (-a) with hh | hh
    · rw [min_eq_left hh]; linarith [le_abs_self (b - a)]
    · rw [min_eq_right hh]; linarith
  have h1 : |Real.exp b - Real.exp a| ≤ D * (Real.exp a * Real.exp D) := by
    calc |Real.exp b - Real.exp a| ≤ |b - a| * Real.exp (-min (-b) (-a)) := h0
      _ ≤ D * Real.exp (a + D) :=
          mul_le_mul h (Real.exp_le_exp.2 hmax) (Real.exp_pos _).le hD
      _ = D * (Real.exp a * Real.exp D) := by rw [Real.exp_add]
  calc (Real.exp b - Real.exp a) ^ 2 = |Real.exp b - Real.exp a| ^ 2 := (sq_abs _).symm
    _ ≤ (D * (Real.exp a * Real.exp D)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = Real.exp a ^ 2 * (D ^ 2 * Real.exp D ^ 2) := by ring

/-- The discrete gradient term against the time derivative: for `C ≥ max(6, 216 K)`, `t ≥ 1` and
`D = G(t, r + 1)/C`, `K D² e^{2D} ≤ -(∂_t g(t, r))/(2C) + 1/t`. -/
theorem slope_sq_le_timeDeriv {K C t r : ℝ} (hK : 0 < K) (hC6 : 6 ≤ C) (hCK : 216 * K ≤ C)
    (ht : 1 ≤ t) (hr : 0 ≤ r) :
    K * ((dgShapeSlope t (r + 1) / C) ^ 2 * Real.exp (dgShapeSlope t (r + 1) / C) ^ 2) ≤
      -(dgShapeTimeDeriv t r / C) / 2 + 1 / t := by
  have ht0 : 0 < t := by linarith
  have hC0 : 0 < C := by linarith
  have he1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hCC : 6 * C ≤ C ^ 2 := by nlinarith
  have hKC : 216 * K * C ≤ C ^ 2 := by nlinarith
  have ht1 : 0 < 1 / t := by positivity
  have hD0 : 0 ≤ dgShapeSlope t (r + 1) / C :=
    div_nonneg (dgShapeSlope_nonneg ht0 (by linarith)) hC0.le
  by_cases hrt1 : r + 1 ≤ t
  · have hrt : r ≤ t := by linarith
    have hS : dgShapeSlope t (r + 1) = 2 * (r + 1) / t := by
      unfold dgShapeSlope; rw [if_pos hrt1]
    have hT : dgShapeTimeDeriv t r = -(r ^ 2 / t ^ 2) := by
      unfold dgShapeTimeDeriv; rw [if_pos hrt]
    rw [hS, hT]
    have hDle : 2 * (r + 1) / t / C ≤ 1 / 2 := by
      rw [div_le_iff₀ hC0, div_le_iff₀ ht0]
      nlinarith [mul_le_mul_of_nonneg_right hC6 ht0.le]
    have hE : Real.exp (2 * (r + 1) / t / C) ^ 2 ≤ 3 := by
      rw [exp_sq]
      exact (Real.exp_le_exp.2 (by linarith)).trans he1.le
    have hD2 : (2 * (r + 1) / t / C) ^ 2 = 4 * (r + 1) ^ 2 / (t ^ 2 * C ^ 2) := by
      rw [div_pow, div_pow, mul_pow, div_div]
      norm_num
    calc K * ((2 * (r + 1) / t / C) ^ 2 * Real.exp (2 * (r + 1) / t / C) ^ 2)
        ≤ K * ((2 * (r + 1) / t / C) ^ 2 * 3) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (sq_nonneg _)) hK.le
      _ = 12 * K * (r + 1) ^ 2 / (t ^ 2 * C ^ 2) := by rw [hD2]; ring
      _ ≤ (r ^ 2 * C / 2 + t * C ^ 2) / (t ^ 2 * C ^ 2) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          nlinarith [mul_nonneg hK.le (sq_nonneg (r - 1)),
            mul_nonneg (sq_nonneg r) (by linarith : (0 : ℝ) ≤ C - 48 * K),
            mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1) (sq_nonneg C)]
      _ = -(-(r ^ 2 / t ^ 2) / C) / 2 + 1 / t := by
          field_simp
  · push Not at hrt1
    have hS : dgShapeSlope t (r + 1) = 2 + Real.log ((r + 1) / t) := by
      unfold dgShapeSlope; rw [if_neg (not_le.2 hrt1)]
    by_cases hrt : r ≤ t
    · have hT : dgShapeTimeDeriv t r = -(r ^ 2 / t ^ 2) := by
        unfold dgShapeTimeDeriv; rw [if_pos hrt]
      have hlog : Real.log ((r + 1) / t) ≤ 1 := by
        have h2 : (r + 1) / t ≤ 2 := by rw [div_le_iff₀ ht0]; linarith
        have := Real.log_le_log (div_pos (by linarith) ht0) h2
        linarith [Real.log_two_lt_d9]
      have hDle : dgShapeSlope t (r + 1) / C ≤ 3 / C := by
        rw [hS]; exact div_le_div_of_nonneg_right (by linarith) hC0.le
      have h3C : 3 / C ≤ 1 / 2 := by rw [div_le_iff₀ hC0]; linarith
      have hE : Real.exp (dgShapeSlope t (r + 1) / C) ^ 2 ≤ 3 := by
        rw [exp_sq]
        exact (Real.exp_le_exp.2 (by linarith)).trans he1.le
      have hD2 : (dgShapeSlope t (r + 1) / C) ^ 2 ≤ 9 / C ^ 2 := by
        calc (dgShapeSlope t (r + 1) / C) ^ 2 ≤ (3 / C) ^ 2 := pow_le_pow_left₀ hD0 hDle 2
          _ = 9 / C ^ 2 := by ring
      have hmain : K * ((dgShapeSlope t (r + 1) / C) ^ 2 *
          Real.exp (dgShapeSlope t (r + 1) / C) ^ 2) ≤ 27 * K / C ^ 2 := by
        calc K * ((dgShapeSlope t (r + 1) / C) ^ 2 * Real.exp (dgShapeSlope t (r + 1) / C) ^ 2)
            ≤ K * (9 / C ^ 2 * 3) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hD2 hE (by positivity) (by positivity)) hK.le
          _ = 27 * K / C ^ 2 := by ring
      rw [hT]
      have e : -(-(r ^ 2 / t ^ 2) / C) / 2 = r ^ 2 / t ^ 2 / C / 2 := by ring
      rw [e]
      have hq : 0 ≤ r ^ 2 / t ^ 2 / C / 2 := by positivity
      by_cases ht2 : t ≤ 2
      · have : 27 * K / C ^ 2 ≤ 1 / t := by
          rw [div_le_div_iff₀ (by positivity) ht0]
          nlinarith [mul_le_mul_of_nonneg_left ht2 (by linarith : (0 : ℝ) ≤ 27 * K)]
        linarith
      · push Not at ht2
        have h2r : t ≤ 2 * r := by linarith
        have h14 : 1 / 4 ≤ r ^ 2 / t ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        have hk : 27 * K / C ^ 2 ≤ 1 / 4 / C / 2 := by
          rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have : 1 / 4 / C / 2 ≤ r ^ 2 / t ^ 2 / C / 2 := by gcongr
        linarith
    · push Not at hrt
      have hT : dgShapeTimeDeriv t r = -(r / t) := by
        unfold dgShapeTimeDeriv; rw [if_neg (not_le.2 hrt)]
      have hr1 : 1 ≤ r := by linarith
      have hrt0 : 0 < r / t := div_pos (by linarith) ht0
      obtain ⟨s, hs⟩ : ∃ s, s = Real.log (r / t) := ⟨_, rfl⟩
      have hs0 : 0 ≤ s := by rw [hs]; exact Real.log_nonneg (by rw [le_div_iff₀ ht0]; linarith)
      have hes : Real.exp s = r / t := by rw [hs]; exact Real.exp_log hrt0
      have hlog : Real.log ((r + 1) / t) ≤ 1 + s := by
        have h2 : (r + 1) / t ≤ 2 * (r / t) := by
          rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) ht0.le
        have := Real.log_le_log (div_pos (by linarith) ht0) h2
        rw [Real.log_mul (by norm_num) hrt0.ne', ← hs] at this
        linarith [Real.log_two_lt_d9]
      have hDle : dgShapeSlope t (r + 1) / C ≤ (3 + s) / C := by
        rw [hS]; exact div_le_div_of_nonneg_right (by linarith) hC0.le
      have h3 : 3 + s ≤ 3 * Real.exp (s / 3) := by
        have := Real.add_one_le_exp (s / 3); linarith
      have hE : Real.exp (dgShapeSlope t (r + 1) / C) ^ 2 ≤ 3 * Real.exp (s / 3) := by
        rw [exp_sq]
        have hle : 2 * (dgShapeSlope t (r + 1) / C) ≤ 1 + s / 3 := by
          have : 2 * ((3 + s) / C) ≤ 1 + s / 3 := by
            rw [show 2 * ((3 + s) / C) = (6 + 2 * s) / C by ring, div_le_iff₀ hC0]
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C - 6) hs0]
          linarith
        calc Real.exp (2 * (dgShapeSlope t (r + 1) / C)) ≤ Real.exp (1 + s / 3) :=
              Real.exp_le_exp.2 hle
          _ = Real.exp 1 * Real.exp (s / 3) := Real.exp_add _ _
          _ ≤ 3 * Real.exp (s / 3) :=
              mul_le_mul_of_nonneg_right he1.le (Real.exp_pos _).le
      have hD2 : (dgShapeSlope t (r + 1) / C) ^ 2 ≤ 9 * Real.exp (s / 3) ^ 2 / C ^ 2 := by
        have h4 : dgShapeSlope t (r + 1) / C ≤ 3 * Real.exp (s / 3) / C :=
          hDle.trans (div_le_div_of_nonneg_right h3 hC0.le)
        calc (dgShapeSlope t (r + 1) / C) ^ 2 ≤ (3 * Real.exp (s / 3) / C) ^ 2 :=
              pow_le_pow_left₀ hD0 h4 2
          _ = 9 * Real.exp (s / 3) ^ 2 / C ^ 2 := by ring
      have hcube : Real.exp (s / 3) ^ 2 * Real.exp (s / 3) = r / t := by
        rw [← hes, sq, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have hmain : K * ((dgShapeSlope t (r + 1) / C) ^ 2 *
          Real.exp (dgShapeSlope t (r + 1) / C) ^ 2) ≤ 27 * K * (r / t) / C ^ 2 := by
        calc K * ((dgShapeSlope t (r + 1) / C) ^ 2 * Real.exp (dgShapeSlope t (r + 1) / C) ^ 2)
            ≤ K * (9 * Real.exp (s / 3) ^ 2 / C ^ 2 * (3 * Real.exp (s / 3))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hD2 hE (by positivity) (by positivity)) hK.le
          _ = 27 * K * (Real.exp (s / 3) ^ 2 * Real.exp (s / 3)) / C ^ 2 := by ring
          _ = 27 * K * (r / t) / C ^ 2 := by rw [hcube]
      have hk : 27 * K / C ^ 2 ≤ 1 / C / 2 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hfin : 27 * K * (r / t) / C ^ 2 ≤ r / t / C / 2 := by
        calc 27 * K * (r / t) / C ^ 2 = r / t * (27 * K / C ^ 2) := by ring
          _ ≤ r / t * (1 / C / 2) := mul_le_mul_of_nonneg_left hk hrt0.le
          _ = r / t / C / 2 := by ring
      rw [hT]
      have e : -(-(r / t) / C) / 2 = r / t / C / 2 := by ring
      rw [e]
      linarith

/-- **The repaired (4.27) and (4.41) of Dario–Gu.** For every `K > 0` and `A ≥ 0` there is
`C₀` such that for `C ≥ C₀` there is `C₁` with, for `t ≥ 1`, `r, r' ≥ 0` and `|r' - r| ≤ 1`,
`ψ(r)² (∂_t g(t, r)/C + A/t) + K (ψ(r') - ψ(r))² ≤ C₁/t`, where `ψ = exp(g(t, ·)/C)`, so that
`(∂_t ψ) ψ = ψ² ∂_t g/C`. -/
theorem dgWeight_bound {K A : ℝ} (hK : 0 < K) (hA : 0 ≤ A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ t r r' : ℝ, 1 ≤ t → 0 ≤ r → 0 ≤ r' → |r' - r| ≤ 1 →
        Real.exp (dgShape t r / C) ^ 2 * (dgShapeTimeDeriv t r / C + A / t) +
          K * (Real.exp (dgShape t r' / C) - Real.exp (dgShape t r / C)) ^ 2 ≤ C₁ / t := by
  refine ⟨max 6 (216 * K), by positivity, fun C hC => ?_⟩
  have hC6 : 6 ≤ C := (le_max_left _ _).trans hC
  have hCK : 216 * K ≤ C := (le_max_right _ _).trans hC
  have hC0 : 0 < C := by linarith
  set B := A + 1 with hB
  have hB0 : 0 < B := by linarith
  refine ⟨B * Real.exp (4 * B + 8 * B ^ 2 * C), by positivity, fun t r r' ht hr hr' hrr => ?_⟩
  have ht0 : 0 < t := by linarith
  set E := Real.exp (dgShape t r / C) ^ 2 with hEdef
  have hE0 : 0 ≤ E := by positivity
  set T := dgShapeTimeDeriv t r / C with hTdef
  set D := dgShapeSlope t (r + 1) / C with hDdef
  have hdiff : |dgShape t r' / C - dgShape t r / C| ≤ D := by
    rw [← sub_div, abs_div, abs_of_pos hC0]
    exact div_le_div_of_nonneg_right (abs_dgShape_sub_le_slope ht0 hr hr' hrr) hC0.le
  have h1 : K * (Real.exp (dgShape t r' / C) - Real.exp (dgShape t r / C)) ^ 2 ≤
      E * (K * (D ^ 2 * Real.exp D ^ 2)) := by
    have := sq_exp_sub_exp_le hdiff
    calc K * (Real.exp (dgShape t r' / C) - Real.exp (dgShape t r / C)) ^ 2
        ≤ K * (E * (D ^ 2 * Real.exp D ^ 2)) := mul_le_mul_of_nonneg_left this hK.le
      _ = E * (K * (D ^ 2 * Real.exp D ^ 2)) := by ring
  have h2 : K * (D ^ 2 * Real.exp D ^ 2) ≤ -T / 2 + 1 / t :=
    slope_sq_le_timeDeriv hK hC6 hCK ht hr
  have h3 : E * (T + A / t) + K * (Real.exp (dgShape t r' / C) -
      Real.exp (dgShape t r / C)) ^ 2 ≤ E * (t * T / 2 + B) / t := by
    have := mul_le_mul_of_nonneg_left h2 hE0
    have e : E * (T + A / t) + E * (-T / 2 + 1 / t) = E * (t * T / 2 + B) / t := by
      rw [hB]; field_simp; ring
    linarith
  refine h3.trans (div_le_div_of_nonneg_right ?_ ht0.le)
  have hEexp : E = Real.exp (2 * (dgShape t r / C)) := exp_sq _
  have hgs := dgShape_nonneg ht0 hr
  by_cases hrt : r ≤ t
  · have hg : dgShape t r = r ^ 2 / t := by unfold dgShape; rw [if_pos hrt]
    have htT : t * T / 2 = -(dgShape t r / C) / 2 := by
      rw [hTdef, hg]; unfold dgShapeTimeDeriv; rw [if_pos hrt]; field_simp
    rw [htT]
    set a := dgShape t r / C with ha
    have ha0 : 0 ≤ a := div_nonneg hgs hC0.le
    by_cases hab : 2 * B ≤ a
    · have : -a / 2 + B ≤ 0 := by linarith
      have := mul_nonpos_of_nonneg_of_nonpos hE0 this
      have : 0 < B * Real.exp (4 * B + 8 * B ^ 2 * C) := by positivity
      linarith
    · push Not at hab
      have hEle : E ≤ Real.exp (4 * B + 8 * B ^ 2 * C) := by
        rw [hEexp]; exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg B])
      calc E * (-a / 2 + B) ≤ E * B := mul_le_mul_of_nonneg_left (by linarith) hE0
        _ ≤ Real.exp (4 * B + 8 * B ^ 2 * C) * B := mul_le_mul_of_nonneg_right hEle hB0.le
        _ = B * Real.exp (4 * B + 8 * B ^ 2 * C) := by ring
  · push Not at hrt
    have htT : t * T / 2 = -(r / C) / 2 := by
      rw [hTdef]; unfold dgShapeTimeDeriv; rw [if_neg (not_le.2 hrt)]; field_simp
    rw [htT]
    by_cases hab : 2 * B * C ≤ r
    · have : -(r / C) / 2 + B ≤ 0 := by
        have : 2 * B ≤ r / C := by rw [le_div_iff₀ hC0]; linarith
        linarith
      have := mul_nonpos_of_nonneg_of_nonpos hE0 this
      have : 0 < B * Real.exp (4 * B + 8 * B ^ 2 * C) := by positivity
      linarith
    · push Not at hab
      have hgle : dgShape t r ≤ r ^ 2 := by
        have := dgShape_le_sq ht0 hr
        have : r ^ 2 / t ≤ r ^ 2 := div_le_self (sq_nonneg r) ht
        linarith
      have hEle : E ≤ Real.exp (4 * B + 8 * B ^ 2 * C) := by
        rw [hEexp]
        refine Real.exp_le_exp.2 ?_
        have : 2 * (dgShape t r / C) ≤ 2 * (r ^ 2 / C) := by
          have := div_le_div_of_nonneg_right hgle hC0.le
          linarith
        have : r ^ 2 / C ≤ 4 * B ^ 2 * C := by
          rw [div_le_iff₀ hC0]
          have : r ^ 2 ≤ (2 * B * C) ^ 2 := pow_le_pow_left₀ hr hab.le 2
          nlinarith
        nlinarith
      have hr0 : 0 ≤ r / C := div_nonneg hr hC0.le
      calc E * (-(r / C) / 2 + B) ≤ E * B := mul_le_mul_of_nonneg_left (by linarith) hE0
        _ ≤ Real.exp (4 * B + 8 * B ^ 2 * C) * B := mul_le_mul_of_nonneg_right hEle hB0.le
        _ = B * Real.exp (4 * B + 8 * B ^ 2 * C) := by ring

/-- `∂_t g(t, r) = dgShapeTimeDeriv t r` for `t > 0`. -/
theorem hasDerivAt_dgShape_time {t r : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => dgShape s r) (dgShapeTimeDeriv t r) t := by
  have hq : HasDerivAt (fun s : ℝ => r ^ 2 * s⁻¹) (r ^ 2 * -(t ^ 2)⁻¹) t :=
    (hasDerivAt_inv ht.ne').const_mul _
  have hl : HasDerivAt (fun s : ℝ => r * ((1 + Real.log r) - Real.log s)) (r * (0 - t⁻¹)) t :=
    ((hasDerivAt_const t (1 + Real.log r)).sub (Real.hasDerivAt_log ht.ne')).const_mul r
  rcases lt_trichotomy r t with h | h | h
  · have hT : dgShapeTimeDeriv t r = r ^ 2 * -(t ^ 2)⁻¹ := by
      unfold dgShapeTimeDeriv; rw [if_pos h.le]; ring
    rw [hT]
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    unfold dgShape
    rw [if_pos (Set.mem_Ioi.1 hs).le, div_eq_mul_inv]
  · have hr0 : 0 < r := h ▸ ht
    have hdiag : r ^ 2 / r = r * (1 + Real.log r - Real.log r) := by
      rw [add_sub_cancel_right, mul_one, pow_two, mul_div_assoc, div_self hr0.ne', mul_one]
    have hT : dgShapeTimeDeriv t r = r ^ 2 * -(t ^ 2)⁻¹ := by
      unfold dgShapeTimeDeriv; rw [if_pos h.le]; ring
    have hT' : r ^ 2 * -(t ^ 2)⁻¹ = r * (0 - t⁻¹) := by
      rw [← h, mul_neg, mul_inv_cancel₀ (pow_ne_zero 2 hr0.ne'), zero_sub, mul_neg,
        mul_inv_cancel₀ hr0.ne']
    have h1 : HasDerivWithinAt (fun s => dgShape s r) (dgShapeTimeDeriv t r) (Set.Ici t) t := by
      rw [hT]
      refine hq.hasDerivWithinAt.congr_of_mem (fun s hs => ?_) Set.self_mem_Ici
      unfold dgShape
      rw [if_pos (h.le.trans (Set.mem_Ici.1 hs)), div_eq_mul_inv]
    have h2 : HasDerivWithinAt (fun s => dgShape s r) (dgShapeTimeDeriv t r) (Set.Iic t) t := by
      rw [hT, hT']
      refine hl.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs hs0
        have hs0' : 0 < s := hs0
        unfold dgShape
        split_ifs with h'
        · have : s = r := le_antisymm (h ▸ Set.mem_Iic.1 hs) h'
          rw [this]
          exact hdiag
        · rw [Real.log_div hr0.ne' hs0'.ne']
          ring
      · unfold dgShape
        rw [if_pos h.le, ← h]
        exact hdiag
    have := h2.union h1
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have hT : dgShapeTimeDeriv t r = r * (0 - t⁻¹) := by
      unfold dgShapeTimeDeriv; rw [if_neg (not_le.2 h)]; ring
    rw [hT]
    refine hl.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h, Ioi_mem_nhds ht] with s hs hs0
    have hs0' : 0 < s := hs0
    unfold dgShape
    rw [if_neg (not_le.2 (Set.mem_Iio.1 hs)), Real.log_div (ht.trans h).ne' hs0'.ne']
    ring

end Rigidity.Green

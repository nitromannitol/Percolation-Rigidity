import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The iteration of the decay of `ω`

This file proves the iteration step in the proof of Lemma 5.10 of Armstrong and Dario (Steps 1-3), as
a statement about real sequences. Let `D_n` be bounded below by `-C σⁿ`, decrease along `τ_n ≥ 0`
up to `C σⁿ`:

`D_{n+1} ≤ D_n - c τ_n + C σⁿ`,

and be controlled by the weighted past of `τ` (the conclusion of Lemma 5.9):

`D_n ≤ C σⁿ + C ∑_{l ≤ n} ρ^{n-l} τ_l`.

If `0 ≤ σ < μ < 1` and `0 ≤ ρ ≤ μ²`, then `D_n ≤ K λⁿ` for some `λ < 1`.

Following Armstrong and Dario, the proof uses the weighted averages
`D̃_n = ∑_{k ≤ n} μ^{n-k} D_k`, which satisfy `D̃_{n+1} = μ D̃_n + D_{n+1}`; they are bounded above
by `C μⁿ + C T_n / (1 - μ)` with `T_n = ∑_{l ≤ n} μ^{n-l} τ_l` (from the control of `D` by the past
of `τ`), and they satisfy `D̃_{n+1} ≤ D̃_n - c T_n + C μⁿ` (from the decrease of `D`). Hence
`D̃_{n+1} ≤ θ D̃_n + K μⁿ` with `θ < 1`, which iterates to a geometric bound.
-/

open Finset

namespace Rigidity.Percolation

/-- The convolution `∑_{l ≤ n} a^{n-l} f(l)` of a sequence with a geometric sequence. -/
noncomputable def geomConv (a : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ l ∈ range (n + 1), a ^ (n - l) * f l

theorem geomConv_zero (a : ℝ) (f : ℕ → ℝ) : geomConv a f 0 = f 0 := by
  simp [geomConv]

theorem geomConv_succ (a : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    geomConv a f (n + 1) = a * geomConv a f n + f (n + 1) := by
  rw [geomConv, sum_range_succ, Nat.sub_self, pow_zero, one_mul, geomConv, mul_sum]
  congr 1
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hl)
  rw [show n + 1 - l = (n - l) + 1 by omega, pow_succ]
  ring

theorem geomConv_mono {a : ℝ} (ha : 0 ≤ a) {f g : ℕ → ℝ} (h : ∀ k, f k ≤ g k) (n : ℕ) :
    geomConv a f n ≤ geomConv a g n :=
  sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (pow_nonneg ha _)

theorem geomConv_nonneg {a : ℝ} (ha : 0 ≤ a) {f : ℕ → ℝ} (h : ∀ k, 0 ≤ f k) (n : ℕ) :
    0 ≤ geomConv a f n :=
  sum_nonneg fun l _ => mul_nonneg (pow_nonneg ha _) (h l)

theorem geomConv_linear (a b : ℝ) (f g : ℕ → ℝ) (n : ℕ) :
    geomConv a (fun k => b * f k + g k) n = b * geomConv a f n + geomConv a g n := by
  simp only [geomConv, mul_add, sum_add_distrib, mul_sum]
  congr 1
  exact sum_congr rfl fun l _ => by ring

theorem geomConv_sub (a : ℝ) (f g : ℕ → ℝ) (n : ℕ) :
    geomConv a (fun k => f k - g k) n = geomConv a f n - geomConv a g n := by
  simp only [geomConv, mul_sub, sum_sub_distrib]

/-- The convolution of two geometric sequences. -/
theorem sub_mul_geomConv_pow (μ σ : ℝ) (n : ℕ) :
    (μ - σ) * geomConv μ (fun k => σ ^ k) n = μ ^ (n + 1) - σ ^ (n + 1) := by
  induction n with
  | zero => rw [geomConv_zero]; ring
  | succ n ih =>
    rw [geomConv_succ, mul_add, ← mul_assoc, mul_comm (μ - σ) μ, mul_assoc, ih]
    ring

theorem geomConv_pow_le {μ σ : ℝ} (hσ : 0 ≤ σ) (hσμ : σ < μ) (hμ : μ ≤ 1) (n : ℕ) :
    geomConv μ (fun k => σ ^ k) n ≤ μ ^ n / (μ - σ) := by
  have hμσ : 0 < μ - σ := sub_pos.2 hσμ
  have hμ0 : 0 ≤ μ := hσ.trans hσμ.le
  rw [le_div_iff₀ hμσ, mul_comm, sub_mul_geomConv_pow]
  have h1 : μ ^ (n + 1) ≤ μ ^ n := pow_le_pow_of_le_one hμ0 hμ (Nat.le_succ n)
  have h2 : 0 ≤ σ ^ (n + 1) := pow_nonneg hσ _
  linarith

/-- Comparison of geometric convolutions with ratios `ρ ≤ μ²`. -/
theorem geomConv_le_geomConv_sq {ρ μ : ℝ} (hρ0 : 0 ≤ ρ) (hρμ : ρ ≤ μ ^ 2) {τ : ℕ → ℝ}
    (hτ : ∀ k, 0 ≤ τ k) (n : ℕ) : geomConv ρ τ n ≤ geomConv (μ ^ 2) τ n := by
  induction n with
  | zero => rw [geomConv_zero, geomConv_zero]
  | succ n ih =>
    rw [geomConv_succ, geomConv_succ]
    have h0 := geomConv_nonneg hρ0 hτ n
    nlinarith

/-- The iterated geometric convolution `∑_{k ≤ n} μ^{n-k} ∑_{l ≤ k} μ^{2(k-l)} τ_l`. -/
theorem one_sub_mul_geomConv_geomConv (μ : ℝ) (τ : ℕ → ℝ) (n : ℕ) :
    (1 - μ) * geomConv μ (geomConv (μ ^ 2) τ) n = geomConv μ τ n - μ * geomConv (μ ^ 2) τ n := by
  induction n with
  | zero => simp only [geomConv_zero]; ring
  | succ n ih =>
    rw [geomConv_succ μ (geomConv (μ ^ 2) τ), geomConv_succ μ τ, geomConv_succ (μ ^ 2) τ]
    have e : (1 - μ) * (μ * geomConv μ (geomConv (μ ^ 2) τ) n + (μ ^ 2 * geomConv (μ ^ 2) τ n +
        τ (n + 1))) = μ * ((1 - μ) * geomConv μ (geomConv (μ ^ 2) τ) n) +
        (1 - μ) * (μ ^ 2 * geomConv (μ ^ 2) τ n + τ (n + 1)) := by ring
    rw [e, ih]
    ring

/-- The shifted weighted sum. -/
theorem geomConv_succ_eq_shift (μ : ℝ) (D : ℕ → ℝ) (n : ℕ) :
    geomConv μ D (n + 1) = μ ^ (n + 1) * D 0 + geomConv μ (fun k => D (k + 1)) n := by
  induction n with
  | zero => simp only [geomConv_succ, geomConv_zero]; ring
  | succ n ih =>
    rw [geomConv_succ μ D (n + 1), ih, geomConv_succ μ (fun k => D (k + 1)) n]
    ring

/-- **The iteration of the decay of `ω`** (Armstrong and Dario, proof of Lemma 5.10, Steps 1-3, for
real sequences). -/
theorem exists_le_mul_pow_of_omega_iteration {D τ : ℕ → ℝ} {c C ρ σ μ : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσμ : σ < μ) (hμ1 : μ < 1) (hρ0 : 0 ≤ ρ) (hρμ : ρ ≤ μ ^ 2)
    (hτ : ∀ n, 0 ≤ τ n)
    (h1 : ∀ n, D (n + 1) ≤ D n - c * τ n + C * σ ^ n)
    (h2 : ∀ n, -(C * σ ^ n) ≤ D n)
    (h3 : ∀ n, D n ≤ C * σ ^ n + C * ∑ l ∈ range (n + 1), ρ ^ (n - l) * τ l) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∀ n, D n ≤ K * l ^ n := by
  -- normalized constants
  set C₀ := C + 1 with hC₀def
  have hC₀ : 0 < C₀ := by linarith
  set c₀ := min c C₀ with hc₀def
  have hc₀ : 0 < c₀ := lt_min hc hC₀
  have hc₀C : c₀ ≤ C₀ := min_le_right _ _
  have hμ0 : 0 < μ := lt_of_le_of_lt hσ0 hσμ
  have hμσ : 0 < μ - σ := sub_pos.2 hσμ
  have h1μ : 0 < 1 - μ := sub_pos.2 hμ1
  have hσn : ∀ n, 0 ≤ σ ^ n := fun n => pow_nonneg hσ0 n
  have hS0 : ∀ n, 0 ≤ geomConv ρ τ n := geomConv_nonneg hρ0 hτ
  have h1' : ∀ n, c₀ * τ n ≤ D n - D (n + 1) + C₀ * σ ^ n := fun n => by
    have := h1 n
    have : c₀ * τ n ≤ c * τ n := mul_le_mul_of_nonneg_right (min_le_left _ _) (hτ n)
    nlinarith [hσn n]
  have h2' : ∀ n, -(C₀ * σ ^ n) ≤ D n := fun n => by
    have := h2 n
    nlinarith [hσn n]
  have h3' : ∀ n, D n ≤ C₀ * σ ^ n + C₀ * geomConv ρ τ n := fun n => by
    have := h3 n
    have e : ∑ l ∈ range (n + 1), ρ ^ (n - l) * τ l = geomConv ρ τ n := rfl
    rw [e] at this
    nlinarith [hσn n, hS0 n]
  set G := geomConv μ (fun k => σ ^ k) with hGdef
  set T := geomConv μ τ with hTdef
  set Dt := geomConv μ D with hDtdef
  have hG : ∀ n, G n ≤ μ ^ n / (μ - σ) := geomConv_pow_le hσ0 hσμ hμ1.le
  have hG0 : ∀ n, 0 ≤ G n := geomConv_nonneg hμ0.le hσn
  have hT0 : ∀ n, 0 ≤ T n := geomConv_nonneg hμ0.le hτ
  -- upper bound for the weighted averages
  have hup : ∀ n, Dt n ≤ C₀ * (μ ^ n / (μ - σ)) + C₀ * (T n / (1 - μ)) := by
    intro n
    have a1 : Dt n ≤ geomConv μ (fun k => C₀ * σ ^ k + C₀ * geomConv ρ τ k) n :=
      geomConv_mono hμ0.le h3' n
    have a2 : geomConv μ (fun k => C₀ * σ ^ k + C₀ * geomConv ρ τ k) n =
        C₀ * G n + C₀ * geomConv μ (geomConv ρ τ) n := by
      rw [geomConv_linear]
      have := geomConv_linear μ C₀ (geomConv ρ τ) (fun _ => 0) n
      simp only [add_zero] at this
      rw [this]
      have hz : geomConv μ (fun _ => (0 : ℝ)) n = 0 := by simp [geomConv]
      rw [hz, add_zero]
    have a3 : geomConv μ (geomConv ρ τ) n ≤ geomConv μ (geomConv (μ ^ 2) τ) n :=
      geomConv_mono hμ0.le (geomConv_le_geomConv_sq hρ0 hρμ hτ) n
    have a4 := one_sub_mul_geomConv_geomConv μ τ n
    have a5 : 0 ≤ geomConv (μ ^ 2) τ n := geomConv_nonneg (sq_nonneg μ) hτ n
    have a6 : geomConv μ (geomConv (μ ^ 2) τ) n ≤ T n / (1 - μ) := by
      rw [le_div_iff₀ h1μ]
      nlinarith
    have a7 := hG n
    rw [a2] at a1
    have := mul_le_mul_of_nonneg_left (a3.trans a6) hC₀.le
    have := mul_le_mul_of_nonneg_left a7 hC₀.le
    linarith
  -- decrease of the weighted averages
  have hdec : ∀ n, Dt (n + 1) ≤ Dt n - c₀ * T n + μ ^ (n + 1) * D 0 + C₀ * G n := by
    intro n
    have b1 : geomConv μ (fun k => c₀ * τ k + 0) n ≤
        geomConv μ (fun k => (D k - D (k + 1)) + C₀ * σ ^ k) n :=
      geomConv_mono hμ0.le (fun k => by rw [add_zero]; linarith [h1' k]) n
    have b2 : geomConv μ (fun k => c₀ * τ k + 0) n = c₀ * T n := by
      rw [geomConv_linear]
      have hz : geomConv μ (fun _ => (0 : ℝ)) n = 0 := by simp [geomConv]
      rw [hz, add_zero]
    have b3 : geomConv μ (fun k => (D k - D (k + 1)) + C₀ * σ ^ k) n =
        Dt n - geomConv μ (fun k => D (k + 1)) n + C₀ * G n := by
      have := geomConv_linear μ C₀ (fun k => σ ^ k) (fun k => D k - D (k + 1)) n
      have e : (fun k => C₀ * σ ^ k + (D k - D (k + 1))) =
          (fun k => (D k - D (k + 1)) + C₀ * σ ^ k) := by
        funext k
        ring
      rw [e] at this
      rw [this, geomConv_sub]
      ring
    have b4 := geomConv_succ_eq_shift μ D n
    rw [b2, b3] at b1
    linarith
  -- the contraction
  set θ := 1 - c₀ * (1 - μ) / C₀ with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef, sub_nonneg, div_le_one hC₀]
    nlinarith
  have hθ1 : θ < 1 := by
    rw [hθdef]
    have : 0 < c₀ * (1 - μ) / C₀ := by positivity
    linarith
  set K₀ := c₀ * (1 - μ) / (μ - σ) + μ * |D 0| + C₀ / (μ - σ) with hK₀def
  have hK₀ : 0 ≤ K₀ := by positivity
  have hrec : ∀ n, Dt (n + 1) ≤ θ * Dt n + K₀ * μ ^ n := by
    intro n
    have d1 := hdec n
    have d2 := hup n
    have d3 : T n ≥ (1 - μ) / C₀ * (Dt n - C₀ * (μ ^ n / (μ - σ))) := by
      have : Dt n - C₀ * (μ ^ n / (μ - σ)) ≤ C₀ * (T n / (1 - μ)) := by linarith
      calc (1 - μ) / C₀ * (Dt n - C₀ * (μ ^ n / (μ - σ)))
          ≤ (1 - μ) / C₀ * (C₀ * (T n / (1 - μ))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = T n := by field_simp
    have d4 : -(c₀ * T n) ≤ -(c₀ * ((1 - μ) / C₀ * (Dt n - C₀ * (μ ^ n / (μ - σ))))) := by
      have := mul_le_mul_of_nonneg_left d3 hc₀.le
      linarith
    have d5 : μ ^ (n + 1) * D 0 ≤ μ * |D 0| * μ ^ n := by
      rw [pow_succ]
      have hμn : 0 ≤ μ ^ n := pow_nonneg hμ0.le n
      have := mul_le_mul_of_nonneg_left (le_abs_self (D 0)) (mul_nonneg hμn hμ0.le)
      linarith
    have d6 : C₀ * G n ≤ C₀ / (μ - σ) * μ ^ n := by
      have := mul_le_mul_of_nonneg_left (hG n) hC₀.le
      calc C₀ * G n ≤ C₀ * (μ ^ n / (μ - σ)) := this
        _ = C₀ / (μ - σ) * μ ^ n := by ring
    have e : -(c₀ * ((1 - μ) / C₀ * (Dt n - C₀ * (μ ^ n / (μ - σ))))) =
        (θ - 1) * Dt n + c₀ * (1 - μ) / (μ - σ) * μ ^ n := by
      rw [hθdef]
      field_simp
      ring
    rw [e] at d4
    have e2 : K₀ * μ ^ n = c₀ * (1 - μ) / (μ - σ) * μ ^ n + μ * |D 0| * μ ^ n +
        C₀ / (μ - σ) * μ ^ n := by
      rw [hK₀def]
      ring
    rw [e2]
    linarith
  -- iteration
  set l := (1 + max θ μ) / 2 with hldef
  have hθl : θ < l := by
    have := le_max_left θ μ
    rw [hldef]
    linarith [max_lt hθ1 hμ1]
  have hμl : μ ≤ l := by
    have := le_max_right θ μ
    rw [hldef]
    linarith [max_lt hθ1 hμ1]
  have hl1 : l < 1 := by
    rw [hldef]
    linarith [max_lt hθ1 hμ1]
  have hl0' : 0 < l := hμ0.trans_le hμl
  have hl0 : 0 ≤ l := hl0'.le
  set M := max (max (D 0) (K₀ / (l - θ))) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMD : D 0 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMK : K₀ ≤ (l - θ) * M := by
    have h := (le_max_right (D 0) (K₀ / (l - θ))).trans (le_max_left _ (0 : ℝ))
    rw [← hMdef, div_le_iff₀ (sub_pos.2 hθl)] at h
    linarith
  have hDt : ∀ n, Dt n ≤ M * l ^ n := by
    intro n
    induction n with
    | zero =>
      rw [hDtdef, geomConv_zero, pow_zero, mul_one]
      exact hMD
    | succ n ih =>
      have r1 := hrec n
      have hln : 0 ≤ l ^ n := pow_nonneg hl0 n
      have r2 : θ * Dt n ≤ θ * (M * l ^ n) := mul_le_mul_of_nonneg_left ih hθ0
      have r3 : K₀ * μ ^ n ≤ K₀ * l ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ0.le hμl n) hK₀
      have r4 : (θ * M + K₀) * l ^ n ≤ (M * l) * l ^ n :=
        mul_le_mul_of_nonneg_right (by linarith) hln
      rw [pow_succ]
      nlinarith
  -- back to `D`
  refine ⟨M + C₀ / (μ - σ), l, hl0', hl1, fun n => ?_⟩
  have hC₀μσ : 0 ≤ C₀ / (μ - σ) := by positivity
  cases n with
  | zero =>
    rw [pow_zero, mul_one]
    linarith
  | succ n =>
    have f1 : D (n + 1) = Dt (n + 1) - μ * Dt n := by
      rw [hDtdef, geomConv_succ]
      ring
    have f2 : -(C₀ * G n) ≤ Dt n := by
      have := geomConv_mono hμ0.le h2' n
      have e : geomConv μ (fun k => -(C₀ * σ ^ k)) n = -(C₀ * G n) := by
        simp only [geomConv, hGdef, mul_sum, ← sum_neg_distrib]
        exact sum_congr rfl fun k _ => by ring
      rw [e] at this
      exact this
    have f3 : μ * (C₀ * G n) ≤ C₀ / (μ - σ) * l ^ (n + 1) := by
      have := hG n
      have g1 : μ * (C₀ * G n) ≤ C₀ / (μ - σ) * μ ^ (n + 1) := by
        rw [pow_succ]
        have := mul_le_mul_of_nonneg_left this (mul_nonneg hμ0.le hC₀.le)
        calc μ * (C₀ * G n) = μ * C₀ * G n := by ring
          _ ≤ μ * C₀ * (μ ^ n / (μ - σ)) := this
          _ = C₀ / (μ - σ) * (μ ^ n * μ) := by ring
      exact g1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ0.le hμl _) hC₀μσ)
    have f4 := hDt (n + 1)
    have f5 : -(μ * Dt n) ≤ μ * (C₀ * G n) := by
      have := mul_le_mul_of_nonneg_left f2 hμ0.le
      linarith
    rw [f1, add_mul]
    linarith

/-- **The iteration of the decay of `ω` from a starting scale** (Armstrong and Dario, proof of
Lemma 5.10, Steps 1-3): the hypotheses are required only from a scale `N` on, and the control by the
past of `τ` is the one of Lemma 5.9, with the sum over all `l ≤ n`. -/
theorem exists_le_mul_pow_of_omega_iteration_of_ge {D τ : ℕ → ℝ} {c C ρ σ μ : ℝ} (N : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσμ : σ < μ) (hμ1 : μ < 1) (hρ0 : 0 ≤ ρ)
    (hρμ : ρ ≤ μ ^ 2) (hτ : ∀ n, 0 ≤ τ n)
    (h1 : ∀ n, N ≤ n → D (n + 1) ≤ D n - c * τ n + C * σ ^ n)
    (h2 : ∀ n, N ≤ n → -(C * σ ^ n) ≤ D n)
    (h3 : ∀ n, N ≤ n → D n ≤ C * σ ^ n + C * ∑ l ∈ range (n + 1), ρ ^ (n - l) * τ l) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∀ n, N ≤ n → D n ≤ K * l ^ n := by
  have hμ0 : 0 < μ := lt_of_le_of_lt hσ0 hσμ
  have hρμ' : ρ < μ := lt_of_le_of_lt hρμ (by nlinarith)
  set σ' := max σ ρ with hσ'
  have hσ'0 : 0 ≤ σ' := le_max_of_le_left hσ0
  have hσ'μ : σ' < μ := max_lt hσμ hρμ'
  have hσ'1 : σ' ≤ 1 := (hσ'μ.trans hμ1).le
  set B := ∑ l ∈ range N, ρ ^ (N - l) * τ l with hB
  have hB0 : 0 ≤ B := sum_nonneg fun l _ => mul_nonneg (pow_nonneg hρ0 _) (hτ l)
  set C' := C + C * B with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hσj : ∀ j, C * σ ^ (N + j) ≤ C * σ' ^ j := fun j => by
    have a : σ ^ (N + j) ≤ σ ^ j := by
      rw [pow_add]
      have : σ ^ N ≤ 1 := pow_le_one₀ hσ0 (hσμ.trans hμ1).le
      have := pow_nonneg hσ0 j
      nlinarith
    have b : σ ^ j ≤ σ' ^ j := pow_le_pow_left₀ hσ0 (le_max_left _ _) j
    exact mul_le_mul_of_nonneg_left (a.trans b) hC
  have hC'j : ∀ j, C * σ' ^ j ≤ C' * σ' ^ j := fun j => by
    have := pow_nonneg hσ'0 j
    have : 0 ≤ C * B * σ' ^ j := by positivity
    rw [hC']
    nlinarith
  obtain ⟨K, l, hl0, hl1, hK⟩ := exists_le_mul_pow_of_omega_iteration (D := fun j => D (N + j))
    (τ := fun j => τ (N + j)) (C := C') (ρ := ρ) (σ := σ') (μ := μ) hc hC'0 hσ'0 hσ'μ hμ1 hρ0 hρμ
    (fun j => hτ _) (fun j => by
      have := h1 (N + j) (Nat.le_add_right N j)
      simp only [← add_assoc]
      linarith [hσj j, hC'j j])
    (fun j => by
      have := h2 (N + j) (Nat.le_add_right N j)
      linarith [hσj j, hC'j j])
    (fun j => by
      have h := h3 (N + j) (Nat.le_add_right N j)
      have hsplit : ∑ l ∈ range (N + j + 1), ρ ^ (N + j - l) * τ l =
          ρ ^ j * B + ∑ i ∈ range (j + 1), ρ ^ (j - i) * τ (N + i) := by
        rw [show N + j + 1 = N + (j + 1) by ring, sum_range_add, hB, mul_sum]
        congr 1
        · refine sum_congr rfl fun l hl => ?_
          have hl' := mem_range.1 hl
          rw [show N + j - l = j + (N - l) by omega, pow_add]
          ring
        · refine sum_congr rfl fun i hi => ?_
          rw [show N + j - (N + i) = j - i by omega]
      rw [hsplit] at h
      have hρj : ρ ^ j ≤ σ' ^ j := pow_le_pow_left₀ hρ0 (le_max_right _ _) j
      have hS : 0 ≤ ∑ i ∈ range (j + 1), ρ ^ (j - i) * τ (N + i) :=
        sum_nonneg fun i _ => mul_nonneg (pow_nonneg hρ0 _) (hτ _)
      have e1 : C * (ρ ^ j * B) ≤ C * B * σ' ^ j := by
        have := mul_le_mul_of_nonneg_left hρj (mul_nonneg hC hB0)
        nlinarith
      have hσ'j := pow_nonneg hσ'0 j
      have e2 : C * ∑ i ∈ range (j + 1), ρ ^ (j - i) * τ (N + i) ≤
          C' * ∑ i ∈ range (j + 1), ρ ^ (j - i) * τ (N + i) := by
        have : C ≤ C' := by rw [hC']; nlinarith
        exact mul_le_mul_of_nonneg_right this hS
      have := hσj j
      rw [hC'] at e2 ⊢
      nlinarith)
  refine ⟨K / l ^ N, l, hl0, hl1, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have := hK j
  rw [pow_add, div_mul_eq_mul_div, mul_comm (l ^ N), ← mul_assoc, mul_div_assoc,
    div_self (pow_ne_zero N hl0.ne'), mul_one]
  exact this

end Rigidity.Percolation

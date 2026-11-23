import Rigidity.Proofs.Green.LazyCarneVaropoulos

/-!
# The Carne–Varopoulos bound in dimension two (Proposition 2.15 of Dario–Gu)

`carneVaropoulosTwo_holds : CarneVaropoulosTwo`: for the heat kernel of the variable speed random
walk on the open graph of a planar configuration, with `r = |x - y|`,

* `p(t, x, y) ≤ C exp(-r²/(C t))` for `r ≤ t`,
* `p(t, x, y) ≤ C exp(-(r/C) (1 + ln(r/t)))` for `t ≤ r`,

with `C = 200`. The source cites Davies 1993 (Corollaries 11 and 12). The proof here averages the
Carne–Varopoulos bound of the lazy walk `Qⁿ(x, y) ≤ 2 e^{-dist(x, y)²/(2n)}`
(`lazyPow_le_carneVaropoulos`; the graph distance is at least `r`) over the Poisson number of steps
`n ~ Pois(4t)`:

* for `r ≤ t`, the steps `n < 16t` contribute at most `2 e^{-r²/(32t)}` and the steps `n ≥ 16t` at
  most `2^{-16t} E[2^{Pois(4t)}] = 2^{-16t} e^{4t} ≤ e^{-r²/(32t)}`;
* for `t ≤ r ≤ 256 t`, `p(t, x, y) ≤ 3 e^{-r/18}` (`openHeat_le_exp_of_le_norm`);
* for `r > 256 t`, `Qⁿ(x, y) = 0` for `n < r` (finite propagation speed), and the Poisson tail
  `P[Pois(4t) ≥ r] ≤ θ^{-r} E[θ^{Pois(4t)}] = θ^{-r} e^{4t(θ - 1)}`, `θ = r/(4t)`, is at most
  `exp(-r (ln(r/t) - ln 4 - 1))`.
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

/-- The Poisson weights against `θ^n` sum to `e^{Dt(θ - 1)}`. -/
theorem hasSum_poissonWeight_mul_real_pow (D : ℕ) (t θ : ℝ) :
    HasSum (fun n => poissonWeight D t n * θ ^ n) (Real.exp (D * t * (θ - 1))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (θ * ((D : ℝ) * t))
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-D * t))
  have he : Real.exp (-D * t) * Real.exp (θ * (D * t)) = Real.exp (D * t * (θ - 1)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he] at h2
  have hf : (fun n => poissonWeight D t n * θ ^ n) =
      fun i => Real.exp (-D * t) * ((θ * ((D : ℝ) * t)) ^ i / i.factorial) := by
    funext n
    unfold poissonWeight
    rw [mul_pow]
    ring
  rw [hf]
  exact h2

/-- If `Qⁿ(x, y) ≤ A + B θⁿ` for every `n`, then `p(t, x, y) ≤ A + B e^{4t(θ - 1)}`. -/
theorem openHeat_le_of_lazyPow_le (ω : Configuration 2) {x y : Vertex 2} {t A B θ : ℝ}
    (ht : 0 ≤ t) (h : ∀ n, lazyPow (openGraph ω) 4 n x y ≤ A + B * θ ^ n) :
    openHeat ω t x y ≤ A + B * Real.exp (4 * t * (θ - 1)) := by
  have hdeg := openGraph_degree_le_four ω
  have hsum : HasSum (fun n => poissonWeight 4 t n * (A + B * θ ^ n))
      (A + B * Real.exp (4 * t * (θ - 1))) := by
    have := ((hasSum_poissonWeight (D := 4) t).mul_left A).add
      ((hasSum_poissonWeight_mul_real_pow 4 t θ).mul_left B)
    have hf : (fun n => poissonWeight 4 t n * (A + B * θ ^ n)) =
        fun n => A * poissonWeight 4 t n + B * (poissonWeight 4 t n * θ ^ n) := by
      funext n
      ring
    have hv : A * 1 + B * Real.exp (((4 : ℕ) : ℝ) * t * (θ - 1)) =
        A + B * Real.exp (4 * t * (θ - 1)) := by
      push_cast
      ring
    rw [hf, ← hv]
    exact this
  rw [openHeat, vsrwHeat, ← hsum.tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_vsrwHeat (by norm_num) hdeg t x y)
    hsum.summable
  exact mul_le_mul_of_nonneg_left (h n) (poissonWeight_nonneg ht n)

/-- Finite propagation speed: `Qⁿ(x, y) = 0` for `n < |x - y|`. -/
theorem lazyPow_eq_zero_of_lt_norm (ω : Configuration 2) {x y : Vertex 2} {n : ℕ}
    (hn : (n : ℝ) < ‖edz x y‖) : lazyPow (openGraph ω) 4 n x y = 0 := by
  by_contra hne
  obtain ⟨q, hq⟩ := exists_walk_of_lazyPow_ne_zero n x y hne
  have h1 := norm_edz_le_length q
  have h2 : (q.length : ℝ) ≤ n := by exact_mod_cast hq
  linarith

/-- The Carne–Varopoulos bound of the lazy walk with the Euclidean distance:
`Qⁿ(x, y) ≤ 2 e^{-|x - y|²/(2n)}` for `n ≥ 1`. -/
theorem lazyPow_le_two_mul_exp (ω : Configuration 2) (x y : Vertex 2) {n : ℕ} (hn : 1 ≤ n) :
    lazyPow (openGraph ω) 4 n x y ≤ 2 * Real.exp (-(‖edz x y‖ ^ 2 / (2 * n))) := by
  have hdeg := openGraph_degree_le_four ω
  by_cases hreach : (openGraph ω).Reachable x y
  · obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    have hd : ‖edz x y‖ ≤ (openGraph ω).dist x y := by
      have := norm_edz_le_length q
      rwa [hq] at this
    have hcv := lazyPow_le_carneVaropoulos (by norm_num) hdeg x y n hn
    refine hcv.trans ?_
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    gcongr
    rw [neg_div]
    apply neg_le_neg
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  · have h0 : lazyPow (openGraph ω) 4 n x y = 0 := by
      by_contra hne
      obtain ⟨q, -⟩ := exists_walk_of_lazyPow_ne_zero n x y hne
      exact hreach ⟨q⟩
    rw [h0]
    positivity

/-- **Gaussian regime**: `p(t, x, y) ≤ 3 e^{-r²/(32t)}` for `r = |x - y| ≤ t`. -/
theorem openHeat_le_of_norm_le (ω : Configuration 2) {x y : Vertex 2} {t : ℝ} (ht : 0 < t)
    (hr : ‖edz x y‖ ≤ t) : openHeat ω t x y ≤ 3 * Real.exp (-(‖edz x y‖ ^ 2 / (32 * t))) := by
  set r := ‖edz x y‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  have hdeg := openGraph_degree_le_four ω
  set N : ℕ := ⌈16 * t⌉₊ with hN
  have hN1 : 16 * t ≤ N := Nat.le_ceil _
  have hpt : ∀ n : ℕ, lazyPow (openGraph ω) 4 n x y ≤
      2 * Real.exp (-(r ^ 2 / (32 * t))) + (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
    intro n
    have h01 := lazyPow_mem_Icc (by norm_num) hdeg n x y
    have hE : 0 ≤ (2 : ℝ)⁻¹ ^ N * 2 ^ n := by positivity
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [lazyPow_zero]
      split_ifs with hxy
      · subst hxy
        have : r = 0 := by rw [hrdef, edz_self, norm_zero]
        rw [this]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
          Real.exp_zero, mul_one]
        linarith
      · positivity
    by_cases hnN : n < N
    · have hnt : (n : ℝ) ≤ 16 * t := (Nat.lt_ceil.1 hnN).le
      have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
      have h1 := lazyPow_le_two_mul_exp ω x y hnpos
      have h2 : Real.exp (-(r ^ 2 / (2 * n))) ≤ Real.exp (-(r ^ 2 / (32 * t))) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        linarith
      linarith
    · have hpow : 1 ≤ (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
        rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
        exact pow_le_pow_right₀ (by norm_num) (not_lt.1 hnN)
      have : 0 ≤ 2 * Real.exp (-(r ^ 2 / (32 * t))) := by positivity
      linarith [h01.2]
  have hle := openHeat_le_of_lazyPow_le ω ht.le hpt
  have htail : (2 : ℝ)⁻¹ ^ N * Real.exp (4 * t * (2 - 1)) ≤ Real.exp (-(r ^ 2 / (32 * t))) := by
    have h2 : (2 : ℝ)⁻¹ ^ N = Real.exp (-(N * Real.log 2)) := by
      rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), inv_pow]
    rw [h2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl2 := Real.log_two_gt_d9
    have hrt : r ^ 2 / (32 * t) ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  linarith

/-- **Far regime**: `p(t, x, y) ≤ exp(-r (ln(r/t) - ln 4 - 1))` for `r = |x - y| ≥ 4t`. -/
theorem openHeat_le_of_four_mul_le_norm (ω : Configuration 2) {x y : Vertex 2} {t : ℝ}
    (ht : 0 < t) (hr : 4 * t ≤ ‖edz x y‖) :
    openHeat ω t x y ≤
      Real.exp (-(‖edz x y‖ * (Real.log (‖edz x y‖ / t) - Real.log 4 - 1))) := by
  set r := ‖edz x y‖ with hrdef
  have hr0 : 0 < r := by linarith
  set θ := r / (4 * t) with hθ
  have hθ1 : 1 ≤ θ := by rw [hθ, le_div_iff₀ (by positivity)]; linarith
  have hθ0 : 0 < θ := by linarith
  set m : ℕ := ⌈r⌉₊ with hm
  have hmr : r ≤ m := Nat.le_ceil _
  have hdeg := openGraph_degree_le_four ω
  have hpt : ∀ n : ℕ, lazyPow (openGraph ω) 4 n x y ≤ 0 + (θ ^ m)⁻¹ * θ ^ n := by
    intro n
    have h01 := lazyPow_mem_Icc (by norm_num) hdeg n x y
    by_cases hnm : n < m
    · rw [lazyPow_eq_zero_of_lt_norm ω (Nat.lt_ceil.1 hnm)]
      positivity
    · have : 1 ≤ (θ ^ m)⁻¹ * θ ^ n := by
        rw [inv_mul_eq_div, one_le_div (by positivity)]
        exact pow_le_pow_right₀ hθ1 (not_lt.1 hnm)
      linarith [h01.2]
  have hle := openHeat_le_of_lazyPow_le ω ht.le hpt
  rw [zero_add] at hle
  refine hle.trans ?_
  have hlogθ : Real.log θ = Real.log (r / t) - Real.log 4 := by
    rw [hθ, show r / (4 * t) = (r / t) / 4 by field_simp, Real.log_div (by positivity)
      (by norm_num)]
  have hl0 : 0 ≤ Real.log θ := Real.log_nonneg hθ1
  have hpow : (θ ^ m)⁻¹ ≤ Real.exp (-(r * Real.log θ)) := by
    rw [Real.exp_neg, inv_le_inv₀ (by positivity) (Real.exp_pos _), ← Real.rpow_natCast,
      Real.rpow_def_of_pos hθ0]
    apply Real.exp_le_exp.2
    nlinarith
  have hexp : Real.exp (4 * t * (θ - 1)) ≤ Real.exp r := by
    apply Real.exp_le_exp.2
    have : 4 * t * θ = r := by rw [hθ]; field_simp
    nlinarith
  calc (θ ^ m)⁻¹ * Real.exp (4 * t * (θ - 1)) ≤ Real.exp (-(r * Real.log θ)) * Real.exp r :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(r * (Real.log (r / t) - Real.log 4 - 1))) := by
        rw [← Real.exp_add, hlogθ]
        ring_nf

/-- **Dario–Gu, Proposition 2.15** (Carne–Varopoulos bound) in dimension two, with `C = 200`. -/
theorem carneVaropoulosTwo_holds : CarneVaropoulosTwo := by
  refine ⟨200, by norm_num, fun ω K _ x _ y _ t ht => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · change openHeat ω t x y ≤ 200 * Real.exp (-(‖edz x y‖ ^ 2 / (200 * t)))
    have h := openHeat_le_of_norm_le ω ht hr
    refine h.trans ?_
    have : Real.exp (-(‖edz x y‖ ^ 2 / (32 * t))) ≤ Real.exp (-(‖edz x y‖ ^ 2 / (200 * t))) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      linarith
    have := Real.exp_pos (-(‖edz x y‖ ^ 2 / (200 * t)))
    linarith
  · change openHeat ω t x y ≤
      200 * Real.exp (-(‖edz x y‖ / 200 * (1 + Real.log (‖edz x y‖ / t))))
    set r := ‖edz x y‖ with hrdef
    have hr0 : 0 < r := lt_of_lt_of_le ht hr
    have hrt : 1 ≤ r / t := by rw [le_div_iff₀ ht]; linarith
    have hL0 : 0 ≤ Real.log (r / t) := Real.log_nonneg hrt
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hl256 : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    have hE := Real.exp_pos (-(r / 200 * (1 + Real.log (r / t))))
    rcases le_or_gt r (256 * t) with hnear | hfar
    · have h := openHeat_le_exp_of_le_norm ω ht hr
      refine h.trans ?_
      have hL : Real.log (r / t) ≤ Real.log 256 :=
        Real.log_le_log (by positivity) (by rw [div_le_iff₀ ht]; linarith)
      have : Real.exp (-(r / 18)) ≤ Real.exp (-(r / 200 * (1 + Real.log (r / t)))) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        have h1 : 1 + Real.log (r / t) ≤ 11 := by linarith
        nlinarith
      linarith
    · have h := openHeat_le_of_four_mul_le_norm ω ht (by linarith)
      refine h.trans ?_
      have hL : Real.log 256 ≤ Real.log (r / t) :=
        Real.log_le_log (by norm_num) (by rw [le_div_iff₀ ht]; linarith)
      have : Real.exp (-(r * (Real.log (r / t) - Real.log 4 - 1))) ≤
          Real.exp (-(r / 200 * (1 + Real.log (r / t)))) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        have h1 : (1 + Real.log (r / t)) / 200 ≤ Real.log (r / t) - Real.log 4 - 1 := by
          linarith
        nlinarith
      linarith

end Rigidity.Green

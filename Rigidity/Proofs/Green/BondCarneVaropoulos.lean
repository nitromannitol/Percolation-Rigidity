import Rigidity.Proofs.Green.BondHeat
import Rigidity.Proofs.Green.PlanarCarneVaropoulos
import Rigidity.Proofs.WeakPoincare.Balls

/-!
# The Carne–Varopoulos bound on `ℤ^d` (Proposition 2.15 of Dario–Gu in every dimension)

`carneVaropoulos_holds : CarneVaropoulos d`: for the heat kernel `bondHeat` of the variable speed
random walk on the open graph of a configuration of `ℤ^d`, with `r = |x - y|` (Euclidean),

* `p(t, x, y) ≤ C exp(-r²/(C t))` for `r ≤ t`,
* `p(t, x, y) ≤ C exp(-(r/C) (1 + ln(r/t)))` for `t ≤ r`,

with `C = 100 d²`. The source cites Davies 1993 (Corollaries 11 and 12). The proof is the planar
one (`carneVaropoulosTwo_holds`) with the Poisson clock of rate `2d`: it averages the
Carne–Varopoulos bound of the lazy walk `Qⁿ(x, y) ≤ 2 e^{-dist(x, y)²/(2n)}`
(`lazyPow_le_carneVaropoulos`; the graph distance is at least `r`) over `n ~ Pois(2dt)`:

* for `r ≤ t`, the steps `n < 8dt` contribute at most `2 e^{-r²/(16dt)}` and the steps `n ≥ 8dt` at
  most `2^{-8dt} E[2^{Pois(2dt)}] = 2^{-8dt} e^{2dt} ≤ e^{-r²/(16dt)}`;
* for `t ≤ r`, the steps `n < 4dr` contribute at most `2 e^{-r/(8d)}` and the others at most
  `2^{-4dr} e^{2dt} ≤ e^{-r/(8d)}`;
* for `r ≥ 2dt`, `Qⁿ(x, y) = 0` for `n < r` (finite propagation speed), and the Poisson tail
  `P[Pois(2dt) ≥ r] ≤ θ^{-r} E[θ^{Pois(2dt)}] = θ^{-r} e^{2dt(θ - 1)}`, `θ = r/(2dt)`, is at most
  `exp(-r (ln(r/t) - ln(2d) - 1))`.

`carneVaropoulosTwo_of_carneVaropoulos` recovers the planar statement `CarneVaropoulosTwo`.
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- **Dario–Gu, Proposition 2.15** (Carne–Varopoulos bound, Davies 1993, Corollaries 11 and 12)
for unit conductances on an infinite open component of `ℤ^d`, with the Euclidean distance. -/
def CarneVaropoulos (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (K : OpenComponent ω), K.supp.Infinite →
    ∀ x ∈ K.supp, ∀ y ∈ K.supp, ∀ t : ℝ, 0 < t →
      (WeakPoincare.latticeDist x y ≤ t →
        bondHeat ω t x y ≤ C * Real.exp (-(WeakPoincare.latticeDist x y ^ 2 / (C * t)))) ∧
      (t ≤ WeakPoincare.latticeDist x y →
        bondHeat ω t x y ≤
          C * Real.exp (-(WeakPoincare.latticeDist x y / C *
            (1 + Real.log (WeakPoincare.latticeDist x y / t)))))

/-- The planar Carne–Varopoulos bound is the case `d = 2`. -/
theorem carneVaropoulosTwo_of_carneVaropoulos (h : CarneVaropoulos 2) : CarneVaropoulosTwo := h

/-- Along a walk of the open graph, the `ℓ¹` displacement is at most the length. -/
theorem sum_abs_sub_le_length_bond {ω : Configuration d} :
    ∀ {a b : Vertex d} (q : (openGraph ω).Walk a b), ∑ i, |b i - a i| ≤ q.length := by
  intro a b q
  induction q with
  | nil => simp
  | cons hadj q ih =>
      rename_i u v w
      have h1 : latticeL1Dist u v = 1 := lattice_adj_iff_l1Dist.mp (openGraph_le ω hadj)
      have h2 : ∑ i, |w i - u i| ≤ ∑ i, (|w i - v i| + |v i - u i|) :=
        Finset.sum_le_sum fun i _ => abs_sub_le _ _ _
      have h3 : ∑ i, |v i - u i| = 1 := by
        rw [← h1, latticeL1Dist]
        exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
      rw [Finset.sum_add_distrib, h3] at h2
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- The Euclidean distance of two vertices joined by a walk of the open graph is at most the
length of the walk. -/
theorem latticeDist_le_length {ω : Configuration d} {x y : Vertex d}
    (q : (openGraph ω).Walk x y) : WeakPoincare.latticeDist x y ≤ q.length := by
  have h := sum_abs_sub_le_length_bond q
  have hR : ∑ i, |((y i - x i : ℤ) : ℝ)| ≤ q.length := by
    have h' : ((∑ i, |y i - x i| : ℤ) : ℝ) ≤ ((q.length : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h' ⊢
    exact h'
  refine (WeakPoincare.latticeDist_le_sum_abs x y).trans (le_of_eq_of_le ?_ hR)
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  exact abs_sub_comm _ _

/-- Distinct lattice points are at Euclidean distance at least one. -/
theorem one_le_latticeDist {x y : Vertex d} (hxy : x ≠ y) : 1 ≤ WeakPoincare.latticeDist x y := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.1 hxy
  have h1 : (1 : ℝ) ≤ |(x i : ℝ) - y i| := by
    have : (1 : ℤ) ≤ |x i - y i| := Int.one_le_abs (sub_ne_zero.2 hi)
    exact_mod_cast this
  exact h1.trans (WeakPoincare.abs_sub_le_latticeDist x y i)

variable [NeZero d]

/-- If `Qⁿ(x, y) ≤ A + B θⁿ` for every `n`, then `p(t, x, y) ≤ A + B e^{2dt(θ - 1)}`. -/
theorem bondHeat_le_of_lazyPow_le (ω : Configuration d) {x y : Vertex d} {t A B θ : ℝ}
    (ht : 0 ≤ t) (h : ∀ n, lazyPow (openGraph ω) (2 * d) n x y ≤ A + B * θ ^ n) :
    bondHeat ω t x y ≤ A + B * Real.exp (2 * d * t * (θ - 1)) := by
  have hsum : HasSum (fun n => poissonWeight (2 * d) t n * (A + B * θ ^ n))
      (A + B * Real.exp (2 * d * t * (θ - 1))) := by
    have := ((hasSum_poissonWeight (D := 2 * d) t).mul_left A).add
      ((hasSum_poissonWeight_mul_real_pow (2 * d) t θ).mul_left B)
    have hf : (fun n => poissonWeight (2 * d) t n * (A + B * θ ^ n)) =
        fun n => A * poissonWeight (2 * d) t n + B * (poissonWeight (2 * d) t n * θ ^ n) := by
      funext n
      ring
    have hv : A * 1 + B * Real.exp (((2 * d : ℕ) : ℝ) * t * (θ - 1)) =
        A + B * Real.exp (2 * d * t * (θ - 1)) := by
      push_cast
      ring
    rw [hf, ← hv]
    exact this
  rw [bondHeat, vsrwHeat, ← hsum.tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_bondHeat ω t x y) hsum.summable
  exact mul_le_mul_of_nonneg_left (h n) (poissonWeight_nonneg ht n)

omit [NeZero d] in
/-- Finite propagation speed: `Qⁿ(x, y) = 0` for `n < |x - y|`. -/
theorem lazyPow_eq_zero_of_lt_latticeDist (ω : Configuration d) {x y : Vertex d} {n : ℕ}
    (hn : (n : ℝ) < WeakPoincare.latticeDist x y) : lazyPow (openGraph ω) (2 * d) n x y = 0 := by
  by_contra hne
  obtain ⟨q, hq⟩ := exists_walk_of_lazyPow_ne_zero n x y hne
  have h1 := latticeDist_le_length q
  have h2 : (q.length : ℝ) ≤ n := by exact_mod_cast hq
  linarith

/-- The Carne–Varopoulos bound of the lazy walk with the Euclidean distance:
`Qⁿ(x, y) ≤ 2 e^{-|x - y|²/(2n)}` for `n ≥ 1`. -/
theorem lazyPow_le_two_mul_exp_bond (ω : Configuration d) (x y : Vertex d) {n : ℕ} (hn : 1 ≤ n) :
    lazyPow (openGraph ω) (2 * d) n x y ≤
      2 * Real.exp (-(WeakPoincare.latticeDist x y ^ 2 / (2 * n))) := by
  have hdeg := openGraph_degree_le_two_mul ω
  by_cases hreach : (openGraph ω).Reachable x y
  · obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    have hd : WeakPoincare.latticeDist x y ≤ (openGraph ω).dist x y := by
      have := latticeDist_le_length q
      rwa [hq] at this
    have hcv := lazyPow_le_carneVaropoulos two_mul_dim_pos hdeg x y n hn
    refine hcv.trans ?_
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    gcongr
    rw [neg_div]
    apply neg_le_neg
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (WeakPoincare.latticeDist_nonneg _ _) hd 2
  · have h0 : lazyPow (openGraph ω) (2 * d) n x y = 0 := by
      by_contra hne
      obtain ⟨q, -⟩ := exists_walk_of_lazyPow_ne_zero n x y hne
      exact hreach ⟨q⟩
    rw [h0]
    positivity

/-- `1 ≤ d` as a real number. -/
theorem one_le_dim_real : (1 : ℝ) ≤ d := by
  have := NeZero.pos d
  exact_mod_cast this

/-- The bound `2^{-N} e^{2dt} ≤ e^{-a}` when `N ≥ 4 d T`, `t ≤ T` and `a ≤ d T / 2`. -/
theorem two_inv_pow_mul_exp_le {N : ℕ} {t T a : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hN : 4 * d * T ≤ N) (ha : a ≤ d * T / 2) :
    (2 : ℝ)⁻¹ ^ N * Real.exp (2 * d * t * (2 - 1)) ≤ Real.exp (-a) := by
  have h2 : (2 : ℝ)⁻¹ ^ N = Real.exp (-(N * Real.log 2)) := by
    rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), inv_pow]
  rw [h2, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl2 := Real.log_two_gt_d9
  have hd1 := one_le_dim_real (d := d)
  have hT : 0 ≤ T := ht.trans htT
  have h4 : 4 * d * T * Real.log 2 ≤ N * Real.log 2 :=
    mul_le_mul_of_nonneg_right hN (Real.log_nonneg (by norm_num))
  have h5 : (d : ℝ) * t ≤ d * T := mul_le_mul_of_nonneg_left htT (by positivity)
  have h6 : 0 ≤ (d : ℝ) * T := by positivity
  nlinarith

/-- **Gaussian regime**: `p(t, x, y) ≤ 3 e^{-r²/(16dt)}` for `r = |x - y| ≤ t`. -/
theorem bondHeat_le_of_latticeDist_le (ω : Configuration d) {x y : Vertex d} {t : ℝ} (ht : 0 < t)
    (hr : WeakPoincare.latticeDist x y ≤ t) :
    bondHeat ω t x y ≤ 3 * Real.exp (-(WeakPoincare.latticeDist x y ^ 2 / (16 * d * t))) := by
  set r := WeakPoincare.latticeDist x y with hrdef
  have hr0 : 0 ≤ r := WeakPoincare.latticeDist_nonneg _ _
  have hd1 := one_le_dim_real (d := d)
  have hdeg := openGraph_degree_le_two_mul ω
  set N : ℕ := ⌈8 * d * t⌉₊ with hN
  have hN1 : 8 * d * t ≤ N := Nat.le_ceil _
  have hpt : ∀ n : ℕ, lazyPow (openGraph ω) (2 * d) n x y ≤
      2 * Real.exp (-(r ^ 2 / (16 * d * t))) + (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
    intro n
    have h01 := lazyPow_mem_Icc two_mul_dim_pos hdeg n x y
    have hE : 0 ≤ (2 : ℝ)⁻¹ ^ N * 2 ^ n := by positivity
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [lazyPow_zero]
      split_ifs with hxy
      · subst hxy
        have : r = 0 := by rw [hrdef, WeakPoincare.latticeDist_self]
        rw [this]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
          Real.exp_zero, mul_one]
        linarith
      · positivity
    by_cases hnN : n < N
    · have hnt : (n : ℝ) ≤ 8 * d * t := (Nat.lt_ceil.1 hnN).le
      have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
      have h1 := lazyPow_le_two_mul_exp_bond ω x y hnpos
      have h2 : Real.exp (-(r ^ 2 / (2 * n))) ≤ Real.exp (-(r ^ 2 / (16 * d * t))) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        linarith
      linarith
    · have hpow : 1 ≤ (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
        rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
        exact pow_le_pow_right₀ (by norm_num) (not_lt.1 hnN)
      have : 0 ≤ 2 * Real.exp (-(r ^ 2 / (16 * d * t))) := by positivity
      linarith [h01.2]
  have hle := bondHeat_le_of_lazyPow_le ω ht.le hpt
  have htail : (2 : ℝ)⁻¹ ^ N * Real.exp (2 * d * t * (2 - 1)) ≤
      Real.exp (-(r ^ 2 / (16 * d * t))) := by
    have hdt : 0 ≤ (d : ℝ) * t := by positivity
    refine two_inv_pow_mul_exp_le ht.le le_rfl (by nlinarith [hN1]) ?_
    rw [div_le_iff₀ (by positivity)]
    have : r ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hr0 hr 2
    have hdd : (1 : ℝ) ≤ d * d := by nlinarith
    have h3 : t ^ 2 ≤ 8 * d * t * (d * t) := by
      nlinarith [mul_le_mul_of_nonneg_right hdd (sq_nonneg t)]
    nlinarith
  linarith

/-- **Intermediate regime**: `p(t, x, y) ≤ 3 e^{-r/(8d)}` for `t ≤ r = |x - y|`. -/
theorem bondHeat_le_exp_of_le_latticeDist (ω : Configuration d) {x y : Vertex d} {t : ℝ}
    (ht : 0 < t) (htr : t ≤ WeakPoincare.latticeDist x y) :
    bondHeat ω t x y ≤ 3 * Real.exp (-(WeakPoincare.latticeDist x y / (8 * d))) := by
  set r := WeakPoincare.latticeDist x y with hrdef
  have hr0 : 0 < r := lt_of_lt_of_le ht htr
  have hd1 := one_le_dim_real (d := d)
  have hdeg := openGraph_degree_le_two_mul ω
  have hxy : x ≠ y := by
    intro h
    rw [hrdef, h, WeakPoincare.latticeDist_self] at hr0
    exact lt_irrefl 0 hr0
  set N : ℕ := ⌈4 * d * r⌉₊ with hN
  have hN1 : 4 * d * r ≤ N := Nat.le_ceil _
  have hpt : ∀ n : ℕ, lazyPow (openGraph ω) (2 * d) n x y ≤
      2 * Real.exp (-(r / (8 * d))) + (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
    intro n
    have h01 := lazyPow_mem_Icc two_mul_dim_pos hdeg n x y
    have hE : 0 ≤ (2 : ℝ)⁻¹ ^ N * 2 ^ n := by positivity
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [lazyPow_zero, if_neg hxy]
      positivity
    by_cases hnN : n < N
    · have hnt : (n : ℝ) ≤ 4 * d * r := (Nat.lt_ceil.1 hnN).le
      have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
      have h1 := lazyPow_le_two_mul_exp_bond ω x y hnpos
      have h2 : Real.exp (-(r ^ 2 / (2 * n))) ≤ Real.exp (-(r / (8 * d))) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · have hpow : 1 ≤ (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
        rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
        exact pow_le_pow_right₀ (by norm_num) (not_lt.1 hnN)
      have : 0 ≤ 2 * Real.exp (-(r / (8 * d))) := by positivity
      linarith [h01.2]
  have hle := bondHeat_le_of_lazyPow_le ω ht.le hpt
  have htail : (2 : ℝ)⁻¹ ^ N * Real.exp (2 * d * t * (2 - 1)) ≤ Real.exp (-(r / (8 * d))) := by
    refine two_inv_pow_mul_exp_le ht.le htr hN1 ?_
    rw [div_le_iff₀ (by positivity)]
    have hdd : (1 : ℝ) ≤ d * d := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hdd hr0.le]
  linarith

/-- **Far regime**: `p(t, x, y) ≤ exp(-r (ln(r/t) - ln(2d) - 1))` for `r = |x - y| ≥ 2dt`. -/
theorem bondHeat_le_of_two_mul_le_latticeDist (ω : Configuration d) {x y : Vertex d} {t : ℝ}
    (ht : 0 < t) (hr : 2 * d * t ≤ WeakPoincare.latticeDist x y) :
    bondHeat ω t x y ≤
      Real.exp (-(WeakPoincare.latticeDist x y *
        (Real.log (WeakPoincare.latticeDist x y / t) - Real.log (2 * d) - 1))) := by
  set r := WeakPoincare.latticeDist x y with hrdef
  have hd1 := one_le_dim_real (d := d)
  have hdt : 0 < 2 * d * t := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le hdt hr
  set θ := r / (2 * d * t) with hθ
  have hθ1 : 1 ≤ θ := by rw [hθ, le_div_iff₀ hdt]; linarith
  have hθ0 : 0 < θ := by linarith
  set m : ℕ := ⌈r⌉₊ with hm
  have hmr : r ≤ m := Nat.le_ceil _
  have hdeg := openGraph_degree_le_two_mul ω
  have hpt : ∀ n : ℕ, lazyPow (openGraph ω) (2 * d) n x y ≤ 0 + (θ ^ m)⁻¹ * θ ^ n := by
    intro n
    have h01 := lazyPow_mem_Icc two_mul_dim_pos hdeg n x y
    by_cases hnm : n < m
    · rw [lazyPow_eq_zero_of_lt_latticeDist ω (Nat.lt_ceil.1 hnm)]
      positivity
    · have : 1 ≤ (θ ^ m)⁻¹ * θ ^ n := by
        rw [inv_mul_eq_div, one_le_div (by positivity)]
        exact pow_le_pow_right₀ hθ1 (not_lt.1 hnm)
      linarith [h01.2]
  have hle := bondHeat_le_of_lazyPow_le ω ht.le hpt
  rw [zero_add] at hle
  refine hle.trans ?_
  have hlogθ : Real.log θ = Real.log (r / t) - Real.log (2 * d) := by
    rw [hθ, show r / (2 * d * t) = (r / t) / (2 * d) by field_simp, Real.log_div (by positivity)
      (by positivity)]
  have hl0 : 0 ≤ Real.log θ := Real.log_nonneg hθ1
  have hpow : (θ ^ m)⁻¹ ≤ Real.exp (-(r * Real.log θ)) := by
    rw [Real.exp_neg, inv_le_inv₀ (by positivity) (Real.exp_pos _), ← Real.rpow_natCast,
      Real.rpow_def_of_pos hθ0]
    apply Real.exp_le_exp.2
    nlinarith
  have hexp : Real.exp (2 * d * t * (θ - 1)) ≤ Real.exp r := by
    apply Real.exp_le_exp.2
    have : 2 * d * t * θ = r := by rw [hθ]; field_simp
    nlinarith
  calc (θ ^ m)⁻¹ * Real.exp (2 * d * t * (θ - 1)) ≤ Real.exp (-(r * Real.log θ)) * Real.exp r :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(r * (Real.log (r / t) - Real.log (2 * d) - 1))) := by
        rw [← Real.exp_add, hlogθ]
        ring_nf

/-- **Dario–Gu, Proposition 2.15** (Carne–Varopoulos bound) on `ℤ^d`, with `C = 100 d²`. -/
theorem carneVaropoulos_holds : CarneVaropoulos d := by
  have hd1 := one_le_dim_real (d := d)
  have hdd : (1 : ℝ) ≤ d ^ 2 := by nlinarith
  have hC1 : 16 * (d : ℝ) ≤ 100 * d ^ 2 := by nlinarith
  refine ⟨100 * d ^ 2, by positivity, fun ω K _ x _ y _ t ht => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · have h := bondHeat_le_of_latticeDist_le ω ht hr
    refine h.trans ?_
    have h1 : Real.exp (-(WeakPoincare.latticeDist x y ^ 2 / (16 * d * t))) ≤
        Real.exp (-(WeakPoincare.latticeDist x y ^ 2 / (100 * d ^ 2 * t))) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      nlinarith
    have hE := Real.exp_pos (-(WeakPoincare.latticeDist x y ^ 2 / (100 * d ^ 2 * t)))
    calc 3 * Real.exp (-(WeakPoincare.latticeDist x y ^ 2 / (16 * d * t)))
        ≤ 3 * Real.exp (-(WeakPoincare.latticeDist x y ^ 2 / (100 * d ^ 2 * t))) := by gcongr
      _ ≤ 100 * d ^ 2 * Real.exp (-(WeakPoincare.latticeDist x y ^ 2 / (100 * d ^ 2 * t))) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hE.le
  · set r := WeakPoincare.latticeDist x y with hrdef
    set L := Real.log (r / t) with hLdef
    have hr0 : 0 < r := lt_of_lt_of_le ht hr
    have hrt : 1 ≤ r / t := by rw [le_div_iff₀ ht]; linarith
    have hL0 : 0 ≤ L := Real.log_nonneg hrt
    have hld : Real.log (2 * d) ≤ 2 * d - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hld0 : 0 ≤ Real.log (2 * d) := Real.log_nonneg (by linarith)
    have hE := Real.exp_pos (-(r / (100 * d ^ 2) * (1 + L)))
    rcases le_or_gt L (2 * Real.log (2 * d) + 3) with hnear | hfar
    · have h := bondHeat_le_exp_of_le_latticeDist ω ht hr
      refine h.trans ?_
      have h0 : Real.exp (-(r / (8 * d))) ≤ Real.exp (-(r / (100 * d ^ 2) * (1 + L))) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        have h1 : 1 + L ≤ 8 * d := by linarith
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : r * (1 + L) * (8 * d) ≤ r * (8 * d) * (8 * d) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hr0.le) (by positivity)
        have h3 : r * (8 * d) * (8 * d) ≤ r * (100 * d ^ 2) := by nlinarith
        linarith
      calc 3 * Real.exp (-(r / (8 * d))) ≤ 3 * Real.exp (-(r / (100 * d ^ 2) * (1 + L))) := by
            gcongr
        _ ≤ 100 * d ^ 2 * Real.exp (-(r / (100 * d ^ 2) * (1 + L))) :=
            mul_le_mul_of_nonneg_right (by nlinarith) hE.le
    · have h2d : 2 * d * t ≤ r := by
        have h1 : Real.log (2 * d) ≤ L := by linarith
        have h2 : 2 * (d : ℝ) ≤ r / t := (Real.log_le_log_iff (by positivity) (by positivity)).1 h1
        rw [le_div_iff₀ ht] at h2
        linarith
      have h := bondHeat_le_of_two_mul_le_latticeDist ω ht h2d
      refine h.trans ?_
      have h0 : Real.exp (-(r * (L - Real.log (2 * d) - 1))) ≤
          Real.exp (-(r / (100 * d ^ 2) * (1 + L))) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        have hA : 0 ≤ L - Real.log (2 * d) - 1 - (1 + L) / 2 := by linarith
        have h1 : 1 + L ≤ (L - Real.log (2 * d) - 1) * (100 * d ^ 2) := by
          nlinarith [mul_nonneg hA (by nlinarith : (0 : ℝ) ≤ 100 * d ^ 2 - 2),
            mul_nonneg (by linarith : (0 : ℝ) ≤ d ^ 2 - 1) (by linarith : (0 : ℝ) ≤ 1 + L)]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        calc r * (1 + L) ≤ r * ((L - Real.log (2 * d) - 1) * (100 * d ^ 2)) :=
              mul_le_mul_of_nonneg_left h1 hr0.le
          _ = r * (L - Real.log (2 * d) - 1) * (100 * d ^ 2) := by ring
      calc Real.exp (-(r * (L - Real.log (2 * d) - 1)))
          ≤ Real.exp (-(r / (100 * d ^ 2) * (1 + L))) := h0
        _ ≤ 100 * d ^ 2 * Real.exp (-(r / (100 * d ^ 2) * (1 + L))) :=
            le_mul_of_one_le_left hE.le (by nlinarith)

/-- The small-time bound `p(t, x, y) ≤ C e^{-|x - y|/C}` for `0 < t ≤ |x - y|` on infinite
components of `ℤ^d`: the `d`-dimensional form of `HeatSmallTimeTwo`. -/
def HeatSmallTimeD (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (K : OpenComponent ω), K.supp.Infinite →
    ∀ x ∈ K.supp, ∀ y ∈ K.supp, ∀ t : ℝ, 0 < t → t ≤ WeakPoincare.latticeDist x y →
      bondHeat ω t x y ≤ C * Real.exp (-(WeakPoincare.latticeDist x y / C))

/-- The planar small-time bound is the case `d = 2`. -/
theorem heatSmallTimeTwo_of_heatSmallTimeD (h : HeatSmallTimeD 2) : HeatSmallTimeTwo := h

/-- The small-time bound on `ℤ^d`, with `C = 8d`. -/
theorem heatSmallTimeD_holds : HeatSmallTimeD d := by
  have hd1 := one_le_dim_real (d := d)
  refine ⟨8 * d, by positivity, fun ω K _ x _ y _ t ht htx => ?_⟩
  refine (bondHeat_le_exp_of_le_latticeDist ω ht htx).trans ?_
  have he := Real.exp_pos (-(WeakPoincare.latticeDist x y / (8 * d)))
  exact mul_le_mul_of_nonneg_right (by linarith) he.le

end Rigidity.Green

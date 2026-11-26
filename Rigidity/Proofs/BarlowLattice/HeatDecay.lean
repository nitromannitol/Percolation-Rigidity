import Rigidity.Proofs.BarlowLattice.OnDiagonal
import Rigidity.Proofs.Barlow.HeatDecay
import Rigidity.Proofs.Green.LazyCarneVaropoulos
import Rigidity.Proofs.Green.BondCarneVaropoulos
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Decay of the heat kernel on `ℤ^d` and the functionals of Nash

For the heat kernel `p_t(x, ·)` of the variable speed random walk on the open graph of a
configuration of `ℤ^d`, this file proves the bounds that make the functionals of Nash (used by
Barlow, *Random walks on supercritical percolation clusters*, Ann. Probab. 32 (2004), §3)

  `M(t) = Σ_y |y - x| p_t(x, y)`,   `Q(t) = -Σ_y p_t(x, y) log p_t(x, y)`

differentiable, with the derivatives of the source, (3.8) and (3.10):

  `M'(t) = -½ Σ_{(a, b)} (|b - x| - |a - x|)(p_t(x, b) - p_t(x, a))`,
  `Q'(t) = ½ Σ_{(a, b)} (log p_t(x, b) - log p_t(x, a))(p_t(x, b) - p_t(x, a))`,

the sums running over the directed open edges. The source justifies the use of the Gauss–Green
formula by the decay (1.5) of `p_t(x, ·)`; here the decay is
`p_t(x, y) ≤ e^{126 d t} 64^{-k}`, `k = d(x, y)` the graph distance (`bondHeat_le_exp_mul_pow_dist`),
together with the lower bound `p_t(x, y) ≥ e^{-2dt} t^k / k!` on the component of `x`
(`poissonWeight_mul_le_bondHeat`), which controls `log p_t(x, y)`.
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green Rigidity.WeakPoincare

namespace Rigidity.BarlowLattice

variable {d : ℕ}

variable [NeZero d] {ω : Configuration d}

/-! ### The `ℓ¹` distance and geometric lattice sums -/

/-- The `ℓ¹` distance of two lattice points. -/
def l1Dist (x y : Vertex d) : ℕ := ∑ i, (y i - x i).natAbs

omit [NeZero d] in
/-- `Σ_{y ∈ ℤⁿ} q^{|y|₁} = S^n` with `S = Σ_{a ∈ ℤ} q^{|a|}`. -/
theorem hasSum_pow_sum_natAbs {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∀ n : ℕ, HasSum (fun y : Fin n → ℤ => q ^ ∑ i, (y i).natAbs)
      (((1 - q)⁻¹ + q * (1 - q)⁻¹) ^ n) := by
  have hz := Barlow.hasSum_pow_natAbs hq0 hq1
  intro n
  induction n with
  | zero =>
    convert hasSum_fintype (fun y : Fin 0 → ℤ => q ^ ∑ i, (y i).natAbs) using 1
    simp
  | succ n ih =>
    set S := (1 - q)⁻¹ + q * (1 - q)⁻¹ with hS
    set g : ℤ → ℝ := fun a => q ^ a.natAbs with hg
    set G : (Fin n → ℤ) → ℝ := fun y => q ^ ∑ i, (y i).natAbs with hG
    have hs : Summable fun p : ℤ × (Fin n → ℤ) => g p.1 * G p.2 :=
      Summable.mul_of_nonneg (f := g) (g := G) hz.summable ih.summable
        (fun a => pow_nonneg hq0 _) (fun a => pow_nonneg hq0 _)
    have hprod : HasSum (fun p : ℤ × (Fin n → ℤ) => g p.1 * G p.2) (S * S ^ n) :=
      HasSum.mul (f := g) (g := G) hz ih hs
    have e : (fun p : ℤ × (Fin n → ℤ) => g p.1 * G p.2) =
        (fun y : Fin (n + 1) → ℤ => q ^ ∑ i, (y i).natAbs) ∘ Fin.consEquiv (fun _ => ℤ) := by
      funext p
      simp only [Function.comp_apply, Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ, pow_add, hg, hG]
    rw [e] at hprod
    rw [pow_succ']
    exact (Fin.consEquiv (fun _ => ℤ)).hasSum_iff.1 hprod

omit [NeZero d] in
/-- `Σ_y q^{|y - x|₁} = ((1 - q)⁻¹ + q (1 - q)⁻¹)^d`. -/
theorem hasSum_pow_l1Dist (x : Vertex d) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun y => q ^ l1Dist x y) (((1 - q)⁻¹ + q * (1 - q)⁻¹) ^ d) := by
  have h := (Equiv.subRight x).hasSum_iff.2 (hasSum_pow_sum_natAbs hq0 hq1 d)
  have e : (fun y => q ^ l1Dist x y) =
      (fun y : Fin d → ℤ => q ^ ∑ i, (y i).natAbs) ∘ Equiv.subRight x := by
    funext y
    rfl
  rw [e]
  exact h

omit [NeZero d] in
theorem summable_pow_l1Dist (x : Vertex d) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun y => q ^ l1Dist x y :=
  (hasSum_pow_l1Dist x hq0 hq1).summable

omit [NeZero d] in
theorem l1Dist_le_dist {x y : Vertex d} (h : (openGraph ω).Reachable x y) :
    l1Dist x y ≤ (openGraph ω).dist x y := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist
  have h1 := sum_abs_sub_le_length_bond q
  rw [hq] at h1
  have h2 : ((l1Dist x y : ℕ) : ℤ) = ∑ i, |y i - x i| := by
    simp [l1Dist]
  omega

omit [NeZero d] in
theorem latticeDist_le_dist {x y : Vertex d} (h : (openGraph ω).Reachable x y) :
    latticeDist x y ≤ (openGraph ω).dist x y := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist
  have h1 := latticeDist_le_length q
  rw [hq] at h1
  exact h1

omit [NeZero d] in
/-- `(1 + k)² 64^{-k} ≤ 4 · 16^{-|y - x|₁}` on the component of `x`, `k = d(x, y)`. -/
theorem one_add_sq_mul_pow_dist_le {x y : Vertex d} (h : (openGraph ω).Reachable x y) :
    (1 + ((openGraph ω).dist x y : ℝ)) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y ≤
      4 * (1 / 16 : ℝ) ^ l1Dist x y := by
  refine (Barlow.one_add_sq_mul_pow_le _).trans ?_
  have := l1Dist_le_dist h
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) this)
    (by norm_num)

/-! ### Upper and lower bounds on the heat kernel -/

omit [NeZero d] in
theorem lazyPow_eq_zero_of_lt_dist {x y : Vertex d} {n : ℕ} (hn : n < (openGraph ω).dist x y) :
    lazyPow (openGraph ω) (2 * d) n x y = 0 := by
  by_contra h
  obtain ⟨q, hq⟩ := exists_walk_of_lazyPow_ne_zero n x y h
  have := SimpleGraph.dist_le q
  omega

/-- `p_t(x, y) ≤ e^{126 d t} 64^{-d(x, y)}` for `t ≥ 0`. -/
theorem bondHeat_le_exp_mul_pow_dist {t : ℝ} (ht : 0 ≤ t) (x y : Vertex d) :
    bondHeat ω t x y ≤ Real.exp (126 * d * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
  set j := (openGraph ω).dist x y with hj
  have h := bondHeat_le_of_lazyPow_le ω (A := 0) (B := (1 / 64 : ℝ) ^ j) (θ := 64) ht (fun n => by
    by_cases hn : n < j
    · rw [lazyPow_eq_zero_of_lt_dist hn]
      positivity
    · have hjn : j ≤ n := le_of_not_gt hn
      have h1 := (lazyPow_mem_Icc two_mul_dim_pos (openGraph_degree_le_two_mul ω) n x y).2
      refine h1.trans ?_
      rw [zero_add, one_div, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_right₀ (by norm_num) hjn)
  calc bondHeat ω t x y ≤ 0 + (1 / 64 : ℝ) ^ j * Real.exp (2 * d * t * (64 - 1)) := h
    _ = Real.exp (126 * d * t) * (1 / 64 : ℝ) ^ j := by ring_nf

theorem pow_le_lazyPow_of_walk {x y : Vertex d} (q : (openGraph ω).Walk x y) :
    (1 / (2 * d) : ℝ) ^ q.length ≤ lazyPow (openGraph ω) (2 * d) q.length x y := by
  induction q with
  | nil => simp [lazyPow_zero]
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.length_cons, lazyPow_succ]
    have hdeg := openGraph_degree_le_two_mul ω
    have ha : 0 ≤ 1 - ((openGraph ω).degree u : ℝ) / ((2 * d : ℕ) : ℝ) := by
      rw [sub_nonneg, div_le_one (by exact_mod_cast two_mul_dim_pos)]
      exact_mod_cast hdeg u
    have h0 := (lazyPow_mem_Icc two_mul_dim_pos hdeg p.length u w).1
    have hv : v ∈ (openGraph ω).neighborFinset u := ((openGraph ω).mem_neighborFinset u v).2 h
    have hsingle : lazyPow (openGraph ω) (2 * d) p.length v w ≤
        ∑ z ∈ (openGraph ω).neighborFinset u, lazyPow (openGraph ω) (2 * d) p.length z w :=
      Finset.single_le_sum (fun z _ => (lazyPow_mem_Icc two_mul_dim_pos hdeg p.length z w).1) hv
    have h4 : (1 / ((2 * d : ℕ) : ℝ)) = 1 / (2 * d) := by push_cast; ring
    rw [h4, pow_succ]
    have hc : (0 : ℝ) ≤ 1 / (2 * d) := by positivity
    nlinarith [mul_nonneg ha h0, mul_le_mul_of_nonneg_left ih hc,
      mul_le_mul_of_nonneg_left hsingle hc]

/-- On the component of `x`: `e^{-2dt} (2dt)^k / k! · (2d)^{-k} ≤ p_t(x, y)`, `k = d(x, y)`. -/
theorem poissonWeight_mul_le_bondHeat {t : ℝ} (ht : 0 ≤ t) {x y : Vertex d}
    (h : (openGraph ω).Reachable x y) :
    poissonWeight (2 * d) t ((openGraph ω).dist x y) * (1 / (2 * d) : ℝ) ^ (openGraph ω).dist x y ≤
      bondHeat ω t x y := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist
  have h1 := pow_le_lazyPow_of_walk q
  rw [hq] at h1
  have hs := summable_bondHeat ω t x y
  calc poissonWeight (2 * d) t ((openGraph ω).dist x y) * (1 / (2 * d) : ℝ) ^ (openGraph ω).dist x y
      ≤ poissonWeight (2 * d) t ((openGraph ω).dist x y) *
          lazyPow (openGraph ω) (2 * d) ((openGraph ω).dist x y) x y :=
        mul_le_mul_of_nonneg_left h1 (poissonWeight_nonneg ht _)
    _ ≤ bondHeat ω t x y := hs.le_tsum _ (fun n _ => mul_nonneg (poissonWeight_nonneg ht n)
        (lazyPow_mem_Icc two_mul_dim_pos (openGraph_degree_le_two_mul ω) n x y).1)

theorem bondHeat_pos {t : ℝ} (ht : 0 < t) {x y : Vertex d} (h : (openGraph ω).Reachable x y) :
    0 < bondHeat ω t x y := by
  refine lt_of_lt_of_le ?_ (poissonWeight_mul_le_bondHeat ht.le h)
  have hD : (0 : ℝ) < ((2 * d : ℕ) : ℝ) := by exact_mod_cast two_mul_dim_pos
  have hd : (0 : ℝ) < 1 / (2 * d) := by
    have : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
    positivity
  unfold poissonWeight
  exact mul_pos (div_pos (mul_pos (Real.exp_pos _) (pow_pos (mul_pos hD ht) _))
    (by exact_mod_cast Nat.factorial_pos _)) (pow_pos hd _)

/-- On the component of `x`, for `0 < a ≤ t ≤ b`:
`|log p_t(x, y)| ≤ 4b + d |log a| + d²`, `d = d(x, y)`. -/
theorem abs_log_bondHeat_le {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) {x y : Vertex d}
    (h : (openGraph ω).Reachable x y) :
    |Real.log (bondHeat ω t x y)| ≤
      2 * d * b + (openGraph ω).dist x y * |Real.log a| + ((openGraph ω).dist x y : ℝ) ^ 2 := by
  set k := (openGraph ω).dist x y with hk
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hpos := bondHeat_pos ht h
  have hle1 := bondHeat_le_one ω ht.le x y
  have hlow := poissonWeight_mul_le_bondHeat ht.le h
  rw [← hk] at hlow
  -- `exp(-4b - k|log a| - k²) ≤ e^{-4t} t^k / k!`
  have hfact : (k.factorial : ℝ) ≤ Real.exp ((k : ℝ) ^ 2) := by
    have h1 : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    have h2 : (k : ℝ) ^ k ≤ Real.exp (k : ℝ) ^ k := by
      have : (k : ℝ) ≤ Real.exp k := by linarith [Real.add_one_le_exp (k : ℝ)]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) this k
    calc (k.factorial : ℝ) ≤ Real.exp (k : ℝ) ^ k := h1.trans h2
      _ = Real.exp ((k : ℝ) ^ 2) := by rw [← Real.exp_nat_mul, sq]
  have hal : Real.exp (-|Real.log a|) ≤ t := by
    calc Real.exp (-|Real.log a|) ≤ Real.exp (Real.log a) :=
          Real.exp_le_exp.2 (neg_abs_le _)
      _ = a := Real.exp_log ha
      _ ≤ t := hat
  have he : Real.exp (-(2 * d) * b) * Real.exp (-|Real.log a|) ^ k * (Real.exp ((k : ℝ) ^ 2))⁻¹ =
      Real.exp (-(2 * d * b + k * |Real.log a| + (k : ℝ) ^ 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hp : poissonWeight (2 * d) t k * (1 / (2 * d) : ℝ) ^ k =
      Real.exp (-(2 * d) * t) * t ^ k * ((k.factorial : ℝ))⁻¹ := by
    unfold poissonWeight
    have hd0 : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
    have h4 : ((2 * d : ℕ) : ℝ) = 2 * d := by push_cast; ring
    have h44 : (2 * d : ℝ) ^ k * (1 / (2 * d) : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      field_simp
      simp
    rw [h4, mul_pow, div_eq_mul_inv]
    calc Real.exp (-(2 * d) * t) * ((2 * d) ^ k * t ^ k) * ((k.factorial : ℝ))⁻¹ *
          (1 / (2 * d) : ℝ) ^ k
        = Real.exp (-(2 * d) * t) * t ^ k * ((k.factorial : ℝ))⁻¹ *
            ((2 * d : ℝ) ^ k * (1 / (2 * d) : ℝ) ^ k) := by
          ring
      _ = _ := by rw [h44, mul_one]
  have hk0 : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hexp : Real.exp (-(2 * d * b + k * |Real.log a| + (k : ℝ) ^ 2)) ≤
      poissonWeight (2 * d) t k * (1 / (2 * d) : ℝ) ^ k := by
    rw [← he, hp]
    have f1 : Real.exp (-(2 * d) * b) ≤ Real.exp (-(2 * d) * t) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left htb (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]))
    have f2 : Real.exp (-|Real.log a|) ^ k ≤ t ^ k :=
      pow_le_pow_left₀ (Real.exp_pos _).le hal k
    have f3 : (Real.exp ((k : ℝ) ^ 2))⁻¹ ≤ ((k.factorial : ℝ))⁻¹ := inv_anti₀ hk0 hfact
    exact mul_le_mul (mul_le_mul f1 f2 (pow_nonneg (Real.exp_pos _).le k) (Real.exp_pos _).le) f3
      (inv_nonneg.2 (Real.exp_pos _).le) (by positivity)
  have hlogle : -(2 * d * b + k * |Real.log a| + (k : ℝ) ^ 2) ≤ Real.log (bondHeat ω t x y) := by
    rw [Real.le_log_iff_exp_le hpos]
    exact hexp.trans hlow
  have hlog0 : Real.log (bondHeat ω t x y) ≤ 0 := Real.log_nonpos hpos.le hle1
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg (Real.log a), sq_nonneg (k : ℝ)]

omit [NeZero d] in
theorem bondHeat_eq_zero_of_not_reachable' {x y : Vertex d} (h : ¬ (openGraph ω).Reachable x y)
    (t : ℝ) : bondHeat ω t x y = 0 :=
  bondHeat_eq_zero_of_not_reachable ω h t

/-- A neighbour of a point of the component of `x` carries at most `64 e^{126dt} 64^{-d(x, y)}`. -/
theorem bondHeat_nbr_le {t : ℝ} (ht : 0 ≤ t) {x y z : Vertex d}
    (hxy : (openGraph ω).Reachable x y) (hz : z ∈ (openGraph ω).neighborFinset y) :
    bondHeat ω t x z ≤ 64 * Real.exp (126 * d * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
  have hadj : (openGraph ω).Adj y z := ((openGraph ω).mem_neighborFinset y z).1 hz
  have hxz : (openGraph ω).Reachable x z := hxy.trans hadj.reachable
  have hd : (openGraph ω).dist x y ≤ (openGraph ω).dist x z + 1 := by
    obtain ⟨q, hq⟩ := hxz.exists_walk_length_eq_dist
    have := SimpleGraph.dist_le (q.concat hadj.symm)
    rw [SimpleGraph.Walk.length_concat, hq] at this
    exact this
  refine (bondHeat_le_exp_mul_pow_dist ht x z).trans ?_
  have hp : (1 / 64 : ℝ) ^ (openGraph ω).dist x z ≤ 64 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
    have h1 : (1 / 64 : ℝ) ^ ((openGraph ω).dist x z + 1) ≤ (1 / 64 : ℝ) ^ (openGraph ω).dist x y :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
    rw [pow_succ] at h1
    linarith
  calc Real.exp (126 * d * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x z
      ≤ Real.exp (126 * d * t) * (64 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = _ := by ring

/-- The heat equation in the second variable. -/
theorem hasDerivAt_bondHeat_snd (t : ℝ) (x y : Vertex d) :
    HasDerivAt (fun s => bondHeat ω s x y)
      (openLaplacian ω (fun z => bondHeat ω t x z) y) t := by
  have h := hasDerivAt_bondHeat ω t y x
  have e1 : (fun s => bondHeat ω s y x) = fun s => bondHeat ω s x y :=
    funext fun s => bondHeat_symm ω s y x
  have e2 : (fun z => bondHeat ω t z x) = fun z => bondHeat ω t x z :=
    funext fun z => bondHeat_symm ω t z x
  rw [e1, e2] at h
  exact h

omit [NeZero d] in
theorem openLaplacian_bondHeat_eq_zero {t : ℝ} {x y : Vertex d}
    (h : ¬ (openGraph ω).Reachable x y) : openLaplacian ω (fun z => bondHeat ω t x z) y = 0 := by
  unfold openLaplacian
  refine Finset.sum_eq_zero fun z hz => ?_
  have hadj : (openGraph ω).Adj y z := ((openGraph ω).mem_neighborFinset y z).1 hz
  have hz' : ¬ (openGraph ω).Reachable x z := fun hxz => h (hxz.trans hadj.symm.reachable)
  show bondHeat ω t x z - bondHeat ω t x y = 0
  rw [bondHeat_eq_zero_of_not_reachable' hz', bondHeat_eq_zero_of_not_reachable' h, sub_zero]

/-- `|Δ_y p_t(x, ·)| ≤ 130 d e^{126dt} 64^{-d(x, y)}`. -/
theorem abs_openLaplacian_bondHeat_le {t : ℝ} (ht : 0 ≤ t) (x y : Vertex d) :
    |openLaplacian ω (fun z => bondHeat ω t x z) y| ≤
      130 * d * Real.exp (126 * d * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
  by_cases h : (openGraph ω).Reachable x y
  · unfold openLaplacian
    have hy := bondHeat_le_exp_mul_pow_dist (ω := ω) ht x y
    have hyn := bondHeat_nonneg ω ht x y
    calc |∑ z ∈ (openGraph ω).neighborFinset y, (bondHeat ω t x z - bondHeat ω t x y)|
        ≤ ∑ z ∈ (openGraph ω).neighborFinset y, |bondHeat ω t x z - bondHeat ω t x y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z ∈ (openGraph ω).neighborFinset y,
            65 * Real.exp (126 * d * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hzb := bondHeat_nbr_le ht h hz
          have hzn := bondHeat_nonneg ω ht x z
          rw [abs_le]
          constructor <;> nlinarith [Real.exp_pos (126 * d * t),
            pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 64) ((openGraph ω).dist x y)]
      _ = (openGraph ω).degree y * (65 * Real.exp (126 * d * t) *
            (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          rw [Finset.sum_const, (openGraph ω).card_neighborFinset_eq_degree, nsmul_eq_mul]
      _ ≤ ((2 * d : ℕ) : ℝ) * (65 * Real.exp (126 * d * t) * (1 / 64 : ℝ) ^
            (openGraph ω).dist x y) := by
          gcongr
          exact_mod_cast openGraph_degree_le_two_mul ω y
      _ = _ := by push_cast; ring
  · rw [openLaplacian_bondHeat_eq_zero h, abs_zero]
    positivity

/-! ### The functionals `M` and `Q` -/

/-- **Nash's mean displacement** `M(t) = Σ_y |y - x| p_t(x, y)` (Barlow 2004, §3). -/
noncomputable def meanDist (ω : Configuration d) (x : Vertex d) (t : ℝ) : ℝ :=
  ∑' y, latticeDist x y * bondHeat ω t x y

/-- **Nash's entropy** `Q(t) = -Σ_y p_t(x, y) log p_t(x, y)` (Barlow 2004, §3). -/
noncomputable def heatEntropy (ω : Configuration d) (x : Vertex d) (t : ℝ) : ℝ :=
  ∑' y, Real.negMulLog (bondHeat ω t x y)

/-- The summable majorant `C · 16^{-|y - x|₁}`. -/
noncomputable def decayMajorant (x : Vertex d) (C : ℝ) (y : Vertex d) : ℝ :=
  C * (1 / 16 : ℝ) ^ l1Dist x y

omit [NeZero d] in
theorem summable_decayMajorant (x : Vertex d) (C : ℝ) : Summable (decayMajorant x C) :=
  (summable_pow_l1Dist x (by norm_num) (by norm_num)).mul_left C

theorem abs_latticeDist_mul_bondHeat_le {t b : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) (x y : Vertex d) :
    |latticeDist x y * bondHeat ω t x y| ≤ decayMajorant x (4 * Real.exp (126 * d * b)) y := by
  by_cases h : (openGraph ω).Reachable x y
  · have hd := latticeDist_le_dist h
    have hu := bondHeat_le_exp_mul_pow_dist (ω := ω) ht x y
    have hn := bondHeat_nonneg ω ht x y
    have hpoly := one_add_sq_mul_pow_dist_le h
    have hexp : Real.exp (126 * d * t) ≤ Real.exp (126 * d * b) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htb (by positivity))
    rw [abs_mul, abs_of_nonneg (latticeDist_nonneg x y), abs_of_nonneg hn, decayMajorant]
    set k := ((openGraph ω).dist x y : ℝ)
    have hk : latticeDist x y ≤ (1 + k) ^ 2 := by nlinarith [latticeDist_nonneg x y]
    calc latticeDist x y * bondHeat ω t x y
        ≤ (1 + k) ^ 2 * (Real.exp (126 * d * b) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          apply mul_le_mul hk (hu.trans (mul_le_mul_of_nonneg_right hexp (by positivity))) hn
            (by positivity)
      _ = Real.exp (126 * d * b) * ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by ring
      _ ≤ Real.exp (126 * d * b) * (4 * (1 / 16 : ℝ) ^ l1Dist x y) :=
          mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
      _ = _ := by ring
  · rw [bondHeat_eq_zero_of_not_reachable' h, mul_zero, abs_zero, decayMajorant]
    positivity

theorem abs_latticeDist_mul_openLaplacian_le {t b : ℝ} (ht : 0 ≤ t) (htb : t ≤ b)
    (x y : Vertex d) :
    |latticeDist x y * openLaplacian ω (fun z => bondHeat ω t x z) y| ≤
      decayMajorant x (520 * d * Real.exp (126 * d * b)) y := by
  by_cases h : (openGraph ω).Reachable x y
  · have hd := latticeDist_le_dist h
    have hL := abs_openLaplacian_bondHeat_le (ω := ω) ht x y
    have hpoly := one_add_sq_mul_pow_dist_le h
    have hexp : Real.exp (126 * d * t) ≤ Real.exp (126 * d * b) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htb (by positivity))
    rw [abs_mul, abs_of_nonneg (latticeDist_nonneg x y), decayMajorant]
    set k := ((openGraph ω).dist x y : ℝ)
    have hk : latticeDist x y ≤ (1 + k) ^ 2 := by nlinarith [latticeDist_nonneg x y]
    calc latticeDist x y * |openLaplacian ω (fun z => bondHeat ω t x z) y|
        ≤ (1 + k) ^ 2 * (130 * d * Real.exp (126 * d * b) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          apply mul_le_mul hk (hL.trans ?_) (abs_nonneg _) (by positivity)
          gcongr
      _ = 130 * d * Real.exp (126 * d * b) * ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          ring
      _ ≤ 130 * d * Real.exp (126 * d * b) * (4 * (1 / 16 : ℝ) ^ l1Dist x y) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  · rw [openLaplacian_bondHeat_eq_zero h, mul_zero, abs_zero, decayMajorant]
    positivity

theorem abs_negMulLog_bondHeat_le {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b)
    (x y : Vertex d) :
    |Real.negMulLog (bondHeat ω t x y)| ≤
      decayMajorant x ((2 + 2 * d * b + |Real.log a|) * 4 * Real.exp (126 * d * b)) y := by
  have hb0' : 0 ≤ b := ha.le.trans (hat.trans htb)
  by_cases h : (openGraph ω).Reachable x y
  · have ht : 0 ≤ t := (ha.le.trans hat)
    have hlog := abs_log_bondHeat_le ha hat htb h
    have hu := bondHeat_le_exp_mul_pow_dist (ω := ω) ht x y
    have hn := bondHeat_nonneg ω ht x y
    have hpoly := one_add_sq_mul_pow_dist_le h
    have hexp : Real.exp (126 * d * t) ≤ Real.exp (126 * d * b) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htb (by positivity))
    have hb0 : 0 ≤ b := ht.trans htb
    set k := ((openGraph ω).dist x y : ℝ)
    have hk0 : 0 ≤ k := Nat.cast_nonneg _
    have hfac : 2 * d * b + k * |Real.log a| + k ^ 2 ≤ (2 + 2 * d * b + |Real.log a|) * (1 + k) ^ 2 := by
      have hdb : 0 ≤ 2 * d * b := by positivity
      nlinarith [abs_nonneg (Real.log a), mul_nonneg hdb hk0, mul_nonneg hdb (sq_nonneg k),
        mul_nonneg (abs_nonneg (Real.log a)) hk0, mul_nonneg (abs_nonneg (Real.log a)) (sq_nonneg k)]
    rw [Real.negMulLog, neg_mul, abs_neg, abs_mul, abs_of_nonneg hn, decayMajorant]
    calc bondHeat ω t x y * |Real.log (bondHeat ω t x y)|
        ≤ (Real.exp (126 * d * b) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) *
            ((2 + 2 * d * b + |Real.log a|) * (1 + k) ^ 2) := by
          apply mul_le_mul (hu.trans (mul_le_mul_of_nonneg_right hexp (by positivity)))
            (hlog.trans hfac) (abs_nonneg _) (by positivity)
      _ = (2 + 2 * d * b + |Real.log a|) * Real.exp (126 * d * b) *
            ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by ring
      _ ≤ (2 + 2 * d * b + |Real.log a|) * Real.exp (126 * d * b) * (4 * (1 / 16 : ℝ) ^ l1Dist x y) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  · rw [bondHeat_eq_zero_of_not_reachable' h, Real.negMulLog_zero, abs_zero, decayMajorant]
    positivity

theorem abs_log_mul_openLaplacian_le {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b)
    (x y : Vertex d) :
    |(-Real.log (bondHeat ω t x y) - 1) * openLaplacian ω (fun z => bondHeat ω t x z) y| ≤
      decayMajorant x ((2 + 2 * d * b + |Real.log a|) * 520 * d * Real.exp (126 * d * b)) y := by
  have hb0' : 0 ≤ b := ha.le.trans (hat.trans htb)
  by_cases h : (openGraph ω).Reachable x y
  · have ht : 0 ≤ t := (ha.le.trans hat)
    have hlog := abs_log_bondHeat_le ha hat htb h
    have hL := abs_openLaplacian_bondHeat_le (ω := ω) ht x y
    have hpoly := one_add_sq_mul_pow_dist_le h
    have hexp : Real.exp (126 * d * t) ≤ Real.exp (126 * d * b) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htb (by positivity))
    have hb0 : 0 ≤ b := ht.trans htb
    set k := ((openGraph ω).dist x y : ℝ)
    have hk0 : 0 ≤ k := Nat.cast_nonneg _
    have hfac : |-Real.log (bondHeat ω t x y) - 1| ≤ (2 + 2 * d * b + |Real.log a|) * (1 + k) ^ 2 := by
      have h1 : |-Real.log (bondHeat ω t x y) - 1| ≤ |Real.log (bondHeat ω t x y)| + 1 := by
        calc |-Real.log (bondHeat ω t x y) - 1| ≤ |-Real.log (bondHeat ω t x y)| + |(1 : ℝ)| :=
              abs_sub _ _
          _ = _ := by rw [abs_neg, abs_one]
      have hdb : 0 ≤ 2 * d * b := by positivity
      nlinarith [abs_nonneg (Real.log a), mul_nonneg hdb hk0, mul_nonneg hdb (sq_nonneg k),
        mul_nonneg (abs_nonneg (Real.log a)) hk0, mul_nonneg (abs_nonneg (Real.log a)) (sq_nonneg k)]
    rw [abs_mul, decayMajorant]
    calc |-Real.log (bondHeat ω t x y) - 1| * |openLaplacian ω (fun z => bondHeat ω t x z) y|
        ≤ ((2 + 2 * d * b + |Real.log a|) * (1 + k) ^ 2) *
            (130 * d * Real.exp (126 * d * b) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          apply mul_le_mul hfac (hL.trans ?_) (abs_nonneg _) (by positivity)
          gcongr
      _ = (2 + 2 * d * b + |Real.log a|) * 130 * d * Real.exp (126 * d * b) *
            ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by ring
      _ ≤ (2 + 2 * d * b + |Real.log a|) * 130 * d * Real.exp (126 * d * b) *
            (4 * (1 / 16 : ℝ) ^ l1Dist x y) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  · rw [openLaplacian_bondHeat_eq_zero h, mul_zero, abs_zero, decayMajorant]
    positivity

/-- `M` is continuous on `[0, b]`. -/
theorem continuousOn_meanDist (x : Vertex d) (b : ℝ) :
    ContinuousOn (meanDist ω x) (Set.Icc 0 b) := by
  refine continuousOn_tsum (u := decayMajorant x (4 * Real.exp (126 * d * b)))
    (fun y => (continuous_const.mul (continuous_bondHeat ω x y)).continuousOn)
    (summable_decayMajorant x _) fun y s hs => ?_
  rw [Real.norm_eq_abs]
  exact abs_latticeDist_mul_bondHeat_le hs.1 hs.2 x y

/-- `Q` is continuous on `[a, b]` for `a > 0`. -/
theorem continuousOn_heatEntropy (x : Vertex d) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (heatEntropy ω x) (Set.Icc a b) := by
  refine continuousOn_tsum (u := decayMajorant x ((2 + 2 * d * b + |Real.log a|) * 4 *
    Real.exp (126 * d * b)))
    (fun y => (Real.continuous_negMulLog.comp (continuous_bondHeat ω x y)).continuousOn)
    (summable_decayMajorant x _) fun y s hs => ?_
  rw [Real.norm_eq_abs]
  exact abs_negMulLog_bondHeat_le ha hs.1 hs.2 x y

theorem summable_negMulLog_bondHeat {t : ℝ} (ht : 0 < t) (x : Vertex d) :
    Summable fun y => Real.negMulLog (bondHeat ω t x y) :=
  Summable.of_norm_bounded (summable_decayMajorant x _) fun y => by
    rw [Real.norm_eq_abs]
    exact abs_negMulLog_bondHeat_le (b := t) ht le_rfl le_rfl x y

theorem summable_latticeDist_mul_bondHeat {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    Summable fun y => latticeDist x y * bondHeat ω t x y :=
  Summable.of_norm_bounded (summable_decayMajorant x _) fun y => by
    rw [Real.norm_eq_abs]
    exact abs_latticeDist_mul_bondHeat_le (b := t) ht le_rfl x y

/-- The derivative of `M`. -/
theorem hasDerivAt_meanDist {t : ℝ} (ht : 0 < t) (x : Vertex d) :
    HasDerivAt (meanDist ω x)
      (∑' y, latticeDist x y * openLaplacian ω (fun z => bondHeat ω t x z) y) t := by
  have key := hasDerivAt_tsum_of_isPreconnected
    (u := decayMajorant x (520 * d * Real.exp (126 * d * (t + 1))))
    (g := fun y s => latticeDist x y * bondHeat ω s x y)
    (g' := fun y s => latticeDist x y * openLaplacian ω (fun z => bondHeat ω s x z) y)
    (t := Set.Ioo 0 (t + 1)) (y₀ := t) (y := t)
    (summable_decayMajorant x _) isOpen_Ioo isPreconnected_Ioo
    (fun y s _ => (hasDerivAt_bondHeat_snd s x y).const_mul _)
    (fun y s hs => by
      rw [Real.norm_eq_abs]
      exact abs_latticeDist_mul_openLaplacian_le hs.1.le hs.2.le x y)
    ⟨ht, by linarith⟩ (summable_latticeDist_mul_bondHeat ht.le x) ⟨ht, by linarith⟩
  exact key

/-- The derivative of `Q`. -/
theorem hasDerivAt_heatEntropy {t : ℝ} (ht : 0 < t) (x : Vertex d) :
    HasDerivAt (heatEntropy ω x)
      (∑' y, (-Real.log (bondHeat ω t x y) - 1) *
        openLaplacian ω (fun z => bondHeat ω t x z) y) t := by
  have hderiv : ∀ (y : Vertex d) (s : ℝ), s ∈ Set.Ioo (t / 2) (t + 1) →
      HasDerivAt (fun s => Real.negMulLog (bondHeat ω s x y))
        ((-Real.log (bondHeat ω s x y) - 1) * openLaplacian ω (fun z => bondHeat ω s x z) y) s := by
    intro y s hs
    have hs0 : 0 < s := lt_trans (by linarith) hs.1
    by_cases h : (openGraph ω).Reachable x y
    · have hne := (bondHeat_pos hs0 h).ne'
      exact (Real.hasDerivAt_negMulLog hne).comp s (hasDerivAt_bondHeat_snd s x y)
    · have e : (fun s => Real.negMulLog (bondHeat ω s x y)) = fun _ => 0 := by
        funext s
        rw [bondHeat_eq_zero_of_not_reachable' h, Real.negMulLog_zero]
      rw [e, openLaplacian_bondHeat_eq_zero h, mul_zero]
      exact hasDerivAt_const s 0
  have key := hasDerivAt_tsum_of_isPreconnected
    (u := decayMajorant x ((2 + 2 * d * (t + 1) + |Real.log (t / 2)|) * 520 * d *
      Real.exp (126 * d * (t + 1))))
    (g := fun y s => Real.negMulLog (bondHeat ω s x y))
    (g' := fun y s => (-Real.log (bondHeat ω s x y) - 1) *
      openLaplacian ω (fun z => bondHeat ω s x z) y)
    (t := Set.Ioo (t / 2) (t + 1)) (y₀ := t) (y := t)
    (summable_decayMajorant x _) isOpen_Ioo isPreconnected_Ioo hderiv
    (fun y s hs => by
      rw [Real.norm_eq_abs]
      exact abs_log_mul_openLaplacian_le (by linarith) hs.1.le hs.2.le x y)
    ⟨by linarith, by linarith⟩ (summable_negMulLog_bondHeat ht x) ⟨by linarith, by linarith⟩
  exact key

end Rigidity.BarlowLattice

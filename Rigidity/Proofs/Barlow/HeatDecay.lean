import Rigidity.Proofs.Barlow.OnDiagonal
import Rigidity.Proofs.Green.LazyCarneVaropoulos
import Rigidity.Proofs.Green.PlanarCarneVaropoulos
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Decay of the planar heat kernel and the functionals of Nash

For the heat kernel `p_t(x, ·)` of the variable speed random walk on the open graph of a planar
configuration, this file proves the bounds that make the functionals of Nash (used by Barlow,
*Random walks on supercritical percolation clusters*, Ann. Probab. 32 (2004), §3)

  `M(t) = Σ_y |y - x| p_t(x, y)`,   `Q(t) = -Σ_y p_t(x, y) log p_t(x, y)`

differentiable, with the derivatives of the source, (3.8) and (3.10):

  `M'(t) = -½ Σ_{(a, b)} (|b - x| - |a - x|)(p_t(x, b) - p_t(x, a))`,
  `Q'(t) = ½ Σ_{(a, b)} (log p_t(x, b) - log p_t(x, a))(p_t(x, b) - p_t(x, a))`,

the sums running over the directed open edges. The source justifies the use of the Gauss–Green
formula by the decay (1.5) of `p_t(x, ·)`; here the decay is
`p_t(x, y) ≤ e^{252 t} 64^{-d(x, y)}` in the graph distance `d` (`openHeat_le_exp_mul_pow_dist`)
together with the lower bound `p_t(x, y) ≥ e^{-4t} t^{d} / d!` on the component of `x`
(`poissonWeight_mul_le_openHeat`), which controls `log p_t(x, y)`.
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Barlow

variable {ω : Configuration 2}

/-! ### The `ℓ¹` distance and geometric lattice sums -/

/-- The `ℓ¹` distance of two lattice points. -/
def l1Dist (x y : Vertex 2) : ℕ := (y 0 - x 0).natAbs + (y 1 - x 1).natAbs

theorem natAbs_neg_add_one (n : ℕ) : ((-((n : ℤ) + 1))).natAbs = n + 1 := by
  have hz : (((-((n : ℤ) + 1))).natAbs : ℤ) = ((n + 1 : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, abs_neg, abs_of_nonneg (by positivity)]
    push_cast
    ring
  exact_mod_cast hz

theorem hasSum_pow_natAbs {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun a : ℤ => q ^ a.natAbs) ((1 - q)⁻¹ + q * (1 - q)⁻¹) := by
  have h1 : HasSum (fun n : ℕ => q ^ ((n : ℤ).natAbs)) (1 - q)⁻¹ := by
    have e : (fun n : ℕ => q ^ ((n : ℤ).natAbs)) = fun n : ℕ => q ^ n :=
      funext fun n => by rw [Int.natAbs_natCast]
    rw [e]
    exact hasSum_geometric_of_lt_one hq0 hq1
  have h2 : HasSum (fun n : ℕ => q ^ ((-((n : ℤ) + 1))).natAbs) (q * (1 - q)⁻¹) := by
    have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left q
    have e : (fun n : ℕ => q ^ ((-((n : ℤ) + 1))).natAbs) = fun n : ℕ => q * q ^ n := by
      funext n
      rw [natAbs_neg_add_one n, pow_succ, mul_comm]
    rw [e]
    exact h
  exact h1.of_nat_of_neg_add_one h2

/-- Coordinates of a lattice point relative to `x`. -/
def latticeShift (x : Vertex 2) : Vertex 2 ≃ ℤ × ℤ where
  toFun y := (y 0 - x 0, y 1 - x 1)
  invFun p := ![p.1 + x 0, p.2 + x 1]
  left_inv y := by
    funext i
    fin_cases i
    · simp
    · simp
  right_inv p := by
    ext <;> simp

/-- `Σ_y q^{|y - x|₁} = ((1 - q)⁻¹ + q (1 - q)⁻¹)²`. -/
theorem hasSum_pow_l1Dist (x : Vertex 2) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun y => q ^ l1Dist x y) (((1 - q)⁻¹ + q * (1 - q)⁻¹) ^ 2) := by
  set g : ℤ → ℝ := fun a => q ^ a.natAbs with hg
  have hz : HasSum g ((1 - q)⁻¹ + q * (1 - q)⁻¹) := hasSum_pow_natAbs hq0 hq1
  have hs : Summable fun p : ℤ × ℤ => g p.1 * g p.2 :=
    Summable.mul_of_nonneg hz.summable hz.summable (fun a => pow_nonneg hq0 _)
      (fun a => pow_nonneg hq0 _)
  have hprod : HasSum (fun p : ℤ × ℤ => g p.1 * g p.2)
      (((1 - q)⁻¹ + q * (1 - q)⁻¹) * ((1 - q)⁻¹ + q * (1 - q)⁻¹)) := HasSum.mul hz hz hs
  have h := (latticeShift x).hasSum_iff.2 hprod
  have e : (fun y => q ^ l1Dist x y) =
      (fun p : ℤ × ℤ => g p.1 * g p.2) ∘ latticeShift x := by
    funext y
    show q ^ ((y 0 - x 0).natAbs + (y 1 - x 1).natAbs) =
      q ^ (y 0 - x 0).natAbs * q ^ (y 1 - x 1).natAbs
    exact pow_add _ _ _
  rw [e, sq]
  exact h

theorem summable_pow_l1Dist (x : Vertex 2) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun y => q ^ l1Dist x y :=
  (hasSum_pow_l1Dist x hq0 hq1).summable

theorem l1Dist_le_dist {x y : Vertex 2} (h : (openGraph ω).Reachable x y) :
    l1Dist x y ≤ (openGraph ω).dist x y := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist
  have h1 := sum_abs_sub_le_length_openGraph q
  rw [Fin.sum_univ_two, hq] at h1
  have h2 : ((l1Dist x y : ℕ) : ℤ) = |y 0 - x 0| + |y 1 - x 1| := by
    simp [l1Dist]
  omega

theorem latticeDist_le_dist {x y : Vertex 2} (h : (openGraph ω).Reachable x y) :
    latticeDist x y ≤ (openGraph ω).dist x y := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist
  have h1 := norm_edz_le_length q
  rw [hq] at h1
  exact h1

/-- `(1 + k)² 64^{-k} ≤ 4 · 16^{-k}`. -/
theorem one_add_sq_mul_pow_le (k : ℕ) :
    (1 + (k : ℝ)) ^ 2 * (1 / 64 : ℝ) ^ k ≤ 4 * (1 / 16 : ℝ) ^ k := by
  have h1 : (1 + (k : ℝ)) ≤ 2 * 2 ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    have h' : ((k : ℕ) : ℝ) + 1 ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  have h2 : (1 + (k : ℝ)) ^ 2 ≤ 4 * 4 ^ k := by
    have h0 : (0 : ℝ) ≤ 1 + k := by positivity
    calc (1 + (k : ℝ)) ^ 2 ≤ (2 * 2 ^ k) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * 4 ^ k := by
          rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
          norm_num
  calc (1 + (k : ℝ)) ^ 2 * (1 / 64 : ℝ) ^ k ≤ 4 * 4 ^ k * (1 / 64 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 4 * (1 / 16 : ℝ) ^ k := by
        rw [mul_assoc, ← mul_pow]
        norm_num

/-- `(1 + d)² 64^{-d} ≤ 4 · 16^{-|y - x|₁}` on the component of `x`. -/
theorem one_add_sq_mul_pow_dist_le {x y : Vertex 2} (h : (openGraph ω).Reachable x y) :
    (1 + ((openGraph ω).dist x y : ℝ)) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y ≤
      4 * (1 / 16 : ℝ) ^ l1Dist x y := by
  refine (one_add_sq_mul_pow_le _).trans ?_
  have := l1Dist_le_dist h
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) this)
    (by norm_num)

/-! ### Upper and lower bounds on the heat kernel -/

theorem lazyPow_eq_zero_of_lt_dist {x y : Vertex 2} {n : ℕ} (hn : n < (openGraph ω).dist x y) :
    lazyPow (openGraph ω) 4 n x y = 0 := by
  by_contra h
  obtain ⟨q, hq⟩ := exists_walk_of_lazyPow_ne_zero n x y h
  have := SimpleGraph.dist_le q
  omega

/-- `p_t(x, y) ≤ e^{252 t} 64^{-d(x, y)}` for `t ≥ 0`. -/
theorem openHeat_le_exp_mul_pow_dist {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) :
    openHeat ω t x y ≤ Real.exp (252 * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
  set j := (openGraph ω).dist x y with hj
  have h := openHeat_le_of_lazyPow_le ω (A := 0) (B := (1 / 64 : ℝ) ^ j) (θ := 64) ht (fun n => by
    by_cases hn : n < j
    · rw [lazyPow_eq_zero_of_lt_dist hn]
      positivity
    · have hjn : j ≤ n := le_of_not_gt hn
      have h1 := (lazyPow_mem_Icc (by norm_num) (openGraph_degree_le_four ω) n x y).2
      refine h1.trans ?_
      rw [zero_add, one_div, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_right₀ (by norm_num) hjn)
  calc openHeat ω t x y ≤ 0 + (1 / 64 : ℝ) ^ j * Real.exp (4 * t * (64 - 1)) := h
    _ = Real.exp (252 * t) * (1 / 64 : ℝ) ^ j := by ring_nf

theorem pow_le_lazyPow_of_walk {x y : Vertex 2} (q : (openGraph ω).Walk x y) :
    (1 / 4 : ℝ) ^ q.length ≤ lazyPow (openGraph ω) 4 q.length x y := by
  induction q with
  | nil => simp [lazyPow_zero]
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.length_cons, lazyPow_succ]
    have hdeg := openGraph_degree_le_four ω
    have ha : 0 ≤ 1 - ((openGraph ω).degree u : ℝ) / (4 : ℕ) := by
      have : ((openGraph ω).degree u : ℝ) ≤ 4 := by exact_mod_cast hdeg u
      rw [sub_nonneg, div_le_one (by norm_num)]
      exact_mod_cast hdeg u
    have h0 := (lazyPow_mem_Icc (by norm_num) hdeg p.length u w).1
    have hv : v ∈ (openGraph ω).neighborFinset u := ((openGraph ω).mem_neighborFinset u v).2 h
    have hsingle : lazyPow (openGraph ω) 4 p.length v w ≤
        ∑ z ∈ (openGraph ω).neighborFinset u, lazyPow (openGraph ω) 4 p.length z w :=
      Finset.single_le_sum (fun z _ => (lazyPow_mem_Icc (by norm_num) hdeg p.length z w).1) hv
    have h4 : (1 / ((4 : ℕ) : ℝ)) = 1 / 4 := by norm_num
    rw [h4, pow_succ]
    nlinarith [mul_nonneg ha h0]

/-- On the component of `x`: `e^{-4t} (4t)^d / d! · 4^{-d} ≤ p_t(x, y)`, `d = d(x, y)`. -/
theorem poissonWeight_mul_le_openHeat {t : ℝ} (ht : 0 ≤ t) {x y : Vertex 2}
    (h : (openGraph ω).Reachable x y) :
    poissonWeight 4 t ((openGraph ω).dist x y) * (1 / 4 : ℝ) ^ (openGraph ω).dist x y ≤
      openHeat ω t x y := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist
  have h1 := pow_le_lazyPow_of_walk q
  rw [hq] at h1
  have hs := summable_vsrwHeat (G := openGraph ω) (D := 4) (by norm_num)
    (openGraph_degree_le_four ω) t x y
  calc poissonWeight 4 t ((openGraph ω).dist x y) * (1 / 4 : ℝ) ^ (openGraph ω).dist x y
      ≤ poissonWeight 4 t ((openGraph ω).dist x y) *
          lazyPow (openGraph ω) 4 ((openGraph ω).dist x y) x y :=
        mul_le_mul_of_nonneg_left h1 (poissonWeight_nonneg ht _)
    _ ≤ openHeat ω t x y := hs.le_tsum _ (fun n _ => mul_nonneg (poissonWeight_nonneg ht n)
        (lazyPow_mem_Icc (by norm_num) (openGraph_degree_le_four ω) n x y).1)

theorem openHeat_pos {t : ℝ} (ht : 0 < t) {x y : Vertex 2} (h : (openGraph ω).Reachable x y) :
    0 < openHeat ω t x y := by
  refine lt_of_lt_of_le ?_ (poissonWeight_mul_le_openHeat ht.le h)
  unfold poissonWeight
  positivity

/-- On the component of `x`, for `0 < a ≤ t ≤ b`:
`|log p_t(x, y)| ≤ 4b + d |log a| + d²`, `d = d(x, y)`. -/
theorem abs_log_openHeat_le {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) {x y : Vertex 2}
    (h : (openGraph ω).Reachable x y) :
    |Real.log (openHeat ω t x y)| ≤
      4 * b + (openGraph ω).dist x y * |Real.log a| + ((openGraph ω).dist x y : ℝ) ^ 2 := by
  set k := (openGraph ω).dist x y with hk
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hpos := openHeat_pos ht h
  have hle1 := openHeat_le_one ω ht.le x y
  have hlow := poissonWeight_mul_le_openHeat ht.le h
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
  have he : Real.exp (-4 * b) * Real.exp (-|Real.log a|) ^ k * (Real.exp ((k : ℝ) ^ 2))⁻¹ =
      Real.exp (-(4 * b + k * |Real.log a| + (k : ℝ) ^ 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hp : poissonWeight 4 t k * (1 / 4 : ℝ) ^ k =
      Real.exp (-4 * t) * t ^ k * ((k.factorial : ℝ))⁻¹ := by
    unfold poissonWeight
    have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
    have h44 : (4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    rw [h4, mul_pow, div_eq_mul_inv]
    calc Real.exp (-4 * t) * (4 ^ k * t ^ k) * ((k.factorial : ℝ))⁻¹ * (1 / 4 : ℝ) ^ k
        = Real.exp (-4 * t) * t ^ k * ((k.factorial : ℝ))⁻¹ * ((4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k) := by
          ring
      _ = _ := by rw [h44, mul_one]
  have hk0 : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hexp : Real.exp (-(4 * b + k * |Real.log a| + (k : ℝ) ^ 2)) ≤
      poissonWeight 4 t k * (1 / 4 : ℝ) ^ k := by
    rw [← he, hp]
    have f1 : Real.exp (-4 * b) ≤ Real.exp (-4 * t) := Real.exp_le_exp.2 (by linarith)
    have f2 : Real.exp (-|Real.log a|) ^ k ≤ t ^ k :=
      pow_le_pow_left₀ (Real.exp_pos _).le hal k
    have f3 : (Real.exp ((k : ℝ) ^ 2))⁻¹ ≤ ((k.factorial : ℝ))⁻¹ := inv_anti₀ hk0 hfact
    exact mul_le_mul (mul_le_mul f1 f2 (pow_nonneg (Real.exp_pos _).le k) (Real.exp_pos _).le) f3
      (inv_nonneg.2 (Real.exp_pos _).le) (by positivity)
  have hlogle : -(4 * b + k * |Real.log a| + (k : ℝ) ^ 2) ≤ Real.log (openHeat ω t x y) := by
    rw [Real.le_log_iff_exp_le hpos]
    exact hexp.trans hlow
  have hlog0 : Real.log (openHeat ω t x y) ≤ 0 := Real.log_nonpos hpos.le hle1
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg (Real.log a), sq_nonneg (k : ℝ)]

theorem openHeat_eq_zero_of_not_reachable' {x y : Vertex 2} (h : ¬ (openGraph ω).Reachable x y)
    (t : ℝ) : openHeat ω t x y = 0 :=
  openHeat_eq_zero_of_not_reachable ω h t

/-- A neighbour of a point of the component of `x` carries at most `64 e^{252t} 64^{-d(x, y)}`. -/
theorem openHeat_nbr_le {t : ℝ} (ht : 0 ≤ t) {x y z : Vertex 2}
    (hxy : (openGraph ω).Reachable x y) (hz : z ∈ (openGraph ω).neighborFinset y) :
    openHeat ω t x z ≤ 64 * Real.exp (252 * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
  have hadj : (openGraph ω).Adj y z := ((openGraph ω).mem_neighborFinset y z).1 hz
  have hxz : (openGraph ω).Reachable x z := hxy.trans hadj.reachable
  have hd : (openGraph ω).dist x y ≤ (openGraph ω).dist x z + 1 := by
    obtain ⟨q, hq⟩ := hxz.exists_walk_length_eq_dist
    have := SimpleGraph.dist_le (q.concat hadj.symm)
    rw [SimpleGraph.Walk.length_concat, hq] at this
    exact this
  refine (openHeat_le_exp_mul_pow_dist ht x z).trans ?_
  have hp : (1 / 64 : ℝ) ^ (openGraph ω).dist x z ≤ 64 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
    have h1 : (1 / 64 : ℝ) ^ ((openGraph ω).dist x z + 1) ≤ (1 / 64 : ℝ) ^ (openGraph ω).dist x y :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
    rw [pow_succ] at h1
    linarith
  calc Real.exp (252 * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x z
      ≤ Real.exp (252 * t) * (64 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = _ := by ring

/-- The heat equation in the second variable. -/
theorem hasDerivAt_openHeat_snd (t : ℝ) (x y : Vertex 2) :
    HasDerivAt (fun s => openHeat ω s x y)
      (openLaplacian ω (fun z => openHeat ω t x z) y) t := by
  have h := hasDerivAt_openHeat ω t y x
  have e1 : (fun s => openHeat ω s y x) = fun s => openHeat ω s x y :=
    funext fun s => openHeat_symm ω s y x
  have e2 : (fun z => openHeat ω t z x) = fun z => openHeat ω t x z :=
    funext fun z => openHeat_symm ω t z x
  rw [e1, e2] at h
  exact h

theorem openLaplacian_openHeat_eq_zero {t : ℝ} {x y : Vertex 2}
    (h : ¬ (openGraph ω).Reachable x y) : openLaplacian ω (fun z => openHeat ω t x z) y = 0 := by
  unfold openLaplacian
  refine Finset.sum_eq_zero fun z hz => ?_
  have hadj : (openGraph ω).Adj y z := ((openGraph ω).mem_neighborFinset y z).1 hz
  have hz' : ¬ (openGraph ω).Reachable x z := fun hxz => h (hxz.trans hadj.symm.reachable)
  show openHeat ω t x z - openHeat ω t x y = 0
  rw [openHeat_eq_zero_of_not_reachable' hz', openHeat_eq_zero_of_not_reachable' h, sub_zero]

/-- `|Δ_y p_t(x, ·)| ≤ 260 e^{252t} 64^{-d(x, y)}`. -/
theorem abs_openLaplacian_openHeat_le {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) :
    |openLaplacian ω (fun z => openHeat ω t x z) y| ≤
      260 * Real.exp (252 * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
  by_cases h : (openGraph ω).Reachable x y
  · unfold openLaplacian
    have hy := openHeat_le_exp_mul_pow_dist (ω := ω) ht x y
    have hyn := openHeat_nonneg ω ht x y
    calc |∑ z ∈ (openGraph ω).neighborFinset y, (openHeat ω t x z - openHeat ω t x y)|
        ≤ ∑ z ∈ (openGraph ω).neighborFinset y, |openHeat ω t x z - openHeat ω t x y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z ∈ (openGraph ω).neighborFinset y,
            65 * Real.exp (252 * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hzb := openHeat_nbr_le ht h hz
          have hzn := openHeat_nonneg ω ht x z
          rw [abs_le]
          constructor <;> nlinarith [Real.exp_pos (252 * t),
            pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 64) ((openGraph ω).dist x y)]
      _ = (openGraph ω).degree y * (65 * Real.exp (252 * t) *
            (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          rw [Finset.sum_const, (openGraph ω).card_neighborFinset_eq_degree, nsmul_eq_mul]
      _ ≤ 4 * (65 * Real.exp (252 * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          gcongr
          exact_mod_cast openGraph_degree_le_four ω y
      _ = _ := by ring
  · rw [openLaplacian_openHeat_eq_zero h, abs_zero]
    positivity

/-! ### The functionals `M` and `Q` -/

/-- **Nash's mean displacement** `M(t) = Σ_y |y - x| p_t(x, y)` (Barlow 2004, §3). -/
noncomputable def meanDist (ω : Configuration 2) (x : Vertex 2) (t : ℝ) : ℝ :=
  ∑' y, latticeDist x y * openHeat ω t x y

/-- **Nash's entropy** `Q(t) = -Σ_y p_t(x, y) log p_t(x, y)` (Barlow 2004, §3). -/
noncomputable def heatEntropy (ω : Configuration 2) (x : Vertex 2) (t : ℝ) : ℝ :=
  ∑' y, Real.negMulLog (openHeat ω t x y)

/-- The summable majorant `C · 16^{-|y - x|₁}`. -/
noncomputable def decayMajorant (x : Vertex 2) (C : ℝ) (y : Vertex 2) : ℝ :=
  C * (1 / 16 : ℝ) ^ l1Dist x y

theorem summable_decayMajorant (x : Vertex 2) (C : ℝ) : Summable (decayMajorant x C) :=
  (summable_pow_l1Dist x (by norm_num) (by norm_num)).mul_left C

theorem abs_latticeDist_mul_openHeat_le {t b : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) (x y : Vertex 2) :
    |latticeDist x y * openHeat ω t x y| ≤ decayMajorant x (4 * Real.exp (252 * b)) y := by
  by_cases h : (openGraph ω).Reachable x y
  · have hd := latticeDist_le_dist h
    have hu := openHeat_le_exp_mul_pow_dist (ω := ω) ht x y
    have hn := openHeat_nonneg ω ht x y
    have hpoly := one_add_sq_mul_pow_dist_le h
    have hexp : Real.exp (252 * t) ≤ Real.exp (252 * b) := Real.exp_le_exp.2 (by linarith)
    rw [abs_mul, abs_of_nonneg (latticeDist_nonneg x y), abs_of_nonneg hn, decayMajorant]
    set k := ((openGraph ω).dist x y : ℝ)
    have hk : latticeDist x y ≤ (1 + k) ^ 2 := by nlinarith [latticeDist_nonneg x y]
    calc latticeDist x y * openHeat ω t x y
        ≤ (1 + k) ^ 2 * (Real.exp (252 * b) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          apply mul_le_mul hk (hu.trans (mul_le_mul_of_nonneg_right hexp (by positivity))) hn
            (by positivity)
      _ = Real.exp (252 * b) * ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by ring
      _ ≤ Real.exp (252 * b) * (4 * (1 / 16 : ℝ) ^ l1Dist x y) :=
          mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
      _ = _ := by ring
  · rw [openHeat_eq_zero_of_not_reachable' h, mul_zero, abs_zero, decayMajorant]
    positivity

theorem abs_latticeDist_mul_openLaplacian_le {t b : ℝ} (ht : 0 ≤ t) (htb : t ≤ b)
    (x y : Vertex 2) :
    |latticeDist x y * openLaplacian ω (fun z => openHeat ω t x z) y| ≤
      decayMajorant x (1040 * Real.exp (252 * b)) y := by
  by_cases h : (openGraph ω).Reachable x y
  · have hd := latticeDist_le_dist h
    have hL := abs_openLaplacian_openHeat_le (ω := ω) ht x y
    have hpoly := one_add_sq_mul_pow_dist_le h
    have hexp : Real.exp (252 * t) ≤ Real.exp (252 * b) := Real.exp_le_exp.2 (by linarith)
    rw [abs_mul, abs_of_nonneg (latticeDist_nonneg x y), decayMajorant]
    set k := ((openGraph ω).dist x y : ℝ)
    have hk : latticeDist x y ≤ (1 + k) ^ 2 := by nlinarith [latticeDist_nonneg x y]
    calc latticeDist x y * |openLaplacian ω (fun z => openHeat ω t x z) y|
        ≤ (1 + k) ^ 2 * (260 * Real.exp (252 * b) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          apply mul_le_mul hk (hL.trans ?_) (abs_nonneg _) (by positivity)
          gcongr
      _ = 260 * Real.exp (252 * b) * ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          ring
      _ ≤ 260 * Real.exp (252 * b) * (4 * (1 / 16 : ℝ) ^ l1Dist x y) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  · rw [openLaplacian_openHeat_eq_zero h, mul_zero, abs_zero, decayMajorant]
    positivity

theorem abs_negMulLog_openHeat_le {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b)
    (x y : Vertex 2) :
    |Real.negMulLog (openHeat ω t x y)| ≤
      decayMajorant x ((2 + 4 * b + |Real.log a|) * 4 * Real.exp (252 * b)) y := by
  have hb0' : 0 ≤ b := ha.le.trans (hat.trans htb)
  by_cases h : (openGraph ω).Reachable x y
  · have ht : 0 ≤ t := (ha.le.trans hat)
    have hlog := abs_log_openHeat_le ha hat htb h
    have hu := openHeat_le_exp_mul_pow_dist (ω := ω) ht x y
    have hn := openHeat_nonneg ω ht x y
    have hpoly := one_add_sq_mul_pow_dist_le h
    have hexp : Real.exp (252 * t) ≤ Real.exp (252 * b) := Real.exp_le_exp.2 (by linarith)
    have hb0 : 0 ≤ b := ht.trans htb
    set k := ((openGraph ω).dist x y : ℝ)
    have hk0 : 0 ≤ k := Nat.cast_nonneg _
    have hfac : 4 * b + k * |Real.log a| + k ^ 2 ≤ (2 + 4 * b + |Real.log a|) * (1 + k) ^ 2 := by
      nlinarith [abs_nonneg (Real.log a)]
    rw [Real.negMulLog, neg_mul, abs_neg, abs_mul, abs_of_nonneg hn, decayMajorant]
    calc openHeat ω t x y * |Real.log (openHeat ω t x y)|
        ≤ (Real.exp (252 * b) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) *
            ((2 + 4 * b + |Real.log a|) * (1 + k) ^ 2) := by
          apply mul_le_mul (hu.trans (mul_le_mul_of_nonneg_right hexp (by positivity)))
            (hlog.trans hfac) (abs_nonneg _) (by positivity)
      _ = (2 + 4 * b + |Real.log a|) * Real.exp (252 * b) *
            ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by ring
      _ ≤ (2 + 4 * b + |Real.log a|) * Real.exp (252 * b) * (4 * (1 / 16 : ℝ) ^ l1Dist x y) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  · rw [openHeat_eq_zero_of_not_reachable' h, Real.negMulLog_zero, abs_zero, decayMajorant]
    positivity

theorem abs_log_mul_openLaplacian_le {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b)
    (x y : Vertex 2) :
    |(-Real.log (openHeat ω t x y) - 1) * openLaplacian ω (fun z => openHeat ω t x z) y| ≤
      decayMajorant x ((2 + 4 * b + |Real.log a|) * 1040 * Real.exp (252 * b)) y := by
  have hb0' : 0 ≤ b := ha.le.trans (hat.trans htb)
  by_cases h : (openGraph ω).Reachable x y
  · have ht : 0 ≤ t := (ha.le.trans hat)
    have hlog := abs_log_openHeat_le ha hat htb h
    have hL := abs_openLaplacian_openHeat_le (ω := ω) ht x y
    have hpoly := one_add_sq_mul_pow_dist_le h
    have hexp : Real.exp (252 * t) ≤ Real.exp (252 * b) := Real.exp_le_exp.2 (by linarith)
    have hb0 : 0 ≤ b := ht.trans htb
    set k := ((openGraph ω).dist x y : ℝ)
    have hk0 : 0 ≤ k := Nat.cast_nonneg _
    have hfac : |-Real.log (openHeat ω t x y) - 1| ≤ (2 + 4 * b + |Real.log a|) * (1 + k) ^ 2 := by
      have h1 : |-Real.log (openHeat ω t x y) - 1| ≤ |Real.log (openHeat ω t x y)| + 1 := by
        calc |-Real.log (openHeat ω t x y) - 1| ≤ |-Real.log (openHeat ω t x y)| + |(1 : ℝ)| :=
              abs_sub _ _
          _ = _ := by rw [abs_neg, abs_one]
      nlinarith [abs_nonneg (Real.log a)]
    rw [abs_mul, decayMajorant]
    calc |-Real.log (openHeat ω t x y) - 1| * |openLaplacian ω (fun z => openHeat ω t x z) y|
        ≤ ((2 + 4 * b + |Real.log a|) * (1 + k) ^ 2) *
            (260 * Real.exp (252 * b) * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by
          apply mul_le_mul hfac (hL.trans ?_) (abs_nonneg _) (by positivity)
          gcongr
      _ = (2 + 4 * b + |Real.log a|) * 260 * Real.exp (252 * b) *
            ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x y) := by ring
      _ ≤ (2 + 4 * b + |Real.log a|) * 260 * Real.exp (252 * b) *
            (4 * (1 / 16 : ℝ) ^ l1Dist x y) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  · rw [openLaplacian_openHeat_eq_zero h, mul_zero, abs_zero, decayMajorant]
    positivity

/-- `M` is continuous on `[0, b]`. -/
theorem continuousOn_meanDist (x : Vertex 2) (b : ℝ) :
    ContinuousOn (meanDist ω x) (Set.Icc 0 b) := by
  refine continuousOn_tsum (u := decayMajorant x (4 * Real.exp (252 * b)))
    (fun y => (continuous_const.mul (continuous_openHeat ω x y)).continuousOn)
    (summable_decayMajorant x _) fun y s hs => ?_
  rw [Real.norm_eq_abs]
  exact abs_latticeDist_mul_openHeat_le hs.1 hs.2 x y

/-- `Q` is continuous on `[a, b]` for `a > 0`. -/
theorem continuousOn_heatEntropy (x : Vertex 2) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (heatEntropy ω x) (Set.Icc a b) := by
  refine continuousOn_tsum (u := decayMajorant x ((2 + 4 * b + |Real.log a|) * 4 *
    Real.exp (252 * b)))
    (fun y => (Real.continuous_negMulLog.comp (continuous_openHeat ω x y)).continuousOn)
    (summable_decayMajorant x _) fun y s hs => ?_
  rw [Real.norm_eq_abs]
  exact abs_negMulLog_openHeat_le ha hs.1 hs.2 x y

theorem summable_negMulLog_openHeat {t : ℝ} (ht : 0 < t) (x : Vertex 2) :
    Summable fun y => Real.negMulLog (openHeat ω t x y) :=
  Summable.of_norm_bounded (summable_decayMajorant x _) fun y => by
    rw [Real.norm_eq_abs]
    exact abs_negMulLog_openHeat_le (b := t) ht le_rfl le_rfl x y

theorem summable_latticeDist_mul_openHeat {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    Summable fun y => latticeDist x y * openHeat ω t x y :=
  Summable.of_norm_bounded (summable_decayMajorant x _) fun y => by
    rw [Real.norm_eq_abs]
    exact abs_latticeDist_mul_openHeat_le (b := t) ht le_rfl x y

/-- The derivative of `M`. -/
theorem hasDerivAt_meanDist {t : ℝ} (ht : 0 < t) (x : Vertex 2) :
    HasDerivAt (meanDist ω x)
      (∑' y, latticeDist x y * openLaplacian ω (fun z => openHeat ω t x z) y) t := by
  have key := hasDerivAt_tsum_of_isPreconnected
    (u := decayMajorant x (1040 * Real.exp (252 * (t + 1))))
    (g := fun y s => latticeDist x y * openHeat ω s x y)
    (g' := fun y s => latticeDist x y * openLaplacian ω (fun z => openHeat ω s x z) y)
    (t := Set.Ioo 0 (t + 1)) (y₀ := t) (y := t)
    (summable_decayMajorant x _) isOpen_Ioo isPreconnected_Ioo
    (fun y s _ => (hasDerivAt_openHeat_snd s x y).const_mul _)
    (fun y s hs => by
      rw [Real.norm_eq_abs]
      exact abs_latticeDist_mul_openLaplacian_le hs.1.le hs.2.le x y)
    ⟨ht, by linarith⟩ (summable_latticeDist_mul_openHeat ht.le x) ⟨ht, by linarith⟩
  exact key

/-- The derivative of `Q`. -/
theorem hasDerivAt_heatEntropy {t : ℝ} (ht : 0 < t) (x : Vertex 2) :
    HasDerivAt (heatEntropy ω x)
      (∑' y, (-Real.log (openHeat ω t x y) - 1) *
        openLaplacian ω (fun z => openHeat ω t x z) y) t := by
  have hderiv : ∀ (y : Vertex 2) (s : ℝ), s ∈ Set.Ioo (t / 2) (t + 1) →
      HasDerivAt (fun s => Real.negMulLog (openHeat ω s x y))
        ((-Real.log (openHeat ω s x y) - 1) * openLaplacian ω (fun z => openHeat ω s x z) y) s := by
    intro y s hs
    have hs0 : 0 < s := lt_trans (by linarith) hs.1
    by_cases h : (openGraph ω).Reachable x y
    · have hne := (openHeat_pos hs0 h).ne'
      exact (Real.hasDerivAt_negMulLog hne).comp s (hasDerivAt_openHeat_snd s x y)
    · have e : (fun s => Real.negMulLog (openHeat ω s x y)) = fun _ => 0 := by
        funext s
        rw [openHeat_eq_zero_of_not_reachable' h, Real.negMulLog_zero]
      rw [e, openLaplacian_openHeat_eq_zero h, mul_zero]
      exact hasDerivAt_const s 0
  have key := hasDerivAt_tsum_of_isPreconnected
    (u := decayMajorant x ((2 + 4 * (t + 1) + |Real.log (t / 2)|) * 1040 *
      Real.exp (252 * (t + 1))))
    (g := fun y s => Real.negMulLog (openHeat ω s x y))
    (g' := fun y s => (-Real.log (openHeat ω s x y) - 1) *
      openLaplacian ω (fun z => openHeat ω s x z) y)
    (t := Set.Ioo (t / 2) (t + 1)) (y₀ := t) (y := t)
    (summable_decayMajorant x _) isOpen_Ioo isPreconnected_Ioo hderiv
    (fun y s hs => by
      rw [Real.norm_eq_abs]
      exact abs_log_mul_openLaplacian_le (by linarith) hs.1.le hs.2.le x y)
    ⟨by linarith, by linarith⟩ (summable_negMulLog_openHeat ht x) ⟨by linarith, by linarith⟩
  exact key

end Rigidity.Barlow

import LatticeProb.Graph.HeatVanishing

/-!
# Off-diagonal transition probabilities from return probabilities

For the simple random walk on an infinite connected locally finite graph, reversibility against
the degree measure and the Cauchy-Schwarz inequality bound the transition probability between two
vertices by the geometric mean of the return probabilities:

  `p_{a+b}(x, y) ≤ √(deg y / deg x) √(p_{2a}(x, x) p_{2b}(y, y))`.

At even times `2n` this is the bound by `√(p_{2n}(x, x) p_{2n}(y, y))`. The even return
densities `p_{2n}(x, x) / deg x` decrease in `n` (the one-step inequality of the Nash iteration),
so at odd times `2n + 1` the same bound holds with the return probabilities at time `2n`.
-/

open scoped Classical

namespace Rigidity.Green

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The even return densities decrease: `p_{2n+2}(x, x) / deg x ≤ p_{2n}(x, x) / deg x`. -/
theorem heat_even_succ_div_le [Infinite V] (hG : G.Connected) (x : V) (n : ℕ) :
    heat G (n + 1 + (n + 1)) x x / (G.degree x : ℝ) ≤ heat G (n + n) x x / (G.degree x : ℝ) := by
  have h := heat_step hG x n
  have hnn : 0 ≤ (heat G (n + n) x x / (G.degree x : ℝ)) ^ 3 :=
    pow_nonneg (div_nonneg (heat_nonneg _ _ _) (Nat.cast_nonneg _)) 3
  linarith

/-- The even return densities form a decreasing sequence. -/
theorem antitone_heat_even_div [Infinite V] (hG : G.Connected) (x : V) :
    Antitone fun n : ℕ => heat G (n + n) x x / (G.degree x : ℝ) :=
  antitone_nat_of_succ_le fun n => heat_even_succ_div_le hG x n

/-- The even return probabilities decrease. -/
theorem heat_even_le_of_le [Infinite V] (hG : G.Connected) (x : V) {m n : ℕ} (hmn : m ≤ n) :
    heat G (n + n) x x ≤ heat G (m + m) x x := by
  have hd : (0 : ℝ) < G.degree x := by exact_mod_cast degree_pos hG x
  have := antitone_heat_even_div hG x hmn
  simp only at this
  rwa [div_le_div_iff_of_pos_right hd] at this

/-- **Off-diagonal bound.** `p_{a+b}(x, y) ≤ √(deg y / deg x) √(p_{2a}(x, x) p_{2b}(y, y))`. -/
theorem heat_add_le_sqrt_mul [Infinite V] (hG : G.Connected) (a b : ℕ) (x y : V) :
    heat G (a + b) x y ≤
      Real.sqrt ((G.degree y : ℝ) / G.degree x) *
        Real.sqrt (heat G (a + a) x x * heat G (b + b) y y) := by
  have hdx : (0 : ℝ) < G.degree x := by exact_mod_cast degree_pos hG x
  have hdy : (0 : ℝ) < G.degree y := by exact_mod_cast degree_pos hG y
  have hxx := heat_nonneg (G := G) (a + a) x x
  have hyy := heat_nonneg (G := G) (b + b) y y
  have hcs := heat_div_le_sqrt_two_time hG a b x y
  rw [div_le_iff₀ hdy] at hcs
  calc heat G (a + b) x y
      ≤ (G.degree y : ℝ) * (Real.sqrt (heat G (a + a) x x / G.degree x) *
          Real.sqrt (heat G (b + b) y y / G.degree y)) := by linarith
    _ = Real.sqrt ((G.degree y : ℝ) ^ 2 *
          (heat G (a + a) x x / G.degree x * (heat G (b + b) y y / G.degree y))) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hdy.le,
          Real.sqrt_mul (div_nonneg hxx hdx.le)]
    _ = Real.sqrt ((G.degree y : ℝ) / G.degree x *
          (heat G (a + a) x x * heat G (b + b) y y)) := by
        congr 1
        field_simp
    _ = _ := Real.sqrt_mul (div_nonneg hdy.le hdx.le) _

/-- **Off-diagonal bound at even times.**
`p_{2n}(x, y) ≤ √(deg y / deg x) √(p_{2n}(x, x) p_{2n}(y, y))`. -/
theorem heat_even_le_sqrt_mul [Infinite V] (hG : G.Connected) (n : ℕ) (x y : V) :
    heat G (n + n) x y ≤
      Real.sqrt ((G.degree y : ℝ) / G.degree x) *
        Real.sqrt (heat G (n + n) x x * heat G (n + n) y y) :=
  heat_add_le_sqrt_mul hG n n x y

/-- **Off-diagonal bound at odd times.**
`p_{2n+1}(x, y) ≤ √(deg y / deg x) √(p_{2n}(x, x) p_{2n}(y, y))`. -/
theorem heat_odd_le_sqrt_mul [Infinite V] (hG : G.Connected) (n : ℕ) (x y : V) :
    heat G (n + n + 1) x y ≤
      Real.sqrt ((G.degree y : ℝ) / G.degree x) *
        Real.sqrt (heat G (n + n) x x * heat G (n + n) y y) := by
  have h := heat_add_le_sqrt_mul hG n (n + 1) x y
  rw [show n + (n + 1) = n + n + 1 by omega] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_left (heat_even_le_of_le hG y (Nat.le_succ n))
    (heat_nonneg _ _ _)

/-- On a graph of degree at most `Δ`, `p_{2n}(x, y) ≤ √Δ √(p_{2n}(x, x) p_{2n}(y, y))`. -/
theorem heat_even_le_sqrt_degree_mul [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) (n : ℕ) (x y : V) :
    heat G (n + n) x y ≤
      Real.sqrt Δ * Real.sqrt (heat G (n + n) x x * heat G (n + n) y y) := by
  refine (heat_even_le_sqrt_mul hG n x y).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
  have hdx : (1 : ℝ) ≤ G.degree x := by exact_mod_cast degree_pos hG x
  have hdy : (G.degree y : ℝ) ≤ Δ := by exact_mod_cast hΔ y
  calc (G.degree y : ℝ) / G.degree x ≤ G.degree y := div_le_self (Nat.cast_nonneg _) hdx
    _ ≤ Δ := hdy

/-- On a graph of degree at most `Δ`, `p_{2n+1}(x, y) ≤ √Δ √(p_{2n}(x, x) p_{2n}(y, y))`. -/
theorem heat_odd_le_sqrt_degree_mul [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) (n : ℕ) (x y : V) :
    heat G (n + n + 1) x y ≤
      Real.sqrt Δ * Real.sqrt (heat G (n + n) x x * heat G (n + n) y y) := by
  refine (heat_odd_le_sqrt_mul hG n x y).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
  have hdx : (1 : ℝ) ≤ G.degree x := by exact_mod_cast degree_pos hG x
  have hdy : (G.degree y : ℝ) ≤ Δ := by exact_mod_cast hΔ y
  calc (G.degree y : ℝ) / G.degree x ≤ G.degree y := div_le_self (Nat.cast_nonneg _) hdx
    _ ≤ Δ := hdy

end Rigidity.Green

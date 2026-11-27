import Rigidity.Proofs.Green.ClusterGreenUpperBound

/-!
# Gaussian-type off-diagonal bounds for the transition probabilities

On a graph with degrees at most `Δ`, two upper bounds on `p_n(x, y)` are available at the times
`n ≥ N₀` at least the distance `r = dist(x, y)`: the domination `p_n(x, y) ≤ K n^{-γ}` coming
from Faber-Krahn inequalities around the pole, and the Carne-Varopoulos bound
`p_n(x, y) ≤ 2 √Δ e^{-r²/(2n)}`. Their geometric mean with weights `1 - t` and `t`, `t ∈ [0, 1]`,
is a bound of Gaussian type,

  `p_n(x, y) ≤ K^{1-t} (2 √Δ)^t n^{-γ(1-t)} e^{-t r²/(2n)}`,

and it holds at every time `n ≥ max N₀ 1`, since `p_n(x, y) = 0` when `n < r`.

On the infinite cluster, under `ClusterFaberKrahn d p D η`, this gives almost surely on
`{y ∈ C_∞}`: for every `t ∈ [0, 1]` there are `K` and `N` with

  `p_n(x, y) ≤ K n^{-(D/2)(1-η)(1-t)} e^{-t |x - y|²/(2n)}`  for all `x ∈ C_∞` and `n ≥ N`,

`|·|` the Euclidean norm. This is the Gaussian upper bound of Barlow (Dario-Gu, Theorem 4, in
the regime `|x - y| ≤ n`) with the on-diagonal exponent `d/2` replaced by `(D/2)(1-η)(1-t)` and
the Gaussian constant by `2/t`, for the discrete-time simple random walk.
-/

open MeasureTheory LatticeProb.Percolation LatticeProb.Graph
open scoped Classical

namespace Rigidity.Green

section General

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The constant of a transition bound `K n^{-γ}` is nonnegative. -/
theorem nonneg_of_heatDominated {y : V} {N₀ : ℕ} {K γ : ℝ}
    (h : HeatDominated G y N₀ fun n => K * (n : ℝ) ^ (-γ)) : 0 ≤ K := by
  have h1 := h y (N₀ + 1) (by omega) (by rw [SimpleGraph.dist_self]; omega)
  have h2 : (0 : ℝ) < ((N₀ + 1 : ℕ) : ℝ) ^ (-γ) := Real.rpow_pos_of_pos (by positivity) _
  by_contra hneg
  have : K * ((N₀ + 1 : ℕ) : ℝ) ^ (-γ) < 0 := mul_neg_of_neg_of_pos (by linarith) h2
  linarith [heat_nonneg (G := G) (N₀ + 1) y y]

/-- The Carne-Varopoulos bound on a graph of degree at most `Δ`:
`p_n(x, y) ≤ 2 √Δ e^{-r²/(2n)}` for `n ≥ 1`. -/
theorem heat_le_two_sqrt_mul_exp [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) (x y : V) {n : ℕ} (hn1 : 1 ≤ n) :
    heat G n x y ≤ 2 * Real.sqrt Δ * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by
  refine (heat_le_carneVaropoulos G (fun v => degree_pos hG v) x y n hn1).trans ?_
  have hdx : (1 : ℝ) ≤ G.degree x := by exact_mod_cast degree_pos hG x
  have hdy : (G.degree y : ℝ) ≤ Δ := by exact_mod_cast hΔ y
  have hsq : Real.sqrt ((G.degree y : ℝ) / G.degree x) ≤ Real.sqrt Δ :=
    Real.sqrt_le_sqrt ((div_le_self (Nat.cast_nonneg _) hdx).trans hdy)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
    (Real.exp_nonneg _)

/-- **Gaussian-type off-diagonal bound.** If `p_n(x, y) ≤ K n^{-γ}` for `n ≥ N₀` at least the
distance, then for `t ∈ [0, 1]` and every time `n ≥ max N₀ 1`,
`p_n(x, y) ≤ K^{1-t} (2 √Δ)^t n^{-γ(1-t)} e^{-t r²/(2n)}`. -/
theorem heat_le_rpow_mul_exp_of_heatDominated [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {y : V} {N₀ : ℕ} {K γ : ℝ}
    (h : HeatDominated G y N₀ fun n => K * (n : ℝ) ^ (-γ)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : V) {n : ℕ} (hN : N₀ ≤ n) (hn1 : 1 ≤ n) :
    heat G n x y ≤
      K ^ (1 - t) * (2 * Real.sqrt Δ) ^ t * (n : ℝ) ^ (-(γ * (1 - t))) *
        Real.exp (-(t * (G.dist x y : ℝ) ^ 2 / (2 * n))) := by
  have hK := nonneg_of_heatDominated h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hS : 0 ≤ 2 * Real.sqrt Δ := by positivity
  by_cases hxn : G.dist x y ≤ n
  swap
  · rw [heat_eq_zero_of_lt_dist (by omega)]
    have h1 : 0 ≤ K ^ (1 - t) := Real.rpow_nonneg hK _
    have h2 : 0 ≤ (2 * Real.sqrt Δ) ^ t := Real.rpow_nonneg hS _
    have h3 : 0 ≤ (n : ℝ) ^ (-(γ * (1 - t))) := Real.rpow_nonneg hn0.le _
    have h4 := Real.exp_nonneg (-(t * (G.dist x y : ℝ) ^ 2 / (2 * n)))
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have ha : 0 ≤ heat G n x y := heat_nonneg _ _ _
  have hdom : heat G n x y ≤ K * (n : ℝ) ^ (-γ) := h x n hN hxn
  have hcv := heat_le_two_sqrt_mul_exp hG hΔ x y hn1
  have h1t : (1 - t) + t = 1 := by ring
  have hsplit : heat G n x y = heat G n x y ^ (1 - t) * heat G n x y ^ t := by
    rw [← Real.rpow_add' ha (by rw [h1t]; norm_num), h1t, Real.rpow_one]
  have hKn : 0 ≤ K * (n : ℝ) ^ (-γ) := mul_nonneg hK (Real.rpow_nonneg hn0.le _)
  calc heat G n x y = heat G n x y ^ (1 - t) * heat G n x y ^ t := hsplit
    _ ≤ (K * (n : ℝ) ^ (-γ)) ^ (1 - t) *
          (2 * Real.sqrt Δ * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n))) ^ t :=
        mul_le_mul (Real.rpow_le_rpow ha hdom (by linarith)) (Real.rpow_le_rpow ha hcv ht0)
          (Real.rpow_nonneg ha _) (Real.rpow_nonneg hKn _)
    _ = K ^ (1 - t) * (2 * Real.sqrt Δ) ^ t * (n : ℝ) ^ (-(γ * (1 - t))) *
          Real.exp (-(t * (G.dist x y : ℝ) ^ 2 / (2 * n))) := by
        rw [Real.mul_rpow hK (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le,
          Real.mul_rpow hS (Real.exp_nonneg _), ← Real.exp_mul,
          show -γ * (1 - t) = -(γ * (1 - t)) by ring,
          show -((G.dist x y : ℝ) ^ 2) / (2 * n) * t = -(t * (G.dist x y : ℝ) ^ 2 / (2 * n)) by
            ring]
        ring

/-- **Gaussian-type bound from Faber-Krahn inequalities on growing balls.** If the balls of
radius `R ≥ R₀` around `y` satisfy the Faber-Krahn inequality of dimension `D` with constant
`a₀ R^{-η}`, then for every `t ∈ [0, 1]` there is `K` with
`p_n(x, y) ≤ K n^{-(D/2)(1-η)(1-t)} e^{-t r²/(2n)}` for all `x` and `n ≥ max R₀ 2`. -/
theorem heat_le_rpow_mul_exp_of_faberKrahn_balls [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {D a₀ η : ℝ} (hD : 0 < D) (ha₀ : 0 < a₀) {R₀ : ℕ} (y : V)
    (hFK : ∀ R : ℕ, R₀ ≤ R → FaberKrahnOn G {v | G.dist y v ≤ R} D (a₀ * (R : ℝ) ^ (-η)))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : V) (n : ℕ), max R₀ 2 ≤ n →
      heat G n x y ≤ K * (n : ℝ) ^ (-(D / 2 * (1 - η) * (1 - t))) *
        Real.exp (-(t * (G.dist x y : ℝ) ^ 2 / (2 * n))) := by
  obtain ⟨K₀, hK₀⟩ := heatDominated_of_faberKrahn_balls hG hΔ hD ha₀ y hFK
  refine ⟨K₀ ^ (1 - t) * (2 * Real.sqrt Δ) ^ t,
    mul_nonneg (Real.rpow_nonneg (nonneg_of_heatDominated hK₀) _)
      (Real.rpow_nonneg (by positivity) _), fun x n hn => ?_⟩
  exact heat_le_rpow_mul_exp_of_heatDominated hG hΔ hK₀ ht0 ht1 x hn (by omega)

end General

variable {d : ℕ}

/-- **Gaussian-type bound on the infinite cluster.** Under `ClusterFaberKrahn d p D η`: for each
pole `y`, almost surely on `{y ∈ C_∞}`, for every `t ∈ [0, 1]` there are `K` and `N` with
`p_n(x, y) ≤ K n^{-(D/2)(1-η)(1-t)} e^{-t |x - y|²/(2n)}` for every cluster vertex `x` and every
time `n ≥ N`. -/
theorem clusterHeat_le_of_clusterFaberKrahn [NeZero d] {p : unitInterval} {D η : ℝ}
    (hD : 0 < D) (hFK : ClusterFaberKrahn d p D η) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
          ∀ (x : uniqueInfiniteComponent h) (n : ℕ), N ≤ n →
            heat (componentGraph (uniqueInfiniteComponent h)) n x ⟨y, hy⟩ ≤
              K * (n : ℝ) ^ (-(D / 2 * (1 - η) * (1 - t))) *
                Real.exp (-(t * ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ 2 /
                  (2 * n))) := by
  filter_upwards [hFK y] with ω hω
  intro h hy t ht0 ht1
  obtain ⟨a₀, ha₀, R₀, hR⟩ := hω h hy
  set C := uniqueInfiniteComponent h
  letI : Infinite C := Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)
  obtain ⟨K, hK, hKb⟩ := heat_le_rpow_mul_exp_of_faberKrahn_balls C.connected_toSimpleGraph
    (componentGraph_degree_le C) hD ha₀ ⟨y, hy⟩ hR ht0 ht1
  refine ⟨K, max R₀ 2, hK, fun x n hn => (hKb x n hn).trans ?_⟩
  have hn0 : (0 : ℝ) < 2 * n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right R₀ 2) hn
    linarith
  have hdist := norm_sub_le_dist C x ⟨y, hy⟩
  have hsq : ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ 2 ≤
      ((componentGraph C).dist x ⟨y, hy⟩ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hexp : Real.exp (-(t * ((componentGraph C).dist x ⟨y, hy⟩ : ℝ) ^ 2 / (2 * n))) ≤
      Real.exp (-(t * ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ 2 /
        (2 * n))) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    exact (div_le_div_iff_of_pos_right hn0).2 (mul_le_mul_of_nonneg_left hsq ht0)
  have hpre : 0 ≤ K * (n : ℝ) ^ (-(D / 2 * (1 - η) * (1 - t))) :=
    mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact mul_le_mul_of_nonneg_left hexp hpre

end Rigidity.Green

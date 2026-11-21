import Rigidity.Proofs.Green.ClusterHeatKernel

/-!
# Global polynomial bounds on the Green function

Under a transition bound `p_n(x, y) ≤ K n^{-γ}` at the times `n ≥ N₀` at least the distance, with
`γ > 1`, the bound holds at every time `n ≥ N₀` (the walk cannot reach the pole before the
distance), so the Green function is bounded by `N₀ + ∑_{n ≥ N₀} K n^{-γ}`. Together with the
decay `g(x) ≤ C r^{2-2γ+δ}` at distance `r ≥ max N₀ 1` of `GreenUpperBound.lean`, this gives a
bound at every vertex,

  `g(x) ≤ C (1 + r)^{2 - 2γ + δ}`  when `2 - 2γ + δ ≤ 0`.

On the infinite cluster, under `ClusterFaberKrahn d p D η` with `(D/2)(1 - η) > 1`, almost surely
on `{y ∈ C_∞}`, every Green column with pole `y` in dimension `d ≥ 3` satisfies, for every
`δ > 0`, `0 ≤ g(x) ≤ C (1 + |x - y|)^{2 - D(1-η) + δ}` at every vertex `x` of the cluster.
-/

open MeasureTheory LatticeProb.Percolation LatticeProb.Graph
open scoped Classical

namespace Rigidity.Green

section General

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- Past time `N₀` a transition bound into the pole holds from every starting point. -/
theorem heat_le_of_heatDominated {y : V} {N₀ : ℕ} {K γ : ℝ}
    (h : HeatDominated G y N₀ fun n => K * (n : ℝ) ^ (-γ)) (x : V) {n : ℕ} (hn : N₀ ≤ n) :
    heat G n x y ≤ K * (n : ℝ) ^ (-γ) := by
  by_cases hxn : G.dist x y ≤ n
  · exact h x n hn hxn
  · rw [heat_eq_zero_of_lt_dist (by omega)]
    exact mul_nonneg (nonneg_of_heatDominated h) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The Green function is bounded by `N₀ + ∑_{k ≥ 0} K (k + N₀)^{-γ}`. -/
theorem heatGreen_le_of_heatDominated [Infinite V] (hG : G.Connected) {y : V} {N₀ : ℕ}
    {K γ : ℝ} (hγ : 1 < γ) (h : HeatDominated G y N₀ fun n => K * (n : ℝ) ^ (-γ)) (x : V) :
    heatGreen G y x ≤ N₀ + ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ) := by
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hb : Summable fun n : ℕ => K * (n : ℝ) ^ (-γ) := summable_rpow_mul K hγ
  have hs : Summable fun n => heat G n x y := summable_heat_of_heatDominated hb h x
  have hsplit : ∑ n ∈ Finset.range N₀, heat G n x y + ∑' k, heat G (k + N₀) x y =
      ∑' n, heat G n x y := hs.sum_add_tsum_nat_add N₀
  have h1 : ∑ n ∈ Finset.range N₀, heat G n x y ≤ N₀ := by
    have hle := Finset.sum_le_sum fun n (_ : n ∈ Finset.range N₀) => heat_le_one hdeg n x y
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hle
    exact hle
  have h2 : ∑' k, heat G (k + N₀) x y ≤ ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ) :=
    Summable.tsum_le_tsum (fun k => heat_le_of_heatDominated h x (by omega))
      ((summable_nat_add_iff (f := fun n => heat G n x y) N₀).2 hs)
      ((summable_nat_add_iff (f := fun n : ℕ => K * (n : ℝ) ^ (-γ)) N₀).2 hb)
  have hdy : (1 : ℝ) ≤ G.degree y := by exact_mod_cast hdeg y
  calc heatGreen G y x ≤ ∑' n, heat G n x y :=
        div_le_self (tsum_nonneg fun n => heat_nonneg n x y) hdy
    _ = ∑ n ∈ Finset.range N₀, heat G n x y + ∑' k, heat G (k + N₀) x y := hsplit.symm
    _ ≤ N₀ + ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ) := add_le_add h1 h2

/-- For `e ≤ 0` and `r ≥ 1`, `r^e ≤ 2^{-e} (1 + r)^e`. -/
theorem rpow_le_two_rpow_mul_one_add_rpow {e r : ℝ} (he : e ≤ 0) (hr : 1 ≤ r) :
    r ^ e ≤ (2 : ℝ) ^ (-e) * (1 + r) ^ e := by
  have hr0 : 0 < r := by linarith
  have h1 : r ^ e = (2 : ℝ) ^ (-e) * (2 * r) ^ e := by
    rw [Real.mul_rpow (by norm_num) hr0.le, ← mul_assoc, ← Real.rpow_add (by norm_num),
      neg_add_cancel, Real.rpow_zero, one_mul]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) he)
    (Real.rpow_nonneg (by norm_num) _)

/-- **Global Green function bound.** If `p_n(x, y) ≤ K n^{-γ}` for `n ≥ N₀` at least the
distance, with `γ > 1`, then for every `δ > 0` with `2 - 2γ + δ ≤ 0` there is `C` with
`g(x) ≤ C (1 + r)^{2 - 2γ + δ}` at every vertex `x`, `r` the distance to the pole. -/
theorem heatGreen_le_one_add_rpow_of_heatDominated [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {y : V} {N₀ : ℕ} {K γ : ℝ} (hγ : 1 < γ)
    (h : HeatDominated G y N₀ fun n => K * (n : ℝ) ^ (-γ)) {δ : ℝ} (hδ : 0 < δ)
    (he : 2 - 2 * γ + δ ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V,
      heatGreen G y x ≤ C * (1 + (G.dist x y : ℝ)) ^ (2 - 2 * γ + δ) := by
  obtain ⟨C, hC, hCb⟩ := heatGreen_le_rpow_of_heatDominated hG hΔ hγ h hδ
  have hK := nonneg_of_heatDominated h
  have hB : 0 ≤ (N₀ : ℝ) + ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ) :=
    add_nonneg (Nat.cast_nonneg _)
      (tsum_nonneg fun k => mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hC1 : 0 ≤ C * (2 : ℝ) ^ (-(2 - 2 * γ + δ)) :=
    mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hM : (0 : ℝ) < 1 + (max N₀ 1 : ℕ) := by positivity
  have hC2 : 0 ≤ ((N₀ : ℝ) + ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ)) *
      (1 + ((max N₀ 1 : ℕ) : ℝ)) ^ (-(2 - 2 * γ + δ)) :=
    mul_nonneg hB (Real.rpow_nonneg hM.le _)
  refine ⟨max (C * (2 : ℝ) ^ (-(2 - 2 * γ + δ)))
      (((N₀ : ℝ) + ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ)) *
        (1 + ((max N₀ 1 : ℕ) : ℝ)) ^ (-(2 - 2 * γ + δ))),
    le_max_of_le_left hC1, fun x => ?_⟩
  have hr0 : (0 : ℝ) ≤ G.dist x y := Nat.cast_nonneg _
  have hpow : 0 ≤ (1 + (G.dist x y : ℝ)) ^ (2 - 2 * γ + δ) := Real.rpow_nonneg (by linarith) _
  by_cases hfar : max N₀ 1 ≤ G.dist x y
  · have hr1 : (1 : ℝ) ≤ G.dist x y := by exact_mod_cast le_of_max_le_right hfar
    calc heatGreen G y x ≤ C * (G.dist x y : ℝ) ^ (2 - 2 * γ + δ) :=
          hCb x (le_of_max_le_left hfar) (le_of_max_le_right hfar)
      _ ≤ C * ((2 : ℝ) ^ (-(2 - 2 * γ + δ)) * (1 + (G.dist x y : ℝ)) ^ (2 - 2 * γ + δ)) :=
          mul_le_mul_of_nonneg_left (rpow_le_two_rpow_mul_one_add_rpow he hr1) hC
      _ = C * (2 : ℝ) ^ (-(2 - 2 * γ + δ)) * (1 + (G.dist x y : ℝ)) ^ (2 - 2 * γ + δ) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  · have hnear : (G.dist x y : ℝ) ≤ ((max N₀ 1 : ℕ) : ℝ) := by exact_mod_cast (not_le.1 hfar).le
    have hcancel : (1 + ((max N₀ 1 : ℕ) : ℝ)) ^ (-(2 - 2 * γ + δ)) *
        (1 + ((max N₀ 1 : ℕ) : ℝ)) ^ (2 - 2 * γ + δ) = 1 := by
      rw [← Real.rpow_add hM, neg_add_cancel, Real.rpow_zero]
    have hmono : (1 + ((max N₀ 1 : ℕ) : ℝ)) ^ (2 - 2 * γ + δ) ≤
        (1 + (G.dist x y : ℝ)) ^ (2 - 2 * γ + δ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) he
    calc heatGreen G y x ≤ (N₀ : ℝ) + ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ) :=
          heatGreen_le_of_heatDominated hG hγ h x
      _ = ((N₀ : ℝ) + ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ)) *
            (1 + ((max N₀ 1 : ℕ) : ℝ)) ^ (-(2 - 2 * γ + δ)) *
            (1 + ((max N₀ 1 : ℕ) : ℝ)) ^ (2 - 2 * γ + δ) := by
          rw [mul_assoc, hcancel, mul_one]
      _ ≤ ((N₀ : ℝ) + ∑' k : ℕ, K * ((k + N₀ : ℕ) : ℝ) ^ (-γ)) *
            (1 + ((max N₀ 1 : ℕ) : ℝ)) ^ (-(2 - 2 * γ + δ)) *
            (1 + (G.dist x y : ℝ)) ^ (2 - 2 * γ + δ) := mul_le_mul_of_nonneg_left hmono hC2
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

end General

variable {d : ℕ}

/-- **Global Green column bound on the infinite cluster, `d ≥ 3`.** Under
`ClusterFaberKrahn d p D η` with `(D/2)(1 - η) > 1`: for each pole `y`, almost surely on
`{y ∈ C_∞}`, every Green column `g` with pole `y` satisfies, for every `δ > 0`,
`0 ≤ g(x) ≤ K (1 + |x - y|)^{2 - D(1-η) + δ}` at every vertex `x` of the cluster. -/
theorem clusterGreenColumn_le_one_add_norm_of_clusterFaberKrahn [NeZero d] (hd : 3 ≤ d)
    (hd2 : 2 ≤ d) {p : unitInterval} {D η : ℝ} (hD : 0 < D) (hγ : 1 < D / 2 * (1 - η))
    (hFK : ClusterFaberKrahn d p D η) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ g : uniqueInfiniteComponent h → ℝ,
          IsGreenColumn d hd2 (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
            ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 ≤ K ∧ ∀ x : uniqueInfiniteComponent h,
              0 ≤ g x ∧ g x ≤
                K * (1 + ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖) ^
                  (2 - D * (1 - η) + δ) := by
  filter_upwards [hFK y] with ω hω
  intro h hy g hg δ hδ
  obtain ⟨a₀, ha₀, R₀, hR⟩ := hω h hy
  set C := uniqueInfiniteComponent h
  have hC := uniqueInfiniteComponent_infinite h
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  have hG := C.connected_toSimpleGraph
  obtain ⟨K₀, hK₀⟩ := heatDominated_of_faberKrahn_balls hG (componentGraph_degree_le C) hD ha₀
    ⟨y, hy⟩ hR
  have hgreen := isGreenColumn_heatGreen hd hd2 C hC ⟨y, hy⟩ (summable_rpow_mul K₀ hγ) hK₀
  have hg_eq := eq_of_isGreenColumn_of_three_le hd hd2 C hC hg hgreen
  set δ' := min δ (D * (1 - η) - 2)
  have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have he : 2 - 2 * (D / 2 * (1 - η)) + δ' ≤ 0 := by
    have := min_le_right δ (D * (1 - η) - 2)
    linarith
  obtain ⟨K, hK, hKb⟩ := heatGreen_le_one_add_rpow_of_heatDominated hG
    (componentGraph_degree_le C) hγ hK₀ hδ'0 he
  refine ⟨K, hK, fun x => ?_⟩
  rw [hg_eq]
  refine ⟨heatGreen_nonneg x, (hKb x).trans (mul_le_mul_of_nonneg_left ?_ hK)⟩
  have hdist : ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ≤
      ((componentGraph C).dist x ⟨y, hy⟩ : ℝ) := norm_sub_le_dist C x ⟨y, hy⟩
  have hz0 := norm_nonneg (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y)
  rw [show 2 - 2 * (D / 2 * (1 - η)) + δ' = 2 - D * (1 - η) + δ' by ring] at he ⊢
  calc (1 + ((componentGraph C).dist x ⟨y, hy⟩ : ℝ)) ^ (2 - D * (1 - η) + δ')
      ≤ (1 + ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖) ^
          (2 - D * (1 - η) + δ') :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) he
    _ ≤ (1 + ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖) ^
          (2 - D * (1 - η) + δ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end Rigidity.Green

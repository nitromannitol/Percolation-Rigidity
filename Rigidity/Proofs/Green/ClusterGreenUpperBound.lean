import Rigidity.Proofs.Green.GreenUpperBound
import Rigidity.Proofs.Green.ClusterFaberKrahn
import LatticeProb.Prob.Percolation.LatticeRadialTail

/-!
# Upper bounds on the Green function of the infinite cluster

Assume `ClusterFaberKrahn d p D η` with `(D/2)(1 - η) > 1`: for each pole `y`, almost surely the
graph balls of radius `R ≥ R₀` around `y` in the infinite cluster satisfy the Faber-Krahn
inequality of dimension `D` with constant `a₀ R^{-η}`. Then almost surely on `{y ∈ C_∞}`, for
every `δ > 0` there are `C` and `R₀` such that the Green function `g(·, y)` of the walk on the
cluster satisfies

  `0 ≤ g(x, y) ≤ C |x - y|^{2 - D(1-η) + δ}`  for every `x ∈ C_∞` with `|x - y| ≥ R₀`,

`|·|` the Euclidean norm. In dimension `d ≥ 3` this holds for every Green column in the sense of
`IsGreenColumn`, which is then unique and equal to `∑_n p_n(·, y) / deg y`.

For `D = d` this is the upper half of the Green function asymptotics of Dario-Gu, Theorem 2
(1.10), `g(x, y) ≤ C |x - y|^{2-d}`, with the loss `|x - y|^{dη + δ}`. The Euclidean distance is
at most the graph distance in the cluster, and the exponent is negative, so the graph-distance
bound of `GreenUpperBound.lean` transfers to the Euclidean distance.
-/

open MeasureTheory LatticeProb.Percolation LatticeProb.Graph
open scoped Classical

namespace Rigidity.Green

variable {d : ℕ}

/-- Along a walk in a component, the `ℓ¹` distance grows by at most one per step. -/
theorem sum_abs_sub_le_length {ω : Configuration d} {C : OpenComponent ω} :
    ∀ {a b : C} (q : (componentGraph C).Walk a b),
      ∑ i, |b.val i - a.val i| ≤ q.length := by
  intro a b q
  induction q with
  | nil => simp
  | cons hadj q ih =>
      rename_i u v w
      have hadj' : (openGraph ω).Adj u.val v.val := hadj
      have h1 : latticeL1Dist u.val v.val = 1 := lattice_adj_iff_l1Dist.mp (openGraph_le ω hadj')
      have h2 : ∑ i, |w.val i - u.val i| ≤ ∑ i, (|w.val i - v.val i| + |v.val i - u.val i|) :=
        Finset.sum_le_sum fun i _ => abs_sub_le _ _ _
      have h3 : ∑ i, |v.val i - u.val i| = 1 := by
        rw [← h1, latticeL1Dist]
        exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
      rw [Finset.sum_add_distrib, h3] at h2
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- The Euclidean distance between two vertices of a component is at most their graph distance
in the component. -/
theorem norm_sub_le_dist {ω : Configuration d} (C : OpenComponent ω) (x y : C) :
    ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val‖ ≤
      (componentGraph C).dist x y := by
  obtain ⟨q, hq⟩ := C.connected_toSimpleGraph.exists_walk_length_eq_dist y x
  have h := sum_abs_sub_le_length q
  rw [hq] at h
  have hR : ∑ i, |((x.val i - y.val i : ℤ) : ℝ)| ≤ (componentGraph C).dist x y := by
    have h' : ((∑ i, |x.val i - y.val i| : ℤ) : ℝ) ≤ (((componentGraph C).dist y x : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    rwa [SimpleGraph.dist_comm] at h'
  refine le_trans ?_ hR
  have hcoord : ∀ j, ‖latticeEuclideanEmbedding (x.val - y.val) j‖ =
      |((x.val j - y.val j : ℤ) : ℝ)| := fun j => by
    rw [Real.norm_eq_abs]
    rfl
  rw [← latticeEuclideanEmbedding_sub, EuclideanSpace.norm_eq]
  simp only [hcoord]
  calc √(∑ j, |((x.val j - y.val j : ℤ) : ℝ)| ^ 2)
      ≤ √((∑ j, |((x.val j - y.val j : ℤ) : ℝ)|) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _)
    _ = ∑ j, |((x.val j - y.val j : ℤ) : ℝ)| :=
        Real.sqrt_sq (Finset.sum_nonneg fun j _ => abs_nonneg _)

/-- On one infinite component: Faber-Krahn inequalities on the balls around `y` give the
Euclidean Green function bound `g(x, y) ≤ C |x - y|^{2 - D(1-η) + δ}` for `|x - y| ≥ R₀`. -/
theorem heatGreen_le_norm_rpow_of_faberKrahn_balls {ω : Configuration d} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (y : C) {D a₀ η : ℝ} (hD : 0 < D) (ha₀ : 0 < a₀) {R₀ : ℕ}
    (hFK : ∀ R : ℕ, R₀ ≤ R →
      FaberKrahnOn (componentGraph C) {v | (componentGraph C).dist y v ≤ R} D
        (a₀ * (R : ℝ) ^ (-η)))
    (hγ : 1 < D / 2 * (1 - η)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 < R ∧ ∀ x : C,
      R ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val‖ →
        heatGreen (componentGraph C) y x ≤
          K * ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val‖ ^
            (2 - D * (1 - η) + δ) := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  set δ' := min δ ((D * (1 - η) - 2) / 2) with hδ'
  have hDη : 2 < D * (1 - η) := by linarith
  have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hneg : 2 - D * (1 - η) + δ' ≤ 0 := by
    have := min_le_right δ ((D * (1 - η) - 2) / 2)
    linarith
  obtain ⟨K, hK, hKb⟩ := heatGreen_le_rpow_of_faberKrahn_balls C.connected_toSimpleGraph
    (componentGraph_degree_le C) hD ha₀ y hFK hγ hδ'0
  refine ⟨K, ((max R₀ 2 : ℕ) : ℝ), hK, by positivity, fun x hx => ?_⟩
  set z := ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val‖ with hz
  have hdist := norm_sub_le_dist C x y
  have h2 : (2 : ℝ) ≤ ((max R₀ 2 : ℕ) : ℝ) := by exact_mod_cast le_max_right R₀ 2
  have hz1 : 1 ≤ z := by linarith
  have hz0 : 0 < z := by linarith
  have hxd : max R₀ 2 ≤ (componentGraph C).dist x y := by exact_mod_cast hx.trans hdist
  refine (hKb x hxd).trans (mul_le_mul_of_nonneg_left ?_ hK)
  calc ((componentGraph C).dist x y : ℝ) ^ (2 - D * (1 - η) + δ')
      ≤ z ^ (2 - D * (1 - η) + δ') := Real.rpow_le_rpow_of_nonpos hz0 hdist hneg
    _ ≤ z ^ (2 - D * (1 - η) + δ) := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)

/-- **Green function upper bound on the infinite cluster.** Under `ClusterFaberKrahn d p D η`
with `(D/2)(1 - η) > 1`: for each pole `y`, almost surely on `{y ∈ C_∞}`, for every `δ > 0`
there are `K` and `R` with `g(x, y) ≤ K |x - y|^{2 - D(1-η) + δ}` for every cluster vertex `x`
with `|x - y| ≥ R`, where `g(·, y) = ∑_n p_n(·, y) / deg y`. -/
theorem clusterHeatGreen_le_of_clusterFaberKrahn [NeZero d] {p : unitInterval} {D η : ℝ}
    (hD : 0 < D) (hγ : 1 < D / 2 * (1 - η)) (hFK : ClusterFaberKrahn d p D η) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ δ : ℝ, 0 < δ → ∃ K R : ℝ, 0 ≤ K ∧ 0 < R ∧
          ∀ x : uniqueInfiniteComponent h,
            R ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ →
              heatGreen (componentGraph (uniqueInfiniteComponent h)) ⟨y, hy⟩ x ≤
                K * ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^
                  (2 - D * (1 - η) + δ) := by
  filter_upwards [hFK y] with ω hω
  intro h hy δ hδ
  obtain ⟨a₀, ha₀, R₀, hR⟩ := hω h hy
  exact heatGreen_le_norm_rpow_of_faberKrahn_balls _ (uniqueInfiniteComponent_infinite h)
    ⟨y, hy⟩ hD ha₀ hR hγ hδ

/-- **Green column upper bound on the infinite cluster, `d ≥ 3`.** Under
`ClusterFaberKrahn d p D η` with `(D/2)(1 - η) > 1`: for each pole `y`, almost surely on
`{y ∈ C_∞}`, every Green column `g` with pole `y` satisfies, for every `δ > 0`,
`0 ≤ g(x) ≤ K |x - y|^{2 - D(1-η) + δ}` for `|x - y| ≥ R`. -/
theorem clusterGreenColumn_le_of_clusterFaberKrahn [NeZero d] (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    {p : unitInterval} {D η : ℝ} (hD : 0 < D) (hγ : 1 < D / 2 * (1 - η))
    (hFK : ClusterFaberKrahn d p D η) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ g : uniqueInfiniteComponent h → ℝ,
          IsGreenColumn d hd2 (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
            ∀ δ : ℝ, 0 < δ → ∃ K R : ℝ, 0 ≤ K ∧ 0 < R ∧
              ∀ x : uniqueInfiniteComponent h,
                R ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ →
                  0 ≤ g x ∧ g x ≤
                    K * ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^
                      (2 - D * (1 - η) + δ) := by
  filter_upwards [hFK y] with ω hω
  intro h hy g hg δ hδ
  obtain ⟨a₀, ha₀, R₀, hR⟩ := hω h hy
  set C := uniqueInfiniteComponent h
  have hC := uniqueInfiniteComponent_infinite h
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  obtain ⟨K₀, hK₀⟩ := heatDominated_of_faberKrahn_balls C.connected_toSimpleGraph
    (componentGraph_degree_le C) hD ha₀ ⟨y, hy⟩ hR
  have hgreen := isGreenColumn_heatGreen hd hd2 C hC ⟨y, hy⟩ (summable_rpow_mul K₀ hγ) hK₀
  have hg_eq := eq_of_isGreenColumn_of_three_le hd hd2 C hC hg hgreen
  obtain ⟨K, R, hK, hR0, hb⟩ :=
    heatGreen_le_norm_rpow_of_faberKrahn_balls C hC ⟨y, hy⟩ hD ha₀ hR hγ hδ
  refine ⟨K, R, hK, hR0, fun x hx => ?_⟩
  rw [hg_eq]
  exact ⟨heatGreen_nonneg x, hb x hx⟩

end Rigidity.Green

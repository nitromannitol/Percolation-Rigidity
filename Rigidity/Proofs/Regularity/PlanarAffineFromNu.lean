import Rigidity.Proofs.Regularity.PlanarNuFlatnessAS

/-!
# Harmonic approximations of affine functions on the planar cluster from the maximizers of `ν`

The maximizer `v(·, □, ξ)` of `ν(□, ξ)` is harmonic on the interior of the cluster of `□`
(`planarNuMaximizer_spec`) and, by Lemma 5.8 of Armstrong and Dario (arXiv:1609.09431v2), its
coarsening is close to the affine function `x · ξ` on `□`. This gives the input of Step 3 of
Proposition 3.1 of Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1) for `k = 1`.

* `harmonicOnBall_of_clusterHarmonic`: a function harmonic on the interior of the cluster of a
  resolved cube `V`, minus a constant, is harmonic on `𝒞 ∩ B_R` when the vertices of `𝒞 ∩ B_R` lie
  in the cluster of `V` and in its interior;
* `componentBallL2_le_of_sums`: the normalized norm on `𝒞 ∩ B_R` from the sums of squares over
  the cluster of `V` of `v - [v]_𝒫` and of `[v]_𝒫 - x · ξ - c`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Proofs.Multiscale (affineFun finsetMean)
open scoped Classical

variable {ω : Configuration 2}

/-- **Harmonicity on a ball** from harmonicity on the interior of the cluster of a cube. -/
theorem harmonicOnBall_of_clusterHarmonic (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (C : OpenComponent ω) {v : ClusterFun ω V}
    (hv : v ∈ clusterHarmonic ω V) (c : ℝ) {R : ℝ}
    (hin : ∀ x : C, x ∈ componentEuclideanBall C 0 R →
      x.val ∈ clusterVertices ω V ∧ V.IsInterior x.val) :
    HarmonicOnBall C (fun x => clusterExtend ω V v x.val - c) R := by
  intro x hx _
  obtain ⟨hxV, hint⟩ := hin x hx
  rw [mem_clusterHarmonic] at hv
  have h0 := hv ⟨x.val, hxV⟩ hint
  rw [clusterLaplacianAt_apply] at h0
  rw [Rigidity.Proofs.S3.componentLaplacian_eq_sum_lattice C _ x.val x.2, ← Finset.sum_filter]
  have e1 : ∑ y : ↥(clusterVertices ω V), (if (openGraph ω).Adj x.val y.1 then
      v y - v ⟨x.val, hxV⟩ else 0) =
      ∑ y ∈ clusterVertices ω V, (if (openGraph ω).Adj x.val y then
        clusterExtend ω V v y - clusterExtend ω V v x.val else 0) := by
    rw [← Finset.sum_coe_sort (clusterVertices ω V)]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · rw [clusterExtend_apply_of_mem _ y.2, clusterExtend_apply_of_mem _ hxV]
    · rfl
  rw [e1, ← Finset.sum_filter] at h0
  have hset : (clusterVertices ω V).filter (fun y => (openGraph ω).Adj x.val y) =
      ((lattice 2).neighborFinset x.val).filter (fun y => (openGraph ω).Adj x.val y) := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨-, hy⟩
      exact ⟨openGraph_le ω hy, hy⟩
    · rintro ⟨-, hy⟩
      exact ⟨mem_clusterVertices_of_adj hP hV hxV hint hy, hy⟩
  rw [hset] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨-, hxy⟩ := Finset.mem_filter.1 hy
  have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hxy
  rw [extend_of_mem C _ hyC, extend_of_mem C _ x.2]
  ring

/-- **The normalized norm on the ball** from the sums of squares over the cluster of `V`. -/
theorem componentBallL2_le_of_sums {V : TriadicCube 2} (C : OpenComponent ω) (v : ClusterFun ω V)
    (q : Fin 2 → ℝ) (c : ℝ) {R F G κ' : ℝ} (hκ' : 0 < κ')
    (hin : ∀ x : C, x ∈ componentEuclideanBall C 0 R → x.val ∈ clusterVertices ω V)
    (hcard : κ' ≤ (componentEuclideanBall C 0 R).card)
    (hF : ∑ x ∈ clusterVertices ω V,
      (coarsen ω V v x - affineFun q x - c) ^ 2 ≤ F)
    (hG : ∑ x ∈ clusterVertices ω V, (clusterExtend ω V v x - coarsen ω V v x) ^ 2 ≤ G) :
    componentBallL2 C 0 R (fun x => (clusterExtend ω V v x.val - c) - componentSlope C q x) ≤
      Real.sqrt (2 * (F + G) / κ') := by
  unfold componentBallL2
  apply Real.sqrt_le_sqrt
  have hn : (0 : ℝ) < (componentEuclideanBall C 0 R).card := lt_of_lt_of_le hκ' hcard
  rw [div_le_div_iff₀ hn hκ']
  have hpt : ∀ x : ℝ, ∀ y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
    nlinarith [sq_nonneg (x - y)]
  have hsum : ∑ x ∈ componentEuclideanBall C 0 R,
      ((clusterExtend ω V v x.val - c) - componentSlope C q x) ^ 2 ≤ 2 * (F + G) := by
    calc ∑ x ∈ componentEuclideanBall C 0 R,
          ((clusterExtend ω V v x.val - c) - componentSlope C q x) ^ 2
        = ∑ z ∈ (componentEuclideanBall C 0 R).map (Function.Embedding.subtype _),
            ((clusterExtend ω V v z - coarsen ω V v z) +
              (coarsen ω V v z - affineFun q z - c)) ^ 2 := by
          rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Function.Embedding.coe_subtype, componentSlope, affineFun]
          ring
      _ ≤ ∑ z ∈ (componentEuclideanBall C 0 R).map (Function.Embedding.subtype _),
            (2 * (clusterExtend ω V v z - coarsen ω V v z) ^ 2 +
              2 * (coarsen ω V v z - affineFun q z - c) ^ 2) :=
          Finset.sum_le_sum fun z _ => hpt _ _
      _ ≤ ∑ z ∈ clusterVertices ω V,
            (2 * (clusterExtend ω V v z - coarsen ω V v z) ^ 2 +
              2 * (coarsen ω V v z - affineFun q z - c) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_) fun _ _ _ => by positivity
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hz
          exact hin x hx
      _ = 2 * ∑ z ∈ clusterVertices ω V, (clusterExtend ω V v z - coarsen ω V v z) ^ 2 +
            2 * ∑ z ∈ clusterVertices ω V, (coarsen ω V v z - affineFun q z - c) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (F + G) := by linarith
  have hF0 : 0 ≤ F := le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) hF
  have hG0 : 0 ≤ G := le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) hG
  calc (∑ x ∈ componentEuclideanBall C 0 R,
        ((clusterExtend ω V v x.val - c) - componentSlope C q x) ^ 2) * κ'
      ≤ 2 * (F + G) * (componentEuclideanBall C 0 R).card :=
        mul_le_mul hsum hcard hκ'.le (by positivity)
    _ = 2 * (F + G) * (componentEuclideanBall C 0 R).card := rfl

end Rigidity.Proofs.Regularity

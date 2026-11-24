import Rigidity.Proofs.Cluster.GeneralFlatnessBound
import Rigidity.Proofs.Cluster.GeneralRestrictQuadCoarsen

/-!
# The multiscale vocabulary for the proof of Lemma 5.8, in every dimension

The multiscale Poincaré inequality (`Rigidity.Proofs.Multiscale`) is stated for the lattice points
`cube m z` of the triadic cube of scale `m` and index `z`, the spatial sums `gradSum` of the
gradient and the squared gradients `gradNormSq`; the subadditive quantities of Section 4 use the
triadic cubes, their subcubes `subcubesAt`, the pairings `latticeEdgePairing` and the magnitudes
`gradNormIn`. This file records the dictionary:

* the subcubes of scale `k ≤ m` of the cube of index `z` are the cubes of scale `k` with indices in
  `cube (m - k) z` (`subcubesAt_eq_image_general`, `sum_subcubesAt_eq_general`,
  `card_subcubesAt_eq_general`);
* `gradSum B u j` is the pairing of `eⱼ` with the gradient of `u` over the edges inside `B`
  (`gradSum_eq_latticeEdgePairing`);
* `gradNormSq A u x` is the squared magnitude `gradNormIn (nearestNeighborGraph d) A u x ^ 2`
  (`gradNormSq_eq_gradNormIn_sq_general`).

These are the general-dimensional forms of the corresponding facts of
`Rigidity.Percolation.subcubesAt_eq_image` and
`Rigidity.Percolation.coarsePairing_single_eq_cubeGradSum`.
-/

open LatticeProb LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The subcubes of scale `k ≤ m` of the cube of scale `m` and index `z` are the cubes of scale
`k` whose indices lie in the cube of scale `m - k` and index `z`. -/
theorem subcubesAt_eq_image_general {m k : ℕ} (hk : k ≤ m) (z : Vertex d) :
    (⟨m, z⟩ : TriadicCube d).subcubesAt k =
      (Rigidity.Proofs.Multiscale.cube (m - k) z).image fun j => (⟨k, j⟩ : TriadicCube d) := by
  ext V
  simp only [TriadicCube.subcubesAt, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(triadicCubeAt k x).index, ?_, ?_⟩
    · rw [← Rigidity.Proofs.Multiscale.pow_mul_mem_cube_iff hk]
      have hc : (fun i => 3 ^ k * (triadicCubeAt k x).index i) ∈ (triadicCubeAt k x).vertices := by
        intro i
        have hs : (triadicCubeAt k x).side = 3 ^ k := by
          rw [TriadicCube.side, scale_triadicCubeAt]
        rw [hs]
        simp only [sub_self, mul_zero, abs_zero]
        positivity
      have hsub := triadicCubeAt_subset (U := ⟨m, z⟩) hk
        ((TriadicCube.mem_toIntegerCube_vertices _ _).1 hx) hc
      exact (TriadicCube.mem_toIntegerCube_vertices _ _).2 hsub
    · exact TriadicCube.ext (scale_triadicCubeAt k x).symm rfl
  · rintro ⟨j, hj, rfl⟩
    have hj' := (Rigidity.Proofs.Multiscale.pow_mul_mem_cube_iff hk z j).2 hj
    refine ⟨fun i => 3 ^ k * j i, hj', ?_⟩
    refine TriadicCube.eq_of_mem_of_scale_eq (scale_triadicCubeAt k _) (mem_triadicCubeAt k _) ?_
    intro i
    change |2 * (3 ^ k * j i - (3 : ℤ) ^ k * j i)| < (3 : ℤ) ^ k
    simp only [sub_self, mul_zero, abs_zero]
    positivity

/-- A sum over the subcubes of scale `k ≤ m` is a sum over their indices. -/
theorem sum_subcubesAt_eq_general {β : Type*} [AddCommMonoid β] {m k : ℕ} (hk : k ≤ m)
    (z : Vertex d) (F : TriadicCube d → β) :
    ∑ V ∈ (⟨m, z⟩ : TriadicCube d).subcubesAt k, F V =
      ∑ j ∈ Rigidity.Proofs.Multiscale.cube (m - k) z, F ⟨k, j⟩ := by
  rw [subcubesAt_eq_image_general hk z, Finset.sum_image]
  intro a _ b _ h
  exact congrArg TriadicCube.index h

theorem card_subcubesAt_eq_general {m k : ℕ} (hk : k ≤ m) (z : Vertex d) :
    ((⟨m, z⟩ : TriadicCube d).subcubesAt k).card =
      (Rigidity.Proofs.Multiscale.centers m z k).card := by
  have h := sum_subcubesAt_eq_general (β := ℕ) hk z fun _ => 1
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h, Rigidity.Proofs.Multiscale.card_centers hk, Rigidity.Proofs.Multiscale.card_cube]

/-- The spatial sum of the gradient in the direction `eⱼ` is the pairing of `eⱼ` with the
gradient. -/
theorem gradSum_eq_latticeEdgePairing (B : Finset (Vertex d)) (u : Vertex d → ℝ) (j : Fin d) :
    Rigidity.Proofs.Multiscale.gradSum B u j =
      latticeEdgePairing B (fun _ => Pi.single j 1) u := by
  unfold Rigidity.Proofs.Multiscale.gradSum latticeEdgePairing
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
  simp only [Pi.single_eq_same, one_mul]
  rfl

/-- The squared gradient of the multiscale vocabulary is the squared magnitude of the gradient
for the nearest-neighbour graph. -/
theorem gradNormSq_eq_gradNormIn_sq_general (A : Finset (Vertex d)) (u : Vertex d → ℝ)
    (x : Vertex d) :
    Rigidity.Proofs.Multiscale.gradNormSq A u x =
      gradNormIn (nearestNeighborGraph d) A u x ^ 2 := by
  unfold Rigidity.Proofs.Multiscale.gradNormSq gradNormIn
  rw [Real.sq_sqrt (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun y _ => ite_nonneg (sq_nonneg _) le_rfl))]
  congr 1
  rw [← Finset.sum_filter]
  have hnb : A.filter (fun y => (nearestNeighborGraph d).Adj x y) =
      ((Finset.univ : Finset (Fin d)).image fun i => x + unit i).filter (· ∈ A) ∪
        ((Finset.univ : Finset (Fin d)).image fun i => x - unit i).filter (· ∈ A) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, i, h | h⟩
      · exact Or.inl ⟨⟨i, h.symm⟩, hy⟩
      · exact Or.inr ⟨⟨i, by rw [h]; abel⟩, hy⟩
    · rintro (⟨⟨i, rfl⟩, hy⟩ | ⟨⟨i, rfl⟩, hy⟩)
      · exact ⟨hy, i, Or.inl rfl⟩
      · exact ⟨hy, i, Or.inr (by abel)⟩
  have hdisj : Disjoint (((Finset.univ : Finset (Fin d)).image fun i => x + unit i).filter (· ∈ A))
      (((Finset.univ : Finset (Fin d)).image fun i => x - unit i).filter (· ∈ A)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hy1 hy2
    obtain ⟨⟨i, rfl⟩, -⟩ := hy1
    obtain ⟨⟨k, hk⟩, -⟩ := hy2
    have h := congrFun hk i
    by_cases hki : k = i
    · subst hki
      simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at h
      omega
    · simp [unit, hki] at h
  have hinj1 : Set.InjOn (fun i : Fin d => x + unit i) ↑(Finset.univ : Finset (Fin d)) :=
    fun i _ j _ h => by
      have := congrFun (add_left_cancel h) i
      by_contra hij
      simp [unit, Ne.symm hij] at this
  have hinj2 : Set.InjOn (fun i : Fin d => x - unit i) ↑(Finset.univ : Finset (Fin d)) :=
    fun i _ j _ h => by
      have := congrFun (sub_right_injective h) i
      by_contra hij
      simp [unit, Ne.symm hij] at this
  rw [hnb, Finset.sum_union hdisj, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_image hinj1, Finset.sum_image hinj2, ← Finset.sum_add_distrib]
  rfl

end Rigidity.Percolation

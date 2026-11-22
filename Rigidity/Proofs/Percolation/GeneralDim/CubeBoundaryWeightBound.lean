import Rigidity.Proofs.Percolation.GeneralDim.CubeBoundaryErrorBound
import Rigidity.Proofs.Percolation.GeneralDim.CubeExceptionalTail

/-!
# The boundary weight and the partition sizes

On the partition event, a vertex `z` lies in the crossing cluster of the partition cube of a face
vertex `x` of `U` only if `x` lies in the partition cube `□_𝒫(z)` of `z`; a face of `U` meets
`□_𝒫(z)` in at most `size(□_𝒫(z))^{d-1}` vertices, and only if the margin of `z` in `U` in the
direction of the face is smaller than `size(□_𝒫(z))`. Hence

`W_∂(z) ≤ ∑_i 2 size(□_𝒫(z))^{d-1} 1{margin_i(z) < size(□_𝒫(z))}`.

Together with the slice counts `|face| ≤ L^{d-1}` this is the input for the expectation of the
boundary error (Armstrong and Dario, proof of Lemma 4.5, (4.27)).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- A coordinate slice of an integer cube has at most `size^{d-1}` vertices. -/
theorem IntegerCube.card_filter_coord_eq_le (R : IntegerCube d) (i : Fin d) (t : ℤ) :
    (R.vertices.filter fun x => x i = t).card ≤ R.size ^ (d - 1) := by
  have hsub : R.vertices.filter (fun x => x i = t) ⊆ Fintype.piFinset fun j =>
      if j = i then ({t} : Finset ℤ) else Finset.Ico (R.corner j) (R.corner j + R.size) := by
    intro x hx
    obtain ⟨hxR, hxt⟩ := Finset.mem_filter.1 hx
    rw [Fintype.mem_piFinset]
    intro j
    split_ifs with hj
    · subst hj
      exact Finset.mem_singleton.2 hxt
    · exact (Fintype.mem_piFinset.1 hxR) j
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    if_pos rfl, Finset.card_singleton, one_mul]
  have h : ∀ j ∈ Finset.univ.erase i, (if j = i then ({t} : Finset ℤ)
      else Finset.Ico (R.corner j) (R.corner j + R.size)).card = R.size := by
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj), Int.card_Ico]
    omega
  rw [Finset.prod_congr rfl h, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

/-- A face of `U` meets a cube `Q` in at most `size(Q)^{d-1}` vertices. -/
theorem card_filter_mem_le {Q : TriadicCube d} {i : Fin d} {t : ℤ}
    (F : Finset (Vertex d)) (hF : ∀ x ∈ F, x i = t) :
    ((F.filter fun x => x ∈ Q.vertices).card : ℝ) ≤ ((3 : ℝ) ^ Q.scale) ^ (d - 1) := by
  have hsub : F.filter (fun x => x ∈ Q.vertices) ⊆
      Q.toIntegerCube.vertices.filter fun x => x i = t := by
    intro x hx
    obtain ⟨hxF, hxQ⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨(Q.mem_toIntegerCube_vertices x).2 hxQ, hF x hxF⟩
  have h := (Finset.card_le_card hsub).trans (Q.toIntegerCube.card_filter_coord_eq_le i t)
  have hs : (Q.toIntegerCube.size : ℝ) = (3 : ℝ) ^ Q.scale := by
    change ((3 ^ Q.scale : ℕ) : ℝ) = _
    push_cast
    rfl
  calc ((F.filter fun x => x ∈ Q.vertices).card : ℝ) ≤ ((Q.toIntegerCube.size ^ (d - 1) : ℕ) : ℝ) :=
        by exact_mod_cast h
    _ = ((3 : ℝ) ^ Q.scale) ^ (d - 1) := by push_cast; rw [hs]

/-- **The boundary weight is controlled by the partition size.** -/
theorem cubeBoundaryWeight_le {ω : Configuration d} (hP : PartitionEvent ω) (U : TriadicCube d)
    (z : Vertex d) :
    cubeBoundaryWeight ω U z ≤ ∑ i, 2 * ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (d - 1) *
      (if (U.margin z i : ℝ) < (3 : ℝ) ^ (partitionCube ω z).scale then 1 else 0) := by
  unfold cubeBoundaryWeight
  refine Finset.sum_le_sum fun i _ => ?_
  set Q := partitionCube ω z
  set s := (3 : ℝ) ^ Q.scale
  have hzQ := mem_partitionCube hP z
  -- a face vertex whose partition cube contains `z` in its crossing cluster lies in `Q`
  have hmemQ : ∀ x, z ∈ crossingClusterVertices ω (partitionCube ω x) → x ∈ Q.vertices := by
    intro x hx
    have hz := (partitionCube ω x).crossingCluster_subset ω (mem_crossingClusterVertices.1 hx)
    have heq : partitionCube ω z = partitionCube ω x := partitionCube_eq_of_mem hP hz
    rw [show Q = partitionCube ω x from heq]
    exact mem_partitionCube hP x
  have hface : ∀ (F : Finset (Vertex d)) (t : ℤ), (∀ x ∈ F, x i = t) →
      (∀ x ∈ F, x ∈ Q.vertices → (U.margin z i : ℝ) < s) →
      ∑ x ∈ F, (if z ∈ crossingClusterVertices ω (partitionCube ω x) then (1 : ℝ) else 0) ≤
        s ^ (d - 1) * (if (U.margin z i : ℝ) < s then 1 else 0) := by
    intro F t hF hm
    calc ∑ x ∈ F, (if z ∈ crossingClusterVertices ω (partitionCube ω x) then (1 : ℝ) else 0)
        ≤ ∑ x ∈ F, (if x ∈ Q.vertices then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun x _ => by
            by_cases h : z ∈ crossingClusterVertices ω (partitionCube ω x)
            · rw [if_pos h, if_pos (hmemQ x h)]
            · rw [if_neg h]
              split_ifs <;> norm_num
      _ = ((F.filter fun x => x ∈ Q.vertices).card : ℝ) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> simp
      _ ≤ s ^ (d - 1) * (if (U.margin z i : ℝ) < s then 1 else 0) := by
          by_cases hlt : (U.margin z i : ℝ) < s
          · rw [if_pos hlt, mul_one]
            exact card_filter_mem_le F hF
          · rw [if_neg hlt, mul_zero]
            have : F.filter (fun x => x ∈ Q.vertices) = ∅ := by
              refine Finset.filter_eq_empty_iff.2 fun x hx hxQ => hlt (hm x hx hxQ)
            rw [this, Finset.card_empty, Nat.cast_zero]
  have hclose : ∀ x ∈ Q.vertices, |x i - z i| < (3 : ℤ) ^ Q.scale := fun x hx =>
    TriadicCube.abs_coord_sub_lt_side hx hzQ i
  have hs_cast : ((3 : ℤ) ^ Q.scale : ℝ) = s := by push_cast; rfl
  have hup := hface (U.toIntegerCube.upperFace i) (U.toIntegerCube.corner i + 3 ^ U.scale - 1)
    (fun x hx => by
      have h := ((IntegerCube.mem_upperFace _ _ _).1 hx).2
      have hU : ((U.toIntegerCube.size : ℕ) : ℤ) = 3 ^ U.scale := by
        change ((3 ^ U.scale : ℕ) : ℤ) = _
        push_cast
        rfl
      rw [hU] at h
      omega)
    (fun x hx hxQ => by
      have h := ((IntegerCube.mem_upperFace _ _ _).1 hx).2
      have hU : ((U.toIntegerCube.size : ℕ) : ℤ) = 3 ^ U.scale := by
        change ((3 ^ U.scale : ℕ) : ℤ) = _
        push_cast
        rfl
      rw [hU] at h
      have hc := hclose x hxQ
      rw [abs_lt] at hc
      have hm : U.margin z i < (3 : ℤ) ^ Q.scale := by
        unfold TriadicCube.margin
        exact (min_le_right _ _).trans_lt (by omega)
      rw [← hs_cast]
      exact_mod_cast hm)
  have hlow := hface (U.toIntegerCube.lowerFace i) (U.toIntegerCube.corner i)
    (fun x hx => ((IntegerCube.mem_lowerFace _ _ _).1 hx).2)
    (fun x hx hxQ => by
      have h := ((IntegerCube.mem_lowerFace _ _ _).1 hx).2
      have hc := hclose x hxQ
      rw [abs_lt] at hc
      have hm : U.margin z i < (3 : ℤ) ^ Q.scale := by
        unfold TriadicCube.margin
        exact (min_le_left _ _).trans_lt (by omega)
      rw [← hs_cast]
      exact_mod_cast hm)
  calc _ ≤ s ^ (d - 1) * (if (U.margin z i : ℝ) < s then 1 else 0) +
        s ^ (d - 1) * (if (U.margin z i : ℝ) < s then 1 else 0) := add_le_add hup hlow
    _ = _ := by ring

end Rigidity.Percolation

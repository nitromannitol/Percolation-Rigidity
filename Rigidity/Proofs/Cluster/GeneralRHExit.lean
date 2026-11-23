import Rigidity.Proofs.Partition.Resolved
import Rigidity.Proofs.Cluster.Caccioppoli

/-!
# Vertices joined to far points are joined to their anchors

For the reverse Hölder inequality on a cube `□` of `ℤ^d` whose partition cubes are small, the
vertices of `□` joined by an open path to the outside of the triple `3□` must lie in the cluster of
the integer cube `3□`. Let `Q` be the partition cube of a vertex `x`, of side `s = 2r + 1`. If an
open path from `x` inside the box `x + [-r, r]^d` reaches a point with an open edge leaving the box,
then `x` is joined to the anchor of `Q` inside `Q.parent ∪ (x + [-r, r]^d)`
(`reachable_partitionAnchor_of_exit`): the box is a test cube of the well-connected cube `Q.parent`
(of side `3s`, meeting its three-quarter cube), the path travels a tenth of the side of
`Q.parent`, so it meets the component of the root of `Q.parent`, which contains the crossing
cluster of `Q` and hence the anchor. This is the second half of the proof of
`reachable_partitionAnchor_of_mem_crossingCluster`, with the exit path in place of the path to the
anchor.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- **A vertex joined to the outside of its box is joined to its anchor.** -/
theorem reachable_partitionAnchor_of_exit (hd : 0 < d) (hP : PartitionEvent ω) {x u v : Vertex d}
    (hxu : (openIn ω {y | ∀ i, |y i - x i| ≤ (partitionCube ω x).radius}).Reachable x u)
    (huv : (openGraph ω).Adj u v) (hv : ¬ ∀ i, |v i - x i| ≤ (partitionCube ω x).radius) :
    (openIn ω ((partitionCube ω x).parent.vertices ∪
      {y | ∀ i, |y i - x i| ≤ (partitionCube ω x).radius})).Reachable x (partitionAnchor ω x) := by
  have hPg := parent_partitionCube_mem_goodCubes hP x
  have h3 := three_le_scale_partitionCube hP x
  have hxQ := mem_partitionCube hP x
  have hanchor := partitionAnchor_mem_crossingCluster hP x
  set Q := partitionCube ω x with hQdef
  set box : Set (Vertex d) := {y | ∀ i, |y i - x i| ≤ Q.radius} with hboxdef
  obtain ⟨rP, hrP⟩ := (Q.parent.wellConnectedIn_threeQuarter_iff ω).1 hPg.2.1.2
  have hPs : 2 ≤ Q.parent.scale := hPg.2.1.1
  set N : ℕ := 3 ^ Q.scale
  have hNdef : N = 3 ^ Q.scale := rfl
  have hN : (N : ℤ) = Q.side := Q.natCast_three_pow_scale
  have hN27 : 27 ≤ N := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ Q.scale := Nat.pow_le_pow_right (by norm_num) h3
  have hsr := Q.side_eq_two_mul_radius_add_one
  have hPside : Q.parent.side = 3 * Q.side := Q.side_parent
  have hPsr := Q.parent.side_eq_two_mul_radius_add_one
  have hxP := (Q.parent.mem_vertices_iff_coord x).1 (Q.vertices_subset_parent hxQ)
  -- the displacement of the exit
  obtain ⟨i, hi⟩ : ∃ i, Q.parent.side ≤ 10 * |x i - u i| := by
    push Not at hv
    obtain ⟨i, hi⟩ := hv
    have h1 := Rigidity.Proofs.Cluster.abs_sub_le_one_of_openGraph_adj huv i
    have h2 := abs_sub_le (v i) (u i) (x i)
    refine ⟨i, ?_⟩
    rw [abs_sub_comm]
    rw [abs_sub_comm (u i) (v i)] at h1
    omega
  -- the box as an integer cube
  let c : Vertex d := fun j => x j - Q.radius
  let R : IntegerCube d := ⟨c, N⟩
  have hmemR (y : Vertex d) : y ∈ R.vertices ↔ ∀ j, c j ≤ y j ∧ y j < c j + (N : ℤ) :=
    IntegerCube.mem_vertices R y
  have hboxR : box = ↑R.vertices := by
    ext y
    rw [Finset.mem_coe, hmemR, hboxdef, Set.mem_setOf_eq]
    refine forall_congr' fun j => ?_
    rw [abs_le]
    change -Q.radius ≤ y j - x j ∧ y j - x j ≤ Q.radius ↔
      x j - Q.radius ≤ y j ∧ y j < x j - Q.radius + (N : ℤ)
    constructor <;> intro h <;> constructor <;> omega
  have hxR : x ∈ (↑R.vertices : Set (Vertex d)) := by
    rw [← hboxR, hboxdef, Set.mem_setOf_eq]
    intro j
    rw [sub_self, abs_zero]
    omega
  have hR : R ∈ Q.parent.testCubes Q.parent.threeQuarterCube.vertices := by
    refine ⟨by change Q.parent.side ≤ 10 * ((N : ℕ) : ℤ); omega,
      by change 2 * ((N : ℕ) : ℤ) ≤ Q.parent.side; omega, ?_⟩
    set K : ℕ := 3 * 3 ^ (Q.scale + 1) / 4 with hKdef
    have hpow : 3 ^ (Q.scale + 1) = 3 * N := by rw [pow_succ, hNdef]; ring
    have hK : (K : ℤ) = 3 * Q.parent.side / 4 := by rw [hKdef, hpow]; omega
    refine ⟨fun j => max (c j) (Q.parent.center j - (K : ℤ) / 2), ?_, ?_⟩
    · rw [hmemR]
      intro j
      have := hxP j
      refine ⟨le_max_left _ _, max_lt (by change x j - Q.radius < x j - Q.radius + (N : ℤ); omega)
        ?_⟩
      change Q.parent.center j - (K : ℤ) / 2 < x j - Q.radius + (N : ℤ)
      omega
    · rw [Finset.mem_coe, IntegerCube.mem_vertices]
      intro j
      have := hxP j
      change Q.parent.center j - (K : ℤ) / 2 ≤ max (c j) (Q.parent.center j - (K : ℤ) / 2) ∧
        max (c j) (Q.parent.center j - (K : ℤ) / 2) < Q.parent.center j - (K : ℤ) / 2 + (K : ℤ)
      refine ⟨le_max_right _ _, max_lt ?_ (by omega)⟩
      change x j - Q.radius < Q.parent.center j - (K : ℤ) / 2 + (K : ℤ)
      omega
  obtain ⟨-, hconn⟩ := hrP.2 R hR
  rw [hboxR] at hxu
  obtain ⟨z, -, hxz, hrz⟩ := hconn.exists_of_reachable hxR hxu hi
  have hchild := hrP.crossingCluster_child_subset hd hPs Q.digit
  rw [Q.parent_child] at hchild
  have hra : (openIn ω Q.parent.vertices).Reachable rP (partitionAnchor ω x) := hchild hanchor
  have hsub1 : (↑R.vertices : Set (Vertex d)) ⊆ Q.parent.vertices ∪ box :=
    fun y hy => Or.inr (hboxR ▸ hy)
  have hsub2 : (Q.parent.vertices : Set (Vertex d)) ⊆ Q.parent.vertices ∪ box :=
    fun y hy => Or.inl hy
  exact ((reachable_openIn_mono hsub1 hxz).trans (reachable_openIn_mono hsub2 hrz).symm).trans
    (reachable_openIn_mono hsub2 hra)

end Rigidity.Percolation

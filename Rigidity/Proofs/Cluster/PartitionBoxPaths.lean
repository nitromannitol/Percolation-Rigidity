import Rigidity.Proofs.Partition.Resolved

/-!
# Local paths of the partition into good cubes inside an integer cube

The local paths of the coarse-graining inequalities on the crossing cluster of a resolved triadic
cube (`reachable_partitionAnchor_of_mem_crossingCluster`) use only the box of the triadic cube.
Here the same argument is carried out inside an arbitrary integer cube `B`, such as the triple
`3□'` of a triadic cube `□'` (Armstrong and Dario, proof of Proposition 3.8), which is not
triadic in general. If the parent of the partition cube `Q` of `x` lies in `B` and `x` is joined
to the anchor of `Q` by an open path inside `B`, then it is joined to it inside
`B ∩ (Q.parent ∪ (x + Q_{s - 1}))`, where `s` is the side of `Q`: the path either stays within
distance `(s - 1)/2` of `x`, or travels that far inside the cube of side `s` around `x` moved into
`B`, which is a test cube of the well-connected cube `Q.parent`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- **Local paths inside an integer cube.** If the parent of the partition cube `Q` of `x` lies in
an integer cube `B` and `x` is joined to the anchor of `Q` inside `B`, then `x` is joined to it
inside `B ∩ (Q.parent ∪ (x + Q_{s - 1}))`, where `s` is the side of `Q`. -/
theorem reachable_partitionAnchor_of_reachable_box (hd : 0 < d) (hP : PartitionEvent ω)
    {x : Vertex d} {B : IntegerCube d}
    (hPB : (partitionCube ω x).parent.vertices ⊆ ↑B.vertices)
    (hxa : (openIn ω ↑B.vertices).Reachable x (partitionAnchor ω x)) :
    (openIn ω (↑B.vertices ∩ ((partitionCube ω x).parent.vertices ∪
      cubeAt x (3 ^ (partitionCube ω x).scale - 1)))).Reachable x (partitionAnchor ω x) := by
  have hPg := parent_partitionCube_mem_goodCubes hP x
  have h3 := three_le_scale_partitionCube hP x
  have hxQ := mem_partitionCube hP x
  have hanchor := partitionAnchor_mem_crossingCluster hP x
  set Q := partitionCube ω x with hQdef
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
  have hxB : x ∈ B.vertices := hPB (Q.vertices_subset_parent hxQ)
  have hxB' := (IntegerCube.mem_vertices B x).1 hxB
  -- the extent of `B` around the parent
  have hPr0 : 0 ≤ Q.parent.radius := by omega
  have hlowB : ∀ j, B.corner j ≤ Q.parent.center j - Q.parent.radius := fun j =>
    ((IntegerCube.mem_vertices B _).1 (hPB ((Q.parent.mem_vertices_iff_coord
      (fun j => Q.parent.center j - Q.parent.radius)).2 fun j =>
        ⟨le_rfl, show Q.parent.center j - Q.parent.radius ≤ Q.parent.center j + Q.parent.radius
          by omega⟩)) j).1
  have hupB : ∀ j, Q.parent.center j + Q.parent.radius < B.corner j + (B.size : ℤ) := fun j =>
    ((IntegerCube.mem_vertices B _).1 (hPB ((Q.parent.mem_vertices_iff_coord
      (fun j => Q.parent.center j + Q.parent.radius)).2 fun j =>
        ⟨show Q.parent.center j - Q.parent.radius ≤ Q.parent.center j + Q.parent.radius
          by omega, le_rfl⟩)) j).2
  -- the box of radius `r` around `x`
  set box : Set (Vertex d) := {y | ∀ i, |y i - x i| ≤ Q.radius} with hboxdef
  have hxbox : x ∈ box := by
    rw [hboxdef, Set.mem_setOf_eq]
    intro i
    rw [sub_self, abs_zero]
    omega
  have hboxcube : box ⊆ cubeAt x (N - 1) := by
    intro y hy i
    have h := hy i
    omega
  obtain ⟨u, hxu, hu⟩ := exists_reachable_inter_of_reachable_openIn hxa hxbox
  rcases hu with rfl | ⟨v, hv, huv⟩
  · refine reachable_openIn_mono ?_ hxu
    rintro y ⟨hyB, hyb⟩
    exact ⟨hyB, Or.inr (hboxcube hyb)⟩
  obtain ⟨i, hi⟩ : ∃ i, Q.parent.side ≤ 10 * |x i - u i| := by
    simp only [hboxdef, Set.mem_setOf_eq, not_forall, not_le] at hv
    obtain ⟨i, hi⟩ := hv
    have h1 := abs_sub_le_one_of_openIn_adj huv i
    have h2 := abs_sub_le (v i) (u i) (x i)
    refine ⟨i, ?_⟩
    rw [abs_sub_comm]
    omega
  -- the cube of side `s` around `x`, moved into `B`
  let c : Vertex d := fun j =>
    min (max (x j - Q.radius) (B.corner j)) (B.corner j + (B.size : ℤ) - (N : ℤ))
  let R : IntegerCube d := ⟨c, N⟩
  have hc (j : Fin d) : c j ≤ max (x j - Q.radius) (B.corner j) ∧
      c j ≤ B.corner j + (B.size : ℤ) - (N : ℤ) ∧
      (c j = max (x j - Q.radius) (B.corner j) ∨
        c j = B.corner j + (B.size : ℤ) - (N : ℤ)) ∧
      x j - Q.radius ≤ max (x j - Q.radius) (B.corner j) ∧
      B.corner j ≤ max (x j - Q.radius) (B.corner j) ∧
      (max (x j - Q.radius) (B.corner j) = x j - Q.radius ∨
        max (x j - Q.radius) (B.corner j) = B.corner j) :=
    ⟨min_le_left _ _, min_le_right _ _, min_choice _ _, le_max_left _ _, le_max_right _ _,
      max_choice _ _⟩
  have hmemR (y : Vertex d) : y ∈ R.vertices ↔ ∀ j, c j ≤ y j ∧ y j < c j + (N : ℤ) :=
    IntegerCube.mem_vertices R y
  have hRB : (↑R.vertices : Set (Vertex d)) ⊆ ↑B.vertices := by
    intro y hy
    rw [Finset.mem_coe, hmemR] at hy
    rw [Finset.mem_coe, IntegerCube.mem_vertices]
    intro j
    have := hc j
    have := hy j
    have := hlowB j
    have := hupB j
    omega
  have hboxR : ↑B.vertices ∩ box ⊆ ↑R.vertices := by
    rintro y ⟨hyB, hyb⟩
    rw [Finset.mem_coe, hmemR]
    intro j
    have h1 := (IntegerCube.mem_vertices B y).1 hyB j
    have h2 := abs_le.mp (hyb j)
    have := hc j
    have := hlowB j
    have := hupB j
    omega
  have hxR : x ∈ (↑R.vertices : Set (Vertex d)) := hboxR ⟨hxB, hxbox⟩
  have hRcube : (↑R.vertices : Set (Vertex d)) ⊆ cubeAt x (N - 1) := by
    intro y hy j
    have hx' := hxR
    rw [Finset.mem_coe, hmemR] at hy hx'
    rw [abs_le]
    have := hy j
    have := hx' j
    omega
  have hR : R ∈ Q.parent.testCubes Q.parent.threeQuarterCube.vertices := by
    refine ⟨by change Q.parent.side ≤ 10 * ((N : ℕ) : ℤ); omega,
      by change 2 * ((N : ℕ) : ℤ) ≤ Q.parent.side; omega, ?_⟩
    set K : ℕ := 3 * 3 ^ (Q.scale + 1) / 4 with hKdef
    have hpow : 3 ^ (Q.scale + 1) = 3 * N := by rw [pow_succ, hNdef]; ring
    have hK : (K : ℤ) = 3 * Q.parent.side / 4 := by rw [hKdef, hpow]; omega
    have hx' := hxR
    rw [Finset.mem_coe, hmemR] at hx'
    refine ⟨fun j => max (c j) (Q.parent.center j - (K : ℤ) / 2), ?_, ?_⟩
    · rw [hmemR]
      intro j
      have := hc j
      have := hx' j
      have := hxP j
      have := hlowB j
      have := hupB j
      refine ⟨le_max_left _ _, max_lt (by omega) ?_⟩
      omega
    · rw [Finset.mem_coe, IntegerCube.mem_vertices]
      intro j
      have := hc j
      have := hx' j
      have := hxP j
      have := hlowB j
      have := hupB j
      change Q.parent.center j - (K : ℤ) / 2 ≤ max (c j) (Q.parent.center j - (K : ℤ) / 2) ∧
        max (c j) (Q.parent.center j - (K : ℤ) / 2) < Q.parent.center j - (K : ℤ) / 2 + (K : ℤ)
      refine ⟨le_max_right _ _, max_lt ?_ (by omega)⟩
      omega
  obtain ⟨-, hconn⟩ := hrP.2 R hR
  obtain ⟨z, -, hxz, hrz⟩ := hconn.exists_of_reachable hxR (reachable_openIn_mono hboxR hxu) hi
  have hchild := hrP.crossingCluster_child_subset hd hPs Q.digit
  rw [Q.parent_child] at hchild
  have hra : (openIn ω Q.parent.vertices).Reachable rP (partitionAnchor ω x) := hchild hanchor
  have hsub1 : (↑R.vertices : Set (Vertex d)) ⊆
      ↑B.vertices ∩ (Q.parent.vertices ∪ cubeAt x (N - 1)) :=
    fun y hy => ⟨hRB hy, Or.inr (hRcube hy)⟩
  have hsub2 : Q.parent.vertices ⊆ ↑B.vertices ∩ (Q.parent.vertices ∪ cubeAt x (N - 1)) :=
    fun y hy => ⟨hPB hy, Or.inl hy⟩
  exact ((reachable_openIn_mono hsub1 hxz).trans (reachable_openIn_mono hsub2 hrz).symm).trans
    (reachable_openIn_mono hsub2 hra)

end Rigidity.Percolation

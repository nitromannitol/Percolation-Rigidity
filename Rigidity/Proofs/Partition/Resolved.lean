import Rigidity.Proofs.Partition.Paths

/-!
# Crossing clusters of cubes containing partition cubes

A triadic cube `U` containing the partition cube of one of its vertices is good, and so are all
cubes between them; hence the crossing cluster of that partition cube lies in `C_*(U)`, and the
crossing clusters of the children of `U` are nonempty and lie in `C_*(U)` (the first part of the
display after Definition 2.9 of Armstrong and Dario). Moreover `C_*(U)` lies in the infinite open
component of the anchors.

For the coarse-graining inequalities on `C_*(U)` (Armstrong and Dario, Lemmas 3.2 and 3.3) the
local paths must stay in `C_*(U)`. If the partition cube `Q` of `x ∈ U` is contained in `U`, then
`x ∈ C_*(U)` is joined to the anchor of `Q` inside `C_*(U) ∩ (Q.parent ∪ (x + Q_{s - 1}))`, where
`s` is the side of `Q`: the open path inside `U` from `x` to the anchor either stays within
distance `(s - 1) / 2` of `x`, or travels that far inside the cube of side `s` around `x`, moved
into `U`, which is a test cube of the well-connected cube `Q.parent`. The anchors of the partition
cubes of lattice neighbours of `U` are joined inside `C_*(U)` and the union of the two partition
cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The crossing cluster of a partition cube lies in the crossing cluster of each of its
ancestors. -/
theorem crossingCluster_partitionCube_subset_ancestor (hd : 0 < d) (hP : PartitionEvent ω)
    (x : Vertex d) (m : ℕ) :
    (partitionCube ω x).crossingCluster ω ⊆ ((partitionCube ω x).ancestor m).crossingCluster ω := by
  induction m with
  | zero => exact subset_rfl
  | succ m ih =>
    refine ih.trans ?_
    have hA := ancestor_partitionCube_mem_goodCubes hP x (m + 1)
    rw [TriadicCube.ancestor_succ] at hA ⊢
    obtain ⟨root, hroot⟩ :=
      (((partitionCube ω x).ancestor m).parent.wellConnectedIn_threeQuarter_iff ω).1 hA.2.1.2
    have h := hroot.crossingCluster_child_subset_crossingCluster hd hA.2.1.1
      ((partitionCube ω x).ancestor m).digit
    rwa [TriadicCube.parent_child] at h

/-- The crossing cluster of a partition cube lies in the crossing cluster of every triadic cube
containing it. -/
theorem crossingCluster_partitionCube_subset (hd : 0 < d) (hP : PartitionEvent ω)
    {x : Vertex d} {U : TriadicCube d} (hxU : x ∈ U.vertices)
    (hscale : (partitionCube ω x).scale ≤ U.scale) :
    (partitionCube ω x).crossingCluster ω ⊆ U.crossingCluster ω := by
  rw [TriadicCube.eq_ancestor_of_mem (mem_partitionCube hP x) hxU hscale]
  exact crossingCluster_partitionCube_subset_ancestor hd hP x _

/-- **Children of cubes containing partition cubes.** The crossing clusters of the children of
a triadic cube containing a partition cube are nonempty and lie in its crossing cluster. -/
theorem crossingCluster_child_of_partitionCube_le (hd : 0 < d) (hP : PartitionEvent ω)
    {x : Vertex d} {U : TriadicCube d} (hxU : x ∈ U.vertices)
    (hscale : (partitionCube ω x).scale ≤ U.scale) (digits : Fin d → Fin 3) :
    ((U.child digits).crossingCluster ω).Nonempty ∧
      (U.child digits).crossingCluster ω ⊆ U.crossingCluster ω := by
  have hU := mem_goodCubes_of_partitionCube_le hP hxU hscale
  obtain ⟨root, hroot⟩ := (U.wellConnectedIn_threeQuarter_iff ω).1 hU.2.1.2
  obtain ⟨croot, hcroot⟩ :=
    ((U.child digits).wellConnectedIn_threeQuarter_iff ω).1 (hU.2.2 digits).2
  exact ⟨⟨croot, hcroot.mem_crossingCluster⟩,
    hroot.crossingCluster_child_subset_crossingCluster hd hU.2.1.1 digits⟩

/-- The crossing cluster of a triadic cube containing a partition cube lies in the infinite open
component of the anchors. -/
theorem infinite_supp_of_mem_crossingCluster_of_le (hd : 0 < d) (hP : PartitionEvent ω)
    {x : Vertex d} {U : TriadicCube d} (hxU : x ∈ U.vertices)
    (hscale : (partitionCube ω x).scale ≤ U.scale) {v : Vertex d}
    (hv : v ∈ U.crossingCluster ω) : ((openGraph ω).connectedComponentMk v).supp.Infinite := by
  have hU := mem_goodCubes_of_partitionCube_le hP hxU hscale
  obtain ⟨root, hroot⟩ := (U.wellConnectedIn_threeQuarter_iff ω).1 hU.2.1.2
  have ha := crossingCluster_partitionCube_subset hd hP hxU hscale
    (partitionAnchor_mem_crossingCluster hP x)
  have hr : (openGraph ω).Reachable (partitionAnchor ω x) v := by
    refine (hroot.reachable_of_mem_crossingCluster hd hU.2.1.1 ha hv).mono ?_
    intro u w h
    exact h.1
  rw [show (openGraph ω).connectedComponentMk v =
      (openGraph ω).connectedComponentMk (partitionAnchor ω x) from
    (SimpleGraph.ConnectedComponent.eq.2 hr).symm]
  exact infinite_supp_partitionAnchor hd hP x

/-- Open paths inside a triadic cube started in its crossing cluster stay in the crossing
cluster. -/
theorem TriadicCube.reachable_crossingCluster_inter {Q : TriadicCube d} {S : Set (Vertex d)}
    {x y : Vertex d} (hx : x ∈ Q.crossingCluster ω)
    (h : (openIn ω (Q.vertices ∩ S)).Reachable x y) :
    (openIn ω (Q.crossingCluster ω ∩ S)).Reachable x y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab w ih =>
    have hb : b ∈ Q.crossingCluster ω := by
      obtain ⟨r, hr, hra⟩ := hx
      exact ⟨r, hr, hra.trans (SimpleGraph.Adj.reachable
        (G := openIn ω Q.vertices) ⟨hab.1, hab.2.1.1, hab.2.2.1⟩)⟩
    exact (SimpleGraph.Adj.reachable (G := openIn ω (Q.crossingCluster ω ∩ S))
      ⟨hab.1, ⟨hx, hab.2.1.2⟩, ⟨hb, hab.2.2.2⟩⟩).trans (ih hb)

/-- **Local paths inside a resolved cube.** If the partition cube `Q` of a vertex `x` of the
crossing cluster of a triadic cube `U` lies in `U`, then `x` is joined to the anchor of `Q`
inside `C_*(U) ∩ (Q.parent ∪ (x + Q_{s - 1}))`, where `s` is the side of `Q`. -/
theorem reachable_partitionAnchor_of_mem_crossingCluster (hd : 0 < d) (hP : PartitionEvent ω)
    {x : Vertex d} {U : TriadicCube d} (hxU : x ∈ U.vertices)
    (hscale : (partitionCube ω x).scale ≤ U.scale) (hx : x ∈ U.crossingCluster ω) :
    (openIn ω (U.crossingCluster ω ∩ ((partitionCube ω x).parent.vertices ∪
      cubeAt x (3 ^ (partitionCube ω x).scale - 1)))).Reachable x (partitionAnchor ω x) := by
  have hU := mem_goodCubes_of_partitionCube_le hP hxU hscale
  obtain ⟨rU, hrU⟩ := (U.wellConnectedIn_threeQuarter_iff ω).1 hU.2.1.2
  have hanchorU := crossingCluster_partitionCube_subset hd hP hxU hscale
    (partitionAnchor_mem_crossingCluster hP x)
  have hxa : (openIn ω U.vertices).Reachable x (partitionAnchor ω x) :=
    hrU.reachable_of_mem_crossingCluster hd hU.2.1.1 hx hanchorU
  apply TriadicCube.reachable_crossingCluster_inter hx
  have hPg := parent_partitionCube_mem_goodCubes hP x
  have h3 := three_le_scale_partitionCube hP x
  have hxQ := mem_partitionCube hP x
  have hanchor := partitionAnchor_mem_crossingCluster hP x
  set Q := partitionCube ω x with hQdef
  rcases Nat.eq_or_lt_of_le hscale with hQU | hQU
  · -- the partition cube is `U`
    have hQU' : Q = U := TriadicCube.eq_of_mem_of_scale_eq hQU hxQ hxU
    have hQroot := hrU
    rw [← hQU'] at hQroot hx
    have h := hQroot.reachable_of_mem_crossingCluster hd (by omega) hx hanchor
    refine reachable_openIn_mono ?_ h
    intro y hy
    refine ⟨hQU' ▸ hy, Or.inl (Q.vertices_subset_parent hy)⟩
  -- the parent of the partition cube lies in `U`
  obtain ⟨rP, hrP⟩ := (Q.parent.wellConnectedIn_threeQuarter_iff ω).1 hPg.2.1.2
  have hPs : 2 ≤ Q.parent.scale := hPg.2.1.1
  have hPU : Q.parent.vertices ⊆ U.vertices :=
    TriadicCube.vertices_subset_of_mem_of_scale_le (Q.vertices_subset_parent hxQ) hxU
      (by change Q.scale + 1 ≤ U.scale; omega)
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
  have hxU' := (U.mem_vertices_iff_coord x).1 hxU
  -- the extent of `U` around the parent
  have hPr0 : 0 ≤ Q.parent.radius := by omega
  have hlowU : ∀ j, U.center j - U.radius ≤ Q.parent.center j - Q.parent.radius := fun j =>
    ((U.mem_vertices_iff_coord _).1 (hPU ((Q.parent.mem_vertices_iff_coord
      (fun j => Q.parent.center j - Q.parent.radius)).2 fun j =>
        ⟨le_rfl, show Q.parent.center j - Q.parent.radius ≤ Q.parent.center j + Q.parent.radius
          by omega⟩)) j).1
  have hupU : ∀ j, Q.parent.center j + Q.parent.radius ≤ U.center j + U.radius := fun j =>
    ((U.mem_vertices_iff_coord _).1 (hPU ((Q.parent.mem_vertices_iff_coord
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
    rintro y ⟨hyU, hyb⟩
    exact ⟨hyU, Or.inr (hboxcube hyb)⟩
  obtain ⟨i, hi⟩ : ∃ i, Q.parent.side ≤ 10 * |x i - u i| := by
    simp only [hboxdef, Set.mem_setOf_eq, not_forall, not_le] at hv
    obtain ⟨i, hi⟩ := hv
    have h1 := abs_sub_le_one_of_openIn_adj huv i
    have h2 := abs_sub_le (v i) (u i) (x i)
    refine ⟨i, ?_⟩
    rw [abs_sub_comm]
    omega
  -- the cube of side `s` around `x`, moved into `U`
  let c : Vertex d := fun j =>
    min (max (x j - Q.radius) (U.center j - U.radius)) (U.center j + U.radius - (N : ℤ) + 1)
  let R : IntegerCube d := ⟨c, N⟩
  have hc (j : Fin d) : c j ≤ max (x j - Q.radius) (U.center j - U.radius) ∧
      c j ≤ U.center j + U.radius - (N : ℤ) + 1 ∧
      (c j = max (x j - Q.radius) (U.center j - U.radius) ∨
        c j = U.center j + U.radius - (N : ℤ) + 1) ∧
      x j - Q.radius ≤ max (x j - Q.radius) (U.center j - U.radius) ∧
      U.center j - U.radius ≤ max (x j - Q.radius) (U.center j - U.radius) ∧
      (max (x j - Q.radius) (U.center j - U.radius) = x j - Q.radius ∨
        max (x j - Q.radius) (U.center j - U.radius) = U.center j - U.radius) :=
    ⟨min_le_left _ _, min_le_right _ _, min_choice _ _, le_max_left _ _, le_max_right _ _,
      max_choice _ _⟩
  have hmemR (y : Vertex d) : y ∈ R.vertices ↔ ∀ j, c j ≤ y j ∧ y j < c j + (N : ℤ) :=
    IntegerCube.mem_vertices R y
  have hRU : (↑R.vertices : Set (Vertex d)) ⊆ U.vertices := by
    intro y hy
    rw [Finset.mem_coe, hmemR] at hy
    rw [U.mem_vertices_iff_coord]
    intro j
    have := hc j
    have := hy j
    have := hlowU j
    have := hupU j
    omega
  have hboxR : U.vertices ∩ box ⊆ ↑R.vertices := by
    rintro y ⟨hyU, hyb⟩
    rw [Finset.mem_coe, hmemR]
    intro j
    have h1 := (U.mem_vertices_iff_coord y).1 hyU j
    have h2 := abs_le.mp (hyb j)
    have := hc j
    have := hlowU j
    have := hupU j
    omega
  have hxR : x ∈ (↑R.vertices : Set (Vertex d)) := hboxR ⟨hxU, hxbox⟩
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
      have := hlowU j
      have := hupU j
      refine ⟨le_max_left _ _, max_lt (by omega) ?_⟩
      omega
    · rw [Finset.mem_coe, IntegerCube.mem_vertices]
      intro j
      have := hc j
      have := hx' j
      have := hxP j
      have := hlowU j
      have := hupU j
      change Q.parent.center j - (K : ℤ) / 2 ≤ max (c j) (Q.parent.center j - (K : ℤ) / 2) ∧
        max (c j) (Q.parent.center j - (K : ℤ) / 2) < Q.parent.center j - (K : ℤ) / 2 + (K : ℤ)
      refine ⟨le_max_right _ _, max_lt ?_ (by omega)⟩
      omega
  obtain ⟨-, hconn⟩ := hrP.2 R hR
  obtain ⟨z, -, hxz, hrz⟩ := hconn.exists_of_reachable hxR (reachable_openIn_mono hboxR hxu) hi
  have hchild := hrP.crossingCluster_child_subset hd hPs Q.digit
  rw [Q.parent_child] at hchild
  have hra : (openIn ω Q.parent.vertices).Reachable rP (partitionAnchor ω x) := hchild hanchor
  have hsub1 : (↑R.vertices : Set (Vertex d)) ⊆ U.vertices ∩ (Q.parent.vertices ∪ cubeAt x (N - 1)) :=
    fun y hy => ⟨hRU hy, Or.inr (hRcube hy)⟩
  have hsub2 : Q.parent.vertices ⊆ U.vertices ∩ (Q.parent.vertices ∪ cubeAt x (N - 1)) :=
    fun y hy => ⟨hPU hy, Or.inl hy⟩
  exact ((reachable_openIn_mono hsub1 hxz).trans (reachable_openIn_mono hsub2 hrz).symm).trans
    (reachable_openIn_mono hsub2 hra)

/-- **Pairs inside a resolved cube.** If the partition cubes of lattice neighbours `x, y ∈ U` lie
in `U`, their anchors are joined inside `C_*(U)` and the union of the two partition cubes. -/
theorem reachable_partitionAnchor_of_adj_of_le (hd : 0 < d) (hP : PartitionEvent ω)
    {x y : Vertex d} {U : TriadicCube d} (hxU : x ∈ U.vertices) (hyU : y ∈ U.vertices)
    (hx : (partitionCube ω x).scale ≤ U.scale) (hy : (partitionCube ω y).scale ≤ U.scale)
    (hxy : (nearestNeighborGraph d).Adj x y) :
    (openIn ω (U.crossingCluster ω ∩
      ((partitionCube ω x).vertices ∪ (partitionCube ω y).vertices))).Reachable
      (partitionAnchor ω x) (partitionAnchor ω y) := by
  have hxs := TriadicCube.vertices_subset_of_mem_of_scale_le (mem_partitionCube hP x) hxU hx
  have hys := TriadicCube.vertices_subset_of_mem_of_scale_le (mem_partitionCube hP y) hyU hy
  apply TriadicCube.reachable_crossingCluster_inter
    (crossingCluster_partitionCube_subset hd hP hxU hx (partitionAnchor_mem_crossingCluster hP x))
  refine reachable_openIn_mono ?_ (reachable_partitionAnchor_of_adj hd hP hxy)
  rintro z (hz | hz)
  · exact ⟨hxs hz, Or.inl hz⟩
  · exact ⟨hys hz, Or.inr hz⟩

end Rigidity.Percolation

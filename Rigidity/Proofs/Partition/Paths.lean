import Rigidity.Proofs.Partition.PartitionCube
import Rigidity.External.WellConnected

/-!
# Paths between anchors of the partition

Armstrong and Dario, Corollary 2.10: along every lattice walk, the anchors of the partition cubes
of its endpoints are joined by an open path inside the union of the partition cubes of the
vertices of the walk. It follows from Lemma 2.8 applied to consecutive partition cubes, which
are good and differ by at most one scale. Consequently all anchors lie in one infinite open
component, which contains the crossing clusters of all partition cubes.

Conversely, every vertex `x` of an infinite open component is joined to the anchor of its
partition cube `Q` inside `Q.parent ∪ (x + Q_r)`, where `r = (s - 1) / 2` and `s` is the side
of `Q`: an open path from `x` leaving `x + Q_r` travels at least `r ≥ 3s / 10` inside that cube,
which is a test cube of the well-connected cube `Q.parent` of side `3s`. This replaces the
display after Definition 2.9 of Armstrong and Dario, whose last equality
`C_*(Q_{n+1}) ∩ Q_n = C_∞ ∩ Q_n` fails at vertices of `C_∞` whose open edges all leave the cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The anchors of the partition cubes of lattice neighbours are joined inside the union of the
two partition cubes. -/
theorem reachable_partitionAnchor_of_adj (hd : 0 < d) (hP : PartitionEvent ω) {x y : Vertex d}
    (hxy : (nearestNeighborGraph d).Adj x y) :
    (openIn ω ((partitionCube ω x).vertices ∪ (partitionCube ω y).vertices)).Reachable
      (partitionAnchor ω x) (partitionAnchor ω y) := by
  have hclose := partitionCube_scales_close hP (abs_sub_le_one_of_nearestNeighbor_adj hxy)
  rcases le_total (partitionCube ω x).scale (partitionCube ω y).scale with h | h
  · exact TriadicCube.reachable_of_mem_goodCubes hd (partitionCube_mem_goodCubes hP x)
      (partitionCube_mem_goodCubes hP y) h hclose.2 (mem_partitionCube hP x)
      (mem_partitionCube hP y) hxy (partitionAnchor_mem_crossingCluster hP x)
      (partitionAnchor_mem_crossingCluster hP y)
  · have h' := TriadicCube.reachable_of_mem_goodCubes hd (partitionCube_mem_goodCubes hP y)
      (partitionCube_mem_goodCubes hP x) h hclose.1 (mem_partitionCube hP y)
      (mem_partitionCube hP x) hxy.symm (partitionAnchor_mem_crossingCluster hP y)
      (partitionAnchor_mem_crossingCluster hP x)
    rw [Set.union_comm] at h'
    exact h'.symm

/-- **Armstrong and Dario, Corollary 2.10.** Along every lattice walk from `x` to `y`, the anchors
of the partition cubes of `x` and `y` are joined by an open path inside the union of the partition
cubes of the vertices of the walk. -/
theorem reachable_partitionAnchor_of_walk (hd : 0 < d) (hP : PartitionEvent ω) {x y : Vertex d}
    (p : (nearestNeighborGraph d).Walk x y) :
    (openIn ω (⋃ z ∈ p.support, (partitionCube ω z).vertices)).Reachable
      (partitionAnchor ω x) (partitionAnchor ω y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have hsub1 : (partitionCube ω a).vertices ∪ (partitionCube ω b).vertices ⊆
        ⋃ z ∈ (SimpleGraph.Walk.cons hab p).support, (partitionCube ω z).vertices := by
      rintro w (hw | hw) <;> simp only [Set.mem_iUnion]
      · exact ⟨a, by simp, hw⟩
      · exact ⟨b, by simp [SimpleGraph.Walk.start_mem_support], hw⟩
    have hsub2 : (⋃ z ∈ p.support, (partitionCube ω z).vertices) ⊆
        ⋃ z ∈ (SimpleGraph.Walk.cons hab p).support, (partitionCube ω z).vertices := by
      intro w hw
      simp only [Set.mem_iUnion] at hw ⊢
      obtain ⟨z, hz, hw⟩ := hw
      exact ⟨z, by simp [hz], hw⟩
    exact (reachable_openIn_mono hsub1 (reachable_partitionAnchor_of_adj hd hP hab)).trans
      (reachable_openIn_mono hsub2 ih)

/-- All anchors of partition cubes lie in one open component. -/
theorem reachable_partitionAnchor (hd : 0 < d) (hP : PartitionEvent ω) (x y : Vertex d) :
    (openGraph ω).Reachable (partitionAnchor ω x) (partitionAnchor ω y) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨p⟩ := (LatticeProb.Graph.Zd.latticeConnected d).preconnected x y
  refine (reachable_partitionAnchor_of_walk hd hP p).mono ?_
  intro u v h
  exact h.1

/-- The open component of the anchors is infinite. -/
theorem infinite_supp_partitionAnchor (hd : 0 < d) (hP : PartitionEvent ω) (x : Vertex d) :
    ((openGraph ω).connectedComponentMk (partitionAnchor ω x)).supp.Infinite := by
  haveI : NeZero d := ⟨by omega⟩
  intro hfin
  apply Set.infinite_univ (α := Vertex d)
  have hcover : (Set.univ : Set (Vertex d)) ⊆
      ⋃ a ∈ ((openGraph ω).connectedComponentMk (partitionAnchor ω x)).supp,
        (partitionCube ω a).vertices := by
    intro y _
    simp only [Set.mem_iUnion]
    refine ⟨partitionAnchor ω y, ?_, ?_⟩
    · rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
      exact (reachable_partitionAnchor hd hP x y).symm
    · rw [partitionCube_eq_of_mem hP (partitionAnchor_mem hP y)]
      exact mem_partitionCube hP y
  exact (hfin.biUnion fun a _ => (partitionCube ω a).finite_vertices).subset hcover

/-- The crossing cluster of every partition cube lies in the infinite open component of the
anchors. -/
theorem infinite_supp_of_mem_crossingCluster (hd : 0 < d) (hP : PartitionEvent ω) {x v : Vertex d}
    (hv : v ∈ (partitionCube ω x).crossingCluster ω) :
    ((openGraph ω).connectedComponentMk v).supp.Infinite := by
  have hQ := (partitionCube_mem_goodCubes hP x).2.1
  obtain ⟨root, hroot⟩ := ((partitionCube ω x).wellConnectedIn_threeQuarter_iff ω).1 hQ.2
  have hr : (openGraph ω).Reachable (partitionAnchor ω x) v := by
    refine (hroot.reachable_of_mem_crossingCluster hd hQ.1
      (partitionAnchor_mem_crossingCluster hP x) hv).mono ?_
    intro u w h
    exact h.1
  rw [show (openGraph ω).connectedComponentMk v =
      (openGraph ω).connectedComponentMk (partitionAnchor ω x) from
    (SimpleGraph.ConnectedComponent.eq.2 hr).symm]
  exact infinite_supp_partitionAnchor hd hP x

/-- **Vertices of infinite open components.** A vertex `x` of an infinite open component is
joined to the anchor of its partition cube `Q` by an open path inside the union of the parent of
`Q` and the cube `x + Q_r`, `r = (s - 1) / 2`, where `s = 3ⁿ` is the side of `Q`. -/
theorem reachable_partitionAnchor_of_infinite (hd : 0 < d) (hP : PartitionEvent ω)
    {x : Vertex d} (hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite) :
    (openIn ω ((partitionCube ω x).parent.vertices ∪
      cubeAt x (3 ^ (partitionCube ω x).scale / 2))).Reachable x (partitionAnchor ω x) := by
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
  -- the cube of radius `r` around `x`
  let R : IntegerCube d := ⟨fun i => x i - Q.radius, N⟩
  have hmemR (y : Vertex d) : y ∈ R.vertices ↔ ∀ i, |y i - x i| ≤ Q.radius := by
    rw [IntegerCube.mem_vertices]
    change (∀ i, x i - Q.radius ≤ y i ∧ y i < x i - Q.radius + (N : ℤ)) ↔ _
    refine forall_congr' fun i => ?_
    rw [abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
  have hRcube : (↑R.vertices : Set (Vertex d)) = cubeAt x (N / 2) := by
    ext y
    rw [Finset.mem_coe, hmemR]
    change _ ↔ ∀ i, |y i - x i| ≤ ((N / 2 : ℕ) : ℤ)
    have h : ((N / 2 : ℕ) : ℤ) = Q.radius := by omega
    rw [h]
  have hxR : x ∈ (↑R.vertices : Set (Vertex d)) := by
    rw [Finset.mem_coe, hmemR]
    intro i
    rw [sub_self, abs_zero]
    omega
  have hR : R ∈ Q.parent.testCubes Q.parent.threeQuarterCube.vertices := by
    refine ⟨by change Q.parent.side ≤ 10 * ((N : ℕ) : ℤ); omega,
      by change 2 * ((N : ℕ) : ℤ) ≤ Q.parent.side; omega, ?_⟩
    set K : ℕ := 3 * 3 ^ (Q.scale + 1) / 4 with hKdef
    have hpow : 3 ^ (Q.scale + 1) = 3 * N := by rw [pow_succ, hNdef]; ring
    have hK : (K : ℤ) = 3 * Q.parent.side / 4 := by rw [hKdef, hpow]; omega
    let w : Vertex d := fun i => max (x i - Q.radius) (min (x i + Q.radius) (Q.parent.center i))
    have hw (i : Fin d) : x i - Q.radius ≤ w i ∧
        min (x i + Q.radius) (Q.parent.center i) ≤ w i ∧
        (w i = x i - Q.radius ∨ w i = min (x i + Q.radius) (Q.parent.center i)) ∧
        min (x i + Q.radius) (Q.parent.center i) ≤ x i + Q.radius ∧
        min (x i + Q.radius) (Q.parent.center i) ≤ Q.parent.center i ∧
        (min (x i + Q.radius) (Q.parent.center i) = x i + Q.radius ∨
          min (x i + Q.radius) (Q.parent.center i) = Q.parent.center i) :=
      ⟨le_max_left _ _, le_max_right _ _, max_choice _ _, min_le_left _ _, min_le_right _ _,
        min_choice _ _⟩
    refine ⟨w, ?_, ?_⟩
    · rw [hmemR]
      intro i
      have := hw i
      rw [abs_le]
      omega
    · rw [Finset.mem_coe, IntegerCube.mem_vertices]
      intro i
      have := hw i
      have := hxP i
      change Q.parent.center i - (K : ℤ) / 2 ≤ w i ∧
        w i < Q.parent.center i - (K : ℤ) / 2 + (K : ℤ)
      omega
  -- an open path from `x` leaving the cube around `x`
  obtain ⟨b, hb, hbR⟩ := (hinf.sdiff R.vertices.finite_toSet).nonempty
  have hbx : (openGraph ω).Reachable b x := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq] at hb
    exact hb
  have hxb : (openIn ω Set.univ).Reachable x b := by
    refine hbx.symm.mono ?_
    intro u v h
    exact ⟨h, trivial, trivial⟩
  obtain ⟨u, hxu, hu⟩ := exists_reachable_inter_of_reachable_openIn hxb hxR
  have huR' : u ∈ Set.univ ∩ (↑R.vertices : Set (Vertex d)) :=
    mem_of_reachable_openIn_of_mem ⟨trivial, hxR⟩ hxu
  have huR : u ∈ (↑R.vertices : Set (Vertex d)) := huR'.2
  obtain ⟨i, hi⟩ : ∃ i, Q.parent.side ≤ 10 * |x i - u i| := by
    rcases hu with rfl | ⟨v, hv, huv⟩
    · exact absurd huR hbR
    · rw [Finset.mem_coe, hmemR] at hv
      simp only [not_forall, not_le] at hv
      obtain ⟨i, hi⟩ := hv
      have h1 := abs_sub_le_one_of_openIn_adj huv i
      have h2 := abs_sub_le (v i) (u i) (x i)
      refine ⟨i, ?_⟩
      rw [abs_sub_comm]
      omega
  obtain ⟨-, hconn⟩ := hrP.2 R hR
  obtain ⟨z, -, hxz, hrz⟩ := hconn.exists_of_reachable hxR
    (reachable_openIn_mono Set.inter_subset_right hxu) hi
  have hchild := hrP.crossingCluster_child_subset hd hPs Q.digit
  rw [Q.parent_child] at hchild
  have hra : (openIn ω Q.parent.vertices).Reachable rP (partitionAnchor ω x) := hchild hanchor
  rw [← hRcube]
  exact ((reachable_openIn_mono Set.subset_union_right hxz).trans
    (reachable_openIn_mono Set.subset_union_left hrz).symm).trans
    (reachable_openIn_mono Set.subset_union_left hra)

/-- The region of `reachable_partitionAnchor_of_infinite` lies in the cube of radius `3s` around
`x`. -/
theorem parent_union_cubeAt_subset (hP : PartitionEvent ω) (x : Vertex d) :
    (partitionCube ω x).parent.vertices ∪ cubeAt x (3 ^ (partitionCube ω x).scale / 2) ⊆
      cubeAt x (3 ^ ((partitionCube ω x).scale + 1)) := by
  have hxP := (partitionCube ω x).vertices_subset_parent (mem_partitionCube hP x)
  have hle : 3 ^ (partitionCube ω x).scale / 2 ≤ 3 ^ ((partitionCube ω x).scale + 1) :=
    (Nat.div_le_self _ _).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
  rintro y (hy | hy) i
  · have h := TriadicCube.abs_coord_sub_lt_side hy hxP i
    have hs : (partitionCube ω x).parent.side = ((3 ^ ((partitionCube ω x).scale + 1) : ℕ) : ℤ) :=
      (partitionCube ω x).parent.natCast_three_pow_scale.symm
    rw [hs] at h
    exact h.le
  · exact (hy i).trans (by exact_mod_cast hle)

end Rigidity.Percolation

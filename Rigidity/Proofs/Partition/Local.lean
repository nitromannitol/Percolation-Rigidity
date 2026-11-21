import Rigidity.Proofs.Partition.Resolved

/-!
# Local paths to anchors inside neighbouring partition cubes

The proof of Armstrong and Dario, Lemma 3.2, uses that every vertex `x` of `C_*(U)` is joined to
the anchor of its partition cube `Q` by a path inside the union of the partition cubes at distance
at most one from `Q`. This holds. Let `s` be the side of `Q` and `ρ = ⌈s / 10⌉`. A test cube of `Q`
of side `(s - 1) / 2` containing the box of radius `ρ` around `x` (moved into `U`, and towards the
centre of `Q`) lies in the `ρ`-neighbourhood of `Q`; an open path from `x` leaving that box is
joined inside the test cube to the root of the well-connected cube `Q`. Every point of the
`s / 3`-neighbourhood of `Q` lies in a partition cube at `ℓ∞` distance at most one from `Q`, whose
scale differs from that of `Q` by at most one: the triadic cube of side `s / 3` containing it
touches `Q`.

The same argument joins a vertex of an infinite open component to the anchor of its partition cube
inside the `ρ`-neighbourhood of the cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The `ρ`-neighbourhood of a triadic cube in the `ℓ∞` norm. -/
def TriadicCube.thickening (Q : TriadicCube d) (ρ : ℤ) : Set (Vertex d) :=
  {y | ∀ i, Q.center i - Q.radius - ρ ≤ y i ∧ y i ≤ Q.center i + Q.radius + ρ}

theorem TriadicCube.vertices_subset_thickening (Q : TriadicCube d) {ρ : ℤ} (hρ : 0 ≤ ρ) :
    Q.vertices ⊆ Q.thickening ρ := by
  intro y hy i
  have := (Q.mem_vertices_iff_coord y).1 hy i
  constructor <;> omega

theorem TriadicCube.thickening_mono (Q : TriadicCube d) {ρ ρ' : ℤ} (h : ρ ≤ ρ') :
    Q.thickening ρ ⊆ Q.thickening ρ' := by
  intro y hy i
  have := hy i
  constructor <;> omega

/-- **A test cube near a vertex.** For a vertex `x` of a triadic cube `Q` of scale at least two
and bounds `lo ≤ Q ≤ hi`, there is a test cube of `Q` containing every point between the bounds
at distance at most `ρ = ⌈s / 10⌉` from `x`, and contained between the bounds and in the
`ρ`-neighbourhood of `Q`. -/
theorem TriadicCube.exists_testCube_near (Q : TriadicCube d) (hs : 2 ≤ Q.scale) {x : Vertex d}
    (hx : x ∈ Q.vertices) (lo hi : Vertex d) (hlo : ∀ i, lo i ≤ Q.center i - Q.radius)
    (hhi : ∀ i, Q.center i + Q.radius ≤ hi i) :
    ∃ R ∈ Q.testCubes Q.threeQuarterCube.vertices,
      (∀ y : Vertex d, (∀ i, |y i - x i| ≤ (Q.side + 9) / 10) →
        (∀ i, lo i ≤ y i ∧ y i ≤ hi i) → y ∈ R.vertices) ∧
      (∀ y ∈ R.vertices, (∀ i, lo i ≤ y i ∧ y i ≤ hi i) ∧
        y ∈ Q.thickening ((Q.side + 9) / 10)) := by
  classical
  set N : ℕ := 3 ^ Q.scale
  have hNdef : N = 3 ^ Q.scale := rfl
  have hN : (N : ℤ) = Q.side := Q.natCast_three_pow_scale
  have hN9 : 9 ≤ N := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ Q.scale := Nat.pow_le_pow_right (by norm_num) hs
  have hsr := Q.side_eq_two_mul_radius_add_one
  set ρ : ℤ := (Q.side + 9) / 10 with hρdef
  have hL : ((N / 2 : ℕ) : ℤ) = Q.radius := by omega
  let c : Vertex d := fun j => if x j ≤ Q.center j then max (x j - ρ) (lo j)
    else min (x j + ρ) (hi j) - Q.radius + 1
  have hc (j : Fin d) : (x j ≤ Q.center j ∧ c j = max (x j - ρ) (lo j)) ∨
      (Q.center j < x j ∧ c j = min (x j + ρ) (hi j) - Q.radius + 1) := by
    by_cases h : x j ≤ Q.center j
    · exact Or.inl ⟨h, if_pos h⟩
    · exact Or.inr ⟨lt_of_not_ge h, if_neg h⟩
  have hmm (j : Fin d) : x j - ρ ≤ max (x j - ρ) (lo j) ∧ lo j ≤ max (x j - ρ) (lo j) ∧
      (max (x j - ρ) (lo j) = x j - ρ ∨ max (x j - ρ) (lo j) = lo j) ∧
      min (x j + ρ) (hi j) ≤ x j + ρ ∧ min (x j + ρ) (hi j) ≤ hi j ∧
      (min (x j + ρ) (hi j) = x j + ρ ∨ min (x j + ρ) (hi j) = hi j) :=
    ⟨le_max_left _ _, le_max_right _ _, max_choice _ _, min_le_left _ _, min_le_right _ _,
      min_choice _ _⟩
  have hxQ := (Q.mem_vertices_iff_coord x).1 hx
  let R : IntegerCube d := ⟨c, N / 2⟩
  have hmemR (y : Vertex d) : y ∈ R.vertices ↔ ∀ j, c j ≤ y j ∧ y j < c j + Q.radius := by
    rw [IntegerCube.mem_vertices]
    change (∀ j, c j ≤ y j ∧ y j < c j + ((N / 2 : ℕ) : ℤ)) ↔ _
    rw [hL]
  refine ⟨R, ?_, ?_, ?_⟩
  · refine ⟨by change Q.side ≤ 10 * ((N / 2 : ℕ) : ℤ); omega,
      by change 2 * ((N / 2 : ℕ) : ℤ) ≤ Q.side; omega, ?_⟩
    set K : ℕ := 3 * 3 ^ Q.scale / 4 with hKdef
    have hK : (K : ℤ) = 3 * Q.side / 4 := by rw [hKdef, ← hNdef]; omega
    refine ⟨fun j => max (c j) (Q.center j - (K : ℤ) / 2), ?_, ?_⟩
    · rw [hmemR]
      intro j
      have := hc j
      have := hmm j
      have := hxQ j
      have := hlo j
      have := hhi j
      refine ⟨le_max_left _ _, max_lt (by omega) (by omega)⟩
    · rw [Finset.mem_coe, IntegerCube.mem_vertices]
      intro j
      have := hc j
      have := hmm j
      have := hxQ j
      have := hlo j
      have := hhi j
      change Q.center j - (K : ℤ) / 2 ≤ max (c j) (Q.center j - (K : ℤ) / 2) ∧
        max (c j) (Q.center j - (K : ℤ) / 2) < Q.center j - (K : ℤ) / 2 + (K : ℤ)
      exact ⟨le_max_right _ _, max_lt (by omega) (by omega)⟩
  · intro y hy hlohi
    rw [hmemR]
    intro j
    have := abs_le.mp (hy j)
    have := hlohi j
    have := hc j
    have := hmm j
    have := hxQ j
    omega
  · intro y hyR
    rw [hmemR] at hyR
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := hyR j
      have := hc j
      have := hmm j
      have := hxQ j
      have := hlo j
      have := hhi j
      omega
    · have := hyR j
      have := hc j
      have := hmm j
      have := hxQ j
      have := hlo j
      have := hhi j
      constructor <;> omega

/-- **Absorption near a well-connected cube.** Let `R` be a test cube of a well-connected cube `Q`
of scale at least two, contained in a region `D` and containing the points of `D` at distance at
most `⌈s / 10⌉` from `x ∈ D`. An open path inside `D` from `x` to `b` either stays inside `R`, or
`x` is joined to the root inside `R ∪ Q`. -/
theorem TriadicCube.IsWellConnectedRoot.reachable_or_of_testCube {Q : TriadicCube d}
    {root : Vertex d} (hroot : Q.IsWellConnectedRoot ω root) {D : Set (Vertex d)}
    {R : IntegerCube d} (hR : R ∈ Q.testCubes Q.threeQuarterCube.vertices) {x b : Vertex d}
    (hxD : x ∈ D) (hboxR : ∀ y ∈ D, (∀ i, |y i - x i| ≤ (Q.side + 9) / 10) → y ∈ R.vertices)
    (hxb : (openIn ω D).Reachable x b) :
    (openIn ω ↑R.vertices).Reachable x b ∨
      (openIn ω (↑R.vertices ∪ Q.vertices)).Reachable x root := by
  set ρ : ℤ := (Q.side + 9) / 10 with hρdef
  set box : Set (Vertex d) := {y | ∀ i, |y i - x i| ≤ ρ} with hboxdef
  have hside := Q.side_pos
  have hxbox : x ∈ box := by
    rw [hboxdef, Set.mem_setOf_eq]
    intro i
    rw [sub_self, abs_zero]
    omega
  have hsub : D ∩ box ⊆ ↑R.vertices := fun y hy => hboxR y hy.1 hy.2
  have hxR : x ∈ (↑R.vertices : Set (Vertex d)) := hsub ⟨hxD, hxbox⟩
  obtain ⟨u, hxu, hu⟩ := exists_reachable_inter_of_reachable_openIn hxb hxbox
  rcases hu with rfl | ⟨v, hv, huv⟩
  · exact Or.inl (reachable_openIn_mono hsub hxu)
  right
  obtain ⟨i, hi⟩ : ∃ i, Q.side ≤ 10 * |x i - u i| := by
    simp only [hboxdef, Set.mem_setOf_eq, not_forall, not_le] at hv
    obtain ⟨i, hi⟩ := hv
    have h1 := abs_sub_le_one_of_openIn_adj huv i
    have h2 := abs_sub_le (v i) (u i) (x i)
    refine ⟨i, ?_⟩
    rw [abs_sub_comm]
    omega
  obtain ⟨-, hconn⟩ := hroot.2 R hR
  obtain ⟨z, -, hxz, hrz⟩ := hconn.exists_of_reachable hxR (reachable_openIn_mono hsub hxu) hi
  exact (reachable_openIn_mono Set.subset_union_left hxz).trans
    (reachable_openIn_mono Set.subset_union_right hrz).symm

/-- **Local paths from the infinite cluster.** A vertex `x` of an infinite open component is
joined to the anchor of its partition cube `Q` inside the `⌈s / 10⌉`-neighbourhood of `Q`, where
`s` is the side of `Q`. -/
theorem reachable_partitionAnchor_of_infinite_local (hd : 0 < d) (hP : PartitionEvent ω)
    {x : Vertex d} (hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite) :
    (openIn ω ((partitionCube ω x).thickening (((partitionCube ω x).side + 9) / 10))).Reachable
      x (partitionAnchor ω x) := by
  have hQg := partitionCube_mem_goodCubes hP x
  have h3 := three_le_scale_partitionCube hP x
  have hxQ := mem_partitionCube hP x
  have hanchor := partitionAnchor_mem_crossingCluster hP x
  set Q := partitionCube ω x with hQdef
  obtain ⟨rQ, hrQ⟩ := (Q.wellConnectedIn_threeQuarter_iff ω).1 hQg.2.1.2
  set ρ : ℤ := (Q.side + 9) / 10 with hρdef
  have hside := Q.side_pos
  have hρ0 : 0 ≤ ρ := by omega
  have hxQ' := (Q.mem_vertices_iff_coord x).1 hxQ
  obtain ⟨R, hR, hboxR, hRsub⟩ := Q.exists_testCube_near (by omega) hxQ
    (fun i => Q.center i - Q.radius - ρ) (fun i => Q.center i + Q.radius + ρ)
    (fun i => by omega) (fun i => by omega)
  obtain ⟨b, hb, hbR⟩ := (hinf.sdiff R.vertices.finite_toSet).nonempty
  have hbx : (openGraph ω).Reachable b x := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq] at hb
    exact hb
  have hxb : (openIn ω Set.univ).Reachable x b := by
    refine hbx.symm.mono ?_
    intro u v h
    exact ⟨h, trivial, trivial⟩
  have hbox : ∀ y ∈ (Set.univ : Set (Vertex d)), (∀ i, |y i - x i| ≤ (Q.side + 9) / 10) →
      y ∈ R.vertices := by
    intro y _ hy
    refine hboxR y hy fun i => ?_
    have := abs_le.mp (hy i)
    have := hxQ' i
    constructor <;> omega
  have hRQ : (↑R.vertices : Set (Vertex d)) ∪ Q.vertices ⊆ Q.thickening ρ := by
    rintro y (hy | hy)
    · exact (hRsub y hy).2
    · exact Q.vertices_subset_thickening hρ0 hy
  have hxR : x ∈ (↑R.vertices : Set (Vertex d)) :=
    hbox x trivial fun i => by rw [sub_self, abs_zero]; exact hρ0
  rcases hrQ.reachable_or_of_testCube (D := Set.univ) hR trivial hbox hxb with h | h
  · exact absurd (mem_of_reachable_openIn_of_mem hxR h) hbR
  · have hra : (openIn ω Q.vertices).Reachable rQ (partitionAnchor ω x) := by
      have h' := hanchor
      rw [hrQ.crossingCluster_eq hd (by omega)] at h'
      exact h'
    exact (reachable_openIn_mono hRQ h).trans
      (reachable_openIn_mono (Q.vertices_subset_thickening hρ0) hra)

/-- **Local paths inside a resolved cube** (the paths of the proof of Armstrong and Dario,
Lemma 3.2). If the partition cube `Q` of a vertex `x` of the crossing cluster of a triadic cube
`U` lies in `U`, then `x` is joined to the anchor of `Q` inside `C_*(U)` and the
`⌈s / 10⌉`-neighbourhood of `Q`, where `s` is the side of `Q`. -/
theorem reachable_partitionAnchor_of_mem_crossingCluster_local (hd : 0 < d)
    (hP : PartitionEvent ω) {x : Vertex d} {U : TriadicCube d} (hxU : x ∈ U.vertices)
    (hscale : (partitionCube ω x).scale ≤ U.scale) (hx : x ∈ U.crossingCluster ω) :
    (openIn ω (U.crossingCluster ω ∩
      (partitionCube ω x).thickening (((partitionCube ω x).side + 9) / 10))).Reachable
      x (partitionAnchor ω x) := by
  have hU := mem_goodCubes_of_partitionCube_le hP hxU hscale
  obtain ⟨rU, hrU⟩ := (U.wellConnectedIn_threeQuarter_iff ω).1 hU.2.1.2
  have hanchorU := crossingCluster_partitionCube_subset hd hP hxU hscale
    (partitionAnchor_mem_crossingCluster hP x)
  have hxa : (openIn ω U.vertices).Reachable x (partitionAnchor ω x) :=
    hrU.reachable_of_mem_crossingCluster hd hU.2.1.1 hx hanchorU
  apply TriadicCube.reachable_crossingCluster_inter hx
  have hQg := partitionCube_mem_goodCubes hP x
  have h3 := three_le_scale_partitionCube hP x
  have hxQ := mem_partitionCube hP x
  have hanchor := partitionAnchor_mem_crossingCluster hP x
  have hQU : (partitionCube ω x).vertices ⊆ U.vertices :=
    TriadicCube.vertices_subset_of_mem_of_scale_le hxQ hxU hscale
  set Q := partitionCube ω x with hQdef
  obtain ⟨rQ, hrQ⟩ := (Q.wellConnectedIn_threeQuarter_iff ω).1 hQg.2.1.2
  set ρ : ℤ := (Q.side + 9) / 10 with hρdef
  have hside := Q.side_pos
  have hsr := Q.side_eq_two_mul_radius_add_one
  have hρ0 : 0 ≤ ρ := by omega
  have hlowU : ∀ j, U.center j - U.radius ≤ Q.center j - Q.radius := fun j =>
    ((U.mem_vertices_iff_coord _).1 (hQU ((Q.mem_vertices_iff_coord
      (fun j => Q.center j - Q.radius)).2 fun j =>
        ⟨le_rfl, show Q.center j - Q.radius ≤ Q.center j + Q.radius by omega⟩)) j).1
  have hupU : ∀ j, Q.center j + Q.radius ≤ U.center j + U.radius := fun j =>
    ((U.mem_vertices_iff_coord _).1 (hQU ((Q.mem_vertices_iff_coord
      (fun j => Q.center j + Q.radius)).2 fun j =>
        ⟨show Q.center j - Q.radius ≤ Q.center j + Q.radius by omega, le_rfl⟩)) j).2
  obtain ⟨R, hR, hboxR, hRsub⟩ := Q.exists_testCube_near (by omega) hxQ
    (fun i => U.center i - U.radius) (fun i => U.center i + U.radius) hlowU hupU
  have hbox : ∀ y ∈ U.vertices, (∀ i, |y i - x i| ≤ (Q.side + 9) / 10) → y ∈ R.vertices :=
    fun y hy hyb => hboxR y hyb ((U.mem_vertices_iff_coord y).1 hy)
  have hRU : (↑R.vertices : Set (Vertex d)) ⊆ U.vertices := fun y hy =>
    (U.mem_vertices_iff_coord y).2 (hRsub y hy).1
  have hreg : (↑R.vertices : Set (Vertex d)) ∪ Q.vertices ⊆ U.vertices ∩ Q.thickening ρ := by
    rintro y (hy | hy)
    · exact ⟨hRU hy, (hRsub y hy).2⟩
    · exact ⟨hQU hy, Q.vertices_subset_thickening hρ0 hy⟩
  rcases hrQ.reachable_or_of_testCube hR hxU hbox hxa with h | h
  · exact reachable_openIn_mono (Set.subset_union_left.trans hreg) h
  · have hra : (openIn ω Q.vertices).Reachable rQ (partitionAnchor ω x) := by
      have h' := hanchor
      rw [hrQ.crossingCluster_eq hd (by omega)] at h'
      exact h'
    exact (reachable_openIn_mono hreg h).trans
      (reachable_openIn_mono (Set.subset_union_right.trans hreg) hra)

/-- **Neighbouring partition cubes.** Every point of the `3^{n-1}`-neighbourhood of a partition
cube `Q` of scale `n` lies in a partition cube at `ℓ∞` distance at most one from `Q`, whose scale
differs from `n` by at most one. -/
theorem partitionCube_near_of_mem_thickening (hP : PartitionEvent ω) {x y : Vertex d}
    (hy : y ∈ (partitionCube ω x).thickening (3 ^ ((partitionCube ω x).scale - 1))) :
    (partitionCube ω x).scale ≤ (partitionCube ω y).scale + 1 ∧
      (partitionCube ω y).scale ≤ (partitionCube ω x).scale + 1 ∧
      ∃ a ∈ (partitionCube ω y).vertices, ∃ b ∈ (partitionCube ω x).vertices,
        ∀ i, |a i - b i| ≤ 1 := by
  have h3 := three_le_scale_partitionCube hP x
  set Q := partitionCube ω x with hQdef
  obtain ⟨C, ⟨hCs, hyC⟩, -⟩ := TriadicCube.existsUnique_mem d (Q.scale - 1) y
  have hsides : Q.side = 3 * C.side := by
    simp only [TriadicCube.side, hCs]
    rw [← pow_succ']
    congr 1
    omega
  have hCsr := C.side_eq_two_mul_radius_add_one
  have hQsr := Q.side_eq_two_mul_radius_add_one
  have hCpos := C.side_pos
  have hthick : (3 : ℤ) ^ (Q.scale - 1) = C.side := by
    simp only [TriadicCube.side, hCs]
  let y' : Vertex d := fun i => if Q.center i + Q.radius < y i then Q.center i + Q.radius + 1
    else if y i < Q.center i - Q.radius then Q.center i - Q.radius - 1 else y i
  let q : Vertex d := fun i => if Q.center i + Q.radius < y i then Q.center i + Q.radius
    else if y i < Q.center i - Q.radius then Q.center i - Q.radius else y i
  have hcoord (i : Fin d) :
      (C.center i - C.radius ≤ y' i ∧ y' i ≤ C.center i + C.radius) ∧
        (Q.center i - Q.radius ≤ q i ∧ q i ≤ Q.center i + Q.radius) ∧
        (-1 ≤ q i - y' i ∧ q i - y' i ≤ 1) := by
    have hyCi := (C.mem_vertices_iff_coord y).1 hyC i
    have hyi := hy i
    rw [hthick] at hyi
    have hCt : C.center i = Q.center i + C.side * (C.index i - 3 * Q.index i) := by
      change C.side * C.index i = Q.side * Q.index i + C.side * (C.index i - 3 * Q.index i)
      rw [hsides]
      ring
    set t := C.index i - 3 * Q.index i with ht
    have htle : t ≤ 2 := by
      by_contra h
      have h' : 3 ≤ t := by omega
      have := mul_le_mul_of_nonneg_left h' hCpos.le
      omega
    have htge : -2 ≤ t := by
      by_contra h
      have h' : t ≤ -3 := by omega
      have := mul_le_mul_of_nonneg_left h' hCpos.le
      omega
    rw [hCt] at hyCi ⊢
    simp only [y', q]
    interval_cases t <;> split_ifs <;> omega
  have hy'C : y' ∈ C.vertices := (C.mem_vertices_iff_coord y').2 fun i => (hcoord i).1
  have hqQ : q ∈ Q.vertices := (Q.mem_vertices_iff_coord q).2 fun i => (hcoord i).2.1
  have hnear : ∀ i, |q i - y' i| ≤ 1 := fun i => abs_le.2 (hcoord i).2.2
  have hpq : partitionCube ω q = Q := partitionCube_eq_of_mem hP hqQ
  have hclose := partitionCube_scales_close hP hnear
  rw [hpq] at hclose
  have hCsub : C.vertices ⊆ (partitionCube ω y').vertices :=
    TriadicCube.vertices_subset_of_mem_of_scale_le hy'C (mem_partitionCube hP y') (by omega)
  have hyy' : partitionCube ω y = partitionCube ω y' := partitionCube_eq_of_mem hP (hCsub hyC)
  rw [hyy']
  exact ⟨hclose.1, hclose.2, y', mem_partitionCube hP y', q, hqQ, fun i => by
    rw [abs_sub_comm]; exact hnear i⟩

/-- The `⌈s / 10⌉`-neighbourhood of a partition cube of side `s` is covered by partition cubes at
`ℓ∞` distance at most one from it, of comparable scales. -/
theorem partitionCube_near_of_mem_thickening_local (hP : PartitionEvent ω) {x y : Vertex d}
    (hy : y ∈ (partitionCube ω x).thickening (((partitionCube ω x).side + 9) / 10)) :
    (partitionCube ω x).scale ≤ (partitionCube ω y).scale + 1 ∧
      (partitionCube ω y).scale ≤ (partitionCube ω x).scale + 1 ∧
      ∃ a ∈ (partitionCube ω y).vertices, ∃ b ∈ (partitionCube ω x).vertices,
        ∀ i, |a i - b i| ≤ 1 := by
  have h3 := three_le_scale_partitionCube hP x
  refine partitionCube_near_of_mem_thickening hP ((partitionCube ω x).thickening_mono ?_ hy)
  have hpow : (partitionCube ω x).side = 3 * 3 ^ ((partitionCube ω x).scale - 1) := by
    simp only [TriadicCube.side]
    rw [← pow_succ']
    congr 1
    omega
  have hpos : (0 : ℤ) < 3 ^ ((partitionCube ω x).scale - 1) := by positivity
  omega

end Rigidity.Percolation

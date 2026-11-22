import Rigidity.Proofs.Cluster.PlanarBoxWindows
import Rigidity.Proofs.Cluster.PlanarCoarseData

/-!
# The cluster of an integer square resolved by the planar partition

An integer square `B` (not necessarily triadic) is resolved by the planar partition
when it contains the partition cubes of its vertices. The anchors of all partition cubes inside `B`
are then joined by open paths inside `B`, and the cluster `C(B)` is the set of vertices of `B`
joined inside `B` to the anchor of their partition cube. The domain `B`, the cluster `C(B)`, the
partition cubes with their anchors, and the windows and pair windows inside `B` restricted to
`C(B)` form coarse-graining data, as for resolved triadic cubes (`planarCoarseData`).

For the triple `B = 3□'` of a triadic cube `□'`, this is the cluster on which Armstrong and Dario
use the Sobolev inequality (Proposition 3.4) in the proof of the reverse Hölder inequality of
Lemma 3.6 at `□'`, as needed by the Gehring argument of Proposition 3.8.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- An integer square is resolved by the planar partition when it contains the partition cubes of
its vertices. -/
def PlanarBoxResolved (ω : Configuration 2) (B : IntegerCube 2) : Prop :=
  ∀ z ∈ B.vertices, (planarPartCube ω z).vertices ⊆ ↑B.vertices

/-- **Chains in an integer square.** A transitive relation holding between all pairs of adjacent
or diagonal neighbours in an integer square holds between all pairs of its vertices. -/
theorem IntegerCube.forall_of_near (B : IntegerCube 2) (R : Vertex 2 → Vertex 2 → Prop)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ z ∈ B.vertices, ∀ z' ∈ B.vertices, (∀ i, |z i - z' i| ≤ 1) → R z z') :
    ∀ z ∈ B.vertices, ∀ z' ∈ B.vertices, R z z' := by
  suffices h : ∀ n : ℕ, ∀ z ∈ B.vertices, ∀ z' ∈ B.vertices,
      (z 0 - z' 0).natAbs + (z 1 - z' 1).natAbs ≤ n → R z z' from
    fun z hz z' hz' => h _ z hz z' hz' le_rfl
  intro n
  induction n with
  | zero =>
    intro z hz z' hz' h0
    refine hstep z hz z' hz' fun i => ?_
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> rw [abs_le] <;> omega
  | succ n ih =>
    intro z hz z' hz' hn
    obtain ⟨c0, h0, hb0, hd0⟩ := exists_step_toward (z 0) (z' 0)
    obtain ⟨c1, h1, hb1, hd1⟩ := exists_step_toward (z 1) (z' 1)
    set z'' : Vertex 2 := ![c0, c1]
    have e0 : z'' 0 = c0 := rfl
    have e1 : z'' 1 = c1 := rfl
    have hzB := (IntegerCube.mem_vertices B z).1 hz
    have hz'B := (IntegerCube.mem_vertices B z').1 hz'
    have hz''B : z'' ∈ B.vertices := by
      rw [IntegerCube.mem_vertices]
      intro i
      fin_cases i
      · have h1 := hzB 0
        have h2 := hz'B 0
        simp only [Fin.zero_eta, e0]
        omega
      · have h1 := hzB 1
        have h2 := hz'B 1
        simp only [Fin.mk_one, e1]
        omega
    have hnear : ∀ i, |z i - z'' i| ≤ 1 := by
      intro i
      fin_cases i
      · simpa only [Fin.zero_eta, e0] using h0
      · simpa only [Fin.mk_one, e1] using h1
    have hdist : (z'' 0 - z' 0).natAbs + (z'' 1 - z' 1).natAbs ≤ n := by
      rw [e0, e1]
      omega
    exact htrans _ _ _ (hstep z hz z'' hz''B hnear) (ih z'' hz''B z' hz' hdist)

/-- **Anchors inside a resolved square.** The anchors of the partition cubes of any two vertices
of a resolved integer square are joined by an open path inside the square. -/
theorem reachIn_planarAnchor_of_boxResolved (hP : PlanarPartitionEvent ω) {B : IntegerCube 2}
    (hBr : PlanarBoxResolved ω B) {z z' : Vertex 2}
    (hz : z ∈ B.vertices) (hz' : z' ∈ B.vertices) :
    ReachIn ω ↑B.vertices ((planarPartCube ω z).planarAnchor ω)
      ((planarPartCube ω z').planarAnchor ω) := by
  refine B.forall_of_near (fun z z' => ReachIn ω ↑B.vertices
    ((planarPartCube ω z).planarAnchor ω) ((planarPartCube ω z').planarAnchor ω))
    (fun a b c h1 h2 => h1.trans h2) ?_ z hz z' hz'
  intro z hz z' hz' hnear
  obtain ⟨hsc1, hsc2⟩ := planarPartCube_scales_close hP hnear
  rcases le_total (planarPartCube ω z).scale (planarPartCube ω z').scale with h | h
  · exact (TriadicCube.reachIn_planarAnchor_boxPairWindow (planarPartCube_meshed hP z).1
      (planarPartCube_meshed hP z').1 (planarPartCube_large hP z) (hBr z hz) (hBr z' hz')
      h hsc2 (planarPartCube_spec hP z).1 (planarPartCube_spec hP z').1 hnear).mono
      (Finset.coe_subset.2 (TriadicCube.boxPairWindow_spec (hBr z hz) (hBr z' hz') h hsc2
        (planarPartCube_spec hP z).1 (planarPartCube_spec hP z').1 hnear).2.2.2)
  · have hnear' : ∀ i, |z' i - z i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    exact ((TriadicCube.reachIn_planarAnchor_boxPairWindow (planarPartCube_meshed hP z').1
      (planarPartCube_meshed hP z).1 (planarPartCube_large hP z') (hBr z' hz') (hBr z hz)
      h hsc1 (planarPartCube_spec hP z').1 (planarPartCube_spec hP z).1 hnear').mono
      (Finset.coe_subset.2 (TriadicCube.boxPairWindow_spec (hBr z' hz') (hBr z hz) h hsc1
        (planarPartCube_spec hP z').1 (planarPartCube_spec hP z).1 hnear').2.2.2)).symm

/-- The cluster `C(B)` of an integer square: the vertices of `B` joined inside `B` to the anchor
of their partition cube. -/
def planarBoxCluster (ω : Configuration 2) (B : IntegerCube 2) : Set (Vertex 2) :=
  {x | x ∈ B.vertices ∧ ReachIn ω ↑B.vertices x ((planarPartCube ω x).planarAnchor ω)}

/-- The vertices of the cluster of an integer square, as a finite set. -/
noncomputable def boxClusterVertices (ω : Configuration 2) (B : IntegerCube 2) :
    Finset (Vertex 2) :=
  B.vertices.filter (· ∈ planarBoxCluster ω B)

theorem mem_boxClusterVertices {B : IntegerCube 2} {x : Vertex 2} :
    x ∈ boxClusterVertices ω B ↔ x ∈ planarBoxCluster ω B := by
  unfold boxClusterVertices
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- A vertex of a resolved square joined inside it to some anchor belongs to its cluster. -/
theorem mem_planarBoxCluster_of_reachIn (hP : PlanarPartitionEvent ω) {B : IntegerCube 2}
    (hBr : PlanarBoxResolved ω B) {y z : Vertex 2}
    (hy : y ∈ B.vertices) (hz : z ∈ B.vertices)
    (h : ReachIn ω ↑B.vertices y ((planarPartCube ω z).planarAnchor ω)) :
    y ∈ planarBoxCluster ω B :=
  ⟨hy, h.trans (reachIn_planarAnchor_of_boxResolved hP hBr hz hy)⟩

/-- Anchors of partition cubes inside a resolved square belong to its cluster. -/
theorem planarAnchor_mem_planarBoxCluster (hP : PlanarPartitionEvent ω) {B : IntegerCube 2}
    (hBr : PlanarBoxResolved ω B) {z : Vertex 2}
    (hz : z ∈ B.vertices) : (planarPartCube ω z).planarAnchor ω ∈ planarBoxCluster ω B := by
  have hmem := ((planarPartCube ω z).planarAnchor_spec (planarPartCube_meshed hP z).1
    (planarPartCube_large hP z)).1
  have hB' : (planarPartCube ω z).planarAnchor ω ∈ B.vertices := hBr z hz hmem
  exact mem_planarBoxCluster_of_reachIn hP hBr hB' hz
    ⟨SimpleGraph.Walk.nil, fun v hv => by
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      exact hv ▸ hB'⟩

/-- Every open path inside `B` from a vertex of the cluster stays in the cluster. -/
theorem reachIn_planarBoxCluster (hP : PlanarPartitionEvent ω) {B : IntegerCube 2} 
    (hBr : PlanarBoxResolved ω B) {S : Set (Vertex 2)}
    (hSB : S ⊆ ↑B.vertices) {a b : Vertex 2} (ha : a ∈ planarBoxCluster ω B)
    (h : ReachIn ω S a b) : ReachIn ω (S ∩ planarBoxCluster ω B) a b := by
  obtain ⟨W, hW⟩ := h
  refine ⟨W, fun y hy => ⟨hW y hy, ?_⟩⟩
  have hya : ReachIn ω ↑B.vertices y a := ((reachIn_of_mem_support W hW hy).mono hSB).symm
  exact mem_planarBoxCluster_of_reachIn hP hBr (hSB (hW y hy)) ha.1 (hya.trans ha.2)

/-- The cluster of a resolved square contains every vertex of the square joined to it by an open
edge. -/
theorem mem_planarBoxCluster_of_adj (hP : PlanarPartitionEvent ω) {B : IntegerCube 2} 
    (hBr : PlanarBoxResolved ω B) {z y : Vertex 2}
    (hz : z ∈ planarBoxCluster ω B) (hadj : (openGraph ω).Adj z y) (hy : y ∈ B.vertices) :
    y ∈ planarBoxCluster ω B := by
  have hyz : ReachIn ω ↑B.vertices y z :=
    ⟨SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil, fun w hw => by
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hy
      · exact hz.1⟩
  exact mem_planarBoxCluster_of_reachIn hP hBr hy hz.1 (hyz.trans hz.2)

/-- The window of a partition cube inside `B`, restricted to the cluster of `B`. -/
noncomputable def planarBoxClusterWindow (ω : Configuration 2) (B : IntegerCube 2)
    (x : Vertex 2) : Finset (Vertex 2) :=
  ((planarPartCube ω x).boxWindow B).vertices.filter (· ∈ planarBoxCluster ω B)

/-- The pair window of two adjacent partition cubes inside `B`, restricted to the cluster of
`B`. -/
noncomputable def planarBoxClusterPairWindow (ω : Configuration 2) (B : IntegerCube 2)
    (x y : Vertex 2) : Finset (Vertex 2) :=
  ((planarPartCube ω x).boxPairWindow (planarPartCube ω y) B).vertices.filter
    (· ∈ planarBoxCluster ω B)

/-- The pair region of two lattice neighbours: the pair window of their partition cubes, taken
from the one of smaller scale, restricted to the cluster of `B`. -/
noncomputable def planarBoxClusterPairRegion (ω : Configuration 2) (B : IntegerCube 2)
    (x y : Vertex 2) : Finset (Vertex 2) :=
  if (planarPartCube ω x).scale ≤ (planarPartCube ω y).scale then
    planarBoxClusterPairWindow ω B x y
  else planarBoxClusterPairWindow ω B y x

theorem planarBoxClusterWindow_subset (B : IntegerCube 2) (x : Vertex 2) :
    planarBoxClusterWindow ω B x ⊆ boxClusterVertices ω B := fun _ hy =>
  mem_boxClusterVertices.2 (Finset.mem_filter.1 hy).2

theorem planarBoxClusterPairRegion_subset (B : IntegerCube 2) (x y : Vertex 2) :
    planarBoxClusterPairRegion ω B x y ⊆ boxClusterVertices ω B := by
  intro z hz
  unfold planarBoxClusterPairRegion at hz
  split_ifs at hz <;> exact mem_boxClusterVertices.2 (Finset.mem_filter.1 hz).2

/-- A vertex of the cluster of a resolved square is joined to the anchor of its partition cube by
an open path inside the window of the partition cube and the cluster. -/
theorem joinedWithin_planarBoxClusterWindow (hP : PlanarPartitionEvent ω) {B : IntegerCube 2}
    (hBr : PlanarBoxResolved ω B) {x : Vertex 2}
    (hx : x ∈ planarBoxCluster ω B) :
    JoinedWithin ω ↑(planarBoxClusterWindow ω B x) x (planarCoarseAnchor ω x) := by
  set Q := planarPartCube ω x
  have hsub := hBr x hx.1
  have h := Q.reachIn_boxWindow_of_reachIn (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x) hsub (planarPartCube_spec hP x).1
    (fun _ _ v hv hvB _ => absurd hv hvB) hx.2
  have hA : Q.planarAnchor ω ∈ planarBoxCluster ω B :=
    planarAnchor_mem_planarBoxCluster hP hBr hx.1
  have h' := reachIn_planarBoxCluster hP hBr
    (Finset.coe_subset.2 (Q.boxWindow_subset hsub)) hA h
  have hcoe : (↑(planarBoxClusterWindow ω B x) : Set (Vertex 2)) =
      ↑(Q.boxWindow B).vertices ∩ planarBoxCluster ω B := by
    ext y
    simp only [planarBoxClusterWindow, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff,
      Finset.mem_coe, Q]
  rw [hcoe]
  exact h'.symm

/-- The anchors of the partition cubes of two adjacent vertices of a resolved square, the first of
the same or smaller scale, are joined by an open path inside their pair window and the cluster. -/
theorem joinedWithin_planarBoxClusterPairWindow (hP : PlanarPartitionEvent ω)
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B)
    {x y : Vertex 2} (hx : x ∈ B.vertices) (hy : y ∈ B.vertices) (hnear : ∀ i, |x i - y i| ≤ 1)
    (hscale : (planarPartCube ω x).scale ≤ (planarPartCube ω y).scale) :
    JoinedWithin ω ↑(planarBoxClusterPairWindow ω B x y) (planarCoarseAnchor ω x)
      (planarCoarseAnchor ω y) := by
  set Q := planarPartCube ω x
  set Q' := planarPartCube ω y
  have hsub := hBr x hx
  have hsub' := hBr y hy
  have hsc2 := (planarPartCube_scales_close hP hnear).2
  have h := TriadicCube.reachIn_planarAnchor_boxPairWindow (planarPartCube_meshed hP x).1
    (planarPartCube_meshed hP y).1 (planarPartCube_large hP x) hsub hsub' hscale hsc2
    (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
  have hspec := TriadicCube.boxPairWindow_spec hsub hsub' hscale hsc2
    (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
  have hA : Q.planarAnchor ω ∈ planarBoxCluster ω B :=
    planarAnchor_mem_planarBoxCluster hP hBr hx
  have h' := reachIn_planarBoxCluster hP hBr (Finset.coe_subset.2 hspec.2.2.2) hA h
  have hcoe : (↑(planarBoxClusterPairWindow ω B x y) : Set (Vertex 2)) =
      ↑(Q.boxPairWindow Q' B).vertices ∩ planarBoxCluster ω B := by
    ext z
    simp only [planarBoxClusterPairWindow, Finset.coe_filter, Set.mem_setOf_eq,
      Set.mem_inter_iff, Finset.mem_coe, Q, Q']
  rw [hcoe]
  exact h'

private theorem box_abs_sub_le_one_of_adj {d : ℕ} {u v : Vertex d}
    (h : (nearestNeighborGraph d).Adj u v) (k : Fin d) : |u k - v k| ≤ 1 := by
  obtain ⟨l, hl | hl⟩ := h <;> subst hl <;> by_cases hkl : k = l <;> simp [LatticeProb.unit, hkl]

/-- **Coarse-graining data of a resolved integer square**: domain `B`, cluster `C(B)`, the planar
partition cubes and their anchors, the windows of the partition cubes and the pair windows of
adjacent partition cubes inside `B`, restricted to `C(B)`. -/
noncomputable def planarBoxCoarseData (hP : PlanarPartitionEvent ω) (B : IntegerCube 2) 
    (hBr : PlanarBoxResolved ω B) : CoarseData 2 ω where
  domain := B.vertices
  cluster := boxClusterVertices ω B
  cluster_subset := Finset.filter_subset _ _
  part := planarPartCube ω
  mem_part x _ := (planarPartCube_spec hP x).1
  part_subset x hx := hBr x hx
  part_eq_of_mem _ _ _ hy := planarPartCube_eq_of_mem hP hy
  anchor := planarCoarseAnchor ω
  anchor_congr x y h := by
    change (planarPartCube ω x).planarAnchor ω = (planarPartCube ω y).planarAnchor ω
    rw [h]
  anchor_mem x hx := mem_boxClusterVertices.2 (planarAnchor_mem_planarBoxCluster hP hBr hx)
  anchor_mem_part x _ := ((planarPartCube ω x).planarAnchor_spec (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x)).1
  region := planarBoxClusterWindow ω B
  joinedWithin_region x hx :=
    (joinedWithin_planarBoxClusterWindow hP hBr (mem_boxClusterVertices.1 hx)).mono
      (Finset.coe_subset.2 (Finset.subset_inter (Finset.Subset.refl _)
        (planarBoxClusterWindow_subset B x)))
  pairRegion := planarBoxClusterPairRegion ω B
  joinedWithin_pairRegion x hx y hy hadj _ := by
    have hnear : ∀ i, |x i - y i| ≤ 1 := box_abs_sub_le_one_of_adj hadj
    refine JoinedWithin.mono ?_
      (Finset.coe_subset.2 (Finset.subset_inter (Finset.Subset.refl _)
        (planarBoxClusterPairRegion_subset B x y)))
    unfold planarBoxClusterPairRegion
    split_ifs with h
    · exact joinedWithin_planarBoxClusterPairWindow hP hBr hx hy hnear h
    · exact (joinedWithin_planarBoxClusterPairWindow hP hBr hy hx
        (fun i => by rw [abs_sub_comm]; exact hnear i) (by omega)).symm

@[simp] theorem planarBoxCoarseData_cluster (hP : PlanarPartitionEvent ω) (B : IntegerCube 2)
    (hBr : PlanarBoxResolved ω B) :
    (planarBoxCoarseData hP B hBr).cluster = boxClusterVertices ω B :=
  rfl

@[simp] theorem planarBoxCoarseData_part (hP : PlanarPartitionEvent ω) (B : IntegerCube 2)
    (hBr : PlanarBoxResolved ω B) :
    (planarBoxCoarseData hP B hBr).part = planarPartCube ω :=
  rfl

@[simp] theorem planarBoxCoarseData_anchor (hP : PlanarPartitionEvent ω) (B : IntegerCube 2)
    (hBr : PlanarBoxResolved ω B) :
    (planarBoxCoarseData hP B hBr).anchor = planarCoarseAnchor ω :=
  rfl

end Rigidity.Percolation

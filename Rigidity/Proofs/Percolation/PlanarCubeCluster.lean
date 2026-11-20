import Rigidity.Proofs.Percolation.PlanarWindows
import Rigidity.Proofs.Percolation.ClusterCoarsening

/-!
# The cluster of a resolved triadic cube

A triadic cube `U` is resolved by the planar partition when it contains the partition cubes of its
vertices. The anchors of all partition cubes inside a resolved cube are then joined by open paths
inside `U`, and the cluster `C_*(U)` is the set of vertices of `U` joined inside `U` to the anchor
of their partition cube (equivalently, to any anchor inside `U`).

For functions on `C_*(U)`, the coarsening error at a vertex and the coarse gradient across an edge
are bounded by the variation over the open edges of `C_*(U)` inside the window of the partition
cube, respectively the pair window of two adjacent partition cubes; these windows lie in `U` and in
the square of side `9s` around the smaller partition cube. This is the planar form of Armstrong and
Dario, Lemmas 3.2 and 3.3, with local paths that stay inside `U`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- A triadic cube is resolved by the planar partition when it contains the partition cubes of
its vertices. -/
def PlanarResolved (ω : Configuration 2) (U : TriadicCube 2) : Prop :=
  ∀ z ∈ U.vertices, (planarPartCube ω z).scale ≤ U.scale

theorem planarPartCube_subset_of_resolved (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {z : Vertex 2} (hz : z ∈ U.vertices) :
    (planarPartCube ω z).vertices ⊆ U.vertices :=
  TriadicCube.vertices_subset_of_mem_of_scale_le (planarPartCube_spec hP z).1 hz (hU z hz)

/-- A unit step from `a` towards `b`. -/
theorem exists_step_toward (a b : ℤ) :
    ∃ c, |a - c| ≤ 1 ∧ ((a ≤ c ∧ c ≤ b) ∨ (b ≤ c ∧ c ≤ a)) ∧
      ((a = b ∧ c = b) ∨ (a ≠ b ∧ (c - b).natAbs + 1 = (a - b).natAbs)) := by
  rcases lt_trichotomy a b with h | h | h
  · exact ⟨a + 1, by rw [abs_le]; omega, by omega, by omega⟩
  · exact ⟨a, by simp, by omega, by omega⟩
  · exact ⟨a - 1, by rw [abs_le]; omega, by omega, by omega⟩

/-- **Chains in a triadic cube.** A transitive relation holding between all pairs of adjacent or
diagonal neighbours in a triadic cube holds between all pairs of its vertices. -/
theorem TriadicCube.forall_of_near (U : TriadicCube 2) (R : Vertex 2 → Vertex 2 → Prop)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ z ∈ U.vertices, ∀ z' ∈ U.vertices, (∀ i, |z i - z' i| ≤ 1) → R z z') :
    ∀ z ∈ U.vertices, ∀ z' ∈ U.vertices, R z z' := by
  suffices h : ∀ n : ℕ, ∀ z ∈ U.vertices, ∀ z' ∈ U.vertices,
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
    have hz''U : z'' ∈ U.vertices := by
      apply TriadicCube.mem_of_corner_le
      intro i
      fin_cases i
      · have h1 := TriadicCube.corner_le_of_mem hz 0
        have h2 := TriadicCube.corner_le_of_mem hz' 0
        simp only [Fin.zero_eta, e0]
        omega
      · have h1 := TriadicCube.corner_le_of_mem hz 1
        have h2 := TriadicCube.corner_le_of_mem hz' 1
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
    exact htrans _ _ _ (hstep z hz z'' hz''U hnear) (ih z'' hz''U z' hz' hdist)

/-- **Anchors inside a resolved cube.** The anchors of the partition cubes of any two vertices
of a resolved triadic cube are joined by an open path inside the cube. -/
theorem reachIn_planarAnchor_of_resolved (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {z z' : Vertex 2} (hz : z ∈ U.vertices) (hz' : z' ∈ U.vertices) :
    ReachIn ω U.vertices ((planarPartCube ω z).planarAnchor ω)
      ((planarPartCube ω z').planarAnchor ω) := by
  refine U.forall_of_near (fun z z' => ReachIn ω U.vertices ((planarPartCube ω z).planarAnchor ω)
    ((planarPartCube ω z').planarAnchor ω)) (fun a b c h1 h2 => h1.trans h2) ?_ z hz z' hz'
  intro z hz z' hz' hnear
  obtain ⟨hsc1, hsc2⟩ := planarPartCube_scales_close hP hnear
  rcases le_total (planarPartCube ω z).scale (planarPartCube ω z').scale with h | h
  · exact (TriadicCube.reachIn_planarAnchor_pairWindow (planarPartCube_meshed hP z).1
      (planarPartCube_meshed hP z').1 (planarPartCube_large hP z) (hU z hz)
      (planarPartCube_subset_of_resolved hP hU hz) (planarPartCube_subset_of_resolved hP hU hz')
      h hsc2 (planarPartCube_spec hP z).1 (planarPartCube_spec hP z').1 hnear).mono
      (TriadicCube.pairWindow_spec (hU z hz) (planarPartCube_subset_of_resolved hP hU hz)
        (planarPartCube_subset_of_resolved hP hU hz') h hsc2 (planarPartCube_spec hP z).1
        (planarPartCube_spec hP z').1 hnear).2.2.2
  · have hnear' : ∀ i, |z' i - z i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    exact ((TriadicCube.reachIn_planarAnchor_pairWindow (planarPartCube_meshed hP z').1
      (planarPartCube_meshed hP z).1 (planarPartCube_large hP z') (hU z' hz')
      (planarPartCube_subset_of_resolved hP hU hz') (planarPartCube_subset_of_resolved hP hU hz)
      h hsc1 (planarPartCube_spec hP z').1 (planarPartCube_spec hP z).1 hnear').mono
      (TriadicCube.pairWindow_spec (hU z' hz') (planarPartCube_subset_of_resolved hP hU hz')
        (planarPartCube_subset_of_resolved hP hU hz) h hsc1 (planarPartCube_spec hP z').1
        (planarPartCube_spec hP z).1 hnear').2.2.2).symm

/-- The cluster `C_*(U)` of a triadic cube: the vertices of `U` joined inside `U` to the anchor of
their partition cube. -/
def planarCubeCluster (ω : Configuration 2) (U : TriadicCube 2) : Set (Vertex 2) :=
  {x | x ∈ U.vertices ∧ ReachIn ω U.vertices x ((planarPartCube ω x).planarAnchor ω)}

/-- A vertex of a resolved cube joined inside it to some anchor belongs to its cluster. -/
theorem mem_planarCubeCluster_of_reachIn (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {y z : Vertex 2} (hy : y ∈ U.vertices) (hz : z ∈ U.vertices)
    (h : ReachIn ω U.vertices y ((planarPartCube ω z).planarAnchor ω)) :
    y ∈ planarCubeCluster ω U :=
  ⟨hy, h.trans (reachIn_planarAnchor_of_resolved hP hU hz hy)⟩

/-- Anchors of partition cubes inside a resolved cube belong to its cluster. -/
theorem planarAnchor_mem_planarCubeCluster (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {z : Vertex 2} (hz : z ∈ U.vertices) :
    (planarPartCube ω z).planarAnchor ω ∈ planarCubeCluster ω U := by
  have hmem := ((planarPartCube ω z).planarAnchor_spec (planarPartCube_meshed hP z).1
    (planarPartCube_large hP z)).1
  have hU' := planarPartCube_subset_of_resolved hP hU hz hmem
  exact mem_planarCubeCluster_of_reachIn hP hU hU' hz
    ⟨SimpleGraph.Walk.nil, fun v hv => by
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      exact hv ▸ hU'⟩

/-- Every open path inside `U` from a vertex of the cluster stays in the cluster. -/
theorem reachIn_planarCubeCluster (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {S : Set (Vertex 2)} (hSU : S ⊆ U.vertices) {a b : Vertex 2}
    (ha : a ∈ planarCubeCluster ω U) (h : ReachIn ω S a b) :
    ReachIn ω (S ∩ planarCubeCluster ω U) a b := by
  obtain ⟨W, hW⟩ := h
  refine ⟨W, fun y hy => ⟨hW y hy, ?_⟩⟩
  have hya : ReachIn ω U.vertices y a := ((reachIn_of_mem_support W hW hy).mono hSU).symm
  exact mem_planarCubeCluster_of_reachIn hP hU (hSU (hW y hy)) ha.1 (hya.trans ha.2)

/-- The window of a partition cube restricted to the cluster of `U`. -/
noncomputable def planarClusterWindow (ω : Configuration 2) (U : TriadicCube 2) (x : Vertex 2) :
    Finset (Vertex 2) :=
  ((planarPartCube ω x).window U).vertices.filter (· ∈ planarCubeCluster ω U)

/-- The pair window of two adjacent partition cubes restricted to the cluster of `U`. -/
noncomputable def planarClusterPairWindow (ω : Configuration 2) (U : TriadicCube 2)
    (x y : Vertex 2) : Finset (Vertex 2) :=
  ((planarPartCube ω x).pairWindow (planarPartCube ω y) U).vertices.filter
    (· ∈ planarCubeCluster ω U)

/-- **Coarsening error inside a resolved cube** (planar form of Armstrong and Dario, Lemma 3.2).
At a vertex of the cluster of a resolved cube, a function differs from its value at the anchor of
the partition cube by at most its variation over the open edges of the cluster inside the window
of the partition cube. -/
theorem abs_sub_coarseAnchor_le_clusterWindow (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {x : Vertex 2} (hx : x ∈ planarCubeCluster ω U)
    (w : Vertex 2 → ℝ) :
    |w x - w (planarCoarseAnchor ω x)| ≤ edgeVariationIn ω (planarClusterWindow ω U x) w := by
  set Q := planarPartCube ω x
  have hsub := planarPartCube_subset_of_resolved hP hU hx.1
  have h := Q.reachIn_window_of_reachIn (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x) (hU x hx.1) hsub (planarPartCube_spec hP x).1 hx.2
  have hA : Q.planarAnchor ω ∈ planarCubeCluster ω U :=
    planarAnchor_mem_planarCubeCluster hP hU hx.1
  have h' := reachIn_planarCubeCluster hP hU (Q.window_subset hsub) hA h
  have hcoe : (↑(planarClusterWindow ω U x) : Set (Vertex 2)) =
      ↑(Q.window U).vertices ∩ planarCubeCluster ω U := by
    ext y
    simp only [planarClusterWindow, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff,
      Finset.mem_coe, Q]
  rw [abs_sub_comm]
  exact abs_sub_le_edgeVariationIn _ w (hcoe ▸ h')

/-- **Coarse gradient inside a resolved cube** (planar form of Armstrong and Dario, Lemma 3.3).
For two adjacent vertices of a resolved cube, the first with the partition cube of the same or
smaller scale, the coarsened values differ by at most the variation over the open edges of the
cluster inside the pair window of the two partition cubes. -/
theorem abs_coarseAnchor_sub_le_clusterPairWindow (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) {x y : Vertex 2} (hx : x ∈ U.vertices)
    (hy : y ∈ U.vertices) (hnear : ∀ i, |x i - y i| ≤ 1)
    (hscale : (planarPartCube ω x).scale ≤ (planarPartCube ω y).scale) (w : Vertex 2 → ℝ) :
    |w (planarCoarseAnchor ω x) - w (planarCoarseAnchor ω y)| ≤
      edgeVariationIn ω (planarClusterPairWindow ω U x y) w := by
  set Q := planarPartCube ω x
  set Q' := planarPartCube ω y
  have hsub := planarPartCube_subset_of_resolved hP hU hx
  have hsub' := planarPartCube_subset_of_resolved hP hU hy
  have hsc2 := (planarPartCube_scales_close hP hnear).2
  have h := TriadicCube.reachIn_planarAnchor_pairWindow (planarPartCube_meshed hP x).1
    (planarPartCube_meshed hP y).1 (planarPartCube_large hP x) (hU x hx) hsub hsub' hscale hsc2
    (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
  have hspec := TriadicCube.pairWindow_spec (hU x hx) hsub hsub' hscale hsc2
    (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
  have hA : Q.planarAnchor ω ∈ planarCubeCluster ω U :=
    planarAnchor_mem_planarCubeCluster hP hU hx
  have h' := reachIn_planarCubeCluster hP hU hspec.2.2.2 hA h
  have hcoe : (↑(planarClusterPairWindow ω U x y) : Set (Vertex 2)) =
      ↑(Q.pairWindow Q' U).vertices ∩ planarCubeCluster ω U := by
    ext z
    simp only [planarClusterPairWindow, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff,
      Finset.mem_coe, Q, Q']
  exact abs_sub_le_edgeVariationIn _ w (hcoe ▸ h')

/-- Surrounding squares of a cube lie in the square of side `9s` around it. -/
theorem TriadicCube.subset_ninefold_of_mem_planarSquares {Q : TriadicCube 2} {R : IntegerCube 2}
    (hR : R ∈ Q.planarSquares) : R.vertices ⊆ Q.ninefold.vertices := by
  intro z hz
  rw [← Finset.mem_coe, TriadicCube.mem_ninefold]
  intro i
  obtain ⟨-, -, hc⟩ := (TriadicCube.mem_planarSquares).1 hR
  have hzi := ((IntegerCube.mem_vertices _ z).1 hz) i
  have hci := hc i
  rw [abs_le]
  constructor <;> omega

end Rigidity.Percolation

import Rigidity.Proofs.Percolation.ClusterCoarsening
import Rigidity.Percolation.TriadicStoppingNeighbors

/-!
# The planar partition and coarsened functions

For a configuration in which every vertex lies in a unique maximal stopping cube of the good meshed
cubes, `planarPartCube ω x` is that cube. It is meshed, of scale at least `8`, and neighbouring
partition cubes differ by at most one scale. The coarsening of a function `w` is its value at the
anchor of the partition cube; for vertices of infinite open clusters, the coarsening error is
controlled by the total variation of `w` over the open edges of the square of side `9s` around the
partition cube, and the coarsened function changes between neighbouring cubes by at most the total
variation over the square around the smaller one.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

/-- The good meshed cubes. -/
def planarGoodCubes (ω : Configuration 2) : Set (TriadicCube 2) :=
  TriadicCube.goodOfWellConnected (planarMeshedFamily ω)

/-- Every vertex lies in a unique maximal stopping cube of the good meshed cubes. -/
def PlanarPartitionEvent (ω : Configuration 2) : Prop :=
  ∀ x : Vertex 2, ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarGoodCubes ω)

/-- The partition event holds almost surely in the supercritical regime. -/
theorem ae_planarPartitionEvent {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᵐ ω ∂(latticeBondLaw 2 p), PlanarPartitionEvent ω :=
  (planar_meshed_partition_estimates hpc).1

/-- The partition cube of a vertex. -/
noncomputable def planarPartCube (ω : Configuration 2) (x : Vertex 2) : TriadicCube 2 :=
  if h : ∃ Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarGoodCubes ω) then
    Classical.choose h
  else ⟨0, x⟩

theorem planarPartCube_spec {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    x ∈ (planarPartCube ω x).vertices ∧
      (planarPartCube ω x).IsMaximalStopping (planarGoodCubes ω) := by
  have h : ∃ Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarGoodCubes ω) :=
    (hP x).exists
  unfold planarPartCube
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The partition cube is the unique maximal stopping cube containing the vertex. -/
theorem planarPartCube_eq {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {x : Vertex 2}
    {Q : TriadicCube 2} (hx : x ∈ Q.vertices) (hQ : Q.IsMaximalStopping (planarGoodCubes ω)) :
    planarPartCube ω x = Q :=
  (hP x).unique (planarPartCube_spec hP x) ⟨hx, hQ⟩

/-- Vertices of a partition cube have that partition cube. -/
theorem planarPartCube_eq_of_mem {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x y : Vertex 2} (hy : y ∈ (planarPartCube ω x).vertices) :
    planarPartCube ω y = planarPartCube ω x :=
  planarPartCube_eq hP hy (planarPartCube_spec hP x).2

/-- Partition cubes are good. -/
theorem planarPartCube_mem_good {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (x : Vertex 2) : planarPartCube ω x ∈ planarGoodCubes ω :=
  (planarPartCube_spec hP x).2.1.1 (TriadicCube.mem_influence_self _)

/-- Partition cubes are meshed and have scale at least `8`. -/
theorem planarPartCube_meshed {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (x : Vertex 2) :
    (planarPartCube ω x).planarMeshed ω ∧ 8 ≤ (planarPartCube ω x).scale := by
  obtain ⟨hpos, ⟨h7, hmesh⟩, hchild⟩ := planarPartCube_mem_good hP x
  refine ⟨hmesh, ?_⟩
  have hc := (hchild fun _ => 0).1
  change 7 ≤ (planarPartCube ω x).scale - 1 at hc
  omega

/-- Partition cubes have side at least `1000`. -/
theorem planarPartCube_large {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    1000 ≤ 3 ^ (planarPartCube ω x).scale :=
  calc 1000 ≤ 3 ^ 8 := by norm_num
    _ ≤ 3 ^ (planarPartCube ω x).scale :=
      Nat.pow_le_pow_right (by norm_num) (planarPartCube_meshed hP x).2

/-- Neighbouring partition cubes differ by at most one scale. -/
theorem planarPartCube_scales_close {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x y : Vertex 2} (hnear : ∀ i, |x i - y i| ≤ 1) :
    (planarPartCube ω x).scale ≤ (planarPartCube ω y).scale + 1 ∧
      (planarPartCube ω y).scale ≤ (planarPartCube ω x).scale + 1 :=
  (planarPartCube_spec hP x).2.1.scales_close_of_near (planarPartCube_spec hP y).2.1
    (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear

/-- The anchor of the partition cube of a vertex. -/
noncomputable def planarCoarseAnchor (ω : Configuration 2) (x : Vertex 2) : Vertex 2 :=
  (planarPartCube ω x).planarAnchor ω

/-- **Coarsening error at a cluster vertex.** -/
theorem abs_sub_coarseAnchor_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x : Vertex 2} (hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite)
    (w : Vertex 2 → ℝ) :
    |w x - w (planarCoarseAnchor ω x)| ≤
      edgeVariationIn ω (planarPartCube ω x).ninefold.vertices w :=
  TriadicCube.abs_sub_planarAnchor_le (planarPartCube_meshed hP x).1 (planarPartCube_large hP x)
    (planarPartCube_spec hP x).1 hinf w

/-- **Coarse gradient between neighbouring vertices.** -/
theorem abs_coarseAnchor_sub_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x y : Vertex 2} (hnear : ∀ i, |x i - y i| ≤ 1)
    (hscale : (planarPartCube ω x).scale ≤ (planarPartCube ω y).scale) (w : Vertex 2 → ℝ) :
    |w (planarCoarseAnchor ω x) - w (planarCoarseAnchor ω y)| ≤
      edgeVariationIn ω (planarPartCube ω x).ninefold.vertices w :=
  TriadicCube.abs_planarAnchor_sub_le (planarPartCube_meshed hP x).1
    (planarPartCube_meshed hP y).1 (planarPartCube_large hP x) hscale
    (planarPartCube_scales_close hP hnear).2 (planarPartCube_spec hP x).1
    (planarPartCube_spec hP y).1 hnear w

end Rigidity.Percolation

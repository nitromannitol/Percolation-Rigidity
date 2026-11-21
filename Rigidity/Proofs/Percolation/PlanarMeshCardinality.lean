import Rigidity.Proofs.Percolation.PlanarMesh

/-!
# Largest clusters in planar crossing meshes

A crossing cluster contains at least a full crossing path. Other clusters are confined to small
cubes when all strips are crossed.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- A planar crossing cluster contains at least `2N + 1` vertices. -/
theorem crossingCluster_card_lower {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {V : Set (Vertex 2)} (hV : IsCrossingCluster ω x N V) : 2 * N + 1 ≤ V.ncard := by
  classical
  obtain ⟨⟨u, hu, hVeq⟩, hcross⟩ := hV
  have hVsub : V ⊆ cubeAt x N := by
    intro z hz
    rw [hVeq] at hz
    exact (reachIn_of_reachable_openIn hu hz).end_mem
  have hVfin : V.Finite := (Rigidity.Proofs.S3.finite_cubeAt x N).subset hVsub
  obtain ⟨⟨a, ha, haf⟩, ⟨b, hb, hbf⟩⟩ := hcross 0
  rw [hVeq] at ha hb
  obtain ⟨P⟩ := ha.symm.trans hb
  have hcoord := Rigidity.Proofs.S3.abs_getVert_sub_le
    ((Rigidity.Proofs.S3.openIn_le ω _).trans (openGraph_le ω)) P.bypass P.bypass.length 0
  rw [SimpleGraph.Walk.getVert_length, hbf, haf, abs_le] at hcoord
  have hlen : 2 * N ≤ P.bypass.length := by omega
  have hsub : P.bypass.support.toFinset ⊆ hVfin.toFinset := by
    intro z hz
    have hz' : z ∈ P.bypass.support := List.mem_toFinset.mp hz
    apply hVfin.mem_toFinset.mpr
    rw [hVeq]
    exact ha.trans ⟨P.bypass.takeUntil z hz'⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup P.bypass_isPath.support_nodup,
    SimpleGraph.Walk.length_support, ← Set.ncard_eq_toFinset_card V hVfin] at hcard
  omega

/-- A cluster disjoint from the crossing cluster is confined to a cube of the strip width. -/
theorem noncrossing_cluster_subset_cube {ω : Configuration 2} {x : Vertex 2} {N w : ℕ}
    {V : Set (Vertex 2)} (hmesh : HasStripCrossings ω x N w)
    (hV : IsCrossingCluster ω x N V) {a : Vertex 2} (ha : a ∈ cubeAt x N)
    (haV : a ∉ V) :
    {b | (openIn ω (cubeAt x N)).Reachable a b} ⊆ cubeAt a w := by
  intro b hab j
  by_contra h
  have hdisp : (w : ℤ) < |b j - a j| := lt_of_not_ge h
  exact haV (mem_crossingCluster_of_displacement hmesh hV
    (reachIn_of_reachable_openIn ha hab) hdisp)

/-- A cluster disjoint from the crossing cluster has at most `(2w + 1)²` vertices. -/
theorem noncrossing_cluster_card_le {ω : Configuration 2} {x : Vertex 2} {N w : ℕ}
    {V : Set (Vertex 2)} (hmesh : HasStripCrossings ω x N w)
    (hV : IsCrossingCluster ω x N V) {a : Vertex 2} (ha : a ∈ cubeAt x N)
    (haV : a ∉ V) :
    {b | (openIn ω (cubeAt x N)).Reachable a b}.ncard ≤ (2 * w + 1) ^ 2 := by
  have hfin := Rigidity.Proofs.S3.finite_cubeAt a w
  have hcard := Set.ncard_le_ncard (noncrossing_cluster_subset_cube hmesh hV ha haV) hfin
  have hset : cubeAt a w = ↑(Rigidity.Proofs.S3.cubeFinset a w) := by
    ext y
    exact Rigidity.Proofs.S3.mem_cubeFinset.symm
  rw [hset, Set.ncard_coe_finset, Rigidity.Proofs.S3.card_cubeFinset] at hcard
  exact hcard

/-- A crossing mesh with sufficiently narrow strips has a largest crossing cluster. -/
theorem crossingCluster_isLargest_of_mesh {ω : Configuration 2} {x : Vertex 2} {N w : ℕ}
    {V : Set (Vertex 2)} (hmesh : HasStripCrossings ω x N w)
    (hV : IsCrossingCluster ω x N V) (hsize : (2 * w + 1) ^ 2 ≤ 2 * N + 1) :
    IsLargestClusterIn ω (cubeAt x N) V := by
  refine ⟨hV.1, fun a ha => ?_⟩
  by_cases haV : a ∈ V
  · obtain ⟨⟨u, _, hVeq⟩, _⟩ := hV
    rw [hVeq] at haV ⊢
    have heq : {b | (openIn ω (cubeAt x N)).Reachable a b} =
        {b | (openIn ω (cubeAt x N)).Reachable u b} := by
      ext b
      exact ⟨fun hab => haV.trans hab, fun hub => haV.symm.trans hub⟩
    rw [heq]
  · exact (noncrossing_cluster_card_le hmesh hV ha haV).trans
      (hsize.trans (crossingCluster_card_lower hV))

/-- A narrow crossing mesh makes the cube good. -/
theorem isGoodSubcube_of_mesh {ω : Configuration 2} {x : Vertex 2} {N w : ℕ}
    {V : Set (Vertex 2)} (hmesh : HasStripCrossings ω x N w)
    (hV : IsCrossingCluster ω x N V) (hsize : (2 * w + 1) ^ 2 ≤ 2 * N + 1)
    (hlength : ∀ n : ℕ, (N : ℝ) / 100 ≤ n → (2 * w + 1) ^ 2 < n + 1) :
    IsGoodSubcube ω x N := by
  refine ⟨V, crossingCluster_isLargest_of_mesh hmesh hV hsize, hV.2, ?_⟩
  intro n γ hinj hγ hn
  exact ⟨γ 0, long_path_mem_crossingCluster hmesh hV γ hinj hγ (hlength n hn),
    SimpleGraph.Reachable.refl _⟩

end Rigidity.Percolation

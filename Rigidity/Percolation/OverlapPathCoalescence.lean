import Rigidity.Percolation.TriadicSmallTestPaths
import Rigidity.Percolation.TriadicCrossingPaths

/-!
# Coalescence through an overlap

Paths in two regions can be connected through a shorter path in their
intersection, provided that paths at the shorter scale coalesce in each region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- A path has coordinate diameter at least the prescribed threshold. -/
def pathDiameterAtLeast {d : ℕ} (threshold : ℤ) (n : ℕ)
    (γ : Fin (n + 1) → Vertex d) : Prop :=
  ∃ (i j : Fin (n + 1)) (coordinate : Fin d),
    threshold ≤ |γ i coordinate - γ j coordinate|

/-- A crossing component contains a path of at least the side length minus one. -/
theorem IntegerCube.exists_diameter_path_of_crossingRoot {d : ℕ}
    (hd : 0 < d) (T : IntegerCube d) (threshold : ℤ)
    (hthreshold : threshold ≤ (T.size : ℤ) - 1)
    {ω : Configuration d} {root : Vertex d}
    (hroot : IsCrossingRoot ω (↑T.vertices)
      (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i)) root) :
    ∃ n γ, IsSelectedOpenPath ω (↑T.vertices) (pathDiameterAtLeast threshold) n γ ∧
      (openIn ω (↑T.vertices)).Reachable root (γ 0) := by
  let coordinate : Fin d := ⟨0, hd⟩
  obtain ⟨⟨y, hyT, hyl, hy⟩, ⟨z, _, hzu, hz⟩⟩ := hroot.2 coordinate
  have hyl' := ((IntegerCube.mem_lowerFace T coordinate y).mp hyl).2
  have hzu' := ((IntegerCube.mem_upperFace T coordinate z).mp hzu).2
  have hsep : threshold ≤ |y coordinate - z coordinate| := by
    have hbound := neg_abs_le (y coordinate - z coordinate)
    omega
  let walk := (hy.symm.trans hz).some
  let γ : Fin (walk.length + 1) → Vertex d := fun j => walk.getVert j.val
  have hfirst : γ 0 = y := by simp only [γ, Fin.val_zero, SimpleGraph.Walk.getVert_zero]
  have hlast : γ (Fin.last walk.length) = z := by
    simp only [γ, Fin.val_last, SimpleGraph.Walk.getVert_length]
  refine ⟨walk.length, γ, ?_, ?_⟩
  · refine ⟨⟨0, Fin.last walk.length, coordinate, ?_⟩, ?_, ?_⟩
    · simpa only [hfirst, hlast] using hsep
    · simpa only [hfirst] using hyT
    · intro i
      exact walk.adj_getVert_succ i.isLt
  · simpa only [hfirst] using hy

/-- A selected path in a smaller region is a selected path in a larger region. -/
theorem IsSelectedOpenPath.mono_region {d : ℕ} {ω : Configuration d}
    {B C : Set (Vertex d)} {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {n : ℕ} {γ : Fin (n + 1) → Vertex d}
    (h : IsSelectedOpenPath ω B large n γ) (hBC : B ⊆ C) :
    IsSelectedOpenPath ω C large n γ := by
  refine ⟨h.1, hBC h.2.1, ?_⟩
  intro i
  obtain ⟨hedge, hleft, hright⟩ := h.2.2 i
  exact ⟨hedge, hBC hleft, hBC hright⟩

/-- Coalescence at a shorter scale connects selected paths through a path in
the overlap whose ambient component contains the root. -/
theorem connectsSelectedPaths_of_overlap {d : ℕ} {ω : Configuration d}
    {B C D : Set (Vertex d)} {root : Vertex d}
    {large small : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (hDB : D ⊆ B) (hDC : D ⊆ C)
    (hlarge : ∀ n γ, large n γ → small n γ)
    (hB : LargePathsCoalesce ω B small)
    (hC : LargePathsCoalesce ω C small)
    (hroot : HasAnchoredLargePath ω C C root small)
    (hbridge : HasSelectedOpenPath ω B large → HasSelectedOpenPath ω D small) :
    ConnectsSelectedPaths ω B C root large := by
  intro n γ hγ hstart hadj
  have hγB : IsSelectedOpenPath ω B small n γ := ⟨hlarge n γ hγ, hstart, hadj⟩
  obtain ⟨m, η, hη⟩ := hbridge ⟨n, γ, hγ, hstart, hadj⟩
  obtain ⟨k, ξ, hξ, hrootξ⟩ := hroot
  have hηB := hη.mono_region hDB
  have hηC := hη.mono_region hDC
  exact ⟨η 0, hηB.2.1, hB n γ hγB m η hηB,
    hrootξ.trans (hC k ξ hξ m η hηC)⟩

/-- A crossing overlap and shorter-scale coalescence connect every large test
path to the ambient crossing component. -/
theorem TriadicCube.connectsSelectedPaths_of_crossing_overlap {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) (hside : 2 ≤ Q.side)
    (R T : IntegerCube d) (threshold : ℤ)
    (hthreshold : threshold ≤ (T.size : ℤ) - 1)
    (hscale : 10 * threshold ≤ Q.side)
    (hTQ : (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices)
    (hTR : (↑T.vertices : Set (Vertex d)) ⊆ R.vertices)
    {ω : Configuration d} {root overlapRoot : Vertex d}
    (hroot : IsCrossingRoot ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root)
    (hoverlap : IsCrossingRoot ω (↑T.vertices)
      (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i)) overlapRoot)
    (hQ : LargePathsCoalesce ω Q.vertices (pathDiameterAtLeast threshold))
    (hR : LargePathsCoalesce ω (↑R.vertices) (pathDiameterAtLeast threshold)) :
    ConnectsSelectedPaths ω (↑R.vertices) Q.vertices root Q.largePath := by
  have hlarge : ∀ n γ, Q.largePath n γ → pathDiameterAtLeast threshold n γ := by
    intro n γ hγ
    obtain ⟨i, j, coordinate, hsep⟩ := hγ
    exact ⟨i, j, coordinate, by omega⟩
  obtain ⟨n, γ, hγ, hrootγ⟩ := Q.exists_selected_path_of_crossingRoot hd hside hroot
  obtain ⟨m, η, hη, _⟩ := T.exists_diameter_path_of_crossingRoot hd threshold
    hthreshold hoverlap
  apply connectsSelectedPaths_of_overlap hTR hTQ hlarge hR hQ
  · exact ⟨n, γ, ⟨hlarge n γ hγ.1, hγ.2⟩, hrootγ⟩
  · intro _
    exact ⟨m, η, hη⟩

/-- Crossing overlap cubes and shorter-scale coalescence imply
well-connectedness of the ambient cube. -/
theorem TriadicCube.wellConnectedIn_of_crossing_overlaps {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) (hside : 2 ≤ Q.side)
    (interior : Set (Vertex d)) (threshold : ℤ)
    (hscale : 10 * threshold ≤ Q.side)
    {ω : Configuration d} {root : Vertex d}
    (hroot : IsCrossingRoot ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root)
    (hQ : LargePathsCoalesce ω Q.vertices (pathDiameterAtLeast threshold))
    (htests : ∀ R ∈ Q.testCubes interior,
      CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
        (fun i => ↑(R.upperFace i)) ∧
      LargePathsCoalesce ω (↑R.vertices) (pathDiameterAtLeast threshold) ∧
      ∃ (T : IntegerCube d) (overlapRoot : Vertex d),
        threshold ≤ (T.size : ℤ) - 1 ∧
        (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices ∧
        (↑T.vertices : Set (Vertex d)) ⊆ R.vertices ∧
        IsCrossingRoot ω (↑T.vertices)
          (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i)) overlapRoot) :
    Q.wellConnectedIn interior ω := by
  apply (Q.wellConnectedIn_iff interior ω).2
  refine ⟨root, hroot, ?_⟩
  intro R hR
  obtain ⟨hcross, hcoal, T, overlapRoot, hthreshold, hTQ, hTR, hoverlap⟩ := htests R hR
  exact ⟨hcross, Q.connectsSelectedPaths_of_crossing_overlap hd hside R T threshold
    hthreshold hscale hTQ hTR hroot hoverlap hQ hcoal⟩

end Rigidity.Percolation

import Rigidity.Percolation.OverlapPathCoalescence

/-!
# Gluing local path coalescence

Coalescence in overlapping regions can be propagated along a connected graph
of regions. This applies when each neighboring pair shares a selected path.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- Connectivity inside a region persists inside a larger region. -/
theorem reachable_openIn_mono {d : ℕ} {ω : Configuration d}
    {B C : Set (Vertex d)} (hBC : B ⊆ C) {x y : Vertex d}
    (h : (openIn ω B).Reachable x y) : (openIn ω C).Reachable x y := by
  apply SimpleGraph.Reachable.mono ?_ h
  intro x y hxy
  exact ⟨hxy.1, hBC hxy.2.1, hBC hxy.2.2⟩

/-- Selected paths in neighboring regions connect in the ambient region if
local coalescence holds and the regions share a selected path. -/
theorem selectedPaths_reachable_of_overlap {d : ℕ} {ω : Configuration d}
    {B C D : Set (Vertex d)}
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (hBD : B ⊆ D) (hCD : C ⊆ D)
    (hB : LargePathsCoalesce ω B large) (hC : LargePathsCoalesce ω C large)
    (hbridge : HasSelectedOpenPath ω (B ∩ C) large)
    {n m : ℕ} {γ : Fin (n + 1) → Vertex d} {η : Fin (m + 1) → Vertex d}
    (hγ : IsSelectedOpenPath ω B large n γ) (hη : IsSelectedOpenPath ω C large m η) :
    (openIn ω D).Reachable (γ 0) (η 0) := by
  obtain ⟨k, ξ, hξ⟩ := hbridge
  have hξB := hξ.mono_region Set.inter_subset_left
  have hξC := hξ.mono_region Set.inter_subset_right
  exact (reachable_openIn_mono hBD (hB n γ hγ k ξ hξB)).trans
    (reachable_openIn_mono hCD (hC k ξ hξC m η hη))

/-- Local selected paths in graph-connected regions belong to one ambient
component when every region has a selected path and neighbors share one. -/
theorem selectedPaths_reachable_of_connected_cover {d : ℕ} {ι : Type*}
    {ω : Configuration d} (G : SimpleGraph ι) (B : ι → Set (Vertex d))
    (D : Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hBD : ∀ i, B i ⊆ D)
    (hcoal : ∀ i, LargePathsCoalesce ω (B i) large)
    (hpath : ∀ i, HasSelectedOpenPath ω (B i) large)
    (hbridge : ∀ i j, G.Adj i j → HasSelectedOpenPath ω (B i ∩ B j) large)
    {i j : ι} (hij : G.Reachable i j)
    {n m : ℕ} {γ : Fin (n + 1) → Vertex d} {η : Fin (m + 1) → Vertex d}
    (hγ : IsSelectedOpenPath ω (B i) large n γ)
    (hη : IsSelectedOpenPath ω (B j) large m η) :
    (openIn ω D).Reachable (γ 0) (η 0) := by
  obtain ⟨w⟩ := hij
  induction w generalizing n γ with
  | nil =>
    exact reachable_openIn_mono (hBD _) (hcoal _ n γ hγ m η hη)
  | @cons a b c hab w ih =>
    obtain ⟨k, ξ, hξ⟩ := hpath b
    exact (selectedPaths_reachable_of_overlap (hBD a) (hBD b) (hcoal a) (hcoal b)
      (hbridge a b hab) hγ hξ).trans (ih hξ hη)

/-- A connected cover gives ambient coalescence when every selected ambient
path connects to a selected path in one of its regions. -/
theorem largePathsCoalesce_of_connected_cover {d : ℕ} {ι : Type*}
    {ω : Configuration d} (G : SimpleGraph ι) (B : ι → Set (Vertex d))
    (D : Set (Vertex d))
    (small large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hBD : ∀ i, B i ⊆ D)
    (hcoal : ∀ i, LargePathsCoalesce ω (B i) small)
    (hpath : ∀ i, HasSelectedOpenPath ω (B i) small)
    (hbridge : ∀ i j, G.Adj i j → HasSelectedOpenPath ω (B i ∩ B j) small)
    (hconnected : ∀ i j, G.Reachable i j)
    (hsegment : ∀ n γ, IsSelectedOpenPath ω D large n γ →
      ∃ i m η, IsSelectedOpenPath ω (B i) small m η ∧
        (openIn ω D).Reachable (γ 0) (η 0)) :
    LargePathsCoalesce ω D large := by
  intro n γ hγ m η hη
  obtain ⟨i, k, ξ, hξ, hγξ⟩ := hsegment n γ hγ
  obtain ⟨j, l, ζ, hζ, hηζ⟩ := hsegment m η hη
  exact hγξ.trans ((selectedPaths_reachable_of_connected_cover G B D small
    hBD hcoal hpath hbridge (hconnected i j) hξ hζ).trans hηζ.symm)

/-- A crossing cube inside a region supplies a selected path whose coordinate
diameter is at least any threshold below its side length. -/
theorem IntegerCube.hasSelectedOpenPath_of_crossing_subset {d : ℕ}
    (hd : 0 < d) (T : IntegerCube d) (threshold : ℤ)
    (hthreshold : threshold ≤ (T.size : ℤ) - 1)
    {ω : Configuration d} {B : Set (Vertex d)}
    (hTB : (↑T.vertices : Set (Vertex d)) ⊆ B)
    (hcross : HasCrossingComponent ω (↑T.vertices)
      (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))) :
    HasSelectedOpenPath ω B (pathDiameterAtLeast threshold) := by
  obtain ⟨root, hroot⟩ := hcross
  obtain ⟨n, γ, hγ, _⟩ := T.exists_diameter_path_of_crossingRoot hd threshold
    hthreshold hroot
  exact ⟨n, γ, hγ.mono_region hTB⟩

/-- Crossing cubes in neighboring overlaps provide the bridges needed to glue
their local coalescence estimates. -/
theorem largePathsCoalesce_of_connected_crossing_cover {d : ℕ} {ι : Type*}
    (hd : 0 < d) {ω : Configuration d} (G : SimpleGraph ι)
    (B : ι → Set (Vertex d)) (D : Set (Vertex d)) (threshold : ℤ)
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hBD : ∀ i, B i ⊆ D)
    (hcoal : ∀ i, LargePathsCoalesce ω (B i) (pathDiameterAtLeast threshold))
    (hpath : ∀ i, HasSelectedOpenPath ω (B i) (pathDiameterAtLeast threshold))
    (hoverlap : ∀ i j, G.Adj i j → ∃ T : IntegerCube d,
      threshold ≤ (T.size : ℤ) - 1 ∧
      (↑T.vertices : Set (Vertex d)) ⊆ B i ∩ B j ∧
      HasCrossingComponent ω (↑T.vertices)
        (fun k => ↑(T.lowerFace k)) (fun k => ↑(T.upperFace k)))
    (hconnected : ∀ i j, G.Reachable i j)
    (hsegment : ∀ n γ, IsSelectedOpenPath ω D large n γ →
      ∃ i m η, IsSelectedOpenPath ω (B i) (pathDiameterAtLeast threshold) m η ∧
        (openIn ω D).Reachable (γ 0) (η 0)) :
    LargePathsCoalesce ω D large := by
  apply largePathsCoalesce_of_connected_cover G B D (pathDiameterAtLeast threshold) large
    hBD hcoal hpath ?_ hconnected hsegment
  intro i j hij
  obtain ⟨T, hthreshold, hT, hcross⟩ := hoverlap i j hij
  exact T.hasSelectedOpenPath_of_crossing_subset hd threshold hthreshold hT hcross

end Rigidity.Percolation

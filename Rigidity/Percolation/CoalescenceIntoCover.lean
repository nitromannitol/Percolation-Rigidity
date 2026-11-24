import PercolationClusterHomogenization.Percolation.PathSegmentGeometry

/-!
# Coalescence inside a larger region

Paths in each cover region may connect in a larger ambient region. Overlapping
selected paths then connect the local components throughout the cover.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- Any two selected paths in `B` have connected starting points in `D`. -/
def LargePathsCoalesceInto {d : ℕ} (ω : Configuration d) (B D : Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) : Prop :=
  ∀ n γ, IsSelectedOpenPath ω B large n γ → ∀ m η,
    IsSelectedOpenPath ω B large m η → (openIn ω D).Reachable (γ 0) (η 0)

/-- Coalescence into a region is measurable. -/
theorem measurableSet_largePathsCoalesceInto {d : ℕ} (B D : Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) :
    MeasurableSet {ω : Configuration d | LargePathsCoalesceInto ω B D large} := by
  apply measurableSet_setOf.2
  exact Measurable.forall fun n => Measurable.forall fun γ =>
    (measurableSet_setOf.1 (measurableSet_isSelectedOpenPath B large n γ)).imp
      (Measurable.forall fun m => Measurable.forall fun η =>
        (measurableSet_setOf.1 (measurableSet_isSelectedOpenPath B large m η)).imp
          (measurableSet_setOf.1 (measurableSet_openIn_reachable D (γ 0) (η 0))))

/-- Coalescence into a region extends to every larger region. -/
theorem LargePathsCoalesceInto.mono_region {d : ℕ} {ω : Configuration d}
    {B D E : Set (Vertex d)} {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (h : LargePathsCoalesceInto ω B D large) (hDE : D ⊆ E) :
    LargePathsCoalesceInto ω B E large := by
  intro n γ hγ m η hη
  exact reachable_openIn_mono hDE (h n γ hγ m η hη)

/-- Local paths in connected cover regions coalesce in an ambient region if
neighboring cover regions share a selected path. -/
theorem selectedPaths_reachable_of_connected_cover_into {d : ℕ} {ι : Type*}
    {ω : Configuration d} (G : SimpleGraph ι) (B : ι → Set (Vertex d))
    (D : Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hcoal : ∀ i, LargePathsCoalesceInto ω (B i) D large)
    (hpath : ∀ i, HasSelectedOpenPath ω (B i) large)
    (hbridge : ∀ i j, G.Adj i j → HasSelectedOpenPath ω (B i ∩ B j) large)
    {i j : ι} (hij : G.Reachable i j)
    {n m : ℕ} {γ : Fin (n + 1) → Vertex d} {η : Fin (m + 1) → Vertex d}
    (hγ : IsSelectedOpenPath ω (B i) large n γ)
    (hη : IsSelectedOpenPath ω (B j) large m η) :
    (openIn ω D).Reachable (γ 0) (η 0) := by
  obtain ⟨w⟩ := hij
  induction w generalizing n γ with
  | nil => exact hcoal _ n γ hγ m η hη
  | @cons a b c hab w ih =>
    obtain ⟨l, ζ, hζ⟩ := hbridge a b hab
    obtain ⟨k, ξ, hξ⟩ := hpath b
    have hfirst := hcoal a n γ hγ l ζ (hζ.mono_region Set.inter_subset_left)
    have hsecond := hcoal b l ζ (hζ.mono_region Set.inter_subset_right) k ξ hξ
    exact hfirst.trans (hsecond.trans (ih hξ hη))

/-- A buffered connected cover gives coalescence in the ambient region when
local coalescence is allowed to use that region. -/
theorem largePathsCoalesce_of_buffered_cover_into {d : ℕ} {ι : Type*}
    {ω : Configuration d} (G : SimpleGraph ι) (B : ι → Set (Vertex d))
    (D : Set (Vertex d)) (R : ℤ) (hR : 0 < R)
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hcoal : ∀ i, LargePathsCoalesceInto ω (B i) D (pathDiameterAtLeast R))
    (hpath : ∀ i, HasSelectedOpenPath ω (B i) (pathDiameterAtLeast R))
    (hbridge : ∀ i j, G.Adj i j →
      HasSelectedOpenPath ω (B i ∩ B j) (pathDiameterAtLeast R))
    (hconnected : ∀ i j, G.Reachable i j)
    (hdiam : ∀ n γ, large n γ → pathDiameterAtLeast R n γ)
    (hcover : ∀ x ∈ D, ∃ i, ∀ y ∈ D, (∀ k, |y k - x k| ≤ R) → y ∈ B i) :
    LargePathsCoalesce ω D large := by
  intro n γ hγ m η hη
  obtain ⟨i, a, l, hl, hlargeγ, hmemγ⟩ :=
    hγ.exists_segment_of_buffered_cover B R hR (hdiam n γ hγ.1) hcover
  obtain ⟨j, b, k, hk, hlargeη, hmemη⟩ :=
    hη.exists_segment_of_buffered_cover B R hR (hdiam m η hη.1) hcover
  have hlocalγ := hγ.segment a l hl hlargeγ hmemγ
  have hlocalη := hη.segment b k hk hlargeη hmemη
  exact (hγ.reachable_segment_start a l hl).trans
    ((selectedPaths_reachable_of_connected_cover_into G B D (pathDiameterAtLeast R)
      hcoal hpath hbridge (hconnected i j) hlocalγ hlocalη).trans
        (hη.reachable_segment_start b k hk).symm)

end Rigidity.Percolation

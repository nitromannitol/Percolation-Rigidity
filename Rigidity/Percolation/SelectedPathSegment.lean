import Rigidity.Percolation.CoalescenceCover

/-!
# Segments of selected paths

Consecutive vertices of an open path form an open path in every region
containing them. The start of such a segment remains connected to the start
of the original path in its ambient region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- Every vertex of a selected open path is connected to its initial vertex. -/
theorem IsSelectedOpenPath.reachable_start {d : ℕ} {ω : Configuration d}
    {B : Set (Vertex d)} {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {n : ℕ} {γ : Fin (n + 1) → Vertex d} (hγ : IsSelectedOpenPath ω B large n γ)
    (i : Fin (n + 1)) : (openIn ω B).Reachable (γ 0) (γ i) := by
  have h : ∀ k (hk : k ≤ n), (openIn ω B).Reachable (γ 0) (γ ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hadj := hγ.2.2 ⟨k, hk'⟩
      exact (ih (by omega)).trans hadj.reachable
  exact h i.val (by omega)

/-- Restrict a finite path to consecutive indices. -/
def pathSegment {d : ℕ} {n : ℕ} (γ : Fin (n + 1) → Vertex d)
    (a m : ℕ) (h : a + m ≤ n) : Fin (m + 1) → Vertex d :=
  fun i => γ ⟨a + i.val, by omega⟩

/-- A path segment contained in a region is an open path in that region. -/
theorem IsSelectedOpenPath.segment {d : ℕ} {ω : Configuration d}
    {B C : Set (Vertex d)}
    {large small : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {n : ℕ} {γ : Fin (n + 1) → Vertex d} (hγ : IsSelectedOpenPath ω B large n γ)
    (a m : ℕ) (h : a + m ≤ n)
    (hsmall : small m (pathSegment γ a m h))
    (hC : ∀ i, pathSegment γ a m h i ∈ C) :
    IsSelectedOpenPath ω C small m (pathSegment γ a m h) := by
  refine ⟨hsmall, hC 0, ?_⟩
  intro i
  have hadj := hγ.2.2 ⟨a + i.val, by omega⟩
  exact ⟨hadj.1, hC i.castSucc, hC i.succ⟩

/-- A segment of a selected path is connected to the original path's start. -/
theorem IsSelectedOpenPath.reachable_segment_start {d : ℕ} {ω : Configuration d}
    {B : Set (Vertex d)} {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {n : ℕ} {γ : Fin (n + 1) → Vertex d} (hγ : IsSelectedOpenPath ω B large n γ)
    (a m : ℕ) (h : a + m ≤ n) :
    (openIn ω B).Reachable (γ 0) (pathSegment γ a m h 0) := by
  exact hγ.reachable_start ⟨a, by omega⟩

/-- Local coalescence and crossing overlaps give ambient coalescence when every
selected ambient path has a sufficiently large segment in one cover region. -/
theorem largePathsCoalesce_of_crossing_cover_segments {d : ℕ} {ι : Type*}
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
      ∃ i a m, ∃ h : a + m ≤ n,
        pathDiameterAtLeast threshold m (pathSegment γ a m h) ∧
        ∀ j, pathSegment γ a m h j ∈ B i) :
    LargePathsCoalesce ω D large := by
  apply largePathsCoalesce_of_connected_crossing_cover hd G B D threshold large
    hBD hcoal hpath hoverlap hconnected
  intro n γ hγ
  obtain ⟨i, a, m, h, hdiam, hmem⟩ := hsegment n γ hγ
  exact ⟨i, m, pathSegment γ a m h, hγ.segment a m h hdiam hmem,
    hγ.reachable_segment_start a m h⟩

end Rigidity.Percolation

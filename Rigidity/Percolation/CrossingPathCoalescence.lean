import Rigidity.Percolation.LargePathCoalescence

/-!
# Coalescence from a crossing component

If all selected paths connect to one crossing component inside a region,
they coalesce inside that region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- Paths connected to a common component coalesce inside the region. -/
theorem largePathsCoalesce_of_connectsSelectedPaths {d : ℕ} {ω : Configuration d}
    {B : Set (Vertex d)} {root : Vertex d}
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (h : ConnectsSelectedPaths ω B B root large) :
    LargePathsCoalesce ω B large := by
  intro n γ hγ m η hη
  obtain ⟨x, _, hγx, hrx⟩ := h n γ hγ.1 hγ.2.1 hγ.2.2
  obtain ⟨y, _, hηy, hry⟩ := h m η hη.1 hη.2.1 hη.2.2
  exact hγx.trans (hrx.symm.trans (hry.trans hηy.symm))

/-- A crossing component to which every selected path connects inside the region. -/
def HasCrossingComponentConnectingPaths {d : ℕ} (ω : Configuration d)
    (B : Set (Vertex d)) (lower upper : Fin d → Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) : Prop :=
  ∃ root, IsCrossingRoot ω B lower upper root ∧ ConnectsSelectedPaths ω B B root large

/-- The crossing and connection event is measurable. -/
theorem measurableSet_hasCrossingComponentConnectingPaths {d : ℕ}
    (B : Set (Vertex d)) (lower upper : Fin d → Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) :
    MeasurableSet {ω : Configuration d |
      HasCrossingComponentConnectingPaths ω B lower upper large} := by
  apply measurableSet_setOf.2
  exact Measurable.exists fun root =>
    (measurableSet_setOf.1 (measurableSet_isCrossingRoot B lower upper root)).and
      (measurableSet_setOf.1 (measurableSet_connectsSelectedPaths B B root large))

/-- A crossing and connection event supplies both crossing and coalescence. -/
theorem HasCrossingComponentConnectingPaths.crossing_and_coalescence {d : ℕ}
    {ω : Configuration d} {B : Set (Vertex d)} {lower upper : Fin d → Set (Vertex d)}
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (h : HasCrossingComponentConnectingPaths ω B lower upper large) :
    HasCrossingComponent ω B lower upper ∧ LargePathsCoalesce ω B large := by
  obtain ⟨root, hroot, hpaths⟩ := h
  exact ⟨⟨root, hroot⟩, largePathsCoalesce_of_connectsSelectedPaths hpaths⟩

end Rigidity.Percolation

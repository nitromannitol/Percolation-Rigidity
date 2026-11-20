import Rigidity.Percolation.TriadicWellConnectedGeometry

/-!
# Locality of well-connectedness

The well-connectedness event depends only on open edges with endpoints in the
concentric threefold enlargement of the ambient triadic cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- Configurations agreeing on all edges inside a region induce the same
restricted graph on every subset. -/
theorem openIn_eq_of_agree_on {d : ℕ} {ω ω' : Configuration d}
    {U B : Set (Vertex d)} (hB : B ⊆ U)
    (h : ∀ x ∈ U, ∀ y ∈ U, (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y) :
    openIn ω B = openIn ω' B := by
  ext x y
  change ((openGraph ω).Adj x y ∧ x ∈ B ∧ y ∈ B) ↔
    ((openGraph ω').Adj x y ∧ x ∈ B ∧ y ∈ B)
  constructor <;> rintro ⟨ha, hx, hy⟩
  · exact ⟨(h x (hB hx) y (hB hy)).mp ha, hx, hy⟩
  · exact ⟨(h x (hB hx) y (hB hy)).mpr ha, hx, hy⟩

/-- Each triadic cube is contained in its concentric threefold enlargement. -/
theorem TriadicCube.vertices_subset_centeredTriple {d : ℕ} (Q : TriadicCube d) :
    Q.vertices ⊆ Q.centeredTriple := by
  intro x hx i
  have hx' := hx i
  change |2 * (x i - Q.center i)| < Q.side at hx'
  change |2 * (x i - Q.center i)| < 3 * Q.side
  have hs := Q.side_pos
  omega

/-- Well-connectedness is unchanged if configurations agree inside the
concentric threefold enlargement. -/
theorem TriadicCube.wellConnectedIn_congr {d : ℕ} (Q : TriadicCube d)
    {interior : Set (Vertex d)} (hinterior : interior ⊆ Q.vertices)
    {ω ω' : Configuration d}
    (h : ∀ x ∈ Q.centeredTriple, ∀ y ∈ Q.centeredTriple,
      (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y) :
    Q.wellConnectedIn interior ω ↔ Q.wellConnectedIn interior ω' := by
  have hQ : openIn ω Q.vertices = openIn ω' Q.vertices :=
    openIn_eq_of_agree_on Q.vertices_subset_centeredTriple h
  have hR (R : IntegerCube d) (hR : R ∈ Q.testCubes interior) :
      openIn ω (↑R.vertices) = openIn ω' (↑R.vertices) :=
    openIn_eq_of_agree_on (Q.testCube_vertices_subset_centeredTriple hinterior hR) h
  rw [Q.wellConnectedIn_iff, Q.wellConnectedIn_iff]
  apply exists_congr
  intro root
  have hc : IsCrossingRoot ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root ↔
      IsCrossingRoot ω' Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root := by
    simp only [IsCrossingRoot, hQ]
  rw [hc]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro R
  apply imp_congr_right
  intro hRT
  simp only [CrossableRegion, ConnectsSelectedPaths, hQ, hR R hRT]


/-- The concentric threefold enlargement of a cube is contained in the
concentric threefold enlargement of its parent. -/
theorem TriadicCube.centeredTriple_subset_parent_centeredTriple {d : ℕ}
    (Q : TriadicCube d) : Q.centeredTriple ⊆ Q.parent.centeredTriple := by
  intro x hx i
  have hc := Q.vertices_subset_parent Q.center_mem
  have hc' := hc i
  change |2 * (Q.center i - Q.parent.center i)| < Q.parent.side at hc'
  have hx' := hx i
  change |2 * (x i - Q.center i)| < 3 * Q.side at hx'
  change |2 * (x i - Q.parent.center i)| < 3 * Q.parent.side
  have hs := Q.side_pos
  have hp := Q.side_parent
  have ha := abs_lt.mp hc'
  have hb := abs_lt.mp hx'
  apply abs_lt.mpr
  omega

/-- Goodness built from the well-connectedness events depends only on edges
inside the concentric threefold enlargement. -/
theorem TriadicCube.mem_goodOfWellConnected_congr {d : ℕ} (Q : TriadicCube d)
    (interior : TriadicCube d → Set (Vertex d))
    (hinterior : ∀ R, interior R ⊆ R.vertices) {ω ω' : Configuration d}
    (h : ∀ x ∈ Q.centeredTriple, ∀ y ∈ Q.centeredTriple,
      (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y) :
    Q ∈ goodOfWellConnected (wellConnectedFamily interior ω) ↔
      Q ∈ goodOfWellConnected (wellConnectedFamily interior ω') := by
  by_cases hscale : 0 < Q.scale
  · have hchild (digits : Fin d → Fin 3) :
        (Q.child digits).centeredTriple ⊆ Q.centeredTriple := by
      have hp := (Q.child digits).centeredTriple_subset_parent_centeredTriple
      rwa [child_parent Q digits hscale] at hp
    simp only [goodOfWellConnected, Set.mem_setOf_eq, hscale, true_and,
      wellConnectedFamily]
    refine and_congr (Q.wellConnectedIn_congr (hinterior Q) h) ?_
    apply forall_congr'
    intro digits
    apply (Q.child digits).wellConnectedIn_congr (hinterior _)
    intro x hx y hy
    exact h x (hchild digits hx) y (hchild digits hy)
  · simp only [goodOfWellConnected, Set.mem_setOf_eq, hscale, false_and]

end Rigidity.Percolation

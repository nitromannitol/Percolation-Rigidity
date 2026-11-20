import Rigidity.Percolation.TriadicLocalizationGeometry

/-!
# Localization with parent-cube support

When the good-cube event is determined by its parent, a change in the
stopping partition is witnessed by a nearby bad cube whose parent reaches
outside the region of localization.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A point of the parent of a cube and a point of the parent of an influenced
cube are within fourteen side lengths of the influenced cube. -/
theorem TriadicCube.abs_coord_sub_lt_of_mem_parents_of_mem_influence {d : ℕ}
    {S T : TriadicCube d} {x y : Vertex d} (hx : x ∈ S.parent.vertices)
    (hT : T ∈ S.influence) (hy : y ∈ T.parent.vertices) (i : Fin d) :
    |x i - y i| < 14 * T.side := by
  have hside : S.side ≤ T.side :=
    pow_le_pow_right₀ (by norm_num) (scale_le_of_mem_influence hT)
  have hS := S.parent.abs_coord_sub_lt_side hx (S.vertices_subset_parent S.center_mem) i
  rw [S.side_parent] at hS
  change |x i - S.center i| < 3 * S.side at hS
  have hST := abs_center_sub_le_of_mem_influence hT i
  have hT' := T.parent.abs_coord_sub_lt_side (T.vertices_subset_parent T.center_mem) hy i
  rw [T.side_parent] at hT'
  change |T.center i - y i| < 3 * T.side at hT'
  calc
    |x i - y i| ≤ |x i - S.center i| + |S.center i - T.center i| + |T.center i - y i| := by
      have h : x i - y i = (x i - S.center i) + (S.center i - T.center i) +
          (T.center i - y i) := by ring
      rw [h]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < 14 * T.side := by nlinarith

/-- If good-cube collections agree for cubes whose parents lie inside a
region, a discrepancy yields a bad cube near the point and a nearby point of
its parent outside the region. -/
theorem TriadicCube.exists_bad_near_parent_compl_of_stopping_ne {d : ℕ}
    {G H : Set (TriadicCube d)} {U : Set (Vertex d)} (hGH : G ⊆ H)
    (hlocal : ∀ T : TriadicCube d, T.parent.vertices ⊆ U → T ∈ H → T ∈ G)
    {Q R : TriadicCube d} {x : Vertex d}
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H) (hne : Q ≠ R) :
    ∃ T : TriadicCube d, T ∉ G ∧ T ∈ H ∧
      (∀ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side) ∧
      ∃ y ∈ T.parent.vertices, y ∉ U ∧ ∀ i, |x i - y i| < 14 * T.side := by
  classical
  obtain ⟨T, hT, hTG, hTH⟩ := exists_new_good_of_stopping_ne hGH hxQ hxR hQ hR hne
  have hnot : ¬ T.parent.vertices ⊆ U := fun h => hTG (hlocal T h hTH)
  obtain ⟨y, hyT, hyU⟩ := Set.not_subset.mp hnot
  have hgeom : ∀ S : TriadicCube d, x ∈ S.parent.vertices → T ∈ S.influence →
      (∀ z ∈ T.vertices, ∀ i, |x i - z i| < 12 * T.side) ∧
        ∀ i, |x i - y i| < 14 * T.side := by
    intro S hxS hST
    exact ⟨fun z hz i => abs_coord_sub_lt_of_mem_parent_of_mem_influence hxS hST hz i,
      fun i => abs_coord_sub_lt_of_mem_parents_of_mem_influence hxS hST hyT i⟩
  have hclose : (∀ z ∈ T.vertices, ∀ i, |x i - z i| < 12 * T.side) ∧
      ∀ i, |x i - y i| < 14 * T.side := by
    rcases hT with hT | ⟨hscale, digits, hT⟩
    · exact hgeom R (R.vertices_subset_parent hxR) hT
    · have hxQ' : x ∈ (Q.child digits).parent.vertices := by
        simpa only [child_parent Q digits hscale] using hxQ
      exact hgeom (Q.child digits) hxQ' hT
  exact ⟨T, hTG, hTH, hclose.1, y, hyT, hyU, hclose.2⟩

end Rigidity.Percolation

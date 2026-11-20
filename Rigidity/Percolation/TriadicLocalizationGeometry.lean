import Rigidity.Percolation.TriadicLocalizationWitness
import Rigidity.Percolation.TriadicInfluenceBounds

/-!
# Geometry of stopping partition localization

A discrepancy between stopping partitions has a nearby newly good cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A point of the parent and a point of an influenced cube are within twelve
side lengths of the influenced cube in each coordinate. -/
theorem TriadicCube.abs_coord_sub_lt_of_mem_parent_of_mem_influence {d : ℕ}
    {S T : TriadicCube d} {x y : Vertex d} (hx : x ∈ S.parent.vertices)
    (hT : T ∈ S.influence) (hy : y ∈ T.vertices) (i : Fin d) :
    |x i - y i| < 12 * T.side := by
  have hside : S.side ≤ T.side :=
    pow_le_pow_right₀ (by norm_num) (scale_le_of_mem_influence hT)
  have hS := S.parent.abs_coord_sub_lt_side hx (S.vertices_subset_parent S.center_mem) i
  rw [S.side_parent] at hS
  change |x i - S.center i| < 3 * S.side at hS
  have hST := abs_center_sub_le_of_mem_influence hT i
  have hT' := T.abs_coord_sub_lt_side T.center_mem hy i
  change |T.center i - y i| < T.side at hT'
  calc
    |x i - y i| ≤ |x i - S.center i| + |S.center i - T.center i| + |T.center i - y i| := by
      have h : x i - y i = (x i - S.center i) + (S.center i - T.center i) +
          (T.center i - y i) := by ring
      rw [h]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < 12 * T.side := by nlinarith

/-- If enlarging the good collection changes the stopping cube at a point,
a newly good cube is within twelve of its side lengths from that point. -/
theorem TriadicCube.exists_new_good_near_of_stopping_ne {d : ℕ}
    {G H : Set (TriadicCube d)} (hGH : G ⊆ H)
    {Q R : TriadicCube d} {x : Vertex d}
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H) (hne : Q ≠ R) :
    ∃ T : TriadicCube d, T ∉ G ∧ T ∈ H ∧
      ∀ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side := by
  obtain ⟨T, hT, hTG, hTH⟩ := exists_new_good_of_stopping_ne hGH hxQ hxR hQ hR hne
  refine ⟨T, hTG, hTH, ?_⟩
  intro y hy i
  rcases hT with hT | hT
  · exact abs_coord_sub_lt_of_mem_parent_of_mem_influence
      (R.vertices_subset_parent hxR) hT hy i
  · rcases hT with ⟨hscale, digits, hT⟩
    rw [← child_parent Q digits hscale] at hxQ
    exact abs_coord_sub_lt_of_mem_parent_of_mem_influence hxQ hT hy i


/-- If two good-cube collections agree inside a region, a change in the
stopping cube produces a bad cube with a nearby point outside the region. -/
theorem TriadicCube.exists_bad_near_compl_of_stopping_ne {d : ℕ}
    {G H : Set (TriadicCube d)} {U : Set (Vertex d)} (hGH : G ⊆ H)
    (hlocal : ∀ T : TriadicCube d, T.vertices ⊆ U → T ∈ H → T ∈ G)
    {Q R : TriadicCube d} {x : Vertex d}
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H) (hne : Q ≠ R) :
    ∃ T : TriadicCube d, ∃ y : Vertex d, T ∉ G ∧ T ∈ H ∧
      y ∈ T.vertices ∧ y ∉ U ∧ ∀ i, |x i - y i| < 12 * T.side := by
  classical
  obtain ⟨T, hTG, hTH, hnear⟩ :=
    exists_new_good_near_of_stopping_ne hGH hxQ hxR hQ hR hne
  have hnot : ¬ T.vertices ⊆ U := fun h => hTG (hlocal T h hTH)
  obtain ⟨y, hyT, hyU⟩ := Set.not_subset.mp hnot
  exact ⟨T, y, hTG, hTH, hyT, hyU, hnear y hyT⟩

end Rigidity.Percolation

import Rigidity.Percolation.TriadicLocalizationGeometry
import Rigidity.Percolation.TriadicStoppingMeasurable

/-!
# Centered support for localized stopping partitions

Good-cube events may be determined by the cube with the same center and
three times the side length. A partition discrepancy then has a nearby bad
cube whose centered enlargement reaches outside the localization region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory

/-- The lattice points of the concentric cube with three times the side length. -/
def TriadicCube.centeredTriple {d : ℕ} (Q : TriadicCube d) : Set (Vertex d) :=
  {x | ∀ i, |2 * (x i - Q.center i)| < 3 * Q.side}

/-- A point of the centered enlargement is within three side lengths of the center. -/
theorem TriadicCube.abs_coord_sub_center_lt_of_mem_centeredTriple {d : ℕ}
    {Q : TriadicCube d} {x : Vertex d} (hx : x ∈ Q.centeredTriple) (i : Fin d) :
    |x i - Q.center i| < 3 * Q.side := by
  have h := hx i
  rw [abs_mul] at h
  norm_num only [abs_of_nonneg (show (0 : ℤ) ≤ 2 by norm_num)] at h
  have hnonneg : 0 ≤ |x i - Q.center i| := abs_nonneg _
  omega

/-- Centered threefold support gives the same fourteen-side distance bound as
parent support for a cube reached through the influence relation. -/
theorem TriadicCube.abs_coord_sub_lt_of_mem_parent_of_mem_centeredTriple {d : ℕ}
    {S T : TriadicCube d} {x y : Vertex d} (hx : x ∈ S.parent.vertices)
    (hT : T ∈ S.influence) (hy : y ∈ T.centeredTriple) (i : Fin d) :
    |x i - y i| < 14 * T.side := by
  have hside : S.side ≤ T.side :=
    pow_le_pow_right₀ (by norm_num) (scale_le_of_mem_influence hT)
  have hS := S.parent.abs_coord_sub_lt_side hx (S.vertices_subset_parent S.center_mem) i
  rw [S.side_parent] at hS
  change |x i - S.center i| < 3 * S.side at hS
  have hST := abs_center_sub_le_of_mem_influence hT i
  have hT' := abs_coord_sub_center_lt_of_mem_centeredTriple hy i
  have hT'' : |T.center i - y i| < 3 * T.side := by
    simpa only [abs_sub_comm] using hT'
  calc
    |x i - y i| ≤ |x i - S.center i| + |S.center i - T.center i| +
        |T.center i - y i| := by
      have h : x i - y i = (x i - S.center i) + (S.center i - T.center i) +
          (T.center i - y i) := by ring
      rw [h]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < 14 * T.side := by nlinarith

/-- Declare cubes good whenever their centered threefold support is not
contained in the localization region. -/
def TriadicCube.localGoodCentered {d : ℕ} (G : Set (TriadicCube d))
    (U : Set (Vertex d)) : Set (TriadicCube d) :=
  G ∪ {T | ¬ T.centeredTriple ⊆ U}

/-- Localization preserves every original good cube. -/
theorem TriadicCube.subset_localGoodCentered {d : ℕ} (G : Set (TriadicCube d))
    (U : Set (Vertex d)) : G ⊆ localGoodCentered G U :=
  Set.subset_union_left

/-- Goodness in the local collection agrees with original goodness when the
centered support is contained in the localization region. -/
theorem TriadicCube.mem_of_mem_localGoodCentered {d : ℕ} {G : Set (TriadicCube d)}
    {U : Set (Vertex d)} {T : TriadicCube d} (hT : T.centeredTriple ⊆ U)
    (h : T ∈ localGoodCentered G U) : T ∈ G := by
  rcases h with h | h
  · exact h
  · exact (h hT).elim

/-- The localized good-cube event is measurable in the local environment. -/
theorem TriadicCube.measurableSet_mem_localGoodCentered {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (G : Ω → Set (TriadicCube d)) (U : Set (Vertex d))
    (hG : ∀ T : TriadicCube d, T.centeredTriple ⊆ U → MeasurableSet {ω | T ∈ G ω})
    (Q : TriadicCube d) : MeasurableSet {ω | Q ∈ localGoodCentered (G ω) U} := by
  classical
  by_cases hQ : Q.centeredTriple ⊆ U
  · have heq : {ω | Q ∈ localGoodCentered (G ω) U} = {ω | Q ∈ G ω} := by
      ext ω
      simp only [localGoodCentered, Set.mem_setOf_eq, Set.mem_union, hQ,
        not_true_eq_false, or_false]
    rw [heq]
    exact hG Q hQ
  · have heq : {ω | Q ∈ localGoodCentered (G ω) U} = Set.univ := by
      ext ω
      simp only [localGoodCentered, Set.mem_setOf_eq, Set.mem_union, hQ,
        not_false_eq_true, or_true, Set.mem_univ]
    rw [heq]
    exact MeasurableSet.univ

/-- Membership in the localized maximal stopping partition is measurable in
the local environment. -/
theorem TriadicCube.measurableSet_isMaximalStopping_localGoodCentered {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (G : Ω → Set (TriadicCube d)) (U : Set (Vertex d))
    (hG : ∀ T : TriadicCube d, T.centeredTriple ⊆ U → MeasurableSet {ω | T ∈ G ω})
    (Q : TriadicCube d) : MeasurableSet {ω | Q.IsMaximalStopping (localGoodCentered (G ω) U)} :=
  measurableSet_isMaximalStopping (fun ω => localGoodCentered (G ω) U)
    (measurableSet_mem_localGoodCentered G U hG) Q

/-- A discrepancy between the global partition and its centered-support
localization yields a nearby bad cube whose support meets the complement. -/
theorem TriadicCube.exists_bad_near_centeredTriple_compl_of_stopping_ne {d : ℕ}
    {G H : Set (TriadicCube d)} {U : Set (Vertex d)} (hGH : G ⊆ H)
    (hlocal : ∀ T : TriadicCube d, T.centeredTriple ⊆ U → T ∈ H → T ∈ G)
    {Q R : TriadicCube d} {x : Vertex d}
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H) (hne : Q ≠ R) :
    ∃ T : TriadicCube d, T ∉ G ∧ T ∈ H ∧
      (∀ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side) ∧
      ∃ y ∈ T.centeredTriple, y ∉ U ∧ ∀ i, |x i - y i| < 14 * T.side := by
  classical
  obtain ⟨T, hT, hTG, hTH⟩ := exists_new_good_of_stopping_ne hGH hxQ hxR hQ hR hne
  have hnot : ¬ T.centeredTriple ⊆ U := fun h => hTG (hlocal T h hTH)
  obtain ⟨y, hyT, hyU⟩ := Set.not_subset.mp hnot
  have hgeom : ∀ S : TriadicCube d, x ∈ S.parent.vertices → T ∈ S.influence →
      (∀ z ∈ T.vertices, ∀ i, |x i - z i| < 12 * T.side) ∧
        ∀ i, |x i - y i| < 14 * T.side := by
    intro S hxS hST
    exact ⟨fun z hz i => abs_coord_sub_lt_of_mem_parent_of_mem_influence hxS hST hz i,
      fun i => abs_coord_sub_lt_of_mem_parent_of_mem_centeredTriple hxS hST hyT i⟩
  have hclose : (∀ z ∈ T.vertices, ∀ i, |x i - z i| < 12 * T.side) ∧
      ∀ i, |x i - y i| < 14 * T.side := by
    rcases hT with hT | ⟨hscale, digits, hT⟩
    · exact hgeom R (R.vertices_subset_parent hxR) hT
    · have hxQ' : x ∈ (Q.child digits).parent.vertices := by
        simpa only [child_parent Q digits hscale] using hxQ
      exact hgeom (Q.child digits) hxQ' hT
  exact ⟨T, hTG, hTH, hclose.1, y, hyT, hyU, hclose.2⟩

end Rigidity.Percolation

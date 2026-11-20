import Rigidity.Percolation.TriadicLocalizationCentered

/-!
# Restriction of localized stopping partitions

For a positive-dimensional cube, the centered-support local stopping
partition restricts to a partition by cubes contained in the region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A centered threefold cube at least as large in scale as a cube cannot be
contained in that cube when the dimension is positive. -/
theorem TriadicCube.centeredTriple_not_subset_vertices {d : ℕ} (hd : 0 < d)
    (A T : TriadicCube d) (hscale : A.scale ≤ T.scale) :
    ¬ T.centeredTriple ⊆ A.vertices := by
  classical
  let i : Fin d := ⟨0, hd⟩
  let xp : Vertex d := Function.update T.center i (T.center i + T.side)
  let xm : Vertex d := Function.update T.center i (T.center i - T.side)
  have hside : A.side ≤ T.side := pow_le_pow_right₀ (by norm_num) hscale
  have hpos := T.side_pos
  have hxp : xp ∈ T.centeredTriple := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [xp, Function.update_self, add_sub_cancel_left, abs_mul,
        abs_of_pos (show (0 : ℤ) < 2 by norm_num), abs_of_pos hpos]
      omega
    · simp only [xp, Function.update_of_ne hji, sub_self, mul_zero, abs_zero]
      omega
  have hxm : xm ∈ T.centeredTriple := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [xm, Function.update_self, sub_sub_cancel_left, abs_mul,
        abs_of_pos (show (0 : ℤ) < 2 by norm_num), abs_neg, abs_of_pos hpos]
      omega
    · simp only [xm, Function.update_of_ne hji, sub_self, mul_zero, abs_zero]
      omega
  intro hsub
  have hdist := A.abs_coord_sub_lt_side (hsub hxp) (hsub hxm) i
  have heq : xp i - xm i = 2 * T.side := by
    simp only [xp, xm, Function.update_self]
    ring
  rw [heq, abs_of_pos (by omega : 0 < 2 * T.side)] at hdist
  omega

/-- Every cube at least as large as the localization region is locally stable. -/
theorem TriadicCube.mem_stableGood_localGoodCentered_of_scale_le {d : ℕ} (hd : 0 < d)
    (G : Set (TriadicCube d)) (A T : TriadicCube d) (hscale : A.scale ≤ T.scale) :
    T ∈ stableGood (localGoodCentered G A.vertices) := by
  intro R hR
  right
  exact centeredTriple_not_subset_vertices hd A R (hscale.trans (scale_le_of_mem_influence hR))

/-- A local stopping cube cannot be larger than the localization region. -/
theorem TriadicCube.scale_le_of_isStopping_localGoodCentered {d : ℕ} (hd : 0 < d)
    (G : Set (TriadicCube d)) (A T : TriadicCube d)
    (hT : T.IsStopping (localGoodCentered G A.vertices)) : T.scale ≤ A.scale := by
  by_contra h
  have hgt : A.scale < T.scale := by omega
  rcases hT.2 with hz | ⟨digits, hbad⟩
  · omega
  · apply hbad
    apply mem_stableGood_localGoodCentered_of_scale_le hd G A
    change A.scale ≤ T.scale - 1
    omega

/-- A local stopping cube meeting the localization region is contained in it. -/
theorem TriadicCube.vertices_subset_of_isStopping_localGoodCentered {d : ℕ} (hd : 0 < d)
    (G : Set (TriadicCube d)) (A T : TriadicCube d) {x : Vertex d}
    (hxA : x ∈ A.vertices) (hxT : x ∈ T.vertices)
    (hT : T.IsStopping (localGoodCentered G A.vertices)) : T.vertices ⊆ A.vertices :=
  vertices_subset_of_mem_of_scale_le hxT hxA
    (scale_le_of_isStopping_localGoodCentered hd G A T hT)

/-- Every point of the region belongs to a unique local maximal stopping cube,
and that cube is contained in the region. -/
theorem TriadicCube.existsUnique_localMaximalStopping_subset {d : ℕ} (hd : 0 < d)
    (G : Set (TriadicCube d)) (A : TriadicCube d) {x : Vertex d} (hx : x ∈ A.vertices) :
    ∃! T : TriadicCube d, x ∈ T.vertices ∧ T.IsMaximalStopping (localGoodCentered G A.vertices) ∧
      T.vertices ⊆ A.vertices := by
  have hstable := mem_stableGood_localGoodCentered_of_scale_le hd G A A le_rfl
  obtain ⟨T, ⟨hxT, hT⟩, huniq⟩ := existsUnique_isMaximalStopping_of_mem_stableGood hstable hx
  refine ⟨T, ⟨hxT, hT, vertices_subset_of_isStopping_localGoodCentered hd G A T hx hxT hT.1⟩, ?_⟩
  intro R hR
  exact huniq R ⟨hR.1, hR.2.1⟩

end Rigidity.Percolation

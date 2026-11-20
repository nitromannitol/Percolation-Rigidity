import Rigidity.Percolation.TriadicInteriorGeometry

/-!
# Inner boundaries of triadic cubes

The coordinate interior of a triadic cube agrees with its interior defined
using distance to the inner vertex boundary.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- The inner vertex boundary of a triadic cube in the nearest-neighbor graph. -/
def TriadicCube.innerBoundary {d : ℕ} (A : TriadicCube d) : Set (Vertex d) :=
  {x ∈ A.vertices | ∃ y ∉ A.vertices, (nearestNeighborGraph d).Adj x y}

/-- The integer half-width of a triadic cube. -/
def TriadicCube.radius {d : ℕ} (A : TriadicCube d) : ℤ := A.side / 2

/-- The side length is one more than twice the integer half-width. -/
theorem TriadicCube.side_eq_two_mul_radius_add_one {d : ℕ} (A : TriadicCube d) :
    A.side = 2 * A.radius + 1 := by
  have ho : Odd A.side := by
    simpa only [TriadicCube.side] using (show Odd (3 : ℤ) by norm_num).pow
  obtain ⟨k, hk⟩ := ho
  unfold radius
  omega

/-- Membership in a cube is equivalent to the coordinate half-width bounds. -/
theorem TriadicCube.mem_vertices_iff {d : ℕ} (A : TriadicCube d) (x : Vertex d) :
    x ∈ A.vertices ↔ ∀ i, |x i - A.center i| ≤ A.radius := by
  have hs := A.side_eq_two_mul_radius_add_one
  constructor
  · intro hx i
    have h : |2 * (x i - A.center i)| < A.side := hx i
    rw [abs_mul, abs_of_pos (show (0 : ℤ) < 2 by norm_num)] at h
    omega
  · intro hx i
    have h := hx i
    change |2 * (x i - A.center i)| < A.side
    rw [abs_mul, abs_of_pos (show (0 : ℤ) < 2 by norm_num)]
    omega

/-- Points of a cube at a coordinate face lie on its inner vertex boundary. -/
theorem TriadicCube.mem_innerBoundary_of_coord_eq {d : ℕ} (A : TriadicCube d)
    {x : Vertex d} (hx : x ∈ A.vertices) (i : Fin d)
    (hi : |x i - A.center i| = A.radius) : x ∈ A.innerBoundary := by
  classical
  have hs := A.side_eq_two_mul_radius_add_one
  have hr : 0 ≤ A.radius := by have := A.side_pos; omega
  rcases (abs_eq hr).mp hi with hp | hm
  · refine ⟨hx, x + LatticeProb.unit i, ?_, ⟨i, Or.inl rfl⟩⟩
    intro hy
    have h := (A.mem_vertices_iff _).mp hy i
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same] at h
    have h' := (abs_le.mp h).2
    omega
  · refine ⟨hx, x - LatticeProb.unit i, ?_, ?_⟩
    · intro hy
      have h := (A.mem_vertices_iff _).mp hy i
      simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same] at h
      have h' := (abs_le.mp h).1
      omega
    · refine ⟨i, Or.inr ?_⟩
      ext j
      simp only [Pi.add_apply, Pi.sub_apply]
      abel

/-- Distance at least `3 ^ n` from every inner-boundary point. -/
def TriadicCube.boundaryInterior {d : ℕ} (A : TriadicCube d) (n : ℕ) : Set (Vertex d) :=
  {x ∈ A.vertices | ∀ y ∈ A.innerBoundary, ∃ i, (3 : ℤ) ^ n ≤ |x i - y i|}

/-- Boundary distance implies the corresponding coordinate margins. -/
theorem TriadicCube.boundaryInterior_subset_interiorVertices {d : ℕ}
    (A : TriadicCube d) (n : ℕ) : A.boundaryInterior n ⊆ A.interiorVertices n := by
  classical
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro i
  let z : Vertex d := Function.update x i (A.center i + if 0 ≤ x i - A.center i then A.radius else -A.radius)
  have hr : 0 ≤ A.radius := by
    have := A.side_pos
    have := A.side_eq_two_mul_radius_add_one
    omega
  have hzmem : z ∈ A.vertices := by
    apply (A.mem_vertices_iff z).mpr
    intro j
    by_cases hji : j = i
    · subst j
      simp only [z, Function.update_self]
      split_ifs <;> simp only [add_sub_cancel_left, abs_neg, abs_of_nonneg hr, le_refl]
    · simpa only [z, Function.update_of_ne hji] using (A.mem_vertices_iff x).mp hx.1 j
  have hzface : |z i - A.center i| = A.radius := by
    simp only [z, Function.update_self]
    split_ifs <;> simp only [add_sub_cancel_left, abs_neg, abs_of_nonneg hr]
  obtain ⟨j, hj⟩ := hx.2 z (A.mem_innerBoundary_of_coord_eq hzmem i hzface)
  have hjpos : 0 < (3 : ℤ) ^ n := pow_pos (by norm_num) _
  have hji : j = i := by
    by_contra h
    have : z j = x j := Function.update_of_ne h _ _
    rw [this, sub_self, abs_zero] at hj
    omega
  subst j
  have hzi : z i = A.center i + if 0 ≤ x i - A.center i then A.radius else -A.radius :=
    Function.update_self i _ _
  rw [hzi] at hj
  have hxbound := (A.mem_vertices_iff x).mp hx.1 i
  have hs := A.side_eq_two_mul_radius_add_one
  split_ifs at hj with hsign
  · rw [abs_of_nonneg hsign]
    have hneg : x i - (A.center i + A.radius) ≤ 0 := by
      have := (abs_le.mp hxbound).2
      omega
    rw [abs_of_nonpos hneg] at hj
    omega
  · have hsign' : x i - A.center i ≤ 0 := by omega
    rw [abs_of_nonpos hsign']
    have hpos : 0 ≤ x i - (A.center i + -A.radius) := by
      have := (abs_le.mp hxbound).1
      omega
    rw [abs_of_nonneg hpos] at hj
    omega

/-- Every inner-boundary point lies on a coordinate face. -/
theorem TriadicCube.exists_coord_eq_of_mem_innerBoundary {d : ℕ} (A : TriadicCube d)
    {y : Vertex d} (hy : y ∈ A.innerBoundary) :
    ∃ i, |y i - A.center i| = A.radius := by
  classical
  obtain ⟨hymem, z, hzout, hyz⟩ := hy
  by_contra h
  push Not at h
  apply hzout
  apply (A.mem_vertices_iff z).mpr
  intro i
  have hyi := (A.mem_vertices_iff y).mp hymem i
  have hne := h i
  have hsum : latticeL1Dist y z = 1 := lattice_adj_iff_l1Dist.mp hyz
  have hdist : |y i - z i| ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (y j - z j)) (Finset.mem_univ i)
  have htri : |z i - A.center i| ≤ |y i - z i| + |y i - A.center i| := by
    have heq : z i - A.center i = -(y i - z i) + (y i - A.center i) := by ring
    rw [heq]
    simpa only [abs_neg] using abs_add_le (-(y i - z i)) (y i - A.center i)
  omega

/-- Coordinate margins imply the same distance from the inner vertex boundary. -/
theorem TriadicCube.interiorVertices_subset_boundaryInterior {d : ℕ}
    (A : TriadicCube d) (n : ℕ) : A.interiorVertices n ⊆ A.boundaryInterior n := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := A.exists_coord_eq_of_mem_innerBoundary hy
  refine ⟨i, ?_⟩
  have hm := hx.2 i
  have hs := A.side_eq_two_mul_radius_add_one
  have htri : |y i - A.center i| ≤ |x i - y i| + |x i - A.center i| := by
    have heq : y i - A.center i = -(x i - y i) + (x i - A.center i) := by ring
    rw [heq]
    simpa only [abs_neg] using abs_add_le (-(x i - y i)) (x i - A.center i)
  omega

/-- Coordinate and inner-boundary formulations of a cube's interior agree. -/
theorem TriadicCube.boundaryInterior_eq_interiorVertices {d : ℕ}
    (A : TriadicCube d) (n : ℕ) : A.boundaryInterior n = A.interiorVertices n :=
  Set.Subset.antisymm (A.boundaryInterior_subset_interiorVertices n)
    (A.interiorVertices_subset_boundaryInterior n)

/-- The centered localization discrepancy bound in terms of distance to the
inner vertex boundary of a cube. -/
theorem TriadicCube.measure_localGoodCentered_boundaryInterior_discrepancy_le
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Ω → Set (TriadicCube d)) (A : TriadicCube d)
    (n : ℕ) (hn : 3 ≤ n) (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
      max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) *
        ((2 * 3 ^ (A.scale - (n - 3 + 1)) + 29 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp ((-c * b ^ (n - 3 + 1)) / d)) := by
  rw [A.boundaryInterior_eq_interiorVertices n]
  exact A.measure_localGoodCentered_interior_discrepancy_le hd μ G n hn C b c hb hc hprob

end Rigidity.Percolation

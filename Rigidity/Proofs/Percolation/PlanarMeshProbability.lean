import Rigidity.Proofs.Percolation.PlanarMeshCardinality

/-!
# Probability of planar crossing meshes

A crossing mesh is obtained from finitely many supercritical rectangle crossings.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal

namespace Rigidity.Percolation

/-- Lower corner of a horizontal strip in a cube. -/
def horizontalStripCorner (x : Vertex 2) (N : ℕ) (L : ℤ) : Vertex 2 :=
  fun i => if i = 0 then x 0 - N else L

/-- Lower corner of a vertical strip in a cube. -/
def verticalStripCorner (x : Vertex 2) (N : ℕ) (L : ℤ) : Vertex 2 :=
  fun i => if i = 0 then L else x 1 - N

/-- A horizontal strip is a rectangle with the same lattice vertices. -/
theorem horizontal_strip_eq_rectangle (x : Vertex 2) (N w : ℕ) (L : ℤ)
    (hL : x 1 - N ≤ L) (hU : L + w ≤ x 1 + N) :
    crossingRectangle (horizontalStripCorner x N L) (2 * N) w 0 =
      cubeAt x N ∩ {v | L ≤ v 1 ∧ v 1 ≤ L + w} := by
  ext y
  simp only [crossingRectangle, horizontalStripCorner, cubeAt, Set.mem_setOf_eq,
    Set.mem_inter_iff, Fin.forall_fin_two, Fin.isValue, ite_true,
    Nat.cast_mul, Nat.cast_ofNat, abs_le]
  constructor <;> intro h <;> rcases h with ⟨h₀, h₁⟩ <;>
    simp only [Fin.reduceEq, ↓reduceIte] at h₀ h₁ ⊢ <;> omega

/-- A vertical strip is a rectangle with the same lattice vertices. -/
theorem vertical_strip_eq_rectangle (x : Vertex 2) (N w : ℕ) (L : ℤ)
    (hL : x 0 - N ≤ L) (hU : L + w ≤ x 0 + N) :
    crossingRectangle (verticalStripCorner x N L) (2 * N) w 1 =
      cubeAt x N ∩ {v | L ≤ v 0 ∧ v 0 ≤ L + w} := by
  ext y
  simp only [crossingRectangle, verticalStripCorner, cubeAt, Set.mem_setOf_eq,
    Set.mem_inter_iff, Fin.forall_fin_two, Fin.isValue, ite_true,
    Nat.cast_mul, Nat.cast_ofNat, abs_le]
  constructor <;> intro h <;> rcases h with ⟨h₀, h₁⟩ <;>
    simp only [Fin.reduceEq, ↓reduceIte] at h₀ h₁ ⊢ <;> omega

/-- Rectangle crossings of every admissible strip give a crossing mesh. -/
theorem hasStripCrossings_of_rectangles {ω : Configuration 2} (x : Vertex 2) (N w : ℕ)
    (hH : ∀ L : ℤ, x 1 - N ≤ L → L + w ≤ x 1 + N →
      HasOpenCrossing ω (horizontalStripCorner x N L) (2 * N) w 0)
    (hV : ∀ L : ℤ, x 0 - N ≤ L → L + w ≤ x 0 + N →
      HasOpenCrossing ω (verticalStripCorner x N L) (2 * N) w 1) :
    HasStripCrossings ω x N w := by
  constructor
  · intro L hL hU
    have h := hH L hL hU
    unfold HasOpenCrossing at h
    rw [horizontal_strip_eq_rectangle x N w L hL hU] at h
    obtain ⟨a, b, ha, hb, hfa, hfb, hab⟩ := h
    refine ⟨a, b, reachIn_of_reachable_induce hab, ?_, ?_⟩
    · simpa [horizontalStripCorner] using hfa
    · simp only [horizontalStripCorner, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat] at hfb
      omega
  · intro L hL hU
    have h := hV L hL hU
    unfold HasOpenCrossing at h
    rw [vertical_strip_eq_rectangle x N w L hL hU] at h
    obtain ⟨a, b, ha, hb, hfa, hfb, hab⟩ := h
    refine ⟨a, b, reachIn_of_reachable_induce hab, ?_, ?_⟩
    · simpa [verticalStripCorner] using hfa
    · simp only [verticalStripCorner, Fin.reduceEq, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat] at hfb
      omega

/-- The finitely many potential horizontal and vertical strips of a cube. -/
noncomputable def stripRectangles (x : Vertex 2) (N : ℕ) : Finset (Vertex 2 × Fin 2) := by
  classical
  exact ((Finset.Icc (-(N : ℤ)) N).image fun t =>
      (horizontalStripCorner x N (x 1 + t), (0 : Fin 2))) ∪
    ((Finset.Icc (-(N : ℤ)) N).image fun t =>
      (verticalStripCorner x N (x 0 + t), (1 : Fin 2)))

/-- The number of possible strip rectangles is at most `2(2N+1)`. -/
theorem card_stripRectangles_le (x : Vertex 2) (N : ℕ) :
    (stripRectangles x N).card ≤ 2 * (2 * N + 1) := by
  classical
  unfold stripRectangles
  have h := Finset.card_union_le
    ((Finset.Icc (-(N : ℤ)) N).image fun t =>
      (horizontalStripCorner x N (x 1 + t), (0 : Fin 2)))
    ((Finset.Icc (-(N : ℤ)) N).image fun t =>
      (verticalStripCorner x N (x 0 + t), (1 : Fin 2)))
  have h₁ := Finset.card_image_le (s := Finset.Icc (-(N : ℤ)) N)
    (f := fun t => (horizontalStripCorner x N (x 1 + t), (0 : Fin 2)))
  have h₂ := Finset.card_image_le (s := Finset.Icc (-(N : ℤ)) N)
    (f := fun t => (verticalStripCorner x N (x 0 + t), (1 : Fin 2)))
  rw [Int.card_Icc] at h₁ h₂
  omega

/-- A failed crossing mesh entails a failed rectangle crossing from its finite family. -/
theorem not_hasStripCrossings_subset {x : Vertex 2} {N w : ℕ} :
    {ω | ¬ HasStripCrossings ω x N w} ⊆
      ⋃ q ∈ stripRectangles x N, {ω | ¬ HasOpenCrossing ω q.1 (2 * N) w q.2} := by
  classical
  intro ω hω
  by_contra h
  have hall : ∀ q ∈ stripRectangles x N, HasOpenCrossing ω q.1 (2 * N) w q.2 := by
    intro q hq
    by_contra hq'
    exact h (Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hq'⟩⟩)
  apply hω
  apply hasStripCrossings_of_rectangles x N w
  · intro L hL hU
    have ht : L - x 1 ∈ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      constructor <;> omega
    have hq : (horizontalStripCorner x N L, (0 : Fin 2)) ∈ stripRectangles x N := by
      unfold stripRectangles
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨L - x 1, ht, ?_⟩
      congr 1
      congr 1
      omega
    exact hall _ hq
  · intro L hL hU
    have ht : L - x 0 ∈ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      constructor <;> omega
    have hq : (verticalStripCorner x N L, (1 : Fin 2)) ∈ stripRectangles x N := by
      unfold stripRectangles
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨L - x 0, ht, ?_⟩
      congr 1
      congr 1
      omega
    exact hall _ hq

/-- Supercritical planar strip meshes fail with at most a polynomial times an exponential bound. -/
theorem stripCrossings_failure_bound (p : unitInterval) (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (N w : ℕ),
      latticeBondLaw 2 p {ω | ¬ HasStripCrossings ω x N w} ≤
        ((2 * (2 * N + 1) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (C * ((2 * N : ℕ) + 1) * Real.exp (-(c * w))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := rectangle_crossing_family_failure_bound p hp
  refine ⟨C, c, hC, hc, fun x N w => ?_⟩
  refine (measure_mono not_hasStripCrossings_subset).trans ?_
  refine (hbound (2 * N) w (stripRectangles x N)).trans ?_
  gcongr
  exact_mod_cast card_stripRectangles_le x N

end Rigidity.Percolation

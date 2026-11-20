import Rigidity.Percolation.TriadicInfluence

/-!
# Geometric bounds for triadic influence

Influence chains remain within a bounded multiple of the side length of their
largest cube. The estimates are coordinatewise in the maximum norm.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The center of a triadic cube as a lattice vertex. -/
def TriadicCube.center {d : ℕ} (Q : TriadicCube d) : Vertex d :=
  fun i => Q.side * Q.index i

/-- Two vertices of a cube are less than one side length apart in every coordinate. -/
theorem TriadicCube.abs_coord_sub_lt_side {d : ℕ} {Q : TriadicCube d}
    {x y : Vertex d} (hx : x ∈ Q.vertices) (hy : y ∈ Q.vertices) (i : Fin d) :
    |x i - y i| < Q.side := by
  have hx' := abs_lt.mp (hx i)
  have hy' := abs_lt.mp (hy i)
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- A single influence step moves centers by at most five times the larger side length. -/
theorem TriadicCube.abs_center_sub_le_of_influenceStep {d : ℕ} {Q R : TriadicCube d}
    (h : Q.InfluenceStep R) (i : Fin d) : |Q.center i - R.center i| ≤ 5 * R.side := by
  obtain ⟨hscale, a, ha, b, hb, hab⟩ := h
  have hside : R.side = 3 * Q.side := by
    simp only [side, hscale, pow_succ]
    ring
  have hq : Q.center ∈ Q.vertices := Q.center_mem
  have hr : R.center ∈ R.parent.vertices := R.vertices_subset_parent R.center_mem
  have hqa := abs_lt.mp (Q.abs_coord_sub_lt_side hq ha i)
  have hbr := abs_lt.mp (R.parent.abs_coord_sub_lt_side hb hr i)
  have hab' := abs_le.mp (hab i)
  rw [R.side_parent] at hbr
  have hpos := Q.side_pos
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Every influence chain moves centers by at most eight times the final side length. -/
theorem TriadicCube.abs_center_sub_le_of_mem_influence {d : ℕ} {Q R : TriadicCube d}
    (h : R ∈ Q.influence) (i : Fin d) : |Q.center i - R.center i| ≤ 8 * R.side := by
  induction h with
  | refl =>
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by norm_num) (le_of_lt Q.side_pos)
  | @tail S T hST hstep ih =>
    have hscale := hstep.1
    have hside : T.side = 3 * S.side := by
      simp only [side, hscale, pow_succ]
      ring
    have hlast := abs_center_sub_le_of_influenceStep hstep i
    have hpos := S.side_pos
    calc
      |Q.center i - T.center i| ≤ |Q.center i - S.center i| + |S.center i - T.center i| := by
        have heq : Q.center i - T.center i =
            (Q.center i - S.center i) + (S.center i - T.center i) := by ring
        rw [heq]
        exact abs_add_le _ _
      _ ≤ 8 * S.side + 5 * T.side := add_le_add ih hlast
      _ ≤ 8 * T.side := by nlinarith

/-- Influenced cubes have points at coordinatewise distance at most eight final side lengths. -/
theorem TriadicCube.exists_close_of_mem_influence {d : ℕ} {Q R : TriadicCube d}
    (h : R ∈ Q.influence) :
    ∃ x ∈ Q.vertices, ∃ y ∈ R.vertices, ∀ i, |x i - y i| ≤ 8 * R.side := by
  exact ⟨Q.center, Q.center_mem, R.center, R.center_mem,
    fun i => abs_center_sub_le_of_mem_influence h i⟩

end Rigidity.Percolation

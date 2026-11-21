import Rigidity.External.WellConnected
import Rigidity.Proofs.Percolation.KestenCrossing

/-!
# Crossings of planar cubes

The supercritical rectangle estimate gives crossings of translated lattice cubes in either
coordinate direction.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Percolation

/-- The lower corner of a planar cube. -/
def cubeLowerCorner (x : Vertex 2) (N : ℕ) : Vertex 2 := fun i => x i - N

/-- A cube is the corresponding square rectangle in either coordinate direction. -/
theorem crossingRectangle_cubeLowerCorner (x : Vertex 2) (N : ℕ) (i : Fin 2) :
    crossingRectangle (cubeLowerCorner x N) (2 * N) (2 * N) i = cubeAt x N := by
  ext y
  simp only [crossingRectangle, cubeAt, Set.mem_setOf_eq, cubeLowerCorner, ite_self,
    Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · intro h j
    obtain ⟨hl, hr⟩ := h j
    rw [abs_le]
    constructor <;> omega
  · intro h j
    have hj := (abs_le.mp (h j))
    constructor <;> omega

/-- The probability that a supercritical planar cube has no crossing in a fixed direction. -/
theorem cube_crossing_failure_bound (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (N : ℕ) (i : Fin 2),
      latticeBondLaw 2 p
          {ω | ¬ ∃ (y z : Vertex 2) (hy : y ∈ cubeAt x N) (hz : z ∈ cubeAt x N),
            y i = x i - N ∧ z i = x i + N ∧
              ((openGraph ω).induce (cubeAt x N)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} ≤
        ENNReal.ofReal (C * ((2 * N : ℕ) + 1) * Real.exp (-(c * (2 * N : ℕ)))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := kesten_rectangle_crossing p hp
  refine ⟨C, c, hC, hc, fun x N i => ?_⟩
  have h := hbound (cubeLowerCorner x N) (2 * N) (2 * N) i
  unfold HasOpenCrossing at h
  rw [crossingRectangle_cubeLowerCorner] at h
  simp only [cubeLowerCorner, Nat.cast_mul, Nat.cast_ofNat] at h
  have heq : x i - (N : ℤ) + 2 * N = x i + N := by ring
  rw [heq] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- A union bound for any finite family of equal-sized planar crossing rectangles. -/
theorem rectangle_crossing_family_failure_bound (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (m n : ℕ) (T : Finset (Vertex 2 × Fin 2)),
      latticeBondLaw 2 p (⋃ q ∈ T, {ω | ¬ HasOpenCrossing ω q.1 m n q.2}) ≤
        (T.card : ℝ≥0∞) * ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := kesten_rectangle_crossing p hp
  refine ⟨C, c, hC, hc, fun m n T => ?_⟩
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _q ∈ T, ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n))) :=
      Finset.sum_le_sum fun q _ => hbound q.1 m n q.2
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end Rigidity.Percolation

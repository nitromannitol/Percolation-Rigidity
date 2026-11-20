import Rigidity.Percolation.IntegerCubeOverlap
import Rigidity.Percolation.TriadicWellConnectedEvent

/-!
# Overlap with a centered interior

Test cubes meeting the centered three-quarter interior envelope overlap the
ambient cube in a cube whose side is a fixed fraction of the ambient side.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The centered three-quarter envelope of a triadic cube. -/
def TriadicCube.threeQuarterEnvelope {d : ℕ} (Q : TriadicCube d) : Set (Vertex d) :=
  {x | ∀ i, 4 * |2 * (x i - Q.center i)| ≤ 3 * Q.side}

/-- The centered three-quarter envelope is contained in the triadic cube. -/
theorem TriadicCube.threeQuarterEnvelope_subset {d : ℕ} (Q : TriadicCube d) :
    Q.threeQuarterEnvelope ⊆ Q.vertices := by
  intro x hx i
  have hi := hx i
  have hs := Q.side_pos
  simp only [center] at hi
  omega

/-- Every point of the centered envelope has a coordinate margin of at least
one twentieth of the triadic side, rounded down. -/
theorem TriadicCube.threeQuarterEnvelope_depth {d : ℕ} (Q : TriadicCube d)
    {x : Vertex d} (hx : x ∈ Q.threeQuarterEnvelope) :
    ∀ i, Q.toIntegerCube.corner i + ((3 ^ Q.scale / 20 : ℕ) : ℤ) ≤ x i ∧
      x i + ((3 ^ Q.scale / 20 : ℕ) : ℤ) ≤
        Q.toIntegerCube.corner i + (Q.toIntegerCube.size : ℤ) := by
  let k : ℕ := 3 ^ Q.scale / 20
  have hk : (20 : ℤ) * k ≤ Q.side := by
    have h := Nat.div_mul_le_self (3 ^ Q.scale) 20
    have hs : ((3 ^ Q.scale : ℕ) : ℤ) = Q.side := by
      simp only [side, Nat.cast_pow, Nat.cast_ofNat]
    have h' : ((3 ^ Q.scale / 20 * 20 : ℕ) : ℤ) ≤ ((3 ^ Q.scale : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    change (20 : ℤ) * (k : ℤ) ≤ Q.side
    omega
  have hk0 : 0 ≤ (k : ℤ) := by positivity
  have hside : (Q.toIntegerCube.size : ℤ) = Q.side := by
    simp only [toIntegerCube, side, Nat.cast_pow, Nat.cast_ofNat]
  have hxQ := Q.threeQuarterEnvelope_subset hx
  have hcoord := (Q.mem_toIntegerCube_vertices x).mpr hxQ
  have hbox := (IntegerCube.mem_vertices Q.toIntegerCube x).mp hcoord
  intro i
  have hi := hx i
  have hboxi := hbox i
  have hs := Q.side_pos
  have hr : -(3 * Q.side) ≤ 4 * (2 * (x i - Q.center i)) ∧
      4 * (2 * (x i - Q.center i)) ≤ 3 * Q.side := by
    have hleft := neg_abs_le (2 * (x i - Q.center i))
    have hright := le_abs_self (2 * (x i - Q.center i))
    omega
  simp only [toIntegerCube] at hboxi ⊢
  simp only [toIntegerCube] at hside
  have hdiv := Int.emod_add_mul_ediv Q.side 2
  have hmod := Int.emod_nonneg Q.side (by norm_num : (2 : ℤ) ≠ 0)
  have hmodlt := Int.emod_lt_of_pos Q.side (by norm_num : (0 : ℤ) < 2)
  change Q.side * Q.index i - Q.side / 2 + (k : ℤ) ≤ x i ∧
    x i + (k : ℤ) ≤ Q.side * Q.index i - Q.side / 2 + Q.side
  simp only [center] at hr
  by_cases h : k = 0
  · simp only [h, Nat.cast_zero, add_zero]
    omega
  · have hkp : 1 ≤ (k : ℤ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
    omega

/-- A qualifying test cube meeting the centered envelope contains a cube of
side `⌊3^n / 20⌋` inside its intersection with the ambient cube. -/
theorem TriadicCube.exists_overlap_cube {d : ℕ} (Q : TriadicCube d)
    {R : IntegerCube d} (hR : R ∈ Q.testCubes Q.threeQuarterEnvelope) :
    ∃ T : IntegerCube d, T.size = 3 ^ Q.scale / 20 ∧
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices ∧
      (↑T.vertices : Set (Vertex d)) ⊆ R.vertices := by
  obtain ⟨hsize, _, x, hxR, hxI⟩ := hR
  have hxQ := Q.threeQuarterEnvelope_subset hxI
  have hk : 3 ^ Q.scale / 20 ≤ R.size := by
    have hdiv := Nat.div_mul_le_self (3 ^ Q.scale) 20
    have hside : Q.side = ((3 ^ Q.scale : ℕ) : ℤ) := by
      simp only [side, Nat.cast_pow, Nat.cast_ofNat]
    rw [hside] at hsize
    have hdiv' : ((3 ^ Q.scale / 20 * 20 : ℕ) : ℤ) ≤ ((3 ^ Q.scale : ℕ) : ℤ) := by
      exact_mod_cast hdiv
    push_cast at hdiv'
    have : ((3 ^ Q.scale / 20 : ℕ) : ℤ) ≤ (R.size : ℤ) := by omega
    exact_mod_cast this
  obtain ⟨T, hTsize, hTQ, hTR⟩ := IntegerCube.exists_cube_in_intersection
    Q.toIntegerCube R x (3 ^ Q.scale / 20)
    ((Q.mem_toIntegerCube_vertices x).mpr hxQ) hxR hk (Q.threeQuarterEnvelope_depth hxI)
  refine ⟨T, hTsize, ?_, hTR⟩
  intro y hy
  exact (Q.mem_toIntegerCube_vertices y).mp (hTQ hy)

/-- The same overlap bound applies to any test region contained in the
centered envelope. -/
theorem TriadicCube.exists_overlap_cube_of_subset {d : ℕ} (Q : TriadicCube d)
    {interior : Set (Vertex d)} (hinterior : interior ⊆ Q.threeQuarterEnvelope)
    {R : IntegerCube d} (hR : R ∈ Q.testCubes interior) :
    ∃ T : IntegerCube d, T.size = 3 ^ Q.scale / 20 ∧
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices ∧
      (↑T.vertices : Set (Vertex d)) ⊆ R.vertices := by
  obtain ⟨hlo, hhi, x, hxR, hxI⟩ := hR
  exact Q.exists_overlap_cube ⟨hlo, hhi, x, hxR, hinterior hxI⟩

end Rigidity.Percolation

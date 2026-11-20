import Rigidity.Percolation.TriadicInteriorOverlap

/-!
# Rounded three-quarter cubes

A centered integer cube of the prescribed rounded side length is contained in
the centered three-quarter envelope.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The integer cube of side `⌊3 · 3^n / 4⌋` whose lower corner is obtained by
rounding half its side down from the center. -/
def TriadicCube.threeQuarterCube {d : ℕ} (Q : TriadicCube d) : IntegerCube d where
  corner i := Q.center i - (((3 * 3 ^ Q.scale / 4 : ℕ) : ℤ) / 2)
  size := 3 * 3 ^ Q.scale / 4

/-- The rounded three-quarter cube lies in the centered three-quarter envelope. -/
theorem TriadicCube.threeQuarterCube_subset_envelope {d : ℕ} (Q : TriadicCube d) :
    (↑Q.threeQuarterCube.vertices : Set (Vertex d)) ⊆ Q.threeQuarterEnvelope := by
  intro x hx i
  have hmem := (IntegerCube.mem_vertices Q.threeQuarterCube x).mp hx i
  let k : ℕ := 3 * 3 ^ Q.scale / 4
  have hk : (4 : ℤ) * k ≤ 3 * Q.side := by
    have h := Nat.div_mul_le_self (3 * 3 ^ Q.scale) 4
    have h' : ((3 * 3 ^ Q.scale / 4 * 4 : ℕ) : ℤ) ≤
        ((3 * 3 ^ Q.scale : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    have hs : ((3 ^ Q.scale : ℕ) : ℤ) = Q.side := by
      simp only [side, Nat.cast_pow, Nat.cast_ofNat]
    change (4 : ℤ) * (k : ℤ) ≤ 3 * Q.side
    omega
  have hk0 : 0 ≤ (k : ℤ) := by positivity
  have hdiv := Int.emod_add_mul_ediv (k : ℤ) 2
  have hmod := Int.emod_nonneg (k : ℤ) (by norm_num : (2 : ℤ) ≠ 0)
  have hmodlt := Int.emod_lt_of_pos (k : ℤ) (by norm_num : (0 : ℤ) < 2)
  change Q.center i - (k : ℤ) / 2 ≤ x i ∧
    x i < Q.center i - (k : ℤ) / 2 + (k : ℤ) at hmem
  have habs : |2 * (x i - Q.center i)| ≤ (k : ℤ) := by
    apply abs_le.mpr
    omega
  omega

/-- A test cube meeting the rounded three-quarter cube has a macroscopic
intersection with the triadic cube. -/
theorem TriadicCube.exists_overlap_cube_threeQuarter {d : ℕ} (Q : TriadicCube d)
    {R : IntegerCube d} (hR : R ∈ Q.testCubes Q.threeQuarterCube.vertices) :
    ∃ T : IntegerCube d, T.size = 3 ^ Q.scale / 20 ∧
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices ∧
      (↑T.vertices : Set (Vertex d)) ⊆ R.vertices :=
  Q.exists_overlap_cube_of_subset Q.threeQuarterCube_subset_envelope hR

end Rigidity.Percolation

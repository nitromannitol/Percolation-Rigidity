import Rigidity.Percolation.OverlapPathCoalescence
import Rigidity.Percolation.TriadicThreeQuarterCube

/-!
# Well-connectedness from overlap crossings

A crossing component in each macroscopic overlap joins the large paths in a
triadic cube to the large paths in its test cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- Macroscopic overlap crossings and coalescence at the overlap scale imply
well-connectedness for the rounded three-quarter interior. -/
theorem TriadicCube.wellConnectedIn_threeQuarter_of_overlap_crossings {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) (hside : 2 ≤ Q.side)
    {ω : Configuration d} {root : Vertex d}
    (hroot : IsCrossingRoot ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root)
    (hQ : LargePathsCoalesce ω Q.vertices
      (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1)))
    (htests : ∀ R ∈ Q.testCubes Q.threeQuarterCube.vertices,
      CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
        (fun i => ↑(R.upperFace i)) ∧
      LargePathsCoalesce ω (↑R.vertices)
        (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1)))
    (hoverlap : ∀ T : IntegerCube d, T.size = 3 ^ Q.scale / 20 →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      HasCrossingComponent ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))) :
    Q.wellConnectedIn Q.threeQuarterCube.vertices ω := by
  let k : ℕ := 3 ^ Q.scale / 20
  have hk : 20 * (k : ℤ) ≤ Q.side := by
    have h := Nat.div_mul_le_self (3 ^ Q.scale) 20
    have h' : ((3 ^ Q.scale / 20 * 20 : ℕ) : ℤ) ≤ ((3 ^ Q.scale : ℕ) : ℤ) := by
      exact_mod_cast h
    have hs : ((3 ^ Q.scale : ℕ) : ℤ) = Q.side := by
      simp only [TriadicCube.side, Nat.cast_pow, Nat.cast_ofNat]
    push_cast at h'
    change 20 * (((3 ^ Q.scale / 20 : ℕ) : ℤ)) ≤ Q.side
    omega
  have hk0 : 0 ≤ (k : ℤ) := by positivity
  apply Q.wellConnectedIn_of_crossing_overlaps hd hside Q.threeQuarterCube.vertices
    ((k : ℤ) - 1) (by omega) hroot hQ
  intro R hR
  obtain ⟨hcross, hcoal⟩ := htests R hR
  obtain ⟨T, hsize, hTQ, hTR⟩ := Q.exists_overlap_cube_threeQuarter hR
  obtain ⟨overlapRoot, hoverlap⟩ := hoverlap T hsize hTQ
  exact ⟨hcross, hcoal, T, overlapRoot, by rw [hsize], hTQ, hTR, hoverlap⟩

end Rigidity.Percolation

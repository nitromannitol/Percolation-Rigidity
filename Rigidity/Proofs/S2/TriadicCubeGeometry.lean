import Rigidity.Proofs.S2.ClusterDensityFromDarioGu
import Rigidity.Proofs.Percolation.BondShells

/-!
# Triadic cubes and lattice bond shells

Every triadic cube lies in a centered lattice cube at the same length scale.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.External

/-- A triadic cube is contained in a lattice cube of radius its sidelength. -/
theorem triadicCube_subset_cubeAt {d : ℕ} (m : ℕ) (k : Vertex d) :
    triadicCube d m k ⊆ cubeAt (fun i => (3 : ℤ) ^ m * k i) (3 ^ m) := by
  intro x hx i
  have h := hx i
  have h3 : 0 ≤ (3 : ℝ) ^ m := by positivity
  have h' : |(x i : ℝ) - (((3 : ℤ) ^ m * k i : ℤ) : ℝ)| ≤ ((3 ^ m : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h'

end Rigidity.Proofs.S2

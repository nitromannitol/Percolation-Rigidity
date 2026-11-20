import Rigidity.Percolation.TriadicWellConnectedEvent
import Rigidity.Percolation.TriadicLocalizationCentered

/-!
# Geometry of well-connectedness test cubes

Every test cube meeting a subset of a triadic cube is contained in the
concentric threefold enlargement of that triadic cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A test cube meeting the ambient triadic cube is contained in its
concentric threefold enlargement. -/
theorem TriadicCube.testCube_vertices_subset_centeredTriple {d : ℕ}
    {Q : TriadicCube d} {interior : Set (Vertex d)} (hinterior : interior ⊆ Q.vertices)
    {R : IntegerCube d} (hR : R ∈ Q.testCubes interior) :
    (↑R.vertices : Set (Vertex d)) ⊆ Q.centeredTriple := by
  obtain ⟨_, hsize, x, hxR, hxI⟩ := hR
  have hxQ := hinterior hxI
  intro y hy i
  have hx := (IntegerCube.mem_vertices R x).mp hxR i
  have hy' := (IntegerCube.mem_vertices R y).mp hy i
  have hq := hxQ i
  change |2 * (y i - Q.center i)| < 3 * Q.side
  change |2 * (x i - Q.center i)| < Q.side at hq
  have hq' := abs_lt.mp hq
  apply abs_lt.mpr
  omega

end Rigidity.Percolation

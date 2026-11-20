import Rigidity.Percolation.SlabCrossingLargePaths
import Rigidity.Percolation.PisztoraDiameter

/-!
# Slab connectivity and radius-based path estimates

The cube-crossing bound for paths of large coordinate diameter also bounds the
radius-based event used in the percolation crossing estimates.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- Full-slab two-point connectivity bounds failure of the cube-crossing
component that connects every path above a prescribed lattice-radius scale. -/
theorem IntegerCube.measureReal_no_crossing_connecting_radius_le_of_twoPoint_slabs {d : ℕ}
    (hd : 0 < d) (Q : IntegerCube d) (j i : Fin d) (hij : i ≠ j)
    (width k₀ N radius : ℕ) (hwidth : 0 < width) (hstart : 0 < k₀ * width)
    (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (hradius : 10 * d * ((N + 1) * width - 1) ≤ radius)
    (p : unitInterval) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hprob : ∀ t : Fin d, ∀ k : ℕ, (k + 1) * width ≤ Q.size →
      ∀ x ∈ Q.slab t width k, ∀ y ∈ Q.slab t width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab t width k)).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ¬ HasCrossingComponentConnectingPaths ω Q.vertices
      (fun t => ↑(Q.lowerFace t)) (fun t => ↑(Q.upperFace t))
      (fun n γ => ∀ z : Vertex d, ∃ a : Fin (n + 1),
        (radius : ℤ) < 10 * ∑ k, |γ a k - z k|)} ≤
      ((1 - ρ) ^ (Q.size / width) +
        ((Q.lowerFace j).card : ℝ) * (1 - (p : ℝ) * ρ ^ (2 * d)) ^ N) +
      ((d * Q.size : ℕ) : ℝ) * ((Q.vertices.card : ℝ) ^ 2 *
        (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N) := by
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (Q.measureReal_no_crossing_connecting_paths_le_of_twoPoint_slabs j i hij width k₀ N
      hwidth hstart hsize p ρ hρ hρ₁ hprob)
  intro ω hfail hdiam
  have hpos : 0 < (N + 1) * width := Nat.mul_pos (by omega) hwidth
  have hcast : (((N + 1) * width - 1 : ℕ) : ℤ) + 1 =
      (((N + 1) * width : ℕ) : ℤ) := by
    have h := Nat.sub_add_cancel (show 1 ≤ (N + 1) * width by omega)
    exact_mod_cast h
  apply hfail
  apply HasCrossingComponentConnectingPaths.of_coordinate_diameter hd radius
    ((N + 1) * width - 1) hradius
  simpa only [hcast] using hdiam

end Rigidity.Percolation

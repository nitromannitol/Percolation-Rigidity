import Rigidity.Percolation.CrossingRootCoalescence
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

/-!
# Crossing paths and crossing components

A crossing component of a nontrivial cube contains a selected path. If all
selected paths coalesce inside the cube, its crossing component is unique.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- A crossing root is connected to a selected path in a nontrivial triadic
cube in positive dimension. -/
theorem TriadicCube.exists_selected_path_of_crossingRoot {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) (hside : 2 ≤ Q.side)
    {ω : Configuration d} {root : Vertex d}
    (hroot : IsCrossingRoot ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root) :
    ∃ n γ, IsSelectedOpenPath ω Q.vertices Q.largePath n γ ∧
      (openIn ω Q.vertices).Reachable root (γ 0) := by
  let t : Fin d := ⟨0, hd⟩
  obtain ⟨⟨y, hyQ, hyl, hy⟩, ⟨z, _, hzu, hz⟩⟩ := hroot.2 t
  have hyl' := ((IntegerCube.mem_lowerFace Q.toIntegerCube t y).mp hyl).2
  have hzu' := ((IntegerCube.mem_upperFace Q.toIntegerCube t z).mp hzu).2
  have hcast : (Q.toIntegerCube.size : ℤ) = Q.side := by
    simp only [toIntegerCube, side, Nat.cast_pow, Nat.cast_ofNat]
  have hsep : Q.side ≤ 10 * |y t - z t| := by
    have hbound := neg_abs_le (y t - z t)
    omega
  let w := (hy.symm.trans hz).some
  let γ : Fin (w.length + 1) → Vertex d := fun j => w.getVert j.val
  have hfirst : γ 0 = y := by simp only [γ, Fin.val_zero, SimpleGraph.Walk.getVert_zero]
  have hlast : γ (Fin.last w.length) = z := by
    simp only [γ, Fin.val_last, SimpleGraph.Walk.getVert_length]
  refine ⟨w.length, γ, ?_, ?_⟩
  · refine ⟨⟨0, Fin.last w.length, t, ?_⟩, ?_, ?_⟩
    · simpa only [hfirst, hlast] using hsep
    · simpa only [hfirst] using hyQ
    · intro i
      exact w.adj_getVert_succ i.isLt
  · simpa only [hfirst] using hy

/-- If large paths coalesce in a nontrivial triadic cube, all of its crossing
roots belong to the same component. -/
theorem TriadicCube.crossingRootsCoalesce_of_largePathsCoalesce {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) (hside : 2 ≤ Q.side)
    {ω : Configuration d} (hcoal : LargePathsCoalesce ω Q.vertices Q.largePath) :
    CrossingRootsCoalesce ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) := by
  intro root root' hroot hroot'
  obtain ⟨n, γ, hγ, hreach⟩ := Q.exists_selected_path_of_crossingRoot hd hside hroot
  obtain ⟨m, η, hη, hreach'⟩ := Q.exists_selected_path_of_crossingRoot hd hside hroot'
  exact hreach.trans ((hcoal n γ hγ m η hη).trans hreach'.symm)

end Rigidity.Percolation

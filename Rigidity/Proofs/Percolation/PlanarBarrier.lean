import Rigidity.Proofs.Percolation.PlanarBoxGeometry

/-!
# Open crossing barriers

A path crossing a strip of a planar cube meets a transverse open crossing of that strip.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- An open path through a horizontal strip joins its horizontal crossing inside the cube. -/
theorem horizontal_barrier_connects {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {L U : ℤ} {a b c d : Vertex 2}
    (hbar : ReachIn ω (cubeAt x N ∩ {v | L ≤ v 1 ∧ v 1 ≤ U}) a b)
    (ha : a 0 = x 0 - N) (hb : b 0 = x 0 + N)
    (hpath : ReachIn ω (cubeAt x N) c d) (hc : c 1 ≤ L) (hd : U ≤ d 1) :
    ReachIn ω (cubeAt x N) a c := by
  have hcoord : ∀ w ∈ cubeAt x N, x 0 - N ≤ w 0 ∧ w 0 ≤ x 0 + N := by
    intro w hw
    have h := abs_le.mp (hw 0)
    constructor <;> omega
  obtain ⟨z, h₁, h₂⟩ := exists_reachIn_of_crossing hbar hpath
    (xa := x 0 - N) (xb := x 0 + N) (ya := L) (yb := U)
    (fun _ hw => hw.2) hcoord (le_of_eq ha) (le_of_eq hb.symm) hc hd
  exact (h₁.mono Set.inter_subset_left).trans h₂.symm

/-- An open path through a vertical strip joins its vertical crossing inside the cube. -/
theorem vertical_barrier_connects {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {L U : ℤ} {a b c d : Vertex 2}
    (hbar : ReachIn ω (cubeAt x N ∩ {v | L ≤ v 0 ∧ v 0 ≤ U}) a b)
    (ha : a 1 = x 1 - N) (hb : b 1 = x 1 + N)
    (hpath : ReachIn ω (cubeAt x N) c d) (hc : c 0 ≤ L) (hd : U ≤ d 0) :
    ReachIn ω (cubeAt x N) a c := by
  have hcoord : ∀ w ∈ cubeAt x N, x 1 - N ≤ w 1 ∧ w 1 ≤ x 1 + N := by
    intro w hw
    have h := abs_le.mp (hw 1)
    constructor <;> omega
  obtain ⟨z, h₁, h₂⟩ := exists_reachIn_of_crossing hpath hbar
    (xa := L) (xb := U) (ya := x 1 - N) (yb := x 1 + N)
    hcoord (fun _ hw => hw.2) hc hd (le_of_eq ha) (le_of_eq hb.symm)
  exact (h₂.mono Set.inter_subset_left).trans h₁.symm

end Rigidity.Percolation

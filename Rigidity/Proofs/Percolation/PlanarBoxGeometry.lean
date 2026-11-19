import Rigidity.External.WellConnected
import Rigidity.Proofs.Section5.LoopFromCrossings

/-!
# Intersections of planar cube crossings

Horizontal and vertical open crossings of a planar cube are joined inside the cube.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- Horizontal and vertical open paths crossing a cube meet inside it. -/
theorem cube_crossings_meet {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {a b c d : Vertex 2}
    (ha : a 0 = x 0 - N) (hb : b 0 = x 0 + N)
    (hc : c 1 = x 1 - N) (hd : d 1 = x 1 + N)
    (hH : ReachIn ω (cubeAt x N) a b) (hV : ReachIn ω (cubeAt x N) c d) :
    ∃ w, ReachIn ω (cubeAt x N) a w ∧ ReachIn ω (cubeAt x N) c w := by
  apply exists_reachIn_of_crossing hH hV
    (xa := x 0 - N) (xb := x 0 + N) (ya := x 1 - N) (yb := x 1 + N)
  · intro w hw
    have h := abs_le.mp (hw 1)
    constructor <;> omega
  · intro w hw
    have h := abs_le.mp (hw 0)
    constructor <;> omega
  · exact le_of_eq ha
  · exact le_of_eq hb.symm
  · exact le_of_eq hc
  · exact le_of_eq hd.symm

end Rigidity.Percolation

import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Rigidity.Frozen.VertexV1

open scoped BigOperators

namespace RigidityFinitePatch

abbrev Bond (d : ℕ) :=
  {e : Sym2 (Vertex d) // ∃ x y : Vertex d,
    e = s(x, y) ∧ (∑ i, |x i - y i|) = 1}

end RigidityFinitePatch

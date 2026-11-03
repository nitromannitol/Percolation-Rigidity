import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homotopy.Path

/-! The Jordan curve theorem on the sphere `S²` (literature input; the part of Lemma 2.14 of the
corrected draft used by Lemma 2.16): the complement of a simple closed curve has exactly two
connected components, both open, each with the curve as its frontier.

Source: A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Proposition 2B.1 and
the remark after it (p. 169): a subspace of `S²` homeomorphic to `S¹` separates `S²` into two
complementary components (2B.1(b) with `n = 2`, `k = 1`), which are open and path-connected. The
range of a closed path injective on `[0, 1)` is such a subspace, and the frontier clause follows
from 2B.1(a): the complement in `S²` of an arc of the curve is connected. Also W. Rudin, *Real and
Complex Analysis*, Chapter 14 (the Jordan curve theorem), as cited in the paper; in the plane,
M. H. A. Newman, *Elements of the Topology of Plane Sets of Points*, Chapter V.

Lemma 2.14 as printed says "continuous loop"; the theorem is for simple loops, which is how it is
stated here (a closed path injective on `[0, 1)`). -/

namespace Rigidity.External

/-- The unit sphere `S²` of `ℝ³`. -/
abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- **Jordan curve theorem on `S²`** (literature input). -/
def JordanCurveTheoremSphere : Prop :=
  ∀ (q : S2) (β : Path q q), Set.InjOn β (Set.Ico 0 1) →
    ∃ U V : Set S2, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (Set.range β)ᶜ ∧ frontier U = Set.range β ∧ frontier V = Set.range β

end Rigidity.External

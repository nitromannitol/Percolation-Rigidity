import LatticeProb.Prob.Percolation.LatticeBondCritical
import LatticeProb.Prob.Percolation.LatticeBondGraph

/-! Open crossings of long rectangles in supercritical planar bond percolation (literature input):
the rectangle `[0, m] × [0, n]` has an open crossing in its first direction, inside it, outside an
event of probability at most `C (m + 1) exp(-c n)`. Used for the loops around annuli (Lemma 5.14),
the Kesten channels of very good boxes (Section 5.3.2) and step:5.24-crossings.

Source: H. Kesten, *Percolation Theory for Mathematicians*, Birkhäuser (1982), Theorem 11.1,
equation (11.4), for the covering graph `𝒢₁` of `ℤ²` (bond percolation, Example 2.1(ii)), with
`p_H(𝒢₁) = p_c(2)`: for `p > p_H` there are at least `C₁ (p - p_H)^{δ₁} n` disjoint open horizontal
crossings of `[0, m] × [0, n]` with probability at least `1 - C₂ (m + 1) exp(-C₃ (p - p_H)^{δ₂} n)`;
only the existence of one crossing is used. Stated here for every translate and, by the symmetry of
`ℤ²` exchanging the coordinates, for both directions. -/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.External

/-- The rectangle `x + R`, where `R` is `[0, m]` in direction `i` and `[0, n]` in the other one. -/
def crossingRectangle (x : Vertex 2) (m n : ℕ) (i : Fin 2) : Set (Vertex 2) :=
  {y | ∀ j, x j ≤ y j ∧ y j ≤ x j + (if j = i then (m : ℤ) else n)}

/-- An open path inside `x + R` joins its two faces orthogonal to direction `i`. -/
def HasOpenCrossing (ω : Configuration 2) (x : Vertex 2) (m n : ℕ) (i : Fin 2) : Prop :=
  ∃ (y z : Vertex 2) (hy : y ∈ crossingRectangle x m n i) (hz : z ∈ crossingRectangle x m n i),
    y i = x i ∧ z i = x i + m ∧
      ((openGraph ω).induce (crossingRectangle x m n i)).Reachable ⟨y, hy⟩ ⟨z, hz⟩

/-- **Kesten, Theorem 11.1** (literature input). -/
def KestenRectangleCrossing : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (m n : ℕ) (i : Fin 2),
      latticeBondLaw 2 p {ω | ¬ HasOpenCrossing ω x m n i} ≤
        ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n)))

end Rigidity.External

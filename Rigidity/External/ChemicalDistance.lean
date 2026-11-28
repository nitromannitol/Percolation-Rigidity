import LatticeProb.Prob.Percolation.LatticeBondCritical
import LatticeProb.Prob.Percolation.LatticeBondGraph

/-! The chemical distance in supercritical bond percolation: two connected sites at Euclidean
distance `L` are joined by an open path of length at most `ρ L` outside an event of probability
exponentially small in `L`. It is stated as a proposition; no numbered result and no proof in the
library uses it.

Source: P. Antal and A. Pisztora, *On the chemical distance for supercritical Bernoulli
percolation*, Ann. Probab. 24 (1996), Theorem 1.1, which states, for `p > p_c(d)`, that
`limsup_{|y| → ∞} |y|⁻¹ log P[0 ↔ y, D(0, y) > ρ |y|] < 0` for some `ρ < ∞`. Stated here for all
pairs `x, y` (translation invariance) with the `ℓ¹` distance, and with a constant `C` absorbing the
finitely many short distances. `D` is the graph distance of the open subgraph. -/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.External

/-- **Antal–Pisztora, Theorem 1.1**, stated as a proposition; no proof uses it. -/
def AntalPisztoraChemicalDistance : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ 0 < C ∧ ∀ x y : Vertex d,
      latticeBondLaw d p {ω | (openGraph ω).Reachable x y ∧
          ρ * (∑ i, |((x i - y i : ℤ) : ℝ)|) < (openGraph ω).dist x y} ≤
        ENNReal.ofReal (C * Real.exp (-(c * ∑ i, |((x i - y i : ℤ) : ℝ)|)))

end Rigidity.External

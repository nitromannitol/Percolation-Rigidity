import Rigidity.Proofs.Section5.AnnulusCrossings
import LatticeProb.Lattice.Planar.Winding
import PercolationClusterHomogenization.Proofs.Planar.LoopFromCrossings

/-!
# Lemma 5.14: the loop around an annulus from the crossings

This file proves `LoopFromCrossingsStep` (`step:5.14-planarity`),
the deterministic planarity step of Lemma 5.14 (corrected draft L1945-1959). No literature input
is used: the only planar topology is the following discrete crossing lemma.

* `exists_reachIn_of_crossing`: an open path in the horizontal strip `ℝ × [y_a, y_b]` from
  `x ≤ x_a` to `x ≥ x_b` and an open path in the vertical strip `[x_a, x_b] × ℝ` from `y ≤ y_a` to
  `y ≥ y_b` share a vertex. Its proof uses the crossing number `LatticeProb.Lattice.Planar.wind`
  of the horizontal path with the eastward ray from a point: along the vertical path, this
  crossing number plus the indicator of lying above the endpoint of the horizontal path is
  constant, while it equals `0` at the bottom and `1` at the top.

The loop at scale `R` is built from the four crossings of the annulus `Q_{2R} \ Q_R`: the bottom
crossing meets the left and the right crossings, the top crossing meets them too, and the four
arcs between the four meeting points form a closed walk. Along the bottom, right and top arcs the
principal argument is continuous (the arcs lie in the open lower, right and upper half-planes),
and along the left arc the argument of `-z` is; summing the increments gives `2π`, so the winding
number is `1`. The radial crossings join the right crossing at scale `R` to the right crossing at
scale `2R`, so the loop is joined by open paths to vertices with arbitrarily large first
coordinate: its open cluster is infinite, hence it is the unique infinite cluster.

With `crossingProbabilityStep` and `borelCantelliStep` (`AnnulusCrossings.lean`), this gives
Lemma 5.14 (`loopsAroundAnnuli`) from Kesten's crossing estimate `KestenRectangleCrossing` and the
almost sure uniqueness of the infinite cluster.
-/

open MeasureTheory LatticeProb.Percolation LatticeProb.Lattice

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.External Rigidity.Steps.Section5

/-! ### Crossing numbers of open lattice walks -/

/-! ### Open paths inside a set and the crossing lemma -/

variable {ω : Configuration 2}

/-! ### The winding number of a loop made of four arcs -/

theorem toComplex_ne_zero_of_re {v : Vertex 2} (h : v 0 ≠ 0) : toComplex v ≠ 0 := fun h0 =>
  h (by exact_mod_cast (toComplex_re v).symm.trans (congrArg Complex.re h0))

/-! ### The crossings at all scales lie in the unique infinite cluster -/

/-! ### The loop around the annulus -/

/-- **Step `step:5.14-planarity`** of Lemma 5.14: crossings at all sufficiently large scales
give loops in the unique infinite cluster at all sufficiently large scales. -/
theorem loopFromCrossingsStep : LoopFromCrossingsStep := by
  intro ω h M hM
  exact ⟨M + 1, fun R hR => loop_at_scale_of_crossings ω h M hM R hR⟩

/-- **Lemma 5.14** (`lemma:loops-around-annuli`): for `p > p_c(2)`, almost surely there is a scale
`M` such that for every `R ≥ M` the unique infinite cluster contains a loop in `Q_{2R} \ Q_R` with
nonzero winding number around the origin. Inputs: Kesten's crossing estimate (Theorem 11.1) and
the almost sure uniqueness of the infinite cluster. -/
theorem loopsAroundAnnuli {p : unitInterval} (hK : KestenRectangleCrossing)
    (hpc : criticalProbability 2 < (p : ℝ)) (hU : UniqueClusterAe p) :
    LoopsAroundAnnuliStmt p :=
  loopsAroundAnnuli_of_steps hK hpc hU crossingProbabilityStep borelCantelliStep
    loopFromCrossingsStep

end Rigidity.Proofs.Section5

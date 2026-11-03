import Mathlib
import Rigidity.Proofs.Assembly.Main
import RigidityAudit.IntegerLinearGrowth.SolutionBasic

/-!
# Bridge: the `IntegerLinearGrowth` audit vocabulary is the library's

Each definition of the audit vocabulary (`RigidityAudit/IntegerLinearGrowth/SolutionBasic.lean`,
a verbatim copy of the vocabulary block of `Challenge.lean`) is a token-for-token copy of a
definition of the library's `lattice-probability` dependency, so the two are definitionally
equal: every identification below is `rfl`.
-/

open MeasureTheory

namespace Rigidity
namespace StatementAudit
namespace IntegerLinearGrowth

theorem lattice_eq (d : ℕ) : lattice d = LatticeProb.lattice d := rfl

theorem bondOfAdjacent_eq {d : ℕ} {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent h = LatticeProb.Percolation.bondOfAdjacent h := rfl

theorem openGraph_eq {d : ℕ} (ω : Configuration d) :
    openGraph ω = LatticeProb.Percolation.openGraph ω := rfl

theorem componentLaplacian_eq {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (x : C) :
    componentLaplacian C u x = LatticeProb.Percolation.componentLaplacian C u x := rfl

theorem latticeBondLaw_eq (d : ℕ) (p : unitInterval) :
    latticeBondLaw d p = LatticeProb.Percolation.latticeBondLaw d p := rfl

theorem theta_eq (d : ℕ) (p : unitInterval) :
    theta d p = LatticeProb.Percolation.theta d p := rfl

theorem criticalProbability_eq (d : ℕ) [NeZero d] :
    criticalProbability d = LatticeProb.Percolation.criticalProbability d := rfl

theorem hasUniqueInfiniteOpenComponent_iff {d : ℕ} (ω : Configuration d) :
    HasUniqueInfiniteOpenComponent ω ↔
      LatticeProb.Percolation.HasUniqueInfiniteOpenComponent ω := Iff.rfl

theorem uniqueInfiniteComponent_eq {d : ℕ} {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) :
    uniqueInfiniteComponent h = LatticeProb.Percolation.uniqueInfiniteComponent h := rfl

theorem supercriticalBondUniqueness_iff :
    SupercriticalBondUniqueness ↔ LatticeProb.External.SupercriticalBondUniqueness := Iff.rfl

theorem componentPointwiseLinearGrowth_iff {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) :
    componentPointwiseLinearGrowth C u ↔
      LatticeProb.Percolation.componentPointwiseLinearGrowth C u := Iff.rfl

theorem componentEuclideanBall_eq {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) :
    componentEuclideanBall C z r = LatticeProb.Percolation.componentEuclideanBall C z r := rfl

theorem componentBallL2_eq {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) (u : C → ℝ) :
    componentBallL2 C z r u = LatticeProb.Percolation.componentBallL2 C z r u := rfl

theorem harmonicGrowthSpace_eq {d : ℕ} {ω : Configuration d} (C : OpenComponent ω) (k : ℕ) :
    harmonicGrowthSpace C k = LatticeProb.Percolation.harmonicGrowthSpace C k := rfl

theorem isCorrectedPlane_iff {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (q : Fin d → ℝ) (u : C → ℝ) :
    IsCorrectedPlane C q u ↔ LatticeProb.Percolation.IsCorrectedPlane C q u := Iff.rfl

theorem supercriticalBondCorrectorInput_iff :
    SupercriticalBondCorrectorInput ↔ LatticeProb.External.SupercriticalBondCorrectorInput :=
  Iff.rfl

end IntegerLinearGrowth
end StatementAudit
end Rigidity

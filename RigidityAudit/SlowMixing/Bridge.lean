import Mathlib
import Rigidity.Proofs.Assembly.Main
import RigidityAudit.SlowMixing.SolutionBasic

/-!
# Bridge: the `SlowMixing` audit vocabulary is the library's

Each definition of the audit vocabulary (`RigidityAudit/SlowMixing/SolutionBasic.lean`, a
verbatim copy of the vocabulary block of `Challenge.lean`) is a token-for-token copy of a
definition of the library or of its `lattice-probability` dependency, so the two are
definitionally equal: every identification below is `rfl`.  The last one identifies the
conclusion of the challenge theorem with the library's statement of Theorem 6.5,
`Rigidity.Section6.SlowMixingStmt`.
-/

open MeasureTheory Classical Filter

namespace Rigidity
namespace StatementAudit
namespace SlowMixing

theorem lattice_eq (d : ℕ) : lattice d = LatticeProb.lattice d := rfl

theorem bondOfAdjacent_eq {d : ℕ} {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent h = LatticeProb.Percolation.bondOfAdjacent h := rfl

theorem openGraph_eq {d : ℕ} (ω : Configuration d) :
    openGraph ω = LatticeProb.Percolation.openGraph ω := rfl

theorem degree_eq {d : ℕ} (ω : Configuration d) (x : Vertex d) :
    (openGraph ω).degree x = (LatticeProb.Percolation.openGraph ω).degree x := rfl

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

theorem isWellConnected_iff {d : ℕ} (ω : Configuration d) (x : Vertex d) (R : ℕ) :
    IsWellConnected ω x R ↔ Rigidity.External.IsWellConnected ω x R := Iff.rfl

theorem wellConnectedInput_iff :
    WellConnectedInput ↔ Rigidity.External.WellConnectedInput := Iff.rfl

theorem dualLattice_eq {N k : ℕ} (b : Fin k → EuclideanSpace ℝ (Fin N)) :
    dualLattice b = Rigidity.External.dualLattice b := rfl

theorem micciancioRegevSmoothing_iff :
    MicciancioRegevSmoothing ↔ Rigidity.External.MicciancioRegevSmoothing := Iff.rfl

theorem isLargestBoxCluster_iff {d : ℕ} (ω : Configuration d) (n : ℕ) (V : Finset (Vertex d)) :
    IsLargestBoxCluster ω n V ↔ Rigidity.Section6.IsLargestBoxCluster ω n V := Iff.rfl

theorem toppling_eq {d : ℕ} (ω : Configuration d) (V : Finset (Vertex d)) :
    toppling ω V = Rigidity.Section6.toppling ω V := rfl

theorem sandpileGroup_eq {d : ℕ} (ω : Configuration d) (V : Finset (Vertex d)) :
    SandpileGroup ω V = Rigidity.Section6.SandpileGroup ω V := rfl

theorem chainLaw_eq {d : ℕ} (ω : Configuration d) (V : Finset (Vertex d)) (t : ℕ)
    (g : SandpileGroup ω V) :
    chainLaw ω V t g = Rigidity.Section6.chainLaw ω V t g := rfl

theorem l2DistSq_eq {d : ℕ} (ω : Configuration d) (V : Finset (Vertex d)) (t : ℕ) :
    l2DistSq ω V t = Rigidity.Section6.l2DistSq ω V t := rfl

/-- The conclusion of the challenge theorem is the library's statement of Theorem 6.5. -/
theorem slowMixingStmt_iff (d : ℕ) [NeZero d] (p : unitInterval) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∃ V : Finset (Vertex d), IsLargestBoxCluster ω n V ∧
          ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) ∧
        ∀ V : Finset (Vertex d), IsLargestBoxCluster ω n V →
          (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) → (∃ x ∈ V, ∃ i, |x i| = (n : ℤ)) →
          (∀ t : ℕ, C * (n : ℝ) ^ d * Real.log n ≤ t → l2DistSq ω V t ≤ ε) ∧
          (∀ t : ℕ, (t : ℝ) ≤ c * (n : ℝ) ^ d * Real.log n → ε ≤ l2DistSq ω V t)) ↔
      Rigidity.Section6.SlowMixingStmt d p := Iff.rfl

end SlowMixing
end StatementAudit
end Rigidity

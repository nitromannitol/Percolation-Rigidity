import Mathlib
import Rigidity.Proofs.Assembly.Unconditional
import RigidityAudit.SlowMixing.SolutionBasic

/-!
# Solution: `SlowMixingUnconditional` (Theorem 6.5 with no literature input)

Proves `Rigidity.StatementAudit.SlowMixing.slow_mixing_unconditional`, with the statement of
`RigidityAudit/SlowMixingUnconditional/Challenge.lean`, from
`Rigidity.Assembly.Unconditional.slow_mixing` (`Rigidity/Proofs/Assembly/Unconditional.lean`), whose only
hypotheses are the regime.  The vocabulary is that of `RigidityAudit/SlowMixing/SolutionBasic.lean`, a
token-for-token copy of the library's, so the conclusion of the library theorem is definitionally the
restated one, as in `RigidityAudit/SlowMixing/Solution.lean`.
-/

namespace Rigidity
namespace StatementAudit
namespace SlowMixing

open MeasureTheory Classical Filter

/-- **Theorem 6.5** (`theorem:slow-mixing-percolation`) with the regime `2 ≤ d`, `p_c(d) < p < 1` as
its only hypotheses. -/
theorem slow_mixing_unconditional (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∃ V : Finset (Vertex d), IsLargestBoxCluster ω n V ∧
          ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) ∧
        ∀ V : Finset (Vertex d), IsLargestBoxCluster ω n V →
          (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) → (∃ x ∈ V, ∃ i, |x i| = (n : ℤ)) →
          (∀ t : ℕ, C * (n : ℝ) ^ d * Real.log n ≤ t → l2DistSq ω V t ≤ ε) ∧
          (∀ t : ℕ, (t : ℝ) ≤ c * (n : ℝ) ^ d * Real.log n → ε ≤ l2DistSq ω V t)
:= by
  exact Rigidity.Assembly.Unconditional.slow_mixing d hd p hpc hp1

end SlowMixing
end StatementAudit
end Rigidity

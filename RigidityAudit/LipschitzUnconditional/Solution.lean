import Mathlib
import Rigidity.Proofs.Assembly.Unconditional
import RigidityAudit.Lipschitz.SolutionBasic

/-!
# Solution: `LipschitzUnconditional` (Theorem 1.1 with no literature input)

Proves `Rigidity.StatementAudit.Lipschitz.lipschitz_unconditional`, with the statement of
`RigidityAudit/LipschitzUnconditional/Challenge.lean`, from
`Rigidity.Assembly.Unconditional.lipschitz` (`Rigidity/Proofs/Assembly/Unconditional.lean`), whose
only hypotheses are the regime.  The vocabulary is that of
`RigidityAudit/Lipschitz/SolutionBasic.lean`, a token-for-token copy of the library's, so the
conclusion of the library theorem is definitionally the restated one, as in
`RigidityAudit/Lipschitz/Solution.lean`.
-/

open MeasureTheory Filter

namespace Rigidity
namespace StatementAudit
namespace Lipschitz

/-- **Theorem 1.1** (`theorem:lipschitz`) with the regime `2 ≤ d`, `p_c(d) < p < 1` as its only
hypotheses. -/
theorem lipschitz_unconditional (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          ComponentLipschitz (uniqueInfiniteComponent h) u →
          ∃ c : ℝ, ∀ x, u x = c
:= by
  exact Rigidity.Assembly.Unconditional.lipschitz d hd p hpc hp1

end Lipschitz
end StatementAudit
end Rigidity

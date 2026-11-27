import Mathlib
import Rigidity.Proofs.Assembly.Unconditional
import RigidityAudit.FastDecay.SolutionBasic

/-!
# Solution: `FastDecayUnconditional` (Theorem 1.3 with no literature input)

Proves `Rigidity.StatementAudit.FastDecay.fast_decay_unconditional`, with the statement of
`RigidityAudit/FastDecayUnconditional/Challenge.lean`, from
`Rigidity.Assembly.Unconditional.fast_decay` (`Rigidity/Proofs/Assembly/Unconditional.lean`),
whose only hypotheses are the regime.  The vocabulary is that of
`RigidityAudit/FastDecay/SolutionBasic.lean`, a token-for-token copy of the library's, so the
conclusion of the library theorem is definitionally the restated one, as in
`RigidityAudit/FastDecay/Solution.lean`.
-/

namespace Rigidity
namespace StatementAudit
namespace FastDecay

/-- **Theorem 1.3** (`theorem:fast-decay`, fast decay, `d = 2`): for `p_c(2) < p < 1`, almost
surely the infinite cluster `𝒞_∞` exists and is unique, and for every finitely supported
`f : ℤ² → ℤ`, every `u : 𝒞_∞ → ℝ` with `-Δu = f` and
`lim sup_R R sup_{𝒞_∞ ∩ (B_R \ B_{R/2})} |u| = 0` has finite support.  The regime is the only
hypothesis. -/
theorem fast_decay_unconditional (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    FastDecayStmt p := by
  exact Rigidity.Assembly.Unconditional.fast_decay p hpc hp1

end FastDecay
end StatementAudit
end Rigidity

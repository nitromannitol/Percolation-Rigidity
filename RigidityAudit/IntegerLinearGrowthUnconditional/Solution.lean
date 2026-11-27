import Mathlib
import Rigidity.Proofs.Assembly.Unconditional
import RigidityAudit.IntegerLinearGrowth.SolutionBasic

/-!
# Solution: `IntegerLinearGrowthUnconditional` (Theorem 1.2 with no literature input)

Proves `Rigidity.StatementAudit.IntegerLinearGrowth.integer_valued_linear_growth_unconditional`,
with the statement of `RigidityAudit/IntegerLinearGrowthUnconditional/Challenge.lean`, from
`Rigidity.Assembly.Unconditional.integer_valued_linear_growth`
(`Rigidity/Proofs/Assembly/Unconditional.lean`), whose only hypotheses are the regime.  The
vocabulary is that of `RigidityAudit/IntegerLinearGrowth/SolutionBasic.lean`, a token-for-token
copy of the library's, so the conclusion of the library theorem is definitionally the restated
one, as in `RigidityAudit/IntegerLinearGrowth/Solution.lean`.
-/

namespace Rigidity
namespace StatementAudit
namespace IntegerLinearGrowth

open MeasureTheory

/-- **Theorem 1.2** (`theorem:integer-valued-linear-growth`): for `d ≥ 2` and `p_c(d) < p < 1`,
almost surely the infinite cluster `𝒞_∞` exists and is unique, and every harmonic, integer-valued
function `u : 𝒞_∞ → ℝ` of at most linear growth is a constant integer.  The regime is the only
hypothesis. -/
theorem integer_valued_linear_growth_unconditional (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (p : unitInterval) (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x : uniqueInfiniteComponent h,
            componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          (∀ x : uniqueInfiniteComponent h, ∃ z : ℤ, u x = (z : ℝ)) →
          componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u →
          ∃ a : ℤ, ∀ x : uniqueInfiniteComponent h, u x = (a : ℝ)
:= by
  exact Rigidity.Assembly.Unconditional.integer_valued_linear_growth d hd p hpc hp1

end IntegerLinearGrowth
end StatementAudit
end Rigidity

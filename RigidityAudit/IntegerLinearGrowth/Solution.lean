import Mathlib
import Rigidity.Proofs.Assembly.Main
import RigidityAudit.IntegerLinearGrowth.SolutionBasic
import RigidityAudit.IntegerLinearGrowth.Bridge

/-!
# Solution: `IntegerLinearGrowth` (Theorem 1.2, integer-valued harmonic functions)

The challenge module `RigidityAudit/IntegerLinearGrowth/Challenge.lean` imports only Mathlib and
states `integer_valued_linear_growth` with one intentional `sorry`.  This solution imports the
library together with `RigidityAudit.IntegerLinearGrowth.SolutionBasic`, a verbatim copy of the
challenge's statement vocabulary, and proves the byte-identical statement from
`Rigidity.Assembly.Main.integerValuedLinearGrowth` (`Rigidity/Proofs/Assembly/Main.lean`).

The transport is definitional.  The audit vocabulary (`latticeBondLaw`, `criticalProbability`,
`HasUniqueInfiniteOpenComponent`, `uniqueInfiniteComponent`, `componentLaplacian`,
`componentPointwiseLinearGrowth`, and the two cited results `SupercriticalBondUniqueness` and
`SupercriticalBondCorrectorInput`, with everything they mention) is a token-for-token copy of
the library's, so each hypothesis and the conclusion of the library theorem are definitionally
equal to the audit's; the identifications are recorded as `rfl` lemmas in
`RigidityAudit/IntegerLinearGrowth/Bridge.lean`.  The one `structure` value of the vocabulary,
the submodule `harmonicGrowthSpace`, has the same carrier as the library's; its closure proofs
are proof terms, equal by proof irrelevance, so no field-by-field repacking is needed.
-/

namespace Rigidity
namespace StatementAudit
namespace IntegerLinearGrowth

open MeasureTheory

/-- **Theorem 1.2** (`theorem:integer-valued-linear-growth`): for `d ≥ 2` and `p_c(d) < p < 1`,
almost surely the infinite cluster `𝒞_∞` exists and is unique, and every harmonic, integer-valued
function `u : 𝒞_∞ → ℝ` of at most linear growth is a constant integer.  The two cited results
enter as explicit hypotheses. -/
theorem integer_valued_linear_growth (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x : uniqueInfiniteComponent h,
            componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          (∀ x : uniqueInfiniteComponent h, ∃ z : ℤ, u x = (z : ℝ)) →
          componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u →
          ∃ a : ℤ, ∀ x : uniqueInfiniteComponent h, u x = (a : ℝ)
:= by
  exact Rigidity.Assembly.Main.integerValuedLinearGrowth d hd p hpc hp1 hUq hCorr

end IntegerLinearGrowth
end StatementAudit
end Rigidity

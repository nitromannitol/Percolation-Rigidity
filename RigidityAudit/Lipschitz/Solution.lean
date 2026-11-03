import Mathlib
import Rigidity.Proofs.Assembly.Main
import RigidityAudit.Lipschitz.SolutionBasic
import RigidityAudit.Lipschitz.Bridge

/-!
# Solution: `Lipschitz` (Lipschitz rigidity on the supercritical cluster)

The challenge module `RigidityAudit/Lipschitz/Challenge.lean` imports only Mathlib and states
`lipschitz` with one intentional `sorry`.  This solution imports the library `Rigidity` together
with `RigidityAudit.Lipschitz.SolutionBasic`, a verbatim copy of the challenge's statement
vocabulary, and proves the byte-identical statement from `Rigidity.Assembly.Main.lipschitz`
(`Rigidity/Proofs/Assembly/Main.lean`).

The transport is definitional.  The audit vocabulary (`latticeBondLaw`, `criticalProbability`,
`uniqueInfiniteComponent`, `componentLaplacian`, `ComponentLipschitz`, and the seven cited results
`SupercriticalBondUniqueness`, `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`,
`ArmstrongDarioOrderZero`, `SupercriticalBondGreenColumnExistence`,
`SupercriticalBondGreenQuantitative`, `WellConnectedInput`, with everything they mention) is a
token-for-token copy of the library's, so each hypothesis and the conclusion of the library
theorem are definitionally equal to the audit's; the identifications are recorded as `rfl` lemmas
in `RigidityAudit/Lipschitz/Bridge.lean`.  The vocabulary has no `structure`, so no
field-by-field repacking is needed.
-/

open MeasureTheory Filter

namespace Rigidity
namespace StatementAudit
namespace Lipschitz
/-! ## The theorem -/

/-- **Theorem 1.1** (`theorem:lipschitz`): for `d ≥ 2` and `p_c(d) < p < 1`, almost surely the
infinite cluster exists and is unique, and every function `u` on it that is harmonic
(`componentLaplacian u = 0` at every vertex) and Lipschitz for the graph distance of the cluster is
constant.  The seven cited results enter as explicit hypotheses. -/
theorem lipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput)
    (hCQ : CorrectorQuantitativeInput)
    (hAD : ArmstrongDarioOrderZero)
    (hE : SupercriticalBondGreenColumnExistence)
    (hGQ : SupercriticalBondGreenQuantitative)
    (hW : WellConnectedInput) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          ComponentLipschitz (uniqueInfiniteComponent h) u →
          ∃ c : ℝ, ∀ x, u x = c
:= by
  rw [supercriticalBondUniqueness_eq] at hUq
  rw [supercriticalBondCorrectorInput_eq] at hCorr
  rw [correctorQuantitativeInput_eq] at hCQ
  rw [armstrongDarioOrderZero_eq] at hAD
  rw [supercriticalBondGreenColumnExistence_eq] at hE
  rw [supercriticalBondGreenQuantitative_eq] at hGQ
  rw [wellConnectedInput_eq] at hW
  exact Rigidity.Assembly.Main.lipschitz d hd p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW

end Lipschitz
end StatementAudit
end Rigidity

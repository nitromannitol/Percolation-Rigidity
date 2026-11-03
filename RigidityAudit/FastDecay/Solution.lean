import Mathlib
import Rigidity.Proofs.Assembly.Main
import RigidityAudit.FastDecay.SolutionBasic

/-!
# Solution: `FastDecay` (Theorem 1.3, fast decay on the planar cluster)

The challenge module `RigidityAudit/FastDecay/Challenge.lean` imports only Mathlib and states
`fastDecay` with one intentional `sorry`.  This solution imports the library together with
`RigidityAudit.FastDecay.SolutionBasic`, a verbatim copy of the challenge's statement vocabulary,
and proves the byte-identical statement from `Rigidity.Assembly.Main.fastDecay`
(`Rigidity/Proofs/Assembly/Main.lean`).

The transport is definitional.  The audit vocabulary is a token-for-token copy of the library's
definitions (those of the `lattice-probability` dependency included), elaborated in the same
`open` and `variable` context, so each of the eleven hypotheses and the conclusion of the library
theorem are definitionally equal to the audit's.  The vocabulary has no `structure` or
`inductive` of its own, so no field-by-field repacking is needed; the proof terms that the copies
carry inside `SimpleGraph`, `Submodule` and subtype constructors differ from the library's only
up to proof irrelevance.
-/

namespace Rigidity
namespace StatementAudit
namespace FastDecay

/-- **Theorem 1.3** (fast decay, `d = 2`).  For `p_c(2) < p < 1`, almost surely the infinite
cluster `𝒞_∞` exists and is unique, and for every finitely supported `f : ℤ² → ℤ`, every
`u : 𝒞_∞ → ℝ` with `-Δu = f` and `lim sup_R R sup_{𝒞_∞ ∩ (B_R \ B_{R/2})} |u| = 0` has finite
support.  The eleven cited results enter as explicit hypotheses. -/
theorem fastDecay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput)
    (hCQ : CorrectorQuantitativeInput)
    (hAD : ArmstrongDarioOrderZero)
    (hAD1 : ArmstrongDarioOrderOneOrigin)
    (hE : SupercriticalBondGreenColumnExistence)
    (hGQ : SupercriticalBondGreenQuantitative)
    (hDG : ClusterDensityConcentrationInput)
    (hW : WellConnectedInput)
    (hK : KestenRectangleCrossing)
    (hJ : JordanCurveTheoremSphere) :
    FastDecayStmt p := by
  exact Rigidity.Assembly.Main.fastDecay p hpc hp1 hUq hCorr hCQ hAD hAD1 hE hGQ hDG hW hK hJ

end FastDecay
end StatementAudit
end Rigidity

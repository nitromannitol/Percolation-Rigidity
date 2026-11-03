import Mathlib
import Rigidity.Proofs.Assembly.Main
import RigidityAudit.SlowMixing.SolutionBasic
import RigidityAudit.SlowMixing.Bridge

/-!
# Solution: `SlowMixing` (Theorem 6.5, slow mixing of the sandpile chain)

The challenge module `RigidityAudit/SlowMixing/Challenge.lean` imports only Mathlib and states
`slow_mixing` with one intentional `sorry`.  This solution imports the library together with
`RigidityAudit.SlowMixing.SolutionBasic`, a verbatim copy of the challenge's statement
vocabulary, and proves the byte-identical statement from `Rigidity.Assembly.Main.slowMixing`
(`Rigidity/Proofs/Assembly/Main.lean`).

The transport is definitional.  The audit vocabulary (`latticeBondLaw`, `criticalProbability`,
`HasUniqueInfiniteOpenComponent`, `uniqueInfiniteComponent`, `IsLargestBoxCluster`, `l2DistSq`,
and the three cited results `SupercriticalBondUniqueness`, `WellConnectedInput`,
`MicciancioRegevSmoothing`, with everything they mention) is a token-for-token copy of the
library's, so each hypothesis and the conclusion of the library theorem are definitionally equal
to the audit's; the identifications are recorded as `rfl` lemmas in
`RigidityAudit/SlowMixing/Bridge.lean`.  The vocabulary has no `structure` or `inductive`, so no
field-by-field repacking is needed.
-/

namespace Rigidity
namespace StatementAudit
namespace SlowMixing

open MeasureTheory Classical Filter

/-- **Theorem 6.5** (`theorem:slow-mixing-percolation`): for `d ≥ 2` and `p_c(d) < p < 1` there
are `c, C > 0` such that, almost surely, the infinite cluster `𝒞_∞` exists and is unique, and for
every `ε > 0` and every large `n`, some largest open cluster `V` of `Q_n` lies in `𝒞_∞`, and for
every such `V` meeting the boundary of `Q_n` the sandpile chain on `V` satisfies
`‖P^t - U‖₂² ≤ ε` for `t ≥ C n^d log n` and `‖P^t - U‖₂² ≥ ε` for `t ≤ c n^d log n`.  The three
cited results enter as explicit hypotheses. -/
theorem slow_mixing (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness)
    (hW : WellConnectedInput)
    (hMR : MicciancioRegevSmoothing) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∃ V : Finset (Vertex d), IsLargestBoxCluster ω n V ∧
          ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) ∧
        ∀ V : Finset (Vertex d), IsLargestBoxCluster ω n V →
          (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) → (∃ x ∈ V, ∃ i, |x i| = (n : ℤ)) →
          (∀ t : ℕ, C * (n : ℝ) ^ d * Real.log n ≤ t → l2DistSq ω V t ≤ ε) ∧
          (∀ t : ℕ, (t : ℝ) ≤ c * (n : ℝ) ^ d * Real.log n → ε ≤ l2DistSq ω V t)
:= by
  exact Rigidity.Assembly.Main.slowMixing d hd p hpc hp1 hUq hW hMR

end SlowMixing
end StatementAudit
end Rigidity

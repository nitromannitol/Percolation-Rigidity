import Rigidity.Steps.Section5.FastDecayDichotomy

/-!
# Theorem 1.3: the steps of the fast-decay theorem

Theorem 1.3 (paper L113-122 of the corrected draft) is carved into Theorem 5.1
(`FastDecayDichotomyStmt`) and the deterministic annulus step `step:1.3-annulus`: the decay
`lim sup_R R sup_{B_R \ B_{R/2}} |u| = 0` gives `u → 0` at infinity and `|x| |u(x)| → 0`, so eq.
`linear-decay` fails and Theorem 5.1 gives eq. `compactly-supported`, that is finite support of `u`
on the cluster. The Laplacian `Δu = -f` is integer valued.
-/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- Step `step:1.3-annulus`: on an open component, the annulus decay
`lim sup_R R sup_{B_R \ B_{R/2}} |u| = 0` gives `u → 0` at infinity and excludes eq.
`linear-decay`, and eq. `compactly-supported` gives finite support. -/
def AnnulusStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u : C → ℝ),
    (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ x : C,
      R / 2 ≤ eucl x.val → eucl x.val < R → R * |u x| ≤ ε) →
      Tendsto u cofinite (𝓝 0) ∧ ¬LinearDecay C u ∧
        (EventuallyZero C u → (Function.support u).Finite)

/-- Theorem 1.3 from Theorem 5.1 and the annulus step. -/
theorem fastDecay_of_steps {p : unitInterval} (h51 : FastDecayDichotomyStmt p)
    (hann : AnnulusStep) : FastDecayStmt p := by
  filter_upwards [h51] with ω ⟨h, H⟩
  refine ⟨h, fun f _ u hu hdec => ?_⟩
  obtain ⟨h0, hlin, hfin⟩ := hann ω _ u hdec
  exact hfin ((H u h0 fun x => ⟨-f x.val, by push_cast; linarith [hu x]⟩).resolve_left hlin)

end Rigidity.Steps.Section5

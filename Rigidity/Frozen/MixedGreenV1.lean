import Rigidity.Frozen.MixedGreenEntryV1
import Rigidity.Support.MixedGreenResult
import LatticeProb.External.GreenQuantitative
import LatticeProb.External.ArmstrongDarioOrderZero
import LatticeProb.Prob.Percolation.GreenColumnEvent

open MeasureTheory LatticeProb.Percolation LatticeProb.External
open scoped BigOperators Classical

namespace Rigidity

/-- Stretched-exponential radial control of the full mixed Green matrix. -/
-- FROZEN-STATEMENT-BEGIN
theorem mixed_green : ∀ (_ : SupercriticalBondGreenQuantitative)
    (_ : ArmstrongDarioOrderZero)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ δ : ℝ, 0 < δ → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
      ∀ y : Vertex d, ∃ M : Configuration d → ℝ,
        Measurable M ∧ (∀ ω, 1 ≤ M ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (M ω / C) s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (Real.rpow (M ω / C) s) ∂latticeBondLaw d p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h : HasUniqueInfiniteOpenComponent ω,
              ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                ∀ g : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ,
                  (∀ z, IsGreenColumn d hd (uniqueInfiniteComponent h) z (g z)) →
                  ∀ x : uniqueInfiniteComponent h,
                    M ω ≤ (latticeL1Dist x.val y : ℝ) →
                    (∑ i : Fin d, ∑ j : Fin d,
                      |mixedEntry (uniqueInfiniteComponent h) g x ⟨y, hy⟩ i j|) ≤
                        C / Real.rpow (latticeL1Dist x.val y : ℝ) ((d : ℝ) - δ)
-- FROZEN-STATEMENT-END
:= by
  exact Rigidity.Support.mixed_green

end Rigidity

import Mathlib
import Rigidity.Proofs.Assembly.Main
import RigidityAudit.Lipschitz.SolutionBasic

/-!
# Bridge: the `Lipschitz` audit vocabulary is the library's

The audit vocabulary of `RigidityAudit/Lipschitz/SolutionBasic.lean` is a token-for-token copy of
the definitions of the library and of its `lattice-probability` dependency, so each audit
definition is definitionally equal to the library's: every identification below is `rfl`.  The
vocabulary has no `structure` or `inductive`, so no field-by-field repacking is needed.
-/

namespace Rigidity
namespace StatementAudit
namespace Lipschitz

open MeasureTheory

theorem latticeBondLaw_eq (d : ℕ) (p : unitInterval) :
    latticeBondLaw d p = LatticeProb.Percolation.latticeBondLaw d p := rfl

theorem criticalProbability_eq (d : ℕ) [NeZero d] :
    criticalProbability d = LatticeProb.Percolation.criticalProbability d := rfl

theorem openGraph_eq {d : ℕ} (ω : Configuration d) :
    openGraph ω = LatticeProb.Percolation.openGraph ω := rfl

theorem hasUniqueInfiniteOpenComponent_eq {d : ℕ} (ω : Configuration d) :
    HasUniqueInfiniteOpenComponent ω = LatticeProb.Percolation.HasUniqueInfiniteOpenComponent ω :=
  rfl

theorem uniqueInfiniteComponent_eq {d : ℕ} {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) :
    uniqueInfiniteComponent h = LatticeProb.Percolation.uniqueInfiniteComponent h := rfl

theorem componentLaplacian_eq {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (x : C) :
    componentLaplacian C u x = LatticeProb.Percolation.componentLaplacian C u x := rfl

theorem componentLipschitz_eq {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) :
    ComponentLipschitz C u = LatticeProb.Percolation.ComponentLipschitz C u := rfl

theorem harmonicGrowthSpace_eq {d : ℕ} {ω : Configuration d} (C : OpenComponent ω) (k : ℕ) :
    harmonicGrowthSpace C k = LatticeProb.Percolation.harmonicGrowthSpace C k := rfl

theorem isGreenColumn_eq (d : ℕ) (hd : 2 ≤ d) {ω : Configuration d} (C : OpenComponent ω)
    (y : C) (g : C → ℝ) :
    IsGreenColumn d hd C y g = LatticeProb.Percolation.IsGreenColumn d hd C y g := rfl

theorem isWellConnected_eq {d : ℕ} (ω : Configuration d) (x : Vertex d) (R : ℕ) :
    IsWellConnected ω x R = Rigidity.External.IsWellConnected ω x R := rfl

theorem supercriticalBondUniqueness_eq :
    SupercriticalBondUniqueness = LatticeProb.External.SupercriticalBondUniqueness := rfl

theorem supercriticalBondCorrectorInput_eq :
    SupercriticalBondCorrectorInput = LatticeProb.External.SupercriticalBondCorrectorInput := rfl

theorem correctorQuantitativeInput_eq :
    CorrectorQuantitativeInput = Rigidity.External.CorrectorQuantitativeInput := rfl

theorem armstrongDarioOrderZero_eq :
    ArmstrongDarioOrderZero = LatticeProb.External.ArmstrongDarioOrderZero := rfl

theorem supercriticalBondGreenColumnExistence_eq :
    SupercriticalBondGreenColumnExistence =
      LatticeProb.External.SupercriticalBondGreenColumnExistence := rfl

theorem supercriticalBondGreenQuantitative_eq :
    SupercriticalBondGreenQuantitative =
      LatticeProb.External.SupercriticalBondGreenQuantitative := rfl

theorem wellConnectedInput_eq :
    WellConnectedInput = Rigidity.External.WellConnectedInput := rfl

end Lipschitz
end StatementAudit
end Rigidity

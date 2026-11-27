import Rigidity.Proofs.Green.GeneralFluxStepTwoInput
import Rigidity.Proofs.Corrector.GeneralResamplePartitionHolds

/-!
# The boundary between the bounds for the bonds open and closed in the variance bound of Gu on `ℤ^d`

Part 2 of the port of the flip chain of the flux to `ℤ^d` (`GeneralFluxStepTwoInput.lean`), the
bound `FluxFlipWeightBoundD` of each squared flip difference by the Step 2 factor, splits as in the
planar files into the bound for the bonds open in the configuration (`DarioGuFluxOpenBound.lean`)
and the bound for the bonds closed in the configuration with their combination
(`DarioGuFluxClosedBound.lean` and the first half of `DarioGuFluxFlipSum.lean`). This file states
the bound for the open bonds, `FluxOpenBoundD d p`, the `ℤ^d` form of the planar
`Rigidity.Green.ae_fluxFlip_sq_le_open`:

`(D_e X)² ≤ 2 (1 + (8d 7^d 243^d S^d)²)² G(x₀)² (E_v(x₀) + Φ_{r²}(x, x₀)²)`

for a bond `e` of `a = (x₀, i')` open in `ω`, with `S = max(s_ω(x₀), s_{ω^{e,0}}(x₀))` the larger
of the sides `partSide` of the partition cubes of `x₀` for `ω` and `ω^{e,0}`.

The planar statement assumes Lemma 3.5 in the form `ResamplePartitionBound C₀ C`, with the side of
the partition cube of `x₀` for `ω` alone, and has the constant `1296 C² s²` from the ninefold
squares. On `ℤ^d` the proof uses Lemma 3.5 in its corrected form,
`Rigidity.Corrector.GeneralDim.resamplePartition_max_bound` (constants `81` and `243`, with the
scale `S`), and the dipole bound `ae_dipoleCoeff_eq` with the boxes `anchorBox`
(`|anchorBox| ≤ 7^d M^d` when the side is at most `M`: `card_anchorBox_le`), whence the constant
`8d 7^d 243^d S^d`. No hypothesis on Lemma 3.5 remains in the statement. The bound is proved in
`GeneralFluxOpenBound.lean` (`fluxOpenBoundD_holds`) and combined with the bound for the closed
bonds in `GeneralFluxFlipWeight.lean` (`fluxFlipWeightBoundD_holds`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External Rigidity.Corrector.GeneralDim
open Rigidity.Poincare.GeneralDim (zdHeat)
open scoped Classical ENNReal

namespace Rigidity.Green.GeneralFlux

/-- **Part 2a, the flip difference for a bond open in `ω`** (planar:
`Rigidity.Green.ae_fluxFlip_sq_le_open`): almost surely, for every oriented edge `a` open in `ω` on
the partition event, the squared flip difference of the heat average of the flux is at most
`2 (1 + (8d 7^d 243^d S^d)²)² G(a.1)² (E_v(a.1) + Φ_{r²}(x, a.1)²)` with
`S = max (partSide ω a.1) (partSide ω^{e,0} a.1)`, `G = planeGrad` and `v` the potential of the
Green projection of the heat field of the edges. -/
def FluxOpenBoundD (d : ℕ) (p : unitInterval) : Prop :=
  ∀ (G : Set (Configuration d)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d),
    (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (k i : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (a : LatticeEdge d), EdgeOpen ω a → PartitionEvent ω →
      bondFlipDiff (fluxObsD hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
        2 * (1 + (8 * d * 7 ^ d * 243 ^ d *
            (((max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1) : ℕ) : ℝ)) ^ d) ^
              2) ^ 2 *
          planeGrad hG hGv k ω a.1 ^ 2 *
          (Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) a.1 +
            zdHeat d (r ^ 2) x a.1 ^ 2)

end Rigidity.Green.GeneralFlux

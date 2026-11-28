import Rigidity.Proofs.Green.GeneralFluxHeatEdge
import Rigidity.Proofs.Corrector.GeneralFlipCluster

/-!
# The variance bound of Gu on `ℤ^d`: the inputs and the boundaries of the flip chain

The variance bound (3.4) of Gu's proof of his Proposition 1.1 (*An efficient algorithm for solving
elliptic problems on percolation clusters*), `FluxVarianceBoundD d p`, is proved in dimension two
from the flip sum of the heat average of the flux (`Rigidity.Green.fluxFlipSum_isOsBond`, files
`DarioGuFlux{Flip,Pairing,OpenBound,ClosedBound,FlipSum,Partition,FlipMoments}`), which rests on
Step 2 of the proof of Lemma 3.3 of Dario (*Optimal corrector estimates on percolation clusters*)
and on Lemma 3.5. On `ℤ^d` the deterministic and almost sure facts of Step 2 are proved in the
repository (`Rigidity.Corrector.GeneralDim`: `ae_exists_correctedPlane_eq_add_const`,
`le_of_finite_piece`, `ae_correctedPlane_sub_eq_smul_greenProj`,
`ae_correctedPlane_sub_eq_smul_greenProj_closed`, `ae_dipoleCoeff_eq`, `tsum_bond_eq_tsum_edge`),
Lemma 3.5 for the partition into good cubes of `ℤ^d` is proved in its corrected form
(`Rigidity.Corrector.GeneralDim.resamplePartition_max_bound`) and enters the proof of part 2, and
the probabilistic part of Step 2 for `d ≥ 3`,
`Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree` (the partition of the good cubes of Step 2
and a majorant with moments of polynomial growth of the Step 2 weight and the path weight), is
proved as well (`Rigidity.Corrector.GeneralDim.darioStepTwoWeightThree_holds`).

The target is `FluxVarianceBoundThree`: `FluxVarianceBoundD d p` for every `d ≥ 3` and
`p_c(d) < p < 1`. This file fixes the boundary statements between the four parts of the proof on `ℤ^d`:

* part 1 (`DarioGuFlux{Flip,Heat,Observable,Pairing}`, with `GeneralFluxHeatEdge`):
  `FluxPairingOpenD`, `FluxPairingClosedD`, `FluxPairingZeroD`, the flip difference of the heat
  average of the flux of the corrected planes in Cases 3 and 1-2 (planar
  `ae_heat_planeFlux_sub_open`, `_closed`, `_eq_zero`);
* part 2 (`DarioGuFlux{OpenBound,ClosedBound}` and the first half of `DarioGuFluxFlipSum`):
  `FluxFlipWeightBoundD`, the bound of each squared flip difference by the Step 2 factor (planar
  `ae_fluxFlip_sq_le_weight`), whose proof uses Lemma 3.5;
* part 3 (the second half of `DarioGuFluxFlipSum` and `DarioGuFluxPartition`):
  `FluxFlipSumPartitionD`, the flip sum through a partition into good cubes (planar
  `fluxFlipSum_le_of_partition`);
* part 4 (`DarioGuFluxFlipMoments`): `FluxVarianceBoundThree` from the three boundaries and
  `DarioStepTwoWeightThree`.

Each boundary is the planar statement on `ℤ^d`, with the heat kernel `zdHeat d` of `ℤ^d`, the
partition into good cubes of `ℤ^d` in place of the partition of meshed squares, and the numerical
constants tied to the square lattice made existential. The four parts are proved
(`fluxPairingOpenD_holds`, `fluxPairingClosedD_holds`, `fluxPairingZeroD_holds`,
`fluxFlipWeightBoundD_holds`, `fluxFlipSumPartitionD_holds`,
`fluxVarianceBoundThree_of_weightBound`),
so `FluxVarianceBoundThree` follows from `DarioStepTwoWeightThree`
(`fluxVarianceBoundThree_of_stepTwoWeight`), which is proved
(`Rigidity.Corrector.GeneralDim.darioStepTwoWeightThree_holds`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External Rigidity.Corrector.GeneralDim
open Rigidity.Poincare.GeneralDim (zdHeat)
open scoped Classical ENNReal

namespace Rigidity.Green.GeneralFlux

/-- **The variance bound of Gu in dimension `d ≥ 3`**: `FluxVarianceBoundD d p` for every `d ≥ 3`
and every supercritical `p < 1`. -/
def FluxVarianceBoundThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → FluxVarianceBoundD d p

/-- **Part 1, Case 3 with the bond open** (planar: `Rigidity.Green.ae_heat_planeFlux_sub_open`):
the difference of the heat averages of the fluxes of corrected planes of `ω^{e,1}` and `ω^{e,0}`. -/
def FluxPairingOpenD (d : ℕ) (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ a : LatticeEdge d,
    ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
      (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
      (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
      (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp)
      (q : Fin d → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
      (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
      IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
      IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
      ∀ (r : ℝ), 0 < r → ∀ (x : Vertex d) (i : Fin d),
        (∑' z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₁ (z, i)) -
            ∑' z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₀ (z, i) =
          (ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) *
            (greenProj (setBond (edgeBond a) true ω)
                (heatEdgeD (setBond (edgeBond a) true ω) r x i) a -
              if a.2 = i then zdHeat d (r ^ 2) x a.1 else 0)

/-- **Part 1, Case 3 with the bond closed** (planar:
`Rigidity.Green.ae_heat_planeFlux_sub_closed`). -/
def FluxPairingClosedD (d : ℕ) (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ a : LatticeEdge d,
    ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
      (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
      (_hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
      (_hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp)
      (q : Fin d → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
      (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
      IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
      IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
      ∀ (pw : (openGraph (setBond (edgeBond a) false ω)).Walk a.1
          (edgeHead a))
        (r : ℝ), 0 < r → ∀ (x : Vertex d) (i : Fin d),
        (∑' z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₁ (z, i)) -
            ∑' z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₀ (z, i) =
          (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)) *
            (walkSum (setBond (edgeBond a) false ω)
                (greenProj (setBond (edgeBond a) false ω)
                  (heatEdgeD (setBond (edgeBond a) false ω) r x i)) pw -
              if a.2 = i then zdHeat d (r ^ 2) x a.1 else 0)

/-- **Part 1, Cases 1 and 2** (planar: `Rigidity.Green.ae_heat_planeFlux_sub_eq_zero`). -/
def FluxPairingZeroD (d : ℕ) (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ a : LatticeEdge d,
    ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
      (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω)),
      ¬ (a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
        edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) →
      ∀ (q : Fin d → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
        (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
        IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
        IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
        ∀ (r : ℝ) (x : Vertex d) (i : Fin d),
          (∑' z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₁ (z, i)) -
            ∑' z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₀ (z, i) = 0

/-- **Part 2, the bound of each flip difference** (planar:
`Rigidity.Green.ae_fluxFlip_sq_le_weight`, from `ae_fluxFlip_sq_le_open` and
`ae_fluxFlip_sq_le_closed`): every squared flip difference of the heat average of the flux is at
most `K₀ F_a (Σ_{B_a} E_v + Σ_{B_a} Φ_{r²}(x, ·)²)`, with the factor `F_a = stepTwoFactor` and the
box `B_a = stepTwoBox` of the Step 2 sum for some box parameter `κ`, the form of the bound
`ae_flipTermTwo_sq_le_weight` of the corrector. The planar statement assumes Lemma 3.5 with
constants `C₀, C` and has the constants `2 · 1297⁴ · 46656` and `κ = C₀ + 5C + 6`; here the
constants are existential and Lemma 3.5 enters only the proof (`fluxFlipWeightBoundD_holds`). -/
def FluxFlipWeightBoundD (d : ℕ) (p : unitInterval) : Prop :=
  ∀ (G : Set (Configuration d)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d),
    (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∃ κ : ℕ, 1 ≤ κ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ (k i : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
        (a : LatticeEdge d), PartitionEvent ω →
        bondFlipDiff (fluxObsD hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
          K₀ * stepTwoFactor hG hGv κ k ω a *
            (∑ u ∈ stepTwoBox κ ω a,
                Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u +
              ∑ y ∈ stepTwoBox κ ω a,
                zdHeat d (r ^ 2) x y ^ 2)

/-- **Part 3, the flip sum through the partition of the good cubes** (planar:
`Rigidity.Green.fluxFlipSum_le_of_partition`, with `ae_fluxFlipSum_le` and
`tsum_weight_openEnergy_heat_le`): from the bound of each flip difference with constants `K₀`, `κ`,
for every partition into good cubes of Step 2 with parameters `ε, CM, M`,
`Σ_e (D_e X)² ≤ Σ_y Φ_{r²}(x, y)² K₀ (W(y) + K_c ((3^d)^{n(y)})^{1 - 1/(1 + ε/2)})` with `n(y)`
the scale of the cell of `y`; the planar constant `3 (M^{1/q'} + 48 cellConst)` is existential. -/
def FluxFlipSumPartitionD (d : ℕ) (p : unitInterval) : Prop :=
  ∀ (G : Set (Configuration d)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)
    (K₀ : ℝ) (κ : ℕ), 0 < K₀ →
    (∀ᵐ ω ∂latticeBondLaw d p, ∀ (k i : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
        (a : LatticeEdge d), PartitionEvent ω →
        bondFlipDiff (fluxObsD hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
          K₀ * stepTwoFactor hG hGv κ k ω a *
            (∑ u ∈ stepTwoBox κ ω a,
                Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u +
              ∑ y ∈ stepTwoBox κ ω a,
                zdHeat d (r ^ 2) x y ^ 2)) →
    ∀ (ε CM M : ℝ), 0 < ε → 0 ≤ CM → 0 ≤ M → ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ (k i : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
        (hpart : ∀ z : Vertex d, ∃! Q : TriadicCube d, z ∈ Q.vertices ∧
          Q.IsMaximalStopping (stepTwoGood hG hGv κ k ε CM M ω)),
        PartitionEvent ω →
        fluxFlipSumD hG hGv k i r x ω ≤ ∑' y, ENNReal.ofReal
            (zdHeat d (r ^ 2) x y ^ 2) *
          (ENNReal.ofReal K₀ * (stepTwoWeight hG hGv κ k ω y + ENNReal.ofReal Kc *
            ENNReal.ofReal ((((3 : ℝ) ^ d) ^ partScale hpart y) ^
              (1 - 1 / (1 + ε / 2)))))

end Rigidity.Green.GeneralFlux

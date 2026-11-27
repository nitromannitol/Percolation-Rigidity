import Rigidity.Proofs.Green.GeneralFluxFlip
import Rigidity.Proofs.Green.GeneralFluxStepTwoInput

/-!
# The flip difference of the heat average of the flux on `ℤ^d`

The extension of `DarioGuFluxPairing.lean` from `ℤ²` to `ℤ^d`: the boundary statements of part 1
of `GeneralFluxStepTwoInput.lean`. With the flip formulas of `GeneralFluxFlip` and the heat field
`heatEdgeD` of `GeneralFluxHeatEdge`, the change of the heat average
`X = Σ_z Φ_{r²}(x, z) planeFluxD(z, i)` of the flux when the bond `e` of `a` is flipped is, in
Case 3 (Gu, *An efficient algorithm for solving elliptic problems on percolation clusters*, proof
of Proposition 1.1, Steps 3 and 4: the terms `A_e + B_e`, with the symmetry (2.15) of the Green
projection),

* `X(ω^{e,1}) - X(ω^{e,0}) = c ((P₁ h₁)(a) - 1{a.2 = i} Φ_{r²}(x, a.1))` with
  `c = ℓ₀(a.1) - ℓ₀(edgeHead a)`, `P₁` the Green projection of `ω^{e,1}` and `h₁` its heat field
  (`fluxPairingOpenD_holds`, planar `ae_heat_planeFlux_sub_open`);
* `X(ω^{e,1}) - X(ω^{e,0}) = c' (Σ_{b ∈ π} (P₀ h₀)(b) - 1{a.2 = i} Φ_{r²}(x, a.1))` for an open path
  `π` of `ω^{e,0}` joining the endpoints, with `c' = ℓ₁(a.1) - ℓ₁(edgeHead a)`
  (`fluxPairingClosedD_holds`, planar `ae_heat_planeFlux_sub_closed`);

and in Cases 1 and 2 it vanishes (`fluxPairingZeroD_holds`, planar `ae_heat_planeFlux_sub_eq_zero`).
The statements are those of the planar file on `ℤ^d`, with `2 ≤ d` and `p_c(d) < p < 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.Corrector.GeneralDim
open Rigidity.Poincare.GeneralDim (zdHeat zdHeat_nonneg)
open scoped Classical ENNReal InnerProductSpace

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ} [NeZero d]

variable {p : unitInterval}

/-- **Case 3, through the configuration with the bond open**: the flip difference of the heat
average of the flux is `c ((P₁ h₁)(a) - 1{a.2 = i} Φ_{r²}(x, a.1))`. -/
theorem fluxPairingOpenD_holds (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : FluxPairingOpenD d p := by
  unfold FluxPairingOpenD
  filter_upwards [ae_planeFluxD_setBond_sub_open hd hpc hp1] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ r hr x i
  set c := ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩
  set P := greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1)
  have hpt : ∀ z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₁ (z, i) -
      zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₀ (z, i) =
      c * (zdHeat d (r ^ 2) x z *
        (if EdgeOpen (setBond (edgeBond a) true ω) (z, i) ∧ (setBond (edgeBond a) true ω) ∈ infiniteComponentEvent z then P (z, i) else 0)) -
      c * (zdHeat d (r ^ 2) x z * (if ((z, i) : LatticeEdge d) = a then 1 else 0)) := by
    intro z
    rw [← mul_sub, hω a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ (z, i)]
    have e1 : (EdgeOpen (setBond (edgeBond a) true ω) (z, i) ∧ ((z, i) : LatticeEdge d).1 ∈ (uniqueInfiniteComponent h₁).supp) ↔
        (EdgeOpen (setBond (edgeBond a) true ω) (z, i) ∧ (setBond (edgeBond a) true ω) ∈ infiniteComponentEvent z) :=
      and_congr_right fun _ => mem_uniqueInfiniteComponent_iff h₁ z
    by_cases hc1 : EdgeOpen (setBond (edgeBond a) true ω) (z, i) ∧ (setBond (edgeBond a) true ω) ∈ infiniteComponentEvent z
    · rw [if_pos (e1.2 hc1), if_pos hc1]
      split_ifs <;> ring
    · rw [if_neg (fun h => hc1 (e1.1 h)), if_neg hc1]
      split_ifs <;> ring
  rw [← (summable_heat_planeFluxD hℓ₁ i r x).tsum_sub (summable_heat_planeFluxD hℓ₀ i r x)]
  rw [tsum_congr hpt]
  have hS1 := (summable_heat_ite_greenProjD (setBond (edgeBond a) true ω) r x i (lp.single 2 a 1) 1
    (fun b => abs_greenProj_single_le (setBond (edgeBond a) true ω) a b)).mul_left c
  have hS2 := (summable_heat_ite_eqD r x i a).mul_left c
  rw [hS1.tsum_sub hS2, tsum_mul_left, tsum_mul_left, ← inner_heatEdgeD, tsum_heat_ite_eqD,
    inner_greenProj_comm, lp.inner_single_left]
  rw [Real.inner_apply, one_mul]
  split_ifs <;> ring

/-- **Case 3, through the configuration with the bond closed**: for an open path `pw` of
`ω^{e,0}` joining the endpoints, the flip difference of the heat average of the flux is
`c' (Σ_{b ∈ pw} (P₀ h₀)(b) - 1{a.2 = i} Φ_{r²}(x, a.1))`. -/
theorem fluxPairingClosedD_holds (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : FluxPairingClosedD d p := by
  unfold FluxPairingClosedD
  filter_upwards [ae_planeFluxD_setBond_sub_closed hd hpc hp1] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw r hr x i
  set c := extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)
  set P := greenProj (setBond (edgeBond a) false ω) (pathField (setBond (edgeBond a) false ω) pw)
  have hpt : ∀ z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₁ (z, i) -
      zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₀ (z, i) =
      c * (zdHeat d (r ^ 2) x z *
        (if EdgeOpen (setBond (edgeBond a) false ω) (z, i) ∧ (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent z then P (z, i) else 0)) -
      c * (zdHeat d (r ^ 2) x z * (if ((z, i) : LatticeEdge d) = a then 1 else 0)) := by
    intro z
    rw [← mul_sub, hω a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw (z, i)]
    have e1 : (EdgeOpen (setBond (edgeBond a) false ω) (z, i) ∧ ((z, i) : LatticeEdge d).1 ∈ (uniqueInfiniteComponent h₀).supp) ↔
        (EdgeOpen (setBond (edgeBond a) false ω) (z, i) ∧ (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent z) :=
      and_congr_right fun _ => mem_uniqueInfiniteComponent_iff h₀ z
    by_cases hc1 : EdgeOpen (setBond (edgeBond a) false ω) (z, i) ∧ (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent z
    · rw [if_pos (e1.2 hc1), if_pos hc1]
      split_ifs <;> ring
    · rw [if_neg (fun h => hc1 (e1.1 h)), if_neg hc1]
      split_ifs <;> ring
  rw [← (summable_heat_planeFluxD hℓ₁ i r x).tsum_sub (summable_heat_planeFluxD hℓ₀ i r x)]
  rw [tsum_congr hpt]
  have hB : ∀ b, |P b| ≤ ‖pathField (setBond (edgeBond a) false ω) pw‖ := fun b =>
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) P b).trans (norm_greenProj_le (setBond (edgeBond a) false ω) _)
  have hS1 := (summable_heat_ite_greenProjD (setBond (edgeBond a) false ω) r x i
    (pathField (setBond (edgeBond a) false ω) pw) _ hB).mul_left c
  have hS2 := (summable_heat_ite_eqD r x i a).mul_left c
  rw [hS1.tsum_sub hS2, tsum_mul_left, tsum_mul_left, ← inner_heatEdgeD, tsum_heat_ite_eqD,
    inner_greenProj_comm, real_inner_comm, inner_pathField]
  split_ifs <;> ring

/-- **Cases 1 and 2**: the flip difference of the heat average of the flux vanishes. -/
theorem fluxPairingZeroD_holds (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : FluxPairingZeroD d p := by
  unfold FluxPairingZeroD
  filter_upwards [ae_planeFluxD_setBond_eq hd hpc hp1] with ω hω
  intro a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀ r x i
  rw [sub_eq_zero]
  exact tsum_congr fun z => by rw [hω a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀ (z, i)]


end Rigidity.Green.GeneralFlux

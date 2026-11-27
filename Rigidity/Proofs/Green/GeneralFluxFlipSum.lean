import Rigidity.Proofs.Green.GeneralFluxStepTwoInput
import Rigidity.Proofs.Corrector.GeneralStepTwoReduce

/-!
# The flip sum of the heat average of the flux on `ℤ^d` through a partition of good cubes

The extension of the second half of `DarioGuFluxFlipSum.lean` and of the first theorem of
`DarioGuFluxFlipMoments.lean` from `ℤ²` to `ℤ^d`: the boundary statement of part 3 of
`GeneralFluxStepTwoInput.lean` (`fluxFlipSumPartitionD_holds`, `FluxFlipSumPartitionD`).

* `fluxFlipSumD_le_of_bound` (planar `ae_fluxFlipSum_le`, deterministic here): if every squared flip
  difference of `X = Σ_z Φ_{r²}(x, z) flux_{e_k}(z, i)` is at most
  `K₀ F_a (Σ_{B_a} E_v + Σ_{B_a} Φ_{r²}(x, ·)²)`, with the factor `F_a` and the box `B_a` of the
  Step 2 sum of the proof of Lemma 3.3 of Dario, then summing over the bonds
  `Σ_e (D_e X)² ≤ K₀ (Σ_u W(u) E_v(u) + Σ_y W(y) Φ_{r²}(x, y)²)` with the weight `W` of the
  Step 2 sum (Gu, *An efficient algorithm for solving elliptic problems on percolation clusters*,
  proof of Proposition 1.1, Steps 3 and 4, in the form of the bound (4) of Dario's Step 2).
* `fluxFlipSumPartitionD_holds` (planar `fluxFlipSum_le_of_partition`): for a partition of `ℤ^d`
  into maximal stopping cubes of the good cubes of Step 2, the weighted energy is summed through
  the cells (`tsum_weight_openEnergy_heatD_le`), so that
  `Σ_e (D_e X)² ≤ Σ_y Φ_{r²}(x, y)² K₀ (W(y) + K_c ((3^d)^{n(y)})^{1 - 1/(1 + ε/2)})` with
  `K_c = 3 cellSumConst d ε C_M M`; the planar statement has `K₀ = 2 · 1297⁴ · 46656`,
  `K_c = 3 (M^{1/q'} + 48 cellConst(ε, C_M, 9M))` and `9^{n(y)}`, and assumes Lemma 3.5 for the
  bound of each flip difference, which is here the hypothesis of the boundary statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External Rigidity.Corrector.GeneralDim
open Rigidity.Poincare.GeneralDim (zdHeat)
open scoped Classical ENNReal

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

section Weight

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The sum of the squared flip differences bounded by a weighted energy** (planar:
`ae_fluxFlipSum_le`). -/
theorem fluxFlipSumD_le_of_bound {K₀ : ℝ} (hK₀ : 0 ≤ K₀) {κ : ℕ} {k i : Fin d} {r : ℝ}
    {x : Vertex d} {ω : Configuration d}
    (hw : ∀ a : LatticeEdge d,
      bondFlipDiff (fluxObsD hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
        K₀ * stepTwoFactor hG hGv κ k ω a *
          (∑ u ∈ stepTwoBox κ ω a,
              Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u +
            ∑ y ∈ stepTwoBox κ ω a, zdHeat d (r ^ 2) x y ^ 2)) :
    fluxFlipSumD hG hGv k i r x ω ≤ ENNReal.ofReal K₀ *
      (∑' u, stepTwoWeight hG hGv κ k ω u * ENNReal.ofReal
          (Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u) +
        ∑' y, stepTwoWeight hG hGv κ k ω y * ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2)) := by
  have hbond : ∀ a : LatticeEdge d,
      ENNReal.ofReal (bondFlipDiff (fluxObsD hG hGv k i r x) (edgeBond a) ω ^ 2) ≤
      ENNReal.ofReal K₀ *
        ((∑' u, (if u ∈ stepTwoBox κ ω a then
            ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) else 0) *
              ENNReal.ofReal (Rigidity.Corrector.GeneralDim.openEnergy ω
                (clusterPot ω (heatEdgeD ω r x i)) u)) +
          ∑' y, (if y ∈ stepTwoBox κ ω a then
            ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) else 0) *
              ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2)) := by
    intro a
    refine (ENNReal.ofReal_le_ofReal (hw a)).trans (le_of_eq ?_)
    have hF0 := stepTwoFactor_nonneg hG hGv κ k ω a
    have hE0 : ∀ u ∈ stepTwoBox κ ω a,
        0 ≤ Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u :=
      fun u _ => Rigidity.Corrector.GeneralDim.openEnergy_nonneg _ _ u
    have hΦ0 : ∀ y ∈ stepTwoBox κ ω a, 0 ≤ zdHeat d (r ^ 2) x y ^ 2 := fun y _ => sq_nonneg _
    have hite : ∀ (g : Vertex d → ℝ≥0∞),
        ∑' u, (if u ∈ stepTwoBox κ ω a then
          ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) else 0) * g u =
        ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) * ∑ u ∈ stepTwoBox κ ω a, g u := by
      intro g
      rw [Finset.mul_sum, ← tsum_ite_mem]
      refine tsum_congr fun u => ?_
      split_ifs <;> simp
    rw [hite, hite, ← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hK₀,
      ← ENNReal.ofReal_sum_of_nonneg hE0, ← ENNReal.ofReal_sum_of_nonneg hΦ0,
      ← ENNReal.ofReal_add (Finset.sum_nonneg hE0) (Finset.sum_nonneg hΦ0),
      ← ENNReal.ofReal_mul (mul_nonneg hK₀ hF0)]
  unfold fluxFlipSumD
  rw [tsum_bond_eq_tsum_edge]
  refine (ENNReal.tsum_le_tsum hbond).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_comm,
    ENNReal.tsum_comm (f := fun a y => (if y ∈ stepTwoBox κ ω a then
      ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) else 0) *
        ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2))]
  unfold stepTwoWeight
  simp only [ENNReal.tsum_mul_right]

end Weight

/-- **Part 3, the flip sum through the partition of the good cubes** (planar:
`fluxFlipSum_le_of_partition`). -/
theorem fluxFlipSumPartitionD_holds [NeZero d] (p : unitInterval) : FluxFlipSumPartitionD d p := by
  intro G hG hGv K₀ κ hK₀ hw ε CM M hε hCM hM
  refine ⟨3 * cellSumConst d ε CM M, mul_nonneg (by norm_num) (cellSumConst_nonneg d hCM hM), ?_⟩
  filter_upwards [hw] with ω hω k i r hr x hpart hP
  have hfs := fluxFlipSumD_le_of_bound hG hGv hK₀.le (fun a => hω k i r hr x a hP)
  have hfin : ∀ u, stepTwoWeight hG hGv κ k ω u ≠ ∞ := fun u =>
    (partCell_mem hpart u).2.1 u
      ((TriadicCube.mem_toIntegerCube_vertices _ u).2 (partCell_spec hpart u).1)
  have hMey : ∀ x' z, 1 ≤ partScale hpart x' → z ∈ cube (partScale hpart x') x' →
      GeneralDim.MeyersCube ε CM ω (partScale hpart x' - 1) z := fun x' z h1 hz =>
    (partCell_mem hpart x').1 (partScale hpart x' - 1) (by unfold partScale at h1 ⊢; omega) z
      ((mem_cube_partScale_iff hpart).1 hz)
  have hWM : ∀ x', ∑ u ∈ cube (partScale hpart x') x',
      (stepTwoWeight hG hGv κ k ω u).toReal ^ Real.conjExponent (1 + ε / 2) ≤
        M * (cube (partScale hpart x') x').card := fun x' => by
    rw [cube_partScale]
    exact (partCell_mem hpart x').2.2
  have hE := tsum_weight_openEnergy_heatD_le (r := r) (x := x) (i := i)
    (isCellScale_partScale hpart) hε hCM hM hMey hfin hWM
  refine hfs.trans ?_
  calc ENNReal.ofReal K₀ *
        (∑' u, stepTwoWeight hG hGv κ k ω u * ENNReal.ofReal
            (Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u) +
          ∑' y, stepTwoWeight hG hGv κ k ω y * ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2))
      ≤ ENNReal.ofReal K₀ *
        (3 * ENNReal.ofReal (cellSumConst d ε CM M) *
          ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) *
            ENNReal.ofReal ((((3 : ℝ) ^ d) ^ partScale hpart y) ^ (1 - 1 / (1 + ε / 2))) +
          ∑' y, stepTwoWeight hG hGv κ k ω y * ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2)) := by
        unfold cellSumConst
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat,
          ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        ring

end Rigidity.Green.GeneralFlux

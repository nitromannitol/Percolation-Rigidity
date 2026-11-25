import Rigidity.Proofs.Green.DarioGuFluxFlipSum
import Rigidity.Proofs.Corrector.DarioStepTwoReduce

/-!
# The sum of the squared flip differences of the flux through the partition of the good cubes

The heat field of the edges is `Φ_{r²}(x, z)` on the open edge `(z, i)` of an infinite component
(`heatEdge_apply`), so `Γ(z) = Σ_j h(z, j)² ≤ Φ_{r²}(x, z)²` (`edgeSq_heatEdge_le`). The summation of
estimate (2) over a partition into cells carrying the Meyers estimate and the weight bound
(`tsum_weight_energy_le`, generic in the source field), with the energy bound
`Σ_z E_v(z) ≤ 2 Σ_z Γ(z)` (`tsum_clusterOpenEnergy_le`), gives
`Σ_u W(u) E_v(u) ≤ 3 K Σ_y Φ_{r²}(x, y)² c(y)` with `c(y) = (9^{n(y)})^{1 - 1/p}`
(`tsum_weight_openEnergy_heat_le`), the plain heat field replacing the field of the coarsened
gradient and its path weight in `tsum_weight_openEnergy_le`. Through the partition of the good cubes
of the Step 2 sum (`fluxFlipSum_le_of_partition`):

`Σ_e (D_e X)² ≤ Σ_y Φ_{r²}(x, y)² K₀ (W(y) + 3 K c(y))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Corrector Rigidity.External Rigidity.Poincare
open scoped Classical ENNReal InnerProductSpace

/-- **The heat field at an edge.** -/
theorem heatEdge_apply (ω : Configuration 2) (r : ℝ) (x : Vertex 2) (i : Fin 2) (b : LatticeEdge) :
    heatEdge ω r x i b =
      if b.2 = i ∧ EdgeOpen ω b ∧ ω ∈ infiniteComponentEvent b.1 then
        latticeHeat (r ^ 2) x b.1 else 0 := by
  obtain ⟨z₀, j⟩ := b
  have h := inner_heatEdge ω r x i (lp.single 2 (z₀, j) (1 : ℝ))
  rw [lp.inner_single_left, Real.inner_apply, one_mul] at h
  rw [h, tsum_eq_single z₀]
  · by_cases hji : j = i
    · subst hji
      by_cases hc : EdgeOpen ω (z₀, j) ∧ ω ∈ infiniteComponentEvent z₀
      · rw [if_pos hc, lp.single_apply_self, mul_one, if_pos ⟨rfl, hc⟩]
      · rw [if_neg hc, mul_zero, if_neg (fun h' => hc h'.2)]
    · have hne : ((z₀, i) : LatticeEdge) ≠ (z₀, j) := fun e => hji (congrArg Prod.snd e).symm
      rw [if_neg (show ¬ (((z₀, j) : LatticeEdge).2 = i ∧ EdgeOpen ω (z₀, j) ∧
        ω ∈ infiniteComponentEvent ((z₀, j) : LatticeEdge).1) from fun h' => hji h'.1)]
      split_ifs
      · rw [lp.single_apply_ne _ _ _ hne, mul_zero]
      · rw [mul_zero]
  · intro z hz
    have hne : ((z, i) : LatticeEdge) ≠ (z₀, j) := fun e => hz (congrArg Prod.fst e)
    split_ifs
    · rw [lp.single_apply_ne _ _ _ hne, mul_zero]
    · rw [mul_zero]

theorem edgeSq_heatEdge_le (ω : Configuration 2) (r : ℝ) (x : Vertex 2) (i : Fin 2) (z : Vertex 2) :
    edgeSq (heatEdge ω r x i) z ≤ latticeHeat (r ^ 2) x z ^ 2 := by
  have hterm : ∀ j : Fin 2, heatEdge ω r x i (z, j) ^ 2 ≤
      if j = i then latticeHeat (r ^ 2) x z ^ 2 else 0 := by
    intro j
    rw [heatEdge_apply]
    by_cases hj : j = i
    · rw [if_pos hj]
      split_ifs
      · exact le_rfl
      · rw [sq, mul_zero]; exact sq_nonneg _
    · rw [if_neg (fun h => hj h.1), if_neg hj, sq, mul_zero]
  unfold edgeSq
  calc ∑ j : Fin 2, heatEdge ω r x i (z, j) ^ 2 ≤
        ∑ j : Fin 2, (if j = i then latticeHeat (r ^ 2) x z ^ 2 else 0) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = latticeHeat (r ^ 2) x z ^ 2 := by
        rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]

/-- **The weighted energy for the heat field** over a partition into cells carrying the Meyers
estimate and the weight bound. -/
theorem tsum_weight_openEnergy_heat_le {ω : Configuration 2} {r : ℝ} {x : Vertex 2} {i : Fin 2}
    {n : Vertex 2 → ℕ} (hn : IsCellScale n) {ε CM M : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hM : 0 ≤ M)
    (hMey : ∀ x' z, 1 ≤ n x' → z ∈ cube (n x') x' → GeneralDim.MeyersCube ε CM ω (n x' - 1) z)
    {We : Vertex 2 → ℝ≥0∞} (hfin : ∀ u, We u ≠ ∞)
    (hWM : ∀ x', ∑ u ∈ cube (n x') x', (We u).toReal ^ Real.conjExponent (1 + ε / 2) ≤
      M * (cube (n x') x').card) :
    ∑' u, We u * ENNReal.ofReal (openEnergy ω (clusterPot ω (heatEdge ω r x i)) u) ≤
      3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M)) *
        ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
          ENNReal.ofReal (((9 : ℝ) ^ n y) ^ (1 - 1 / (1 + ε / 2))) := by
  have hα0 : 0 ≤ 1 - 1 / (1 + ε / 2) := by
    have : 1 / (1 + ε / 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hc1 : ∀ z, 1 ≤ ((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) := fun z =>
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) hα0
  have hv : ∀ z, ω ∈ infiniteComponentEvent z → openLaplacian ω
      (clusterPot ω (heatEdge ω r x i)) z = edgeDiv ω (heatEdge ω r x i) z :=
    fun z hz => openLaplacian_clusterPot _ hz
  have hcell := tsum_weight_energy_le hn hv hε hCM hMey (W := fun u => (We u).toReal)
    (fun u => ENNReal.toReal_nonneg) hM hWM
  have henergy := tsum_clusterOpenEnergy_le (ω := ω) (heatEdge ω r x i)
  have hpath : ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
      edgeSq (heatEdge ω r x i) z) ≤
      ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
        ENNReal.ofReal (((9 : ℝ) ^ n y) ^ (1 - 1 / (1 + ε / 2))) := by
    refine ENNReal.tsum_le_tsum fun z => ?_
    rw [mul_comm, ← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (edgeSq_heatEdge_le ω r x i z)
      (zero_le_one.trans (hc1 z))
  have hΓ : ∑' z, ENNReal.ofReal (edgeSq (heatEdge ω r x i) z) ≤
      ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
        edgeSq (heatEdge ω r x i) z) :=
    ENNReal.tsum_le_tsum fun z => ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_left (edgeSq_nonneg _ z) (hc1 z))
  have e1 : ∑' u, We u * ENNReal.ofReal (openEnergy ω (clusterPot ω (heatEdge ω r x i)) u) =
      ∑' u, ENNReal.ofReal ((We u).toReal *
        clusterOpenEnergy ω (clusterPot ω (heatEdge ω r x i)) u) := by
    refine tsum_congr fun u => ?_
    rw [openEnergy_clusterPot_eq, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hfin u)]
  rw [e1]
  refine hcell.trans ?_
  calc _ ≤ ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M)) *
        (2 * ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
            edgeSq (heatEdge ω r x i) z) +
          ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
            edgeSq (heatEdge ω r x i) z)) := by
        gcongr
        exact henergy.trans (by gcongr)
    _ = 3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          48 * cellConst ε CM (9 * M)) *
        ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
          edgeSq (heatEdge ω r x i) z) := by ring
    _ ≤ _ := by gcongr

end Rigidity.Green

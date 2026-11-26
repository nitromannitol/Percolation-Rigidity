import Rigidity.Proofs.Green.DarioGuFluxPartition
import Rigidity.Proofs.Poincare.DarioStepTwoHolds

/-!
# The sum of the squared flip differences of the heat average of the flux is `O_s(C/r²)`

Through the partition of the good cubes of the Step 2 sum of Dario's Lemma 3.3
(`exists_stepTwoGood_partition`), the sum of the squared flip differences of
`X = Σ_z Φ_{r²}(x, z) flux_{e_k}(z, i)` is at most `Σ_y Φ_{r²}(x, y)² W(y)`
(`fluxFlipSum_le_of_partition`) with `W(y) = K₀ (W₂(y) + 3 K c(y))`, the Step 2 weight `W₂` of the
slope `e_k` and the cell factor `c(y) = (9^{n(y)})^{1 - 1/p} ≤ size(□(y))²`. The weight is dominated
by the majorant of the Step 2 weight built from the Lipschitz bounds of the corrector
(`stepOne_lipschitz_data`), and both have moments of polynomial growth uniformly in `y`
(`exists_fluxFlip_weight_data`), so `Σ_e (D_e X)² = O_s(C/r²)`
(`fluxFlipSum_isOsBond`, by `isOsBond_heatSqSum_of_moments`). This is the variance condition (3.4)
of Gu's proof of Proposition 1.1 in flip form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Corrector Rigidity.External Rigidity.Poincare
open scoped Classical ENNReal

section Good

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The flip sum of the flux through the partition of the good cubes.** -/
theorem fluxFlipSum_le_of_partition {C₀ C : ℕ} (hC₀ : 2 ≤ C₀) (hres : ResamplePartitionBound C₀ C)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {ε CM M : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hM : 0 ≤ M) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (k i : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (hpart : ∀ z : Vertex 2, ∃! Q : TriadicCube 2, z ∈ Q.vertices ∧
        Q.IsMaximalStopping (stepTwoGood hG hGv (C₀ + 5 * C + 6) k ε CM M ω)),
      fluxFlipSum hG hGv k i r x ω ≤ ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
        (ENNReal.ofReal (2 * 1297 ^ 4 * 46656) *
          (stepTwoWeight hG hGv (C₀ + 5 * C + 6) k ω y + 3 * ENNReal.ofReal
            (M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M)) *
            ENNReal.ofReal (((9 : ℝ) ^ partScale hpart y) ^ (1 - 1 / (1 + ε / 2))))) := by
  filter_upwards [ae_fluxFlipSum_le hG hGv hC₀ hres hpc hp1 hGae, ae_planarPartitionEvent hpc]
    with ω hfs hP k i r hr x hpart
  have hfin : ∀ u, stepTwoWeight hG hGv (C₀ + 5 * C + 6) k ω u ≠ ∞ := fun u =>
    (partCell_mem hpart u).2.1 u
      ((TriadicCube.mem_toIntegerCube_vertices _ u).2 (partCell_spec hpart u).1)
  have hMey : ∀ x' z, 1 ≤ partScale hpart x' → z ∈ cube (partScale hpart x') x' →
      GeneralDim.MeyersCube ε CM ω (partScale hpart x' - 1) z := fun x' z h1 hz =>
    (partCell_mem hpart x').1 (partScale hpart x' - 1) (by unfold partScale at h1 ⊢; omega) z
      ((mem_cube_partScale_iff hpart).1 hz)
  have hWM : ∀ x', ∑ u ∈ cube (partScale hpart x') x',
      (stepTwoWeight hG hGv (C₀ + 5 * C + 6) k ω u).toReal ^ Real.conjExponent (1 + ε / 2) ≤
        M * (cube (partScale hpart x') x').card := fun x' => by
    rw [cube_partScale]
    exact (partCell_mem hpart x').2.2
  have hE := tsum_weight_openEnergy_heat_le (r := r) (x := x) (i := i)
    (isCellScale_partScale hpart) hε hCM hM hMey hfin hWM
  refine (hfs k i r hr x hP).trans ?_
  calc ENNReal.ofReal (2 * 1297 ^ 4 * 46656) *
        (∑' u, stepTwoWeight hG hGv (C₀ + 5 * C + 6) k ω u *
            ENNReal.ofReal (Rigidity.Corrector.openEnergy ω (clusterPot ω (heatEdge ω r x i)) u) +
          ∑' y, stepTwoWeight hG hGv (C₀ + 5 * C + 6) k ω y *
            ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2))
      ≤ ENNReal.ofReal (2 * 1297 ^ 4 * 46656) *
        (3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
            48 * cellConst ε CM (9 * M)) *
          ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
            ENNReal.ofReal (((9 : ℝ) ^ partScale hpart y) ^ (1 - 1 / (1 + ε / 2))) +
          ∑' y, stepTwoWeight hG hGv (C₀ + 5 * C + 6) k ω y *
            ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by gcongr
    _ = _ := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        ring

/-- **The weight of the flip sum of the flux, with moments of polynomial growth.** -/
theorem exists_fluxFlip_weight_data {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (k : Fin 2) :
    ∃ (W : Vertex 2 → Configuration 2 → ℝ≥0∞) (A κ : ℝ), 0 < A ∧ 0 < κ ∧
      (∀ y, Measurable (W y)) ∧ (∀ y, GrowthMoments p (W y) A κ) ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i : Fin 2) (r : ℝ), 0 < r → ∀ x : Vertex 2,
        fluxFlipSum hG hGv k i r x ω ≤
          ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * W y ω := by
  have hκ : 1 ≤ 4747 + 5 * 14244 + 6 := by norm_num
  obtain ⟨ε, CM, M, hε, hCM, hM, s0, hs0, hpart⟩ :=
    exists_stepTwoGood_partition hG hGv hpc hp1 hGae hκ
  obtain ⟨hae, θ, hθ, hexpτ⟩ := hpart k
  obtain ⟨Λ, BΛ, κΛ, hBΛ, hκΛ, hΛm, hΛ0, hlip, hΛmom⟩ := stepOne_lipschitz_data hG hGv
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds hpc hp1 hGae
  -- the sizes of the good cubes
  have hτm : ∀ z, Measurable fun ω =>
      TriadicCube.stoppingSize (stepTwoGood hG hGv (4747 + 5 * 14244 + 6) k ε CM M ω) z :=
    TriadicCube.measurable_stoppingSize _ (measurableSet_mem_stepTwoGood hG hGv _ k ε CM M)
  have hτ2 := fun z => growthMoments_sq_of_exp_moment (hτm z) (fun ω => stoppingSize_nonneg' _ z)
    hθ hs0 (hexpτ z).1 (hexpτ z).2
  set Bτ : ℝ := (2 * θ * (1 / s0) ^ (1 / s0)) * (2 * θ * (1 / s0) ^ (1 / s0)) *
    2 ^ (1 / s0 + 1 / s0) with hBτ
  set kτ : ℝ := 1 / s0 + 1 / s0 with hkτ
  have hBτ0 : 0 ≤ Bτ := by rw [hBτ]; positivity
  have hkτ0 : 0 < kτ := by rw [hkτ]; positivity
  -- the Step 2 weight
  have hΛ4 : ∀ z, GrowthMoments p (fun ω => ENNReal.ofReal (1 + 4 * Λ k z ω)) (4 * BΛ) κΛ := by
    intro z
    have h4 := (show GrowthMoments p (fun ω => ENNReal.ofReal (1 + Λ k z ω)) BΛ κΛ from
      fun q hq => hΛmom k z q hq).const_mul (c := 4) (by norm_num) hBΛ.le
    refine h4.mono fun ω => ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith [hΛ0 k z ω])
  have hK : (0 : ℝ) < 6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ) := by positivity
  obtain ⟨AV, kV, hAV, hkV, hV⟩ := growthMoments_weightMajorant hpc
    (fun z => (hΛm k z).const_mul 4) (by positivity : (0 : ℝ) < 4 * BΛ) hκΛ hΛ4 hK hK
  have hVm : ∀ y, Measurable (weightMajorant (fun z ω => 4 * Λ k z ω)
      (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) y) :=
    fun y => measurable_weightMajorant (fun z => (hΛm k z).const_mul 4) _ _ y
  -- the constants
  set Kc : ℝ := M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; unfold cellConst; positivity
  set K0 : ℝ := 2 * 1297 ^ 4 * 46656 with hK0
  set Bm : ℝ := max AV (3 * Kc * Bτ) with hBm
  set km : ℝ := max kV kτ with hkm
  have hBm0 : 0 < Bm := lt_max_of_lt_left hAV
  have hkm0 : 0 < km := lt_max_of_lt_left hkV
  have hW1 : ∀ y, GrowthMoments p (weightMajorant (fun z ω => 4 * Λ k z ω)
      (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) y) Bm km :=
    fun y => (hV y).of_le hAV.le (le_max_left _ _) (le_max_left _ _)
  have hW2 : ∀ y, GrowthMoments p (fun ω => ENNReal.ofReal (3 * Kc) * ENNReal.ofReal
      (TriadicCube.stoppingSize (stepTwoGood hG hGv (4747 + 5 * 14244 + 6) k ε CM M ω) y ^ 2))
      Bm km :=
    fun y => ((hτ2 y).const_mul (c := 3 * Kc) (by positivity) hBτ0).of_le
      (by positivity) (le_max_right _ _) (le_max_right _ _)
  refine ⟨fun y ω => ENNReal.ofReal K0 * (weightMajorant (fun z ω => 4 * Λ k z ω)
      (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) y ω +
      ENNReal.ofReal (3 * Kc) * ENNReal.ofReal
        (TriadicCube.stoppingSize (stepTwoGood hG hGv (4747 + 5 * 14244 + 6) k ε CM M ω) y ^ 2)),
    K0 * (2 * Bm), km, by positivity, hkm0, fun y => ?_, fun y => ?_, ?_⟩
  · exact measurable_const.mul ((hVm y).add (measurable_const.mul
      (((hτm y).pow_const 2).ennreal_ofReal)))
  · exact ((GrowthMoments.add (hVm y).aemeasurable (hW1 y) (hW2 y) hBm0.le).const_mul
      (c := K0) (by positivity) (by positivity))
  -- the almost sure bound
  filter_upwards [fluxFlipSum_le_of_partition hG hGv (C₀ := 4747) (C := 14244) (by norm_num)
    resamplePartitionBound_holds hpc hp1 hGae hε hCM hM, hae, ae_planarPartitionEvent hpc,
    hlip k] with ω hfs hp hPω hl
  intro i r hr x
  refine (hfs k i r hr x hp).trans (ENNReal.tsum_le_tsum fun y => ?_)
  have h1 : stepTwoWeight hG hGv (4747 + 5 * 14244 + 6) k ω y ≤
      weightMajorant (fun z ω => 4 * Λ k z ω) (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ))
        (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) y ω :=
    stepTwoWeight_le_weightMajorant hG hGv hPω (fun z => by positivity [hΛ0 k z ω])
      (fun z => planeGrad_le_of_lipschitz hG hGv (fun z => hΛ0 k z ω) hl z) y
  have hc : ENNReal.ofReal (((9 : ℝ) ^ partScale hp y) ^ (1 - 1 / (1 + ε / 2))) ≤
      ENNReal.ofReal
        (TriadicCube.stoppingSize (stepTwoGood hG hGv (4747 + 5 * 14244 + 6) k ε CM M ω) y ^
          2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [TriadicCube.stoppingSize_eq_of_mem (partCell_spec hp y).1 (partCell_spec hp y).2]
    exact rpow_nine_pow_le_sq (by have : 0 ≤ 1 / (1 + ε / 2) := by positivity
                                  linarith)
  have h2 : 3 * ENNReal.ofReal Kc *
      ENNReal.ofReal (((9 : ℝ) ^ partScale hp y) ^ (1 - 1 / (1 + ε / 2))) ≤
      ENNReal.ofReal (3 * Kc) * ENNReal.ofReal
        (TriadicCube.stoppingSize (stepTwoGood hG hGv (4747 + 5 * 14244 + 6) k ε CM M ω) y ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
  gcongr

/-- **The flip sum of the heat average of the flux is `O_s(C/r²)`.** -/
theorem fluxFlipSum_isOsBond {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (k i : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
      (∀ᵐ ω ∂latticeBondLaw 2 p, fluxFlipSum hG hGv k i r x ω < ∞) ∧
      IsOsBond 2 p (fun ω => (fluxFlipSum hG hGv k i r x ω).toReal) s (C / r ^ 2) := by
  choose W A κ hA hκ hWm hWmom hWae using fun k => exists_fluxFlip_weight_data hG hGv hpc hp1 hGae k
  obtain ⟨s, C, hs, hC, hOs⟩ := isOsBond_heatSqSum_of_moments (p := p) (A := ∑ k, A k)
    (k := ∑ k, κ k) (Finset.sum_pos (fun k _ => hA k) Finset.univ_nonempty)
    (Finset.sum_pos (fun k _ => hκ k) Finset.univ_nonempty)
  refine ⟨s, C, hs, hC, fun k i r hr x => ?_⟩
  have hAk : A k ≤ ∑ k, A k :=
    Finset.single_le_sum (fun k _ => (hA k).le) (Finset.mem_univ k)
  have hκk : κ k ≤ ∑ k, κ k :=
    Finset.single_le_sum (fun k _ => (hκ k).le) (Finset.mem_univ k)
  have hr0 : 0 < r := by linarith
  have hYm : Measurable (fluxFlipSum hG hGv k i r x) := by
    unfold fluxFlipSum
    exact Measurable.tsum fun e => ENNReal.measurable_ofReal.comp
      ((measurable_bondFlipDiff (measurable_fluxObs hG hGv k i r x) e).pow_const 2)
  exact hOs r hr x (W k) (hWm k) (fun y => (hWmom k y).of_le (hA k).le hAk hκk)
    (fluxFlipSum hG hGv k i r x) hYm
    (by filter_upwards [hWae k] with ω h using h i r hr0 x)

end Good

end Rigidity.Green

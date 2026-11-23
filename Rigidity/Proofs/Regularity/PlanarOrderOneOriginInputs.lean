import Rigidity.Proofs.Regularity.PlanarMesoscopicDegreeTwo
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationTwo
import Rigidity.Proofs.Regularity.PlanarCorrectorReduction
import Rigidity.Proofs.Corrector.PlanarCorrectorQuantitative
import Rigidity.Proofs.Cluster.PlanarMinimalScales

/-!
# Theorem 2 (iii) at `k = 1` in the plane from the estimates on squares

The inputs of `armstrongDarioOrderOneOriginTwo_of_inputs` are discharged as follows.

* `PlanarCoarseHarmonicApproximationTwo` is `PlanarHarmonicApproximationTwo`
  (`planarCoarseHarmonicApproximationTwo_iff`): the coarsenings `coarseAtAnchor C u` and
  `planarCoarse C u` are the same function.
* `PlanarPartCubeMoments p` holds for `p > p_c(2)` (`planarPartCubeMoments_holds`): it is part of
  the minimal scales `Rigidity.Proofs.Cluster.PlanarMinimalScales p` of Proposition 2.4
  (`Rigidity.Proofs.Cluster.planarMinimalScales_holds`).
* `PlanarPartitionSizeScale p`, the hypothesis on the partition cubes of
  `planarHarmonicApproximationTwo_of_squareEstimates`, follows from the same minimal scales with
  `t = 1` and `α = 1/2`, above `max(M, 81)` (`planarPartitionSizeScale_of_partCubeMoments`,
  `planarPartitionSizeScale_holds`).
* The planar corrector inputs are `supercriticalBondCorrectorInputTwo_of_orderOne` (Theorem 2 (i),
  (ii) at `k = 1` and the order-zero regularity) and `correctorQuantitativeInputTwo_of_dario`
  (Theorem 1 of Dario, `DarioOptimalCorrectorTwo`).

`armstrongDarioOrderOneOriginTwo_of_squareEstimates`: Theorem 2 (iii) at `k = 1` in the plane from
the estimates on squares of the proof of Lemma 7.1 (`PlanarSquareEstimatesTwo`), Dario's Theorem 1
in dimension two, the existence of the corrected planes and `dim 𝒜_1 ≤ 3`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.S2

/-- The two coarsenings of Lemma 7.1 in dimension two are the same. -/
theorem planarCoarseApproximationAt_iff {ω : Configuration 2} (C : OpenComponent ω)
    (A α K X : ℝ) :
    PlanarCoarseApproximationAt C A α K X ↔ PlanarHarmonicApproximationAt C A α K X :=
  Iff.rfl

/-- **Lemma 7.1 in dimension two**: the two statements are the same. -/
theorem planarCoarseHarmonicApproximationTwo_iff :
    PlanarCoarseHarmonicApproximationTwo ↔ PlanarHarmonicApproximationTwo :=
  Iff.rfl

/-- The moments and the maxima of the sizes of the planar partition cubes are part of the
minimal scales of Proposition 2.4. -/
theorem planarPartCubeMoments_of_minimalScales {p : unitInterval}
    (H : Rigidity.Proofs.Cluster.PlanarMinimalScales p) : PlanarPartCubeMoments p := by
  obtain ⟨A₀, s, -, H⟩ := H
  intro t ht α hα
  obtain ⟨K, r, θ, hK, hr, hθ, M, hMm, hM0, hMos, hae⟩ := H t ht α hα
  exact ⟨K, r, θ, hK, hr, hθ, M, hMm, hM0, hMos,
    hae.mono fun ω h m hm => ⟨(h m hm).2.2.1, (h m hm).2.2.2.1⟩⟩

/-- **The minimal scales of the sizes of the planar partition cubes** for `p > p_c(2)`. -/
theorem planarPartCubeMoments_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarPartCubeMoments p :=
  planarPartCubeMoments_of_minimalScales (Rigidity.Proofs.Cluster.planarMinimalScales_holds hpc)

/-- The square `□_m` lies in the triadic cube `cube m 0`. -/
theorem mem_cube_zero_of_mem_triadicCubeFinset {m : ℕ} {x : Vertex 2}
    (hx : x ∈ triadicCubeFinset 2 m 0) : x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2) := by
  rw [Rigidity.Proofs.Cluster.cube, Rigidity.Proofs.Cluster.mem_box]
  intro i
  have h3 := Rigidity.Proofs.Cluster.two_mul_halfSide_add_one m
  have h0 := Rigidity.Proofs.Cluster.halfSide_nonneg m
  have hc : Rigidity.Proofs.Cluster.center m (0 : Vertex 2) i = 0 := by
    simp only [Rigidity.Proofs.Cluster.center, Rigidity.Proofs.Cluster.idx, Pi.zero_apply,
      zero_add]
    rw [Int.ediv_eq_zero_of_lt h0 (by omega), mul_zero]
  rw [hc, sub_zero]
  have h2 := (mem_square_iff_int.1 hx) i
  generalize |x i| = a at h2 ⊢
  generalize (3 : ℤ) ^ m = b at h2 h3
  omega

/-- A scale `k` with `3^k ≤ (3^m)^{1/2}` and `81 ≤ 3^m` satisfies `k + 2 ≤ m`. -/
theorem add_two_le_of_three_pow_le {k m : ℕ} (hk : (3 : ℝ) ^ k ≤ ((3 : ℝ) ^ m) ^ ((1 : ℝ) / 2))
    (hm : (81 : ℝ) ≤ 3 ^ m) : k + 2 ≤ m := by
  have hm4 : 4 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : (3 : ℝ) ^ m ≤ 27 :=
      calc (3 : ℝ) ^ m ≤ 3 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 27 := by norm_num
    linarith
  have h2 : ((3 : ℝ) ^ m) ^ ((1 : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have h3 : (3 : ℝ) ^ k = (3 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
  rw [h2, h3] at hk
  have h4 : (k : ℝ) ≤ (m : ℝ) / 2 := (Real.rpow_le_rpow_left_iff (by norm_num)).1 hk
  have h5 : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have h6 : ((k + 2 : ℕ) : ℝ) ≤ m := by push_cast; linarith
  exact_mod_cast h6

/-- **The scales of the planar partition cubes** (`PlanarPartitionSizeScale p`) from the minimal
scales of their sizes, with `t = 1` and `α = 1/2`, above `max(M, 81)`. -/
theorem planarPartitionSizeScale_of_partCubeMoments {p : unitInterval}
    (H : PlanarPartCubeMoments p) : PlanarPartitionSizeScale p := by
  obtain ⟨K, r, θ, -, hr, hθ, M, hMm, hM0, hMos, hae⟩ := H 1 one_pos (1 / 2) (by norm_num)
  have hc := isOsBond_const (d := 2) (p := p) (by norm_num : (0 : ℝ) < 81) hr
  have hos := IsOsBond.max hr hθ (by positivity) hMm measurable_const hMos hc
  refine ⟨r, _, hr, by positivity, fun ω => max (M ω) 81, hMm.max measurable_const,
    fun ω => (hM0 ω).trans (le_max_left _ _), hos, ?_⟩
  filter_upwards [hae] with ω h m hm x hx
  have hM : M ω ≤ 3 ^ m := (le_max_left _ _).trans hm
  have h81 : (81 : ℝ) ≤ 3 ^ m := (le_max_right _ _).trans hm
  exact add_two_le_of_three_pow_le ((h m hM).2 x (mem_cube_zero_of_mem_triadicCubeFinset hx)) h81

/-- **The scales of the planar partition cubes** (`PlanarPartitionSizeScale p`) for `p > p_c(2)`,
from the minimal scales of Proposition 2.4 (`planarMinimalScales_holds`) with `t = 1` and
`α = 1/2`. -/
theorem planarPartitionSizeScale_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) : PlanarPartitionSizeScale p :=
  planarPartitionSizeScale_of_partCubeMoments (planarPartCubeMoments_holds hpc)

/-- **Lemma 7.1 in dimension two** from the estimates on squares. -/
theorem planarHarmonicApproximationTwo_of_squareEstimates_holds
    (hS : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarSquareEstimatesTwo p) :
    PlanarHarmonicApproximationTwo :=
  planarHarmonicApproximationTwo_of_squareEstimates hS fun _ hpc _ =>
    planarPartitionSizeScale_holds hpc

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in the plane**, from the estimates on
squares of the proof of Lemma 7.1. -/
theorem armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates
    (hS : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarSquareEstimatesTwo p) :
    ArmstrongDarioMesoscopicDegreeTwoPlanar :=
  armstrongDarioMesoscopicDegreeTwoPlanar_of_inputs
    (planarCoarseHarmonicApproximationTwo_iff.2
      (planarHarmonicApproximationTwo_of_squareEstimates_holds hS))
    fun _ hpc _ => planarPartCubeMoments_holds hpc

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in the plane**, from the
estimates on squares of the proof of Lemma 7.1, Theorem 1 of Dario in dimension two, the existence
of the corrected planes and the bound `dim 𝒜_1 ≤ 3`. -/
theorem armstrongDarioOrderOneOriginTwo_of_squareEstimates
    (hS : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarSquareEstimatesTwo p)
    (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo)
    (hex : PlanarCorrectedPlaneExistenceTwo) (hdim : PlanarOrderOneDimensionTwo) :
    ArmstrongDarioOrderOneOriginTwo := by
  have hHA := planarHarmonicApproximationTwo_of_squareEstimates_holds hS
  have hR2 := supercriticalBondCorrectorInputTwo_of_orderOne
    (armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation hHA) hex hdim
  exact armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar
    (armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates hS)
    (Rigidity.Corrector.correctorQuantitativeInputTwo_of_dario hD hR2) hR2

end Rigidity.Proofs.Regularity

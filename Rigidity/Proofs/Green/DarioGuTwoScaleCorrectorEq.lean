import Rigidity.Proofs.Green.DarioGuTwoScaleStepOne
import Rigidity.Proofs.Green.DarioGuFluxTranslateHolds
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseComparison
import Rigidity.Proofs.S2.PlanarVarianceMoments
import Rigidity.Proofs.S2.WeightedResamplingTonelli
import Rigidity.Proofs.S3.Divergence
import Rigidity.Proofs.Section5.Peierls

/-!
# The corrector equation in divergence form

For a corrector `χ` of `IsDGCorrector` (the corrected planes `x_k + χ_k` are harmonic on the
cluster), the flux `g_{k,i} = a_i (δ_{ik} + D_i χ_k)` (`openFlux`) is divergence free at every
point of the cluster: `Σ_i (g_{k,i}(x - e_i) - g_{k,i}(x)) = 0` (`sum_openFlux_div_eq_zero`). With
`openLaplacian_twoScale` this gives the spatial part of Step 1 of the proof of Proposition 4.3 of
Dario–Gu for the corrector of the cluster (`openLaplacian_twoScale_of_corrector`).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

theorem cast_add_unit_apply (x : Vertex 2) (i k : Fin 2) :
    (((x + unit i) k : ℤ) : ℝ) = (x k : ℝ) + (if i = k then 1 else 0) := by
  fin_cases i <;> fin_cases k <;> simp [unit]

theorem cast_sub_unit_apply (x : Vertex 2) (i k : Fin 2) :
    (((x - unit i) k : ℤ) : ℝ) = (x k : ℝ) - (if i = k then 1 else 0) := by
  fin_cases i <;> fin_cases k <;> simp [unit]

/-- **The corrector equation in divergence form**: for `x` in the cluster,
`Σ_i (g_{k,i}(x - e_i) - g_{k,i}(x)) = -Δ(x_k + χ_k)(x) = 0`. -/
theorem sum_openFlux_div_eq_zero {ω : Configuration 2} {K : OpenComponent ω} {y : Vertex 2}
    {χ : Fin 2 → Vertex 2 → ℝ} (hχ : IsDGCorrector K y χ) {x : Vertex 2} (hx : x ∈ K.supp)
    (k : Fin 2) :
    ∑ i : Fin 2, (openFlux ω χ k i (x - unit i) - openFlux ω χ k i x) = 0 := by
  set φ : K → ℝ := fun a => (a.val k : ℝ) + χ k a.val with hφ
  have hharm : componentLaplacian K φ ⟨x, hx⟩ = 0 := (hχ k).1.1.1 ⟨x, hx⟩
  rw [← Rigidity.Proofs.Regularity.openLaplacian_extend_eq K φ hx] at hharm
  have hcongr : openLaplacian ω (Rigidity.Section3.extend K φ) x =
      openLaplacian ω (fun z => (z k : ℝ) + χ k z) x := by
    unfold openLaplacian
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [SimpleGraph.mem_neighborFinset] at hz
    have hzK : z ∈ K.supp := mem_supp_of_openAdj hx hz
    simp only [Rigidity.Section3.extend, dif_pos hzK, dif_pos hx, hφ]
  rw [hcongr, openLaplacian_eq_sum] at hharm
  rw [← neg_eq_zero, ← hharm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [openFlux, sub_add_cancel, cast_add_unit_apply, cast_sub_unit_apply]
  ring

/-- **Step 1 of Proposition 4.3 of Dario–Gu (spatial part) for the corrector of the cluster.** -/
theorem openLaplacian_twoScale_of_corrector {ω : Configuration 2} {K : OpenComponent ω}
    {y : Vertex 2} {χ : Fin 2 → Vertex 2 → ℝ} (hχ : IsDGCorrector K y χ) (σ : ℝ)
    (P : Vertex 2 → ℝ) {x : Vertex 2} (hx : x ∈ K.supp) :
    openLaplacian ω (fun z => P z + ∑ k : Fin 2, fwdDiff k P z * χ k z) x =
      ∑ i : Fin 2, (stepOneF ω χ P i (x - unit i) - stepOneF ω χ P i x) +
        ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x * fwdDiff i (fwdDiff k P) x +
        σ / 2 * ∑ k : Fin 2, fwdDiff k (fwdDiff k P) x :=
  openLaplacian_twoScale ω σ χ P x (sum_openFlux_div_eq_zero hχ hx)

end Rigidity.Green

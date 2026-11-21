import Rigidity.Proofs.Partition.PartitionSize
import Rigidity.Proofs.Partition.LambdaClosure

/-!
# The expectation of `Λ_t`

Armstrong and Dario, Section 2, define `Λ_t(U) = |U|⁻¹ ∑_{x ∈ cl(U)} size(𝒫(x))^t`, the sum running
over the union `cl(U)` of the partition cubes meeting `U`, and note the bound `Λ_t(U) ≤ 𝒪_{s/t}(C)`.
We prove its first moment consequence: `E[∑_{x ∈ cl(U)} size(𝒫(x))^t] ≤ C |U|` with `C` depending
only on `t`, `d` and `p`. Since `cl(U)` depends on the configuration, the expectation is the lower
Lebesgue integral.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **Expectation of `Λ_t`.** For supercritical bond percolation on `ℤᵈ`, `d ≥ 2`, there is
`θ > 0` such that for every `t ∈ ℕ` and every finite set `U` of vertices,
`E[∑_{x ∈ cl(U)} 3^{t n(x)}] ≤ 2 (t + d)! θ^{t + d} |U|`, `n(x)` the scale of the partition cube
of `x`. -/
theorem exists_lintegral_sum_partitionClosure_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (t : ℕ) (U : Finset (Vertex d)),
      (∫⁻ ω, ENNReal.ofReal (∑ x ∈ partitionClosure ω U,
        (3 : ℝ) ^ (t * (partitionCube ω x).scale)) ∂(latticeBondLaw d p)) ≤
        ENNReal.ofReal (2 * ((t + d).factorial : ℝ) * θ ^ (t + d) * U.card) := by
  obtain ⟨θ, hθ, h⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  refine ⟨θ, hθ, fun t U => ?_⟩
  obtain ⟨hint, hle⟩ := h (t + d) U
  calc (∫⁻ ω, ENNReal.ofReal (∑ x ∈ partitionClosure ω U,
        (3 : ℝ) ^ (t * (partitionCube ω x).scale)) ∂(latticeBondLaw d p))
      ≤ ∫⁻ ω, ENNReal.ofReal (∑ x ∈ U,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (t + d))
          ∂(latticeBondLaw d p) := by
        apply lintegral_mono_ae
        filter_upwards [ae_partitionEvent hd hpc] with ω hP
        apply ENNReal.ofReal_le_ofReal
        refine (sum_partitionClosure_le hP U t).trans
          (le_of_eq (Finset.sum_congr rfl fun z _ => ?_))
        rw [stoppingSize_goodCubes_eq hP z, ← pow_mul, Nat.mul_comm]
    _ = ENNReal.ofReal (∫ ω, ∑ x ∈ U,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (t + d)
          ∂(latticeBondLaw d p)) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω =>
          Finset.sum_nonneg fun x _ =>
            pow_nonneg (TriadicCube.stoppingSize_nonneg _ x) _)).symm
    _ ≤ ENNReal.ofReal (2 * ((t + d).factorial : ℝ) * θ ^ (t + d) * U.card) :=
        ENNReal.ofReal_le_ofReal hle

end Rigidity.Percolation

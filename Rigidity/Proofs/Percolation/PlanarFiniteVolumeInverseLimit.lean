import Rigidity.Proofs.Percolation.PlanarFiniteVolumeInverse
import Rigidity.Proofs.Percolation.PlanarMuLimitBounds

/-!
# Convergence of the finite-volume homogenized matrices

The limit `L` of the matrices `ā_{□_n}⁻¹` is positive definite (since `lim E[-μ(□_n, q)] ≥ |q|²/18`),
hence invertible, and the finite-volume homogenized matrices `ā_{□_n} = (ā_{□_n}⁻¹)⁻¹` converge
entrywise to `L⁻¹` (in dimension two, by the formula for the inverse of a `2 × 2` matrix).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped Classical Matrix

namespace Rigidity.Percolation

/-- **The limit matrix is invertible.** -/
theorem planarAhomInvLimit_det_ne_zero {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    (planarAhomInvLimit p).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hLv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨C, -, hb⟩ := exists_planarMuLimit_two_sided hpc
  have h1 := (hb v).1
  have hrow : ∀ i, ∑ j, planarAhomInvLimit p i j * v j = 0 := fun i => by
    have := congrFun hLv i
    simpa [Matrix.mulVec, dotProduct] using this
  have hq : ∑ i, ∑ j, v i * planarAhomInvLimit p i j * v j = 0 := by
    simp_rw [mul_assoc, ← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
  rw [planarMuLimit_eq_planarAhomInvLimit hpc, hq, mul_zero] at h1
  apply hv
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.zero_apply]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  · simp only [Fin.mk_one, Pi.zero_apply]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- **The finite-volume homogenized matrices converge** (entrywise) to the inverse of the limit of
the finite-volume inverse matrices. -/
theorem tendsto_planarAhomFinite {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (i j : Fin 2) :
    Tendsto (fun n => planarAhomFinite p n i j) atTop (𝓝 ((planarAhomInvLimit p)⁻¹ i j)) := by
  have hB := tendsto_planarAhomInvFinite hpc
  have hdet : Tendsto (fun n => (planarAhomInvFinite p n).det) atTop
      (𝓝 (planarAhomInvLimit p).det) := by
    simp only [Matrix.det_fin_two]
    exact ((hB 0 0).mul (hB 1 1)).sub ((hB 0 1).mul (hB 1 0))
  have hinv := hdet.inv₀ (planarAhomInvLimit_det_ne_zero hpc)
  simp only [planarAhomFinite, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
  · exact hinv.mul (hB 1 1)
  · exact hinv.mul (hB 0 1).neg
  · exact hinv.mul (hB 1 0).neg
  · exact hinv.mul (hB 0 0)

end Rigidity.Percolation

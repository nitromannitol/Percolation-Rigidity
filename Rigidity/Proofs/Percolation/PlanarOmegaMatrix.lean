import Rigidity.Proofs.Percolation.PlanarOmegaLimit
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeMatrix

/-!
# The identification of the limits in terms of matrices

The limit `Ω(q)` of `E[ω(□_m, q)]` is the quadratic form of `L - ā⁻¹`, where `L` is the limit of
the finite-volume matrices `ā_{□_n}⁻¹`. Since both matrices are symmetric, `Ω` vanishes identically
if and only if `L = ā⁻¹`, that is, if and only if the finite-volume matrices `ā_{□_n}⁻¹` converge to
the inverse of the homogenized matrix (the qualitative content of Proposition 5.2 of Armstrong and
Dario, in dimension two).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix

namespace Rigidity.Percolation

/-- `Ω(q) = (1/2) q · (L - ā⁻¹) q`. -/
theorem planarOmegaLimit_eq_quadratic {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) :
    planarOmegaLimit p q =
      1 / 2 * ∑ i, ∑ j, q i * (planarAhomInvLimit p i j - (planarAhom p)⁻¹ i j) * q j := by
  rw [planarOmegaLimit_eq hpc, planarMuLimit_eq_planarAhomInvLimit hpc]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The inverse of the homogenized matrix is symmetric. -/
theorem planarAhom_inv_symm (p : unitInterval) (i j : Fin 2) :
    (planarAhom p)⁻¹ i j = (planarAhom p)⁻¹ j i := by
  have hT : (planarAhom p)ᵀ = planarAhom p := Matrix.ext fun i j => planarAhom_symm p j i
  have h := Matrix.transpose_nonsing_inv (planarAhom p)
  rw [hT] at h
  have := congrFun (congrFun h j) i
  rw [Matrix.transpose_apply] at this
  exact this

/-- **`Ω` vanishes identically if and only if the finite-volume matrices `ā_{□_n}⁻¹` converge to
`ā⁻¹`** (in dimension two). -/
theorem forall_planarOmegaLimit_eq_zero_iff {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    (∀ q, planarOmegaLimit p q = 0) ↔ planarAhomInvLimit p = (planarAhom p)⁻¹ := by
  constructor
  · intro h
    have hsL : planarAhomInvLimit p 0 1 = planarAhomInvLimit p 1 0 := rfl
    have hsA := planarAhom_inv_symm p 0 1
    have h0 := h ![1, 0]
    have h1 := h ![0, 1]
    have h2 := h ![1, 1]
    rw [planarOmegaLimit_eq_quadratic hpc] at h0 h1 h2
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add] at h0 h1 h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith
  · intro h q
    rw [planarOmegaLimit_eq_quadratic hpc, h]
    simp

end Rigidity.Percolation

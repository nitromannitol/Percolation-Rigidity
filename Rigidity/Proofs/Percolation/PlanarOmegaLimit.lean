import Rigidity.Proofs.Percolation.PlanarNuDefectTau
import Rigidity.Proofs.Percolation.PlanarDuality

/-!
# The limit of `E[ω]` and the identification of the limit of `E[-μ]`

The homogenized matrix `ā` is invertible (it is positive definite, Armstrong and Dario (5.1)).
For the quantity `ω(□, q) = ν(□, ā⁻¹ q) - μ(□, q) - q · ā⁻¹ q` of Armstrong and Dario (Section 5,
before Lemma 5.3), the expectations `E[ω(□_m, q)]` converge to

`Ω(q) = lim E[ν(□_m, ā⁻¹ q)] + lim E[-μ(□_m, q)] - q · ā⁻¹ q = lim E[-μ(□_m, q)] - (1/2) q · ā⁻¹ q`,

since `lim E[ν(□_m, ā⁻¹ q)] = (1/2) ā⁻¹ q · ā ā⁻¹ q = (1/2) q · ā⁻¹ q`. By the duality inequality,
`Ω(q) ≥ 0`. Hence the identification of the limit of `E[-μ(□_m, q)]` with the convex dual
`(1/2) q · ā⁻¹ q` (the qualitative content of Proposition 5.2) is equivalent to `Ω(q) = 0`, which is
what Lemma 5.3 of Armstrong and Dario reduces Proposition 5.2 to.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

/-- **The homogenized matrix is invertible** (in dimension two). -/
theorem planarAhom_det_ne_zero {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    (planarAhom p).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨c, hc, hb⟩ := exists_planarAhom_bounds hpc
  have h1 := (hb v).1
  have hrow : ∀ i, ∑ j, planarAhom p i j * v j = 0 := fun i => by
    have := congrFun hAv i
    simpa [Matrix.mulVec, dotProduct] using this
  have hq : ∑ i, ∑ j, v i * planarAhom p i j * v j = 0 := by
    simp_rw [mul_assoc, ← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
  rw [hq, mul_zero] at h1
  have h0 : v 0 ^ 2 + v 1 ^ 2 ≤ 0 := by
    by_contra hneg
    have := mul_pos hc (lt_of_not_ge hneg)
    linarith
  apply hv
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.zero_apply]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  · simp only [Fin.mk_one, Pi.zero_apply]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem planarAhom_mulVec_inv_mulVec {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) : planarAhom p *ᵥ ((planarAhom p)⁻¹ *ᵥ q) = q := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (planarAhom_det_ne_zero hpc)),
    Matrix.one_mulVec]

/-- `lim E[ν(□_m, ā⁻¹ q)] = (1/2) q · ā⁻¹ q`. -/
theorem planarNuLimit_ahomInv {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) :
    planarNuLimit p ((planarAhom p)⁻¹ *ᵥ q) =
      1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
  rw [planarNuLimit_eq_planarAhom hpc]
  set ξ := (planarAhom p)⁻¹ *ᵥ q with hξ
  have e : ∑ i, ∑ j, ξ i * planarAhom p i j * ξ j = ∑ i, ξ i * (planarAhom p *ᵥ ξ) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [e, hξ, planarAhom_mulVec_inv_mulVec hpc q]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The expectation `E[ω(□_m, q)] = E[ν(□_m, ā⁻¹ q)] + E[-μ(□_m, q)] - q · ā⁻¹ q`. -/
noncomputable def planarOmegaMean (p : unitInterval) (m : ℕ) (q : Fin 2 → ℝ) : ℝ :=
  planarNuMean p m ((planarAhom p)⁻¹ *ᵥ q) + planarMuMean p m q -
    ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i

/-- The limit `Ω(q)` of `E[ω(□_m, q)]`. -/
noncomputable def planarOmegaLimit (p : unitInterval) (q : Fin 2 → ℝ) : ℝ :=
  planarNuLimit p ((planarAhom p)⁻¹ *ᵥ q) + planarMuLimit p q -
    ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i

theorem tendsto_planarOmegaMean {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) :
    Tendsto (fun m => planarOmegaMean p m q) atTop (𝓝 (planarOmegaLimit p q)) :=
  ((tendsto_planarNuLimit hpc _).add (tendsto_planarMuLimit hpc q)).sub tendsto_const_nhds

/-- `Ω(q) = lim E[-μ(□_m, q)] - (1/2) q · ā⁻¹ q`. -/
theorem planarOmegaLimit_eq {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) :
    planarOmegaLimit p q = planarMuLimit p q - 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
  rw [planarOmegaLimit, planarNuLimit_ahomInv hpc]
  ring

/-- **Nonnegativity of `Ω`**: `lim E[-μ(□_m, q)] ≥ (1/2) q · ā⁻¹ q` (duality, in dimension two). -/
theorem planarOmegaLimit_nonneg {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) : 0 ≤ planarOmegaLimit p q := by
  have h := sum_mul_le_planarMuLimit_add_planarNuLimit hpc ((planarAhom p)⁻¹ *ᵥ q) q
  rw [planarNuLimit_ahomInv hpc] at h
  rw [planarOmegaLimit_eq hpc]
  linarith

/-- **Reduction of the identification of the limits to `Ω = 0`** (the qualitative content of
Proposition 5.2 and Lemma 5.3 of Armstrong and Dario, in dimension two):
`lim E[-μ(□_m, q)] = (1/2) q · ā⁻¹ q` if and only if `lim E[ω(□_m, q)] = 0`. -/
theorem planarMuLimit_eq_iff_planarOmegaLimit_eq_zero {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (q : Fin 2 → ℝ) :
    planarMuLimit p q = 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i ↔
      planarOmegaLimit p q = 0 := by
  rw [planarOmegaLimit_eq hpc]
  constructor <;> intro h <;> linarith

end Rigidity.Percolation

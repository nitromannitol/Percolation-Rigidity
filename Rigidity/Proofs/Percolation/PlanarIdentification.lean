import Rigidity.Proofs.Percolation.PlanarOmegaDLimit
import Rigidity.Proofs.Percolation.PlanarOmegaDecayIteration
import Rigidity.Proofs.Percolation.PlanarOmegaMatrix

/-!
# The identification of the limit of `E[-μ]` from the decay of `ω`

Let `L` be the limit of the finite-volume matrices `ā_{□_n}⁻¹`. By duality `L ≥ ā⁻¹`, hence
`L⁻¹ ≤ ā` (testing `ā⁻¹` with `x - ā q`, `x = L⁻¹ q`). If moreover `lim D_n ≤ 0`, that is
`∑ᵢ (ā_{ii} - (L⁻¹)_{ii}) ≤ 0`, then the nonnegative symmetric matrix `ā - L⁻¹` has nonpositive
trace and vanishes, so that `L = ā⁻¹`. Under the bound of Lemma 5.9 of Armstrong and Dario, `D_n`
decays geometrically, and therefore `lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q` for every `q`: the
qualitative content of Proposition 5.2 (in dimension two), with Lemma 5.9 as a hypothesis.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped Classical Matrix

namespace Rigidity.Percolation

theorem sum_sum_eq_dotProduct_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ) (q : Fin 2 → ℝ) :
    ∑ i, ∑ j, q i * M i j * q j = q ⬝ᵥ (M *ᵥ q) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- **`L⁻¹ ≤ ā`**: the inverse of the limit of the finite-volume inverse matrices is below the
homogenized matrix. -/
theorem dotProduct_inv_planarAhomInvLimit_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (q : Fin 2 → ℝ) :
    q ⬝ᵥ ((planarAhomInvLimit p)⁻¹ *ᵥ q) ≤ q ⬝ᵥ (planarAhom p *ᵥ q) := by
  set L := planarAhomInvLimit p with hL
  set A := planarAhom p with hA
  set P := A⁻¹ with hP
  have hLdet := planarAhomInvLimit_det_ne_zero hpc
  have hAdet := planarAhom_det_ne_zero hpc
  have hLLi : ∀ v, L *ᵥ (L⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hLdet),
      Matrix.one_mulVec]
  have hPA : ∀ v, P *ᵥ (A *ᵥ v) = v := fun v => by
    rw [hP, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hAdet),
      Matrix.one_mulVec]
  have hPsymm : Pᵀ = P := Matrix.ext fun i j => planarAhom_inv_symm p j i
  have hLsymm : Lᵀ = L := Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> rfl
  have hLP : ∀ v, v ⬝ᵥ (P *ᵥ v) ≤ v ⬝ᵥ (L *ᵥ v) := fun v => by
    have h := planarOmegaLimit_nonneg hpc v
    rw [planarOmegaLimit_eq_quadratic hpc] at h
    have e : ∑ i, ∑ j, v i * (L i j - P i j) * v j =
        v ⬝ᵥ (L *ᵥ v) - v ⬝ᵥ (P *ᵥ v) := by
      rw [← sum_sum_eq_dotProduct_mulVec, ← sum_sum_eq_dotProduct_mulVec, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
    rw [e] at h
    linarith
  have hP0 : ∀ v, 0 ≤ v ⬝ᵥ (P *ᵥ v) := fun v => by
    have h2 := planarNuLimit_ahomInv hpc v
    have e2 : ∑ i, v i * ((planarAhom p)⁻¹ *ᵥ v) i = v ⬝ᵥ (P *ᵥ v) := rfl
    rw [e2] at h2
    have h3 : 0 ≤ planarNuLimit p ((planarAhom p)⁻¹ *ᵥ v) :=
      ge_of_tendsto' (tendsto_planarNuLimit hpc _) fun m => ENNReal.toReal_nonneg
    rw [h2] at h3
    linarith
  set x := L⁻¹ *ᵥ q with hx
  set y := A *ᵥ q with hy
  have hcross : x ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPsymm, dotProduct_comm]
  have hsq := hP0 (x - y)
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct] at hsq
  have hPy : P *ᵥ y = q := hPA q
  have hxL : x ⬝ᵥ (L *ᵥ x) = x ⬝ᵥ q := by rw [hx, hLLi]
  have hyq : y ⬝ᵥ q = q ⬝ᵥ y := dotProduct_comm _ _
  have hxq : x ⬝ᵥ q = q ⬝ᵥ x := dotProduct_comm _ _
  rw [hPy] at hsq hcross
  have hLx := hLP x
  rw [hxL] at hLx
  rw [← hcross] at hsq
  linarith

/-- **The identification of the limit of `E[-μ]` from the decay of `D_n`** (in dimension two). If
`lim D_n ≤ 0`, then `lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q` for every `q`. -/
theorem planarMuLimit_eq_of_limit_planarOmegaD_nonpos {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ))
    (hD : 1 / 2 * ∑ i : Fin 2, (planarAhom p i i - (planarAhomInvLimit p)⁻¹ i i) ≤ 0)
    (q : Fin 2 → ℝ) :
    planarMuLimit p q = 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
  set L := planarAhomInvLimit p with hL
  set A := planarAhom p with hA
  have hLdet := planarAhomInvLimit_det_ne_zero hpc
  have hle := dotProduct_inv_planarAhomInvLimit_le hpc
  have hsymA : ∀ i j, A i j = A j i := planarAhom_symm p
  have hsymLi : ∀ i j, L⁻¹ i j = L⁻¹ j i := by
    have hT : Lᵀ = L := Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl
    have h := Matrix.transpose_nonsing_inv L
    rw [hT] at h
    intro i j
    have := congrFun (congrFun h j) i
    rw [Matrix.transpose_apply] at this
    exact this
  have hv : ∀ v : Fin 2 → ℝ, 0 ≤ v 0 * v 0 * (A 0 0 - L⁻¹ 0 0) + v 0 * v 1 * (A 0 1 - L⁻¹ 0 1) +
      v 1 * v 0 * (A 1 0 - L⁻¹ 1 0) + v 1 * v 1 * (A 1 1 - L⁻¹ 1 1) := fun v => by
    have h := hle v
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
    nlinarith
  have h10 := hv ![1, 0]
  have h01 := hv ![0, 1]
  have h11 := hv ![1, 1]
  have h1m := hv ![1, -1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h10 h01 h11 h1m
  norm_num at h10 h01 h11 h1m
  rw [Fin.sum_univ_two] at hD
  have s1 := hsymA 0 1
  have s2 := hsymLi 0 1
  have e00 : L⁻¹ 0 0 = A 0 0 := by linarith
  have e11 : L⁻¹ 1 1 = A 1 1 := by linarith
  have e01 : L⁻¹ 0 1 = A 0 1 := by linarith
  have e10 : L⁻¹ 1 0 = A 1 0 := by linarith
  have hLiA : L⁻¹ = A := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11
  have hLeq : L = A⁻¹ := by
    rw [← hLiA, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hLdet)]
  have hΩ : ∀ q, planarOmegaLimit p q = 0 := (forall_planarOmegaLimit_eq_zero_iff hpc).2 hLeq
  exact (planarMuLimit_eq_iff_planarOmegaLimit_eq_zero hpc q).2 (hΩ q)

/-- **Proposition 5.2 of Armstrong and Dario, qualitative part, from Lemma 5.9** (in dimension
two). If `D_n ≤ C (σⁿ + ∑_{l ≤ n} ρ^{n-l} τ_l)` from some scale on, with `σ, ρ < 1`, then
`lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q` for every `q`. -/
theorem planarMuLimit_eq_of_decay {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉) (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉)
    (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → planarOmegaD p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * planarTau p l)
    (q : Fin 2 → ℝ) :
    planarMuLimit p q = 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
  obtain ⟨K, l, hl0, hl1, N, hK⟩ :=
    exists_planarOmegaD_le_pow_of_decay hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  have hlim := tendsto_planarOmegaD hpc
  have hpow : Tendsto (fun n => K * l ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1).const_mul K
  have hD := le_of_tendsto_of_tendsto hlim hpow (eventually_atTop.2 ⟨N, hK⟩)
  exact planarMuLimit_eq_of_limit_planarOmegaD_nonpos hpc hD q

end Rigidity.Percolation

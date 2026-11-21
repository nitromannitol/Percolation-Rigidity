import Rigidity.Proofs.Percolation.PlanarFiniteVolumeMatrix
import Rigidity.Proofs.Percolation.PlanarMuIncrements

/-!
# Closeness of the finite-volume matrices at two scales

For `n ≤ m`, the quadratic forms `E[-μ(□_m, ·)]` and `E[-μ(□_n, ·)]` differ by at most
`2 |q|² ∑_{k=n}^{m-1} τ^μ_k + C |q|₁² (∑_{k=n}^{m-1} ε_k + ε_n)`, with
`ε_k = 3 ^ (-k/2) + exp (-c 3 ^ k)`: the decrease is controlled by `τ^μ` and the increase by the
approximate monotonicity. Consequently the entries of the finite-volume matrices satisfy
`|ā_{□_m}⁻¹ - ā_{□_n}⁻¹| ≤ C (∑_{k=n}^{m-1} τ^μ_k + ∑_{k=n}^{m-1} ε_k + ε_n)`
(Armstrong and Dario, display (5.24), in dimension two).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- **The quadratic forms `E[-μ(□_m, ·)]` and `E[-μ(□_n, ·)]` are close.** -/
theorem exists_abs_planarMuMean_sub_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), n ≤ m → ∀ q : Fin 2 → ℝ,
      |planarMuMean p m q - planarMuMean p n q| ≤
        2 * (q 0 ^ 2 + q 1 ^ 2) * ∑ k ∈ Finset.Ico n m, planarMuTau p k +
          C * (|q 0| + |q 1|) ^ 2 * (∑ k ∈ Finset.Ico n m,
            (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
            (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, hmono⟩ := exists_lintegral_neg_planarMu_le_of_scale_le hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  obtain ⟨C₂, hC₂, c₂, hc₂, hsub⟩ := exists_planarMuMean_sub_le hpc
  set c := min c₁ c₂ with hcdef
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨C₁.toReal + C₂, by positivity, c, hc, fun n m hnm q => ?_⟩
  have hε : ∀ k : ℕ, ∀ c' : ℝ, c ≤ c' → Real.exp (-c' * (3 : ℝ) ^ k) ≤
      Real.exp (-c * (3 : ℝ) ^ k) := fun k c' hc' => by
    apply Real.exp_le_exp.2
    have h3 : (0 : ℝ) ≤ 3 ^ k := by positivity
    nlinarith
  -- the increase
  have hinc : planarMuMean p m q - planarMuMean p n q ≤ C₁.toReal * ((|q 0| + |q 1|) ^ 2 *
      (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) := by
    have h := hmono ⟨m, 0⟩ ⟨n, 0⟩ hnm q
    have hfin := ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top)
      (hup ⟨n, 0⟩ q)
    have h' := toReal_le_toReal_add_of_lintegral_le hfin hC₁ (by positivity) h
    simp only [planarMuMean]
    linarith
  -- the decrease
  have hdec := hsub n m hnm q
  set Q := (|q 0| + |q 1|) ^ 2 with hQ
  set S := ∑ k ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k))
    with hSdef
  set e := 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n) with hedef
  have hQ0 : 0 ≤ Q := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  have he0 : 0 ≤ e := by positivity
  have hT : 0 ≤ ∑ k ∈ Finset.Ico n m, planarMuTau p k :=
    Finset.sum_nonneg fun k _ => planarMuTau_nonneg p k
  have hq2 : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
  have hC₁0 : 0 ≤ C₁.toReal := ENNReal.toReal_nonneg
  have k1 : C₁.toReal * (Q * (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) ≤
      C₁.toReal * (Q * e) := by
    rw [hedef]
    gcongr
    exact min_le_left _ _
  have k2 : C₂ * Q * ∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₂ * (3 : ℝ) ^ k)) ≤ C₂ * Q * S := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
    exact add_le_add le_rfl (hε k c₂ (min_le_right _ _))
  have hsplit : (C₁.toReal + C₂) * Q * (S + e) = C₁.toReal * (Q * e) + C₂ * Q * S +
      (C₁.toReal * Q * S + C₂ * Q * e) := by ring
  have hextra : 0 ≤ C₁.toReal * Q * S + C₂ * Q * e := by positivity
  have hτ0 : 0 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) * ∑ k ∈ Finset.Ico n m, planarMuTau p k := by
    positivity
  have hp1 : 0 ≤ C₁.toReal * (Q * e) := by positivity
  have hp2 : 0 ≤ C₂ * Q * S := by positivity
  rw [abs_le, hsplit]
  constructor <;> linarith

/-- **Closeness of the finite-volume matrices** (Armstrong and Dario, display (5.24), in dimension
two). -/
theorem exists_abs_planarAhomInvFinite_sub_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), n ≤ m → ∀ i j : Fin 2,
      |planarAhomInvFinite p m i j - planarAhomInvFinite p n i j| ≤
        C * (∑ k ∈ Finset.Ico n m, planarMuTau p k + (∑ k ∈ Finset.Ico n m,
            (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
            (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n)))) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_abs_planarMuMean_sub_le hpc
  refine ⟨12 * (4 + 4 * C), by positivity, c, hc, fun n m hnm i j => ?_⟩
  set T := ∑ k ∈ Finset.Ico n m, planarMuTau p k with hTdef
  set E := ∑ k ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
    (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n)) with hEdef
  have hT : 0 ≤ T := Finset.sum_nonneg fun k _ => planarMuTau_nonneg p k
  have hE : 0 ≤ E := by
    have : 0 ≤ ∑ k ∈ Finset.Ico n m,
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) :=
      Finset.sum_nonneg fun k _ => by positivity
    have : 0 ≤ 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n) := by positivity
    linarith
  have hb : ∀ q : Fin 2 → ℝ, q 0 ^ 2 + q 1 ^ 2 ≤ 2 → (|q 0| + |q 1|) ^ 2 ≤ 4 →
      |planarMuMean p m q - planarMuMean p n q| ≤ (4 + 4 * C) * (T + E) := by
    intro q h1 h2
    have := h n m hnm q
    rw [← hTdef, ← hEdef] at this
    have a1 : 2 * (q 0 ^ 2 + q 1 ^ 2) * T ≤ 4 * T := by nlinarith
    have a2 : C * (|q 0| + |q 1|) ^ 2 * E ≤ 4 * C * E := by
      have := mul_le_mul_of_nonneg_left h2 hC
      nlinarith
    nlinarith
  have b10 := hb ![1, 0] (by simp) (by simp)
  have b01 := hb ![0, 1] (by simp) (by simp)
  have b11 := hb ![1, 1] (by norm_num) (by norm_num)
  have hK : 0 ≤ (4 + 4 * C) * (T + E) := by positivity
  fin_cases i <;> fin_cases j <;>
    simp only [planarAhomInvFinite, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
  · rw [← mul_sub, abs_mul, abs_two]
    linarith
  · have e : planarMuMean p m ![1, 1] - planarMuMean p m ![1, 0] - planarMuMean p m ![0, 1] -
        (planarMuMean p n ![1, 1] - planarMuMean p n ![1, 0] - planarMuMean p n ![0, 1]) =
        (planarMuMean p m ![1, 1] - planarMuMean p n ![1, 1]) -
        (planarMuMean p m ![1, 0] - planarMuMean p n ![1, 0]) -
        (planarMuMean p m ![0, 1] - planarMuMean p n ![0, 1]) := by ring
    rw [e]
    have := abs_sub (planarMuMean p m ![1, 1] - planarMuMean p n ![1, 1] -
      (planarMuMean p m ![1, 0] - planarMuMean p n ![1, 0]))
      (planarMuMean p m ![0, 1] - planarMuMean p n ![0, 1])
    have := abs_sub (planarMuMean p m ![1, 1] - planarMuMean p n ![1, 1])
      (planarMuMean p m ![1, 0] - planarMuMean p n ![1, 0])
    linarith
  · have e : planarMuMean p m ![1, 1] - planarMuMean p m ![1, 0] - planarMuMean p m ![0, 1] -
        (planarMuMean p n ![1, 1] - planarMuMean p n ![1, 0] - planarMuMean p n ![0, 1]) =
        (planarMuMean p m ![1, 1] - planarMuMean p n ![1, 1]) -
        (planarMuMean p m ![1, 0] - planarMuMean p n ![1, 0]) -
        (planarMuMean p m ![0, 1] - planarMuMean p n ![0, 1]) := by ring
    rw [e]
    have := abs_sub (planarMuMean p m ![1, 1] - planarMuMean p n ![1, 1] -
      (planarMuMean p m ![1, 0] - planarMuMean p n ![1, 0]))
      (planarMuMean p m ![0, 1] - planarMuMean p n ![0, 1])
    have := abs_sub (planarMuMean p m ![1, 1] - planarMuMean p n ![1, 1])
      (planarMuMean p m ![1, 0] - planarMuMean p n ![1, 0])
    linarith
  · rw [← mul_sub, abs_mul, abs_two]
    linarith

end Rigidity.Percolation

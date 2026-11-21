import Rigidity.Proofs.Percolation.PlanarOmegaStepOne
import Rigidity.Proofs.Percolation.PlanarDuality

/-!
# The negative part of `D_n` is small

By the comparison of `μ` and `ν` in expectation, `eᵢ · ā_{□_n} eᵢ ≤ E[-μ(□_n, ā_{□_n} eᵢ)] +
E[ν(□_n, eᵢ)] + C |ā_{□_n} eᵢ|₁ 3^(-n/2)`, so that `D_n ≥ -C 3^(-n/2)` from the scale of uniform
ellipticity on (the lower bound on `D_n` in the proof of Lemma 5.10 of Armstrong and Dario, in
dimension two).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

/-- **Lower bound for `D_n`.** -/
theorem exists_neg_le_planarOmegaD {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → -(C * (1 / Real.sqrt ((3 : ℝ) ^ n))) ≤
      planarOmegaD p n := by
  obtain ⟨Cb, hCb, N, hN⟩ := exists_planarAhomInvFinite_mulVec_planarAhomFinite hpc
  obtain ⟨C, hC, hdual⟩ := exists_ofReal_sum_mul_le_lintegral hpc
  obtain ⟨C₂, hC₂, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  refine ⟨2 * (C.toReal * 36), by positivity, N, fun n hn => ?_⟩
  obtain ⟨hinv, -, hb⟩ := hN n hn
  set s := 1 / Real.sqrt ((3 : ℝ) ^ n) with hs
  have hs0 : 0 ≤ s := by positivity
  have hterm : ∀ i : Fin 2, -(C.toReal * 36 * s) ≤
      planarNuMean p n (Pi.single i 1) +
        planarMuMean p n (planarAhomFinite p n *ᵥ Pi.single i 1) -
        (planarAhomFinite p n *ᵥ Pi.single i 1) i := by
    intro i
    set x := planarAhomFinite p n *ᵥ Pi.single i 1 with hx
    have hsq := planarAhomFinite_single_sq_le hpc hinv (fun q => (hb q).1) i
    rw [← hx] at hsq
    have hx0 : |x 0| ≤ 18 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
      nlinarith [sq_nonneg (x 1)]
    have hx1 : |x 1| ≤ 18 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
      nlinarith [sq_nonneg (x 0)]
    have hξ : 0 < |(Pi.single i 1 : Fin 2 → ℝ) 0| + |(Pi.single i 1 : Fin 2 → ℝ) 1| := by
      fin_cases i <;> simp
    have hξ1 : |(Pi.single i 1 : Fin 2 → ℝ) 0| + |(Pi.single i 1 : Fin 2 → ℝ) 1| = 1 := by
      fin_cases i <;> simp
    have h := hdual ⟨n, 0⟩ (Pi.single i 1) x hξ
    rw [hξ1, mul_one] at h
    have hfμ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₂ ENNReal.ofReal_ne_top) (hup ⟨n, 0⟩ x)
    have hfν := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_planarNu_le p ⟨n, 0⟩ (Pi.single i 1))
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hfμ, hfν⟩,
      ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top⟩) h
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfμ, hfν⟩)
        (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top),
      ENNReal.toReal_add hfμ hfν, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg (by positivity) (Real.sqrt_nonneg _))] at h2
    have h3 : ∑ j, x j * (Pi.single i 1 : Fin 2 → ℝ) j ≤
        (ENNReal.ofReal (∑ j, x j * (Pi.single i 1 : Fin 2 → ℝ) j)).toReal := by
      rw [ENNReal.toReal_ofReal']
      exact le_max_left _ _
    have hsum : ∑ j, x j * (Pi.single i 1 : Fin 2 → ℝ) j = x i := by
      rw [← sum_single_mul i x]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hsum] at h3 h2
    have hX : (|x 0| + |x 1|) / Real.sqrt ((3 : ℝ) ^ n) ≤ 36 * s := by
      rw [hs, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (by linarith) hs0
    have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    have := mul_le_mul_of_nonneg_left hX hC0
    simp only [planarMuMean, planarNuMean]
    linarith
  rw [planarOmegaD, Fin.sum_univ_two]
  linarith [hterm 0, hterm 1]

end Rigidity.Percolation

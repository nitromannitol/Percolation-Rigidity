import Rigidity.Proofs.Percolation.PlanarFiniteVolumeMatrix
import Rigidity.Proofs.Percolation.PlanarLimitCubes

/-!
# Uniform ellipticity of the finite-volume matrices

From the bounds `|q|² / 18 - C |q|₁² 3^(-n/2) ≤ E[-μ(□_n, q)] ≤ C |q|₁²`, the finite-volume matrices
satisfy `c |q|² ≤ (1/2) q · ā_{□_n}⁻¹ q ≤ C |q|²` for all `n ≥ N` (Armstrong and Dario,
display (5.22), in dimension two).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- `|q|₁² ≤ 2 |q|²` in the plane. -/
theorem abs_add_abs_sq_le (q : Fin 2 → ℝ) : (|q 0| + |q 1|) ^ 2 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) := by
  have h0 := sq_abs (q 0)
  have h1 := sq_abs (q 1)
  nlinarith [sq_nonneg (|q 0| - |q 1|)]

/-- **Bounds on `E[-μ(□_n, ·)]` for large `n`.** -/
theorem exists_planarMuMean_bounds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ q : Fin 2 → ℝ,
      (q 0 ^ 2 + q 1 ^ 2) / 36 ≤ planarMuMean p n q ∧
        planarMuMean p n q ≤ C * (q 0 ^ 2 + q 1 ^ 2) := by
  obtain ⟨C₁, hC₁, hlow⟩ := exists_lintegral_neg_planarMu_ge hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  have hpos : (0 : ℝ) < 1 / (72 * (C₁.toReal + 1)) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_order.1 tendsto_one_div_sqrt_three_pow).2 _ hpos)
  refine ⟨2 * C₀.toReal, by positivity, N, fun n hn q => ⟨?_, ?_⟩⟩
  · have h := hlow ⟨n, 0⟩ q
    have hfin := ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top)
      (hup ⟨n, 0⟩ q)
    have hR : ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
        ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) else 0) ∂(latticeBondLaw 2 p) +
        C₁ * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 / Real.sqrt ((3 : ℝ) ^ n)) ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨hfin, ENNReal.mul_ne_top hC₁ ENNReal.ofReal_ne_top⟩
    have h' := ENNReal.toReal_mono hR h
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_add hfin
      (ENNReal.mul_ne_top hC₁ ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)] at h'
    have hs := hN n hn
    have hq := abs_add_abs_sq_le q
    have hC₁0 : 0 ≤ C₁.toReal := ENNReal.toReal_nonneg
    have hq2 : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
    have e1 : (|q 0| + |q 1|) ^ 2 / Real.sqrt ((3 : ℝ) ^ n) =
        (|q 0| + |q 1|) ^ 2 * (1 / Real.sqrt ((3 : ℝ) ^ n)) := by ring
    have e2 : C₁.toReal * ((|q 0| + |q 1|) ^ 2 * (1 / Real.sqrt ((3 : ℝ) ^ n))) ≤
        (q 0 ^ 2 + q 1 ^ 2) / 36 := by
      have a1 : (|q 0| + |q 1|) ^ 2 * (1 / Real.sqrt ((3 : ℝ) ^ n)) ≤
          2 * (q 0 ^ 2 + q 1 ^ 2) * (1 / (72 * (C₁.toReal + 1))) :=
        mul_le_mul hq hs.le (by positivity) (by positivity)
      have a2 : C₁.toReal * (2 * (q 0 ^ 2 + q 1 ^ 2) * (1 / (72 * (C₁.toReal + 1)))) ≤
          (q 0 ^ 2 + q 1 ^ 2) / 36 := by
        rw [show C₁.toReal * (2 * (q 0 ^ 2 + q 1 ^ 2) * (1 / (72 * (C₁.toReal + 1)))) =
          (q 0 ^ 2 + q 1 ^ 2) / 36 * (C₁.toReal / (C₁.toReal + 1)) by field_simp; ring]
        have : C₁.toReal / (C₁.toReal + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
        have h36 : 0 ≤ (q 0 ^ 2 + q 1 ^ 2) / 36 := by positivity
        nlinarith
      exact (mul_le_mul_of_nonneg_left a1 hC₁0).trans a2
    rw [e1] at h'
    simp only [planarMuMean]
    linarith
  · have h := hup ⟨n, 0⟩ q
    have hC : C₀ * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) =
        ENNReal.ofReal (C₀.toReal * (|q 0| + |q 1|) ^ 2) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC₀]
    have h' : (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
        ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) else 0) ∂(latticeBondLaw 2 p)).toReal ≤
        C₀.toReal * (|q 0| + |q 1|) ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans hC.le)
    have hq := abs_add_abs_sq_le q
    have hC₀0 : 0 ≤ C₀.toReal := ENNReal.toReal_nonneg
    have h2 := mul_le_mul_of_nonneg_left hq hC₀0
    simp only [planarMuMean]
    linarith

/-- **Uniform ellipticity of the finite-volume matrices** (Armstrong and Dario, display (5.22), in
dimension two). -/
theorem exists_planarAhomInvFinite_bounds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ q : Fin 2 → ℝ,
      (q 0 ^ 2 + q 1 ^ 2) / 36 ≤ 1 / 2 * ∑ i, ∑ j, q i * planarAhomInvFinite p n i j * q j ∧
        1 / 2 * ∑ i, ∑ j, q i * planarAhomInvFinite p n i j * q j ≤ C * (q 0 ^ 2 + q 1 ^ 2) := by
  obtain ⟨C, hC, N, h⟩ := exists_planarMuMean_bounds hpc
  refine ⟨C, hC, N, fun n hn q => ?_⟩
  rw [← planarMuMean_eq_planarAhomInvFinite hpc]
  exact h n hn q

end Rigidity.Percolation

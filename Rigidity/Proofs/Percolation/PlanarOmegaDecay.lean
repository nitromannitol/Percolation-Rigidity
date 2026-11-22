import Rigidity.Proofs.Percolation.PlanarOmegaRates
import Rigidity.Proofs.Percolation.PlanarIdentification

/-!
# Lemma 5.9 of Armstrong and Dario in dimension two, and Proposition 5.2 (qualitative)

From Lemma 5.7 (`PlanarWeakConvergence`), Lemma 5.5 (`PlanarRestrictQuadCoarsenMu`,
`PlanarRestrictQuadCoarsenNu`) and the energy bounds (4.24), (4.25)
(`PlanarCoarseGradMomentMu`, `PlanarCoarseGradMomentNu`), every term of
`D_n = ∑ᵢ (E[ν(□_n, eᵢ)] - E[μ(□_n, ā_{□_n} eᵢ)] - eᵢ · ā_{□_n} eᵢ)` satisfies

`E[ν(□_n, eᵢ)] - E[μ(□_n, q)] - q · eᵢ ≤ K (3^{-n/10} + ∑_{k=0}^{n} 3^{k-n} τ_k)`,
`q = ā_{□_n} eᵢ`, for `n ≥ N`: display (5.37) of Lemma 5.9 of Armstrong and Dario (the
quantity of (5.37) with `ā_{□_n}⁻¹ q = eᵢ`, without the absolute value, which is what Lemma 5.10
uses), in dimension two. This is the hypothesis of `planarMuLimit_eq_of_decay` with
`σ = 3^{-1/10}` and `ρ = 1/3`, whence the identification `lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q`,
the qualitative part of Proposition 5.2.

The proof follows Armstrong and Dario: quadratic response (5.38), the energies of the differences
of Lemma 5.4, the Caccioppoli inequality (5.39), the coarsening (5.40) and the flatness of
Lemma 5.8 (5.41). Every random quantity is bounded by a measurable majorant with controlled
expectation, except one, so that the expectations add; see `PlanarOmegaAssembly`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

namespace Rigidity.Percolation

theorem ahom_inv_mulVec_ahom_mulVec {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (x : Fin 2 → ℝ) : (planarAhom p)⁻¹ *ᵥ (planarAhom p *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2
    (planarAhom_det_ne_zero hpc)), Matrix.one_mulVec]

theorem abs_le_of_sq_add_sq_le {a b K : ℝ} (h : a ^ 2 + b ^ 2 ≤ K ^ 2) (hK : 0 ≤ K) :
    |a| ≤ K ∧ |b| ≤ K := by
  have ha : |a| ^ 2 ≤ K ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg b]
  have hb : |b| ^ 2 ≤ K ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg a]
  exact ⟨(pow_le_pow_iff_left₀ (abs_nonneg a) hK two_ne_zero).1 ha,
    (pow_le_pow_iff_left₀ (abs_nonneg b) hK two_ne_zero).1 hb⟩

/-- The slope `ā_{□_n} eᵢ` has nonnegative `i`-th entry. -/
theorem planarAhomFinite_single_self_nonneg {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {n : ℕ}
    (hinv : ∀ q : Fin 2 → ℝ, planarAhomInvFinite p n *ᵥ (planarAhomFinite p n *ᵥ q) = q)
    (i : Fin 2) : 0 ≤ (planarAhomFinite p n *ᵥ Pi.single i 1) i := by
  have hM := planarMuMean_planarAhomFinite hpc hinv (Pi.single i 1)
  have hsum : ∑ j, (Pi.single i 1 : Fin 2 → ℝ) j * (planarAhomFinite p n *ᵥ Pi.single i 1) j =
      (planarAhomFinite p n *ᵥ Pi.single i 1) i := by
    fin_cases i <;> simp [Fin.sum_univ_two]
  rw [hsum] at hM
  have h0 : 0 ≤ planarMuMean p n (planarAhomFinite p n *ᵥ Pi.single i 1) := ENNReal.toReal_nonneg
  linarith

/-- The real inequality of the integrated bound, for the slopes `ξ = eᵢ` and `q = ā_{□_n} eᵢ`. -/
theorem exists_planarOmegaD_term_raw {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (h57 : PlanarWeakConvergence p) (h55μ : PlanarRestrictQuadCoarsenMu p)
    (h55ν : PlanarRestrictQuadCoarsenNu p) (hcgμ : PlanarCoarseGradMomentMu p)
    (hcgν : PlanarCoarseGradMomentNu p) :
    ∃ CB CH Cu Cv Cμ CBad C1 c1 C3 c3 CG : ℝ, 0 ≤ CB ∧ 0 ≤ CH ∧ 0 ≤ Cu ∧ 0 ≤ Cv ∧ 0 ≤ Cμ ∧
      0 ≤ CBad ∧ 0 ≤ C1 ∧ 0 < c1 ∧ 0 ≤ C3 ∧ 0 < c3 ∧ 0 ≤ CG ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ (ξ q : Fin 2 → ℝ), 0 < |ξ 0| + |ξ 1| → 0 ≤ ∑ i, q i * ξ i →
      planarAhomInvFinite p n *ᵥ q = ξ →
      planarNuMean p n ξ + planarMuMean p n q +
          3 / (⟨n, 0⟩ : TriadicCube 2).volume * (⟨n + 1, 0⟩ : TriadicCube 2).volume *
            (planarMuMean p (n + 1) q + planarNuMean p (n + 1) ξ) ≤
        (∑ i, q i * ξ i + (∑ i, q i * ξ i) / ((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℝ)) +
          (|q 0| + |q 1|) * (CB * (|ξ 0| + |ξ 1|) /
            Real.sqrt ((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℝ)) +
          48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) *
            (CH * ((|ξ 0| + |ξ 1|) ^ 2 + (|q 0| + |q 1|) ^ 2) *
              (⟨n + 1, 0⟩ : TriadicCube 2).volume * (3 : ℝ) ^ (⟨n + 1, 0⟩ : TriadicCube 2).scale) +
          96 * (⟨n + 1, 0⟩ : TriadicCube 2).volume /
              (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) *
            (Cu * (q 0 ^ 2 + q 1 ^ 2) * (9 : ℝ) ^ n *
                ((3 : ℝ) ^ (-(n : ℝ) / 10) +
                  ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k) +
              Cv * (ξ 0 ^ 2 + ξ 1 ^ 2) * (9 : ℝ) ^ n *
                ((3 : ℝ) ^ (-(n : ℝ) / 10) +
                  ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k)) +
          3 / (⟨n, 0⟩ : TriadicCube 2).volume * (Cμ * ((|q 0| + |q 1|) ^ 2 *
            (⟨n + 1, 0⟩ : TriadicCube 2).volume / Real.sqrt (3 ^ n))) +
          3 / (⟨n, 0⟩ : TriadicCube 2).volume * ((⟨n + 1, 0⟩ : TriadicCube 2).volume *
            (planarMuMean p n q + C1 * ((|q 0| + |q 1|) ^ 2 * Real.exp (-c1 * (3 : ℝ) ^ n)))) +
          3 / (⟨n, 0⟩ : TriadicCube 2).volume * ((⟨n + 1, 0⟩ : TriadicCube 2).volume *
            (planarNuMean p n ξ + C3 * ((|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c3 * (3 : ℝ) ^ n)))) +
          CBad * (1 + (|ξ 0| + |ξ 1|) ^ 2 + (|q 0| + |q 1|) ^ 4) / (9 : ℝ) ^ n +
          3 / (⟨n, 0⟩ : TriadicCube 2).volume * (CG * ((|ξ 0| + |ξ 1|) ^ 2 *
            (⟨n + 1, 0⟩ : TriadicCube 2).volume / Real.sqrt (3 ^ n))) := by
  obtain ⟨CB, hCB, hB⟩ := exists_boundaryMajorant hpc
  obtain ⟨CH, hCH, hHm⟩ := exists_coarseError_majorant hpc
  obtain ⟨Cu, hCu, hUf⟩ := exists_planarMuFlatness_majorant hpc h57 h55μ hcgμ
  obtain ⟨Cv, hCv, hVf⟩ := exists_planarNuFlatness_majorant hpc h55ν hcgν
  obtain ⟨Cμ, hCμ, hMμ⟩ := exists_muSubGap_majorant hpc
  obtain ⟨CBad, hCBad, hBad⟩ := exists_badMajorant hpc
  obtain ⟨C1, hC1, c1, hc1, hX1⟩ := exists_lintegral_subMuSum_le hpc
  obtain ⟨C3, hC3, c3, hc3, hX3⟩ := exists_lintegral_subNuSum_le hpc
  obtain ⟨CG, hCG, hG⟩ := exists_lintegral_nuSubGap_le hpc
  refine ⟨CB, CH, Cu, Cv, Cμ, CBad, C1, c1, C3, c3, CG, hCB, hCH, hCu, hCv, hCμ, hCBad, hC1, hc1,
    hC3, hc3, hCG, 1, fun n hn ξ q hξ hs hξq => ?_⟩
  set U : TriadicCube 2 := ⟨n + 1, 0⟩
  set V : TriadicCube 2 := ⟨n, 0⟩
  obtain ⟨M, hMm, hM0, hMle, hMint⟩ := hB V ξ hξ
  obtain ⟨H, hHmeas, hHle, hHint⟩ := hHm U ξ q
  obtain ⟨Φu, hΦum, hΦu0, hΦule, hΦuint⟩ := hUf n q
  obtain ⟨Φv, hΦvm, hΦv0, hΦvle, hΦvint⟩ := hVf n ξ
  obtain ⟨Mμ, hMμm, hMμle, hMμint⟩ := hMμ U n (Nat.le_succ n) q
  obtain ⟨Bad, hBadm, hBadle, hBadint⟩ := hBad n ξ q
  rw [hξq] at hΦule
  set Q1 := |q 0| + |q 1| with hQ1
  have hQ10 : 0 ≤ Q1 := by positivity
  have hMb : ∀ ω, PlanarPartitionEvent ω → PlanarResolved ω V →
      Q1 * boundaryError ω V ξ (planarNuMaximizer ω V ξ) / V.volume ≤ Q1 * M ω := by
    intro ω hP hVr
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hMle ω hP hVr) hQ10
  have IMb : ∫⁻ ω, ENNReal.ofReal (Q1 * M ω) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (Q1 * (CB * (|ξ 0| + |ξ 1|) /
        Real.sqrt (V.toIntegerCube.size : ℝ))) := by
    simp_rw [ENNReal.ofReal_mul hQ10]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_of_nonneg_left hMint zero_le
  exact planarOmega_integral_le (p := p) hn ξ q hs (hMm.const_mul _).aemeasurable
    hHmeas.aemeasurable hΦum hΦvm hMμm.aemeasurable hBadm.aemeasurable hΦu0 hΦv0 hMb hHle hΦule
    hΦvle hMμle hBadle IMb hHint hΦuint hΦvint hMμint (hX1 U n q) (hX3 U n ξ) hBadint
    (hG U n (Nat.le_succ n) ξ)
    ⟨mul_nonneg hQ10 (div_nonneg (mul_nonneg hCB (by positivity)) (Real.sqrt_nonneg _)),
      mul_nonneg (mul_nonneg (mul_nonneg hCH (by positivity)) U.volume_pos.le) (by positivity),
      mul_nonneg (by positivity) (add_nonneg (by positivity) (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (planarTau_nonneg p k)))),
      mul_nonneg (by positivity) (add_nonneg (by positivity) (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (planarTau_nonneg p k)))),
      mul_nonneg hCμ (div_nonneg (mul_nonneg (by positivity) U.volume_pos.le) (Real.sqrt_nonneg _)),
      mul_nonneg U.volume_pos.le (add_nonneg ENNReal.toReal_nonneg (by positivity)),
      mul_nonneg U.volume_pos.le (add_nonneg ENNReal.toReal_nonneg (by positivity)),
      by positivity,
      mul_nonneg hCG (div_nonneg (mul_nonneg (by positivity) U.volume_pos.le) (Real.sqrt_nonneg _))⟩

end Rigidity.Percolation

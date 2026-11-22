import Rigidity.Proofs.Percolation.PlanarOmegaRates
import Rigidity.Proofs.Percolation.PlanarIdentification
import Rigidity.Proofs.Percolation.PlanarFlatnessAE

/-!
# Lemma 5.9 of Armstrong and Dario in dimension two, and Proposition 5.2 (qualitative)

From Lemma 5.7 (`PlanarWeakConvergence`), Lemma 5.5 (`PlanarRestrictQuadCoarsenMu`,
`PlanarRestrictQuadCoarsenNu`), the energy bounds (4.24), (4.25) being proved with measurable
majorants (`PlanarCoarseEnergyMajorant`), every term of
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
    (h55ν : PlanarRestrictQuadCoarsenNu p) :
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
  obtain ⟨Cu, hCu, hUf⟩ := exists_planarMuFlatness_majorant_ae hpc h57 h55μ
  obtain ⟨Cv, hCv, hVf⟩ := exists_planarNuFlatness_majorant_ae hpc h55ν
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

set_option maxHeartbeats 400000 in
/-- **The arithmetic of the proof of Lemma 5.9.** -/
theorem planarOmega_term_arith {p : unitInterval} {n : ℕ} (hn : 1 ≤ n) {ξ q : Fin 2 → ℝ}
    (hξ1 : |ξ 0| + |ξ 1| = 1) (hξ2 : ξ 0 ^ 2 + ξ 1 ^ 2 = 1) (hq : q 0 ^ 2 + q 1 ^ 2 ≤ 324)
    (hs18 : ∑ i, q i * ξ i ≤ 18)
    {CB CH Cu Cv Cμ CBad C1 c1 C3 c3 CG Ci ci Cj cj KA KB : ℝ} (hCB : 0 ≤ CB) (hCH : 0 ≤ CH)
    (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv) (hCμ : 0 ≤ Cμ) (hCBad : 0 ≤ CBad) (hC1 : 0 ≤ C1) (hc1 : 0 < c1)
    (hC3 : 0 ≤ C3) (hc3 : 0 < c3) (hCG : 0 ≤ CG) (hCi : 0 ≤ Ci) (hci : 0 < ci) (hCj : 0 ≤ Cj)
    (hcj : 0 < cj) (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hraw : planarNuMean p n ξ + planarMuMean p n q +
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
            (⟨n + 1, 0⟩ : TriadicCube 2).volume / Real.sqrt (3 ^ n))))
    (hI : planarMuMean p n q - planarMuMean p (n + 1) q ≤
      2 * 324 * planarMuTau p n + Ci * 1296 * (1 / Real.sqrt ((3 : ℝ) ^ n) +
        Real.exp (-ci * (3 : ℝ) ^ n)))
    (hJ : planarNuMean p n ξ - planarNuMean p (n + 1) ξ ≤
      2 * KA * planarNuTau p n + Cj * KB * (1 / Real.sqrt ((3 : ℝ) ^ n) +
        Real.exp (-cj * (3 : ℝ) ^ n))) :
    planarNuMean p n ξ + planarMuMean p n q - ∑ i, q i * ξ i ≤
      (18 + 36 * CB + 1296 * 1297 * 4 * 3 * CH + 3456 * (324 * Cu + Cv) + 27 * 1296 * Cμ +
        27 * 1296 * C1 * c1⁻¹ + 27 * C3 * c3⁻¹ + CBad * (2 + 36 ^ 4) + 27 * CG +
        27 * 1296 * Ci * (1 + ci⁻¹) + 27 * Cj * KB * (1 + cj⁻¹) + 27 * 648 + 54 * KA) *
        ((3 : ℝ) ^ (-(n : ℝ) / 10) +
          ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k) := by
  set ε := (3 : ℝ) ^ (-(n : ℝ) / 10) with hε
  set R := ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k with hR
  have hε0 : 0 ≤ ε := by positivity
  have hR0 : 0 ≤ R := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (planarTau_nonneg p k))
  set s := ∑ i, q i * ξ i with hsdef
  set X : ℝ := (9 : ℝ) ^ n with hX
  set T : ℝ := (3 : ℝ) ^ n with hT
  have hT0 : 0 < T := by positivity
  have hX0 : 0 < X := by positivity
  have hXT : X = T * T := by rw [hX, hT, ← mul_pow]; norm_num
  have hVv : (⟨n, 0⟩ : TriadicCube 2).volume = X := rfl
  have hUv : (⟨n + 1, 0⟩ : TriadicCube 2).volume = 9 * X := by
    change (9 : ℝ) ^ (n + 1) = _
    rw [pow_succ, hX]
    ring
  have hUs : (3 : ℝ) ^ (⟨n + 1, 0⟩ : TriadicCube 2).scale = 3 * T := by
    change (3 : ℝ) ^ (n + 1) = _
    rw [pow_succ, hT]
    ring
  have hL : ((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℝ) = T := by
    change ((3 ^ n : ℕ) : ℝ) = _
    push_cast
    rfl
  rw [hVv, hUv, hUs, hL, hξ1, hξ2] at hraw
  have hq18 := abs_le_of_sq_add_sq_le (show q 0 ^ 2 + q 1 ^ 2 ≤ 18 ^ 2 by linarith) (by norm_num)
  set Q1 := |q 0| + |q 1| with hQ1
  have hQ10 : 0 ≤ Q1 := by positivity
  have hQ1b : Q1 ≤ 36 := by linarith [hq18.1, hq18.2]
  have hQ12 : Q1 ^ 2 ≤ 1296 := by
    have := pow_le_pow_left₀ hQ10 hQ1b 2
    norm_num at this
    linarith
  have hQ14 : Q1 ^ 4 ≤ 36 ^ 4 := pow_le_pow_left₀ hQ10 hQ1b 4
  have hc27 : 3 / X * (9 * X) = 27 := by field_simp; ring
  have hc27' : ∀ a : ℝ, 3 / X * (9 * X * a) = 27 * a := fun a => by field_simp; ring
  rw [hc27] at hraw
  simp only [hc27'] at hraw
  -- the rates
  have r1 : T⁻¹ ≤ ε := inv_three_pow_le_rpow n
  have r2 : 1 / Real.sqrt T ≤ ε := one_div_sqrt_three_pow_le_rpow n
  have r3 : X⁻¹ ≤ ε := inv_nine_pow_le_rpow n
  have r4 : Real.exp (-c1 * T) ≤ c1⁻¹ * ε := exp_neg_le_rpow hc1 n
  have r5 : Real.exp (-c3 * T) ≤ c3⁻¹ * ε := exp_neg_le_rpow hc3 n
  have r6 : Real.exp (-ci * T) ≤ ci⁻¹ * ε := exp_neg_le_rpow hci n
  have r7 : Real.exp (-cj * T) ≤ cj⁻¹ * ε := exp_neg_le_rpow hcj n
  have r8 : ((T - 1) ^ 2)⁻¹ ≤ 4 * X⁻¹ := inv_sq_three_pow_sub_one_le hn
  have hτ : planarMuTau p n + planarNuTau p n ≤ R := planarTau_le_weighted p n
  have hμτ0 := planarMuTau_nonneg p n
  have hντ0 := planarNuTau_nonneg p n
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  -- the terms
  have t1 : s / T ≤ 18 * ε := by
    rw [div_eq_mul_inv]
    calc s * T⁻¹ ≤ 18 * T⁻¹ := mul_le_mul_of_nonneg_right hs18 (inv_nonneg.2 hT0.le)
      _ ≤ 18 * ε := mul_le_mul_of_nonneg_left r1 (by norm_num)
  have t2 : Q1 * (CB * 1 / Real.sqrt T) ≤ 36 * CB * ε := by
    have : CB * 1 / Real.sqrt T = CB * (1 / Real.sqrt T) := by ring
    rw [this]
    calc Q1 * (CB * (1 / Real.sqrt T)) ≤ 36 * (CB * ε) :=
          mul_le_mul hQ1b (mul_le_mul_of_nonneg_left r2 hCB) (by positivity) (by norm_num)
      _ = 36 * CB * ε := by ring
  have t3 : 48 / ((T - 1) ^ 2 * X) * (CH * (1 + Q1 ^ 2) * (9 * X) * (3 * T)) ≤
      1296 * 1297 * 4 * 3 * CH * ε := by
    have e : 48 / ((T - 1) ^ 2 * X) * (CH * (1 + Q1 ^ 2) * (9 * X) * (3 * T)) =
        1296 * CH * (1 + Q1 ^ 2) * T * ((T - 1) ^ 2)⁻¹ := by field_simp; ring
    rw [e]
    have k1 : T * ((T - 1) ^ 2)⁻¹ ≤ 4 * T⁻¹ := by
      calc T * ((T - 1) ^ 2)⁻¹ ≤ T * (4 * X⁻¹) := mul_le_mul_of_nonneg_left r8 hT0.le
        _ = 4 * T⁻¹ := by rw [hXT]; field_simp
    have k2 : 1296 * CH * (1 + Q1 ^ 2) ≤ 1296 * CH * 1297 := by
      have := mul_le_mul_of_nonneg_left (show 1 + Q1 ^ 2 ≤ 1297 by linarith)
        (show 0 ≤ 1296 * CH by positivity)
      linarith
    calc 1296 * CH * (1 + Q1 ^ 2) * T * ((T - 1) ^ 2)⁻¹ =
          1296 * CH * (1 + Q1 ^ 2) * (T * ((T - 1) ^ 2)⁻¹) := by ring
      _ ≤ 1296 * CH * 1297 * (4 * T⁻¹) := mul_le_mul k2 k1 (by positivity) (by positivity)
      _ ≤ 1296 * CH * 1297 * (4 * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r1 (by norm_num)) (by positivity)
      _ = 1296 * 1297 * 4 * 3 * CH * ε / 3 := by ring
      _ ≤ _ := by
          have : 0 ≤ 1296 * 1297 * 4 * 3 * CH * ε := by positivity
          linarith
  have t4 : 96 * (9 * X) / ((T - 1) ^ 2 * X) * (Cu * (q 0 ^ 2 + q 1 ^ 2) * X * (ε + R) +
      Cv * 1 * X * (ε + R)) ≤ 3456 * (324 * Cu + Cv) * (ε + R) := by
    have e : 96 * (9 * X) / ((T - 1) ^ 2 * X) * (Cu * (q 0 ^ 2 + q 1 ^ 2) * X * (ε + R) +
        Cv * 1 * X * (ε + R)) = 864 * (Cu * (q 0 ^ 2 + q 1 ^ 2) + Cv) * (ε + R) *
          (X * ((T - 1) ^ 2)⁻¹) := by field_simp; ring
    rw [e]
    have k1 : X * ((T - 1) ^ 2)⁻¹ ≤ 4 := by
      calc X * ((T - 1) ^ 2)⁻¹ ≤ X * (4 * X⁻¹) := mul_le_mul_of_nonneg_left r8 hX0.le
        _ = 4 := by field_simp
    have k2 : Cu * (q 0 ^ 2 + q 1 ^ 2) + Cv ≤ 324 * Cu + Cv := by
      have := mul_le_mul_of_nonneg_left hq hCu
      linarith
    have k3 : 0 ≤ Cu * (q 0 ^ 2 + q 1 ^ 2) + Cv := by positivity
    calc 864 * (Cu * (q 0 ^ 2 + q 1 ^ 2) + Cv) * (ε + R) * (X * ((T - 1) ^ 2)⁻¹)
        ≤ 864 * (Cu * (q 0 ^ 2 + q 1 ^ 2) + Cv) * (ε + R) * 4 :=
          mul_le_mul_of_nonneg_left k1 (by positivity)
      _ ≤ 864 * (324 * Cu + Cv) * (ε + R) * 4 := by
          have := mul_le_mul_of_nonneg_right k2 (show 0 ≤ 864 * (ε + R) * 4 by positivity)
          linarith
      _ = 3456 * (324 * Cu + Cv) * (ε + R) := by ring
  have t5 : 3 / X * (Cμ * (Q1 ^ 2 * (9 * X) / Real.sqrt T)) ≤ 27 * 1296 * Cμ * ε := by
    have e : 3 / X * (Cμ * (Q1 ^ 2 * (9 * X) / Real.sqrt T)) =
        27 * Cμ * Q1 ^ 2 * (1 / Real.sqrt T) := by field_simp; ring
    rw [e]
    calc 27 * Cμ * Q1 ^ 2 * (1 / Real.sqrt T) ≤ 27 * Cμ * 1296 * ε :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQ12 (by positivity)) r2 (by positivity)
            (by positivity)
      _ = 27 * 1296 * Cμ * ε := by ring
  have t6 : 27 * (C1 * (Q1 ^ 2 * Real.exp (-c1 * T))) ≤ 27 * 1296 * C1 * c1⁻¹ * ε := by
    calc 27 * (C1 * (Q1 ^ 2 * Real.exp (-c1 * T))) ≤ 27 * (C1 * (1296 * (c1⁻¹ * ε))) := by
          gcongr
      _ = 27 * 1296 * C1 * c1⁻¹ * ε := by ring
  have t7 : 27 * (C3 * (1 ^ 2 * Real.exp (-c3 * T))) ≤ 27 * C3 * c3⁻¹ * ε := by
    calc 27 * (C3 * (1 ^ 2 * Real.exp (-c3 * T))) ≤ 27 * (C3 * (1 * (c3⁻¹ * ε))) := by
          gcongr
          norm_num
      _ = 27 * C3 * c3⁻¹ * ε := by ring
  have t8 : CBad * (1 + 1 ^ 2 + Q1 ^ 4) / X ≤ CBad * (2 + 36 ^ 4) * ε := by
    rw [div_eq_mul_inv]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCBad) r3
      (inv_nonneg.2 hX0.le) (by positivity)
  have t9 : 3 / X * (CG * (1 ^ 2 * (9 * X) / Real.sqrt T)) ≤ 27 * CG * ε := by
    have e : 3 / X * (CG * (1 ^ 2 * (9 * X) / Real.sqrt T)) = 27 * CG * (1 / Real.sqrt T) := by
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left r2 (by positivity)
  have tI : 27 * (planarMuMean p n q - planarMuMean p (n + 1) q) ≤
      27 * 648 * planarMuTau p n + 27 * 1296 * Ci * (1 + ci⁻¹) * ε := by
    have k : 1 / Real.sqrt T + Real.exp (-ci * T) ≤ (1 + ci⁻¹) * ε := by linarith
    have := mul_le_mul_of_nonneg_left k (show 0 ≤ Ci * 1296 by positivity)
    linarith
  have tJ : 27 * (planarNuMean p n ξ - planarNuMean p (n + 1) ξ) ≤
      54 * KA * planarNuTau p n + 27 * Cj * KB * (1 + cj⁻¹) * ε := by
    have k : 1 / Real.sqrt T + Real.exp (-cj * T) ≤ (1 + cj⁻¹) * ε := by linarith
    have := mul_le_mul_of_nonneg_left k (show 0 ≤ Cj * KB by positivity)
    linarith
  have hτR1 : 27 * 648 * planarMuTau p n + 54 * KA * planarNuTau p n ≤
      (27 * 648 + 54 * KA) * R := by
    have := mul_le_mul_of_nonneg_left hτ (show 0 ≤ 27 * 648 + 54 * KA by positivity)
    linarith [mul_nonneg hKA hμτ0, hντ0]
  have hA0 : 0 ≤ 18 + 36 * CB + 1296 * 1297 * 4 * 3 * CH + 3456 * (324 * Cu + Cv) +
      27 * 1296 * Cμ + 27 * 1296 * C1 * c1⁻¹ + 27 * C3 * c3⁻¹ + CBad * (2 + 36 ^ 4) + 27 * CG +
      27 * 1296 * Ci * (1 + ci⁻¹) + 27 * Cj * KB * (1 + cj⁻¹) := by positivity
  have hB0 : 0 ≤ 18 + 36 * CB + 1296 * 1297 * 4 * 3 * CH + 27 * 1296 * Cμ +
      27 * 1296 * C1 * c1⁻¹ + 27 * C3 * c3⁻¹ + CBad * (2 + 36 ^ 4) + 27 * CG +
      27 * 1296 * Ci * (1 + ci⁻¹) + 27 * Cj * KB * (1 + cj⁻¹) := by positivity
  have hKA' : 0 ≤ 27 * 648 + 54 * KA := by positivity
  have h1 : (18 + 36 * CB + 1296 * 1297 * 4 * 3 * CH + 3456 * (324 * Cu + Cv) +
      27 * 1296 * Cμ + 27 * 1296 * C1 * c1⁻¹ + 27 * C3 * c3⁻¹ + CBad * (2 + 36 ^ 4) + 27 * CG +
      27 * 1296 * Ci * (1 + ci⁻¹) + 27 * Cj * KB * (1 + cj⁻¹)) * ε ≤
      (18 + 36 * CB + 1296 * 1297 * 4 * 3 * CH + 3456 * (324 * Cu + Cv) +
      27 * 1296 * Cμ + 27 * 1296 * C1 * c1⁻¹ + 27 * C3 * c3⁻¹ + CBad * (2 + 36 ^ 4) + 27 * CG +
      27 * 1296 * Ci * (1 + ci⁻¹) + 27 * Cj * KB * (1 + cj⁻¹) + 27 * 648 + 54 * KA) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε0
  have h2 : (27 * 648 + 54 * KA + 3456 * (324 * Cu + Cv)) * R ≤
      (18 + 36 * CB + 1296 * 1297 * 4 * 3 * CH + 3456 * (324 * Cu + Cv) +
        27 * 1296 * Cμ + 27 * 1296 * C1 * c1⁻¹ + 27 * C3 * c3⁻¹ + CBad * (2 + 36 ^ 4) + 27 * CG +
        27 * 1296 * Ci * (1 + ci⁻¹) + 27 * Cj * KB * (1 + cj⁻¹) + 27 * 648 + 54 * KA) * R :=
    mul_le_mul_of_nonneg_right (by linarith) hR0
  have h3 : 3456 * (324 * Cu + Cv) * (ε + R) = 3456 * (324 * Cu + Cv) * ε +
      3456 * (324 * Cu + Cv) * R := by ring
  linarith

/-- The weights `3^{k-n} = (1/3)^{n-k}` for `k ≤ n`. -/
theorem inv_three_pow_mul_sum_eq (n : ℕ) (τ : ℕ → ℝ) :
    ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * τ k =
      ∑ k ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - k) * τ k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have h3 : (3 : ℝ) ^ n = 3 ^ (n - k) * 3 ^ k := by rw [← pow_add, Nat.sub_add_cancel hkn]
  rw [h3, one_div, inv_pow]
  field_simp

theorem three_rpow_neg_div_ten (n : ℕ) :
    (3 : ℝ) ^ (-(n : ℝ) / 10) = ((3 : ℝ) ^ (-(1 / 10 : ℝ))) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

set_option maxHeartbeats 400000 in
/-- The term `i` of `D_n`, from the integrated bound and the bounds of the increments. -/
theorem planarOmegaD_term_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) {n : ℕ}
    (hn2 : 1 ≤ n) {CB CH Cu Cv Cμ CBad C1 c1 C3 c3 CG Ci ci Cj cj : ℝ} (hCB : 0 ≤ CB)
    (hCH : 0 ≤ CH) (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv) (hCμ : 0 ≤ Cμ) (hCBad : 0 ≤ CBad)
    (hC1 : 0 ≤ C1) (hc1 : 0 < c1) (hC3 : 0 ≤ C3) (hc3 : 0 < c3) (hCG : 0 ≤ CG) (hCi : 0 ≤ Ci)
    (hci : 0 < ci) (hCj : 0 ≤ Cj) (hcj : 0 < cj)
    (hraw :
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
          (⟨n + 1, 0⟩ : TriadicCube 2).volume / Real.sqrt (3 ^ n))) )
    (hIμ : ∀ (k : ℕ) (q : Fin 2 → ℝ),
      planarMuIncrement p k q ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) * planarMuTau p k +
        Ci * ((|q 0| + |q 1|) ^ 2 * (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-ci * (3 : ℝ) ^ k))))
    (hJν : ∀ (k : ℕ) (q : Fin 2 → ℝ),
      planarNuIncrement p k ((planarAhom p)⁻¹ *ᵥ q) ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) * planarNuTau p k +
        Cj * ((|((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 0| +
          |((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 1|) ^ 2 *
          (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-cj * (3 : ℝ) ^ k))))
    (hinv : ∀ q : Fin 2 → ℝ, planarAhomInvFinite p n *ᵥ (planarAhomFinite p n *ᵥ q) = q)
    (hlow : ∀ q : Fin 2 → ℝ, (q 0 ^ 2 + q 1 ^ 2) / 36 ≤ planarMuMean p n q) (i : Fin 2) :
    planarNuMean p n (Pi.single i 1) + planarMuMean p n (planarAhomFinite p n *ᵥ Pi.single i 1) -
        (planarAhomFinite p n *ᵥ Pi.single i 1) i ≤
      (18 + 36 * CB + 1296 * 1297 * 4 * 3 * CH + 3456 * (324 * Cu + Cv) + 27 * 1296 * Cμ +
        27 * 1296 * C1 * c1⁻¹ + 27 * C3 * c3⁻¹ + CBad * (2 + 36 ^ 4) + 27 * CG +
        27 * 1296 * Ci * (1 + ci⁻¹) +
        27 * Cj * (∑ i : Fin 2, (|((planarAhom p)⁻¹ *ᵥ ![(planarAhom p *ᵥ Pi.single i 1) 0,
          -(planarAhom p *ᵥ Pi.single i 1) 1]) 0| +
          |((planarAhom p)⁻¹ *ᵥ ![(planarAhom p *ᵥ Pi.single i 1) 0,
            -(planarAhom p *ᵥ Pi.single i 1) 1]) 1|) ^ 2) * (1 + cj⁻¹) + 27 * 648 +
        54 * (∑ i : Fin 2, ((planarAhom p *ᵥ Pi.single i 1) 0 ^ 2 +
          (planarAhom p *ᵥ Pi.single i 1) 1 ^ 2))) *
        ((3 : ℝ) ^ (-(n : ℝ) / 10) +
          ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k) := by
  set A := planarAhom p with hA
  have hKA0 : 0 ≤ ∑ i : Fin 2, ((A *ᵥ Pi.single i 1) 0 ^ 2 + (A *ᵥ Pi.single i 1) 1 ^ 2) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hKB0 : 0 ≤ ∑ i : Fin 2, (|(A⁻¹ *ᵥ ![(A *ᵥ Pi.single i 1) 0,
      -(A *ᵥ Pi.single i 1) 1]) 0| + |(A⁻¹ *ᵥ ![(A *ᵥ Pi.single i 1) 0,
      -(A *ᵥ Pi.single i 1) 1]) 1|) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hq324 : (planarAhomFinite p n *ᵥ Pi.single i 1) 0 ^ 2 +
      (planarAhomFinite p n *ᵥ Pi.single i 1) 1 ^ 2 ≤ 324 :=
    planarAhomFinite_single_sq_le hpc hinv hlow i
  have hξ1 : |(Pi.single i 1 : Fin 2 → ℝ) 0| + |(Pi.single i 1 : Fin 2 → ℝ) 1| = 1 := by
    fin_cases i <;> simp
  have hξ2 : (Pi.single i 1 : Fin 2 → ℝ) 0 ^ 2 + (Pi.single i 1 : Fin 2 → ℝ) 1 ^ 2 = 1 := by
    fin_cases i <;> simp
  have hsi : ∑ j, (planarAhomFinite p n *ᵥ Pi.single i 1) j * (Pi.single i 1 : Fin 2 → ℝ) j =
      (planarAhomFinite p n *ᵥ Pi.single i 1) i := by
    fin_cases i <;> simp [Fin.sum_univ_two]
  have hs0 : 0 ≤ ∑ j, (planarAhomFinite p n *ᵥ Pi.single i 1) j *
      (Pi.single i 1 : Fin 2 → ℝ) j := by
    rw [hsi]; exact planarAhomFinite_single_self_nonneg hpc hinv i
  have hq18 := abs_le_of_sq_add_sq_le
    (show (planarAhomFinite p n *ᵥ Pi.single i 1) 0 ^ 2 +
      (planarAhomFinite p n *ᵥ Pi.single i 1) 1 ^ 2 ≤ 18 ^ 2 by linarith) (by norm_num)
  have hqi : (planarAhomFinite p n *ᵥ Pi.single i 1) i ≤ 18 := by
    fin_cases i
    · exact (abs_le.1 hq18.1).2
    · exact (abs_le.1 hq18.2).2
  have hs18 : ∑ j, (planarAhomFinite p n *ᵥ Pi.single i 1) j *
      (Pi.single i 1 : Fin 2 → ℝ) j ≤ 18 := by rw [hsi]; exact hqi
  have hr := hraw (Pi.single i 1) (planarAhomFinite p n *ᵥ Pi.single i 1) (by rw [hξ1]; norm_num)
    hs0 (hinv _)
  have hQ1 : (|(planarAhomFinite p n *ᵥ Pi.single i 1) 0| +
      |(planarAhomFinite p n *ᵥ Pi.single i 1) 1|) ^ 2 ≤ 1296 := by
    have h1 : |(planarAhomFinite p n *ᵥ Pi.single i 1) 0| +
        |(planarAhomFinite p n *ᵥ Pi.single i 1) 1| ≤ 36 := by linarith [hq18.1, hq18.2]
    calc _ ≤ (36 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = 1296 := by norm_num
  have hI : planarMuMean p n (planarAhomFinite p n *ᵥ Pi.single i 1) -
      planarMuMean p (n + 1) (planarAhomFinite p n *ᵥ Pi.single i 1) ≤
      2 * 324 * planarMuTau p n + Ci * 1296 * (1 / Real.sqrt ((3 : ℝ) ^ n) +
        Real.exp (-ci * (3 : ℝ) ^ n)) := by
    have h := hIμ n (planarAhomFinite p n *ᵥ Pi.single i 1)
    have hμτ := planarMuTau_nonneg p n
    have e1 := mul_le_mul_of_nonneg_right hq324 hμτ
    have hpos : 0 ≤ 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-ci * (3 : ℝ) ^ n) := by positivity
    have e2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ1 hpos) hCi
    change planarMuIncrement p n _ ≤ _
    linarith
  have hJ : planarNuMean p n (Pi.single i 1) - planarNuMean p (n + 1) (Pi.single i 1) ≤
      2 * (∑ i : Fin 2, ((A *ᵥ Pi.single i 1) 0 ^ 2 + (A *ᵥ Pi.single i 1) 1 ^ 2)) *
        planarNuTau p n +
      Cj * (∑ i : Fin 2, (|(A⁻¹ *ᵥ ![(A *ᵥ Pi.single i 1) 0,
      -(A *ᵥ Pi.single i 1) 1]) 0| + |(A⁻¹ *ᵥ ![(A *ᵥ Pi.single i 1) 0,
      -(A *ᵥ Pi.single i 1) 1]) 1|) ^ 2) * (1 / Real.sqrt ((3 : ℝ) ^ n) +
        Real.exp (-cj * (3 : ℝ) ^ n)) := by
    have hback : A⁻¹ *ᵥ (A *ᵥ Pi.single i 1) = Pi.single i 1 := ahom_inv_mulVec_ahom_mulVec hpc _
    have h := hJν n (A *ᵥ Pi.single i 1)
    rw [hback] at h
    have hντ := planarNuTau_nonneg p n
    have hKAi := Finset.single_le_sum (f := fun i : Fin 2 =>
      (A *ᵥ Pi.single i 1) 0 ^ 2 + (A *ᵥ Pi.single i 1) 1 ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ i)
    have hKBi := Finset.single_le_sum (f := fun i : Fin 2 =>
      (|(A⁻¹ *ᵥ ![(A *ᵥ Pi.single i 1) 0, -(A *ᵥ Pi.single i 1) 1]) 0| +
        |(A⁻¹ *ᵥ ![(A *ᵥ Pi.single i 1) 0, -(A *ᵥ Pi.single i 1) 1]) 1|) ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i)
    have hpos : 0 ≤ 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-cj * (3 : ℝ) ^ n) := by positivity
    have e1 := mul_le_mul_of_nonneg_right hKAi hντ
    have e2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKBi hpos) hCj
    change planarNuIncrement p n _ ≤ _
    linarith
  have harith := planarOmega_term_arith (p := p) hn2 hξ1 hξ2 hq324 hs18 hCB hCH hCu hCv hCμ
    hCBad hC1 hc1 hC3 hc3 hCG hCi hci hCj hcj hKA0 hKB0 hr hI hJ
  rw [hsi] at harith
  exact harith

/-- **Lemma 5.9 of Armstrong and Dario** (in dimension two, in the form used by Lemma 5.10): from
Lemmas 5.7 and 5.5,
`D_n ≤ K (3^{-n/10} + ∑_{k ≤ n} 3^{k-n} τ_k)` for `n ≥ N`. -/
theorem exists_planarOmegaD_le_of_inputs {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (h57 : PlanarWeakConvergence p)
    (h55μ : PlanarRestrictQuadCoarsenMu p) (h55ν : PlanarRestrictQuadCoarsenNu p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      planarOmegaD p n ≤ K * ((3 : ℝ) ^ (-(n : ℝ) / 10) +
        ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k) := by
  obtain ⟨CB, CH, Cu, Cv, Cμ, CBad, C1, c1, C3, c3, CG, hCB, hCH, hCu, hCv, hCμ, hCBad, hC1, hc1,
    hC3, hc3, hCG, N0, hraw⟩ := exists_planarOmegaD_term_raw hpc h57 h55μ h55ν
  obtain ⟨Cb0, -, N1, hN1⟩ := exists_planarAhomInvFinite_mulVec_planarAhomFinite hpc
  obtain ⟨Ci, hCi, ci, hci, hIμ⟩ := exists_planarMuIncrement_le hpc
  obtain ⟨Cj, hCj, cj, hcj, hJν⟩ := exists_planarNuIncrement_ahomInv_le hpc
  refine ⟨2 * (18 + 36 * CB + 1296 * 1297 * 4 * 3 * CH + 3456 * (324 * Cu + Cv) + 27 * 1296 * Cμ +
        27 * 1296 * C1 * c1⁻¹ + 27 * C3 * c3⁻¹ + CBad * (2 + 36 ^ 4) + 27 * CG +
        27 * 1296 * Ci * (1 + ci⁻¹) +
        27 * Cj * (∑ i : Fin 2, (|((planarAhom p)⁻¹ *ᵥ ![(planarAhom p *ᵥ Pi.single i 1) 0,
          -(planarAhom p *ᵥ Pi.single i 1) 1]) 0| +
          |((planarAhom p)⁻¹ *ᵥ ![(planarAhom p *ᵥ Pi.single i 1) 0,
            -(planarAhom p *ᵥ Pi.single i 1) 1]) 1|) ^ 2) * (1 + cj⁻¹) + 27 * 648 +
        54 * (∑ i : Fin 2, ((planarAhom p *ᵥ Pi.single i 1) 0 ^ 2 +
          (planarAhom p *ᵥ Pi.single i 1) 1 ^ 2))), ?_, max (max N0 N1) 1, fun n hn => ?_⟩
  · have hKA0 : 0 ≤ ∑ i : Fin 2, ((planarAhom p *ᵥ Pi.single i 1) 0 ^ 2 +
        (planarAhom p *ᵥ Pi.single i 1) 1 ^ 2) := Finset.sum_nonneg fun i _ => by positivity
    have hKB0 : 0 ≤ ∑ i : Fin 2, (|((planarAhom p)⁻¹ *ᵥ ![(planarAhom p *ᵥ Pi.single i 1) 0,
          -(planarAhom p *ᵥ Pi.single i 1) 1]) 0| +
          |((planarAhom p)⁻¹ *ᵥ ![(planarAhom p *ᵥ Pi.single i 1) 0,
            -(planarAhom p *ᵥ Pi.single i 1) 1]) 1|) ^ 2 := Finset.sum_nonneg fun i _ => by
      positivity
    positivity
  have hn0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hinv, -, hb⟩ := hN1 n hn1
  have h0 := planarOmegaD_term_le hpc hn2 hCB hCH hCu hCv hCμ hCBad hC1 hc1 hC3 hc3 hCG hCi hci
    hCj hcj (hraw n hn0) hIμ hJν hinv (fun q => (hb q).1) 0
  have h1 := planarOmegaD_term_le hpc hn2 hCB hCH hCu hCv hCμ hCBad hC1 hc1 hC3 hc3 hCG hCi hci
    hCj hcj (hraw n hn0) hIμ hJν hinv (fun q => (hb q).1) 1
  rw [planarOmegaD, Fin.sum_univ_two]
  linarith

/-- **Lemma 5.9 of Armstrong and Dario in the form of the hypothesis of
`planarMuLimit_eq_of_decay`** (dimension two): `D_n ≤ C σⁿ + C ∑_{l ≤ n} ρ^{n-l} τ_l` with
`σ = 3^{-1/10}` and `ρ = 1/3`. -/
theorem exists_planarOmegaD_decay {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (h57 : PlanarWeakConvergence p) (h55μ : PlanarRestrictQuadCoarsenMu p)
    (h55ν : PlanarRestrictQuadCoarsenNu p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → planarOmegaD p n ≤
      C * ((3 : ℝ) ^ (-(1 / 10 : ℝ))) ^ n +
        C * ∑ l ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - l) * planarTau p l := by
  obtain ⟨K, hK, N, h⟩ := exists_planarOmegaD_le_of_inputs hpc h57 h55μ h55ν
  refine ⟨K, hK, N, fun n hn => ?_⟩
  have := h n hn
  rw [three_rpow_neg_div_ten, inv_three_pow_mul_sum_eq] at this
  linarith

/-- **Proposition 5.2 of Armstrong and Dario, qualitative part** (dimension two), from Lemma 5.7
and Lemma 5.5: `lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q`. -/
theorem planarMuLimit_eq_of_inputs {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (h57 : PlanarWeakConvergence p) (h55μ : PlanarRestrictQuadCoarsenMu p)
    (h55ν : PlanarRestrictQuadCoarsenNu p) (q : Fin 2 → ℝ) :
    planarMuLimit p q = 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
  obtain ⟨C, hC, N, h⟩ := exists_planarOmegaD_decay hpc h57 h55μ h55ν
  have hσ0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 10 : ℝ)) := by positivity
  have hσ1 : (3 : ℝ) ^ (-(1 / 10 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact planarMuLimit_eq_of_decay hpc hC hσ0 hσ1 (by norm_num) (by norm_num) h q

end Rigidity.Percolation

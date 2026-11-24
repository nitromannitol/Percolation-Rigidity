import Rigidity.Proofs.Cluster.GeneralRestrictMoments
import Rigidity.Proofs.Cluster.PlanarRestrictQuadCoarsen
import Rigidity.Proofs.Cluster.GeneralTauIncrements

/-!
# Lemma 5.5 of Armstrong and Dario in every dimension

For `p > p_c(d)`, `d ≥ 2`, there is `C` such that for `2d ≤ n < m ≤ 2n` and every slope,

`E[N⁻¹ ∑_V ∑ᵢ (|V|⁻¹ (⟨eᵢ, ∇[u(·, □_m, q)]_𝒫⟩_V - ⟨eᵢ, ∇[u(·, V, q)]_𝒫⟩_V))²]
  ≤ C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`

(`exists_lintegral_cubeMuRestrictError_le`), and the same for the maximizers of `ν` at the slopes
`ā⁻¹ q` (`exists_lintegral_cubeNuRestrictError_le`): display (5.12) of Lemma 5.5. The proof is
that of the two-dimensional `Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenMu_of_rhPartition`:

* off the bad event `cubeRestrictBad` (with the partition `𝓡` of Definition 3.7 and the Meyers
  estimate `meyers_rh_uniform`), the quantity is at most `Λ₀ D_n(□_m)/|□_m|`
  (`cubeMuRestrictError_le_of_not_mem_cubeRestrictBad`), and Lemma 5.4
  (`exists_lintegral_cubeMuDefect_le_tau`) bounds the expectation of the right side;
* on the bad event, of probability at most `C 3^{-(4d+1)n}` (`exists_measure_cubeRestrictBad_le`
  with `scale ≤ 2n`), the Cauchy–Schwarz inequality with the measurable majorant of second moment
  `C |q|⁴ |□_m|²` (`exists_cubeMuRestrictError_majorant`) gives at most `C |q|² 3^{-n/2}`
  (`sqrt_cubeBadTerm_le`), through `Rigidity.Proofs.Cluster.lintegral_le_add_sqrt_measure`.

Armstrong and Dario state the lemma for `n ≥ (4d+1)m/(4d+2)` and every cube of `T_m`; it is stated
here for the cubes `□_m` and `2d ≤ n`, `m ≤ 2n`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
  Rigidity.Proofs.Cluster.GeneralDim
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

theorem three_rpow_neg_div_four_eq (n : ℕ) :
    (3 : ℝ) ^ (-(n : ℝ) / 4) = 1 / √(√((3 : ℝ) ^ n)) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), one_div, ← Real.rpow_neg (by norm_num)]
  congr 1
  ring

/-- The error term of the bad event:
`(C₁ Q² |U|²)^{1/2} (C₂ 3^{-(4d+1)n})^{1/2} ≤ C Q 3^{-n/4}` when `scale U ≤ 2n`. -/
theorem sqrt_cubeBadTerm_le {C₁ C₂ : ℝ≥0∞} (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞) {Q : ℝ} (hQ : 0 ≤ Q)
    {U : TriadicCube d} {n : ℕ} (hmn : U.scale ≤ 2 * n) :
    (C₁ * ENNReal.ofReal Q ^ 2 * (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) *
        (C₂ * (3⁻¹ : ℝ≥0∞) ^ ((4 * d + 1) * n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (((C₁ * C₂) ^ (1 / 2 : ℝ)).toReal * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
  have hN := card_toIntegerCube_vertices_eq_three_pow_mul U
  set N : ℝ≥0∞ := (U.toIntegerCube.vertices.card : ℝ≥0∞) with hNdef
  have h3 : N ^ 2 * (3⁻¹ : ℝ≥0∞) ^ ((4 * d + 1) * n) ≤ (3⁻¹ : ℝ≥0∞) ^ n := by
    rw [hN, ← pow_mul]
    calc (3 : ℝ≥0∞) ^ (d * U.scale * 2) * (3⁻¹) ^ ((4 * d + 1) * n) ≤ 3 ^ 0 * (3⁻¹) ^ n :=
          three_pow_mul_inv_pow_le (by nlinarith)
      _ = (3⁻¹) ^ n := by rw [pow_zero, one_mul]
  have hprod : C₁ * ENNReal.ofReal Q ^ 2 * N ^ 2 * (C₂ * (3⁻¹ : ℝ≥0∞) ^ ((4 * d + 1) * n)) ≤
      C₁ * C₂ * ENNReal.ofReal Q ^ 2 * (3⁻¹ : ℝ≥0∞) ^ n := by
    calc C₁ * ENNReal.ofReal Q ^ 2 * N ^ 2 * (C₂ * (3⁻¹ : ℝ≥0∞) ^ ((4 * d + 1) * n))
        = C₁ * C₂ * ENNReal.ofReal Q ^ 2 * (N ^ 2 * (3⁻¹ : ℝ≥0∞) ^ ((4 * d + 1) * n)) := by ring
      _ ≤ C₁ * C₂ * ENNReal.ofReal Q ^ 2 * (3⁻¹ : ℝ≥0∞) ^ n := by gcongr
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  refine (ENNReal.rpow_le_rpow hprod (by norm_num)).trans ?_
  have h3n : (3⁻¹ : ℝ≥0∞) ^ n = ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  have hQ2 : ENNReal.ofReal Q ^ 2 = ENNReal.ofReal (Q ^ 2) := (ENNReal.ofReal_pow hQ 2).symm
  have hXfin : (C₁ * C₂) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hC₁ hC₂)
  rw [mul_assoc, hQ2, h3n, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity)
      (by norm_num)]
  have hsq : (Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ))) ^ (1 / 2 : ℝ) = Q * (3 : ℝ) ^ (-(n : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast Q 2,
      ← Real.rpow_mul hQ, ← Real.rpow_mul (by norm_num),
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one,
      show -(n : ℝ) * (1 / 2) = -(n : ℝ) / 2 by ring]
  have hexp : (3 : ℝ) ^ (-(n : ℝ) / 2) ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  calc (C₁ * C₂) ^ (1 / 2 : ℝ) * ENNReal.ofReal ((Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ))) ^ (1 / 2 : ℝ))
      = ENNReal.ofReal (((C₁ * C₂) ^ (1 / 2 : ℝ)).toReal *
          (Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ))) ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hXfin]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hsq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hexp (mul_nonneg ENNReal.toReal_nonneg hQ)

theorem restrictOffBadConst_nonneg {A CM p : ℝ} (hA : 0 ≤ A) (hCM : 0 ≤ CM) :
    0 ≤ restrictOffBadConst d A CM p := by
  unfold restrictOffBadConst
  have := Real.rpow_nonneg hCM (1 / p)
  positivity

/-- **Lemma 5.5 of Armstrong and Dario for `μ`** (display (5.12), first term, every dimension
`d ≥ 2`, `p > p_c(d)`): for `2d ≤ n < m ≤ 2n`,
`E[cubeMuRestrictError(□_m, n, q)] ≤ C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`.
Armstrong and Dario print `∑_{k=n}^{m+1}`; the sum over `[n, m)` is the stronger form given by the
proof, since `τ_k ≥ 0`. -/
theorem exists_lintegral_cubeMuRestrictError_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ) (q : Fin d → ℝ), 2 * d ≤ n → n < m → m ≤ 2 * n →
      ∫⁻ ω, ENNReal.ofReal (cubeMuRestrictError ω ⟨m, 0⟩ n q) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, q i ^ 2) *
          (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n)))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨A₀, s, has, hpack⟩ := exists_measure_cubeRestrictBad_le hd hpc
  obtain ⟨ε, hε, t, ht, hMU⟩ := meyers_rh_uniform (d := d) (by omega) A₀
  have hp1 : 1 < 1 + ε / 2 := by linarith
  have hpq : (1 + ε / 2).HolderConjugate (1 + ε / 2).conjExponent :=
    Real.HolderConjugate.conjExponent hp1
  set r := (1 + ε / 2).conjExponent with hr
  set τ : ℕ := ⌈((2 * d - 1 : ℕ) : ℝ) * r⌉₊ with hτ
  have hτr : ((2 * d - 1 : ℕ) : ℝ) * r ≤ τ := Nat.le_ceil _
  obtain ⟨Aτ, hAτ, htK⟩ := hpack τ
  obtain ⟨K, hK, hMβ⟩ := htK t ht
  obtain ⟨CM, hCM, hMey⟩ := hMU K hK
  obtain ⟨Cb, hCb, hbad⟩ := hMβ 2 (4 * d + 1)
  obtain ⟨CD, hCD, hdef⟩ := exists_lintegral_cubeMuDefect_le_tau hd hpc
  obtain ⟨Cmj, hCmj, hmaj⟩ := exists_cubeMuRestrictError_majorant hd hpc
  set Λ₀ := restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) with hΛ₀def
  have hΛ₀ : 0 ≤ Λ₀ := restrictOffBadConst_nonneg (Real.rpow_nonneg hAτ _) hCM
  set Ccs : ℝ := ((Cmj * Cb) ^ (1 / 2 : ℝ)).toReal with hCcs
  have hCcs0 : 0 ≤ Ccs := ENNReal.toReal_nonneg
  have hae := (ae_partitionEvent hd hpc).and has
  refine ⟨Λ₀ * CD + Ccs, by positivity, fun n m q hn hnm hmn => ?_⟩
  set U : TriadicCube d := ⟨m, 0⟩ with hU
  have hUs : U.scale = m := rfl
  obtain ⟨M, hMm, hMle, hM2⟩ := hmaj U n hnm.le q
  set P := ∑ i, q i ^ 2 with hPdef
  set T := ∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n)) with hTdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hT1 : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ T := by
    rw [three_rpow_neg_div_four_eq]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => cubeTau_nonneg p k)
  have hT0 : 0 ≤ T := le_trans (by positivity) hT1
  have hvol := U.latticeVolume_pos
  set g : Configuration d → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Λ₀ * (cubeMuDefect ω U n q / U.latticeVolume)) with hgdef
  have hgood : ∀ᵐ ω ∂(latticeBondLaw d p), ω ∉ cubeRestrictBad s t K τ Aτ U n →
      ENNReal.ofReal (cubeMuRestrictError ω U n q) ≤ g ω := by
    filter_upwards [hae] with ω ⟨hP, hs⟩ hω
    exact ENNReal.ofReal_le_ofReal (cubeMuRestrictError_le_of_not_mem_cubeRestrictBad hd0 hpq hτr
      hCM hAτ hMey hP hs hn hnm hω q)
  have hsplit := lintegral_le_add_sqrt_measure (latticeBondLaw d p)
    (fun ω => ENNReal.ofReal (cubeMuRestrictError ω U n q)) g M
    (cubeRestrictBad s t K τ Aτ U n) hMm hgood hMle
  refine hsplit.trans ?_
  have h1 : ∫⁻ ω, g ω ∂(latticeBondLaw d p) ≤ ENNReal.ofReal (Λ₀ * CD * P * T) := by
    have hpt : ∀ ω, g ω = ENNReal.ofReal (Λ₀ / U.latticeVolume) *
        ENNReal.ofReal (cubeMuDefect ω U n q) := fun ω => by
      simp only [hgdef]
      rw [← ENNReal.ofReal_mul (div_nonneg hΛ₀ hvol.le)]
      congr 1
      ring
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Λ₀ / U.latticeVolume) *
          ∫⁻ ω, ENNReal.ofReal (cubeMuDefect ω U n q) ∂(latticeBondLaw d p)
        ≤ ENNReal.ofReal (Λ₀ / U.latticeVolume) *
            ENNReal.ofReal (U.latticeVolume * (CD * P * T)) :=
          mul_le_mul_of_nonneg_left (hdef n m q hnm.le) zero_le
      _ = ENNReal.ofReal (Λ₀ * CD * P * T) := by
          rw [← ENNReal.ofReal_mul (div_nonneg hΛ₀ hvol.le)]
          congr 1
          field_simp
  have h2 : (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)) ^ (1 / 2 : ℝ) *
      (latticeBondLaw d p) (cubeRestrictBad s t K τ Aτ U n) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Ccs * P * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
    refine le_trans ?_ (sqrt_cubeBadTerm_le hCmj hCb hP0 (by rw [hUs]; exact hmn))
    exact mul_le_mul' (ENNReal.rpow_le_rpow hM2 (by norm_num))
      (ENNReal.rpow_le_rpow (hbad U n hn hnm hmn) (by norm_num))
  calc ∫⁻ ω, g ω ∂(latticeBondLaw d p) + (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)) ^ (1 / 2 : ℝ) *
        (latticeBondLaw d p) (cubeRestrictBad s t K τ Aτ U n) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Λ₀ * CD * P * T) + ENNReal.ofReal (Ccs * P * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (Λ₀ * CD * P * T + Ccs * P * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((Λ₀ * CD + Ccs) * P * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : Ccs * P * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ Ccs * P * T :=
          mul_le_mul_of_nonneg_left hT1 (by positivity)
        nlinarith

/-- **Lemma 5.5 of Armstrong and Dario for `ν`** (display (5.12), second term, every dimension
`d ≥ 2`, `p > p_c(d)`, at the slopes `ā⁻¹ q`): for `2d ≤ n < m ≤ 2n`,
`E[cubeNuRestrictError(□_m, n, ā⁻¹ q)] ≤ C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`.
Armstrong and Dario print `∑_{k=n}^{m+1}`; the sum over `[n, m)` is the stronger form given by the
proof, since `τ_k ≥ 0`. -/
theorem exists_lintegral_cubeNuRestrictError_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ) (q : Fin d → ℝ), 2 * d ≤ n → n < m → m ≤ 2 * n →
      ∫⁻ ω, ENNReal.ofReal (cubeNuRestrictError ω ⟨m, 0⟩ n ((cubeAhom p)⁻¹ *ᵥ q))
          ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, q i ^ 2) *
          (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n)))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨A₀, s, has, hpack⟩ := exists_measure_cubeRestrictBad_le hd hpc
  obtain ⟨ε, hε, t, ht, hMU⟩ := meyers_rh_uniform (d := d) (by omega) A₀
  have hp1 : 1 < 1 + ε / 2 := by linarith
  have hpq : (1 + ε / 2).HolderConjugate (1 + ε / 2).conjExponent :=
    Real.HolderConjugate.conjExponent hp1
  set r := (1 + ε / 2).conjExponent with hr
  set τ : ℕ := ⌈((2 * d - 1 : ℕ) : ℝ) * r⌉₊ with hτ
  have hτr : ((2 * d - 1 : ℕ) : ℝ) * r ≤ τ := Nat.le_ceil _
  obtain ⟨Aτ, hAτ, htK⟩ := hpack τ
  obtain ⟨K, hK, hMβ⟩ := htK t ht
  obtain ⟨CM, hCM, hMey⟩ := hMU K hK
  obtain ⟨Cb, hCb, hbad⟩ := hMβ 2 (4 * d + 1)
  obtain ⟨CD, hCD, hdef⟩ := exists_lintegral_cubeNuDefect_le_tau hd hpc
  obtain ⟨Cmj, hCmj, hmaj⟩ := exists_cubeNuRestrictError_majorant hd hpc
  set B := (cubeAhom (d := d) p)⁻¹ with hB
  set SB := ∑ i, ∑ j, |B i j| with hSB
  have hSB0 : 0 ≤ SB := by positivity
  set Λ₀ := restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) with hΛ₀def
  have hΛ₀ : 0 ≤ Λ₀ := restrictOffBadConst_nonneg (Real.rpow_nonneg hAτ _) hCM
  set Ccs : ℝ := ((Cmj * Cb) ^ (1 / 2 : ℝ)).toReal with hCcs
  have hCcs0 : 0 ≤ Ccs := ENNReal.toReal_nonneg
  have hae := (ae_partitionEvent hd hpc).and has
  refine ⟨Λ₀ * CD + Ccs * (SB ^ 2 * d), by positivity, fun n m q hn hnm hmn => ?_⟩
  set U : TriadicCube d := ⟨m, 0⟩ with hU
  have hUs : U.scale = m := rfl
  set ξ := B *ᵥ q with hξ
  obtain ⟨M, hMm, hMle, hM2⟩ := hmaj U n hnm.le ξ
  set P := ∑ i, q i ^ 2 with hPdef
  set Q := (∑ i, |ξ i|) ^ 2 with hQdef
  set T := ∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n)) with hTdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hQ0 : 0 ≤ Q := sq_nonneg _
  have hQP : Q ≤ SB ^ 2 * d * P := by
    have h1 := sum_abs_mulVec_le B q
    have h2 := sq_sum_abs_le_card_mul q
    have h3 : (0 : ℝ) ≤ ∑ i, |ξ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h4 : Q ≤ (SB * ∑ i, |q i|) ^ 2 := pow_le_pow_left₀ h3 h1 2
    calc Q ≤ (SB * ∑ i, |q i|) ^ 2 := h4
      _ = SB ^ 2 * (∑ i, |q i|) ^ 2 := by ring
      _ ≤ SB ^ 2 * (d * P) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = SB ^ 2 * d * P := by ring
  have hT1 : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ T := by
    rw [three_rpow_neg_div_four_eq]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => cubeTau_nonneg p k)
  have hT0 : 0 ≤ T := le_trans (by positivity) hT1
  have hvol := U.latticeVolume_pos
  set g : Configuration d → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Λ₀ * (cubeNuDefect ω U n ξ / U.latticeVolume)) with hgdef
  have hgood : ∀ᵐ ω ∂(latticeBondLaw d p), ω ∉ cubeRestrictBad s t K τ Aτ U n →
      ENNReal.ofReal (cubeNuRestrictError ω U n ξ) ≤ g ω := by
    filter_upwards [hae] with ω ⟨hP, hs⟩ hω
    exact ENNReal.ofReal_le_ofReal (cubeNuRestrictError_le_of_not_mem_cubeRestrictBad hd0 hpq hτr
      hCM hAτ hMey hP hs hn hnm hω ξ)
  have hsplit := lintegral_le_add_sqrt_measure (latticeBondLaw d p)
    (fun ω => ENNReal.ofReal (cubeNuRestrictError ω U n ξ)) g M
    (cubeRestrictBad s t K τ Aτ U n) hMm hgood hMle
  refine hsplit.trans ?_
  have h1 : ∫⁻ ω, g ω ∂(latticeBondLaw d p) ≤ ENNReal.ofReal (Λ₀ * CD * P * T) := by
    have hpt : ∀ ω, g ω = ENNReal.ofReal (Λ₀ / U.latticeVolume) *
        ENNReal.ofReal (cubeNuDefect ω U n ξ) := fun ω => by
      simp only [hgdef]
      rw [← ENNReal.ofReal_mul (div_nonneg hΛ₀ hvol.le)]
      congr 1
      ring
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Λ₀ / U.latticeVolume) *
          ∫⁻ ω, ENNReal.ofReal (cubeNuDefect ω U n ξ) ∂(latticeBondLaw d p)
        ≤ ENNReal.ofReal (Λ₀ / U.latticeVolume) *
            ENNReal.ofReal (U.latticeVolume * (CD * P * T)) :=
          mul_le_mul_of_nonneg_left (hdef n m q hnm.le) zero_le
      _ = ENNReal.ofReal (Λ₀ * CD * P * T) := by
          rw [← ENNReal.ofReal_mul (div_nonneg hΛ₀ hvol.le)]
          congr 1
          field_simp
  have h2 : (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)) ^ (1 / 2 : ℝ) *
      (latticeBondLaw d p) (cubeRestrictBad s t K τ Aτ U n) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
    refine le_trans ?_ (sqrt_cubeBadTerm_le hCmj hCb hQ0 (by rw [hUs]; exact hmn))
    exact mul_le_mul' (ENNReal.rpow_le_rpow hM2 (by norm_num))
      (ENNReal.rpow_le_rpow (hbad U n hn hnm hmn) (by norm_num))
  calc ∫⁻ ω, g ω ∂(latticeBondLaw d p) + (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)) ^ (1 / 2 : ℝ) *
        (latticeBondLaw d p) (cubeRestrictBad s t K τ Aτ U n) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Λ₀ * CD * P * T) + ENNReal.ofReal (Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (Λ₀ * CD * P * T + Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((Λ₀ * CD + Ccs * (SB ^ 2 * d)) * P * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ Ccs * (SB ^ 2 * d * P) * T :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQP hCcs0) hT1 (by positivity) (by positivity)
        nlinarith

end Rigidity.Percolation

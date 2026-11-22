import Rigidity.Proofs.Cluster.PlanarRestrictQuadGood
import Rigidity.Proofs.Percolation.PlanarDefectTauCube
import Rigidity.Proofs.Percolation.PlanarNuDefectTauCube

/-!
# Lemma 5.5 of Armstrong and Dario in dimension two

The inputs `PlanarRestrictQuadCoarsenMu` and `PlanarRestrictQuadCoarsenNu` (display (5.12) of
Lemma 5.5 for the minimizers of `μ` and the maximizers of `ν`) are
proved from the two probabilistic statements `PlanarGehringPartition` (the partition `𝓡` of
Definition 3.7 of Armstrong and Dario with its minimal scales) and `PlanarReachConcentration` (the
averages of the powers of the reach of the planar partition), following the proof of Armstrong
and Dario with the repaired Step 3:
* the Meyers estimate with the exponents chosen before the moment bound
  (`planar_meyers_clusterHarmonic_uniform`) gives the Meyers estimate on the cells of scale
  `⌊n/2⌋ - 1` off the bad event;
* off the bad event the quantity is at most `Λ₀ D_n(U, q)/|U|`
  (`planarMuRestrictError_le_of_not_mem_restrictBad`), and Lemma 5.4 on every triadic cube
  (`exists_lintegral_planarMuDefect_le_tau`) bounds the expectation of the right side by
  `C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`;
* on the bad event, of probability at most `C 3^{-4n}` (`measure_restrictBad_le`), the
  Cauchy–Schwarz inequality with the measurable majorant of second moment `C |q|₁⁴ |U|^{2/3}`
  (`exists_planarMuRestrictError_majorant`) gives at most `C |q|² 3^{-n/2}`;
* the measurability is `measurable_planarMuRestrictError`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- **Splitting an expectation into a good and a bad event.** If `f ≤ g` off `B` and `f ≤ M`
everywhere with `M` measurable, then `∫ f ≤ ∫ g + (∫ M²)^{1/2} μ(B)^{1/2}`. -/
theorem lintegral_le_add_sqrt_measure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g M : Ω → ℝ≥0∞) (B : Set Ω) (hM : Measurable M)
    (hgood : ∀ᵐ ω ∂μ, ω ∉ B → f ω ≤ g ω) (hmaj : ∀ᵐ ω ∂μ, f ω ≤ M ω) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, g ω ∂μ + (∫⁻ ω, M ω ^ 2 ∂μ) ^ (1 / 2 : ℝ) * μ B ^ (1 / 2 : ℝ) := by
  set B' := toMeasurable μ B with hB'def
  have hB' : MeasurableSet B' := measurableSet_toMeasurable μ B
  have hBB' : B ⊆ B' := subset_toMeasurable μ B
  have hμB : μ B' = μ B := measure_toMeasurable B
  have hpt : ∀ᵐ ω ∂μ, f ω ≤ g ω + B'.indicator M ω := by
    filter_upwards [hgood, hmaj] with ω h1 h2
    by_cases hω : ω ∈ B'
    · rw [Set.indicator_of_mem hω]
      exact h2.trans le_add_self
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact h1 fun h => hω (hBB' h)
  have hind : ∀ ω, B'.indicator M ω = M ω * B'.indicator 1 ω := fun ω => by
    by_cases hω : ω ∈ B'
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
  have hsq : ∀ ω, B'.indicator (1 : Ω → ℝ≥0∞) ω ^ (2 : ℝ) = B'.indicator 1 ω := fun ω => by
    by_cases hω : ω ∈ B'
    · rw [Set.indicator_of_mem hω, Pi.one_apply, ENNReal.one_rpow]
    · rw [Set.indicator_of_notMem hω, ENNReal.zero_rpow_of_pos (by norm_num)]
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hM.aemeasurable
    ((measurable_one.indicator hB').aemeasurable (μ := μ))
  simp only [Pi.mul_apply, hsq, ENNReal.rpow_two] at hCS
  rw [lintegral_indicator_one hB', hμB] at hCS
  calc ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, (g ω + B'.indicator M ω) ∂μ := lintegral_mono_ae hpt
    _ = ∫⁻ ω, g ω ∂μ + ∫⁻ ω, B'.indicator M ω ∂μ := lintegral_add_right _ (hM.indicator hB')
    _ ≤ ∫⁻ ω, g ω ∂μ + (∫⁻ ω, M ω ^ 2 ∂μ) ^ (1 / 2 : ℝ) * μ B ^ (1 / 2 : ℝ) := by
        refine add_le_add le_rfl ?_
        simp only [hind]
        exact hCS

/-- The error term of the bad event: `(C₁ Q² |U|^{2/3})^{1/2} (C₂ 3^{-4n})^{1/2} ≤ C Q 3^{-n/4}`
when `9 scale U ≤ 10 n`. -/
theorem sqrt_badTerm_le {C₁ C₂ : ℝ≥0∞} (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞) {Q : ℝ} (hQ : 0 ≤ Q)
    {U : TriadicCube 2} {n : ℕ} (hmn : 9 * U.scale ≤ 10 * n) :
    (C₁ * ENNReal.ofReal Q ^ 2 * (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (2 / 3 : ℝ)) ^
        (1 / 2 : ℝ) * (C₂ * (3⁻¹ : ℝ≥0∞) ^ (4 * n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (((C₁ * C₂) ^ (1 / 2 : ℝ)).toReal * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
  have hN := card_toIntegerCube_vertices_eq_three_pow U
  set N : ℝ≥0∞ := (U.toIntegerCube.vertices.card : ℝ≥0∞) with hNdef
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact one_le_pow₀ (by norm_num)
  have hN23 : N ^ (2 / 3 : ℝ) ≤ N := by
    calc N ^ (2 / 3 : ℝ) ≤ N ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := ENNReal.rpow_one N
  have h3 : N * (3⁻¹ : ℝ≥0∞) ^ (4 * n) ≤ (3⁻¹ : ℝ≥0∞) ^ n := by
    rw [hN]
    calc (3 : ℝ≥0∞) ^ (2 * U.scale) * (3⁻¹) ^ (4 * n) ≤ 3 ^ 0 * (3⁻¹) ^ n :=
          three_pow_mul_inv_pow_le (by omega)
      _ = (3⁻¹) ^ n := by rw [pow_zero, one_mul]
  have hprod : C₁ * ENNReal.ofReal Q ^ 2 * N ^ (2 / 3 : ℝ) * (C₂ * (3⁻¹ : ℝ≥0∞) ^ (4 * n)) ≤
      C₁ * C₂ * ENNReal.ofReal Q ^ 2 * (3⁻¹ : ℝ≥0∞) ^ n := by
    calc C₁ * ENNReal.ofReal Q ^ 2 * N ^ (2 / 3 : ℝ) * (C₂ * (3⁻¹ : ℝ≥0∞) ^ (4 * n))
        ≤ C₁ * ENNReal.ofReal Q ^ 2 * N * (C₂ * (3⁻¹ : ℝ≥0∞) ^ (4 * n)) := by gcongr
      _ = C₁ * C₂ * ENNReal.ofReal Q ^ 2 * (N * (3⁻¹ : ℝ≥0∞) ^ (4 * n)) := by ring
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

/-- Off the bad event, the cube is resolved. -/
theorem planarResolved_of_not_mem_restrictBad {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {s : Configuration 2 → Vertex 2 → ℕ} {t K : ℝ} {τ : ℕ} {Aτ A₂ : ℝ} {U : TriadicCube 2}
    {n : ℕ} (hnm : n < U.scale) (h : ω ∉ restrictBad s t K τ Aτ A₂ U n) :
    PlanarResolved ω U := by
  simp only [restrictBad, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or,
    not_exists, not_and, not_lt] at h
  obtain ⟨⟨hE2, -⟩, -⟩ := h
  intro z hz
  exact (hE2 hP z ((U.mem_toIntegerCube_vertices z).2 hz)).trans (by omega)

/-- **Lemma 5.5 of Armstrong and Dario for `μ`** (display (5.12), first term, in dimension two),
from the partition `𝓡` for the reverse Hölder inequality with its minimal scales and the
concentration of the averages of the reach. -/
theorem planarRestrictQuadCoarsenMu_of_inputs {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p)
    (hR : PlanarReachConcentration p) : PlanarRestrictQuadCoarsenMu p := by
  obtain ⟨CG, hCG, s, has, hmin⟩ := hG
  obtain ⟨ε, hε, t, ht, hMU⟩ := planar_meyers_clusterHarmonic_uniform hCG
  obtain ⟨K, hK, hKB⟩ := hmin t ht
  obtain ⟨CM, hCM, hMey⟩ := hMU K hK
  have hp1 : 1 < 1 + ε / 2 := by linarith
  have hpq : (1 + ε / 2).HolderConjugate (1 + ε / 2).conjExponent :=
    Real.HolderConjugate.conjExponent hp1
  set r := (1 + ε / 2).conjExponent with hr
  set τ : ℕ := ⌈3 * r⌉₊ with hτ
  have hτr : 3 * r ≤ τ := Nat.le_ceil _
  obtain ⟨Aτ, hAτ, hAτB⟩ := hR τ
  obtain ⟨A₂, hA₂, hA₂B⟩ := hR 2
  obtain ⟨Cτ, hCτ, hτ14⟩ := hAτB 14
  obtain ⟨C₂, hC₂, h260⟩ := hA₂B 60
  obtain ⟨Cg, hCg, hg14⟩ := hKB 14
  obtain ⟨Cs, hCs, hscale⟩ := exists_measure_partitionScale_gt_le hpc 20
  obtain ⟨Cb, hCb, hbad⟩ := measure_restrictBad_le (latticeBondLaw 2 p) s hCs hscale hC₂ hCτ hCg
    h260 hτ14 hg14
  obtain ⟨CD, hCD, hdef⟩ := exists_lintegral_planarMuDefect_le_tau hpc
  obtain ⟨Cmj, hCmj, hmaj⟩ := exists_planarMuRestrictError_majorant hpc
  set Λ₀ := restrictConst Aτ r CM (1 + ε / 2) A₂ with hΛ₀def
  have hΛ₀ : 0 ≤ Λ₀ := restrictConst_nonneg hAτ hCM
  set Ccs : ℝ := ((Cmj * Cb) ^ (1 / 2 : ℝ)).toReal with hCcs
  have hCcs0 : 0 ≤ Ccs := ENNReal.toReal_nonneg
  have hae := (ae_planarPartitionEvent hpc).and (has.and (ae_planarReach_ne_top hpc))
  refine ⟨Λ₀ * CD + 2 * Ccs, by positivity, fun U n hmn hnm q =>
    ⟨(measurable_planarMuRestrictError U hnm.le q).aemeasurable, ?_⟩⟩
  obtain ⟨M, hMm, hMle, hM2⟩ := hmaj U n hnm.le q
  set P := q 0 ^ 2 + q 1 ^ 2 with hPdef
  set Q := (|q 0| + |q 1|) ^ 2 with hQdef
  set T := ∑ k ∈ Finset.Ico n U.scale, planarTau p k + (3 : ℝ) ^ (-(n : ℝ) / 4) with hTdef
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hQP : Q ≤ 2 * P := abs_add_abs_sq_le q
  have hT1 : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ T :=
    le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => planarTau_nonneg p k)
  have hT0 : 0 ≤ T := le_trans (by positivity) hT1
  have hvol := U.volume_pos
  set g : Configuration 2 → ℝ≥0∞ := fun ω =>
    if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (Λ₀ * (planarMuDefect ω U n q / U.volume)) else 0 with hgdef
  have hgood : ∀ᵐ ω ∂(latticeBondLaw 2 p), ω ∉ restrictBad s t K τ Aτ A₂ U n →
      ENNReal.ofReal (planarMuRestrictError ω U n q) ≤ g ω := by
    filter_upwards [hae] with ω ⟨hP, hs, hfin⟩ hω
    have h := planarMuRestrictError_le_of_not_mem_restrictBad hpq hτr hCM hAτ hA₂ hMey hP hs
      hfin hmn hnm hω q
    have hU := planarResolved_of_not_mem_restrictBad hP hnm hω
    simp only [hgdef, if_pos (show PlanarPartitionEvent ω ∧ PlanarResolved ω U from ⟨hP, hU⟩)]
    exact ENNReal.ofReal_le_ofReal h
  have hsplit := lintegral_le_add_sqrt_measure (latticeBondLaw 2 p)
    (fun ω => ENNReal.ofReal (planarMuRestrictError ω U n q)) g M
    (restrictBad s t K τ Aτ A₂ U n) hMm hgood (ae_of_all _ hMle)
  refine hsplit.trans ?_
  have h1 : ∫⁻ ω, g ω ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal (Λ₀ * CD * P * T) := by
    have hpt : ∀ ω, g ω = ENNReal.ofReal (Λ₀ / U.volume) *
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMuDefect ω U n q) else 0) := fun ω => by
      simp only [hgdef]
      split_ifs
      · rw [← ENNReal.ofReal_mul (div_nonneg hΛ₀ hvol.le)]
        congr 1
        ring
      · rw [mul_zero]
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Λ₀ / U.volume) * ∫⁻ ω, (if PlanarPartitionEvent ω ∧
          PlanarResolved ω U then ENNReal.ofReal (planarMuDefect ω U n q) else 0)
          ∂(latticeBondLaw 2 p)
        ≤ ENNReal.ofReal (Λ₀ / U.volume) * ENNReal.ofReal (U.volume * (CD * P * T)) :=
          mul_le_mul_of_nonneg_left (hdef U n hnm.le q) zero_le
      _ = ENNReal.ofReal (Λ₀ * CD * P * T) := by
          rw [← ENNReal.ofReal_mul (div_nonneg hΛ₀ hvol.le)]
          congr 1
          field_simp
  have h2 : (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw 2 p)) ^ (1 / 2 : ℝ) *
      (latticeBondLaw 2 p) (restrictBad s t K τ Aτ A₂ U n) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
    refine le_trans ?_ (sqrt_badTerm_le hCmj hCb hQ0 hmn)
    exact mul_le_mul' (ENNReal.rpow_le_rpow hM2 (by norm_num))
      (ENNReal.rpow_le_rpow (hbad U n hmn hnm) (by norm_num))
  calc ∫⁻ ω, g ω ∂(latticeBondLaw 2 p) + (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw 2 p)) ^ (1 / 2 : ℝ) *
        (latticeBondLaw 2 p) (restrictBad s t K τ Aτ A₂ U n) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Λ₀ * CD * P * T) + ENNReal.ofReal (Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (Λ₀ * CD * P * T + Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((Λ₀ * CD + 2 * Ccs) * P * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ Ccs * (2 * P) * T :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQP hCcs0) hT1 (by positivity) (by positivity)
        nlinarith

/-- **Lemma 5.5 of Armstrong and Dario for `ν`** (display (5.12), second term, in dimension two),
from the partition `𝓡` for the reverse Hölder inequality with its minimal scales and the
concentration of the averages of the reach. -/
theorem planarRestrictQuadCoarsenNu_of_inputs {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p)
    (hR : PlanarReachConcentration p) : PlanarRestrictQuadCoarsenNu p := by
  obtain ⟨CG, hCG, s, has, hmin⟩ := hG
  obtain ⟨ε, hε, t, ht, hMU⟩ := planar_meyers_clusterHarmonic_uniform hCG
  obtain ⟨K, hK, hKB⟩ := hmin t ht
  obtain ⟨CM, hCM, hMey⟩ := hMU K hK
  have hp1 : 1 < 1 + ε / 2 := by linarith
  have hpq : (1 + ε / 2).HolderConjugate (1 + ε / 2).conjExponent :=
    Real.HolderConjugate.conjExponent hp1
  set r := (1 + ε / 2).conjExponent with hr
  set τ : ℕ := ⌈3 * r⌉₊ with hτ
  have hτr : 3 * r ≤ τ := Nat.le_ceil _
  obtain ⟨Aτ, hAτ, hAτB⟩ := hR τ
  obtain ⟨A₂, hA₂, hA₂B⟩ := hR 2
  obtain ⟨Cτ, hCτ, hτ14⟩ := hAτB 14
  obtain ⟨C₂, hC₂, h260⟩ := hA₂B 60
  obtain ⟨Cg, hCg, hg14⟩ := hKB 14
  obtain ⟨Cs, hCs, hscale⟩ := exists_measure_partitionScale_gt_le hpc 20
  obtain ⟨Cb, hCb, hbad⟩ := measure_restrictBad_le (latticeBondLaw 2 p) s hCs hscale hC₂ hCτ hCg
    h260 hτ14 hg14
  obtain ⟨CD, hCD, hdef⟩ := exists_lintegral_planarNuDefect_le_tau hpc
  obtain ⟨Cmj, hCmj, hmaj⟩ := exists_planarNuRestrictError_majorant hpc
  set Λ₀ := restrictConst Aτ r CM (1 + ε / 2) A₂ with hΛ₀def
  have hΛ₀ : 0 ≤ Λ₀ := restrictConst_nonneg hAτ hCM
  set Ccs : ℝ := ((Cmj * Cb) ^ (1 / 2 : ℝ)).toReal with hCcs
  have hCcs0 : 0 ≤ Ccs := ENNReal.toReal_nonneg
  have hae := (ae_planarPartitionEvent hpc).and (has.and (ae_planarReach_ne_top hpc))
  refine ⟨Λ₀ * CD + 2 * Ccs, by positivity, fun U n hmn hnm q =>
    ⟨(measurable_planarNuRestrictError U hnm.le q).aemeasurable, ?_⟩⟩
  obtain ⟨M, hMm, hMle, hM2⟩ := hmaj U n hnm.le q
  set P := q 0 ^ 2 + q 1 ^ 2 with hPdef
  set Q := (|q 0| + |q 1|) ^ 2 with hQdef
  set T := ∑ k ∈ Finset.Ico n U.scale, planarTau p k + (3 : ℝ) ^ (-(n : ℝ) / 4) with hTdef
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hQP : Q ≤ 2 * P := abs_add_abs_sq_le q
  have hT1 : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ T :=
    le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => planarTau_nonneg p k)
  have hT0 : 0 ≤ T := le_trans (by positivity) hT1
  have hvol := U.volume_pos
  set g : Configuration 2 → ℝ≥0∞ := fun ω =>
    if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (Λ₀ * (planarNuDefect ω U n q / U.volume)) else 0 with hgdef
  have hgood : ∀ᵐ ω ∂(latticeBondLaw 2 p), ω ∉ restrictBad s t K τ Aτ A₂ U n →
      ENNReal.ofReal (planarNuRestrictError ω U n q) ≤ g ω := by
    filter_upwards [hae] with ω ⟨hP, hs, hfin⟩ hω
    have h := planarNuRestrictError_le_of_not_mem_restrictBad hpq hτr hCM hAτ hA₂ hMey hP hs
      hfin hmn hnm hω q
    have hU := planarResolved_of_not_mem_restrictBad hP hnm hω
    simp only [hgdef, if_pos (show PlanarPartitionEvent ω ∧ PlanarResolved ω U from ⟨hP, hU⟩)]
    exact ENNReal.ofReal_le_ofReal h
  have hsplit := lintegral_le_add_sqrt_measure (latticeBondLaw 2 p)
    (fun ω => ENNReal.ofReal (planarNuRestrictError ω U n q)) g M
    (restrictBad s t K τ Aτ A₂ U n) hMm hgood (ae_of_all _ hMle)
  refine hsplit.trans ?_
  have h1 : ∫⁻ ω, g ω ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal (Λ₀ * CD * P * T) := by
    have hpt : ∀ ω, g ω = ENNReal.ofReal (Λ₀ / U.volume) *
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNuDefect ω U n q) else 0) := fun ω => by
      simp only [hgdef]
      split_ifs
      · rw [← ENNReal.ofReal_mul (div_nonneg hΛ₀ hvol.le)]
        congr 1
        ring
      · rw [mul_zero]
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Λ₀ / U.volume) * ∫⁻ ω, (if PlanarPartitionEvent ω ∧
          PlanarResolved ω U then ENNReal.ofReal (planarNuDefect ω U n q) else 0)
          ∂(latticeBondLaw 2 p)
        ≤ ENNReal.ofReal (Λ₀ / U.volume) * ENNReal.ofReal (U.volume * (CD * P * T)) :=
          mul_le_mul_of_nonneg_left (hdef U n hnm.le q) zero_le
      _ = ENNReal.ofReal (Λ₀ * CD * P * T) := by
          rw [← ENNReal.ofReal_mul (div_nonneg hΛ₀ hvol.le)]
          congr 1
          field_simp
  have h2 : (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw 2 p)) ^ (1 / 2 : ℝ) *
      (latticeBondLaw 2 p) (restrictBad s t K τ Aτ A₂ U n) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
    refine le_trans ?_ (sqrt_badTerm_le hCmj hCb hQ0 hmn)
    exact mul_le_mul' (ENNReal.rpow_le_rpow hM2 (by norm_num))
      (ENNReal.rpow_le_rpow (hbad U n hmn hnm) (by norm_num))
  calc ∫⁻ ω, g ω ∂(latticeBondLaw 2 p) + (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw 2 p)) ^ (1 / 2 : ℝ) *
        (latticeBondLaw 2 p) (restrictBad s t K τ Aτ A₂ U n) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Λ₀ * CD * P * T) + ENNReal.ofReal (Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (Λ₀ * CD * P * T + Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((Λ₀ * CD + 2 * Ccs) * P * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ Ccs * (2 * P) * T :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQP hCcs0) hT1 (by positivity) (by positivity)
        nlinarith

end Rigidity.Proofs.Cluster

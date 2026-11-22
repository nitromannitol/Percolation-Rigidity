import Rigidity.Proofs.Cluster.PlanarRestrictFieldCoarsen

/-!
# Lemma 5.5 of Armstrong and Dario for the pairings with a bounded field: the expectation

For a lattice field `g` with `|g| ≤ G`, `n ∈ [9m/10, m)` and every triadic cube `U` of scale `m`,
`E[N⁻¹ ∑_V (⟨∇[u(·, U, q)]_𝒫, g⟩_V - ⟨∇[u(·, V, q)]_𝒫, g⟩_V)² / |V|²]
  ≤ C G² |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`
(`exists_lintegral_planarMuRestrictFieldError_le`), from the partition for the reverse Hölder
inequality, as for the constant directions in `planarRestrictQuadCoarsenMu_of_inputs`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- **Lemma 5.5 of Armstrong and Dario for the pairings with a bounded field**, in expectation,
in dimension two. -/
theorem exists_lintegral_planarMuRestrictFieldError_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (n : ℕ), 9 * U.scale ≤ 10 * n → n < U.scale →
      ∀ (q : Fin 2 → ℝ) (g : Vertex 2 → Fin 2 → ℝ) (G : ℝ), (∀ x i, |g x i| ≤ G) →
      ∫⁻ ω, ENNReal.ofReal (planarMuRestrictFieldError ω U n q g) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * G ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
          (∑ k ∈ Finset.Ico n U.scale, planarTau p k + (3 : ℝ) ^ (-(n : ℝ) / 4))) := by
  have hR := planarReachConcentration_holds hpc
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
  obtain ⟨Cmj, hCmj, hmaj⟩ := exists_planarMuRestrictFieldError_majorant hpc
  set Λ₀ := restrictConst Aτ r CM (1 + ε / 2) A₂ with hΛ₀def
  have hΛ₀ : 0 ≤ Λ₀ := restrictConst_nonneg hAτ hCM
  set Ccs : ℝ := ((Cmj * Cb) ^ (1 / 2 : ℝ)).toReal with hCcs
  have hCcs0 : 0 ≤ Ccs := ENNReal.toReal_nonneg
  have hae := (ae_planarPartitionEvent hpc).and (has.and (ae_planarReach_ne_top hpc))
  refine ⟨Λ₀ * CD + 4 * Ccs, by positivity, fun U n hmn hnm q g G hg => ?_⟩
  obtain ⟨M, hMm, hMle, hM2⟩ := hmaj U n hnm.le q
  have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
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
  set g' : Configuration 2 → ℝ≥0∞ := fun ω =>
    if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (G ^ 2 * Λ₀ * (planarMuDefect ω U n q / U.volume)) else 0 with hgdef
  have hgood : ∀ᵐ ω ∂(latticeBondLaw 2 p), ω ∉ restrictBad s t K τ Aτ A₂ U n →
      ENNReal.ofReal (planarMuRestrictFieldError ω U n q g) ≤ g' ω := by
    filter_upwards [hae] with ω ⟨hP, hs, hfin⟩ hω
    have h := planarMuRestrictFieldError_le_of_not_mem_restrictBad hpq hτr hCM hAτ hA₂ hMey hP hs
      hfin hmn hnm hω q hg
    have hU := planarResolved_of_not_mem_restrictBad hP hnm hω
    simp only [hgdef, if_pos (show PlanarPartitionEvent ω ∧ PlanarResolved ω U from ⟨hP, hU⟩)]
    exact ENNReal.ofReal_le_ofReal h
  have hsplit := lintegral_le_add_sqrt_measure (latticeBondLaw 2 p)
    (fun ω => ENNReal.ofReal (planarMuRestrictFieldError ω U n q g)) g'
    (fun ω => ENNReal.ofReal (2 * G ^ 2) * M ω) (restrictBad s t K τ Aτ A₂ U n)
    (hMm.const_mul _) hgood (ae_of_all _ (hMle g G hg))
  refine hsplit.trans ?_
  have h1 : ∫⁻ ω, g' ω ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal (G ^ 2 * Λ₀ * CD * P * T) := by
    have hpt : ∀ ω, g' ω = ENNReal.ofReal (G ^ 2 * Λ₀ / U.volume) *
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMuDefect ω U n q) else 0) := fun ω => by
      simp only [hgdef]
      split_ifs
      · rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hG2 hΛ₀) hvol.le)]
        congr 1
        ring
      · rw [mul_zero]
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (G ^ 2 * Λ₀ / U.volume) * ∫⁻ ω, (if PlanarPartitionEvent ω ∧
          PlanarResolved ω U then ENNReal.ofReal (planarMuDefect ω U n q) else 0)
          ∂(latticeBondLaw 2 p)
        ≤ ENNReal.ofReal (G ^ 2 * Λ₀ / U.volume) * ENNReal.ofReal (U.volume * (CD * P * T)) :=
          mul_le_mul_of_nonneg_left (hdef U n hnm.le q) zero_le
      _ = ENNReal.ofReal (G ^ 2 * Λ₀ * CD * P * T) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hG2 hΛ₀) hvol.le)]
          congr 1
          field_simp
  set a : ℝ≥0∞ := ENNReal.ofReal (2 * G ^ 2) with ha
  have hM2' : ∫⁻ ω, (a * M ω) ^ 2 ∂(latticeBondLaw 2 p) ≤
      a ^ 2 * Cmj * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) ^ 2 *
        (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (2 / 3 : ℝ) := by
    simp_rw [mul_pow]
    rw [lintegral_const_mul _ (hMm.pow_const 2)]
    calc a ^ 2 * ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw 2 p)
        ≤ a ^ 2 * (Cmj * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) ^ 2 *
          (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hM2 zero_le
      _ = _ := by ring
  have hafin : a ^ 2 * Cmj ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hCmj
  have hreal : ((a ^ 2 * Cmj * Cb) ^ (1 / 2 : ℝ)).toReal = 2 * G ^ 2 * Ccs := by
    rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.toReal_mul]
    have hsq : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hsq, ha, ENNReal.toReal_ofReal (by positivity), hCcs]
  have h2 : (∫⁻ ω, (a * M ω) ^ 2 ∂(latticeBondLaw 2 p)) ^ (1 / 2 : ℝ) *
      (latticeBondLaw 2 p) (restrictBad s t K τ Aτ A₂ U n) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * G ^ 2 * Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
    have hb := sqrt_badTerm_le hafin hCb hQ0 hmn
    rw [hreal] at hb
    refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow hM2' (by norm_num))
      (ENNReal.rpow_le_rpow (hbad U n hmn hnm) (by norm_num))) hb
  calc ∫⁻ ω, g' ω ∂(latticeBondLaw 2 p) + (∫⁻ ω, (a * M ω) ^ 2 ∂(latticeBondLaw 2 p)) ^
        (1 / 2 : ℝ) * (latticeBondLaw 2 p) (restrictBad s t K τ Aτ A₂ U n) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (G ^ 2 * Λ₀ * CD * P * T) +
          ENNReal.ofReal (2 * G ^ 2 * Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) := add_le_add h1 h2
    _ = ENNReal.ofReal (G ^ 2 * Λ₀ * CD * P * T + 2 * G ^ 2 * Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((Λ₀ * CD + 4 * Ccs) * G ^ 2 * P * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : 2 * G ^ 2 * Ccs * Q * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ 2 * G ^ 2 * Ccs * (2 * P) * T :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQP (by positivity)) hT1 (by positivity)
            (by positivity)
        nlinarith

end Rigidity.Proofs.Cluster

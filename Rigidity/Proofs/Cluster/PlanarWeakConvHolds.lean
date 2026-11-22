import Rigidity.Proofs.Cluster.PlanarWeakConvOrigin
import Rigidity.Proofs.Cluster.PlanarRestrictQuadGehring
import Rigidity.Proofs.Percolation.PlanarLocalStationary

/-!
# Lemma 5.7 of Armstrong and Dario in dimension two

`PlanarWeakConvergence p` holds for `p > p_c(2)` from the partition for the reverse Hölder
inequality (`planarWeakConvergence_of_gehring`):
* for the cube `□_n` centred at the origin and `n ≥ 120`, the mean of the spatial average is
  `ā_{□_n}⁻¹ q` (display (5.23)) and its variance is controlled by
  `exists_variance_planarMuGradAvg_origin_le`;
* for every triadic cube `V` of scale `n`, the spatial average on `V` at `ω` equals the spatial
  average on `□_n` at the translated configuration on the event that the partition agrees with
  the capped partition on both cubes, whose complement has probability at most `C exp(-c 3ⁿ)`;
  the translation preserves the law of the bonds (the stationarity used by Armstrong and Dario to
  pass from `□_n` to `z + □_n`);
* for `n < 120` the spatial average is bounded by a constant multiple of `|q|₁`.
With Lemma 5.5 this gives Proposition 5.2, qualitative part, in dimension two from the partition
for the reverse Hölder inequality alone (`planarMuLimit_eq_of_gehring_partition`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

variable {ω : Configuration 2}

/-- The spatial average as the subcube pairing with the constant field `e_j`. -/
theorem planarMuGradAvg_eq_edgePairing (V : TriadicCube 2) (q : Fin 2 → ℝ) (j : Fin 2) :
    planarMuGradAvg ω V q j = edgePairing V.toIntegerCube.vertices
      (fun _ => (Pi.single j 1 : Fin 2 → ℝ)) (coarsen ω V (planarMuMinimizer ω V q)) /
        9 ^ V.scale := by
  rw [planarMuGradAvg, subcubePairing_eq, fieldPairing_const]
  rfl

/-- **A deterministic bound for the spatial average.** -/
theorem abs_planarMuGradAvg_le (V : TriadicCube 2) (q : Fin 2 → ℝ) (j : Fin 2) :
    |planarMuGradAvg ω V q j| ≤ 72 * 81 ^ V.scale * (|q 0| + |q 1|) := by
  rw [planarMuGradAvg_eq_edgePairing]
  have h := abs_subcubePairing_le V q (G := 1) (g := fun _ => (Pi.single j 1 : Fin 2 → ℝ))
    (fun _ i => by
      rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h | h <;>
        rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h' | h' <;> simp [h, h']) ω
  simpa using h

theorem abs_mulVec_le_of_entries {A : Matrix (Fin 2) (Fin 2) ℝ} {K : ℝ}
    (hA : ∀ i j, |A i j| ≤ K) (q : Fin 2 → ℝ) (j : Fin 2) :
    |(A *ᵥ q) j| ≤ K * (|q 0| + |q 1|) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h0 := hA j 0
  have h1 := hA j 1
  have := abs_nonneg (q 0)
  have := abs_nonneg (q 1)
  nlinarith

/-- The pointwise bound of the quantity of display (5.25). -/
theorem weakConv_integrand_le {A : Matrix (Fin 2) (Fin 2) ℝ} {K : ℝ} (hA : ∀ i j, |A i j| ≤ K)
    (V : TriadicCube 2) (q : Fin 2 → ℝ) (ω : Configuration 2) :
    ∑ j : Fin 2, (planarMuGradAvg ω V q j - (A *ᵥ q) j) ^ 2 ≤
      2 * (72 * 81 ^ V.scale + K) ^ 2 * (|q 0| + |q 1|) ^ 2 := by
  have hb : ∀ j, (planarMuGradAvg ω V q j - (A *ᵥ q) j) ^ 2 ≤
      (72 * 81 ^ V.scale + K) ^ 2 * (|q 0| + |q 1|) ^ 2 := by
    intro j
    have h1 := abs_planarMuGradAvg_le (ω := ω) V q j
    have h2 := abs_mulVec_le_of_entries hA q j
    have h3 : |planarMuGradAvg ω V q j - (A *ᵥ q) j| ≤ (72 * 81 ^ V.scale + K) * (|q 0| + |q 1|) :=
      (abs_sub _ _).trans (by nlinarith)
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [Fin.sum_univ_two]
  linarith [hb 0, hb 1]

/-- **The mean of the spatial average on `□_n`** (display (5.23)). -/
theorem integral_planarMuGradAvg_origin {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (n : ℕ) (q : Fin 2 → ℝ) (j : Fin 2) :
    ∫ ω, planarMuGradAvg ω ⟨n, 0⟩ q j ∂(latticeBondLaw 2 p) =
      (planarAhomInvFinite p n *ᵥ q) j := by
  have h := integral_coarsePairing_planarMuMinimizer hpc n (Pi.single j 1) q
  have hfun : (fun ω => planarMuGradAvg ω ⟨n, 0⟩ q j) = fun ω =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
        coarsePairing ω ⟨n, 0⟩ (Pi.single j 1) (planarMuMinimizer ω ⟨n, 0⟩ q) /
          (⟨n, 0⟩ : TriadicCube 2).volume else 0 := by
    funext ω
    rw [planarMuGradAvg]
    split_ifs with hω
    · rfl
    · rw [planarMuMinimizer, dif_neg hω, map_zero, zero_div]
  rw [hfun, h]
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Display (5.25) for `□_n`**, `n ≥ 120`. -/
theorem exists_lintegral_planarMuGradAvg_origin_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 120 ≤ n → ∀ q : Fin 2 → ℝ,
      ∫⁻ ω, ENNReal.ofReal (∑ j : Fin 2,
          (planarMuGradAvg ω ⟨n, 0⟩ q j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2)
          ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) *
          (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4))) := by
  obtain ⟨C, hC, hvar⟩ := exists_variance_planarMuGradAvg_origin_le hpc hG
  refine ⟨2 * C, by positivity, fun n hn q => ?_⟩
  set μ := latticeBondLaw 2 p
  have hm : ∀ j, AEMeasurable (fun ω => planarMuGradAvg ω ⟨n, 0⟩ q j) μ :=
    fun j => aemeasurable_planarMuGradAvg hpc _ q j
  have hint : ∀ j, Integrable (fun ω =>
      (planarMuGradAvg ω ⟨n, 0⟩ q j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2) μ := by
    intro j
    obtain ⟨K, hK, hA⟩ := exists_abs_planarAhomInvFinite_le hpc
    refine Integrable.of_bound ((((hm j).sub aemeasurable_const).pow_const 2).aestronglyMeasurable)
      ((72 * 81 ^ n + K) ^ 2 * (|q 0| + |q 1|) ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_planarMuGradAvg_le (ω := ω) (⟨n, 0⟩ : TriadicCube 2) q j
    have h2 := abs_mulVec_le_of_entries (hA n) q j
    have h3 : |planarMuGradAvg ω ⟨n, 0⟩ q j - (planarAhomInvFinite p n *ᵥ q) j| ≤
        (72 * 81 ^ n + K) * (|q 0| + |q 1|) := (abs_sub _ _).trans (by
          change |planarMuGradAvg ω ⟨n, 0⟩ q j| + _ ≤ _
          nlinarith)
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hvj : ∀ j, ∫ ω, (planarMuGradAvg ω ⟨n, 0⟩ q j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2 ∂μ ≤
      C * (q 0 ^ 2 + q 1 ^ 2) * (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
    intro j
    have := hvar n hn q j
    rw [variance_eq_integral (hm j), integral_planarMuGradAvg_origin hpc] at this
    exact this
  rw [← ofReal_integral_eq_lintegral_ofReal ((hint 0).add (hint 1) |>.congr
      (ae_of_all _ fun ω => by simp [Fin.sum_univ_two]))
    (ae_of_all _ fun ω => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : ∫ ω, ∑ j : Fin 2, (planarMuGradAvg ω ⟨n, 0⟩ q j -
      (planarAhomInvFinite p n *ᵥ q) j) ^ 2 ∂μ =
      ∫ ω, (planarMuGradAvg ω ⟨n, 0⟩ q 0 - (planarAhomInvFinite p n *ᵥ q) 0) ^ 2 ∂μ +
        ∫ ω, (planarMuGradAvg ω ⟨n, 0⟩ q 1 - (planarAhomInvFinite p n *ᵥ q) 1) ^ 2 ∂μ := by
    rw [← integral_add (hint 0) (hint 1)]
    congr 1
    funext ω
    rw [Fin.sum_univ_two]
  rw [e]
  linarith [hvj 0, hvj 1]

/-- **Translation of the spatial average.** On the event that the partition agrees with the capped
partition on `V` at `ω` and on the translated cube at the translated configuration, the spatial
average moves with the translation. -/
theorem planarMuGradAvg_shift_eq_of_good {V : TriadicCube 2} {z : Vertex 2}
    (hz : ∀ i, V.side ∣ z i) (hω : PlanarLocalGood ω V)
    (hω' : PlanarLocalGood (configurationTranslation z ω) (V.shift z)) (q : Fin 2 → ℝ)
    (j : Fin 2) :
    planarMuGradAvg (configurationTranslation z ω) (V.shift z) q j = planarMuGradAvg ω V q j := by
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hpart : ∀ x ∈ V.vertices, planarPartCube (configurationTranslation z ω) (x + z) =
      (planarPartCube ω x).shift z := by
    intro x hx
    rw [planarPartCube_eq_cappedCube hω' ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      planarPartCube_eq_cappedCube hω hx]
    exact cappedCube_planarGoodCubes_translation hz' ω x
  have key : ∀ r : Fin 2 → ℝ,
      (if PlanarPartitionEvent (configurationTranslation z ω) ∧
          PlanarResolved (configurationTranslation z ω) (V.shift z) then
        -planarMu (configurationTranslation z ω) (V.shift z) r else 0) =
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V r else 0 := by
    intro r
    by_cases hres : PlanarResolved ω V
    · have hres' := (planarResolved_shift_iff hz hpart).2 hres
      rw [if_pos ⟨hω'.1, hres'⟩, if_pos ⟨hω.1, hres⟩,
        planarMu_shift_translation hω.1 hres hz hpart]
    · have hres' : ¬ PlanarResolved (configurationTranslation z ω) (V.shift z) :=
        fun h => hres ((planarResolved_shift_iff hz hpart).1 h)
      rw [if_neg fun h => hres' h.2, if_neg fun h => hres h.2]
  have h1 := congrFun (planarMuGradAvg_eq (V.shift z) q j) (configurationTranslation z ω)
  have h2 := congrFun (planarMuGradAvg_eq V q j) ω
  rw [h1, h2, key, key, key]

/-- A stretched exponential absorbs a power of `81ⁿ`. -/
theorem exists_exp_neg_mul_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      (81 : ℝ) ^ (2 * n) * Real.exp (-c * (3 : ℝ) ^ n) ≤ K * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  obtain ⟨K, hK, h⟩ := exists_exp_neg_rpow_le_inv_pow hc one_pos 9
  refine ⟨K, hK, fun n => ?_⟩
  have h1 := h n
  rw [Real.rpow_one] at h1
  have h81 : (81 : ℝ) ^ (2 * n) = ((3 : ℝ) ^ n) ^ 8 := by
    rw [← pow_mul, show (81 : ℝ) = 3 ^ 4 by norm_num, ← pow_mul]
    congr 1
    ring
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  calc (81 : ℝ) ^ (2 * n) * Real.exp (-c * (3 : ℝ) ^ n)
      ≤ ((3 : ℝ) ^ n) ^ 8 * (K * ((3 : ℝ) ^ n)⁻¹ ^ 9) := by
        rw [h81]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K * ((3 : ℝ) ^ n)⁻¹ := by
        field_simp
    _ ≤ K * (3 : ℝ) ^ (-(n : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (inv_three_pow_le n) hK

/-- **Lemma 5.7 of Armstrong and Dario** (display (5.25), in dimension two), for every triadic cube,
from the partition for the reverse Hölder inequality. -/
theorem planarWeakConvergence_of_gehring {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p) :
    PlanarWeakConvergence p := by
  obtain ⟨C₀, hC₀, horig⟩ := exists_lintegral_planarMuGradAvg_origin_le hpc hG
  obtain ⟨K, hK, hA⟩ := exists_abs_planarAhomInvFinite_le hpc
  obtain ⟨Cl, hCl, c, hc, hloc⟩ := exists_planarNuLoc_localization hpc
  obtain ⟨Ke, hKe, hexp⟩ := exists_exp_neg_mul_le hc
  set Cs : ℝ := 2 * (72 * 81 ^ 120 + K) ^ 2 * 2 * 3 ^ 30 with hCs
  set Ce : ℝ := 2 * (72 + K) ^ 2 * 2 * (2 * Cl.toReal * Ke) with hCe
  refine ⟨Cs + C₀ + Ce, by positivity, fun V q => ?_⟩
  set n := V.scale with hn
  set μ := latticeBondLaw 2 p
  set P := q 0 ^ 2 + q 1 ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hQP : (|q 0| + |q 1|) ^ 2 ≤ 2 * P := abs_add_abs_sq_le q
  set x : ℝ := (3 : ℝ) ^ (-(n : ℝ) / 4) with hx
  have hx0 : 0 ≤ x := by positivity
  have hτ : 0 ≤ planarTau p n := planarTau_nonneg p n
  set F : TriadicCube 2 → Configuration 2 → ℝ := fun W ω => ∑ j : Fin 2,
    (planarMuGradAvg ω W q j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2 with hF
  have hFb : ∀ W ω, F W ω ≤ 2 * (72 * 81 ^ W.scale + K) ^ 2 * (|q 0| + |q 1|) ^ 2 :=
    fun W ω => weakConv_integrand_le (hA n) W q ω
  have hFb0 : ∀ W ω, 0 ≤ F W ω := fun W ω => Finset.sum_nonneg fun j _ => sq_nonneg _
  change ∫⁻ ω, ENNReal.ofReal (F V ω) ∂μ ≤ _
  by_cases hsmall : n < 120
  · -- small scales
    calc ∫⁻ ω, ENNReal.ofReal (F V ω) ∂μ
        ≤ ∫⁻ _ω, ENNReal.ofReal (2 * (72 * 81 ^ n + K) ^ 2 * (|q 0| + |q 1|) ^ 2) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hFb V ω)
      _ = ENNReal.ofReal (2 * (72 * 81 ^ n + K) ^ 2 * (|q 0| + |q 1|) ^ 2) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h81 : (81 : ℝ) ^ n ≤ 81 ^ 120 := pow_le_pow_right₀ (by norm_num) hsmall.le
          have hx30 : (3 : ℝ) ^ (-(30 : ℝ)) ≤ x := by
            rw [hx]
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have : (n : ℝ) < 120 := by exact_mod_cast hsmall
            linarith
          have h330 : (3 : ℝ) ^ (-(30 : ℝ)) * 3 ^ 30 = 1 := by
            rw [Real.rpow_neg (by norm_num), ← Real.rpow_natCast]
            norm_num
          have hA1 : (2 * (72 * 81 ^ n + K) ^ 2 * (|q 0| + |q 1|) ^ 2 : ℝ) ≤
              2 * (72 * 81 ^ 120 + K) ^ 2 * (2 * P) := by
            have : (72 * 81 ^ n + K) ^ 2 ≤ (72 * 81 ^ 120 + K) ^ 2 :=
              pow_le_pow_left₀ (by positivity) (by linarith) 2
            exact mul_le_mul (mul_le_mul_of_nonneg_left this (by norm_num)) hQP (by positivity)
              (by positivity)
          have hCsP : 2 * (72 * 81 ^ 120 + K) ^ 2 * (2 * P) ≤ Cs * P * x := by
            rw [hCs]
            have e : 2 * (72 * 81 ^ 120 + K) ^ 2 * 2 * 3 ^ 30 * P * x =
                2 * (72 * 81 ^ 120 + K) ^ 2 * (2 * P) * (3 ^ 30 * x) := by ring
            rw [e]
            have h1 : (1 : ℝ) ≤ 3 ^ 30 * x := by
              have := mul_le_mul_of_nonneg_left hx30 (by positivity : (0 : ℝ) ≤ 3 ^ 30)
              linarith
            nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
              (sq_nonneg (72 * 81 ^ 120 + K))) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hP0)]
          have : Cs * P * x ≤ (Cs + C₀ + Ce) * P * (planarTau p n + x) := by
            have h1 : Cs * P * x ≤ (Cs + C₀ + Ce) * P * x :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by
                have : 0 ≤ Ce := by positivity
                linarith) hP0) hx0
            have h2 : (Cs + C₀ + Ce) * P * x ≤ (Cs + C₀ + Ce) * P * (planarTau p n + x) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            linarith
          linarith
  · -- large scales: translate to the origin
    push Not at hsmall
    set V₀ : TriadicCube 2 := V.originCube with hV₀
    set z : Vertex 2 := V.center with hz
    have hV₀z : V₀.shift z = V := V.originCube_shift_center
    have hzd : ∀ i, V₀.side ∣ z i := V.originCube_side_dvd_center
    have hmp := measurePreserving_configurationTranslation p z
    have hemb : MeasurableEmbedding (configurationTranslation z : Configuration 2 → _) :=
      (configurationTranslationMeasurableEquiv z).measurableEmbedding
    set B₁ := {ω : Configuration 2 | ¬ PlanarLocalGood ω V₀} with hB₁
    set B₂ := {ω : Configuration 2 | ¬ PlanarLocalGood ω V} with hB₂
    set B := B₁ ∪ (configurationTranslation z) ⁻¹' B₂ with hB
    have hμB₁ : μ B₁ ≤ Cl * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) := (hloc V₀ 0).1
    have hμB₂ : μ ((configurationTranslation z) ⁻¹' B₂) ≤
        Cl * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) := by
      rw [hmp.measure_preimage_emb hemb]
      exact (hloc V 0).1
    have hμB : μ (toMeasurable μ B) ≤ 2 * Cl * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) := by
      rw [measure_toMeasurable]
      refine (measure_union_le _ _).trans ?_
      calc μ B₁ + μ ((configurationTranslation z) ⁻¹' B₂)
          ≤ Cl * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) +
            Cl * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) := add_le_add hμB₁ hμB₂
        _ = 2 * Cl * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) := by ring
    set Mb : ℝ := 2 * (72 * 81 ^ n + K) ^ 2 * (|q 0| + |q 1|) ^ 2 with hMb
    have hpt : ∀ ω, ENNReal.ofReal (F V (configurationTranslation z ω)) ≤
        ENNReal.ofReal (F V₀ ω) + ENNReal.ofReal Mb * (toMeasurable μ B).indicator 1 ω := by
      intro ω
      by_cases hω : ω ∈ toMeasurable μ B
      · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
        exact le_add_left (ENNReal.ofReal_le_ofReal (hFb V _))
      · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
        have hωB : ω ∉ B := fun h => hω (subset_toMeasurable _ _ h)
        simp only [hB, Set.mem_union, Set.mem_preimage, hB₁, hB₂, Set.mem_setOf_eq, not_or,
          not_not] at hωB
        have hgood' : PlanarLocalGood (configurationTranslation z ω) (V₀.shift z) := by
          rw [hV₀z]; exact hωB.2
        refine le_of_eq (congrArg ENNReal.ofReal ?_)
        simp only [hF]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← planarMuGradAvg_shift_eq_of_good hzd hωB.1 hgood' q j, hV₀z]
    have hcomp : ∫⁻ ω, ENNReal.ofReal (F V ω) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (F V (configurationTranslation z ω)) ∂μ :=
      (hmp.lintegral_comp_emb hemb (fun ω => ENNReal.ofReal (F V ω))).symm
    have hV₀n : V₀ = ⟨n, 0⟩ := rfl
    have horig' := horig n hsmall q
    rw [← hV₀n] at horig'
    rw [hcomp]
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_right _ ((measurable_one.indicator (measurableSet_toMeasurable _ _)).const_mul
      _), lintegral_const_mul _ (measurable_one.indicator (measurableSet_toMeasurable _ _)),
      lintegral_indicator_one (measurableSet_toMeasurable _ _)]
    refine (add_le_add horig' (mul_le_mul_of_nonneg_left hμB zero_le)).trans ?_
    -- real arithmetic
    set ex := Real.exp (-c * (3 : ℝ) ^ n) with hex
    have hc2 : (2 : ℝ≥0∞) * Cl * ENNReal.ofReal ex = ENNReal.ofReal (2 * Cl.toReal * ex) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_toReal hCl, ENNReal.ofReal_ofNat]
    rw [hc2, ← ENNReal.ofReal_mul (by positivity : 0 ≤ Mb),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h81 : (1 : ℝ) ≤ 81 ^ n := one_le_pow₀ (by norm_num)
    have hlin : 72 * (81 : ℝ) ^ n + K ≤ (72 + K) * 81 ^ n := by nlinarith
    have hsq : (72 * (81 : ℝ) ^ n + K) ^ 2 ≤ (72 + K) ^ 2 * 81 ^ (2 * n) := by
      have := pow_le_pow_left₀ (by positivity) hlin 2
      rw [mul_pow, ← pow_mul, mul_comm n 2] at this
      exact this
    have he := hexp n
    have hMb : Mb * (2 * Cl.toReal * ex) ≤ Ce * P * x := by
      rw [hMb, hCe]
      have hCl0 : 0 ≤ Cl.toReal := ENNReal.toReal_nonneg
      have hex0 : 0 ≤ ex := (Real.exp_pos _).le
      calc 2 * (72 * 81 ^ n + K) ^ 2 * (|q 0| + |q 1|) ^ 2 * (2 * Cl.toReal * ex)
          ≤ 2 * ((72 + K) ^ 2 * 81 ^ (2 * n)) * (2 * P) * (2 * Cl.toReal * ex) := by
            gcongr
        _ = 2 * (72 + K) ^ 2 * (2 * P) * (2 * Cl.toReal) * (81 ^ (2 * n) * ex) := by ring
        _ ≤ 2 * (72 + K) ^ 2 * (2 * P) * (2 * Cl.toReal) * (Ke * x) :=
            mul_le_mul_of_nonneg_left he (by positivity)
        _ = 2 * (72 + K) ^ 2 * 2 * (2 * Cl.toReal * Ke) * P * x := by ring
    have hCs0 : 0 ≤ Cs := by positivity
    have hCe0 : 0 ≤ Ce := by positivity
    have e : (Cs + C₀ + Ce) * P * (planarTau p n + x) =
        C₀ * P * (planarTau p n + x) + (Cs * P * (planarTau p n + x) +
          Ce * P * (planarTau p n + x)) := by ring
    rw [e]
    have h1 : Ce * P * x ≤ Ce * P * (planarTau p n + x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 0 ≤ Cs * P * (planarTau p n + x) := by positivity
    linarith

/-- **Proposition 5.2 of Armstrong and Dario, qualitative part** (dimension two), from the
partition for the reverse Hölder inequality: `lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q`. -/
theorem planarMuLimit_eq_of_gehring_partition {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p) (q : Fin 2 → ℝ) :
    planarMuLimit p q = 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i :=
  planarMuLimit_eq_of_gehring hpc (planarWeakConvergence_of_gehring hpc hG) hG q

end Rigidity.Proofs.Cluster

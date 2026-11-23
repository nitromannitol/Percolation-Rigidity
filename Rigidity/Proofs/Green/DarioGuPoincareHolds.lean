import Rigidity.Proofs.Green.DarioGuPoincareScales
import Rigidity.Proofs.Green.DarioGuApproxLemma
import Rigidity.Proofs.Cluster.PlanarReachConcentrationHolds
import Rigidity.Proofs.S2.ClusterDensityConcentration

/-!
# The weak Poincaré inequality on balls of the planar infinite cluster

`clusterPoincareTwo_holds : ClusterPoincareTwo`: the weak form of Proposition 2.7 of Dario–Gu in
dimension two, `‖u - (u)_{𝒞_∞ ∩ B_R(y)}‖_{L̲²} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_{24R}(y))}` for
`R ≥ M_Poinc(y) ≤ O_s(C)`. The source cites Barlow 2004 (Theorem 2.18) and Armstrong–Dario
(Proposition 3.4); here it follows from the Sobolev inequality of Armstrong–Dario on resolved
squares (`sum_sq_sub_finAvg_clusterBall_le`), the concentration of the stopping sizes of the
partition into coarsely good cubes (`exists_measure_sum_stoppingSize_gt_le`, `τ = 4`) through a
minimal scale above which every scale is good on the nine cubes around `y`
(`goodScale_consequences`), and the lower bound on the volume of the cluster in balls
(Proposition A.1, `clusterDensityInputFaithful_of_concentration`).
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.Cluster Rigidity.Proofs.S2
open scoped ENNReal

namespace Rigidity.Green

/-- The normalization of the weak Poincaré inequality: from
`S ≤ K_p R² E`, `|B_R| ≥ c 10⁴ R²`, `|B_{24R}| ≤ 14400 R²` and `2 K_p / c ≤ C²`,
`(S/|B_R|)^{1/2} ≤ C R (E/|B_{24R}|)^{1/2}`. -/
theorem poincare_normalize {S nR n24 gE Kp cD C R : ℝ} (hR : 0 < R) (hcD : 0 < cD)
    (hKp : 0 ≤ Kp) (hgE : 0 ≤ gE) (hS : S ≤ Kp * R ^ 2 * gE) (hvol : cD * 100 ^ 2 * R ^ 2 ≤ nR)
    (hcard : n24 ≤ 14400 * R ^ 2) (hn24 : 0 < n24) (hC : 2 * Kp / cD ≤ C ^ 2) (hC0 : 0 ≤ C) :
    Real.sqrt (S / nR) ≤ C * R * Real.sqrt (gE / n24) := by
  have hnR : 0 < nR := lt_of_lt_of_le (by positivity) hvol
  have hX : S / nR ≤ Kp / (cD * 100 ^ 2) * gE := by
    rw [div_le_iff₀ hnR]
    calc S ≤ Kp * R ^ 2 * gE := hS
      _ = Kp / (cD * 100 ^ 2) * gE * (cD * 100 ^ 2 * R ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hvol (by positivity)
  have hY : gE / (14400 * R ^ 2) ≤ gE / n24 := div_le_div_of_nonneg_left hgE hn24 hcard
  have hfin : S / nR ≤ (C * R) ^ 2 * (gE / n24) := by
    refine hX.trans ?_
    calc Kp / (cD * 100 ^ 2) * gE ≤ C ^ 2 / 14400 * gE := by
          apply mul_le_mul_of_nonneg_right _ hgE
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have h2 : 2 * Kp ≤ C ^ 2 * cD := by rwa [div_le_iff₀ hcD] at hC
          nlinarith
      _ = (C * R) ^ 2 * (gE / (14400 * R ^ 2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hY (by positivity)
  calc Real.sqrt (S / nR) ≤ Real.sqrt ((C * R) ^ 2 * (gE / n24)) := Real.sqrt_le_sqrt hfin
    _ = C * R * Real.sqrt (gE / n24) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **The weak Poincaré inequality on balls of the planar infinite cluster** (Dario–Gu,
Proposition 2.7, weak form). -/
theorem clusterPoincareTwo_holds : ClusterPoincareTwo := by
  intro p hpc hp1
  set μ := latticeBondLaw 2 p with hμ
  obtain ⟨C₀, hC₀, c₀, hc₀, hq⟩ := exists_measure_not_mem_planarCoarseGood_le hpc
  obtain ⟨Cfin, Ctot, hCtot, c', hc', hsum⟩ := exists_measure_sum_stoppingSize_gt_le (d := 2)
    (by norm_num) p planarCoarseGood measurableSet_mem_planarCoarseGood
    measurableSet_not_mem_planarCoarseGood_localEdge hC₀ hc₀ one_pos le_rfl hq 4
  have hH : ∀ᵐ ω ∂μ, ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω) :=
    TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched μ
      planarCoarseGood (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top 1 c₀ one_pos hc₀ fun R => by
        rw [← ENNReal.ofReal_mul hC₀]
        exact hq R
  have hPae := ae_planarPartitionEvent (p := p) hpc
  obtain ⟨KS, hKS, hdet⟩ := sum_sq_sub_finAvg_clusterBall_le
  obtain ⟨sD, CD, cD, hsD, hCD, hcD, hD⟩ :=
    clusterDensityInputFaithful_of_concentration cluster_density_concentration 2 le_rfl p hpc hp1
  set s' : ℝ := 1 / ((2 * (2 + 4 + 1) : ℕ) : ℝ) with hs'
  have hs'0 : 0 < s' := by positivity
  set s := s' / 2 with hs
  have hs0 : 0 < s := by positivity
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (6561 * Cfin) (by norm_num : (1 : ℝ) < 9)
  set Cfp := max Cfin 0 with hCfp
  set Kp := KS * 144 * Cfp * 36 with hKp
  have hKp0 : 0 ≤ Kp := by positivity
  set Kc := 1 + 2 * Kp / cD with hKc
  have hKc1 : 1 ≤ Kc := by
    have : 0 ≤ 2 * Kp / cD := by positivity
    rw [hKc]
    linarith
  set b : ℕ → ℝ := fun m => 9 * Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ m) ^ s') with hb
  have hb0 : ∀ m, 0 ≤ b m := fun m => by positivity
  -- summability
  have hsumm : Summable fun m => b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s) := by
    set τ := s * Real.log 3 with hτ
    have hτ0 : 0 < τ := mul_pos hs0 (Real.log_pos (by norm_num))
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_exp_mul_sub_sq (3 ^ s) c' τ hc' hτ0).mul_left (9 * Ctot.toReal))
    have hv1 : ((3 : ℝ) ^ m) ^ s' = Real.exp (τ * m) ^ 2 := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, sq, ← Real.exp_add, hτ, hs]
      congr 1
      ring
    have hv2 : ((1 : ℝ) * 3 ^ (m + 1)) ^ s = 3 ^ s * Real.exp (τ * m) := by
      rw [scale_exponent_eq (by norm_num) m, mul_one, hτ]
    show 9 * Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ m) ^ s') *
      Real.exp ((1 * 3 ^ (m + 1)) ^ s) ≤ _
    rw [hv1, hv2]
    apply le_of_eq
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  -- the bad scales
  set Bad : Vertex 2 → ℕ → Set (Configuration 2) := fun y m =>
    ⋃ e ∈ indexBox (idx m y) 1, {ω | Cfin * 3 ^ (2 * m) < ∑ x ∈ (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices,
      TriadicCube.stoppingSize (planarCoarseGood ω) x ^ 4} with hBad
  have hBadμ : ∀ y m, μ (toMeasurable μ (Bad y m)) ≤ ENNReal.ofReal (b m) := by
    intro y m
    rw [measure_toMeasurable]
    calc μ (Bad y m) ≤ ∑ e ∈ indexBox (idx m y) 1, μ {ω | Cfin * 3 ^ (2 * m) <
          ∑ x ∈ (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices,
            TriadicCube.stoppingSize (planarCoarseGood ω) x ^ 4} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _e ∈ indexBox (idx m y) 1, Ctot * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^
          ((1 : ℝ) / ((2 * (2 + 4 + 1) : ℕ) : ℝ)))) := Finset.sum_le_sum fun e _ => hsum ⟨m, e⟩
      _ = ENNReal.ofReal (b m) := by
          rw [Finset.sum_const, card_indexBox_one, hb]
          conv_lhs => rw [← ENNReal.ofReal_toReal hCtot]
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num), hs']
          congr 1
          push_cast
          ring
  -- the constants of the minimal scale
  set B₁ := Real.exp ((1 : ℝ) ^ s) + ∑' m, b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s) with hB₁
  have hB₁1 : 1 ≤ B₁ := by
    have h1 := Real.one_le_exp (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1) s)
    have h2 : 0 ≤ ∑' m, b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s) :=
      tsum_nonneg fun m => mul_nonneg (hb0 m) (Real.exp_pos _).le
    linarith
  set sS := min s sD with hsS
  have hsS0 : 0 < sS := lt_min hs0 hsD
  set θM := 1 * B₁ ^ (1 / s) with hθM
  set θ1 := (3 : ℝ) ^ m₀ * θM * (6 : ℝ) ^ (1 / sS) with hθ1
  set θD := CD * (6 : ℝ) ^ (1 / sS) with hθD
  set θc := (1 : ℝ) * (3 : ℝ) ^ (1 / sS) with hθc
  set θ2 := max θD θc * (4 : ℝ) ^ (1 / sS) with hθ2
  set θP := max θ1 θ2 * (4 : ℝ) ^ (1 / sS) with hθP
  set C := max θP Kc with hC
  have hC0 : 0 < C := lt_max_of_lt_right (by linarith)
  refine ⟨sS, C, 24, hsS0, hC0, by norm_num, fun y => ?_⟩
  obtain ⟨M, hMm, hM0, hMint, hMle, hMae⟩ := exists_minimalScale_of_summable μ
    (fun m => toMeasurable μ (Bad y m)) (fun m => measurableSet_toMeasurable _ _) one_pos b hb0
    (hBadμ y) hsumm
  -- `M ≤ O_s`
  have he : (fun ω => Real.exp ((max (M ω / 1) 0).rpow s)) = fun ω => Real.exp (M ω ^ s) := by
    funext ω
    rw [div_one, max_eq_left (hM0 ω)]
    rfl
  have hMos : IsOsBond 2 p M s θM := by
    refine isOsBond_of_integral_le hs0 hB₁1 (by rw [he]; exact hMint) ?_
    rw [he]
    exact hMle
  have hm1 : Measurable fun ω => (3 : ℝ) ^ m₀ * M ω := measurable_const.mul hMm
  have hos1 : IsOsBond 2 p (fun ω => (3 : ℝ) ^ m₀ * M ω) sS θ1 :=
    IsOsBond.mono_exponent hsS0 (min_le_left _ _) hm1 (IsOsBond.const_mul (by positivity) hMos)
  obtain ⟨MD, hMDm, hMD0, hMDos, hDae⟩ := hD y
  have hosD : IsOsBond 2 p MD sS θD :=
    IsOsBond.mono_exponent hsS0 (min_le_right _ _) hMDm hMDos
  have hosc : IsOsBond 2 p (fun _ => (1 : ℝ)) sS θc := isOsBond_const one_pos hsS0
  have hos2 := IsOsBond.max hsS0 (by positivity) (by positivity) hMDm measurable_const hosD hosc
  have hos := IsOsBond.max hsS0 (by positivity) (by positivity) hm1
    (hMDm.max measurable_const) hos1 hos2
  set MP : Configuration 2 → ℝ := fun ω => max ((3 : ℝ) ^ m₀ * M ω) (max (MD ω) 1) with hMP
  have hMPm : Measurable MP := hm1.max (hMDm.max measurable_const)
  refine ⟨MP, hMPm, fun ω => le_max_of_le_right (le_max_of_le_right zero_le_one),
    IsOsBond.mono_scale hsS0 (by positivity) (le_max_left _ _) hMPm hos, ?_⟩
  filter_upwards [hMae, hH, hPae, hDae] with ω hMω hHω hPω hDω
  clear_value Bad b B₁ θM θ1 θD θc θ2 θP
  intro h R hR u
  obtain ⟨N, hMN, hgoodN⟩ := hMω
  have hR1 : 1 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hRD : MD ω ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRM : (3 : ℝ) ^ m₀ * 3 ^ N ≤ R := by
    have := (le_max_left _ _).trans hR
    rw [hMN, one_mul] at this
    exact this
  have hR0 : 0 < R := by linarith
  -- the scale
  have hex : ∃ n : ℕ, 2 * R < (3 : ℝ) ^ n := pow_unbounded_of_one_lt _ (by norm_num)
  classical
  set m := Nat.find hex with hmdef
  have hm2 : 2 * R < (3 : ℝ) ^ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hm2
    linarith
  have hm6 : (3 : ℝ) ^ m ≤ 6 * R := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hmin := Nat.find_min hex (show k < m by omega)
    rw [not_lt] at hmin
    rw [hk, pow_succ]
    linarith
  have hNm : N + m₀ < m := by
    have h1 : (3 : ℝ) ^ (N + m₀) < 3 ^ m := by
      rw [pow_add, mul_comm]
      linarith
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1
  -- the good scale
  set ss : Vertex 2 → ℝ := fun x => TriadicCube.stoppingSize (planarCoarseGood ω) x with hss
  have hnot : ω ∉ Bad y m := fun hb => hgoodN m (by omega) (subset_toMeasurable _ _ hb)
  have hgood : ∀ e ∈ indexBox (idx m y) 1,
      ∑ z ∈ (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices, ss z ^ 4 ≤ Cfin * 9 ^ m := by
    intro e he
    by_contra hlt
    rw [not_le] at hlt
    apply hnot
    rw [hBad, Set.mem_iUnion₂]
    refine ⟨e, he, ?_⟩
    change Cfin * 3 ^ (2 * m) < _
    rw [pow_mul]
    norm_num
    exact hlt
  have hreach : ∀ z, planarReach ω z ≤ ENNReal.ofReal (ss z) := fun z =>
    planarReach_le_stoppingSize hHω z
  have hm9 : 6561 * Cfin < 9 ^ m :=
    lt_of_lt_of_le hm₀ (pow_le_pow_right₀ (by norm_num) (by omega))
  obtain ⟨H1, H2⟩ := goodScale_consequences hPω ss hreach hgood hm9
  have hsum := hdet ω hPω h y m (144 * Cfin * 9 ^ m) R (24 * R) H1 H2 hm2.le (by linarith) u
  set K := uniqueInfiniteComponent h with hK
  set gE := gradEnergy ω (clusterBall K y (24 * R)) u with hgE
  have hgE0 : 0 ≤ gE := gradEnergy_nonneg _ _ _
  have h9m : (9 : ℝ) ^ m ≤ 36 * R ^ 2 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    have h3 : (0 : ℝ) ≤ 3 ^ m := by positivity
    nlinarith
  have hsum2 : ∑ x ∈ clusterBall K y R, (u x - finAvg (clusterBall K y R) u) ^ 2 ≤
      Kp * R ^ 2 * gE := by
    refine hsum.trans ?_
    have hc : Cfin * 9 ^ m ≤ Cfp * (36 * R ^ 2) := by
      have h1 : Cfin * 9 ^ m ≤ Cfp * 9 ^ m :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      exact h1.trans (mul_le_mul_of_nonneg_left h9m (le_max_right _ _))
    have e1 : KS * (144 * Cfin * 9 ^ m) * gE = KS * 144 * (Cfin * 9 ^ m) * gE := by ring
    have e2 : KS * 144 * (Cfp * (36 * R ^ 2)) * gE = Kp * R ^ 2 * gE := by rw [hKp]; ring
    rw [e1, ← e2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hgE0
  -- the volumes
  have hvol : cD * 100 ^ 2 * R ^ 2 ≤ (clusterBall K y R).card := by
    have h1 := hDω h (100 * R) (by linarith) (latticeEuclideanEmbedding y) (by
      rw [dist_self]; positivity)
    rw [show 100 * R / 100 = R by ring, ncard_eq_card_clusterBall] at h1
    calc cD * 100 ^ 2 * R ^ 2 = cD * (100 * R) ^ 2 := by ring
      _ ≤ _ := h1
  have hBR : (0 : ℝ) < (clusterBall K y R).card := lt_of_lt_of_le (by positivity) hvol
  have hcard24 : ((clusterBall K y (24 * R)).card : ℝ) ≤ 14400 * R ^ 2 := by
    have h := card_clusterBall_le K y (show 1 ≤ 24 * R by linarith)
    have e : 25 * (24 * R) ^ 2 = 14400 * R ^ 2 := by ring
    exact h.trans e.le
  have hB24 : (0 : ℝ) < (clusterBall K y (24 * R)).card := by
    have : ((clusterBall K y R).card : ℝ) ≤ (clusterBall K y (24 * R)).card := by
      exact_mod_cast Finset.card_le_card (clusterBall_mono (by linarith))
    exact lt_of_lt_of_le hBR this
  -- conclusion
  have hC2 : 2 * Kp / cD ≤ C ^ 2 := by
    have hCK : Kc ≤ C := le_max_right _ _
    have h1 : 2 * Kp / cD ≤ Kc := by rw [hKc]; exact le_add_of_nonneg_left zero_le_one
    have hC1 : 1 ≤ C := hKc1.trans hCK
    exact h1.trans (hCK.trans (le_self_pow₀ hC1 two_ne_zero))
  exact poincare_normalize hR0 hcD hKp0 hgE0 hsum2 hvol hcard24 hB24 hC2 hC0.le

end Rigidity.Green

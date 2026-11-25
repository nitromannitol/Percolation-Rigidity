import Rigidity.Proofs.WeakPoincare.Scales
import PercolationClusterHomogenization.Proofs.Cluster.GeneralReachDomination
import PercolationClusterHomogenization.Proofs.Partition.GeneralMinimalScaleMain
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityConcentration
import Rigidity.Proofs.S2.ClusterDensityFromDarioGu

/-!
# Good balls of the supercritical infinite cluster in every dimension

`clusterGoodBalls_holds : ClusterGoodBalls d` for `d ≥ 2`: Barlow's Theorem 2.18 (a), (b) with the
random scale of Lemma 2.19, at a fixed centre, for Euclidean balls of `𝒞_∞` with the counting
measure. For `R ≥ M(y) ≤ O_s(C)`,

* `C⁻¹ R^d ≤ |𝒞_∞ ∩ B_R(y)| ≤ C R^d`;
* `Σ_{𝒞_∞ ∩ B_R(y)} (u - (u)_{𝒞_∞ ∩ B_R(y)})² ≤ C R² Σ_{edges of 𝒞_∞ ∩ B_{12dR}(y)} |∇u|²`.

The route is that of the planar case (`Rigidity.Green.clusterPoincareTwo_holds`), in every
dimension: the Sobolev inequality of Armstrong–Dario on the cluster of the triple of the triadic
cube of scale `m` containing `y` (`sum_sq_sub_finAvg_clusterBall_le`), the concentration of the
stopping sizes of the partition into coarsely good cubes (Armstrong–Dario, Proposition 2.4,
`exists_measure_sum_stoppingSize_gt_le`, with `τ = d(d+2)`), which dominate the reach of the
partition (`partitionReach_le_stoppingSize_coarseGood`), through a minimal scale above which every
scale is good on the `3^d` cubes around `y` (`goodScale_consequences`), and the lower bound on the
volume of the cluster in balls (Dario–Gu, Proposition A.1, in every dimension,
`clusterDensityInputFaithful_of_concentration`). The upper bound on the volume is the count of the
lattice points of the ball.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.Cluster Rigidity.Proofs.S2
open scoped ENNReal

namespace Rigidity.WeakPoincare

variable {d : ℕ}

theorem ncard_eq_card_clusterBall {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d)
    (r : ℝ) :
    ({z : K | dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding y) < r}.ncard) =
      (clusterBall K y r).card := by
  set S := {z : K | dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding y) < r}
  rw [← Set.ncard_image_of_injective S Subtype.val_injective, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_image, Finset.mem_coe, mem_clusterBall, S, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, by rw [dist_eq_norm] at hz; exact hz⟩
  · rintro ⟨hv, hd⟩
    exact ⟨⟨v, hv⟩, by rw [dist_eq_norm]; exact hd, rfl⟩

theorem card_box_one_nat (c : Vertex d) : (box c 1).card = 3 ^ d := by
  have h := card_box_one c
  exact_mod_cast h

/-- `(c 3^{dm})^{2/d} ≤ 36 c^{2/d} R²` when `3^m ≤ 6 R`. -/
theorem rpow_two_div_le {m : ℕ} (hd : 0 < d) {c R : ℝ} (hc : 0 ≤ c)
    (h6 : (3 : ℝ) ^ m ≤ 6 * R) :
    (c * 3 ^ (d * m)) ^ (2 / (d : ℝ)) ≤ c ^ (2 / (d : ℝ)) * 36 * R ^ 2 := by
  have hdne : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  have hx : (0 : ℝ) ≤ 3 ^ m := by positivity
  have h3 : ((3 : ℝ) ^ (d * m)) = ((3 : ℝ) ^ m) ^ (d : ℝ) := by
    rw [Real.rpow_natCast, ← pow_mul, mul_comm]
  have e : (d : ℝ) * (2 / d) = 2 := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hdne, mul_one]
  have h1 : (c * (3 : ℝ) ^ (d * m)) ^ (2 / (d : ℝ)) = c ^ (2 / (d : ℝ)) * ((3 : ℝ) ^ m) ^ 2 := by
    rw [Real.mul_rpow hc (by positivity), h3, ← Real.rpow_mul hx, e, Real.rpow_two]
  rw [h1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc _)
  calc ((3 : ℝ) ^ m) ^ 2 ≤ (6 * R) ^ 2 := pow_le_pow_left₀ hx h6 2
    _ = 36 * R ^ 2 := by ring

/-- The condition of a good scale, `C 3^{dm + 2d(d+2)} < 3^{d(d+2)m}`, for `m ≥ m₀`, where
`3^{2d(d+2)} C < 3^{m₀}`. -/
theorem good_scale_of_le {m m₀ : ℕ} (hd : 0 < d) {Cf : ℝ}
    (hm₀ : (3 : ℝ) ^ (2 * (d * (d + 2))) * Cf < 3 ^ m₀) (hm : m₀ ≤ m) :
    Cf * 3 ^ (d * m + 2 * (d * (d + 2))) < 3 ^ (d * (d + 2) * m) := by
  have h1 : (3 : ℝ) ^ (2 * (d * (d + 2))) * Cf < 3 ^ m :=
    lt_of_lt_of_le hm₀ (pow_le_pow_right₀ (by norm_num) hm)
  have h2 : m + d * m ≤ d * (d + 2) * m := by
    have : d + 1 ≤ d * (d + 2) := by nlinarith
    calc m + d * m = (d + 1) * m := by ring
      _ ≤ d * (d + 2) * m := Nat.mul_le_mul_right m this
  have h3 : (3 : ℝ) ^ (m + d * m) ≤ 3 ^ (d * (d + 2) * m) := pow_le_pow_right₀ (by norm_num) h2
  have e1 : Cf * (3 : ℝ) ^ (d * m + 2 * (d * (d + 2))) =
      ((3 : ℝ) ^ (2 * (d * (d + 2))) * Cf) * 3 ^ (d * m) := by
    rw [pow_add]
    ring
  have e2 : (3 : ℝ) ^ (m + d * m) = 3 ^ m * 3 ^ (d * m) := pow_add _ _ _
  have h4 : (0 : ℝ) < 3 ^ (d * m) := by positivity
  rw [e1]
  calc ((3 : ℝ) ^ (2 * (d * (d + 2))) * Cf) * 3 ^ (d * m) < 3 ^ m * 3 ^ (d * m) :=
        mul_lt_mul_of_pos_right h1 h4
    _ = 3 ^ (m + d * m) := e2.symm
    _ ≤ 3 ^ (d * (d + 2) * m) := h3

/-- **A good ball from the estimates.** The Poincaré bound with the factor `K_S A`,
`A ≤ X R²`, the volume bounds `c_V R^d ≤ |K ∩ B_R(y)| ≤ (5R)^d` and `K_S X ≤ C`, `C⁻¹ ≤ c_V`,
`5^d ≤ C` give a good ball with constants `C⁻¹, C` and `|K ∩ B_R(y)| ≤ C R^d`. -/
theorem isGoodBall_of_bounds {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d)
    {R L C KS A X cV : ℝ} (hR : 0 ≤ R) (hKS : 0 ≤ KS)
    (hpo : ∀ u : Vertex d → ℝ, ∑ x ∈ clusterBall K y R,
      (u x - finAvg (clusterBall K y R) u) ^ 2 ≤ KS * A * nbrEnergy ω (clusterBall K y (L * R)) u)
    (hA : A ≤ X * R ^ 2) (hvol : cV * R ^ d ≤ (clusterBall K y R).card)
    (hcard : ((clusterBall K y R).card : ℝ) ≤ (5 * R) ^ d)
    (hC1 : KS * X ≤ C) (hC2 : C⁻¹ ≤ cV) (hC3 : (5 : ℝ) ^ d ≤ C) :
    IsGoodBall ω K C⁻¹ C L y R ∧ ((clusterBall K y R).card : ℝ) ≤ C * R ^ d := by
  refine ⟨⟨?_, fun u => ?_⟩, ?_⟩
  · calc C⁻¹ * R ^ d ≤ cV * R ^ d := mul_le_mul_of_nonneg_right hC2 (by positivity)
      _ ≤ _ := hvol
  · have hE := nbrEnergy_nonneg ω (clusterBall K y (L * R)) u
    calc ∑ x ∈ clusterBall K y R, (u x - finAvg (clusterBall K y R) u) ^ 2
        ≤ KS * A * nbrEnergy ω (clusterBall K y (L * R)) u := hpo u
      _ ≤ KS * (X * R ^ 2) * nbrEnergy ω (clusterBall K y (L * R)) u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hKS) hE
      _ = (KS * X) * R ^ 2 * nbrEnergy ω (clusterBall K y (L * R)) u := by ring
      _ ≤ C * R ^ 2 * nbrEnergy ω (clusterBall K y (L * R)) u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 (by positivity)) hE
  · calc ((clusterBall K y R).card : ℝ) ≤ (5 * R) ^ d := hcard
      _ = 5 ^ d * R ^ d := by ring
      _ ≤ C * R ^ d := mul_le_mul_of_nonneg_right hC3 (by positivity)

/-- **Good balls of the infinite cluster** (Barlow 2004, Theorem 2.18 (a), (b), Lemma 2.19), in
every dimension `d ≥ 2`, with dilation `L = 12 d`. -/
theorem clusterGoodBalls_holds [NeZero d] (hd : 2 ≤ d) : ClusterGoodBalls d := by
  intro p hpc hp1
  have hd0 : 0 < d := by omega
  set μ := latticeBondLaw d p with hμ
  obtain ⟨C₀, hC₀, c₀, hc₀, hq⟩ := exists_measure_not_mem_coarseGood_le hd hpc
  obtain ⟨Cfin, Ctot, hCtot, c', hc', hsum⟩ := exists_measure_sum_stoppingSize_gt_le hd0
    p coarseGood measurableSet_mem_coarseGood
    measurableSet_not_mem_coarseGood_localEdge hC₀ hc₀ one_pos le_rfl hq (d * (d + 2))
  have hH : ∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (coarseGood ω) :=
    TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched μ
      coarseGood (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top 1 c₀ one_pos hc₀ fun R => by
        rw [← ENNReal.ofReal_mul hC₀]
        exact hq R
  have hPae := ae_partitionEvent (p := p) hd hpc
  obtain ⟨KS, hKS, hdet⟩ := sum_sq_sub_finAvg_clusterBall_le hd
  obtain ⟨sD, CD, cD, hsD, hCD, hcD, hD⟩ :=
    clusterDensityInputFaithful_of_concentration cluster_density_concentration d hd p hpc hp1
  set s' : ℝ := 1 / ((2 * (d + d * (d + 2) + 1) : ℕ) : ℝ) with hs'
  have hs'0 : 0 < s' := by positivity
  set s := s' / 2 with hs
  have hs0 : 0 < s := by positivity
  set Cfp := max Cfin 0 with hCfp
  have hCfp0 : 0 ≤ Cfp := le_max_right _ _
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt ((3 : ℝ) ^ (2 * (d * (d + 2))) * Cfp)
    (by norm_num : (1 : ℝ) < 3)
  set Kp : ℝ := KS * (((3 : ℝ) ^ d * Cfp) ^ (2 / (d : ℝ)) * 36) with hKp
  set Kc : ℝ := max (max Kp (cD * 100 ^ d)⁻¹) (5 ^ d) with hKc
  have hKc1 : 1 ≤ Kc := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 5)).trans (le_max_right _ _)
  set b : ℕ → ℝ := fun m => 3 ^ d * Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ m) ^ s') with hb
  have hb0 : ∀ m, 0 ≤ b m := fun m => by positivity
  -- summability
  have hsumm : Summable fun m => b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s) := by
    set τ' := s * Real.log 3 with hτ'
    have hτ0 : 0 < τ' := mul_pos hs0 (Real.log_pos (by norm_num))
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_exp_mul_sub_sq (3 ^ s) c' τ' hc' hτ0).mul_left (3 ^ d * Ctot.toReal))
    have hv1 : ((3 : ℝ) ^ m) ^ s' = Real.exp (τ' * m) ^ 2 := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, sq, ← Real.exp_add, hτ', hs]
      congr 1
      ring
    have hv2 : ((1 : ℝ) * 3 ^ (m + 1)) ^ s = 3 ^ s * Real.exp (τ' * m) := by
      rw [scale_exponent_eq (by norm_num) m, mul_one, hτ']
    show 3 ^ d * Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ m) ^ s') *
      Real.exp ((1 * 3 ^ (m + 1)) ^ s) ≤ _
    rw [hv1, hv2]
    apply le_of_eq
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  -- the bad scales
  set Bad : Vertex d → ℕ → Set (Configuration d) := fun y m =>
    ⋃ e ∈ box (idx m y) 1, {ω | Cfin * 3 ^ (d * m) <
      ∑ x ∈ (⟨m, e⟩ : TriadicCube d).toIntegerCube.vertices,
        TriadicCube.stoppingSize (coarseGood ω) x ^ (d * (d + 2))} with hBad
  have hBadμ : ∀ y m, μ (toMeasurable μ (Bad y m)) ≤ ENNReal.ofReal (b m) := by
    intro y m
    rw [measure_toMeasurable]
    calc μ (Bad y m) ≤ ∑ e ∈ box (idx m y) 1, μ {ω | Cfin * 3 ^ (d * m) <
          ∑ x ∈ (⟨m, e⟩ : TriadicCube d).toIntegerCube.vertices,
            TriadicCube.stoppingSize (coarseGood ω) x ^ (d * (d + 2))} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _e ∈ box (idx m y) 1, Ctot * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^
          ((1 : ℝ) / ((2 * (d + d * (d + 2) + 1) : ℕ) : ℝ)))) :=
          Finset.sum_le_sum fun e _ => hsum ⟨m, e⟩
      _ = ENNReal.ofReal (b m) := by
          rw [Finset.sum_const, card_box_one_nat, hb]
          conv_lhs => rw [← ENNReal.ofReal_toReal hCtot]
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hs']
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
  refine ⟨sS, C, 12 * d, hsS0, hC0, ?_, fun y => ?_⟩
  · have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨M, hMm, hM0, hMint, hMle, hMae⟩ := exists_minimalScale_of_summable μ
    (fun m => toMeasurable μ (Bad y m)) (fun m => measurableSet_toMeasurable _ _) one_pos b hb0
    (hBadμ y) hsumm
  -- `M ≤ O_s`
  have he : (fun ω => Real.exp ((max (M ω / 1) 0).rpow s)) = fun ω => Real.exp (M ω ^ s) := by
    funext ω
    rw [div_one, max_eq_left (hM0 ω)]
    rfl
  have hMos : IsOsBond d p M s θM := by
    refine isOsBond_of_integral_le hs0 hB₁1 (by rw [he]; exact hMint) ?_
    rw [he]
    exact hMle
  have hm1 : Measurable fun ω => (3 : ℝ) ^ m₀ * M ω := measurable_const.mul hMm
  have hos1 : IsOsBond d p (fun ω => (3 : ℝ) ^ m₀ * M ω) sS θ1 :=
    IsOsBond.mono_exponent hsS0 (min_le_left _ _) hm1 (IsOsBond.const_mul (by positivity) hMos)
  obtain ⟨MD, hMDm, hMD0, hMDos, hDae⟩ := hD y
  have hosD : IsOsBond d p MD sS θD :=
    IsOsBond.mono_exponent hsS0 (min_le_right _ _) hMDm hMDos
  have hosc : IsOsBond d p (fun _ => (1 : ℝ)) sS θc := isOsBond_const one_pos hsS0
  have hos2 := IsOsBond.max hsS0 (by positivity) (by positivity) hMDm measurable_const hosD hosc
  have hos := IsOsBond.max hsS0 (by positivity) (by positivity) hm1
    (hMDm.max measurable_const) hos1 hos2
  set MP : Configuration d → ℝ := fun ω => max ((3 : ℝ) ^ m₀ * M ω) (max (MD ω) 1) with hMP
  have hMPm : Measurable MP := hm1.max (hMDm.max measurable_const)
  refine ⟨MP, hMPm, fun ω => le_max_of_le_right (le_max_of_le_right zero_le_one),
    IsOsBond.mono_scale hsS0 (by positivity) (le_max_left _ _) hMPm hos, ?_⟩
  filter_upwards [hMae, hH, hPae, hDae] with ω hMω hHω hPω hDω
  clear_value Bad b B₁ θM θ1 θD θc θ2 θP
  intro h R hR
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
  set ss : Vertex d → ℝ := fun x => TriadicCube.stoppingSize (coarseGood ω) x with hss
  have hnot : ω ∉ Bad y m := fun hb => hgoodN m (by omega) (subset_toMeasurable _ _ hb)
  have hgood : ∀ e ∈ box (idx m y) 1,
      ∑ z ∈ (⟨m, e⟩ : TriadicCube d).toIntegerCube.vertices, ss z ^ (d * (d + 2)) ≤
        Cfp * 3 ^ (d * m) := by
    intro e he
    by_contra hlt
    rw [not_le] at hlt
    apply hnot
    rw [hBad, Set.mem_iUnion₂]
    refine ⟨e, he, ?_⟩
    change Cfin * 3 ^ (d * m) < _
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hlt
  have hreach : ∀ z, partitionReach ω z ≤ ENNReal.ofReal (ss z) := fun z =>
    partitionReach_le_stoppingSize_coarseGood hHω z
  obtain ⟨H1, H2⟩ := goodScale_consequences hPω ss hreach hgood
    (good_scale_of_le hd0 hm₀ (by omega))
  have hρ : 2 * (d : ℝ) * 3 ^ m ≤ 12 * d * R := by
    calc 2 * (d : ℝ) * 3 ^ m ≤ 2 * d * (6 * R) := mul_le_mul_of_nonneg_left hm6 (by positivity)
      _ = 12 * d * R := by ring
  have hvol : cD * 100 ^ d * R ^ d ≤ (clusterBall (uniqueInfiniteComponent h) y R).card := by
    have h1 := hDω h (100 * R) (by linarith) (latticeEuclideanEmbedding y) (by
      rw [dist_self]; positivity)
    rw [show 100 * R / 100 = R by ring, ncard_eq_card_clusterBall] at h1
    calc cD * 100 ^ d * R ^ d = cD * (100 * R) ^ d := by ring
      _ ≤ _ := h1
  have hKpC : Kp ≤ C := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h5C : (5 : ℝ) ^ d ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hCinv : C⁻¹ ≤ cD * 100 ^ d := by
    rw [inv_le_comm₀ hC0 (by positivity)]
    exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  exact isGoodBall_of_bounds (uniqueInfiniteComponent h) y hR0.le hKS
    (fun u => hdet ω hPω h y m (3 ^ d * Cfp * 3 ^ (d * m)) R (12 * d * R) ss H1 hreach H2
      hm2.le hρ u)
    (rpow_two_div_le hd0 (mul_nonneg (by positivity) hCfp0) hm6) hvol
    (card_clusterBall_le _ y hR1) hKpC hCinv h5C

end Rigidity.WeakPoincare

import Rigidity.Proofs.Cluster.PlanarRHRestrictQuad
import Rigidity.Proofs.Cluster.PlanarWeakConvHolds

/-!
# Lemma 5.7 and Proposition 5.2 of Armstrong and Dario in dimension two, from `p > p_c(2)` alone

Display (5.30), the variance bound on `□_n`, display (5.25) on `□_n` and `PlanarWeakConvergence` on
every triadic cube hold above the partition `𝓡` of Definition 3.7 (`PlanarRHPartition`); the
proofs are those of `exists_lintegral_sum_subcube_solenoidal_sq_le`,
`exists_variance_planarMuGradAvg_origin_le`, `exists_lintegral_planarMuGradAvg_origin_le` and
`planarWeakConvergence_of_gehring`, with Lemma 5.5 for the pairings with a bounded field from `𝓡`
(`exists_lintegral_planarMuRestrictFieldError_le_rh`). Since `𝓡` exists for `p > p_c(2)`
(`planarRHPartition_holds`), Lemma 5.7 (`planarWeakConvergence_holds`) and, with Lemma 5.5
(`planarRestrictQuadCoarsenMu_holds`, `planarRestrictQuadCoarsenNu_holds`), the qualitative part of
Proposition 5.2 (`planarMuLimit_eq`) hold in dimension two with no other hypothesis.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

variable {ω : Configuration 2}

/-- **Display (5.30) of Armstrong and Dario** (proof of Lemma 5.7, Step 3, in dimension two), above the
partition `𝓡` of Definition 3.7. -/
theorem exists_lintegral_sum_subcube_solenoidal_sq_le_rh {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hRP : PlanarRHPartition p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 9 ≤ n → ∀ q e : Fin 2 → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n,
          edgePairing V.toIntegerCube.vertices (solenoidalField n e)
            (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ n) ^ 2) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (|e 0| + |e 1|) ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
          (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4))) := by
  obtain ⟨C₁, hC₁, hfield⟩ := exists_lintegral_planarMuRestrictFieldError_le_rh hpc hRP
  obtain ⟨C₂, hC₂, hcross⟩ := exists_lintegral_edgePairing_sub_sum_subcubes_le hpc
    (a := 4) (by norm_num)
  refine ⟨100 * (162 * C₁ + 2 * 324 * C₂.toReal), by positivity, fun n hn q e => ?_⟩
  have hWs : (⟨n + 1, 0⟩ : TriadicCube 2).scale = n + 1 := rfl
  have hnW : n ≤ (⟨n + 1, 0⟩ : TriadicCube 2).scale := by omega
  have hg := abs_solenoidalField_le n e
  have hfm : Measurable fun ω => ENNReal.ofReal 162 * ENNReal.ofReal
      (planarMuRestrictFieldError ω (⟨n + 1, 0⟩ : TriadicCube 2) n q (solenoidalField n e)) :=
    ((measurable_planarMuRestrictFieldError _ hnW q _).ennreal_ofReal).const_mul _
  have hcrossbound := hcross (⟨n + 1, 0⟩ : TriadicCube 2) n hnW q (solenoidalField n e) _ hg
  have hfieldbound := hfield (⟨n + 1, 0⟩ : TriadicCube 2) n (by rw [hWs]; omega)
    (by rw [hWs]; omega) q (solenoidalField n e) _ hg
  rw [hWs, Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty, zero_add]
    at hfieldbound
  refine (lintegral_mono fun ω => ofReal_sum_subcube_solenoidal_sq_le ω (by omega) q e).trans ?_
  rw [lintegral_add_right _ hfm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (add_le_add (mul_le_mul_of_nonneg_left hcrossbound zero_le)
    (mul_le_mul_of_nonneg_left hfieldbound zero_le)).trans ?_
  -- back to real numbers
  have hNW : ((⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ≥0∞) =
      ENNReal.ofReal ((9 : ℝ) ^ (n + 1)) := by
    rw [← ENNReal.ofReal_natCast, card_toIntegerCube_vertices_eq, hWs]
  have hvW : (⟨n + 1, 0⟩ : TriadicCube 2).volume = (9 : ℝ) ^ (n + 1) := by
    rw [TriadicCube.volume, hWs]
  rw [hNW, hvW, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  conv_lhs => rw [← ENNReal.ofReal_toReal hC₂]
  have hτx : 0 ≤ planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4) :=
    add_nonneg (planarTau_nonneg p n) (by positivity)
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg hC₁ (by positivity))
        (by positivity)) hτx))]
  refine ENNReal.ofReal_le_ofReal ?_
  set y := 2 / 81 ^ n * ((9 : ℝ) ^ (n + 1) / 3 ^ n) * 9 ^ (n + 1) *
    ((9 : ℝ) ^ (n + 1)) ^ (1 / ((4 : ℕ) : ℝ)) with hy
  have hy' : y ≤ 324 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
    rw [hy, show (1 / ((4 : ℕ) : ℝ)) = (1 / 4 : ℝ) by norm_num]
    exact crossing_arith n
  have e2 : 2 / 81 ^ n * (C₂.toReal * (10 * (|e 0| + |e 1|)) ^ 2 * (|q 0| + |q 1|) ^ 2 *
      ((9 : ℝ) ^ (n + 1) / 3 ^ n) * 9 ^ (n + 1) * ((9 : ℝ) ^ (n + 1)) ^ (1 / ((4 : ℕ) : ℝ))) =
      C₂.toReal * (10 * (|e 0| + |e 1|)) ^ 2 * (|q 0| + |q 1|) ^ 2 * y := by rw [hy]; ring
  rw [e2]
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have key := oneVarEst_arith (C₁ := C₁) (C₂ := C₂.toReal) (G := 10 * (|e 0| + |e 1|))
    (Q := (|q 0| + |q 1|) ^ 2) (P := q 0 ^ 2 + q 1 ^ 2) (τ := planarTau p n)
    (x := (3 : ℝ) ^ (-(n : ℝ) / 4)) (y := y) (K := (|e 0| + |e 1|) ^ 2)
    ENNReal.toReal_nonneg (by positivity) (planarTau_nonneg p n) hy0
    (abs_add_abs_sq_le q) hy' (by ring) (by positivity)
  calc C₂.toReal * (10 * (|e 0| + |e 1|)) ^ 2 * (|q 0| + |q 1|) ^ 2 * y +
        162 * (C₁ * (10 * (|e 0| + |e 1|)) ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
          (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4)))
      ≤ 100 * (162 * C₁ + 2 * 324 * C₂.toReal) * (|e 0| + |e 1|) ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
          (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4)) := key
    _ = _ := by ring

/-- **The variance of the spatial average on `□_n`** (proof of Lemma 5.7, in dimension two), for
`n ≥ 120`, above the partition `𝓡` of Definition 3.7. -/
theorem exists_variance_planarMuGradAvg_origin_le_rh {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hRP : PlanarRHPartition p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 120 ≤ n → ∀ (q : Fin 2 → ℝ) (j : Fin 2),
      variance (fun ω => planarMuGradAvg ω ⟨n, 0⟩ q j) (latticeBondLaw 2 p) ≤
        C * (q 0 ^ 2 + q 1 ^ 2) * (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
  obtain ⟨C₃, hC₃, h530⟩ := exists_lintegral_sum_subcube_solenoidal_sq_le_rh hpc hRP
  obtain ⟨C₄, hC₄, h531⟩ := exists_lintegral_sq_sub_switchLoc_le hpc
  refine ⟨4 * C₃ + 38 * 9 * (C₄ * 100 * 2), by positivity, fun n hn q j => ?_⟩
  set μ := latticeBondLaw 2 p with hμ
  set e : Fin 2 → ℝ := Pi.single j 1 with he
  set g := solenoidalField n e with hgdef
  set G : ℝ := 10 * (|e 0| + |e 1|) with hGdef
  have hG10 : G = 10 := by rw [hGdef, he, abs_single_sum]; ring
  have hg : ∀ x i, |g x i| ≤ G := abs_solenoidalField_le n e
  set Q := |q 0| + |q 1| with hQdef
  set P := q 0 ^ 2 + q 1 ^ 2 with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hQP : Q ^ 2 ≤ 2 * P := abs_add_abs_sq_le q
  set τx := planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4) with hτx
  have hτx0 : 0 ≤ τx := add_nonneg (planarTau_nonneg p n) (by positivity)
  have hx0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by positivity
  have hxτ : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ τx := by
    rw [hτx]; linarith [planarTau_nonneg p n]
  set s := subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n with hs
  set M := 72 * 81 ^ n * G * Q with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef, hG10]; positivity
  have hscale : ∀ V ∈ s, V.scale = n := fun V hV => scale_of_mem_subcubesAt hV
  have hi₀ : (⟨n, 0⟩ : TriadicCube 2) ∈ s := by
    have h0 : scaleCube n 0 = ⟨n, 0⟩ :=
      TriadicCube.eq_of_mem_of_scale_eq (scale_scaleCube n 0) (mem_scaleCube n 0)
        (zero_mem_originCube n)
    rw [hs, subcubesAt, ← h0]
    refine Finset.mem_image.2 ⟨0, ?_, rfl⟩
    rw [TriadicCube.mem_toIntegerCube_vertices]
    exact zero_mem_originCube (n + 1)
  -- the variables
  set X : TriadicCube 2 → Configuration 2 → ℝ := fun V => if V ∈ s then fun ω =>
    edgePairing V.toIntegerCube.vertices g (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ n
    else fun _ => 0 with hXdef
  set Y : TriadicCube 2 → Configuration 2 → ℝ := fun V => if V ∈ s then
    switchLoc (n / 12) V g q M else fun _ => 0 with hYdef
  have hXm : ∀ V, Measurable (X V) := by
    intro V
    simp only [hXdef]
    split_ifs
    · exact (measurable_edgePairing_coarsen_planarMuMinimizer subset_rfl g q).div_const _
    · exact measurable_const
  have hYm : ∀ V, Measurable (Y V) := by
    intro V
    simp only [hYdef]
    split_ifs
    · exact measurable_switchLoc _ _ _ _ _
    · exact measurable_const
  have hXb : ∀ V ω, |X V ω| ≤ M := by
    intro V ω
    simp only [hXdef]
    split_ifs with hV
    · have := abs_subcubePairing_le V q hg ω
      rwa [hscale V hV] at this
    · simpa using hM0
  have hYb : ∀ V ω, |Y V ω| ≤ M := by
    intro V ω
    simp only [hYdef]
    split_ifs with hV
    · exact abs_switchLoc_le g q hM0 ω
    · simpa using hM0
  have hind : Set.Pairwise ↑s fun V W => IndepFun (Y V) (Y W) μ := by
    intro V hV W hW hVW
    have hV := Finset.mem_coe.1 hV
    have hW := Finset.mem_coe.1 hW
    have hV' : Y V = switchLoc (n / 12) V g q M := by simp only [hYdef, if_pos hV]
    have hW' : Y W = switchLoc (n / 12) W g q M := by simp only [hYdef, if_pos hW]
    rw [hV', hW']
    refine indepFun_switchLoc p ?_ g g q M
    refine Set.disjoint_left.2 fun x hxV hxW => hVW ?_
    exact TriadicCube.eq_of_mem_of_scale_eq (by rw [hscale V hV, hscale W hW]) hxV hxW
  have hvar := variance_le_of_pairwise_indep (μ := μ) s hi₀ X Y hXm hYm hXb hYb hind
  -- the first term: display (5.30)
  have hsum : ∫ ω, (∑ V ∈ s, X V ω) ^ 2 ∂μ ≤ C₃ * P * τx := by
    have h := h530 n (by omega) q e
    rw [he, abs_single_sum] at h
    have hfun : ∀ ω, (∑ V ∈ s, X V ω) = ∑ V ∈ s, edgePairing V.toIntegerCube.vertices g
        (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ n := fun ω =>
      Finset.sum_congr rfl fun V hV => by simp only [hXdef, if_pos hV]
    simp only [hfun]
    refine integral_le_of_lintegral_le (fun ω => sq_nonneg _)
      ((Finset.measurable_sum s fun V _ =>
        (measurable_edgePairing_coarsen_planarMuMinimizer subset_rfl g q).div_const _).pow_const 2)
      (by positivity) ?_
    refine h.trans (le_of_eq ?_)
    congr 1
    ring
  -- the second term: display (5.31)
  have hloc : ∀ V ∈ s, ∫ ω, (X V ω - Y V ω) ^ 2 ∂μ ≤ C₄ * 100 * 2 * P * τx := by
    intro V hV
    have h := h531 V (by rw [hscale V hV]; exact hn) q g G hg
    rw [hscale V hV] at h
    have hfun : ∀ ω, X V ω - Y V ω = edgePairing V.toIntegerCube.vertices g
        (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ n - switchLoc (n / 12) V g q M ω :=
      fun ω => by simp only [hXdef, hYdef, if_pos hV]
    simp only [hfun]
    refine integral_le_of_lintegral_le (fun ω => sq_nonneg _)
      (((measurable_edgePairing_coarsen_planarMuMinimizer subset_rfl g q).div_const _).sub
        (measurable_switchLoc _ _ _ _ _) |>.pow_const 2) (by positivity) ?_
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hG10]
    have h1 : C₄ * 10 ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤
        C₄ * 10 ^ 2 * (2 * P) * (3 : ℝ) ^ (-(n : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQP (by positivity)) hx0
    have h2 : C₄ * 10 ^ 2 * (2 * P) * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ C₄ * 10 ^ 2 * (2 * P) * τx :=
      mul_le_mul_of_nonneg_left hxτ (by positivity)
    nlinarith
  have hcard : (s.card : ℝ) = 9 := card_subcubesAt_originCube n
  have hsum2 : ∑ V ∈ s, ∫ ω, (X V ω - Y V ω) ^ 2 ∂μ ≤ 9 * (C₄ * 100 * 2 * P * τx) := by
    refine (Finset.sum_le_sum hloc).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hX0 : X ⟨n, 0⟩ = fun ω => planarMuGradAvg ω ⟨n, 0⟩ q j := by
    funext ω
    simp only [hXdef, if_pos hi₀, planarMuGradAvg]
    rw [edgePairing_solenoidalField_origin]
    rfl
  rw [hX0] at hvar
  refine hvar.trans ?_
  rw [hcard]
  have : (4 * 9 + 2 : ℝ) = 38 := by norm_num
  rw [this]
  have e1 : (4 * C₃ + 38 * 9 * (C₄ * 100 * 2)) * P * τx =
      4 * (C₃ * P * τx) + 38 * (9 * (C₄ * 100 * 2 * P * τx)) := by ring
  rw [e1]
  have h38 := mul_le_mul_of_nonneg_left hsum2 (by norm_num : (0 : ℝ) ≤ 38)
  linarith

/-- **Display (5.25) for `□_n`**, `n ≥ 120`, above the partition `𝓡` of Definition 3.7. -/
theorem exists_lintegral_planarMuGradAvg_origin_le_rh {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hRP : PlanarRHPartition p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 120 ≤ n → ∀ q : Fin 2 → ℝ,
      ∫⁻ ω, ENNReal.ofReal (∑ j : Fin 2,
          (planarMuGradAvg ω ⟨n, 0⟩ q j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2)
          ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) *
          (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4))) := by
  obtain ⟨C, hC, hvar⟩ := exists_variance_planarMuGradAvg_origin_le_rh hpc hRP
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

/-- **Lemma 5.7 of Armstrong and Dario** (display (5.25), in dimension two), for every triadic cube,
above the partition `𝓡` of Definition 3.7. -/
theorem planarWeakConvergence_of_rhPartition {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hRP : PlanarRHPartition p) :
    PlanarWeakConvergence p := by
  obtain ⟨C₀, hC₀, horig⟩ := exists_lintegral_planarMuGradAvg_origin_le_rh hpc hRP
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

/-- **Lemma 5.7 of Armstrong and Dario** (display (5.25), in dimension two), for every triadic cube,
for `p > p_c(2)`. -/
theorem planarWeakConvergence_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarWeakConvergence p :=
  planarWeakConvergence_of_rhPartition hpc (planarRHPartition_holds hpc)

/-- **Proposition 5.2 of Armstrong and Dario, qualitative part** (dimension two), for
`p > p_c(2)`: `lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q`. -/
theorem planarMuLimit_eq {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) :
    planarMuLimit p q = 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i :=
  planarMuLimit_eq_of_inputs hpc (planarWeakConvergence_holds hpc)
    (planarRestrictQuadCoarsenMu_holds hpc) (planarRestrictQuadCoarsenNu_holds hpc) q

end Rigidity.Proofs.Cluster

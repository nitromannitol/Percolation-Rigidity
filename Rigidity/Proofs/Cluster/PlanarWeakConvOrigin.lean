import Rigidity.Proofs.Cluster.PlanarWeakConvVariance

/-!
# Lemma 5.7 of Armstrong and Dario for the cube centred at the origin

For `n ≥ 120`, the variance of the spatial average `|□_n|⁻¹ ⟨e_j, ∇[u(·, □_n, q)]_𝒫⟩_{□_n}` is at
most `C |q|² (τ_n + 3^{-n/4})` (`exists_variance_planarMuGradAvg_origin_le`), from display (5.30)
for the sum over the nine subcubes of `□_{n+1}` of the pairings with the solenoidal field, which
equals `e_j` on `□_n`, display (5.31) for each subcube and the variance step. Since the mean of
the spatial average is `ā_{□_n}⁻¹ q` (display (5.23)), this is display (5.25) for `□_n`
(`exists_lintegral_planarMuGradAvg_origin_le`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

variable {ω : Configuration 2}

/-- On `□_n` the solenoidal field of scale `n` in direction `e` is `e`, so its pairing with the
coarsened gradient is the coarse pairing with `e`. -/
theorem edgePairing_solenoidalField_origin (n : ℕ) (e : Fin 2 → ℝ)
    (u : ClusterFun ω (⟨n, 0⟩ : TriadicCube 2)) :
    edgePairing (⟨n, 0⟩ : TriadicCube 2).toIntegerCube.vertices (solenoidalField n e)
      (coarsen ω ⟨n, 0⟩ u) = coarsePairing ω ⟨n, 0⟩ e u := by
  rw [subcubePairing_eq, ← fieldPairing_const, fieldPairing_eq_sum_latticeEdgesIn,
    fieldPairing_eq_sum_latticeEdgesIn]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, _⟩ := Finset.mem_filter.1 hk
  have hx := (Finset.mem_product.1 hk1).1
  rw [TriadicCube.mem_toIntegerCube_vertices] at hx
  have hb : ∀ i, |(k.1 i : ℝ)| + 1 ≤ 3 ^ n := by
    intro i
    have h := hx i
    change |2 * (k.1 i - (3 : ℤ) ^ n * 0)| < 3 ^ n at h
    simp only [mul_zero, sub_zero, abs_mul, abs_two] at h
    have h1 : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    have h2 : |k.1 i| + 1 ≤ 3 ^ n := by linarith
    have h3 : ((|k.1 i| + 1 : ℤ) : ℝ) ≤ ((3 ^ n : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    exact h3
  have hs : supNorm k.1 + 1 ≤ 3 ^ n := by
    unfold supNorm
    rcases le_total |(k.1 0 : ℝ)| |(k.1 1 : ℝ)| with h | h
    · rw [max_eq_right h]; exact hb 1
    · rw [max_eq_left h]; exact hb 0
  rw [solenoidalField_eq e hs k.2]

theorem zero_mem_originCube (m : ℕ) : (0 : Vertex 2) ∈ (⟨m, 0⟩ : TriadicCube 2).vertices := by
  intro i
  change |2 * ((0 : Vertex 2) i - (3 : ℤ) ^ m * (0 : Vertex 2) i)| < 3 ^ m
  simp only [Pi.zero_apply, mul_zero, sub_zero, abs_zero]
  positivity

theorem abs_single_sum (j : Fin 2) :
    |(Pi.single j (1 : ℝ) : Fin 2 → ℝ) 0| + |(Pi.single j (1 : ℝ) : Fin 2 → ℝ) 1| = 1 := by
  fin_cases j <;> simp

/-- The nonnegative integral bounded through the lower integral. -/
theorem integral_le_of_lintegral_le {μ : Measure (Configuration 2)} {f : Configuration 2 → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfm : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal B) : ∫ ω, f ω ∂μ ≤ B := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB h

/-- **The variance of the spatial average on `□_n`** (proof of Lemma 5.7, conclusion, in
dimension two), for `n ≥ 120`, from the partition for the reverse Hölder inequality. -/
theorem exists_variance_planarMuGradAvg_origin_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 120 ≤ n → ∀ (q : Fin 2 → ℝ) (j : Fin 2),
      variance (fun ω => planarMuGradAvg ω ⟨n, 0⟩ q j) (latticeBondLaw 2 p) ≤
        C * (q 0 ^ 2 + q 1 ^ 2) * (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
  obtain ⟨C₃, hC₃, h530⟩ := exists_lintegral_sum_subcube_solenoidal_sq_le hpc hG
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

end Rigidity.Proofs.Cluster

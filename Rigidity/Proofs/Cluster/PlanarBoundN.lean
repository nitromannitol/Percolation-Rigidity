import Rigidity.Proofs.Cluster.PlanarSubaddTail

/-!
# Proposition 5.13 of Armstrong and Dario in dimension two

The tails of Proposition 5.2 on the cubes `□_m` at the origin (`exists_planarSubaddGood_tail`)
extend to every triadic cube (`exists_planarSubaddGood_tail_cube`): on the good event of the
stationary local versions, `μ(V, ·)` and `ν(V, ·)` are the values on `□_{scale V}` in the
configuration translated by `-center V` (`planarSubaddGood_of_statGood`), and the bond law is
translation invariant. With `n = ⌈m/4⌉` the bad event at scale `m` (some subcube of scale `n` of
`□_m`, or some translate `z + □_n`, `z ∈ □_m`, fails the bounds) has probability at most
`C exp(-c 3^{m s/4})`, and the random scale `𝒩 = 3 sup {3^m : bad at m}` is `O_r(θ)` by Lemma 2.3
(`exceptionalScale_exp_moment`). This is `PlanarBoundN` (`planarBoundN_holds`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

variable {ω : Configuration 2}

/-- **Transport of Proposition 5.2 by a translation** on the good event of the stationary local
versions. -/
theorem planarSubaddGood_of_statGood {p : unitInterval} {V : TriadicCube 2} {K β : ℝ}
    (hSG : PlanarStatGood ω V)
    (hG : PlanarSubaddGood p (configurationTranslation (-V.center) ω) V.originCube K β) :
    PlanarSubaddGood p ω V K β := by
  set ω' := configurationTranslation (-V.center) ω with hω'
  have hω : configurationTranslation V.center ω' = ω := by
    rw [hω', configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]
  have hz : ∀ i, V.originCube.side ∣ V.center i := V.originCube_side_dvd_center
  have hz' : ∀ i, (3 : ℤ) ^ V.originCube.scale ∣ V.center i := hz
  have hLG' : PlanarLocalGood ω' V.originCube := hSG.2
  have hLG : PlanarLocalGood (configurationTranslation V.center ω')
      (V.originCube.shift V.center) := by
    rw [hω, V.originCube_shift_center]; exact hSG.1
  have hpart : ∀ x ∈ V.originCube.vertices,
      planarPartCube (configurationTranslation V.center ω') (x + V.center) =
        (planarPartCube ω' x).shift V.center := by
    intro x hx
    rw [planarPartCube_eq_cappedCube hLG ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      planarPartCube_eq_cappedCube hLG' hx]
    exact cappedCube_planarGoodCubes_translation hz' ω' x
  obtain ⟨hP', hres', hμ, hν⟩ := hG
  have hres := (planarResolved_shift_iff hz hpart).2 hres'
  have hμe := planarMu_shift_translation hP' hres' hz hpart
  have hνe := planarNu_shift_translation hP' hres' hz hpart
  rw [hω, V.originCube_shift_center] at hres hμe hνe
  refine ⟨hSG.1.1, hres, fun q => ?_, fun ξ => ?_⟩
  · rw [hμe q]; exact hμ q
  · rw [hνe ξ]; exact hν ξ

theorem measure_preimage_configurationTranslation (p : unitInterval) (z : Vertex 2)
    (s : Set (Configuration 2)) :
    latticeBondLaw 2 p (configurationTranslation z ⁻¹' s) = latticeBondLaw 2 p s :=
  (measurePreserving_configurationTranslation p z).measure_preimage_emb
    (configurationTranslationMeasurableEquiv z).measurableEmbedding s

/-- **Proposition 5.2 with stretched-exponential tails on every triadic cube.** -/
theorem exists_planarSubaddGood_tail_cube {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K β s c K' : ℝ, 0 ≤ K ∧ 0 < β ∧ 0 < s ∧ s ≤ 1 ∧ 0 < c ∧ 0 ≤ K' ∧
      (∀ (m : ℕ) (z : Vertex 2), latticeBondLaw 2 p
        {ω | ¬ PlanarSubaddGood p (configurationTranslation z ω) ⟨m, 0⟩ K β} ≤
          ENNReal.ofReal (K' * Real.exp (-c * ((3 : ℝ) ^ m) ^ s))) ∧
      ∀ V : TriadicCube 2, latticeBondLaw 2 p {ω | ¬ PlanarSubaddGood p ω V K β} ≤
        ENNReal.ofReal (2 * K' * Real.exp (-c * ((3 : ℝ) ^ V.scale) ^ s)) := by
  obtain ⟨K, β, s, c, K', hK, hβ, hs0, hs1, hc, hK', htail⟩ := exists_planarSubaddGood_tail hpc
  obtain ⟨C₂, hC₂, c₂, hc₂, hgood⟩ := exists_measure_not_planarStatGood_le hpc
  -- the stationary good event, in the form of a stretched exponential
  set c' : ℝ := min c c₂ with hc'
  have hc'0 : 0 < c' := lt_min hc hc₂
  set K'' : ℝ := max K' (2 * C₂.toReal) with hK''
  refine ⟨K, β, s, c', K'', hK, hβ, hs0, hs1, hc'0, le_max_of_le_left hK', fun m z => ?_,
    fun V => ?_⟩
  · have h := htail m
    rw [← measure_preimage_configurationTranslation p z] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (le_max_of_le_left hK')
    have : 0 ≤ ((3 : ℝ) ^ m) ^ s := by positivity
    nlinarith [min_le_left c c₂]
  · set ω₀ := fun ω : Configuration 2 => configurationTranslation (-V.center) ω
    have hsub : {ω | ¬ PlanarSubaddGood p ω V K β} ⊆ {ω | ¬ PlanarStatGood ω V} ∪
        configurationTranslation (-V.center) ⁻¹'
          {ω | ¬ PlanarSubaddGood p ω ⟨V.scale, 0⟩ K β} := by
      intro ω hω
      by_contra hne
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage, not_or, not_not] at hne
      exact hω (planarSubaddGood_of_statGood hne.1 hne.2)
    have hX0 : 0 ≤ ((3 : ℝ) ^ V.scale) ^ s := by positivity
    have h1 : latticeBondLaw 2 p {ω | ¬ PlanarStatGood ω V} ≤
        ENNReal.ofReal (K'' * Real.exp (-c' * ((3 : ℝ) ^ V.scale) ^ s)) := by
      refine (hgood V).trans ?_
      rw [show (2 : ℝ≥0∞) * C₂ = ENNReal.ofReal (2 * C₂.toReal) by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hC₂, ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        (le_max_of_le_left hK')
      have h3 : ((3 : ℝ) ^ V.scale) ^ s ≤ (3 : ℝ) ^ V.scale := by
        calc ((3 : ℝ) ^ V.scale) ^ s ≤ ((3 : ℝ) ^ V.scale) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hs1
          _ = _ := Real.rpow_one _
      nlinarith [min_le_right c c₂]
    have h2 : latticeBondLaw 2 p (configurationTranslation (-V.center) ⁻¹'
          {ω | ¬ PlanarSubaddGood p ω ⟨V.scale, 0⟩ K β}) ≤
        ENNReal.ofReal (K'' * Real.exp (-c' * ((3 : ℝ) ^ V.scale) ^ s)) := by
      rw [measure_preimage_configurationTranslation]
      refine (htail V.scale).trans (ENNReal.ofReal_le_ofReal ?_)
      apply mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        (le_max_of_le_left hK')
      nlinarith [min_le_left c c₂]
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add h1 h2).trans ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    linarith

theorem center_mem_vertices (V : TriadicCube 2) : V.center ∈ V.vertices := by
  intro i
  change |2 * (V.side * V.index i - V.side * V.index i)| < V.side
  simp [V.side_pos]

/-- A triadic cube of scale `n` inside `U` is a subcube of `U` of scale `n`. -/
theorem mem_subcubesAt_of_subset {U V : TriadicCube 2} {n : ℕ} (hV : V.scale = n)
    (hVU : V.vertices ⊆ U.vertices) : V ∈ subcubesAt U n := by
  refine Finset.mem_image.2 ⟨V.center, (U.mem_toIntegerCube_vertices _).2
    (hVU (center_mem_vertices V)), ?_⟩
  exact TriadicCube.eq_of_mem_of_scale_eq (by rw [scale_scaleCube, hV]) (mem_scaleCube n _)
    (center_mem_vertices V)

/-- **Proposition 5.13 of Armstrong and Dario for a general mesoscopic scale** (dimension two,
`p > p_c(2)`): for every scale `n(m) ≤ m` with `m ≤ L n(m)` there is a random scale `𝒩 ≤ O_r(θ)`
such that, whenever `𝒩 ≤ 3ᵐ`, Proposition 5.2 holds at level `K 3^{-β n(m)}` on every triadic
subcube of `□_m` of scale `n(m)` and on `□_{n(m)}` in the configuration translated by `-z`, for
every `z ∈ □_m`. -/
theorem exists_planarBoundN_general {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {L : ℕ} (hL : 0 < L) (nf : ℕ → ℕ) (hnf : ∀ m, nf m ≤ m ∧ m ≤ L * nf m) :
    ∃ K β r θ : ℝ, 0 ≤ K ∧ 0 < β ∧ 0 < r ∧ 0 < θ ∧
      ∃ N : Configuration 2 → ℝ, Measurable N ∧ (∀ ω, 0 ≤ N ω) ∧ IsOsBond 2 p N r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ m : ℕ, N ω ≤ 3 ^ m →
          (∀ V : TriadicCube 2, V.scale = nf m →
            V.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices → PlanarSubaddGood p ω V K β) ∧
          ∀ z ∈ (⟨m, 0⟩ : TriadicCube 2).vertices,
            PlanarSubaddGood p (configurationTranslation (-z) ω) ⟨nf m, 0⟩ K β := by
  obtain ⟨K, β, s, c, K', hK, hβ, hs0, hs1, hc, hK', htr, hcube⟩ :=
    exists_planarSubaddGood_tail_cube hpc
  set μ := latticeBondLaw 2 p with hμ
  obtain ⟨bad, hbad⟩ : ∃ bad : ℕ → Set (Configuration 2), ∀ m, bad m = {ω |
      ¬ ((∀ V : TriadicCube 2, V.scale = nf m →
          V.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices → PlanarSubaddGood p ω V K β) ∧
        ∀ z ∈ (⟨m, 0⟩ : TriadicCube 2).vertices,
          PlanarSubaddGood p (configurationTranslation (-z) ω) ⟨nf m, 0⟩ K β)} :=
    ⟨_, fun _ => rfl⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hs'0 : 0 < s / L := by positivity
  obtain ⟨K₁, hK₁, h₁⟩ := exists_nine_pow_mul_exp_rpow_le hc hs'0
  -- the bad events are rare
  have hbadm : ∀ m, μ (bad m) ≤ ENNReal.ofReal (3 * K' * K₁) *
      ENNReal.ofReal (Real.exp (-(c / 2) * ((3 : ℝ) ^ m) ^ (s / L))) := by
    intro m
    rw [hbad]
    have hnm : nf m ≤ (⟨m, 0⟩ : TriadicCube 2).scale := (hnf m).1
    have hLn : (m : ℝ) ≤ L * (nf m : ℝ) := by exact_mod_cast (hnf m).2
    generalize nf m = n at hnm hLn ⊢
    have hsub : {ω | ¬ ((∀ V : TriadicCube 2, V.scale = n →
          V.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices → PlanarSubaddGood p ω V K β) ∧
        ∀ z ∈ (⟨m, 0⟩ : TriadicCube 2).vertices,
          PlanarSubaddGood p (configurationTranslation (-z) ω) ⟨n, 0⟩ K β)} ⊆
        (⋃ V ∈ subcubesAt (⟨m, 0⟩ : TriadicCube 2) n,
          {ω | ¬ PlanarSubaddGood p ω V K β}) ∪
        ⋃ z ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
          {ω | ¬ PlanarSubaddGood p (configurationTranslation (-z) ω) ⟨n, 0⟩ K β} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      by_contra hne
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
        not_not] at hne
      apply hω
      refine ⟨fun V hV hVU => hne.1 V (mem_subcubesAt_of_subset hV hVU), fun z hz => ?_⟩
      exact hne.2 z ((TriadicCube.mem_toIntegerCube_vertices _ z).2 hz)
    have hX : ((3 : ℝ) ^ m) ^ (s / L) ≤ ((3 : ℝ) ^ n) ^ s := by
      rw [three_rpow_natCast_mul, three_rpow_natCast_mul]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [mul_div_assoc', div_le_iff₀ hL0]
      nlinarith
    have hcard : ((subcubesAt (⟨m, 0⟩ : TriadicCube 2) n).card : ℝ) ≤ 9 ^ m := by
      have h := card_subcubesAt_mul hnm
      have hv : (⟨m, 0⟩ : TriadicCube 2).volume = (9 : ℝ) ^ m := rfl
      rw [hv] at h
      have h9 : (1 : ℝ) ≤ 9 ^ n := one_le_pow₀ (by norm_num)
      nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (subcubesAt (⟨m, 0⟩ : TriadicCube 2) n).card)]
    have hcardU : (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℕ) : ℝ) = 9 ^ m :=
      card_toIntegerCube_vertices_eq _
    have hA : μ (⋃ V ∈ subcubesAt (⟨m, 0⟩ : TriadicCube 2) n,
        {ω | ¬ PlanarSubaddGood p ω V K β}) ≤
        ENNReal.ofReal ((9 : ℝ) ^ m * (2 * K' * Real.exp (-c * ((3 : ℝ) ^ n) ^ s))) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine (sum_le_ofReal_card_mul _ _ fun V hV => ?_).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity)))
      have := hcube V
      rwa [scale_of_mem_subcubesAt hV] at this
    have hB : μ (⋃ z ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        {ω | ¬ PlanarSubaddGood p (configurationTranslation (-z) ω) ⟨n, 0⟩ K β}) ≤
        ENNReal.ofReal ((9 : ℝ) ^ m * (K' * Real.exp (-c * ((3 : ℝ) ^ n) ^ s))) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine (sum_le_ofReal_card_mul _ _ fun z _ => htr n (-z)).trans
        (le_of_eq (by rw [hcardU]))
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hA hB).trans ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := h₁ m
    have he' : Real.exp (-c * ((3 : ℝ) ^ n) ^ s) ≤ Real.exp (-c * ((3 : ℝ) ^ m) ^ (s / L)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h9 : (0 : ℝ) ≤ 9 ^ m := by positivity
    have h2 : (9 : ℝ) ^ m * Real.exp (-c * ((3 : ℝ) ^ n) ^ s) ≤
        K₁ * Real.exp (-(c / 2) * ((3 : ℝ) ^ m) ^ (s / L)) :=
      (mul_le_mul_of_nonneg_left he' h9).trans h1
    have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 3 * K' by positivity)
    nlinarith
  -- the random scale
  set E : ℕ → Set (Configuration 2) := fun m => toMeasurable μ (bad m) with hE
  have hEm : ∀ m, MeasurableSet (E m) := fun m => measurableSet_toMeasurable _ _
  have hEμ : ∀ m, μ (E m) ≤ ENNReal.ofReal (3 * K' * K₁) *
      ENNReal.ofReal (Real.exp (-(c / 2) * ((3 : ℝ) ^ m) ^ (s / L))) := fun m => by
    rw [hE, measure_toMeasurable]; exact hbadm m
  obtain ⟨θ, hθ, hint, hle⟩ := exceptionalScale_exp_moment μ E hEm _ ENNReal.ofReal_ne_top
    (s / L) (c / 2) hs'0 (by positivity) hEμ
  have hfin : ∀ᵐ ω ∂μ, exceptionalScale E ω ≠ ∞ :=
    ae_exceptionalScale_ne_top μ E _ ENNReal.ofReal_ne_top ((3 : ℝ) ^ (s / L)) (c / 2)
      (Real.one_lt_rpow (by norm_num) hs'0) (by positivity) (fun m => by
        rw [Real.rpow_pow_comm (show (0 : ℝ) ≤ 3 by norm_num) (s / L) m]
        exact hEμ m)
  have hos := isOsBond_toReal_of_exp_moment (p := p) hθ hint hle
  refine ⟨K, β, s / L, 3 * θ, hK, hβ, hs'0, by positivity,
    fun ω => 3 * (exceptionalScale E ω).toReal,
    ((measurable_exceptionalScale E hEm).ennreal_toReal).const_mul 3,
    fun ω => by positivity, Rigidity.Proofs.S2.IsOsBond.const_mul (by norm_num) hos, ?_⟩
  filter_upwards [hfin] with ω hω m hm
  have hlt : exceptionalScale E ω < 3 ^ m := by
    have h1 : (exceptionalScale E ω).toReal < (3 : ℝ) ^ m := by
      have := ENNReal.toReal_nonneg (a := exceptionalScale E ω)
      have h3 : (0 : ℝ) < 3 ^ m := by positivity
      linarith
    rw [← ENNReal.ofReal_toReal hω, ennreal_three_pow_eq_ofReal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 h1
  have hnot : ω ∉ bad m := by
    intro hb
    have hωE : ω ∈ E m := subset_toMeasurable μ (bad m) hb
    have h3 : (3 : ℝ≥0∞) ^ m ≤ exceptionalScale E ω := by
      unfold exceptionalScale
      exact le_iSup_of_le m (by rw [if_pos hωE])
    exact absurd hlt (not_lt.2 h3)
  by_contra h
  exact hnot (by rw [hbad]; exact h)

/-- Proposition 5.2 at level `K 3^{-β n}` with `m ≤ L n` gives the level `K 3^{-(β/L) m}`. -/
theorem PlanarSubaddGood.mono_scale {p : unitInterval} {V : TriadicCube 2} {K β : ℝ} {L m : ℕ}
    (hK : 0 ≤ K) (hβ : 0 < β) (hL : 0 < L) (hm : m ≤ L * V.scale)
    (h : PlanarSubaddGood p ω V K β) :
    PlanarPartitionEvent ω ∧ PlanarResolved ω V ∧
      (∀ q : Fin 2 → ℝ, |planarMu ω V q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
        K * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * (β / L))) ∧
      ∀ ξ : Fin 2 → ℝ, |planarNu ω V ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
        K * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * (β / L)) := by
  obtain ⟨hP, hres, hμb, hνb⟩ := h
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have he : (3 : ℝ) ^ (-(V.scale : ℝ) * β) ≤ (3 : ℝ) ^ (-(m : ℝ) * (β / L)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hm' : (m : ℝ) ≤ L * V.scale := by exact_mod_cast hm
    have : (m : ℝ) * (β / L) ≤ V.scale * β := by
      rw [mul_div_assoc', div_le_iff₀ hL0]
      nlinarith
    linarith
  refine ⟨hP, hres, fun q => (hμb q).trans ?_, fun ξ => (hνb ξ).trans ?_⟩
  · exact mul_le_mul_of_nonneg_left he (by positivity)
  · exact mul_le_mul_of_nonneg_left he (by positivity)

/-- **Armstrong and Dario, Proposition 5.13** (dimension two, `p > p_c(2)`). -/
theorem planarBoundN_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarBoundN p := by
  obtain ⟨K, β, r, θ, hK, hβ, hr, hθ, N, hNm, hN0, hNos, hN⟩ :=
    exists_planarBoundN_general hpc (L := 4) (by norm_num) (fun m => (m + 3) / 4)
      (fun m => ⟨by omega, by omega⟩)
  refine ⟨β / 4, r, θ, K, by positivity, hr, hθ, hK, N, hNm, hN0, hNos, ?_⟩
  filter_upwards [hN] with ω hω m hm
  obtain ⟨h1, h2⟩ := hω m hm
  refine ⟨fun V hV hVU => ?_, fun z hz => ?_⟩
  · have := (h1 V hV hVU).mono_scale (L := 4) (m := m) hK hβ (by norm_num) (by rw [hV]; omega)
    simpa using this
  · have := (h2 z hz).mono_scale (L := 4) (m := m) hK hβ (by norm_num)
      (show m ≤ 4 * ((m + 3) / 4) by omega)
    simpa using this

end Rigidity.Proofs.Cluster

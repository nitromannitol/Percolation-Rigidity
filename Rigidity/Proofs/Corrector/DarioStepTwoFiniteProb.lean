import Rigidity.Proofs.Corrector.DarioStepTwoFiniteWeight

/-!
# The good events of the finite-range weight are likely

* `measure_not_farGood_le`: an edge with its tail `v` outside `B(u, R)` reaching `u` needs
  `|u - v| ≤ 6κ σ(v)`, so a union bound with the exponential tail of the planar partition sizes
  gives `P(¬ FarGood) ≤ 8 (1 + 24κθ)² e^{-R/(12κθ)}`;
* `measure_not_sideGood_le`: a difference between the side and the capped side at a vertex of
  `B(u, R)` is a discrepancy of the capped partition, of probability `(2R + 1)² C e^{-c 3ⁿ}`;
* `measure_not_gradGood_le`: a failure of the local gradient bound at a site of `B(u, R + 3κR)` is
  a failure of `LocalGradGood` for the configuration seen from the site, which has the law of the
  configuration.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem norm_emb_sub_comm (a b : Vertex 2) :
    ‖latticeEuclideanEmbedding (a - b)‖ = ‖latticeEuclideanEmbedding (b - a)‖ := by
  have : latticeEuclideanEmbedding (a - b) = -latticeEuclideanEmbedding (b - a) := by
    ext k; simp [latticeEuclideanEmbedding]
  rw [this, norm_neg]

theorem lt_norm_of_not_mem_supBox {u v : Vertex 2} {R : ℕ} (h : v ∉ supBox u R) :
    (R : ℝ) < ‖latticeEuclideanEmbedding (v - u)‖ := by
  rw [mem_supBox] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h1 := abs_coord_le_norm (v - u) i
  have h2 : (R : ℝ) < |(((v - u) i : ℤ) : ℝ)| := by
    simp only [Pi.sub_apply]
    exact_mod_cast hi
  linarith

/-- **Far edges do not reach `u`, with high probability.** -/
theorem measure_not_farGood_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (κ R : ℕ), 1 ≤ κ → ∀ u : Vertex 2,
      latticeBondLaw 2 p {ω | PlanarPartitionEvent ω ∧ ¬ FarGood κ R ω u} ≤
        ENNReal.ofReal (8 * (1 + 2 * (2 * (6 * κ * θ))) ^ 2 *
          Real.exp (-(R / (2 * (6 * κ * θ))))) := by
  obtain ⟨θ', hθ', hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  refine ⟨θ', hθ', fun κ R hκ u => ?_⟩
  have hK : (0 : ℝ) < 6 * κ := by positivity
  set c := 6 * κ * θ' with hc
  have hc0 : 0 < c := by positivity
  have hsub : {ω | PlanarPartitionEvent ω ∧ ¬ FarGood κ R ω u} ⊆
      ⋃ v, {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
        6 * κ * TriadicCube.stoppingSize (planarGoodCubes ω) v} := by
    rintro ω ⟨hP, hfar⟩
    unfold FarGood at hfar
    push Not at hfar
    obtain ⟨v, hv, hvR⟩ := hfar
    refine Set.mem_iUnion.2 ⟨v, hvR, ?_⟩
    have h1 := norm_le_of_mem_supBox hv
    rw [norm_emb_sub_comm, stoppingSize_eq_planarSide hP]
    push_cast at h1
    linarith
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
  have hv : ∀ v, latticeBondLaw 2 p {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
      6 * κ * TriadicCube.stoppingSize (planarGoodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(R / (2 * c)))) *
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * c))) := by
    intro v
    by_cases hvR : v ∈ supBox u R
    · have : {ω : Configuration 2 | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
          6 * κ * TriadicCube.stoppingSize (planarGoodCubes ω) v} = ∅ := by
        ext ω; simp [hvR]
      rw [this, measure_empty]
      positivity
    · have hR := lt_norm_of_not_mem_supBox hvR
      set t := ‖latticeEuclideanEmbedding (v - u)‖
      have hm := measure_le_mul_stoppingSize_le hθ' hK v (hexp v).1 (hexp v).2 t
      refine (measure_mono fun ω hω => hω.2).trans (hm.trans ?_)
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (R : ℝ) / (2 * c) ≤ t / (2 * c) := div_le_div_of_nonneg_right hR.le (by positivity)
      have e : t / c = t / (2 * c) + t / (2 * c) := by field_simp; ring
      have key : -(t / c) ≤ -(R / (2 * c)) + -t / (2 * c) := by
        rw [e, neg_div]; linarith
      calc 2 * Real.exp (-(t / c)) ≤ 2 * Real.exp (-(R / (2 * c)) + -t / (2 * c)) := by
            gcongr
        _ = 2 * Real.exp (-(R / (2 * c))) * Real.exp (-t / (2 * c)) := by
            rw [Real.exp_add]; ring
  refine (ENNReal.tsum_le_tsum hv).trans ?_
  rw [ENNReal.tsum_mul_left]
  have hs := tsum_exp_neg_norm_sub_le u (κ := 2 * c) (by positivity)
  calc ENNReal.ofReal (2 * Real.exp (-(R / (2 * c)))) *
        ∑' v, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * c)))
      ≤ ENNReal.ofReal (2 * Real.exp (-(R / (2 * c)))) *
        ENNReal.ofReal (4 * (1 + 2 * (2 * c)) ^ 2) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring


theorem lt_three_mul_three_pow_capScale (R : ℕ) : R < 3 * 3 ^ capScale R := by
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) R
  rw [pow_succ] at this
  unfold capScale
  omega

/-- **The capped sides are the sides near `u`, with high probability.** -/
theorem measure_not_sideGood_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (R : ℕ) (u : Vertex 2),
      latticeBondLaw 2 p {ω | PlanarPartitionEvent ω ∧ ¬ SideGood R ω u} ≤
        ((2 * R + 1) ^ 2 : ℕ) * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ capScale R))) := by
  obtain ⟨C, hC, c, hc, hD⟩ := measure_exists_planarCappedDiscrepancy_le hpc
  refine ⟨C, hC, c, hc, fun R u => (measure_mono ?_).trans (hD (capScale R) u R)⟩
  rintro ω ⟨hP, hs⟩
  unfold SideGood at hs
  push Not at hs
  obtain ⟨v, hv, hne⟩ := hs
  exact ⟨v, hv, not_not.1 fun hd => hne (planarSide_eq_cappedSide hP hd)⟩

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The local gradient bounds dominate the plane gradient bound near `u`, with high
probability.** -/
theorem measure_not_gradGood_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ C₁ c₁ s δ C₂ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ 0 < s ∧ 0 < δ ∧ 0 < C₂ ∧ ∀ (κ R : ℕ) (i : Fin 2),
      1 ≤ R → ∀ u : Vertex 2,
        latticeBondLaw 2 p {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u} ≤
          ((2 * (R + 3 * κ * R) + 1) ^ 2 : ℕ) *
            ENNReal.ofReal ((2 * R + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) +
              2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s)) := by
  obtain ⟨C₁, c₁, s, δ, C₂, h1, h2, h3, h4, h5, hL⟩ :=
    measure_not_localGradGood_le hG hGv hpc hp1
  refine ⟨C₁, c₁, s, δ, C₂, h1, h2, h3, h4, h5, fun κ R i hR u => ?_⟩
  have hG0 : latticeBondLaw 2 p Gᶜ = 0 := ae_iff.1 hGae
  have hsub : {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u} ⊆
      ⋃ z ∈ supBox u (R + 3 * κ * R), (configurationTranslation (-z) ⁻¹' Gᶜ ∪
        configurationTranslation (-z) ⁻¹' {ω | ω ∈ G ∧ ¬ LocalGradGood hG hGv i R ω}) := by
    rintro ω ⟨hω, hg⟩
    unfold GradGood at hg
    push Not at hg
    obtain ⟨z, hz, hlt⟩ := hg
    refine Set.mem_iUnion₂.2 ⟨z, hz, ?_⟩
    by_cases hτ : configurationTranslation (-z) ω ∈ G
    · exact Or.inr ⟨hτ, fun hgood =>
        absurd (planeGrad_le_siteGrad hG hGv hω hR hτ hgood) (not_le.2 hlt)⟩
    · exact Or.inl hτ
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc _ ≤ ∑ _z ∈ supBox u (R + 3 * κ * R),
        ENNReal.ofReal ((2 * R + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s)) :=
        Finset.sum_le_sum fun z _ => by
          have hmp := measurePreserving_configurationTranslation p (-z)
          refine (measure_union_le _ _).trans
            ((add_le_add (hmp.measure_preimage_le _) (hmp.measure_preimage_le _)).trans ?_)
          rw [hG0, zero_add]
          exact hL i R hR
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_supBox]

end Grad

end Rigidity.Corrector

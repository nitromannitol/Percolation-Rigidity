import Rigidity.Proofs.Corrector.DarioStepTwoFiniteProb

/-!
# The moments of the finite-range weight

With `Λ_R(z) = 4 + 4 J_R(z)` (`siteLambda`), the moments of `1 + Λ_R(z)` are `(5B q^κ)^q` uniformly
in `R` and `z`, since the configuration seen from `z` has the law of the configuration
(`growthMoments_siteLambda`). When the capped sides are the sides near `u`, the finite-range
weight is at most the majorant `weightMajorant Λ_R (6κ) (6κ) u` (`finiteWeight_le_weightMajorant`);
otherwise it is at most a power of `R`, on an event of probability `(2R + 1)² C e^{-c R/3}`. Hence
`E[W_R(u)^q] ≤ M₀` uniformly in `R ≥ 1` and `u` (`exists_lintegral_finiteWeight_rpow_le`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

/-- The shifted local gradient bounds at the sites, `Λ_R(z) = 4 + 4 J_R(z)`. -/
noncomputable def siteLambda (R : ℕ) (z : Vertex 2) (ω : Configuration 2) : ℝ :=
  4 + 4 * siteGrad R ω z

theorem measurable_siteLambda (R : ℕ) (z : Vertex 2) : Measurable (siteLambda R z) :=
  ((measurable_siteGrad R z).const_mul 4).const_add 4

/-- **The moments of the shifted local gradient bounds at the sites.** -/
theorem growthMoments_siteLambda {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ B κ : ℝ, 0 < B ∧ 0 < κ ∧ ∀ R : ℕ, 1 ≤ R → ∀ z : Vertex 2,
      GrowthMoments p (fun ω => ENNReal.ofReal (1 + siteLambda R z ω)) B κ := by
  obtain ⟨B, κ, hB, hκ, hm⟩ := growthMoments_localGrad hpc hp1
  refine ⟨5 * B, κ, by positivity, hκ, fun R hR z q hq => ?_⟩
  have hq0 : 0 ≤ q := by linarith
  have hmp := measurePreserving_configurationTranslation p (-z)
  have hf : Measurable fun ω : Configuration 2 => ENNReal.ofReal (5 + 4 * localGrad R ω) ^ q :=
    (((measurable_localGrad R).const_mul 4).const_add 5).ennreal_ofReal.pow_const q
  calc ∫⁻ ω, ENNReal.ofReal (1 + siteLambda R z ω) ^ q ∂latticeBondLaw 2 p
      = ∫⁻ ω, ENNReal.ofReal (5 + 4 * localGrad R (configurationTranslation (-z) ω)) ^ q
          ∂latticeBondLaw 2 p := by
        refine lintegral_congr fun ω => ?_
        simp only [siteLambda, siteGrad]
        congr 2
        ring
    _ = ∫⁻ ω, ENNReal.ofReal (5 + 4 * localGrad R ω) ^ q ∂latticeBondLaw 2 p :=
        hmp.lintegral_comp hf
    _ ≤ ∫⁻ ω, 5 ^ q * ENNReal.ofReal (1 + localGrad R ω) ^ q ∂latticeBondLaw 2 p := by
        refine lintegral_mono fun ω => ?_
        have h0 := localGrad_nonneg ω hR
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0]
        refine ENNReal.rpow_le_rpow ?_ hq0
        rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = 5 ^ q * ∫⁻ ω, ENNReal.ofReal (1 + localGrad R ω) ^ q ∂latticeBondLaw 2 p :=
        lintegral_const_mul _
          ((measurable_const.add (measurable_localGrad R)).ennreal_ofReal.pow_const q)
    _ ≤ 5 ^ q * ENNReal.ofReal ((B * q ^ κ) ^ q) := by
        gcongr
        exact hm R hR q hq
    _ = ENNReal.ofReal ((5 * B * q ^ κ) ^ q) := by
        have e : (5 * B * q ^ κ) ^ q = 5 ^ q * (B * q ^ κ) ^ q := by
          rw [mul_assoc, Real.mul_rpow (by norm_num) (by positivity)]
        have h5 : ENNReal.ofReal ((5 : ℝ) ^ q) = 5 ^ q := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq0]
          norm_num
        rw [e, ENNReal.ofReal_mul (by positivity), h5]

/-- **The finite-range weight under the majorant** when the capped sides are the sides. -/
theorem finiteWeight_le_weightMajorant {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {κ R : ℕ} (hR : 1 ≤ R) {u : Vertex 2} (hs : SideGood R ω u) :
    ENNReal.ofReal (finiteWeight κ R ω u) ≤ weightMajorant (siteLambda R) (6 * κ) (6 * κ) u ω := by
  set g : LatticeEdge → ℝ≥0∞ := fun a =>
    if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
        6 * κ * TriadicCube.stoppingSize (planarGoodCubes ω) a.1 then
      stepOneBallSum (siteLambda R) (6 * κ) a.1 ω ^ (9 : ℝ) else 0 with hg
  have hball : ∀ v, ENNReal.ofReal
      (∑ z ∈ supBox v (3 * κ * planarSide ω v), (5 + 4 * siteGrad R ω z)) ≤
        stepOneBallSum (siteLambda R) (6 * κ) v ω := by
    intro v
    unfold stepOneBallSum
    rw [ENNReal.ofReal_sum_of_nonneg fun z _ => by have := siteGrad_nonneg hR ω z; linarith]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (supBox v (3 * κ * planarSide ω v)))
    refine Finset.sum_congr rfl fun z hz => ?_
    have hc : ‖latticeEuclideanEmbedding (z - v)‖ ≤
        6 * κ * TriadicCube.stoppingSize (planarGoodCubes ω) v := by
      have h1 := norm_le_of_mem_supBox hz
      rw [stoppingSize_eq_planarSide hP]
      push_cast at h1
      linarith
    rw [if_pos hc, siteLambda]
    congr 1
    ring
  have hv : ∀ v ∈ supBox u R, ENNReal.ofReal
      (if u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
        2 * finiteBallSum κ R ω v ^ 9 else 0) ≤ ∑' k : Fin 2, g (v, k) := by
    intro v hvu
    by_cases hc : u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v)
    · rw [if_pos hc]
      have hsv := hs v hvu
      have hcond : ‖latticeEuclideanEmbedding (v - u)‖ ≤
          6 * κ * TriadicCube.stoppingSize (planarGoodCubes ω) v := by
        rw [← hsv] at hc
        have h1 := norm_le_of_mem_supBox hc
        rw [norm_emb_sub_comm, stoppingSize_eq_planarSide hP]
        push_cast at h1
        linarith
      have hT0 := finiteBallSum_nonneg (κ := κ) hR ω v
      have hT : ENNReal.ofReal (finiteBallSum κ R ω v) ≤
          stepOneBallSum (siteLambda R) (6 * κ) v ω := by
        rw [finiteBallSum_eq, ← hsv]
        exact hball v
      rw [tsum_fintype, Fin.sum_univ_two]
      simp only [hg, if_pos hcond]
      calc ENNReal.ofReal (2 * finiteBallSum κ R ω v ^ 9)
          = 2 * ENNReal.ofReal (finiteBallSum κ R ω v) ^ (9 : ℝ) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hT0, ← ENNReal.rpow_natCast]
            norm_num
        _ ≤ 2 * stepOneBallSum (siteLambda R) (6 * κ) v ω ^ (9 : ℝ) := by gcongr
        _ = _ := two_mul _
    · rw [if_neg hc, ENNReal.ofReal_zero]
      positivity
  calc ENNReal.ofReal (finiteWeight κ R ω u)
      = ∑ v ∈ supBox u R, ENNReal.ofReal
          (if u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
            2 * finiteBallSum κ R ω v ^ 9 else 0) := by
        unfold finiteWeight
        exact ENNReal.ofReal_sum_of_nonneg fun v _ => by
          split_ifs
          · have := finiteBallSum_nonneg (κ := κ) hR ω v; positivity
          · exact le_rfl
    _ ≤ ∑ v ∈ supBox u R, ∑' k : Fin 2, g (v, k) := Finset.sum_le_sum hv
    _ ≤ ∑' v, ∑' k : Fin 2, g (v, k) := ENNReal.sum_le_tsum _
    _ = ∑' a : LatticeEdge, g a := (ENNReal.tsum_prod (f := fun v k => g (v, k))).symm
    _ = weightMajorant (siteLambda R) (6 * κ) (6 * κ) u ω := rfl

/-- The tail term: a power of `R` against `(2R + 1)² e^{-c 3^{⌊log₃ R⌋}}`. -/
theorem finiteWeight_tail_le {κ : ℕ} (hκ : 1 ≤ κ) {q c C' : ℝ} (hq : 1 ≤ q) (hc : 0 < c)
    (hC' : 0 ≤ C') {R : ℕ} (hR : 1 ≤ R) :
    ((2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)) ^ q *
      ((((2 * R + 1) ^ 2 : ℕ) : ℝ) * (C' * Real.exp (-c * (3 : ℝ) ^ capScale R))) ≤
    (18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) ^ q *
      (9 * C' * ((29 * q + 2) / (c / 3)) ^ (29 * q + 2)) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hx0 : (0 : ℝ) ≤ R := by linarith
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hq0 : 0 ≤ q := by linarith
  have hκx : (1 : ℝ) ≤ κ * R := by nlinarith
  have hBd : (2 * (R : ℝ) + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9) ≤
      (18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) * (R : ℝ) ^ 29 := by
    calc (2 * (R : ℝ) + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)
        ≤ (3 * (R : ℝ)) ^ 2 * (2 * ((7 * κ * R) ^ 2 * (29 * R)) ^ 9) := by
          gcongr
          · linarith
          · nlinarith
          · linarith
      _ = _ := by ring
  have h3 : (R : ℝ) / 3 ≤ (3 : ℝ) ^ capScale R := by
    have := lt_three_mul_three_pow_capScale R
    have : (R : ℝ) < 3 * 3 ^ capScale R := by exact_mod_cast this
    linarith
  have hexp : Real.exp (-c * (3 : ℝ) ^ capScale R) ≤ Real.exp (-(c / 3 * R)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h3 hc.le
    have e : c * (R / 3) = c / 3 * R := by ring
    linarith
  have hN : ((((2 * R + 1) ^ 2 : ℕ) : ℝ)) ≤ 9 * (R : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hrp := rpow_mul_exp_neg_le hx0 (a := 29 * q + 2) (by linarith) (c := c / 3) (by positivity)
  have hxq : (R : ℝ) ^ (29 * q + 2) = ((R : ℝ) ^ 29) ^ q * (R : ℝ) ^ 2 := by
    rw [Real.rpow_add (by linarith), Real.rpow_two,
      show (29 : ℝ) * q = ((29 : ℕ) : ℝ) * q by norm_num, Real.rpow_natCast_mul hx0]
  calc _ ≤ ((18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) * (R : ℝ) ^ 29) ^ q *
        (9 * (R : ℝ) ^ 2 * (C' * Real.exp (-(c / 3 * R)))) := by
        gcongr
    _ = (18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) ^ q *
        (9 * C' * ((R : ℝ) ^ (29 * q + 2) * Real.exp (-(c / 3 * R)))) := by
        rw [Real.mul_rpow (by positivity) (by positivity), hxq]
        ring
    _ ≤ _ := by gcongr

/-- **The moments of the finite-range weight are bounded uniformly in the range.** -/
theorem exists_lintegral_finiteWeight_rpow_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {κ : ℕ} (hκ : 1 ≤ κ) {q : ℝ}
    (hq : 1 ≤ q) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ R : ℕ, 1 ≤ R → ∀ u : Vertex 2,
      ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ∂latticeBondLaw 2 p ≤
        ENNReal.ofReal M₀ := by
  obtain ⟨B, κm, hB, hκm, hmom⟩ := growthMoments_siteLambda hpc hp1
  have hK : (0 : ℝ) < 6 * κ := by
    have : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    linarith
  obtain ⟨A, k, hA, hk, hW⟩ := growthMoments_weightMajorant_uniform hpc hB hκm hK hK
  obtain ⟨C, hC, c, hc, hD⟩ := measure_not_sideGood_le hpc
  have hC'0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := by linarith
  have hD0 : 0 ≤ (18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) ^ q *
      (9 * C.toReal * ((29 * q + 2) / (c / 3)) ^ (29 * q + 2)) := by positivity
  refine ⟨(A * q ^ k) ^ q + (18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) ^ q *
      (9 * C.toReal * ((29 * q + 2) / (c / 3)) ^ (29 * q + 2)), by positivity,
    fun R hR u => ?_⟩
  have hPPE : latticeBondLaw 2 p {ω | ¬ PlanarPartitionEvent ω} = 0 :=
    ae_iff.1 (ae_planarPartitionEvent hpc)
  have hBd0 : (0 : ℝ) ≤ (2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9) := by
    positivity
  have hpt : ∀ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ≤
      weightMajorant (siteLambda R) (6 * κ) (6 * κ) u ω ^ q +
        {ω | ¬ (PlanarPartitionEvent ω ∧ SideGood R ω u)}.indicator (fun _ => ENNReal.ofReal
          (((2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)) ^ q)) ω := by
    intro ω
    by_cases hω : PlanarPartitionEvent ω ∧ SideGood R ω u
    · exact le_add_right (ENNReal.rpow_le_rpow (finiteWeight_le_weightMajorant hω.1 hR hω.2) hq0)
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ¬ (PlanarPartitionEvent ω ∧ SideGood R ω u)}
        from hω)]
      refine le_add_left ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (finiteWeight_nonneg hR ω u) hq0]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (finiteWeight_nonneg hR ω u) (finiteWeight_le hR ω u) hq0)
  have hbad : latticeBondLaw 2 p {ω | ¬ (PlanarPartitionEvent ω ∧ SideGood R ω u)} ≤
      ((2 * R + 1) ^ 2 : ℕ) * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ capScale R))) := by
    have hsub : {ω | ¬ (PlanarPartitionEvent ω ∧ SideGood R ω u)} ⊆
        {ω | ¬ PlanarPartitionEvent ω} ∪ {ω | PlanarPartitionEvent ω ∧ ¬ SideGood R ω u} := by
      intro ω hω
      by_cases hP : PlanarPartitionEvent ω
      · exact Or.inr ⟨hP, fun hs => hω ⟨hP, hs⟩⟩
      · exact Or.inl hP
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hPPE, zero_add]
    exact hD R u
  calc ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, (weightMajorant (siteLambda R) (6 * κ) (6 * κ) u ω ^ q +
          {ω | ¬ (PlanarPartitionEvent ω ∧ SideGood R ω u)}.indicator (fun _ => ENNReal.ofReal
            (((2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)) ^ q)) ω)
          ∂latticeBondLaw 2 p := lintegral_mono hpt
    _ = ∫⁻ ω, weightMajorant (siteLambda R) (6 * κ) (6 * κ) u ω ^ q ∂latticeBondLaw 2 p +
        ∫⁻ ω, {ω | ¬ (PlanarPartitionEvent ω ∧ SideGood R ω u)}.indicator (fun _ => ENNReal.ofReal
            (((2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)) ^ q)) ω
          ∂latticeBondLaw 2 p :=
        lintegral_add_left'
          ((measurable_weightMajorant (measurable_siteLambda R) _ _ u).pow_const q).aemeasurable _
    _ ≤ ENNReal.ofReal ((A * q ^ k) ^ q) + ENNReal.ofReal
          (((2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)) ^ q) *
          latticeBondLaw 2 p {ω | ¬ (PlanarPartitionEvent ω ∧ SideGood R ω u)} :=
        add_le_add (hW (siteLambda R) (measurable_siteLambda R) (hmom R hR) u q hq)
          (lintegral_indicator_const_le _ _)
    _ ≤ ENNReal.ofReal ((A * q ^ k) ^ q) + ENNReal.ofReal
          ((18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) ^ q *
            (9 * C.toReal * ((29 * q + 2) / (c / 3)) ^ (29 * q + 2))) := by
        gcongr
        calc _ ≤ ENNReal.ofReal
              (((2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)) ^ q) *
              (((2 * R + 1) ^ 2 : ℕ) *
                (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ capScale R)))) := by gcongr
          _ = ENNReal.ofReal
              (((2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)) ^ q *
                ((((2 * R + 1) ^ 2 : ℕ) : ℝ) *
                  (C.toReal * Real.exp (-c * (3 : ℝ) ^ capScale R)))) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_mul hC'0, ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hC]
          _ ≤ _ := ENNReal.ofReal_le_ofReal (finiteWeight_tail_le hκ hq hc hC'0 hR)
    _ = _ := (ENNReal.ofReal_add (by positivity) hD0).symm

end Rigidity.Corrector

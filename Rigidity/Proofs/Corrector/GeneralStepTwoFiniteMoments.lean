import Rigidity.Proofs.Corrector.GeneralStepTwoFiniteProb
import Rigidity.Proofs.Corrector.GeneralStepTwoWeightMoments
import Rigidity.Proofs.Corrector.GeneralLocalGradientMoments

/-!
# The moments of the finite-range weight on `ℤᵈ`

With `Λ_R(z) = 2d (J_R(z) + 1)` (`siteLambda`), so that `1 + Λ_R(z)` is the summand of the ball
sums of the finite-range weight, the moments of `1 + Λ_R(z)` are `((1 + 2d) B q^κ)^q` uniformly in
`R` and `z` for `d ≥ 3`, since the configuration seen from `z` has the law of the configuration
(`growthMoments_siteLambda`, from `growthMoments_localGrad`). The finite-range weight is at most the
majorant `weightMajorant Λ_R (3dκ) (3dκ) u` when the capped sides are the sides near `u`
(`finiteWeight_le_weightMajorant`); otherwise it is at most a power of `R`, on an event of
probability `(2R + 1)ᵈ C e^{-c R/3}`, and the product is bounded uniformly in `R`
(`finiteWeight_tail_le`). Hence `E[W_R(u)^q] ≤ M₀` uniformly in `R ≥ 1` and `u`
(`exists_lintegral_finiteWeight_rpow_le`).

This ports the planar file `DarioStepTwoFiniteMoments`: the planar `Λ_R = 4 + 4 J_R` becomes
`2d (J_R + 1)`, the radii `6κ` of the planar majorant (twice the side `3κ`) become `3dκ` (the
Euclidean radius of an `ℓ^∞` box of radius `r` in `ℤᵈ` is at most `d r`), the factor `2` of the
edges with a given tail becomes `d`, and the powers of `R` and `κ` in the tail term are those of
the `d`-dimensional bound `finiteWeight_le`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open Rigidity.Poincare.GeneralDim (supBox mem_supBox card_supBox)
open Rigidity.Green.GeneralFlux (GrowthMomentsD)
open scoped Classical ENNReal

variable {d : ℕ}

/-- The local gradient bounds at the sites, `Λ_R(z) = 2d (J_R(z) + 1)`. -/
noncomputable def siteLambda (R : ℕ) (z : Vertex d) (ω : Configuration d) : ℝ :=
  2 * d * (siteGrad R ω z + 1)

theorem measurable_siteLambda (R : ℕ) (z : Vertex d) : Measurable (siteLambda (d := d) R z) :=
  ((measurable_siteGrad R z).add_const 1).const_mul (2 * d)

/-- **The finite-range weight under the majorant** when the capped sides are the sides. -/
theorem finiteWeight_le_weightMajorant {ω : Configuration d} (hP : PartitionEvent ω)
    {κ R : ℕ} (hR : 1 ≤ R) {u : Vertex d} (hs : SideGood R ω u) :
    ENNReal.ofReal (finiteWeight κ R ω u) ≤
      weightMajorant (siteLambda R) (3 * d * κ) (3 * d * κ) u ω := by
  set g : LatticeEdge d → ℝ≥0∞ := fun a =>
    if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
        3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1 then
      stepOneBallSum (siteLambda R) (3 * d * κ) a.1 ω ^ (9 : ℝ) else 0 with hg
  have hball : ∀ v, ENNReal.ofReal
      (∑ z ∈ supBox v (3 * κ * partSide ω v), (1 + 2 * d * (siteGrad R ω z + 1))) ≤
        stepOneBallSum (siteLambda R) (3 * d * κ) v ω := by
    intro v
    unfold stepOneBallSum
    rw [ENNReal.ofReal_sum_of_nonneg fun z _ => by have := siteGrad_nonneg hR ω z; positivity]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (supBox v (3 * κ * partSide ω v)))
    refine Finset.sum_congr rfl fun z hz => ?_
    have hc : ‖latticeEuclideanEmbedding (z - v)‖ ≤
        3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v := by
      have h1 := norm_le_of_mem_supBox hz
      rw [stoppingSize_eq_partSide hP]
      push_cast at h1
      linarith
    simp only [if_pos hc, siteLambda]
  have hv : ∀ v ∈ supBox u R, ENNReal.ofReal
      (if u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
        d * finiteBallSum κ R ω v ^ 9 else 0) ≤ ∑' k : Fin d, g (v, k) := by
    intro v hvu
    by_cases hc : u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v)
    · rw [if_pos hc]
      have hsv := hs v hvu
      have hcond : ‖latticeEuclideanEmbedding (v - u)‖ ≤
          3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v := by
        rw [← hsv] at hc
        have h1 := norm_le_of_mem_supBox hc
        rw [norm_emb_sub_comm, stoppingSize_eq_partSide hP]
        push_cast at h1
        linarith
      have hT0 := finiteBallSum_nonneg (κ := κ) hR ω v
      have hT : ENNReal.ofReal (finiteBallSum κ R ω v) ≤
          stepOneBallSum (siteLambda R) (3 * d * κ) v ω := by
        rw [finiteBallSum_eq, ← hsv]
        exact hball v
      rw [tsum_fintype]
      simp only [hg, if_pos hcond]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc ENNReal.ofReal (d * finiteBallSum κ R ω v ^ 9)
          = d * ENNReal.ofReal (finiteBallSum κ R ω v) ^ (9 : ℝ) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
              ENNReal.ofReal_pow hT0, ← ENNReal.rpow_natCast]
            norm_num
        _ ≤ d * stepOneBallSum (siteLambda R) (3 * d * κ) v ω ^ (9 : ℝ) := by gcongr
    · rw [if_neg hc, ENNReal.ofReal_zero]
      positivity
  calc ENNReal.ofReal (finiteWeight κ R ω u)
      = ∑ v ∈ supBox u R, ENNReal.ofReal
          (if u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
            d * finiteBallSum κ R ω v ^ 9 else 0) := by
        unfold finiteWeight
        exact ENNReal.ofReal_sum_of_nonneg fun v _ => by
          split_ifs
          · have := finiteBallSum_nonneg (κ := κ) hR ω v; positivity
          · exact le_rfl
    _ ≤ ∑ v ∈ supBox u R, ∑' k : Fin d, g (v, k) := Finset.sum_le_sum hv
    _ ≤ ∑' v, ∑' k : Fin d, g (v, k) := ENNReal.sum_le_tsum _
    _ = ∑' a : LatticeEdge d, g a := (ENNReal.tsum_prod (f := fun v k => g (v, k))).symm
    _ = weightMajorant (siteLambda R) (3 * d * κ) (3 * d * κ) u ω := rfl

/-- The tail term: a power of `R` against `(2R + 1)ᵈ e^{-c 3^{⌊log₃ R⌋}}`. -/
theorem finiteWeight_tail_le {κ : ℕ} (hκ : 1 ≤ κ) {q c C' : ℝ} (hq : 1 ≤ q) (hc : 0 < c)
    (hC' : 0 ≤ C') {R : ℕ} (hR : 1 ≤ R) :
    ((2 * R + 1) ^ d * (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9)) ^ q *
      ((((2 * R + 1) ^ d : ℕ) : ℝ) * (C' * Real.exp (-c * (3 : ℝ) ^ capScale R))) ≤
    (3 ^ d * d * 7 ^ (9 * d) * (1 + 14 * d) ^ 9 * κ ^ (9 * d)) ^ q *
      (3 ^ d * C' * (((10 * d + 9) * q + d) / (c / 3)) ^ ((10 * d + 9) * q + d)) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hx0 : (0 : ℝ) ≤ R := by linarith
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hq0 : 0 ≤ q := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set K : ℝ := 3 ^ d * d * 7 ^ (9 * d) * (1 + 14 * d) ^ 9 * κ ^ (9 * d) with hK
  have a1 : 2 * (R : ℝ) + 1 ≤ 3 * R := by linarith
  have a2 : 6 * (κ : ℝ) * R + 1 ≤ 7 * κ * R := by nlinarith
  have a3 : 1 + 2 * (d : ℝ) * (6 * R + 1) ≤ (1 + 14 * d) * R := by
    nlinarith [mul_le_mul_of_nonneg_left hx1 hd0]
  have hBd : (2 * (R : ℝ) + 1) ^ d *
      (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9) ≤
      K * (R : ℝ) ^ (10 * d + 9) := by
    calc (2 * (R : ℝ) + 1) ^ d * (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9)
        ≤ (3 * (R : ℝ)) ^ d * (d * ((7 * κ * R) ^ d * ((1 + 14 * d) * R)) ^ 9) := by
          gcongr
      _ = K * (R : ℝ) ^ (10 * d + 9) := by
          rw [hK]
          ring
  have h3 : (R : ℝ) / 3 ≤ (3 : ℝ) ^ capScale R := by
    have := lt_three_mul_three_pow_capScale R
    have : (R : ℝ) < 3 * 3 ^ capScale R := by exact_mod_cast this
    linarith
  have hexp : Real.exp (-c * (3 : ℝ) ^ capScale R) ≤ Real.exp (-(c / 3 * R)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h3 hc.le
    have e : c * (R / 3) = c / 3 * R := by ring
    linarith
  have hN : ((((2 * R + 1) ^ d : ℕ) : ℝ)) ≤ 3 ^ d * (R : ℝ) ^ d := by
    push_cast
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) a1 d
  have hrp := Rigidity.Corrector.rpow_mul_exp_neg_le hx0 (a := (10 * d + 9) * q + d)
    (by positivity) (c := c / 3) (by positivity)
  have hxq : (R : ℝ) ^ ((10 * d + 9) * q + d) = ((R : ℝ) ^ (10 * d + 9)) ^ q * (R : ℝ) ^ d := by
    rw [Real.rpow_add (by linarith), Real.rpow_natCast,
      show (10 * (d : ℝ) + 9) * q = (((10 * d + 9 : ℕ) : ℝ)) * q by push_cast; ring,
      Real.rpow_natCast_mul hx0]
  calc _ ≤ (K * (R : ℝ) ^ (10 * d + 9)) ^ q *
        (3 ^ d * (R : ℝ) ^ d * (C' * Real.exp (-(c / 3 * R)))) := by
        gcongr
    _ = K ^ q * (3 ^ d * C' * ((R : ℝ) ^ ((10 * d + 9) * q + d) * Real.exp (-(c / 3 * R)))) := by
        rw [Real.mul_rpow (by positivity) (by positivity), hxq]
        ring
    _ ≤ _ := by gcongr

/-- **The moments of the local gradient bounds at the sites**, uniformly in `R` and `z`, for
`d ≥ 3`: the configuration seen from `z` has the law of the configuration. -/
theorem growthMoments_siteLambda [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ B κ : ℝ, 0 < B ∧ 0 < κ ∧ ∀ R : ℕ, 1 ≤ R → ∀ z : Vertex d,
      GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + siteLambda R z ω)) B κ := by
  obtain ⟨B, κ, hB, hκ, hm⟩ := growthMoments_localGrad hd hpc hp1
  refine ⟨(1 + 2 * d) * B, κ, by positivity, hκ, fun R hR z q hq => ?_⟩
  have hq0 : 0 ≤ q := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmp := measurePreserving_configurationTranslation p (-z)
  have hf : Measurable fun ω : Configuration d =>
      ENNReal.ofReal (1 + 2 * d * (localGrad R ω + 1)) ^ q :=
    ((((measurable_localGrad R).add_const 1).const_mul (2 * d)).const_add
      1).ennreal_ofReal.pow_const q
  calc ∫⁻ ω, ENNReal.ofReal (1 + siteLambda R z ω) ^ q ∂latticeBondLaw d p
      = ∫⁻ ω, ENNReal.ofReal
          (1 + 2 * d * (localGrad R (configurationTranslation (-z) ω) + 1)) ^ q
          ∂latticeBondLaw d p := by
        refine lintegral_congr fun ω => ?_
        simp only [siteLambda, siteGrad]
    _ = ∫⁻ ω, ENNReal.ofReal (1 + 2 * d * (localGrad R ω + 1)) ^ q ∂latticeBondLaw d p :=
        hmp.lintegral_comp hf
    _ ≤ ∫⁻ ω, ENNReal.ofReal (1 + 2 * d) ^ q * ENNReal.ofReal (1 + localGrad R ω) ^ q
          ∂latticeBondLaw d p := by
        refine lintegral_mono fun ω => ?_
        have h0 := localGrad_nonneg ω hR
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0]
        refine ENNReal.rpow_le_rpow ?_ hq0
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith
    _ = ENNReal.ofReal (1 + 2 * d) ^ q *
          ∫⁻ ω, ENNReal.ofReal (1 + localGrad R ω) ^ q ∂latticeBondLaw d p :=
        lintegral_const_mul _
          ((measurable_const.add (measurable_localGrad R)).ennreal_ofReal.pow_const q)
    _ ≤ ENNReal.ofReal (1 + 2 * d) ^ q * ENNReal.ofReal ((B * q ^ κ) ^ q) := by
        gcongr
        exact hm R hR q hq
    _ = ENNReal.ofReal (((1 + 2 * d) * B * q ^ κ) ^ q) := by
        have e : ((1 + 2 * (d : ℝ)) * B * q ^ κ) ^ q = (1 + 2 * d) ^ q * (B * q ^ κ) ^ q := by
          rw [mul_assoc, Real.mul_rpow (x := 1 + 2 * (d : ℝ)) (y := B * q ^ κ) (by positivity)
            (by positivity)]
        rw [e, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0]

/-- **The moments of the finite-range weight are bounded uniformly in the range**, for `d ≥ 3`. -/
theorem exists_lintegral_finiteWeight_rpow_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {κ : ℕ} (hκ : 1 ≤ κ) {q : ℝ}
    (hq : 1 ≤ q) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ R : ℕ, 1 ≤ R → ∀ u : Vertex d,
      ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ∂latticeBondLaw d p ≤
        ENNReal.ofReal M₀ := by
  obtain ⟨B, κm, hB, hκm, hmom⟩ := growthMoments_siteLambda hd hpc hp1
  have hK : (0 : ℝ) < 3 * d * κ := by
    have h1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  obtain ⟨A, k, hA, hk, hW⟩ := growthMoments_weightMajorant_uniform (by omega) hpc hB hκm hK hK
  obtain ⟨C, hC, c, hc, hD⟩ := measure_not_sideGood_le (by omega) hpc
  have hC'0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := by linarith
  set T : ℝ := (3 ^ d * d * 7 ^ (9 * d) * (1 + 14 * d) ^ 9 * κ ^ (9 * d)) ^ q *
      (3 ^ d * C.toReal * (((10 * d + 9) * q + d) / (c / 3)) ^ ((10 * d + 9) * q + d)) with hT
  have hT0 : 0 ≤ T := by positivity
  refine ⟨(A * q ^ k) ^ q + T, by positivity, fun R hR u => ?_⟩
  have hPPE : latticeBondLaw d p {ω | ¬ PartitionEvent ω} = 0 :=
    ae_iff.1 (ae_partitionEvent (by omega) hpc)
  set W : ℝ := (2 * R + 1) ^ d * (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9)
    with hWd
  have hW0 : 0 ≤ W := by positivity
  have hpt : ∀ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ≤
      weightMajorant (siteLambda R) (3 * d * κ) (3 * d * κ) u ω ^ q +
        {ω | ¬ (PartitionEvent ω ∧ SideGood R ω u)}.indicator
          (fun _ => ENNReal.ofReal (W ^ q)) ω := by
    intro ω
    by_cases hω : PartitionEvent ω ∧ SideGood R ω u
    · exact le_add_right (ENNReal.rpow_le_rpow (finiteWeight_le_weightMajorant hω.1 hR hω.2) hq0)
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ¬ (PartitionEvent ω ∧ SideGood R ω u)} from hω)]
      refine le_add_left ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (finiteWeight_nonneg hR ω u) hq0]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (finiteWeight_nonneg hR ω u) (finiteWeight_le hR ω u) hq0)
  have hbad : latticeBondLaw d p {ω | ¬ (PartitionEvent ω ∧ SideGood R ω u)} ≤
      ((2 * R + 1) ^ d : ℕ) * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ capScale R))) := by
    have hsub : {ω | ¬ (PartitionEvent ω ∧ SideGood R ω u)} ⊆
        {ω | ¬ PartitionEvent ω} ∪ {ω | PartitionEvent ω ∧ ¬ SideGood R ω u} := by
      intro ω hω
      by_cases hP : PartitionEvent ω
      · exact Or.inr ⟨hP, fun hs => hω ⟨hP, hs⟩⟩
      · exact Or.inl hP
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hPPE, zero_add]
    exact hD R u
  calc ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (weightMajorant (siteLambda R) (3 * d * κ) (3 * d * κ) u ω ^ q +
          {ω | ¬ (PartitionEvent ω ∧ SideGood R ω u)}.indicator
            (fun _ => ENNReal.ofReal (W ^ q)) ω) ∂latticeBondLaw d p := lintegral_mono hpt
    _ = ∫⁻ ω, weightMajorant (siteLambda R) (3 * d * κ) (3 * d * κ) u ω ^ q ∂latticeBondLaw d p +
        ∫⁻ ω, {ω | ¬ (PartitionEvent ω ∧ SideGood R ω u)}.indicator
            (fun _ => ENNReal.ofReal (W ^ q)) ω ∂latticeBondLaw d p :=
        lintegral_add_left'
          ((measurable_weightMajorant (measurable_siteLambda R) _ _ u).pow_const q).aemeasurable _
    _ ≤ ENNReal.ofReal ((A * q ^ k) ^ q) + ENNReal.ofReal (W ^ q) *
          latticeBondLaw d p {ω | ¬ (PartitionEvent ω ∧ SideGood R ω u)} :=
        add_le_add (hW (siteLambda R) (measurable_siteLambda R) (hmom R hR) u q hq)
          (lintegral_indicator_const_le _ _)
    _ ≤ ENNReal.ofReal ((A * q ^ k) ^ q) + ENNReal.ofReal T := by
        gcongr
        calc _ ≤ ENNReal.ofReal (W ^ q) *
              (((2 * R + 1) ^ d : ℕ) *
                (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ capScale R)))) := by gcongr
          _ = ENNReal.ofReal (W ^ q * ((((2 * R + 1) ^ d : ℕ) : ℝ) *
                (C.toReal * Real.exp (-c * (3 : ℝ) ^ capScale R)))) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_mul hC'0, ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hC]
          _ ≤ _ := ENNReal.ofReal_le_ofReal (finiteWeight_tail_le hκ hq hc hC'0 hR)
    _ = _ := (ENNReal.ofReal_add (by positivity) hT0).symm

end Rigidity.Corrector.GeneralDim

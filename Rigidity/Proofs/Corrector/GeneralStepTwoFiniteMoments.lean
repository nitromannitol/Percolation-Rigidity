import Rigidity.Proofs.Corrector.GeneralStepTwoFiniteProb
import Rigidity.Proofs.Corrector.GeneralStepTwoWeightMoments
import Rigidity.Proofs.Corrector.GeneralLocalGradientMoments

/-!
# The moments of the finite-range weight on `ℤᵈ`

With `Λ_R(z) = 2d (J_R(z) + 1)` (`siteLambda`), so that `1 + Λ_R(z)` is the summand of the ball
sums of the finite-range weight, the moments of `1 + Λ_R(z)` are `((1 + 2d) B q^κ)^q` uniformly in
`R` and `z` for `d ≥ 3`, since the configuration seen from `z` has the law of the configuration
(`growthMoments_siteLambda`, from `growthMoments_localGrad`). The finite-range weight is at most the
majorant `weightMajorantOf (edgeRadius edgeBond) Λ_R (3dκ) (3dκ) u`, whose radius at the edge `a`
is `max(σ(v), σ♭(a, v))` with `σ♭` the stopping size of the configuration with the bond of `a`
closed, when the partitions exist and the capped sides are the sides near `u`
(`finiteWeight_le_weightMajorant`); otherwise it is at most a power of `R`, on an event of
probability at most `(2R + 1)ᵈ C' e^{-c' R/3}`, and the product is bounded uniformly in `R`
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

/-- **The finite-range weight under the majorant** when the partitions of `ω` and of the
configurations with one bond closed exist and the capped sides are the sides. -/
theorem finiteWeight_le_weightMajorant {ω : Configuration d} (hP : PartitionEvent ω)
    (hP' : ∀ a : LatticeEdge d, PartitionEvent (setBond (edgeBond a) false ω))
    {κ R : ℕ} (hR : 1 ≤ R) {u : Vertex d} (hs : SideGood R ω u)
    (hsF : SideGoodFlip edgeBond R ω u) :
    ENNReal.ofReal (finiteWeight κ R ω u) ≤
      weightMajorantOf (edgeRadius edgeBond) (siteLambda R) (3 * d * κ) (3 * d * κ) u ω := by
  set g : LatticeEdge d → ℝ≥0∞ := fun a =>
    if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤ 3 * d * κ * edgeRadius edgeBond a ω then
      radiusBallSum (siteLambda R) (fun ω => 3 * d * κ * edgeRadius edgeBond a ω) a.1 ω ^ (9 : ℝ)
    else 0 with hg
  have hρ : ∀ v (k : Fin d), edgeRadius edgeBond (v, k) ω =
      max (partSide ω v : ℝ) (partSide (setBond (edgeBond (v, k)) false ω) v : ℝ) :=
    fun v k => edgeRadius_eq_partSide edgeBond (v, k) hP (hP' (v, k))
  have hball : ∀ v (k : Fin d), ENNReal.ofReal
      (∑ z ∈ supBox v (3 * κ * max (partSide ω v) (partSide (setBond (edgeBond (v, k)) false ω) v)),
        (1 + 2 * d * (siteGrad R ω z + 1))) ≤
        radiusBallSum (siteLambda R) (fun ω => 3 * d * κ * edgeRadius edgeBond (v, k) ω) v ω := by
    intro v k
    unfold radiusBallSum
    rw [ENNReal.ofReal_sum_of_nonneg fun z _ => by have := siteGrad_nonneg hR ω z; positivity]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum
      (supBox v (3 * κ * max (partSide ω v) (partSide (setBond (edgeBond (v, k)) false ω) v))))
    refine Finset.sum_congr rfl fun z hz => ?_
    have hc : ‖latticeEuclideanEmbedding (z - v)‖ ≤ 3 * d * κ * edgeRadius edgeBond (v, k) ω := by
      have h1 := norm_le_of_mem_supBox hz
      rw [hρ v k]
      push_cast at h1
      linarith
    simp only [if_pos hc, siteLambda]
  have hvk : ∀ v ∈ supBox u R, ∀ k : Fin d, ENNReal.ofReal
      (if u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k)) then
        finiteBallSum κ R ω (v, k) ^ 9 else 0) ≤ g (v, k) := by
    intro v hvu k
    by_cases hc : u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k))
    · rw [if_pos hc]
      have hmax := cappedEdgeSide_eq_max k hs hsF hvu
      have hcond : ‖latticeEuclideanEmbedding (v - u)‖ ≤
          3 * d * κ * edgeRadius edgeBond (v, k) ω := by
        rw [hmax] at hc
        have h1 := norm_le_of_mem_supBox hc
        rw [LatticeProb.Percolation.latticeEuclideanEmbedding_sub, norm_sub_rev,
          ← LatticeProb.Percolation.latticeEuclideanEmbedding_sub, hρ v k]
        push_cast at h1
        linarith
      have hT0 := finiteBallSum_nonneg (κ := κ) hR ω (v, k)
      have hT : ENNReal.ofReal (finiteBallSum κ R ω (v, k)) ≤
          radiusBallSum (siteLambda R) (fun ω => 3 * d * κ * edgeRadius edgeBond (v, k) ω) v ω := by
        rw [finiteBallSum_eq, hmax]
        exact hball v k
      simp only [hg, if_pos hcond]
      calc ENNReal.ofReal (finiteBallSum κ R ω (v, k) ^ 9)
          = ENNReal.ofReal (finiteBallSum κ R ω (v, k)) ^ (9 : ℝ) := by
            rw [ENNReal.ofReal_pow hT0, ← ENNReal.rpow_natCast]
            norm_num
        _ ≤ _ := by gcongr
    · rw [if_neg hc, ENNReal.ofReal_zero]
      positivity
  have hnn : ∀ v (k : Fin d), 0 ≤ (if u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k))
      then finiteBallSum κ R ω (v, k) ^ 9 else 0) := fun v k => by
    split_ifs
    · have := finiteBallSum_nonneg (κ := κ) hR ω (v, k); positivity
    · exact le_rfl
  calc ENNReal.ofReal (finiteWeight κ R ω u)
      = ∑ v ∈ supBox u R, ∑ k : Fin d, ENNReal.ofReal
          (if u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k)) then
            finiteBallSum κ R ω (v, k) ^ 9 else 0) := by
        unfold finiteWeight
        rw [ENNReal.ofReal_sum_of_nonneg fun v _ => Finset.sum_nonneg fun k _ => hnn v k]
        exact Finset.sum_congr rfl fun v _ => ENNReal.ofReal_sum_of_nonneg fun k _ => hnn v k
    _ ≤ ∑ v ∈ supBox u R, ∑ k : Fin d, g (v, k) :=
        Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun k _ => hvk v hv k
    _ = ∑ v ∈ supBox u R, ∑' k : Fin d, g (v, k) := by simp only [tsum_fintype]
    _ ≤ ∑' v, ∑' k : Fin d, g (v, k) := ENNReal.sum_le_tsum _
    _ = ∑' a : LatticeEdge d, g a := (ENNReal.tsum_prod (f := fun v k => g (v, k))).symm
    _ = weightMajorantOf (edgeRadius edgeBond) (siteLambda R) (3 * d * κ) (3 * d * κ) u ω := rfl

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
  obtain ⟨A, k, hA, hk, hW⟩ :=
    growthMoments_weightMajorant_edgeRadius_uniform (by omega) hpc hp1 hB hκm hK hK
  obtain ⟨C, hC, c, hc, hD⟩ := measure_not_sideGood_le (by omega) hpc
  obtain ⟨C₂, hC₂, c₂, hc₂, hD₂⟩ := measure_not_sideGoodFlip_le (by omega) hpc hp1
  have hq0 : 0 ≤ q := by linarith
  have hp' : (0 : ℝ) < 1 - p := by linarith
  have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hC₂0 : 0 ≤ C₂.toReal := ENNReal.toReal_nonneg
  set C' : ℝ := C.toReal + d * C₂.toReal / (1 - p) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set c' : ℝ := min c c₂ with hc'
  have hc'0 : 0 < c' := lt_min hc hc₂
  set T : ℝ := (3 ^ d * d * 7 ^ (9 * d) * (1 + 14 * d) ^ 9 * κ ^ (9 * d)) ^ q *
      (3 ^ d * C' * (((10 * d + 9) * q + d) / (c' / 3)) ^ ((10 * d + 9) * q + d)) with hT
  have hT0 : 0 ≤ T := by positivity
  refine ⟨(A * q ^ k) ^ q + T, by positivity, fun R hR u => ?_⟩
  have hPPE : latticeBondLaw d p {ω | ¬ PartitionEvent ω} = 0 :=
    ae_iff.1 (ae_partitionEvent (by omega) hpc)
  have hPF : latticeBondLaw d p
      {ω | ¬ ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)} = 0 :=
    ae_iff.1 (ae_partitionEvent_setBond (by omega) hpc hp1)
  set W : ℝ := (2 * R + 1) ^ d * (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9)
    with hWd
  have hW0 : 0 ≤ W := by positivity
  set bad : Set (Configuration d) := {ω | ¬ (PartitionEvent ω ∧
    (∀ a : LatticeEdge d, PartitionEvent (setBond (edgeBond a) false ω)) ∧
      SideGood R ω u ∧ SideGoodFlip edgeBond R ω u)} with hbad_def
  have hpt : ∀ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ≤
      weightMajorantOf (edgeRadius edgeBond) (siteLambda R) (3 * d * κ) (3 * d * κ) u ω ^ q +
        bad.indicator (fun _ => ENNReal.ofReal (W ^ q)) ω := by
    intro ω
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_mem hω]
      refine le_add_left ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (finiteWeight_nonneg hR ω u) hq0]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (finiteWeight_nonneg hR ω u) (finiteWeight_le hR ω u) hq0)
    · simp only [hbad_def, Set.mem_setOf_eq, not_not] at hω
      exact le_add_right (ENNReal.rpow_le_rpow
        (finiteWeight_le_weightMajorant hω.1 hω.2.1 hR hω.2.2.1 hω.2.2.2) hq0)
  have hbad : latticeBondLaw d p bad ≤
      ((2 * R + 1) ^ d : ℕ) * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ capScale R))) +
        ((d * (2 * R + 1) ^ d : ℕ) : ℝ≥0∞) *
          (C₂ * ENNReal.ofReal (Real.exp (-c₂ * (3 : ℝ) ^ capScale R) / (1 - p))) := by
    have hsub : bad ⊆ {ω | ¬ PartitionEvent ω} ∪
        ({ω | ¬ ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)} ∪
          ({ω | PartitionEvent ω ∧ ¬ SideGood R ω u} ∪ {ω | ¬ SideGoodFlip edgeBond R ω u})) := by
      intro ω hω
      simp only [hbad_def, Set.mem_setOf_eq] at hω
      simp only [Set.mem_union, Set.mem_setOf_eq]
      by_cases hP : PartitionEvent ω
      · by_cases hPf : ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)
        · by_cases hs : SideGood R ω u
          · exact Or.inr (Or.inr (Or.inr fun hsf => hω ⟨hP, fun a => hPf _ _, hs, hsf⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hP, hs⟩))
        · exact Or.inr (Or.inl hPf)
      · exact Or.inl hP
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hPPE, zero_add]
    refine (measure_union_le _ _).trans ?_
    rw [hPF, zero_add]
    exact (measure_union_le _ _).trans (add_le_add (hD R u) (hD₂ edgeBond R u))
  have hbad' : latticeBondLaw d p bad ≤ ENNReal.ofReal
      ((((2 * R + 1) ^ d : ℕ) : ℝ) * (C' * Real.exp (-c' * (3 : ℝ) ^ capScale R))) := by
    refine hbad.trans ?_
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ capScale R := by positivity
    have e1 : Real.exp (-c * (3 : ℝ) ^ capScale R) ≤ Real.exp (-c' * (3 : ℝ) ^ capScale R) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left c c₂])
    have e2 : Real.exp (-c₂ * (3 : ℝ) ^ capScale R) ≤ Real.exp (-c' * (3 : ℝ) ^ capScale R) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right c c₂])
    rw [show (C : ℝ≥0∞) = ENNReal.ofReal C.toReal from (ENNReal.ofReal_toReal hC).symm,
      show (C₂ : ℝ≥0∞) = ENNReal.ofReal C₂.toReal from (ENNReal.ofReal_toReal hC₂).symm,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hC0,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hC₂0,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set N : ℝ := (((2 * R + 1) ^ d : ℕ) : ℝ) with hN
    have hN0 : 0 ≤ N := Nat.cast_nonneg _
    have hdN : (((d * (2 * R + 1) ^ d : ℕ)) : ℝ) = d * N := by rw [hN]; push_cast; ring
    rw [hdN]
    set e' := Real.exp (-c' * (3 : ℝ) ^ capScale R)
    have t1 : N * (C.toReal * Real.exp (-c * (3 : ℝ) ^ capScale R)) ≤ N * (C.toReal * e') := by
      gcongr
    have t2 : d * N * (C₂.toReal * (Real.exp (-c₂ * (3 : ℝ) ^ capScale R) / (1 - p))) ≤
        d * N * (C₂.toReal * (e' / (1 - p))) := by
      gcongr
    have t3 : N * (C' * e') = N * (C.toReal * e') + d * N * (C₂.toReal * (e' / (1 - p))) := by
      rw [hC']
      field_simp
    linarith
  calc ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (weightMajorantOf (edgeRadius edgeBond) (siteLambda R) (3 * d * κ) (3 * d * κ) u ω
            ^ q + bad.indicator (fun _ => ENNReal.ofReal (W ^ q)) ω) ∂latticeBondLaw d p :=
        lintegral_mono hpt
    _ = ∫⁻ ω, weightMajorantOf (edgeRadius edgeBond) (siteLambda R) (3 * d * κ) (3 * d * κ) u ω ^ q
          ∂latticeBondLaw d p +
        ∫⁻ ω, bad.indicator (fun _ => ENNReal.ofReal (W ^ q)) ω ∂latticeBondLaw d p :=
        lintegral_add_left' ((measurable_weightMajorantOf
          (fun a => measurable_edgeRadius edgeBond a) (measurable_siteLambda R) _ _ u).pow_const
            q).aemeasurable _
    _ ≤ ENNReal.ofReal ((A * q ^ k) ^ q) + ENNReal.ofReal (W ^ q) * latticeBondLaw d p bad :=
        add_le_add (hW edgeBond (siteLambda R) (measurable_siteLambda R) (hmom R hR) u q hq)
          (lintegral_indicator_const_le _ _)
    _ ≤ ENNReal.ofReal ((A * q ^ k) ^ q) + ENNReal.ofReal T := by
        gcongr
        calc _ ≤ ENNReal.ofReal (W ^ q) * ENNReal.ofReal
              ((((2 * R + 1) ^ d : ℕ) : ℝ) * (C' * Real.exp (-c' * (3 : ℝ) ^ capScale R))) := by
              gcongr
          _ = ENNReal.ofReal (W ^ q * ((((2 * R + 1) ^ d : ℕ) : ℝ) *
                (C' * Real.exp (-c' * (3 : ℝ) ^ capScale R)))) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (finiteWeight_tail_le hκ hq hc'0 hC'0 hR)
    _ = _ := (ENNReal.ofReal_add (by positivity) hT0).symm

end Rigidity.Corrector.GeneralDim

import Rigidity.Proofs.Section5.LSSDomination
import Rigidity.Proofs.Section5.RenormField
import Rigidity.Proofs.Section5.VeryGoodProbability
import Rigidity.Proofs.Percolation.PlanarWellConnected
import Rigidity.Proofs.Percolation.KestenCrossing

/-!
# Domination of the planar renormalized field

Supercritical planar bond percolation produces a very-good-block field that dominates
Bernoulli site percolation with density tending to one as the block size grows.
-/

namespace Rigidity.Proofs.Section5

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- The planar very-good-block field dominates Bernoulli site fields of density tending to one. -/
theorem planar_renormalized_domination {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) : RenormalizedDominationStmt p := by
  obtain ⟨C, c, s, hC, hc, hs, hbound⟩ := veryGoodProbabilityStep_two
    Rigidity.Percolation.wellConnected_input_two Rigidity.Percolation.kesten_rectangle_crossing p hpc
  obtain ⟨C₀, a, hC₀, ha, hdom⟩ := oneDependentDominationStep
  refine ⟨C₀ * C ^ a, a * c, s, by positivity, by positivity, hs, fun R _ A hA hinc => ?_⟩
  have hmeas := renormFieldMeasurableStep R
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (renormField R)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine hdom _ inferInstance (renormFieldOneDependentStep p R)
    (C * Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s)))
    (by positivity) (fun z => ?_) _ _ ?_ A hA hinc
  · have hz : MeasurableSet {ω : PlanarCarrier → Bool | ω z = false} :=
      measurableSet_eq_fun (measurable_pi_apply z) measurable_const
    rw [Measure.map_apply hmeas hz]
    convert hbound (renormCentre R z) (11 * R / 10) using 2
    ext ω
    simp [renormField]
  · refine (min_le_right _ _).trans (Real.toNNReal_le_toNNReal ?_)
    rw [Real.mul_rpow hC.le (Real.exp_pos _).le, ← Real.exp_mul]
    have hRr : (R : ℝ) ^ s ≤ ((11 * R / 10 : ℕ) : ℝ) ^ s :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show R ≤ 11 * R / 10 by omega))
        hs.le
    have hexp : Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s) * a) ≤
        Real.exp (-(a * c * (R : ℝ) ^ s)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hRr (mul_pos ha hc).le])
    have hCa : 0 < C₀ * C ^ a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hexp hCa.le]

/-- Every prescribed site density below one is dominated at all sufficiently large block sizes. -/
theorem planar_renormalized_domination_eventually {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (q : NNReal) (hq : q < 1) :
    ∀ᶠ R : ℕ in atTop,
      LatticeProb.Percolation.DenseLower (bernoulliFieldPlanar q hq.le)
        ((latticeBondLaw 2 p).map (renormField R)) := by
  obtain ⟨C, c, s, hC, hc, hs, hbound⟩ := veryGoodProbabilityStep_two
    Rigidity.Percolation.wellConnected_input_two Rigidity.Percolation.kesten_rectangle_crossing p hpc
  obtain ⟨C₀, a, hC₀, ha, hdom⟩ := oneDependentDominationStep
  have htend : Tendsto (fun R : ℕ => C₀ * C ^ a * Real.exp (-(a * c * (R : ℝ) ^ s)))
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun R : ℕ => (R : ℝ) ^ s) atTop atTop :=
      (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero, Function.comp_def] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.const_mul_atTop (mul_pos ha hc))).const_mul
        (C₀ * C ^ a)
  have hqpos : 0 < 1 - (q : ℝ) := by exact sub_pos.mpr (by exact_mod_cast hq)
  filter_upwards [htend.eventually_lt_const hqpos] with R hsmall
  have hmeas := renormFieldMeasurableStep R
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (renormField R)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine hdom _ inferInstance (renormFieldOneDependentStep p R)
    (C * Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s)))
    (by positivity) (fun z => ?_) q hq.le ?_
  · have hz : MeasurableSet {ω : PlanarCarrier → Bool | ω z = false} :=
      measurableSet_eq_fun (measurable_pi_apply z) measurable_const
    rw [Measure.map_apply hmeas hz]
    convert hbound (renormCentre R z) (11 * R / 10) using 2
    ext ω
    simp [renormField]
  · rw [← Real.toNNReal_coe (r := q)]
    apply Real.toNNReal_le_toNNReal
    rw [Real.mul_rpow hC.le (Real.exp_pos _).le, ← Real.exp_mul]
    have hRr : (R : ℝ) ^ s ≤ ((11 * R / 10 : ℕ) : ℝ) ^ s :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show R ≤ 11 * R / 10 by omega))
        hs.le
    have hexp : Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s) * a) ≤
        Real.exp (-(a * c * (R : ℝ) ^ s)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hRr (mul_pos ha hc).le])
    have hCa : 0 < C₀ * C ^ a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hexp hCa.le]

end Rigidity.Proofs.Section5

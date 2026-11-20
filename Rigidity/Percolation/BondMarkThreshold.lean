import Rigidity.Percolation.UniformBondMarks

/-!
# Bernoulli configurations from uniform marks

Thresholding independent uniform marks at a fixed density yields the
canonical Bernoulli bond law.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A mark is open at a given density when it is below the threshold. -/
noncomputable def markThreshold (p : unitInterval) (u : unitInterval) : Bool :=
  if u ≤ p then true else false

/-- Thresholding a mark is measurable. -/
theorem measurable_markThreshold (p : unitInterval) : Measurable (markThreshold p) := by
  unfold markThreshold
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- A thresholded uniform mark has the Bernoulli law at that threshold. -/
theorem volume_map_markThreshold (p : unitInterval) :
    (volume : Measure unitInterval).map (markThreshold p) = bernoulliMeasure true false p := by
  have hfalse : (markThreshold p) ⁻¹' ({false} : Set Bool) = Set.Ioi p := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ioi, markThreshold]
    by_cases h : u ≤ p <;> simp [h, not_le.mp]
  haveI : IsProbabilityMeasure ((volume : Measure unitInterval).map (markThreshold p)) :=
    Measure.isProbabilityMeasure_map (measurable_markThreshold p).aemeasurable
  have hfalseProb : ((volume : Measure unitInterval).map (markThreshold p)).real {false} =
      1 - (p : ℝ) := by
    rw [measureReal_def, Measure.map_apply (measurable_markThreshold p)
      (measurableSet_singleton false), hfalse, unitInterval.volume_Ioi,
      ENNReal.toReal_ofReal (sub_nonneg.mpr p.property.2)]
  have hbernoulli : (bernoulliMeasure true false p).real {false} = 1 - (p : ℝ) :=
    bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton false) (by simp) (by simp)
  apply Measure.ext_of_measureReal_singleton
  intro b
  cases b with
  | false => exact hfalseProb.trans hbernoulli.symm
  | true =>
    have h₁ := measureReal_compl (μ := (volume : Measure unitInterval).map (markThreshold p))
      (measurableSet_singleton false)
    have h₂ := measureReal_compl (μ := bernoulliMeasure true false p) (measurableSet_singleton false)
    have hcompl : ({false} : Set Bool)ᶜ = {true} := by ext b; cases b <;> simp
    rw [hcompl, probReal_univ] at h₁ h₂
    linarith

/-- Threshold every bond mark at the same density. -/
noncomputable def thresholdBondMarks {d : ℕ} (p : unitInterval) (ω : BondMarks d) : Configuration d :=
  fun e => markThreshold p (ω e)

/-- The uniform-mark coupling produces the canonical Bernoulli bond law. -/
theorem bondMarkLaw_map_thresholdBondMarks (d : ℕ) (p : unitInterval) :
    (bondMarkLaw d).map (thresholdBondMarks p) = latticeBondLaw d p := by
  change (Measure.infinitePi (fun _ : Bond d => (volume : Measure unitInterval))).map
    (fun ω e => markThreshold p (ω e)) = _
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_markThreshold p)]
  simp only [volume_map_markThreshold, latticeBondLaw]

end Rigidity.Percolation

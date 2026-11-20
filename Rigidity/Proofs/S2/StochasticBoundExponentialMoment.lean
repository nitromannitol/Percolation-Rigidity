import Rigidity.Proofs.S2.NormalizedEnergyStochasticBound

/-!
# Exponential moments from stochastic tail bounds

A stretched-exponential tail gives an integrable half-exponential moment at the same scale.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory
open scoped ENNReal

/-- A stochastic tail bound controls the corresponding half-exponential moment. -/
theorem integrable_half_exponential_of_osBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (s θ : ℝ)
    (hs : 0 < s) (hθ : 0 < θ) (hXm : Measurable X) (hX : LatticeProb.OsBound μ s θ X) :
    Integrable (fun ω => Real.exp ((max (X ω) 0 / θ) ^ s / 2)) μ ∧
      (∫ ω, Real.exp ((max (X ω) 0 / θ) ^ s / 2) ∂μ) ≤ Real.exp 2 := by
  let Z : Ω → ℝ := fun ω => (max (X ω) 0 / θ) ^ s
  have hZm : Measurable Z := ((hXm.max measurable_const).div_const θ).pow_const s
  have hZ0 (ω : Ω) : 0 ≤ Z ω := Real.rpow_nonneg (div_nonneg (le_max_right _ _) hθ.le) _
  have hZ : LatticeProb.OsBound μ 1 1 Z := hX.normalized_rpow hs hθ
  have hlin := hZ.lintegral_exp_half hZm hZ0
  have hEm : Measurable (fun ω => Real.exp (Z ω / 2)) := (hZm.div_const 2).exp
  have hInt : Integrable (fun ω => Real.exp (Z ω / 2)) μ := by
    refine ⟨hEm.aestronglyMeasurable, ?_⟩
    show ∫⁻ ω, ‖Real.exp (Z ω / 2)‖ₑ ∂μ < ⊤
    simpa only [Real.enorm_eq_ofReal (Real.exp_pos _).le] using
      hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hInt, ?_⟩
  have hreal : ENNReal.ofReal (∫ ω, Real.exp (Z ω / 2) ∂μ) ≤ ENNReal.ofReal (Real.exp 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 hreal

end Rigidity.Proofs.S2

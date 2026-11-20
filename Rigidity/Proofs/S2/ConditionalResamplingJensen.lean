import LatticeProb.Prob.EfronSteinCountable

/-!
# Conditional fluctuations and resampling

A coordinate fluctuation about its conditional expectation is bounded by the average squared
resampling difference at that coordinate.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb
open scoped ENNReal

/-- A single-coordinate conditional fluctuation is bounded by its resampling energy. -/
theorem conditional_fluctuation_le_resampling {V : Type*} [DecidableEq V]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (V → ℝ) → ℝ)
    (hFm : Measurable F) (hF : Integrable F (Measure.infinitePi fun _ : V => ν)) (v : V) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : V => ν),
      ENNReal.ofReal ((F ω - MeasureTheory.condExp (coordAlg ({v}ᶜ : Set V))
        (Measure.infinitePi fun _ : V => ν) F ω) ^ 2) ≤
      ∫⁻ η : V → ℝ, ENNReal.ofReal ((F ω - F (Function.update ω v (η v))) ^ 2)
        ∂(Measure.infinitePi fun _ : V => ν) := by
  let P := Measure.infinitePi fun _ : V => ν
  let S : Set V := {v}ᶜ
  have hslice : ∀ᵐ ω ∂P, Integrable (fun η => F (comb S ω η)) P :=
    (integrable_comp_comb (fun _ : V => ν) S hF).prod_right_ae
  have hcond := partialInt_ae_eq_condExp (S := S) ν hFm hF
  filter_upwards [hslice, hcond] with ω hω hcondω
  have hdiff : F ω - MeasureTheory.condExp (coordAlg S) P F ω =
      ∫ η, (F ω - F (comb S ω η)) ∂P := by
    rw [← hcondω]
    change F ω - (∫ η, F (comb S ω η) ∂P) = _
    rw [integral_sub (integrable_const _) hω]
    simp
  rw [hdiff]
  have hmeas : Measurable (fun η : V → ℝ => F ω - F (comb S ω η)) :=
    measurable_const.sub (hFm.comp ((measurable_comb S).comp
      (measurable_const.prodMk measurable_id)))
  have hj := ofReal_sq_integral_le_lintegral P hmeas.aestronglyMeasurable
  simpa only [S, comb_compl_singleton] using hj

end Rigidity.Proofs.S2

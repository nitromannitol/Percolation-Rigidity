import Rigidity.Proofs.S2.PowerVarianceBound

/-!
# Weighted sums of resampling energies

Tonelli's theorem moves a nonnegative endpoint weight outside the sum of independent-copy
resampling energies.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal

/-- The total squared resampling influence, averaged over an independent product copy. -/
noncomputable def totalResamplingEnergy {ι : Type*} [DecidableEq ι] (ν : Measure ℝ)
    (F : (ι → ℝ) → ℝ) (ω : ι → ℝ) : ℝ≥0∞ :=
  ∑' i : ι, ∫⁻ η : ι → ℝ, ENNReal.ofReal
    ((F ω - F (Function.update ω i (η i))) ^ 2) ∂(Measure.infinitePi fun _ : ι => ν)

/-- The total resampling energy is measurable. -/
theorem measurable_totalResamplingEnergy {ι : Type*} [DecidableEq ι] [Countable ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F) :
    Measurable (totalResamplingEnergy ν F) := by
  apply Measurable.tsum
  intro i
  have hu : Measurable (fun q : (ι → ℝ) × (ι → ℝ) =>
      Function.update q.1 i (q.2 i)) :=
    (measurable_updateAt i).comp (measurable_fst.prodMk (measurable_pi_apply i |>.comp measurable_snd))
  exact (((hF.comp measurable_fst).sub (hF.comp hu)).pow_const 2).ennreal_ofReal.lintegral_prod_right'

/-- The weighted sum of two-copy resampling energies is the weighted integral of their sum. -/
theorem tsum_weighted_resampling_eq {ι : Type*} [DecidableEq ι] [Countable ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F) (n : ℕ) :
    let P := Measure.infinitePi (fun _ : ι => ν)
    (∑' i : ι, ∫⁻ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      (|F q.1| ^ n * (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2) ∂(P.prod P)) =
    ∫⁻ ω : ι → ℝ, ENNReal.ofReal (|F ω| ^ n) * totalResamplingEnergy ν F ω ∂P := by
  let P := Measure.infinitePi (fun _ : ι => ν)
  let g (i : ι) (q : (ι → ℝ) × (ι → ℝ)) : ℝ≥0∞ := ENNReal.ofReal
    ((F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2)
  let w (ω : ι → ℝ) : ℝ≥0∞ := ENNReal.ofReal (|F ω| ^ n)
  have hgm (i : ι) : Measurable (g i) := by
    dsimp only [g]
    have hu : Measurable (fun q : (ι → ℝ) × (ι → ℝ) =>
        Function.update q.1 i (q.2 i)) :=
      (measurable_updateAt i).comp (measurable_fst.prodMk (measurable_pi_apply i |>.comp measurable_snd))
    exact (((hF.comp measurable_fst).sub (hF.comp hu)).pow_const 2).ennreal_ofReal
  have hslice (i : ι) : Measurable (fun ω => ∫⁻ η, g i (ω, η) ∂P) :=
    (hgm i).lintegral_prod_right'
  have hterm (i : ι) : (∫⁻ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      (|F q.1| ^ n * (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2) ∂(P.prod P)) =
      ∫⁻ ω, w ω * (∫⁻ η, g i (ω, η) ∂P) ∂P := by
    have heq (q : (ι → ℝ) × (ι → ℝ)) : ENNReal.ofReal
        (|F q.1| ^ n * (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2) = w q.1 * g i q := by
      exact ENNReal.ofReal_mul (by positivity)
    simp_rw [heq]
    have hprod : Measurable (fun q : (ι → ℝ) × (ι → ℝ) => w q.1 * g i q) :=
      ((hF.abs.pow_const n).ennreal_ofReal.comp measurable_fst).mul (hgm i)
    rw [lintegral_prod (fun q => w q.1 * g i q) hprod.aemeasurable]
    congr 1
    funext ω
    change (∫⁻ η, w ω * (fun η => g i (ω, η)) η ∂P) = _
    simpa only [Function.comp_apply, id_eq] using
      (lintegral_const_mul'' (w ω)
        ((hgm i).comp (measurable_const.prodMk measurable_id)).aemeasurable)
  change (∑' i : ι, ∫⁻ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
    (|F q.1| ^ n * (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2) ∂(P.prod P)) = _
  simp_rw [hterm]
  have hfam (i : ι) : AEMeasurable (fun ω => w ω * (∫⁻ η, g i (ω, η) ∂P)) P :=
    ((hF.abs.pow_const n).ennreal_ofReal.mul (hslice i)).aemeasurable
  rw [← lintegral_tsum hfam]
  apply lintegral_congr
  intro ω
  rw [ENNReal.tsum_mul_left]
  rfl

end Rigidity.Proofs.S2

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal

/-- The variance of `Fⁿ` is controlled by the integral of the weighted total influence. -/
theorem evariance_pow_le_total_resampling {ι : Type*} [DecidableEq ι] [Countable ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (n : ℕ) (hF2 : Integrable (fun ω => (F ω ^ n) ^ 2)
      (Measure.infinitePi fun _ : ι => ν)) :
    let P := Measure.infinitePi (fun _ : ι => ν)
    evariance (fun ω => F ω ^ n) P ≤ ENNReal.ofReal ((n : ℝ) ^ 2) *
      ∫⁻ ω : ι → ℝ, ENNReal.ofReal (|F ω| ^ (2 * (n - 1))) *
        totalResamplingEnergy ν F ω ∂P := by
  have h := evariance_pow_le_weighted_resampling ν F hF n hF2
  dsimp only at h
  rw [tsum_weighted_resampling_eq ν F hF (2 * (n - 1))] at h
  exact h

end Rigidity.Proofs.S2

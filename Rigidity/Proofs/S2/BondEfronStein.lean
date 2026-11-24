import PercolationClusterHomogenization.Proofs.Density.BernoulliRealEncoding
import Rigidity.Proofs.S2.PlanarInfluenceTail

/-!
# Efron–Stein variance bound for Bernoulli bonds

The countable product Efron–Stein inequality applies to Boolean bond configurations through the
real Bernoulli encoding. The resulting resampling energy uses an independent bond configuration.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation
open scoped ENNReal

/-- The Efron–Stein variance bound for a square-integrable Bernoulli bond functional. -/
theorem bond_evariance_le_resampling_energy (d : ℕ) (p : unitInterval)
    (F : Configuration d → ℝ) (hF : Measurable F)
    (hF2 : Integrable (fun ω => F ω ^ 2) (latticeBondLaw d p)) :
    evariance F (latticeBondLaw d p) ≤
      (∫⁻ q : Configuration d × Configuration d, ∑' e : Bond d,
        ENNReal.ofReal ((F q.1 - F (resampleBond q.1 q.2 e)) ^ 2)
        ∂((latticeBondLaw d p).prod (latticeBondLaw d p))) / 2 := by
  classical
  let μ := latticeBondLaw d p
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  let ρ := Measure.infinitePi fun _ : Bond d => ν
  let T : (Bond d → ℝ) → Configuration d := bernoulliRealConfiguration
  let F' : (Bond d → ℝ) → ℝ := F ∘ T
  have hT : MeasurePreserving T ρ μ := measurePreserving_bernoulliRealConfiguration d p
  have hF'm : Measurable F' := hF.comp hT.measurable
  have hF'2 : Integrable (fun ω => F' ω ^ 2) ρ := by
    simpa only [F', Function.comp_def] using hT.integrable_comp_of_integrable hF2
  have hvar : evariance F μ = evariance F' ρ := by
    have hmean : (∫ ω, F ω ∂μ) = ∫ ω, F' ω ∂ρ := by
      have hm : AEStronglyMeasurable F (Measure.map T ρ) := by
        rw [hT.map_eq]
        exact hF.aestronglyMeasurable
      have h := integral_map hT.measurable.aemeasurable hm
      rw [hT.map_eq] at h
      exact h
    unfold evariance
    rw [hmean, ← hT.map_eq]
    have hm : Measurable (fun ω => ‖F ω - ∫ x, F' x ∂ρ‖ₑ ^ 2) := by
      simpa only [Pi.sub_apply] using ((hF.sub measurable_const).enorm.pow_const 2)
    rw [lintegral_map hm hT.measurable]
    rfl
  have he : ∀ e : Bond d, LatticeProb.siteEnergy ν F' e =
      ∫⁻ q : Configuration d × Configuration d,
        ENNReal.ofReal ((F q.1 - F (resampleBond q.1 q.2 e)) ^ 2) ∂(μ.prod μ) := by
    intro e
    let H (q : Configuration d × Bool) : ℝ≥0∞ :=
      ENNReal.ofReal ((F q.1 - F (Function.update q.1 e q.2)) ^ 2)
    have hUpd : Measurable (fun q : Configuration d × Bool => Function.update q.1 e q.2) := by
      refine measurable_pi_lambda _ fun j => ?_
      by_cases hj : j = e
      · subst j
        simp only [Function.update_self]
        exact measurable_snd
      · simp only [Function.update_of_ne hj]
        exact (measurable_pi_apply j).comp measurable_fst
    have hHm : Measurable H :=
      ((hF.comp measurable_fst).sub (hF.comp hUpd)).pow_const 2 |>.ennreal_ofReal
    have hbit : MeasurePreserving bernoulliRealBit ν (bernoulliMeasure true false p) :=
      ⟨measurable_bernoulliRealBit, map_bernoulliRealBit p⟩
    have hEval : MeasurePreserving (fun ω : Configuration d => ω e) μ
        (bernoulliMeasure true false p) := ⟨measurable_pi_apply e, latticeBondLaw_map_eval p e⟩
    have hA := hT.prod hbit
    have hB := (MeasurePreserving.id μ).prod hEval
    have hmapA := lintegral_map (μ := ρ.prod ν) hHm hA.measurable
    have hmapB := lintegral_map (μ := μ.prod μ) hHm hB.measurable
    rw [hA.map_eq] at hmapA
    rw [hB.map_eq] at hmapB
    change (∫⁻ q, H q ∂(μ.prod (bernoulliMeasure true false p))) =
      ∫⁻ q : (Bond d → ℝ) × ℝ, H (T q.1, bernoulliRealBit q.2) ∂(ρ.prod ν) at hmapA
    change (∫⁻ q, H q ∂(μ.prod (bernoulliMeasure true false p))) =
      ∫⁻ q : Configuration d × Configuration d, H (q.1, q.2 e) ∂(μ.prod μ) at hmapB
    rw [LatticeProb.siteEnergy_eq_lintegral_prod ν hF'm e]
    have hupdate (ω η : Configuration d) :
        Function.update ω e (η e) = resampleBond ω η e := by
      funext j
      by_cases hj : j = e
      · subst j
        simp [resampleBond]
      · simp [resampleBond, hj]
    calc
      _ = ∫⁻ q : Configuration d × Bool, H q ∂(μ.prod (bernoulliMeasure true false p)) := by
        symm
        simpa only [H, F', T, Function.comp_apply, Prod.map_apply,
          bernoulliRealConfiguration_update] using hmapA
      _ = ∫⁻ q : Configuration d × Configuration d,
          ENNReal.ofReal ((F q.1 - F (resampleBond q.1 q.2 e)) ^ 2) ∂(μ.prod μ) := by
        simpa only [H, Prod.map_apply, id_eq, hupdate] using hmapB
  have hmeas (e : Bond d) : Measurable (fun q : Configuration d × Configuration d =>
      ENNReal.ofReal ((F q.1 - F (resampleBond q.1 q.2 e)) ^ 2)) :=
    (((hF.comp measurable_fst).sub
      (hF.comp (measurePreserving_resampleBond d p e).measurable)).pow_const 2).ennreal_ofReal
  calc
    evariance F μ = evariance F' ρ := hvar
    _ ≤ (∑' e, LatticeProb.siteEnergy ν F' e) / 2 :=
      LatticeProb.evariance_le_half_tsum_siteEnergy ν hF'm hF'2
    _ = (∫⁻ q : Configuration d × Configuration d, ∑' e : Bond d,
        ENNReal.ofReal ((F q.1 - F (resampleBond q.1 q.2 e)) ^ 2) ∂(μ.prod μ)) / 2 := by
      simp_rw [he]
      rw [lintegral_tsum (fun e => (hmeas e).aemeasurable)]

end Rigidity.Proofs.S2

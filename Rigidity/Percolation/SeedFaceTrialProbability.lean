import Rigidity.Percolation.InfiniteSeedProbability
import Rigidity.Percolation.BondSeedFaceContacts

/-!
# Probability of an outward seed trial

A conditional lower bound for outward seed trials integrates to an explicit
probability bound in terms of the number of reached face contacts.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped MeasureTheory

/-- Integrating a conditional lower bound over a past-measurable event gives
a lower bound for the unconditional success probability. -/
theorem mul_measureReal_le_of_condExp_indicator_lower {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {G C : Set Ω} (hG : MeasurableSet[m] G) (hC : @MeasurableSet Ω m₀ C) (δ : ℝ)
    (hcond : ∀ᵐ ω ∂μ.restrict G, δ ≤ μ[C.indicator (fun _ => (1 : ℝ)) | m] ω) :
    δ * μ.real G ≤ μ.real C := by
  have hInt : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hC
  have hbound := setIntegral_mono_ae_restrict (integrable_const δ).integrableOn
    integrable_condExp.integrableOn hcond
  rw [setIntegral_condExp hm hInt hG, setIntegral_indicator hC,
    setIntegral_const, setIntegral_const] at hbound
  have hbound' : δ * μ.real G ≤ μ.real (G ∩ C) := by
    simpa only [smul_eq_mul, mul_one, one_mul, mul_comm] using hbound
  exact hbound'.trans (measureReal_mono Set.inter_subset_right (measure_ne_top _ _))

/-- A lower bound on the number of reached contacts yields an unconditional
probability bound for a fresh outward seed trial. -/
theorem measureReal_seedReachableFaceSuccess_lower {d k m : ℕ} (hk : 0 < k)
    (q r : unitInterval) (B : Set (Vertex d)) (roots face : Finset (Vertex d))
    (j : Fin d) (n : ℤ) (hface : ∀ x ∈ face, x j = n) :
    (1 - (1 - (r : ℝ) ^ ((k ^ d + 1) ^ 2)) ^ m) *
      (1 - (latticeBondLaw d q).real (fewSeedContacts B roots face (m * k ^ d))) ≤
    (bondPairLaw d q r).real (seedReachableFaceSuccess B roots face k j n) := by
  haveI : IsProbabilityMeasure (bondPairLaw d q r) := by
    dsimp only [bondPairLaw]
    infer_instance
  have hbase : Measurable (@baseBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_fst.comp (measurable_pi_apply e)
  let F := fewSeedContacts B roots face (m * k ^ d)
  let G := baseBondConfiguration ⁻¹' Fᶜ
  have hF := measurableSet_fewSeedContacts B roots face (m * k ^ d)
  have hG : MeasurableSet[baseBondSigma d] G := (comap_measurable _) hF.compl
  have hG' : MeasurableSet G := hbase hF.compl
  have hcard : ∀ ω ∈ G, m * k ^ d ≤
      (seedReachableContacts B roots face (baseBondConfiguration ω)).card := by
    intro ω hω
    exact Nat.le_of_not_gt hω
  have hc := condExp_indicator_lower_of_seed_face_contacts hk q r B roots face j n hface hG' hcard
  have hb := mul_measureReal_le_of_condExp_indicator_lower (bondPairLaw d q r)
    hbase.comap_le hG (measurableSet_seedReachableFaceSuccess B roots face k j n) _ hc
  have hmap : (bondPairLaw d q r).real G = 1 - (latticeBondLaw d q).real F := by
    change (bondPairLaw d q r).real (baseBondConfiguration ⁻¹' Fᶜ) = _
    rw [measureReal_def, ← Measure.map_apply hbase hF.compl, bondPairLaw_map_base]
    change (latticeBondLaw d q).real Fᶜ = _
    rw [measureReal_compl hF, probReal_univ]
  rwa [hmap] at hb

end Rigidity.Percolation

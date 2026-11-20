import Rigidity.Percolation.SlabFiniteEnergy
import LatticeProb.Prob.Percolation.LatticeBondCritical

/-!
# Parameters for bond sprinkling

A density strictly above criticality can be decomposed into a supercritical
base density and an independent positive sprinkling density.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory

/-- A larger density can be written as the density of the union of a base
Bernoulli field and a positive independent sprinkling. -/
theorem exists_sprinkling_parameter (q p : unitInterval) (hqp : (q : ℝ) < p) :
    ∃ r : unitInterval, 0 < (r : ℝ) ∧
      (q : ℝ) + (1 - (q : ℝ)) * (r : ℝ) = (p : ℝ) := by
  have hq1 : (q : ℝ) < 1 := lt_of_lt_of_le hqp p.property.2
  have hden : 0 < 1 - (q : ℝ) := sub_pos.mpr hq1
  have hnum : 0 < (p : ℝ) - q := sub_pos.mpr hqp
  have hr : ((p : ℝ) - q) / (1 - q) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact (div_pos hnum hden).le
    · apply (div_le_one hden).2
      linarith [p.property.2]
  refine ⟨⟨((p : ℝ) - q) / (1 - q), hr⟩, div_pos hnum hden, ?_⟩
  field_simp
  ring

/-- A supercritical bond density admits a strictly smaller density with
positive infinite-cluster probability and a positive sprinkling that restores
the original density. -/
theorem exists_supercritical_bond_sprinkling {d : ℕ} [NeZero d] (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ q r : unitInterval, 0 < theta d q ∧ (q : ℝ) < p ∧ 0 < (r : ℝ) ∧
      (q : ℝ) + (1 - (q : ℝ)) * (r : ℝ) = p := by
  obtain ⟨q, hq, hqp⟩ := (criticalProbability_lt_iff (p : ℝ)).mp hp
  obtain ⟨r, hr, heq⟩ := exists_sprinkling_parameter q p hqp
  exact ⟨q, r, hq, hqp, hr, heq⟩

/-- The density of the union of independent base and sprinkling bonds. -/
def sprinkledDensity (q r : unitInterval) : unitInterval :=
  ⟨(q : ℝ) + (1 - (q : ℝ)) * (r : ℝ), by
    constructor
    · exact add_nonneg q.property.1 (mul_nonneg (sub_nonneg.mpr q.property.2) r.property.1)
    · have h := mul_nonneg (sub_nonneg.mpr q.property.2) (sub_nonneg.mpr r.property.2)
      nlinarith⟩

/-- The union of two independent Bernoulli bonds is Bernoulli with the
corresponding sprinkled density. -/
theorem map_or_bernoulli (q r : unitInterval) :
    ((bernoulliMeasure true false q).prod (bernoulliMeasure true false r)).map
      (fun z : Bool × Bool => z.1 || z.2) =
      bernoulliMeasure true false (sprinkledDensity q r) := by
  have hm : Measurable (fun z : Bool × Bool => z.1 || z.2) := by fun_prop
  have hf : (fun z : Bool × Bool => z.1 || z.2) ⁻¹' ({false} : Set Bool) =
      ({false} : Set Bool) ×ˢ ({false} : Set Bool) := by
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp
  have hmapfalse : (((bernoulliMeasure true false q).prod
      (bernoulliMeasure true false r)).map (fun z : Bool × Bool => z.1 || z.2)).real {false} =
      (1 - (q : ℝ)) * (1 - (r : ℝ)) := by
    rw [measureReal_def, Measure.map_apply hm (measurableSet_singleton false), hf]
    change ((bernoulliMeasure true false q).prod (bernoulliMeasure true false r)).real
      (({false} : Set Bool) ×ˢ ({false} : Set Bool)) = _
    rw [measureReal_prod_prod]
    have hq : (bernoulliMeasure true false q).real {false} = 1 - (q : ℝ) :=
      bernoulliMeasure_real_apply_of_notMem_of_mem q (measurableSet_singleton false) (by simp) (by simp)
    have hr : (bernoulliMeasure true false r).real {false} = 1 - (r : ℝ) :=
      bernoulliMeasure_real_apply_of_notMem_of_mem r (measurableSet_singleton false) (by simp) (by simp)
    rw [hq, hr]
  have htargetfalse : (bernoulliMeasure true false (sprinkledDensity q r)).real {false} =
      (1 - (q : ℝ)) * (1 - (r : ℝ)) := by
    rw [bernoulliMeasure_real_apply_of_notMem_of_mem _ (measurableSet_singleton false)
      (by simp) (by simp)]
    change 1 - ((q : ℝ) + (1 - (q : ℝ)) * (r : ℝ)) = _
    ring
  haveI : IsProbabilityMeasure (((bernoulliMeasure true false q).prod
      (bernoulliMeasure true false r)).map (fun z : Bool × Bool => z.1 || z.2)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_measureReal_singleton
  intro b
  cases b with
  | false => exact hmapfalse.trans htargetfalse.symm
  | true =>
    have h₁ := measureReal_compl (μ := ((bernoulliMeasure true false q).prod
      (bernoulliMeasure true false r)).map (fun z : Bool × Bool => z.1 || z.2))
      (measurableSet_singleton false)
    have h₂ := measureReal_compl (μ := bernoulliMeasure true false (sprinkledDensity q r))
      (measurableSet_singleton false)
    have hcompl : ({false} : Set Bool)ᶜ = {true} := by ext b; cases b <;> simp
    rw [hcompl, probReal_univ] at h₁ h₂
    linarith

/-- The product law of independent pairs of base and sprinkling bonds. -/
noncomputable def bondPairLaw (d : ℕ) (q r : unitInterval) :
    Measure (Bond d → Bool × Bool) :=
  Measure.infinitePi (fun _ : Bond d =>
    (bernoulliMeasure true false q).prod (bernoulliMeasure true false r))

/-- The base bond configuration in a field of bond pairs. -/
def baseBondConfiguration {d : ℕ} (ω : Bond d → Bool × Bool) : Configuration d :=
  fun e => (ω e).1

/-- The sprinkling bond configuration in a field of bond pairs. -/
def addedBondConfiguration {d : ℕ} (ω : Bond d → Bool × Bool) : Configuration d :=
  fun e => (ω e).2

/-- A bond is open in the sprinkled configuration if either layer opens it. -/
def sprinkledBondConfiguration {d : ℕ} (ω : Bond d → Bool × Bool) : Configuration d :=
  fun e => (ω e).1 || (ω e).2

/-- The base layer has the canonical bond law. -/
theorem bondPairLaw_map_base (d : ℕ) (q r : unitInterval) :
    (bondPairLaw d q r).map baseBondConfiguration = latticeBondLaw d q := by
  change (Measure.infinitePi (fun _ : Bond d =>
    (bernoulliMeasure true false q).prod (bernoulliMeasure true false r))).map
      (fun ω e => (ω e).1) = _
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_fst)]
  simp only [Measure.map_fst_prod, measure_univ, one_smul, latticeBondLaw]

/-- The added layer has the canonical bond law. -/
theorem bondPairLaw_map_added (d : ℕ) (q r : unitInterval) :
    (bondPairLaw d q r).map addedBondConfiguration = latticeBondLaw d r := by
  change (Measure.infinitePi (fun _ : Bond d =>
    (bernoulliMeasure true false q).prod (bernoulliMeasure true false r))).map
      (fun ω e => (ω e).2) = _
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_snd)]
  simp only [Measure.map_snd_prod, measure_univ, one_smul, latticeBondLaw]

/-- The union of the two bond layers has the canonical law at the sprinkled
density. -/
theorem bondPairLaw_map_sprinkled (d : ℕ) (q r : unitInterval) :
    (bondPairLaw d q r).map sprinkledBondConfiguration =
      latticeBondLaw d (sprinkledDensity q r) := by
  have hm : Measurable (fun z : Bool × Bool => z.1 || z.2) := by fun_prop
  change (Measure.infinitePi (fun _ : Bond d =>
    (bernoulliMeasure true false q).prod (bernoulliMeasure true false r))).map
      (fun ω e => (ω e).1 || (ω e).2) = _
  rw [Measure.infinitePi_map_pi _ (fun _ => hm)]
  simp only [map_or_bernoulli, latticeBondLaw]

end Rigidity.Percolation

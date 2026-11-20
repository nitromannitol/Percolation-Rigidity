import Rigidity.Percolation.SlabFiniteEnergy
import LatticeProb.Prob.Percolation.LatticeBondCritical
import Mathlib.Probability.Independence.Process.Basic

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

/-- On every finite family of bonds, the base and added layer assignments
have the product of their separate probabilities. -/
theorem bondPairLaw_finite_layer_assignments (d : ℕ) (q r : unitInterval)
    (s : Finset (Bond d)) (a b : Configuration d) :
    bondPairLaw d q r {ω | ∀ e ∈ s, (ω e).1 = a e ∧ (ω e).2 = b e} =
      latticeBondLaw d q {ω | ∀ e ∈ s, ω e = a e} *
        latticeBondLaw d r {ω | ∀ e ∈ s, ω e = b e} := by
  have hpair : {ω : Bond d → Bool × Bool | ∀ e ∈ s, (ω e).1 = a e ∧ (ω e).2 = b e} =
      (↑s : Set (Bond d)).pi (fun e => ({a e} : Set Bool) ×ˢ ({b e} : Set Bool)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_singleton_iff]
  have hbase : {ω : Configuration d | ∀ e ∈ s, ω e = a e} =
      (↑s : Set (Bond d)).pi (fun e => ({a e} : Set Bool)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Set.mem_singleton_iff]
  have hadd : {ω : Configuration d | ∀ e ∈ s, ω e = b e} =
      (↑s : Set (Bond d)).pi (fun e => ({b e} : Set Bool)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Set.mem_singleton_iff]
  rw [hpair, hbase, hadd, bondPairLaw, latticeBondLaw, latticeBondLaw]
  rw [Measure.infinitePi_pi, Measure.infinitePi_pi, Measure.infinitePi_pi]
  · simp only [Measure.prod_prod, Finset.prod_mul_distrib]
  · exact fun e _ => measurableSet_singleton (b e)
  · exact fun e _ => measurableSet_singleton (a e)
  · exact fun e _ => (measurableSet_singleton (a e)).prod (measurableSet_singleton (b e))

/-- The restrictions of the two bond layers to the same finite set are
independent. -/
theorem bondPairLaw_indep_restrictions (d : ℕ) (q r : unitInterval) (s : Finset (Bond d)) :
    IndepFun (fun ω (e : s) => (ω e).1) (fun ω (e : s) => (ω e).2) (bondPairLaw d q r) := by
  classical
  let X : (Bond d → Bool × Bool) → (s → Bool) := fun ω e => (ω e).1
  let Y : (Bond d → Bool × Bool) → (s → Bool) := fun ω e => (ω e).2
  have hX : Measurable X := by dsimp only [X]; fun_prop
  have hY : Measurable Y := by dsimp only [Y]; fun_prop
  have hB : Measurable (@baseBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_fst.comp (measurable_pi_apply e)
  have hA : Measurable (@addedBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_snd.comp (measurable_pi_apply e)
  have hres : Measurable (fun ω : Configuration d => fun e : s => ω e) := by fun_prop
  haveI : IsProbabilityMeasure (bondPairLaw d q r) := by
    dsimp only [bondPairLaw]
    infer_instance
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).2
  apply Measure.ext_of_singleton
  rintro ⟨u, v⟩
  let a : Configuration d := fun e => if he : e ∈ s then u ⟨e, he⟩ else false
  let b : Configuration d := fun e => if he : e ∈ s then v ⟨e, he⟩ else false
  have hpre : (fun ω => (X ω, Y ω)) ⁻¹' ({(u, v)} : Set ((s → Bool) × (s → Bool))) =
      {ω | ∀ e ∈ s, (ω e).1 = a e ∧ (ω e).2 = b e} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, funext_iff,
      X, Y, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hu, hv⟩ e he
      exact ⟨by simpa only [a, dif_pos he] using hu ⟨e, he⟩,
        by simpa only [b, dif_pos he] using hv ⟨e, he⟩⟩
    · intro h
      exact ⟨fun e => by simpa only [a, dif_pos e.property] using (h e e.property).1,
        fun e => by simpa only [b, dif_pos e.property] using (h e e.property).2⟩
  have hbaseSet : (fun ω : Configuration d => fun e : s => ω e) ⁻¹' ({u} : Set (s → Bool)) =
      {ω | ∀ e ∈ s, ω e = a e} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_setOf_eq]
    constructor
    · intro h e he
      simpa only [a, dif_pos he] using h ⟨e, he⟩
    · intro h e
      simpa only [a, dif_pos e.property] using h e e.property
  have haddSet : (fun ω : Configuration d => fun e : s => ω e) ⁻¹' ({v} : Set (s → Bool)) =
      {ω | ∀ e ∈ s, ω e = b e} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_setOf_eq]
    constructor
    · intro h e he
      simpa only [b, dif_pos he] using h ⟨e, he⟩
    · intro h e
      simpa only [b, dif_pos e.property] using h e e.property
  have hbase : (bondPairLaw d q r).map X {u} =
      latticeBondLaw d q {ω | ∀ e ∈ s, ω e = a e} := by
    change (bondPairLaw d q r).map ((fun ω : Configuration d => fun e : s => ω e) ∘
      baseBondConfiguration) {u} = _
    rw [← Measure.map_map hres hB, bondPairLaw_map_base,
      Measure.map_apply hres (measurableSet_singleton u), hbaseSet]
  have hadd : (bondPairLaw d q r).map Y {v} =
      latticeBondLaw d r {ω | ∀ e ∈ s, ω e = b e} := by
    change (bondPairLaw d q r).map ((fun ω : Configuration d => fun e : s => ω e) ∘
      addedBondConfiguration) {v} = _
    rw [← Measure.map_map hres hA, bondPairLaw_map_added,
      Measure.map_apply hres (measurableSet_singleton v), haddSet]
  rw [Measure.map_apply (hX.prodMk hY) (measurableSet_singleton (u, v)), hpre,
    ← Set.singleton_prod_singleton, Measure.prod_prod, hbase, hadd]
  exact bondPairLaw_finite_layer_assignments d q r s a b

/-- The base and added bond configurations are independent as full random
fields. -/
theorem bondPairLaw_indep_layers (d : ℕ) (q r : unitInterval) :
    IndepFun baseBondConfiguration addedBondConfiguration (bondPairLaw d q r) := by
  classical
  haveI : IsProbabilityMeasure (bondPairLaw d q r) := by
    dsimp only [bondPairLaw]
    infer_instance
  change IndepFun (fun ω : Bond d → Bool × Bool => fun e => (ω e).1)
    (fun ω : Bond d → Bool × Bool => fun e => (ω e).2) _
  have hX (e : Bond d) : Measurable (fun ω : Bond d → Bool × Bool => (ω e).1) :=
    measurable_fst.comp (measurable_pi_apply e)
  have hY (e : Bond d) : Measurable (fun ω : Bond d → Bool × Bool => (ω e).2) :=
    measurable_snd.comp (measurable_pi_apply e)
  refine IndepFun.process_indepFun_process hX hY ?_
  intro I J
  let S := I ∪ J
  let left : (S → Bool) → (I → Bool) := fun f e => f ⟨e, Finset.mem_union_left J e.property⟩
  let right : (S → Bool) → (J → Bool) := fun f e => f ⟨e, Finset.mem_union_right I e.property⟩
  have hleft : Measurable left := by dsimp only [left]; fun_prop
  have hright : Measurable right := by dsimp only [right]; fun_prop
  have hind := (bondPairLaw_indep_restrictions d q r S).comp hleft hright
  exact hind

/-- The joint law of the two independent layers is the product of their
canonical bond laws. -/
theorem bondPairLaw_map_layers (d : ℕ) (q r : unitInterval) :
    (bondPairLaw d q r).map (fun ω => (baseBondConfiguration ω, addedBondConfiguration ω)) =
      (latticeBondLaw d q).prod (latticeBondLaw d r) := by
  haveI : IsProbabilityMeasure (bondPairLaw d q r) := by
    dsimp only [bondPairLaw]
    infer_instance
  have hB : Measurable (@baseBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_fst.comp (measurable_pi_apply e)
  have hA : Measurable (@addedBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_snd.comp (measurable_pi_apply e)
  rw [(bondPairLaw_indep_layers d q r).map_prod_eq_prod_map_map hB.aemeasurable hA.aemeasurable,
    bondPairLaw_map_base, bondPairLaw_map_added]

/-- The union of two independent canonical bond fields has the canonical law
at the sprinkled density. -/
theorem latticeBondLaw_prod_map_or (d : ℕ) (q r : unitInterval) :
    ((latticeBondLaw d q).prod (latticeBondLaw d r)).map
      (fun ω e => ω.1 e || ω.2 e) = latticeBondLaw d (sprinkledDensity q r) := by
  have hB : Measurable (@baseBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_fst.comp (measurable_pi_apply e)
  have hA : Measurable (@addedBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_snd.comp (measurable_pi_apply e)
  have hpair : Measurable (fun ω => (baseBondConfiguration ω, addedBondConfiguration ω)) :=
    hB.prodMk hA
  have hor : Measurable (fun ω : Configuration d × Configuration d => fun e => ω.1 e || ω.2 e) := by
    fun_prop
  rw [← bondPairLaw_map_layers, Measure.map_map hor hpair]
  exact bondPairLaw_map_sprinkled d q r

/-- Any supercritical bond law can be realized as the union of an independent
positive sprinkle and a lower-density field with positive percolation probability. -/
theorem exists_supercritical_bond_sprinkling_coupling {d : ℕ} [NeZero d] (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ q r : unitInterval, 0 < theta d q ∧ (q : ℝ) < p ∧ 0 < (r : ℝ) ∧
      ((latticeBondLaw d q).prod (latticeBondLaw d r)).map
        (fun ω e => ω.1 e || ω.2 e) = latticeBondLaw d p := by
  obtain ⟨q, r, hθ, hqp, hr, heq⟩ := exists_supercritical_bond_sprinkling p hp
  have hdensity : sprinkledDensity q r = p := Subtype.ext heq
  refine ⟨q, r, hθ, hqp, hr, ?_⟩
  rw [latticeBondLaw_prod_map_or, hdensity]

end Rigidity.Percolation

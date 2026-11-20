import Rigidity.Percolation.SelectedBondMarkThresholds

/-!
# Conditional opening of selected boundary bonds

Conditioning finitely many boundary marks to exceed prescribed thresholds
leaves exterior-selected candidates available for independent threshold
increments.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- At least one selected mark is at most its increased threshold. -/
def selectedBondMarkSuccess {d : ℕ} (U : BondMarks d → Finset (Bond d))
    (β : Bond d → unitInterval) (δ : ℝ) (hδ : 0 ≤ δ)
    (hβ : ∀ e, (β e : ℝ) + δ ≤ 1) : Set (BondMarks d) :=
  {ω | ∃ e ∈ U ω, ω e ≤ raisedBondThreshold β δ hδ hβ (U ω) e}

/-- Selected-mark success is measurable when the selection is measurable. -/
theorem measurableSet_selectedBondMarkSuccess {d : ℕ} (F : Finset (Bond d))
    (U : BondMarks d → Finset (Bond d))
    (hU : @Measurable _ _ (bondMarkSigma (↑F : Set (Bond d))ᶜ) _ U)
    (β : Bond d → unitInterval) (δ : ℝ) (hδ : 0 ≤ δ)
    (hβ : ∀ e, (β e : ℝ) + δ ≤ 1) :
    MeasurableSet (selectedBondMarkSuccess U β δ hδ hβ) := by
  classical
  let γ : Bond d → unitInterval := fun e =>
    ⟨(β e : ℝ) + δ, add_nonneg (β e).property.1 hδ, hβ e⟩
  have heq : selectedBondMarkSuccess U β δ hδ hβ =
      ⋃ e : Bond d, {ω | e ∈ U ω} ∩ (fun ω : BondMarks d => ω e) ⁻¹' Set.Iic (γ e) := by
    ext ω
    simp only [selectedBondMarkSuccess, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨e, he, h⟩
      exact ⟨e, he, by simpa only [raisedBondThreshold, he, ↓reduceIte, γ] using h⟩
    · rintro ⟨e, he, h⟩
      exact ⟨e, he, by simpa only [raisedBondThreshold, he, ↓reduceIte, γ] using h⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro e
  have hlocal : MeasurableSet[bondMarkSigma (↑F : Set (Bond d))ᶜ] {ω | e ∈ U ω} := by
    letI : MeasurableSpace (BondMarks d) := bondMarkSigma (↑F : Set (Bond d))ᶜ
    exact measurableSet_setOf.mpr ((measurable_finset_iff.mp hU) e)
  exact (bondMarkSigma_le _ _ hlocal).inter
    (measurableSet_Iic.preimage (measurable_pi_apply e))

/-- Conditioning the boundary marks above `β`, failure to open any of the
selected candidates costs at most the probability of too few candidates plus
`(1 - δ)^t`. This bound is stated before division by the conditioning event. -/
theorem bondMarkLaw_real_selected_failure_le {d : ℕ} (F : Finset (Bond d))
    (U : BondMarks d → Finset (Bond d))
    (hU : @Measurable _ _ (bondMarkSigma (↑F : Set (Bond d))ᶜ) _ U)
    (hsub : ∀ ω, U ω ⊆ F) (β : Bond d → unitInterval) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hβ : ∀ e, (β e : ℝ) + δ ≤ 1)
    (t : ℕ) (ε : ℝ) (hsmall : (bondMarkLaw d).real {ω | (U ω).card < t} ≤ ε) :
    (bondMarkLaw d).real (bondMarksAbove F β ∩
      (selectedBondMarkSuccess U β δ hδ hβ)ᶜ) ≤
        (ε + (1 - δ) ^ t) * (bondMarkLaw d).real (bondMarksAbove F β) := by
  classical
  haveI : IsProbabilityMeasure (bondMarkLaw d) := by
    dsimp only [bondMarkLaw]
    infer_instance
  let μ := bondMarkLaw d
  let A : Set (BondMarks d) := {ω | (U ω).card < t}
  let H := bondMarksAbove F β
  let C := selectedBondMarkSuccess U β δ hδ hβ
  let E : Set (BondMarks d) := {ω | t ≤ (U ω).card ∧
    ω ∈ bondMarksAbove F (raisedBondThreshold β δ hδ hβ (U ω))}
  have hA : MeasurableSet[bondMarkSigma (↑F : Set (Bond d))ᶜ] A := by
    have hc : @Measurable _ _ (bondMarkSigma (↑F : Set (Bond d))ᶜ) _
        (fun ω => (U ω).card) := (measurable_of_countable Finset.card).comp hU
    exact hc (Set.to_countable {n : ℕ | n < t}).measurableSet
  have hdisj : Disjoint (↑F : Set (Bond d))ᶜ (↑F : Set (Bond d)) := by
    rw [Set.disjoint_left]
    intro e he hf
    exact he hf
  have hind := (Indep_iff _ _ _).mp (indep_bondMarkSigma hdisj) _ _ hA
    (measurableSet_bondMarksAbove_local F β)
  have hreal : μ.real (A ∩ H) = μ.real A * μ.real H := by
    change (μ (A ∩ H)).toReal = _
    rw [hind, ENNReal.toReal_mul]
    rfl
  have hcover : H ∩ Cᶜ ⊆ (A ∩ H) ∪ E := by
    rintro ω ⟨hH, hC⟩
    by_cases hsmallω : (U ω).card < t
    · exact Or.inl ⟨hsmallω, hH⟩
    · refine Or.inr ⟨Nat.le_of_not_gt hsmallω, ?_⟩
      intro e heF
      by_cases heU : e ∈ U ω
      · have hn : ¬ ω e ≤ raisedBondThreshold β δ hδ hβ (U ω) e :=
          fun h => hC ⟨e, heU, h⟩
        exact lt_of_not_ge hn
      · simpa only [raisedBondThreshold, heU, ↓reduceIte] using hH e heF
  have hE := bondMarkLaw_real_selected_raised_le F U hU hsub β δ hδ hδ1 hβ t
  calc
    _ ≤ μ.real ((A ∩ H) ∪ E) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ μ.real (A ∩ H) + μ.real E := measureReal_union_le _ _
    _ ≤ ε * μ.real H + (1 - δ) ^ t * μ.real H := by
      rw [hreal]
      exact add_le_add (mul_le_mul_of_nonneg_right hsmall measureReal_nonneg) hE
    _ = _ := by ring

/-- Positive threshold increments make the boundary conditioning event
strictly positive. -/
theorem bondMarkLaw_real_bondMarksAbove_pos {d : ℕ} (F : Finset (Bond d))
    (β : Bond d → unitInterval) (δ : ℝ) (hδ : 0 < δ)
    (hβ : ∀ e ∈ F, (β e : ℝ) + δ ≤ 1) :
    0 < (bondMarkLaw d).real (bondMarksAbove F β) := by
  rw [bondMarkLaw_real_bondMarksAbove]
  apply Finset.prod_pos
  intro e he
  have h := hβ e he
  linarith

/-- The conditional probability of opening an exterior-selected boundary
candidate is at least one minus the probability of too few candidates and the
geometric failure probability. -/
theorem conditional_selectedBondMarkSuccess_lower {d : ℕ} (F : Finset (Bond d))
    (U : BondMarks d → Finset (Bond d))
    (hU : @Measurable _ _ (bondMarkSigma (↑F : Set (Bond d))ᶜ) _ U)
    (hsub : ∀ ω, U ω ⊆ F) (β : Bond d → unitInterval) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hβ : ∀ e, (β e : ℝ) + δ ≤ 1)
    (t : ℕ) (ε : ℝ) (hsmall : (bondMarkLaw d).real {ω | (U ω).card < t} ≤ ε) :
    1 - ε - (1 - δ) ^ t ≤
      (bondMarkLaw d).real (bondMarksAbove F β ∩
        selectedBondMarkSuccess U β δ hδ.le hβ) /
          (bondMarkLaw d).real (bondMarksAbove F β) := by
  haveI : IsProbabilityMeasure (bondMarkLaw d) := by
    dsimp only [bondMarkLaw]
    infer_instance
  have hpos := bondMarkLaw_real_bondMarksAbove_pos F β δ hδ (fun e _ => hβ e)
  have hfail := bondMarkLaw_real_selected_failure_le F U hU hsub β δ hδ.le hδ1 hβ t ε hsmall
  have hC := measurableSet_selectedBondMarkSuccess F U hU β δ hδ.le hβ
  have hsum := measureReal_inter_add_sdiff (μ := bondMarkLaw d)
    (s := bondMarksAbove F β) hC (measure_ne_top _ _)
  rw [Set.sdiff_eq] at hsum
  apply (le_div_iff₀ hpos).mpr
  nlinarith

end Rigidity.Percolation

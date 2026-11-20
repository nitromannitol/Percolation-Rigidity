import Rigidity.Percolation.BoundaryCandidatesEnergy
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Uniform marks on bonds

Independent uniform bond marks couple all Bernoulli thresholds. A finite
family of marks staying above prescribed thresholds has a product probability.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- An independent uniform mark on each lattice bond. -/
abbrev BondMarks (d : ℕ) := Bond d → unitInterval

/-- The product law of independent uniform bond marks. -/
noncomputable def bondMarkLaw (d : ℕ) : Measure (BondMarks d) :=
  Measure.infinitePi (fun _ : Bond d => volume)

/-- The marks on a finite bond set exceed their prescribed thresholds. -/
def bondMarksAbove {d : ℕ} (F : Finset (Bond d)) (β : Bond d → unitInterval) :
    Set (BondMarks d) := {ω | ∀ e ∈ F, β e < ω e}

/-- A finite family of lower-threshold conditions is measurable. -/
theorem measurableSet_bondMarksAbove {d : ℕ} (F : Finset (Bond d))
    (β : Bond d → unitInterval) : MeasurableSet (bondMarksAbove F β) := by
  have heq : bondMarksAbove F β = ⋂ e ∈ F, (fun ω : BondMarks d => ω e) ⁻¹' Set.Ioi (β e) := by
    ext ω
    simp only [bondMarksAbove, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]
  rw [heq]
  exact F.measurableSet_biInter fun e _ => measurableSet_Ioi.preimage (measurable_pi_apply e)

/-- The probability that all marks exceed their thresholds is the product of
the corresponding upper-tail lengths. -/
theorem bondMarkLaw_real_bondMarksAbove {d : ℕ} (F : Finset (Bond d))
    (β : Bond d → unitInterval) :
    (bondMarkLaw d).real (bondMarksAbove F β) = ∏ e ∈ F, (1 - (β e : ℝ)) := by
  have heq : bondMarksAbove F β = (↑F : Set (Bond d)).pi (fun e => Set.Ioi (β e)) := by
    ext ω
    simp only [bondMarksAbove, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Set.mem_Ioi]
  rw [measureReal_def, heq, bondMarkLaw, Measure.infinitePi_pi]
  · rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro e _
    rw [unitInterval.volume_Ioi, ENNReal.toReal_ofReal (sub_nonneg.mpr (β e).property.2)]
  · exact fun _ _ => measurableSet_Ioi

/-- Raising selected thresholds by `δ` reduces the joint upper-tail
probability by at least a factor `1 - δ` for each selected bond. -/
theorem bondMarkLaw_real_raised_thresholds_le {d : ℕ} (F U : Finset (Bond d))
    (hUF : U ⊆ F) (β : Bond d → unitInterval) (δ : ℝ) (hδ : 0 ≤ δ)
    (hβ : ∀ e ∈ U, (β e : ℝ) + δ ≤ 1) :
    let γ : Bond d → unitInterval := fun e =>
      if he : e ∈ U then ⟨(β e : ℝ) + δ,
        add_nonneg (β e).property.1 hδ, hβ e he⟩ else β e
    (bondMarkLaw d).real (bondMarksAbove F γ) ≤
      (1 - δ) ^ U.card * (bondMarkLaw d).real (bondMarksAbove F β) := by
  classical
  intro γ
  rw [bondMarkLaw_real_bondMarksAbove, bondMarkLaw_real_bondMarksAbove]
  calc
    _ ≤ ∏ e ∈ F, (if e ∈ U then 1 - δ else 1) * (1 - (β e : ℝ)) := by
      apply Finset.prod_le_prod
      · intro e _
        exact sub_nonneg.mpr (γ e).property.2
      · intro e heF
        by_cases he : e ∈ U
        · simp only [he, ↓reduceIte, γ, ↓reduceDIte, Subtype.coe_mk]
          have hb := (β e).property.1
          nlinarith [mul_nonneg hδ hb]
        · simp only [he, ↓reduceIte, γ, ↓reduceDIte, one_mul]
          exact le_rfl
    _ = (∏ e ∈ F, (if e ∈ U then 1 - δ else 1)) *
        (∏ e ∈ F, (1 - (β e : ℝ))) := by rw [Finset.prod_mul_distrib]
    _ = _ := by
      congr 1
      calc
        _ = ∏ e ∈ U, (if e ∈ U then 1 - δ else 1) := by
          symm
          apply Finset.prod_subset hUF
          intro e _ he
          simp only [he, ↓reduceIte]
        _ = ∏ _e ∈ U, (1 - δ) := by
          apply Finset.prod_congr rfl
          intro e he
          simp only [he, ↓reduceIte]
        _ = _ := by simp only [Finset.prod_const]

end Rigidity.Percolation

import Rigidity.External.JordanCurve
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Closed paths and circle maps

A closed path descends to the circle obtained by identifying the two endpoints of the unit
interval.
-/

open Set Metric

namespace Rigidity.Topology

open Rigidity.External

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- A closed path descends to the quotient identifying the interval endpoints. -/
def closedPathQuot {q : S2} (β : Path q q) :
    Quot (AddCircle.EndpointIdent (1 : ℝ) 0) → S2 :=
  Quot.lift (fun t : Icc (0 : ℝ) (0 + 1) => β ⟨t.1, by simpa using t.2⟩) (by
    rintro _ _ ⟨⟩
    simp [β.source, β.target])

/-- The quotient map induced by a closed path is continuous. -/
theorem continuous_closedPathQuot {q : S2} (β : Path q q) :
    Continuous (closedPathQuot β) := by
  apply continuous_quot_lift
  apply β.continuous.comp
  exact continuous_subtype_val.subtype_mk _

/-- The circle map associated with a closed path. -/
noncomputable def closedPathCircle {q : S2} (β : Path q q) : Circle → S2 :=
  closedPathQuot β ∘ (AddCircle.homeoIccQuot (1 : ℝ) 0) ∘
    (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm

/-- The circle map associated with a closed path is continuous. -/
theorem continuous_closedPathCircle {q : S2} (β : Path q q) :
    Continuous (closedPathCircle β) :=
  (continuous_closedPathQuot β).comp
    ((AddCircle.homeoIccQuot (1 : ℝ) 0).continuous.comp
      (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm.continuous)

/-- The quotient map has the same range as the original closed path. -/
theorem range_closedPathQuot {q : S2} (β : Path q q) :
    range (closedPathQuot β) = range β := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    induction z using Quot.ind with
    | _ t => exact ⟨⟨t.1, by simpa using t.2⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨Quot.mk _ ⟨t.1, ?_⟩, ?_⟩
    · simp only [zero_add]
      exact t.2
    · rfl

/-- The circle map and the original path have the same range. -/
theorem range_closedPathCircle {q : S2} (β : Path q q) :
    range (closedPathCircle β) = range β := by
  calc
    range (closedPathCircle β) = range (closedPathQuot β) := by
      apply Set.Subset.antisymm
      · rintro x ⟨c, rfl⟩
        exact ⟨(AddCircle.homeoIccQuot (1 : ℝ) 0)
          ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm c), rfl⟩
      · rintro x ⟨z, rfl⟩
        refine ⟨AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
          ((AddCircle.homeoIccQuot (1 : ℝ) 0).symm z), ?_⟩
        simp only [closedPathCircle, Function.comp_apply, Homeomorph.symm_apply_apply,
          Homeomorph.apply_symm_apply]
    _ = range β := range_closedPathQuot β

/-- A closed path injective away from its final endpoint induces an injective circle map. -/
theorem injective_closedPathCircle {q : S2} (β : Path q q)
    (hβ : InjOn β (Ico 0 1)) : Function.Injective (closedPathCircle β) := by
  let h := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
  let e := AddCircle.equivIco (1 : ℝ) 0
  let u : Circle → unitInterval := fun c =>
    ⟨(e (h.symm c)).1, ⟨(e (h.symm c)).2.1, by
      have hp := (e (h.symm c)).2.2
      simp only [zero_add] at hp
      exact hp.le⟩⟩
  have hu (c : Circle) : u c ∈ Ico 0 1 := by
    change (0 : ℝ) ≤ (u c : ℝ) ∧ (u c : ℝ) < 1
    have hp := (e (h.symm c)).2
    simp only [zero_add] at hp
    exact hp
  have hr (c : Circle) : closedPathCircle β c = β (u c) := rfl
  intro c d hcd
  have heq : u c = u d := hβ (hu c) (hu d) (by simpa only [hr] using hcd)
  apply h.symm.injective
  apply e.injective
  have hv := congrArg (fun x : unitInterval => (x : ℝ)) heq
  exact Subtype.ext hv

end Rigidity.Topology

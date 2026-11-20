import LatticeProb.Prob.PiSum

/-!
# Exchangeability under one-coordinate resampling

Swapping a single coordinate between two independent product configurations preserves their
joint law.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb

/-- Exchanging one coordinate between independent product configurations preserves their law. -/
theorem measurePreserving_swap_coordinate {ι α : Type*} [DecidableEq ι] [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (i : ι) :
    MeasurePreserving (fun q : (ι → α) × (ι → α) =>
      (Function.update q.1 i (q.2 i), Function.update q.2 i (q.1 i)))
      ((Measure.infinitePi fun _ : ι => ν).prod (Measure.infinitePi fun _ : ι => ν))
      ((Measure.infinitePi fun _ : ι => ν).prod (Measure.infinitePi fun _ : ι => ν)) := by
  classical
  let P := Measure.infinitePi (fun _ : ι => ν)
  let Q := Measure.infinitePi (fun _ : ι ⊕ ι => ν)
  let e : (ι ⊕ ι) ≃ (ι ⊕ ι) := Equiv.swap (Sum.inl i) (Sum.inr i)
  let j : ((ι ⊕ ι) → α) ≃ᵐ ((ι → α) × (ι → α)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => α)
  let r : ((ι ⊕ ι) → α) ≃ᵐ ((ι ⊕ ι) → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι ⊕ ι => α) e
  have hj : MeasurePreserving j Q (P.prod P) := by
    refine ⟨j.measurable, ?_⟩
    exact infinitePi_sum (fun _ : ι ⊕ ι => ν)
  have hj' : MeasurePreserving j.symm (P.prod P) Q := by
    refine ⟨j.symm.measurable, ?_⟩
    exact infinitePi_sum_symm (fun _ : ι ⊕ ι => ν)
  have hr : MeasurePreserving r Q Q := by
    refine ⟨r.measurable, ?_⟩
    exact Measure.infinitePi_map_piCongrLeft (fun _ : ι ⊕ ι => ν) e
  have hcomp := hj.comp (hr.comp hj')
  convert hcomp using 1
  funext q
  apply Prod.ext <;> funext x <;>
    by_cases hx : x = i <;>
    simp [j, r, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
      Equiv.piCongrLeft', MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, Equiv.swap_apply_def, hx]

end Rigidity.Proofs.S2

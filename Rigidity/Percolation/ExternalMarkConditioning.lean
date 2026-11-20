import Rigidity.Percolation.BondMarkIndependence

/-!
# Conditioning on disjoint bond-mark histories

An event determined by marks outside a region can be added to the conditioning
without changing conditional probabilities for events inside the region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory

/-- Adding a positive-probability event determined by disjoint marks does not
change the conditional probability of a local event. -/
theorem bondMarkLaw_real_conditional_inter_of_disjoint {d : ℕ}
    (E F : Set (Bond d)) (hEF : Disjoint E F) (A H G : Set (BondMarks d))
    (hA : MeasurableSet[bondMarkSigma E] A)
    (hH : MeasurableSet[bondMarkSigma F] H)
    (hG : MeasurableSet[bondMarkSigma F] G)
    (hApos : 0 < (bondMarkLaw d).real A) (hHpos : 0 < (bondMarkLaw d).real H) :
    0 < (bondMarkLaw d).real (A ∩ H) ∧
    (bondMarkLaw d).real ((A ∩ H) ∩ G) / (bondMarkLaw d).real (A ∩ H) =
      (bondMarkLaw d).real (H ∩ G) / (bondMarkLaw d).real H := by
  have hIndep := (Indep_iff _ _ _).mp (indep_bondMarkSigma hEF)
  have hAH := hIndep A H hA hH
  have hAHG := hIndep A (H ∩ G) hA (hH.inter hG)
  have hprob : (bondMarkLaw d).real (A ∩ H) =
      (bondMarkLaw d).real A * (bondMarkLaw d).real H := by
    change ((bondMarkLaw d) (A ∩ H)).toReal = _
    rw [hAH, ENNReal.toReal_mul]
    rfl
  have hprob' : (bondMarkLaw d).real ((A ∩ H) ∩ G) =
      (bondMarkLaw d).real A * (bondMarkLaw d).real (H ∩ G) := by
    rw [Set.inter_assoc]
    change ((bondMarkLaw d) (A ∩ (H ∩ G))).toReal = _
    rw [hAHG, ENNReal.toReal_mul]
    rfl
  refine ⟨by rw [hprob]; exact mul_pos hApos hHpos, ?_⟩
  rw [hprob, hprob']
  field_simp

end Rigidity.Percolation

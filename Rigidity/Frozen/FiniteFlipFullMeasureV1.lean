import Rigidity.Support.BernoulliFiniteFlip

open MeasureTheory ProbabilityTheory RigidityFinitePatch RigidityFullProduct

namespace Rigidity

theorem finite_flip_full_measure (d : ℕ) (P : Measure (Bond d → Bool))
    [IsProbabilityMeasure P] (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hInd : iIndepFun (fun e (ω : Bond d → Bool) => ω e) P)
    (hMarg : ∀ e, P.map (fun ω => ω e) = bernoulliMeasure true false p)
    {A : Set (Bond d → Bool)} (hA : MeasurableSet A) (hfull : P A = 1) :
    P {ω | ∀ f : Bond d → Bool,
      Set.Finite {e | f e = true} → maskFlip f ω ∈ A} = 1 := by
  exact RigidityFullProduct.bond_all_masks d P p hp0 hp1 hInd hMarg hA hfull

end Rigidity

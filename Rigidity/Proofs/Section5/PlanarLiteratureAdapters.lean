import Rigidity.External.PlanarInputs
import Rigidity.Proofs.Section5.SublinearLiouville
import Rigidity.Steps.Section5.FastDecayPotential

/-!
# Planar adapters for qualitative literature inputs

The order-zero Liouville conclusion and existence of corrected planes use only the planar
specializations of their inputs.
-/

namespace Rigidity.Proofs.Section5

open MeasureTheory LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- The slope-zero Liouville step from planar order-zero regularity. -/
theorem sublinearLiouvilleStep_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (input : Rigidity.External.ArmstrongDarioOrderZeroTwo) :
    Rigidity.Steps.S3.SublinearLiouvilleStep 2 p := by
  obtain ⟨_, _, _, _, _, _, X, _, _, _, _, hae⟩ := input p hpc hp1
  filter_upwards [hae] with ω hω
  intro h v hharm hsub
  obtain ⟨-, hω⟩ := hω
  obtain ⟨hfin, hrank, -⟩ := hω h
  have hv : v ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 0 :=
    ⟨hharm, Rigidity.Proofs.S3.componentL2Subpolynomial_zero_of_slope_asymptotics _ v hsub⟩
  obtain ⟨c, hc⟩ := harmonicGrowthSpace_zero_eq_const _ hfin hrank v hv
  exact ⟨c, fun x => congrFun hc x⟩

/-- The planar sublinear Liouville theorem from planar order-zero regularity. -/
theorem sublinearLiouville_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (input : Rigidity.External.ArmstrongDarioOrderZeroTwo) : SublinearLiouville p := by
  filter_upwards [sublinearLiouvilleStep_two p hpc hp1 input] with ω hω
  intro h v hharm hsub
  exact hω h v hharm (componentSlopeAsymptotics_zero_of_sublinear _ v hsub)

/-- Almost surely the planar infinite cluster has corrected planes of the coordinate slopes. -/
theorem correctedPlanesExist_of_input_two (hC : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    CorrectedPlanesExist p := by
  filter_upwards [hC p hp hp1] with ω hω h i
  have : Infinite (uniqueInfiniteComponent h) :=
    Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)
  obtain ⟨o⟩ := (inferInstance : Nonempty (uniqueInfiniteComponent h))
  obtain ⟨ℓ, hℓ, -⟩ := (hω h).1 (Pi.single i 1) o
  exact ⟨ℓ, hℓ.1⟩

end Rigidity.Proofs.Section5

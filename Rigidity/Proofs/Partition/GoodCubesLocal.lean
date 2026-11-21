import Rigidity.Proofs.Partition.BadCubes
import Rigidity.Percolation.TriadicWellConnectedEdgeSigma

/-!
# Locality of the good cubes

The good cubes satisfy the locality hypothesis (2.1) of Armstrong and Dario, Proposition 2.1:
whether a triadic cube is good is determined by the open edges inside its threefold enlargement.
For scales below three no cube is good; for larger scales goodness is goodness for the
well-connected family of the rounded three-quarter cubes, whose test cubes lie in the enlargement.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory

variable {d : ℕ}

/-- **Locality of goodness** (Armstrong and Dario, (2.1)). -/
theorem TriadicCube.measurableSet_not_mem_goodCubes_localEdge (T : TriadicCube d) :
    MeasurableSet[localEdgeSigma T.centeredTriple]
      {ω : Configuration d | T ∉ TriadicCube.goodCubes ω} := by
  by_cases h3 : 3 ≤ T.scale
  · have heq : {ω : Configuration d | T ∉ TriadicCube.goodCubes ω} =
        {ω | T ∈ goodOfWellConnected
          (wellConnectedFamily (fun R => ↑R.threeQuarterCube.vertices) ω)}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
        TriadicCube.mem_goodCubes_iff_of_three_le h3 ω]
    rw [heq]
    exact (T.measurableSet_goodOfWellConnected_localEdge _
      (fun R => R.threeQuarterCube_subset_envelope.trans R.threeQuarterEnvelope_subset)).compl
  · have heq : {ω : Configuration d | T ∉ TriadicCube.goodCubes ω} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro hT
      exact h3 (TriadicCube.three_le_scale_of_mem_goodCubes hT)
    rw [heq]
    exact MeasurableSet.univ

end Rigidity.Percolation

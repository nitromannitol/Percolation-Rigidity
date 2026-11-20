import Rigidity.Percolation.PadSeedTargetLocality

/-!
# Exterior locality of pad-seed targets

When the explored region avoids the target face, the pad-seed targets use
only bonds internal to the exterior part of the cube and the outward pad.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- If the explored set avoids the face, pad-seed targets use only bonds
inside the exterior part of the cube and the outward pad. -/
theorem measurable_padSeedTargets_exterior {d : ℕ} (M n : ℕ) (i : Fin d)
    (R : Finset (Vertex d))
    (hface : ∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) :
    @Measurable _ _ (bondSigma (localBonds
      ((centeredBondCube n \ (R : Set (Vertex d))) ∪ orthantFaceSeedPad n (2 * M + 1) i))) _
      (padSeedTargets M n i) := by
  classical
  let T : Set (Vertex d) := (centeredBondCube n \ (R : Set (Vertex d))) ∪
    orthantFaceSeedPad n (2 * M + 1) i
  letI : MeasurableSpace (Configuration d) := bondSigma (localBonds T)
  apply measurable_finset_iff.mpr
  intro x
  by_cases hx : x ∈ centeredCubeOrthantFace n i (fun _ => true)
  · have hxT : x ∈ T := Or.inl ⟨((mem_centeredBondCubeBoundary n x).mp
      ((mem_centeredCubeOrthantFace n i _ x).mp hx).1).1, hface x hx⟩
    let step : Vertex d := fun j => if j = i then x j + 1 else x j
    let S : Vertex d → Set (Vertex d) := fun c => (fun z : Vertex d => z + c) '' centeredBondCube M
    have heq : {ω : Configuration d | x ∈ padSeedTargets M n i ω} =
        ⋃ c, ⋃ (_ : S c ⊆ orthantFaceSeedPad n (2 * M + 1) i),
          ⋃ (_ : step ∈ S c), fullyOpenRegion (S c) ∩ {ω | (openGraph ω).Adj x step} := by
      ext ω
      simp only [padSeedTargets, Finset.mem_filter, hx, true_and, Set.mem_setOf_eq,
        Set.mem_iUnion, Set.mem_inter_iff, S, step]
      constructor
      · rintro ⟨c, hpad, hopen, hstep, hedge⟩
        exact ⟨c, hpad, hstep, hopen, hedge⟩
      · rintro ⟨c, hpad, hstep, hopen, hedge⟩
        exact ⟨c, hpad, hopen, hstep, hedge⟩
    apply measurableSet_setOf.mp
    rw [heq]
    refine MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun hpad =>
      MeasurableSet.iUnion fun hstep => ?_
    have hS : localBonds (S c) ⊆ localBonds T := by
      intro e he z hz
      exact Or.inr (hpad (he z hz))
    have hstepT : step ∈ T := Or.inr (hpad hstep)
    exact (bondSigma_mono hS _ (measurableSet_fullyOpenRegion_localBond (S c))).inter
      (measurableSet_openGraph_adj_bondSigma T hxT hstepT)
  · have heq : {ω : Configuration d | x ∈ padSeedTargets M n i ω} = ∅ := by
      ext ω
      simp only [padSeedTargets, Finset.mem_filter, hx, false_and, Set.mem_setOf_eq,
        Set.mem_empty_iff_false]
    exact measurableSet_setOf.mp (heq ▸ MeasurableSet.empty)

end Rigidity.Percolation

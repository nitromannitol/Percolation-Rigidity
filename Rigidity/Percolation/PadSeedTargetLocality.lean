import Rigidity.Percolation.ConditionalFaceSeedSource

/-!
# Locality of outward-pad seed targets

The outward-pad seed targets are determined by bonds inside the union of the
ambient cube and the outward pad.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- Open adjacency between two vertices of a region depends on its internal bonds. -/
theorem measurableSet_openGraph_adj_bondSigma {d : ℕ} (S : Set (Vertex d))
    {x y : Vertex d} (hx : x ∈ S) (hy : y ∈ S) :
    MeasurableSet[bondSigma (localBonds S)] {ω : Configuration d | (openGraph ω).Adj x y} := by
  by_cases hxy : (nearestNeighborGraph d).Adj x y
  · have he : bondOfAdjacent hxy ∈ localBonds S := by
      intro z hz
      change z ∈ s(x, y) at hz
      rcases Sym2.mem_iff.mp hz with hz | hz
      · rwa [hz]
      · rwa [hz]
    have hcoord : @Measurable _ _ (bondSigma (localBonds S)) _
        (fun ω : Configuration d => ω (bondOfAdjacent hxy)) :=
      measurable_iff_comap_le.mpr (le_iSup_of_le _ (le_iSup_of_le he le_rfl))
    have heq : {ω : Configuration d | (openGraph ω).Adj x y} =
        (fun ω : Configuration d => ω (bondOfAdjacent hxy)) ⁻¹' {true} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, openGraph_adj_iff]
      exact ⟨fun ⟨_, hopen⟩ => hopen, fun hopen => ⟨hxy, hopen⟩⟩
    rw [heq]
    exact hcoord (measurableSet_singleton true)
  · have heq : {ω : Configuration d | (openGraph ω).Adj x y} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, openGraph_adj_iff]
      rintro ⟨h, _⟩
      exact hxy h
    rw [heq]
    exact @MeasurableSet.empty _ (bondSigma (localBonds S))

/-- Pad-seed targets depend only on bonds internal to the cube and pad union. -/
theorem measurable_padSeedTargets_local {d : ℕ} (M n : ℕ) (i : Fin d) :
    @Measurable _ _ (bondSigma (localBonds
      (centeredBondCube n ∪ orthantFaceSeedPad n (2 * M + 1) i))) _
      (padSeedTargets M n i) := by
  classical
  let T : Set (Vertex d) := centeredBondCube n ∪ orthantFaceSeedPad n (2 * M + 1) i
  letI : MeasurableSpace (Configuration d) := bondSigma (localBonds T)
  apply measurable_finset_iff.mpr
  intro x
  by_cases hx : x ∈ centeredCubeOrthantFace n i (fun _ => true)
  · have hxT : x ∈ T := Or.inl (((mem_centeredBondCubeBoundary n x).mp
      ((mem_centeredCubeOrthantFace n i _ x).mp hx).1).1)
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

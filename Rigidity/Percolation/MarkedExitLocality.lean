import Rigidity.Percolation.MarkedExitSymmetry
import Rigidity.Percolation.ConditionalFaceSeedInside

/-!
# Locality of marked exterior exits

A marked exit depends only on its cut marks, exterior path bonds, and the
bonds determining its finite target set.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- A marked exterior exit is measurable in any mark sigma algebra containing
the internal cut, the exterior bonds, and the target's bond support. -/
theorem measurableSet_markedRegionExit_local {d : ℕ} (p : unitInterval)
    (R : Finset (Vertex d)) (D : Set (Vertex d)) (hD : D.Finite)
    (hRD : (R : Set (Vertex d)) ⊆ D) (S : Set (Bond d))
    (hcut : (↑(vertexCutBondsIn R D) : Set (Bond d)) ⊆ S)
    (hext : localBonds (D \ (R : Set (Vertex d))) ⊆ S)
    (K : Configuration d → Finset (Vertex d))
    (hK : @Measurable _ _ (bondSigma S) _ K) (β : Bond d → unitInterval) (δ : ℝ) :
    MeasurableSet[bondMarkSigma S] (markedRegionExit p R D K β δ) := by
  classical
  letI : MeasurableSpace (BondMarks d) := bondMarkSigma S
  have hp : @Measurable _ _ (bondMarkSigma S) (bondSigma S) (thresholdBondMarks p) :=
    measurable_thresholdBondMarks_bondSigma p S
  have htargets : Measurable (fun ω : BondMarks d => K (thresholdBondMarks p ω)) := hK.comp hp
  have heq : markedRegionExit p R D K β δ = ⋃ x ∈ R, ⋃ y ∈ D \ (R : Set (Vertex d)),
      ⋃ hxy : (nearestNeighborGraph d).Adj x y,
      {ω | (ω (bondOfAdjacent hxy) : ℝ) ≤ (β (bondOfAdjacent hxy) : ℝ) + δ} ∩
      ⋃ z ∈ D \ (R : Set (Vertex d)), {ω | z ∈ K (thresholdBondMarks p ω)} ∩
        {ω | (openIn (thresholdBondMarks p ω) (D \ (R : Set (Vertex d)))).Reachable y z} := by
    ext ω
    simp only [markedRegionExit, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, y, hy, hxy, hopen, z, hz, hzout, hpath⟩
      exact ⟨x, hx, y, hy, hxy, hopen, z, hzout, hz, hpath⟩
    · rintro ⟨x, hx, y, hy, hxy, hopen, z, hzout, hz, hpath⟩
      exact ⟨x, hx, y, hy, hxy, hopen, z, hz, hzout, hpath⟩
  rw [heq]
  refine MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy =>
      MeasurableSet.iUnion fun hxy => ?_
  apply MeasurableSet.inter
  · have he : bondOfAdjacent hxy ∈ S :=
      hcut (bondOfAdjacent_mem_vertexCutBondsIn R D hRD hx hy hxy)
    have hc : Measurable (fun ω : BondMarks d => ω (bondOfAdjacent hxy)) :=
      measurable_iff_comap_le.mpr (le_iSup_of_le _ (le_iSup_of_le he le_rfl))
    have hc' : Measurable (fun ω : BondMarks d => (ω (bondOfAdjacent hxy) : ℝ)) :=
      measurable_subtype_coe.comp hc
    exact measurableSet_Iic.preimage hc'
  · refine MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun hz => ?_
    have hreach : MeasurableSet[bondSigma S]
        {ω : Configuration d | (openIn ω (D \ (R : Set (Vertex d)))).Reachable y z} :=
      bondSigma_mono hext _ (measurableSet_reachable_openIn_bondSigma _
        (hD.subset Set.sdiff_subset) hy hz)
    exact (measurableSet_setOf.mpr ((measurable_finset_iff.mp htargets) z)).inter (hp hreach)

end Rigidity.Percolation

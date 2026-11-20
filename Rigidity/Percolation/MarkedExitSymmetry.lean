import Rigidity.Percolation.SeedTargetSymmetry

/-!
# Symmetries of marked exterior exits

A lattice symmetry transports a marked boundary exit and its open exterior
path to the corresponding transformed explored region and target family.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- A raised-threshold boundary bond leads to a `p`-open exterior path to
one of the given random targets. -/
def markedRegionExit {d : ℕ} (p : unitInterval) (R : Finset (Vertex d))
    (D : Set (Vertex d)) (K : Configuration d → Finset (Vertex d))
    (β : Bond d → unitInterval) (δ : ℝ) : Set (BondMarks d) :=
  {ω | ∃ x ∈ R, ∃ y ∈ D \ (R : Set (Vertex d)),
    ∃ hxy : (nearestNeighborGraph d).Adj x y,
      (ω (bondOfAdjacent hxy) : ℝ) ≤ (β (bondOfAdjacent hxy) : ℝ) + δ ∧
      ∃ z ∈ K (thresholdBondMarks p ω), z ∈ D \ (R : Set (Vertex d)) ∧
        (openIn (thresholdBondMarks p ω) (D \ (R : Set (Vertex d)))).Reachable y z}

/-- A marked exterior exit to a measurable finite target family is measurable. -/
theorem measurableSet_markedRegionExit {d : ℕ} (p : unitInterval) (R : Finset (Vertex d))
    (D : Set (Vertex d)) (K : Configuration d → Finset (Vertex d)) (hK : Measurable K)
    (β : Bond d → unitInterval) (δ : ℝ) : MeasurableSet (markedRegionExit p R D K β δ) := by
  have hp : Measurable (thresholdBondMarks (d := d) p) := by
    apply measurable_pi_lambda
    intro e
    exact (measurable_markThreshold p).comp (measurable_pi_apply e)
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
  refine MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun hxy => ?_
  apply MeasurableSet.inter
  · have hc : Measurable (fun ω : BondMarks d => ω (bondOfAdjacent hxy)) := measurable_pi_apply _
    have hc' : Measurable (fun ω : BondMarks d => (ω (bondOfAdjacent hxy) : ℝ)) :=
      measurable_subtype_coe.comp hc
    exact measurableSet_Iic.preimage hc'
  · refine MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _ => ?_
    exact (measurableSet_setOf.mpr ((measurable_finset_iff.mp htargets) z)).inter
      ((measurableSet_openIn_reachable _ y z).preimage hp)

/-- Moving all geometric data and thresholds by a lattice symmetry carries
marked exterior exits to marked exterior exits. -/
theorem latticeBondMarkEquiv_mem_markedRegionExit {d : ℕ} (p : unitInterval)
    (f : Vertex d ≃ Vertex d) (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (R : Finset (Vertex d)) (D : Set (Vertex d)) (K : Configuration d → Finset (Vertex d))
    (β : Bond d → unitInterval) (δ : ℝ) (ω : BondMarks d)
    (hω : ω ∈ markedRegionExit p R D K β δ) :
    latticeBondMarkEquiv f hf ω ∈ markedRegionExit p (R.image f) (f '' D)
      (fun η => (K ((latticeConfigurationEquiv f hf).symm η)).image f)
      (fun e => β ((latticeBondEquiv f hf).symm e)) δ := by
  classical
  obtain ⟨x, hx, y, hy, hxy, hopen, z, hz, hzout, hpath⟩ := hω
  have hregion : f '' (D \ (R : Set (Vertex d))) =
      (f '' D) \ (↑(R.image f) : Set (Vertex d)) := by
    rw [Finset.coe_image, Set.image_sdiff f.injective]
  have hy' : f y ∈ (f '' D) \ (↑(R.image f) : Set (Vertex d)) := by
    rw [← hregion]
    exact ⟨y, hy, rfl⟩
  have hz' : f z ∈ (f '' D) \ (↑(R.image f) : Set (Vertex d)) := by
    rw [← hregion]
    exact ⟨z, hzout, rfl⟩
  have hxy' : (nearestNeighborGraph d).Adj (f x) (f y) :=
    (nearestNeighborGraph_adj_latticeEquiv_iff f hf x y).mpr hxy
  have hbond := latticeBondEquiv_bondOfAdjacent f hf hxy
  have hmark : (latticeBondMarkEquiv f hf ω (bondOfAdjacent hxy') : ℝ) ≤
      (β ((latticeBondEquiv f hf).symm (bondOfAdjacent hxy')) : ℝ) + δ := by
    rw [← hbond, latticeBondMarkEquiv_apply_bond, Equiv.symm_apply_apply]
    exact hopen
  have hpath' := (openInLatticeEquiv f hf (thresholdBondMarks p ω)
    (D \ (R : Set (Vertex d)))).reachable_iff.mpr hpath
  change (openIn (latticeConfigurationEquiv f hf (thresholdBondMarks p ω))
    (f '' (D \ (R : Set (Vertex d))))).Reachable (f y) (f z) at hpath'
  rw [hregion, ← thresholdBondMarks_latticeBondMarkEquiv] at hpath'
  refine ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, f y, hy', hxy', hmark, f z, ?_, hz', hpath'⟩
  rw [thresholdBondMarks_latticeBondMarkEquiv]
  change f z ∈ (K ((latticeConfigurationEquiv f hf).symm
    (latticeConfigurationEquiv f hf (thresholdBondMarks p ω)))).image f
  rw [MeasurableEquiv.symm_apply_apply]
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

/-- A conditional marked-exit probability does not decrease when all data
are carried by a lattice symmetry. -/
theorem conditional_markedRegionExit_le_latticeEquiv {d : ℕ} (p : unitInterval)
    (f : Vertex d ≃ Vertex d) (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (R : Finset (Vertex d)) (D : Set (Vertex d)) (K : Configuration d → Finset (Vertex d))
    (F : Finset (Bond d)) (β : Bond d → unitInterval) (δ : ℝ)
    (hHpos : 0 < (bondMarkLaw d).real (bondMarksAbove F β))
    (hG : MeasurableSet (markedRegionExit p (R.image f) (f '' D)
      (fun η => (K ((latticeConfigurationEquiv f hf).symm η)).image f)
      (fun e => β ((latticeBondEquiv f hf).symm e)) δ)) :
    (bondMarkLaw d).real (bondMarksAbove F β ∩ markedRegionExit p R D K β δ) /
        (bondMarkLaw d).real (bondMarksAbove F β) ≤
    (bondMarkLaw d).real
      (bondMarksAbove (F.image (latticeBondEquiv f hf))
        (fun e => β ((latticeBondEquiv f hf).symm e)) ∩
      markedRegionExit p (R.image f) (f '' D)
        (fun η => (K ((latticeConfigurationEquiv f hf).symm η)).image f)
        (fun e => β ((latticeBondEquiv f hf).symm e)) δ) /
    (bondMarkLaw d).real (bondMarksAbove (F.image (latticeBondEquiv f hf))
      (fun e => β ((latticeBondEquiv f hf).symm e))) := by
  haveI : IsProbabilityMeasure (bondMarkLaw d) := by
    dsimp only [bondMarkLaw]
    infer_instance
  let g := latticeBondMarkEquiv f hf
  let H := bondMarksAbove F β
  let H' := bondMarksAbove (F.image (latticeBondEquiv f hf))
    (fun e => β ((latticeBondEquiv f hf).symm e))
  let G := markedRegionExit p R D K β δ
  let G' := markedRegionExit p (R.image f) (f '' D)
    (fun η => (K ((latticeConfigurationEquiv f hf).symm η)).image f)
    (fun e => β ((latticeBondEquiv f hf).symm e)) δ
  have hHpre : g ⁻¹' H' = H := by
    ext ω
    exact bondMarksAbove_latticeEquiv_iff f hf F β ω
  have hmap := bondMarkLaw_map_latticeBondMarkEquiv f hf
  have hHmeas : MeasurableSet H' := measurableSet_bondMarksAbove _ _
  have hHprob : (bondMarkLaw d).real H = (bondMarkLaw d).real H' := by
    rw [← hHpre, measureReal_def, ← Measure.map_apply g.measurable hHmeas, hmap]
    rfl
  have hsubset : H ∩ G ⊆ g ⁻¹' (H' ∩ G') := by
    intro ω ⟨hωH, hωG⟩
    exact ⟨(bondMarksAbove_latticeEquiv_iff f hf F β ω).mpr hωH,
      latticeBondMarkEquiv_mem_markedRegionExit p f hf R D K β δ ω hωG⟩
  have hnum : (bondMarkLaw d).real (H ∩ G) ≤ (bondMarkLaw d).real (H' ∩ G') := by
    calc
      _ ≤ (bondMarkLaw d).real (g ⁻¹' (H' ∩ G')) := measureReal_mono hsubset (measure_ne_top _ _)
      _ = _ := by
        rw [measureReal_def, ← Measure.map_apply g.measurable (hHmeas.inter hG), hmap]
        rfl
  change (bondMarkLaw d).real (H ∩ G) / (bondMarkLaw d).real H ≤
    (bondMarkLaw d).real (H' ∩ G') / (bondMarkLaw d).real H'
  rw [hHprob] at hHpos ⊢
  exact div_le_div_of_nonneg_right hnum hHpos.le

end Rigidity.Percolation

import Rigidity.Percolation.ConditionalFaceSeedInside

/-!
# Conditional connections to seeds in an outward pad

An aligned open grid trial supplies the translated seed in the outward pad
used by the conditional seed-connection construction.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- Face vertices joined by an open bond to an open translate of the central
seed contained in the outward pad. -/
noncomputable def padSeedTargets {d : ℕ} (M n : ℕ) (i : Fin d)
    (ω : Configuration d) : Finset (Vertex d) := by
  classical
  exact (centeredCubeOrthantFace n i (fun _ => true)).filter fun x =>
    ∃ c : Vertex d, let S := (fun z : Vertex d => z + c) '' centeredBondCube M
      S ⊆ orthantFaceSeedPad n (2 * M + 1) i ∧ ω ∈ fullyOpenRegion S ∧
      (fun j => if j = i then x j + 1 else x j) ∈ S ∧
      (openGraph ω).Adj x (fun j => if j = i then x j + 1 else x j)

/-- The outward-pad seed targets form a measurable finite random set. -/
theorem measurable_padSeedTargets {d : ℕ} (M n : ℕ) (i : Fin d) :
    Measurable (padSeedTargets M n i) := by
  classical
  apply measurable_finset_iff.mpr
  intro x
  let S : Vertex d → Set (Vertex d) := fun c => (fun z : Vertex d => z + c) '' centeredBondCube M
  let step : Vertex d := fun j => if j = i then x j + 1 else x j
  have heq : {ω : Configuration d | x ∈ padSeedTargets M n i ω} =
      ⋃ (_ : x ∈ centeredCubeOrthantFace n i (fun _ => true)), ⋃ c,
        {ω | S c ⊆ orthantFaceSeedPad n (2 * M + 1) i} ∩
        fullyOpenRegion (S c) ∩ {ω | step ∈ S c} ∩ {ω | (openGraph ω).Adj x step} := by
    ext ω
    simp only [padSeedTargets, Finset.mem_filter, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, S, step]
    constructor
    · rintro ⟨hx, c, hpad, hopen, hstep, hedge⟩
      exact ⟨hx, c, ⟨⟨⟨hpad, hopen⟩, hstep⟩, hedge⟩⟩
    · rintro ⟨hx, c, ⟨⟨⟨hpad, hopen⟩, hstep⟩, hedge⟩⟩
      exact ⟨hx, c, hpad, hopen, hstep, hedge⟩
  apply measurableSet_setOf.mp
  rw [heq]
  refine MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun c => ?_
  exact (((MeasurableSet.const (S c ⊆ orthantFaceSeedPad n (2 * M + 1) i)).inter
    (bondSigma_le (localBonds (S c)) _ (measurableSet_fullyOpenRegion_localBond (S c)))).inter
      (MeasurableSet.const (step ∈ S c))).inter (measurableSet_openGraph_adj x step)

/-- The aligned grid-seed targets are contained in the outward-pad seed targets. -/
theorem faceSeedTargets_subset_padSeedTargets {d : ℕ} (M n : ℕ) (i : Fin d)
    (halign : (2 * M + 1) ∣ n + 1) (ω : Configuration d) :
    faceSeedTargets (centeredCubeOrthantFace n i (fun _ => true)) (2 * M + 1) i n ω ⊆
      padSeedTargets M n i ω := by
  classical
  intro x hx
  obtain ⟨hface, htrial⟩ := (mem_faceSeedTargets _ _ _ _ _ _).mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hface, ?_⟩
  let k := 2 * M + 1
  have hk : 0 < k := by dsimp [k]; omega
  have hdiv : (k : ℤ) ∣ (n : ℤ) + 1 := by exact_mod_cast halign
  have hxi : x i = (n : ℤ) := by
    have h := ((mem_centeredCubeOrthantFace n i (fun _ => true) x).mp hface).2.1
    simpa only [↓reduceIte] using h
  let c : Vertex d := fun j =>
    (if j = i then (n : ℤ) + 1 else (k : ℤ) * seedGridIndex k x j) + (M : ℤ)
  have hcell : faceSeedCell k i n (seedGridIndex k x) =
      (fun z : Vertex d => z + c) '' centeredBondCube M :=
    faceSeedCell_eq_centeredCube_translate M i n x
  let z : Vertex d := fun j => if j = i then x j + 1 else x j
  have hz : z ∈ faceSeedCell k i n (seedGridIndex k x) :=
    face_contact_step_mem_seed hk i n x hxi
  have hadj : (nearestNeighborGraph d).Adj x z := face_contact_step_adj i x
  have he : bondOfAdjacent hadj ∈ localBonds (faceSeedTrial k i n x) := by
    intro w hw
    change w ∈ s(x, z) at hw
    rcases Sym2.mem_iff.mp hw with hw | hw
    · rw [hw]
      exact Set.mem_insert x _
    · rw [hw]
      exact Set.mem_insert_of_mem _ hz
  have hopen : (openGraph ω).Adj x z := (openGraph_adj_iff ω x z).mpr ⟨hadj, htrial _ he⟩
  refine ⟨c, ?_, ?_, ?_, hopen⟩
  · rw [← hcell]
    exact faceSeedCell_subset_orthantFaceSeedPad hk n i x hface hdiv
  · rw [← hcell]
    exact fullyOpenRegion_faceSeed_of_trial i n x htrial
  · rw [← hcell]
    exact hz

/-- An exit bond opened at its raised threshold leads through the `p`-open
exterior to a face vertex in the outward-pad seed target. -/
def markedPadSeedExit {d : ℕ} (p : unitInterval) (M n : ℕ) (i : Fin d)
    (R : Finset (Vertex d)) (β : Bond d → unitInterval) (δ : ℝ) : Set (BondMarks d) :=
  {ω | ∃ x ∈ R, ∃ y ∈ centeredBondCube n \ (R : Set (Vertex d)),
    ∃ hxy : (nearestNeighborGraph d).Adj x y,
      (ω (bondOfAdjacent hxy) : ℝ) ≤ (β (bondOfAdjacent hxy) : ℝ) + δ ∧
      ∃ z ∈ padSeedTargets M n i (thresholdBondMarks p ω),
        z ∈ centeredBondCube n \ (R : Set (Vertex d)) ∧
        (openIn (thresholdBondMarks p ω) (centeredBondCube n \ (R : Set (Vertex d)))).Reachable y z}

/-- The marked exit event to an outward-pad seed is measurable. -/
theorem measurableSet_markedPadSeedExit {d : ℕ} (p : unitInterval) (M n : ℕ)
    (i : Fin d) (R : Finset (Vertex d)) (β : Bond d → unitInterval) (δ : ℝ) :
    MeasurableSet (markedPadSeedExit p M n i R β δ) := by
  have hp : Measurable (thresholdBondMarks (d := d) p) := by
    apply measurable_pi_lambda
    intro e
    exact (measurable_markThreshold p).comp (measurable_pi_apply e)
  have htargets : Measurable (fun ω : BondMarks d => padSeedTargets M n i (thresholdBondMarks p ω)) :=
    (measurable_padSeedTargets M n i).comp hp
  have heq : markedPadSeedExit p M n i R β δ = ⋃ x ∈ R, ⋃ y ∈ centeredBondCube n \ (R : Set (Vertex d)),
      ⋃ hxy : (nearestNeighborGraph d).Adj x y,
      {ω | (ω (bondOfAdjacent hxy) : ℝ) ≤ (β (bondOfAdjacent hxy) : ℝ) + δ} ∩
      ⋃ z ∈ centeredBondCube n \ (R : Set (Vertex d)),
        {ω | z ∈ padSeedTargets M n i (thresholdBondMarks p ω)} ∩
          {ω | (openIn (thresholdBondMarks p ω) (centeredBondCube n \ (R : Set (Vertex d)))).Reachable y z} := by
    ext ω
    simp only [markedPadSeedExit, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
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

/-- A marked exit to an aligned grid target is an exit to an outward-pad seed. -/
theorem markedFaceSeedExit_subset_markedPadSeedExit {d : ℕ} (p : unitInterval)
    (M n : ℕ) (i : Fin d) (R : Finset (Vertex d)) (β : Bond d → unitInterval) (δ : ℝ)
    (halign : (2 * M + 1) ∣ n + 1) :
    markedFaceSeedExit p M n i R β δ ⊆ markedPadSeedExit p M n i R β δ := by
  rintro ω ⟨x, hx, y, hy, hxy, hopen, z, hz, hzout, hpath⟩
  exact ⟨x, hx, y, hy, hxy, hopen, z,
    faceSeedTargets_subset_padSeedTargets M n i halign (thresholdBondMarks p ω) hz, hzout, hpath⟩

/-- Above criticality and below one, the source seed-and-pad event has
conditional probability above `1 - ε`, uniformly over explored sets and
admissible prior boundary thresholds. -/
theorem exists_conditional_markedPadSeedExit {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      ∀ R : Finset (Vertex d), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        ∀ β : Bond d → unitInterval,
          (∀ e ∈ vertexCutBondsIn R (centeredBondCube n), (β e : ℝ) + δ ≤ 1) →
          0 < (bondMarkLaw d).real (bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β) ∧
          1 - ε < (bondMarkLaw d).real
              (bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β ∩
                markedPadSeedExit p M n i R β δ) /
            (bondMarkLaw d).real (bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β) := by
  haveI : IsProbabilityMeasure (bondMarkLaw d) := by
    dsimp only [bondMarkLaw]
    infer_instance
  obtain ⟨M, n, hM, hn, halign, hsuccess⟩ :=
    exists_conditional_markedFaceSeedExit_internal p hp hp1 i ε δ hε hδ hδ1
  refine ⟨M, n, hM, hn, ?_⟩
  intro R hseed hR hface β hβ
  have hpos := bondMarkLaw_real_bondMarksAbove_pos (vertexCutBondsIn R (centeredBondCube n))
    β δ hδ hβ
  refine ⟨hpos, ?_⟩
  apply (hsuccess R hseed hR hface β hβ).trans_le
  apply div_le_div_of_nonneg_right _ hpos.le
  exact measureReal_mono (Set.inter_subset_inter_right _
    (markedFaceSeedExit_subset_markedPadSeedExit p M n i R β δ halign)) (measure_ne_top _ _)

end Rigidity.Percolation

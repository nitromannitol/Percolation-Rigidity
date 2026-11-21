import Rigidity.Percolation.ConditionalSeedLocalHistory
import Rigidity.Percolation.PadSeedTargetExterior

/-!
# Conditional seed connections with explored interior histories

The marked exit and its boundary conditions do not use bonds internal to the
explored region. Previously revealed information on those bonds can therefore
be included in the conditioning event.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- The bonds needed by an exterior seed exit and its internal boundary cut. -/
def seedExitExteriorSupport {d : ℕ} (M n : ℕ) (i : Fin d)
    (R : Finset (Vertex d)) : Set (Bond d) :=
  localBonds ((centeredBondCube n \ (R : Set (Vertex d))) ∪
    orthantFaceSeedPad n (2 * M + 1) i) ∪ (↑(vertexCutBondsIn R (centeredBondCube n)) : Set (Bond d))

/-- The seed-exit support is disjoint from bonds internal to the explored set. -/
theorem disjoint_localBonds_seedExitExteriorSupport {d : ℕ} (M n : ℕ) (i : Fin d)
    (R : Finset (Vertex d)) (hR : (R : Set (Vertex d)) ⊆ centeredBondCube n) :
    Disjoint (localBonds (R : Set (Vertex d))) (seedExitExteriorSupport M n i R) := by
  classical
  unfold seedExitExteriorSupport
  rw [Set.disjoint_union_right]
  constructor
  · apply disjoint_localBonds
    rw [Set.disjoint_left]
    intro x hxR hxT
    rcases hxT with hxout | hxpad
    · exact hxout.2 hxR
    · have hxi := (mem_centeredBondCube n x).mp (hR hxR) i
      have hhi := (abs_le.mp hxi).2
      have hlow := hxpad.1
      omega
  · rw [Set.disjoint_left]
    intro e heR hecut
    have hefull := (Finset.mem_filter.mp hecut).1
    obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp hefull
    exact Set.disjoint_left.mp
      (disjoint_regionOutgoingBonds_localBonds (R : Set (Vertex d)) hx) he heR

/-- The source seed exit depends only on exterior bonds and the boundary cut. -/
theorem measurableSet_markedPadSeedExit_exterior {d : ℕ} (p : unitInterval)
    (M n : ℕ) (i : Fin d) (R : Finset (Vertex d))
    (hR : (R : Set (Vertex d)) ⊆ centeredBondCube n)
    (hface : ∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R)
    (β : Bond d → unitInterval) (δ : ℝ) :
    MeasurableSet[bondMarkSigma (seedExitExteriorSupport M n i R)]
      (markedPadSeedExit p M n i R β δ) := by
  let S := seedExitExteriorSupport M n i R
  have hcut : (↑(vertexCutBondsIn R (centeredBondCube n)) : Set (Bond d)) ⊆ S := Set.subset_union_right
  have hext : localBonds (centeredBondCube n \ (R : Set (Vertex d))) ⊆ S := by
    intro e he
    apply Or.inl
    intro x hx
    exact Or.inl (he x hx)
  have hK : @Measurable _ _ (bondSigma S) _ (padSeedTargets M n i) :=
    (measurable_padSeedTargets_exterior M n i R hface).mono
      (bondSigma_mono (show localBonds ((centeredBondCube n \ (R : Set (Vertex d))) ∪
        orthantFaceSeedPad n (2 * M + 1) i) ⊆ S from Set.subset_union_left)) le_rfl
  change MeasurableSet[bondMarkSigma S]
    (markedRegionExit p R (centeredBondCube n) (padSeedTargets M n i) β δ)
  exact measurableSet_markedRegionExit_local p R _ (finite_centeredBondCube n) hR S hcut hext
    (padSeedTargets M n i) hK β δ

/-- Boundary threshold constraints are measurable in the exterior exit support. -/
theorem measurableSet_internalCutMarksAbove_exterior {d : ℕ} (M n : ℕ) (i : Fin d)
    (R : Finset (Vertex d)) (β : Bond d → unitInterval) :
    MeasurableSet[bondMarkSigma (seedExitExteriorSupport M n i R)]
      (bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β) := by
  apply bondMarkSigma_mono Set.subset_union_right _ (measurableSet_bondMarksAbove_local _ β)

/-- The conditional seed connection estimate remains valid after conditioning
on any positive-probability history supported on the explored region's
internal bonds. -/
theorem exists_conditional_padSeedExit_with_interior_history {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      ∀ R : Finset (Vertex d), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        ∀ β : Bond d → unitInterval,
          (∀ e ∈ vertexCutBondsIn R (centeredBondCube n), (β e : ℝ) + δ ≤ 1) →
          ∀ A : Set (BondMarks d), MeasurableSet[bondMarkSigma (localBonds (R : Set (Vertex d)))] A →
            0 < (bondMarkLaw d).real A →
          let H := bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β
          let G := markedPadSeedExit p M n i R β δ
          0 < (bondMarkLaw d).real (A ∩ H) ∧
          1 - ε < (bondMarkLaw d).real ((A ∩ H) ∩ G) /
            (bondMarkLaw d).real (A ∩ H) := by
  obtain ⟨M, n, hM, hn, hbase⟩ :=
    exists_conditional_markedPadSeedExit_of_pos p hp hp1 i ε δ hε hδ
  refine ⟨M, n, hM, hn, ?_⟩
  intro R hseed hR hface β hβ A hA hApos
  let H := bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β
  let G := markedPadSeedExit p M n i R β δ
  have hsource := hbase R hseed hR hface β hβ
  have heq := bondMarkLaw_real_conditional_inter_of_disjoint (localBonds (R : Set (Vertex d)))
    (seedExitExteriorSupport M n i R) (disjoint_localBonds_seedExitExteriorSupport M n i R hR) A H G hA
    (measurableSet_internalCutMarksAbove_exterior M n i R β)
    (measurableSet_markedPadSeedExit_exterior p M n i R hR hface β δ) hApos hsource.1
  exact ⟨heq.1, heq.2 ▸ hsource.2⟩

/-- The conditional seed estimate also survives any positive-probability
history on a bond set disjoint from the exterior exit support. -/
theorem exists_conditional_padSeedExit_with_exterior_disjoint_history {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      ∀ R : Finset (Vertex d), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        ∀ β : Bond d → unitInterval,
          (∀ e ∈ vertexCutBondsIn R (centeredBondCube n), (β e : ℝ) + δ ≤ 1) →
          ∀ (E : Set (Bond d)), Disjoint E (seedExitExteriorSupport M n i R) →
          ∀ A : Set (BondMarks d), MeasurableSet[bondMarkSigma E] A →
            0 < (bondMarkLaw d).real A →
          let H := bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β
          let G := markedPadSeedExit p M n i R β δ
          0 < (bondMarkLaw d).real (A ∩ H) ∧
          1 - ε < (bondMarkLaw d).real ((A ∩ H) ∩ G) /
            (bondMarkLaw d).real (A ∩ H) := by
  obtain ⟨M, n, hM, hn, hbase⟩ :=
    exists_conditional_markedPadSeedExit_of_pos p hp hp1 i ε δ hε hδ
  refine ⟨M, n, hM, hn, ?_⟩
  intro R hseed hR hface β hβ E hdisj A hA hApos
  let H := bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β
  let G := markedPadSeedExit p M n i R β δ
  have hsource := hbase R hseed hR hface β hβ
  have heq := bondMarkLaw_real_conditional_inter_of_disjoint E
    (seedExitExteriorSupport M n i R) hdisj A H G hA
    (measurableSet_internalCutMarksAbove_exterior M n i R β)
    (measurableSet_markedPadSeedExit_exterior p M n i R hR hface β δ) hApos hsource.1
  exact ⟨heq.1, heq.2 ▸ hsource.2⟩

end Rigidity.Percolation

import Rigidity.Percolation.PadSeedTargetLocality
import Rigidity.Percolation.MarkedExitLocality
import Rigidity.Percolation.ExternalMarkConditioning
import Rigidity.Percolation.ConditionalSeedIncrement

/-!
# Conditional seed connections with disjoint histories

A seed-and-pad event depends only on marks internal to the cube and pad
union. Conditioning on an additional positive-probability history on disjoint
bonds leaves the seed-connection probability unchanged.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- The marked seed-and-pad event is determined by marks on bonds internal
to the union of the ambient cube and the outward pad. -/
theorem measurableSet_markedPadSeedExit_local {d : ℕ} (p : unitInterval)
    (M n : ℕ) (i : Fin d) (R : Finset (Vertex d))
    (hR : (R : Set (Vertex d)) ⊆ centeredBondCube n)
    (β : Bond d → unitInterval) (δ : ℝ) :
    MeasurableSet[bondMarkSigma (localBonds
      (centeredBondCube n ∪ orthantFaceSeedPad n (2 * M + 1) i))]
      (markedPadSeedExit p M n i R β δ) := by
  classical
  let T := centeredBondCube n ∪ orthantFaceSeedPad n (2 * M + 1) i
  have hcut : (↑(vertexCutBondsIn R (centeredBondCube n)) : Set (Bond d)) ⊆ localBonds T := by
    intro e he x hx
    have heD := (Finset.mem_filter.mp he).2
    exact Or.inl (heD x hx)
  have hext : localBonds (centeredBondCube n \ (R : Set (Vertex d))) ⊆ localBonds T := by
    intro e he x hx
    exact Or.inl (he x hx).1
  change MeasurableSet[bondMarkSigma (localBonds T)]
    (markedRegionExit p R (centeredBondCube n) (padSeedTargets M n i) β δ)
  exact measurableSet_markedRegionExit_local p R _ (finite_centeredBondCube n) hR _ hcut hext
    (padSeedTargets M n i) (measurable_padSeedTargets_local M n i) β δ

/-- The internal-cut threshold event is determined by cube-and-pad bonds. -/
theorem measurableSet_internalCutMarksAbove_local {d : ℕ} (M n : ℕ) (i : Fin d)
    (R : Finset (Vertex d)) (β : Bond d → unitInterval) :
    MeasurableSet[bondMarkSigma (localBonds
      (centeredBondCube n ∪ orthantFaceSeedPad n (2 * M + 1) i))]
      (bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β) := by
  classical
  apply bondMarkSigma_mono _ _ (measurableSet_bondMarksAbove_local _ β)
  intro e he x hx
  have heD := (Finset.mem_filter.mp he).2
  exact Or.inl (heD x hx)

/-- Conditional seed connections retain their lower probability bound after
adding any positive-probability history supported on bonds disjoint from the
cube and pad union. -/
theorem exists_conditional_padSeedExit_with_disjoint_history {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      ∀ R : Finset (Vertex d), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        ∀ β : Bond d → unitInterval,
          (∀ e ∈ vertexCutBondsIn R (centeredBondCube n), (β e : ℝ) + δ ≤ 1) →
          ∀ (E : Set (Bond d)), Disjoint E (localBonds
            (centeredBondCube n ∪ orthantFaceSeedPad n (2 * M + 1) i)) →
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
    (localBonds (centeredBondCube n ∪ orthantFaceSeedPad n (2 * M + 1) i)) hdisj A H G hA
    (measurableSet_internalCutMarksAbove_local M n i R β)
    (measurableSet_markedPadSeedExit_local p M n i R hR β δ) hApos hsource.1
  exact ⟨heq.1, heq.2 ▸ hsource.2⟩

end Rigidity.Percolation

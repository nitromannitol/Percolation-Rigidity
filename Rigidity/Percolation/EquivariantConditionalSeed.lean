import Rigidity.Percolation.MarkedExitSymmetry
import Rigidity.Percolation.ConditionalFaceSeedSource

/-!
# Conditional seed connections in symmetric blocks

The conditional seed-and-pad estimate applies uniformly after any
lattice-distance-preserving change of coordinates.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- A random target family transported by a lattice symmetry. -/
noncomputable def latticeTransportTargets {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (K : Configuration d → Finset (Vertex d)) (η : Configuration d) : Finset (Vertex d) :=
  (K ((latticeConfigurationEquiv f hf).symm η)).image f

/-- Transporting a measurable finite target family preserves measurability. -/
theorem measurable_latticeTransportTargets {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (K : Configuration d → Finset (Vertex d)) (hK : Measurable K) :
    Measurable (latticeTransportTargets f hf K) := by
  classical
  exact (measurable_of_countable fun s : Finset (Vertex d) => s.image f).comp
    (hK.comp (latticeConfigurationEquiv f hf).symm.measurable)

/-- The conditional seed-and-pad estimate holds uniformly under all lattice
symmetries, with the same seed and cube radii. -/
theorem exists_equivariant_conditional_padSeedExit {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      ∀ (f : Vertex d ≃ Vertex d)
        (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
        (R : Finset (Vertex d)), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        ∀ β : Bond d → unitInterval,
          (∀ e ∈ vertexCutBondsIn R (centeredBondCube n), (β e : ℝ) + δ ≤ 1) →
          let F := (vertexCutBondsIn R (centeredBondCube n)).image (latticeBondEquiv f hf)
          let β' := fun e => β ((latticeBondEquiv f hf).symm e)
          let K := latticeTransportTargets f hf (padSeedTargets M n i)
          0 < (bondMarkLaw d).real (bondMarksAbove F β') ∧
          1 - ε < (bondMarkLaw d).real (bondMarksAbove F β' ∩
              markedRegionExit p (R.image f) (f '' centeredBondCube n) K β' δ) /
            (bondMarkLaw d).real (bondMarksAbove F β') := by
  classical
  obtain ⟨M, n, hM, hn, hbase⟩ :=
    exists_conditional_markedPadSeedExit p hp hp1 i ε δ hε hδ hδ1
  refine ⟨M, n, hM, hn, ?_⟩
  intro f hf R hseed hR hface β hβ
  let F := vertexCutBondsIn R (centeredBondCube n)
  let F' := F.image (latticeBondEquiv f hf)
  let β' := fun e => β ((latticeBondEquiv f hf).symm e)
  let K := latticeTransportTargets f hf (padSeedTargets M n i)
  have hsource := hbase R hseed hR hface β hβ
  have hβ' : ∀ e ∈ F', (β' e : ℝ) + δ ≤ 1 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    simpa only [β', Equiv.symm_apply_apply] using hβ a ha
  have hpos := bondMarkLaw_real_bondMarksAbove_pos F' β' δ hδ hβ'
  refine ⟨hpos, ?_⟩
  have hG : MeasurableSet (markedRegionExit p (R.image f) (f '' centeredBondCube n) K β' δ) :=
    measurableSet_markedRegionExit p (R.image f) (f '' centeredBondCube n) K
      (measurable_latticeTransportTargets f hf (padSeedTargets M n i) (measurable_padSeedTargets M n i)) β' δ
  have htrans := conditional_markedRegionExit_le_latticeEquiv p f hf R (centeredBondCube n)
    (padSeedTargets M n i) F β δ hsource.1 hG
  change (bondMarkLaw d).real (bondMarksAbove F β ∩ markedPadSeedExit p M n i R β δ) /
      (bondMarkLaw d).real (bondMarksAbove F β) ≤ _ at htrans
  exact hsource.2.trans_le htrans

end Rigidity.Percolation

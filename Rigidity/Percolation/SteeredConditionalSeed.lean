import Rigidity.Percolation.SteeredSeedSymmetry

/-!
# Conditional seed connections into steered blocks

The conditional seed-and-pad estimate applies to the reflection and
translation that steer the next pad inside a neighboring block.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- One pair of radii works for every steered seed center: the next seed pad
lies inside the neighboring block and the conditional probability of reaching
its seed target exceeds `1 - ε`. -/
theorem exists_steered_conditional_padSeedExit {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      ∀ b : Vertex d, (∀ j, |b j| ≤ ((M + n + 1 : ℕ) : ℤ)) → (M : ℤ) ≤ b i →
      ∀ R : Finset (Vertex d), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        ∀ β : Bond d → unitInterval,
          (∀ e ∈ vertexCutBondsIn R (centeredBondCube n), (β e : ℝ) + δ ≤ 1) →
          let f := steeringVertexEquiv i b
          let hf := latticeL1Dist_steeringVertexEquiv i b
          let F := (vertexCutBondsIn R (centeredBondCube n)).image (latticeBondEquiv f hf)
          let β' := fun e => β ((latticeBondEquiv f hf).symm e)
          let K := seedFamilyTargets ((centeredCubeOrthantFace n i (fun _ => true)).image f)
            (fun c : Vertex d => f '' ((fun z : Vertex d => z + c) '' centeredBondCube M))
            (f '' orthantFaceSeedPad n (2 * M + 1) i)
            (fun x => f (fun j => if j = i then (f.symm x) j + 1 else (f.symm x) j))
          (∀ x ∈ f '' orthantFaceSeedPad n (2 * M + 1) i, ∀ j,
            |x j - (if j = i then (2 * (M + n + 1 : ℕ) : ℤ) else 0)| ≤
              ((M + n + 1 : ℕ) : ℤ)) ∧
          0 < (bondMarkLaw d).real (bondMarksAbove F β') ∧
          1 - ε < (bondMarkLaw d).real (bondMarksAbove F β' ∩
              markedRegionExit p (R.image f) (f '' centeredBondCube n) K β' δ) /
            (bondMarkLaw d).real (bondMarksAbove F β') := by
  obtain ⟨M, n, hM, hn, hbase⟩ :=
    exists_equivariant_conditional_padSeedExit p hp hp1 i ε δ hε hδ hδ1
  refine ⟨M, n, hM, hn, ?_⟩
  intro b hb hbi R hseed hR hface β hβ
  let f := steeringVertexEquiv i b
  let hf := latticeL1Dist_steeringVertexEquiv i b
  refine ⟨steeringVertexEquiv_image_pad_subset_neighborBlock M n i b hb hbi, ?_⟩
  have h := hbase f hf R hseed hR hface β hβ
  have hK : latticeTransportTargets f hf (padSeedTargets M n i) =
      seedFamilyTargets ((centeredCubeOrthantFace n i (fun _ => true)).image f)
        (fun c : Vertex d => f '' ((fun z : Vertex d => z + c) '' centeredBondCube M))
        (f '' orthantFaceSeedPad n (2 * M + 1) i)
        (fun x => f (fun j => if j = i then (f.symm x) j + 1 else (f.symm x) j)) := by
    funext η
    exact latticeTransportTargets_padSeedTargets f hf M n i η
  rw [hK] at h
  exact h

end Rigidity.Percolation

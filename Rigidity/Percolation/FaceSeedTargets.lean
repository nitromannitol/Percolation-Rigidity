import Rigidity.Percolation.BoundaryCandidateCut
import Rigidity.Percolation.FaceSeedLemma

/-!
# Exterior measurability of face seed targets

Face vertices with fully open outward seed trials form a finite target set.
If the explored set lies inside the cube and avoids the face, this target set
is determined without revealing any bond in the explored set's boundary cut.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- Face contacts whose outward trial is fully open. -/
noncomputable def faceSeedTargets {d : ℕ} (face : Finset (Vertex d))
    (k : ℕ) (i : Fin d) (n : ℤ) (ω : Configuration d) : Finset (Vertex d) := by
  classical
  exact face.filter fun x => ω ∈ fullyOpenRegion (faceSeedTrial k i n x)

/-- Membership in the seed-target set records the open trial. -/
theorem mem_faceSeedTargets {d : ℕ} (face : Finset (Vertex d))
    (k : ℕ) (i : Fin d) (n : ℤ) (ω : Configuration d) (x : Vertex d) :
    x ∈ faceSeedTargets face k i n ω ↔
      x ∈ face ∧ ω ∈ fullyOpenRegion (faceSeedTrial k i n x) := by
  classical
  simp only [faceSeedTargets, Finset.mem_filter]

/-- A trial based on a face vertex outside an explored region inside the cube
is disjoint from that region. -/
theorem disjoint_faceSeedTrial_of_subset_cube {d : ℕ} (R : Finset (Vertex d))
    (n k : ℕ) (i : Fin d) (hR : (R : Set (Vertex d)) ⊆ centeredBondCube n)
    (x : Vertex d) (hx : x ∉ R) :
    Disjoint (faceSeedTrial k i n x) (R : Set (Vertex d)) := by
  rw [Set.disjoint_left]
  intro z hz hzR
  rcases Set.mem_insert_iff.mp hz with hzx | hz
  · exact hx (hzx ▸ hzR)
  · have hzi := (mem_centeredBondCube n z).mp (hR hzR) i
    have hhi := (abs_le.mp hzi).2
    have hstep := hz.1
    omega

/-- If a trial region is disjoint from the explored set, its internal bonds
are outside the explored set's boundary cut. -/
theorem localBonds_subset_vertexCutBonds_compl_of_disjoint {d : ℕ}
    (R : Finset (Vertex d)) (S : Set (Vertex d)) (hdisj : Disjoint S (R : Set (Vertex d))) :
    localBonds S ⊆ (↑(vertexCutBonds R) : Set (Bond d))ᶜ := by
  intro e he hcut
  obtain ⟨x, hx, hxe⟩ := exists_mem_of_mem_vertexCutBonds R hcut
  exact Set.disjoint_left.mp hdisj (he x hxe) hx

/-- The open-trial target set on a face avoiding the explored set is measurable
without inspecting any cut bond. -/
theorem measurable_faceSeedTargets_exterior {d : ℕ} (R : Finset (Vertex d))
    (n k : ℕ) (i : Fin d) (hR : (R : Set (Vertex d)) ⊆ centeredBondCube n)
    (face : Finset (Vertex d)) (hface : ∀ x ∈ face, x ∉ R) :
    @Measurable _ _ (bondSigma (↑(vertexCutBonds R) : Set (Bond d))ᶜ) _
      (faceSeedTargets face k i n) := by
  classical
  letI : MeasurableSpace (Configuration d) := bondSigma (↑(vertexCutBonds R) : Set (Bond d))ᶜ
  apply measurable_finset_iff.mpr
  intro x
  by_cases hx : x ∈ face
  · have hdisj := disjoint_faceSeedTrial_of_subset_cube R n k i hR x (hface x hx)
    have hmeas : MeasurableSet (fullyOpenRegion (faceSeedTrial k i n x)) :=
      bondSigma_mono (localBonds_subset_vertexCutBonds_compl_of_disjoint R _ hdisj) _
        (measurableSet_fullyOpenRegion_localBond (faceSeedTrial k i n x))
    apply measurableSet_setOf.mp
    simpa only [mem_faceSeedTargets, hx, true_and, Set.setOf_mem_eq] using hmeas
  · have heq : {ω : Configuration d | x ∈ faceSeedTargets face k i n ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, mem_faceSeedTargets, hx, false_and, Set.mem_empty_iff_false]
    exact measurableSet_setOf.mp (heq ▸ MeasurableSet.empty)

/-- Single-field seed-face success implies a connection from any explored
set containing the seed to the corresponding open-trial target set. -/
theorem singleFieldSeedFaceSuccess_subset_reachable_targets {d : ℕ}
    (M n : ℕ) (i : Fin d) (R : Finset (Vertex d))
    (hseed : centeredBondCubeFinset M ⊆ R)
    (hface : ∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) :
    singleFieldSeedFaceSuccess (centeredBondCube n) (centeredBondCubeFinset M)
      (centeredCubeOrthantFace n i (fun _ => true)) (2 * M + 1) i n ⊆
    {ω | ∃ x ∈ R, ∃ z ∈ faceSeedTargets
      (centeredCubeOrthantFace n i (fun _ => true)) (2 * M + 1) i n ω,
      z ∈ centeredBondCube n \ (R : Set (Vertex d)) ∧
        (openIn ω (centeredBondCube n)).Reachable x z} := by
  intro ω hω
  obtain ⟨y, hy, x, hx, hpath, htrial⟩ := hω
  refine ⟨y, hseed hy, x, (mem_faceSeedTargets _ _ _ _ _ _).mpr ⟨hx, htrial⟩, ?_, hpath⟩
  exact ⟨((mem_centeredBondCubeBoundary n x).mp
    ((mem_centeredCubeOrthantFace n i _ x).mp hx).1).1, hface x hx⟩

end Rigidity.Percolation

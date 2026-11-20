import Rigidity.Percolation.BoundaryCandidatesEnergy
import Rigidity.Percolation.SlabAttachmentGeometry

/-!
# Boundary bonds leading to exterior targets

A boundary bond is a candidate if its exterior endpoint connects to an
exterior target without using a boundary bond. The candidate family depends
only on the exterior field when the targets do.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- Candidate boundary bonds whose exterior endpoints reach a target through
the exterior of the explored region. -/
noncomputable def boundaryCandidateBonds {d : ℕ} (R D : Set (Vertex d))
    (F : Finset (Bond d)) (K : Configuration d → Finset (Vertex d))
    (ω : Configuration d) : Finset (Bond d) := by
  classical
  exact F.filter fun e => ∃ x ∈ R, ∃ y ∈ D \ R,
    ∃ hxy : (nearestNeighborGraph d).Adj x y, e = bondOfAdjacent hxy ∧
      ∃ z ∈ K ω, z ∈ D \ R ∧ (openIn ω (D \ R)).Reachable y z

/-- A candidate is a boundary bond with an exterior connection to a target. -/
theorem mem_boundaryCandidateBonds {d : ℕ} (R D : Set (Vertex d))
    (F : Finset (Bond d)) (K : Configuration d → Finset (Vertex d))
    (ω : Configuration d) (e : Bond d) :
    e ∈ boundaryCandidateBonds R D F K ω ↔ e ∈ F ∧
      ∃ x ∈ R, ∃ y ∈ D \ R, ∃ hxy : (nearestNeighborGraph d).Adj x y,
        e = bondOfAdjacent hxy ∧ ∃ z ∈ K ω, z ∈ D \ R ∧
          (openIn ω (D \ R)).Reachable y z := by
  classical
  simp only [boundaryCandidateBonds, Finset.mem_filter]

/-- Candidate bonds depend only on the exterior field when the targets do
and exterior internal bonds do not belong to the boundary set. -/
theorem measurable_boundaryCandidateBonds {d : ℕ} (R D : Set (Vertex d))
    (hD : D.Finite) (F : Finset (Bond d)) (K : Configuration d → Finset (Vertex d))
    (hK : @Measurable _ _ (bondSigma (↑F : Set (Bond d))ᶜ) _ K)
    (hlocal : localBonds (D \ R) ⊆ (↑F : Set (Bond d))ᶜ) :
    @Measurable _ _ (bondSigma (↑F : Set (Bond d))ᶜ) _
      (boundaryCandidateBonds R D F K) := by
  classical
  letI : MeasurableSpace (Configuration d) := bondSigma (↑F : Set (Bond d))ᶜ
  apply measurable_finset_iff.mpr
  intro e
  have hreach (y z : Vertex d) (hy : y ∈ D \ R) (hz : z ∈ D \ R) :
      MeasurableSet {ω : Configuration d | (openIn ω (D \ R)).Reachable y z} :=
    bondSigma_mono hlocal _
      (measurableSet_reachable_openIn_bondSigma (D \ R) (hD.subset Set.sdiff_subset) hy hz)
  have htarget (z : Vertex d) : MeasurableSet {ω : Configuration d | z ∈ K ω} :=
    measurableSet_setOf.mpr ((measurable_finset_iff.mp hK) z)
  have heq : {ω : Configuration d | e ∈ boundaryCandidateBonds R D F K ω} =
      ⋃ (_ : e ∈ F), ⋃ x ∈ R, ⋃ y ∈ D \ R,
      ⋃ hxy : (nearestNeighborGraph d).Adj x y, ⋃ (_ : e = bondOfAdjacent hxy),
      ⋃ z ∈ D \ R, {ω | z ∈ K ω} ∩ {ω | (openIn ω (D \ R)).Reachable y z} := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_boundaryCandidateBonds, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨he, x, hx, y, hy, hxy, heq, z, hzK, hz, h⟩
      exact ⟨he, x, hx, y, hy, hxy, heq, z, hz, hzK, h⟩
    · rintro ⟨he, x, hx, y, hy, hxy, heq, z, hz, hzK, h⟩
      exact ⟨he, x, hx, y, hy, hxy, heq, z, hzK, hz, h⟩
  apply measurableSet_setOf.mp
  rw [heq]
  exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun x =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun hy => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun z =>
    MeasurableSet.iUnion fun hz => (htarget z).inter (hreach y z hy hz)

/-- Closing every candidate is equivalent to the absence of an open
boundary bond whose exterior endpoint reaches a target. -/
theorem allBondsClosed_boundaryCandidateBonds_iff {d : ℕ} (R D : Set (Vertex d))
    (F : Finset (Bond d)) (K : Configuration d → Finset (Vertex d)) (ω : Configuration d) :
    ω ∈ allBondsClosed (boundaryCandidateBonds R D F K ω) ↔
      ¬ ∃ x ∈ R, ∃ y ∈ D \ R, ∃ hxy : (nearestNeighborGraph d).Adj x y,
        bondOfAdjacent hxy ∈ F ∧ ω (bondOfAdjacent hxy) = true ∧
          ∃ z ∈ K ω, z ∈ D \ R ∧ (openIn ω (D \ R)).Reachable y z := by
  classical
  constructor
  · intro h ⟨x, hx, y, hy, hxy, he, hopen, z, hzK, hz, hreach⟩
    have hc := h (bondOfAdjacent hxy)
      ((mem_boundaryCandidateBonds R D F K ω _).mpr
        ⟨he, x, hx, y, hy, hxy, rfl, z, hzK, hz, hreach⟩)
    rw [hopen] at hc
    cases hc
  · intro h e he
    obtain ⟨heF, x, hx, y, hy, hxy, rfl, z, hzK, hz, hreach⟩ :=
      (mem_boundaryCandidateBonds R D F K ω e).mp he
    cases ho : ω (bondOfAdjacent hxy) with
    | false => rfl
    | true => exact (h ⟨x, hx, y, hy, hxy, heF, ho, z, hzK, hz, hreach⟩).elim

/-- The probability that at most `t` exterior-reaching boundary candidates
exist is controlled by the probability that none of them is open. -/
theorem measureReal_few_boundaryCandidateBonds_le {d : ℕ} (p : unitInterval)
    (hp : (p : ℝ) < 1) (R D : Set (Vertex d)) (hD : D.Finite)
    (F : Finset (Bond d)) (K : Configuration d → Finset (Vertex d)) (t : ℕ)
    (hK : @Measurable _ _ (bondSigma (↑F : Set (Bond d))ᶜ) _ K)
    (hlocal : localBonds (D \ R) ⊆ (↑F : Set (Bond d))ᶜ) :
    (latticeBondLaw d p).real {ω | (boundaryCandidateBonds R D F K ω).card ≤ t} ≤
      (latticeBondLaw d p).real {ω | ω ∈ allBondsClosed (boundaryCandidateBonds R D F K ω)} /
        (1 - (p : ℝ)) ^ t := by
  apply measureReal_few_boundaryCandidates_le p hp (↑F : Set (Bond d))
    (boundaryCandidateBonds R D F K) t (measurable_boundaryCandidateBonds R D hD F K hK hlocal)
  intro ω e he
  exact (mem_boundaryCandidateBonds R D F K ω e).mp he |>.1

end Rigidity.Percolation

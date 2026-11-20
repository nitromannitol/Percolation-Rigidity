import Rigidity.Percolation.BoundaryCandidatePaths
import Rigidity.Percolation.LatticeBoundaryBonds

/-!
# Candidate exits from a finite explored set

The bonds leaving a finite explored set form a finite cut. Exterior paths use
no bonds in this cut, so the candidate-bond finite-energy estimate applies.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The finite set of lattice bonds leaving a finite vertex set. -/
noncomputable def vertexCutBonds {d : ℕ} (R : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact R.biUnion (outgoingBonds (R : Set (Vertex d)))

/-- Every bond from the explored set to its exterior lies in its cut. -/
theorem bondOfAdjacent_mem_vertexCutBonds {d : ℕ} (R : Finset (Vertex d))
    {x y : Vertex d} (hx : x ∈ R) (hy : y ∉ R)
    (hxy : (nearestNeighborGraph d).Adj x y) : bondOfAdjacent hxy ∈ vertexCutBonds R := by
  classical
  change bondOfAdjacent hxy ∈ R.biUnion (outgoingBonds (R : Set (Vertex d)))
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, ?_⟩
  exact bondOfAdjacent_mem_outgoingBonds (R : Set (Vertex d)) hy hxy

/-- A bond in a vertex cut has an endpoint in the explored set. -/
theorem exists_mem_of_mem_vertexCutBonds {d : ℕ} (R : Finset (Vertex d))
    {e : Bond d} (he : e ∈ vertexCutBonds R) : ∃ x ∈ R, x ∈ e.val := by
  classical
  obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp he
  unfold outgoingBonds at he
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp he
  exact ⟨x, hx, Sym2.mem_mk_left x y.val⟩

/-- Bonds internal to the exterior cannot belong to the cut. -/
theorem localBonds_sdiff_subset_vertexCutBonds_compl {d : ℕ} (R : Finset (Vertex d))
    (D : Set (Vertex d)) :
    localBonds (D \ (R : Set (Vertex d))) ⊆ (↑(vertexCutBonds R) : Set (Bond d))ᶜ := by
  intro e he hcut
  obtain ⟨x, hx, hxe⟩ := exists_mem_of_mem_vertexCutBonds R hcut
  exact (he x hxe).2 hx

/-- A small number of candidate exits is unlikely whenever a random exterior
target is likely to be reachable from the explored set. -/
theorem measureReal_few_candidates_le_not_reachable {d : ℕ} (p : unitInterval)
    (hp : (p : ℝ) < 1) (R : Finset (Vertex d)) (D : Set (Vertex d))
    (hD : D.Finite) (hRD : (R : Set (Vertex d)) ⊆ D)
    (K : Configuration d → Finset (Vertex d)) (t : ℕ)
    (hK : @Measurable _ _ (bondSigma (↑(vertexCutBonds R) : Set (Bond d))ᶜ) _ K) :
    (latticeBondLaw d p).real {ω |
      (boundaryCandidateBonds R D (vertexCutBonds R) K ω).card ≤ t} ≤
    (latticeBondLaw d p).real {ω | ¬ ∃ x ∈ R, ∃ z ∈ K ω,
      z ∈ D \ (R : Set (Vertex d)) ∧ (openIn ω D).Reachable x z} /
        (1 - (p : ℝ)) ^ t := by
  have h := measureReal_few_boundaryCandidateBonds_le p hp R D hD (vertexCutBonds R) K t hK
    (localBonds_sdiff_subset_vertexCutBonds_compl R D)
  have hF : ∀ x ∈ (R : Set (Vertex d)), ∀ y ∈ D \ (R : Set (Vertex d)),
      ∀ hxy : (nearestNeighborGraph d).Adj x y, bondOfAdjacent hxy ∈ vertexCutBonds R := by
    intro x hx y hy hxy
    exact bondOfAdjacent_mem_vertexCutBonds R hx hy.2 hxy
  have heq : {ω | ω ∈ allBondsClosed (boundaryCandidateBonds R D (vertexCutBonds R) K ω)} =
      {ω | ¬ ∃ x ∈ R, ∃ z ∈ K ω,
        z ∈ D \ (R : Set (Vertex d)) ∧ (openIn ω D).Reachable x z} := by
    ext ω
    exact allBondsClosed_boundaryCandidateBonds_iff_not_reachable R D hRD _ hF K ω
  rwa [heq] at h

end Rigidity.Percolation

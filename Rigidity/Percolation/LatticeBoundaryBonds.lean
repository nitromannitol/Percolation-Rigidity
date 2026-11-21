import Rigidity.Percolation.BondBoundaryEnergy

/-!
# Outgoing bonds of a lattice region

Each vertex has at most `2d` outgoing bonds, all disjoint from the bonds
internal to the region. These bonds give a concrete finite-energy extinction
estimate for the contacts reached by a finite seed.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The bonds joining a vertex to neighbors outside a region. -/
noncomputable def regionOutgoingBonds {d : ℕ} (P : Set (Vertex d)) (x : Vertex d) :
    Finset (Bond d) := by
  classical
  exact (((nearestNeighborGraph d).neighborFinset x).attach.filter fun y => y.1 ∉ P).image
    fun y => bondOfAdjacent ((SimpleGraph.mem_neighborFinset _ _ _).mp y.2)

/-- Every bond to a neighbor outside the region is among the outgoing bonds. -/
theorem bondOfAdjacent_mem_regionOutgoingBonds {d : ℕ} (P : Set (Vertex d))
    {x y : Vertex d} (hy : y ∉ P) (hxy : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent hxy ∈ regionOutgoingBonds P x := by
  classical
  unfold regionOutgoingBonds
  apply Finset.mem_image.mpr
  refine ⟨⟨y, (SimpleGraph.mem_neighborFinset _ _ _).mpr hxy⟩, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_attach, true_and]
  exact hy

/-- At most `2d` bonds leave a vertex. -/
theorem card_regionOutgoingBonds_le {d : ℕ} (P : Set (Vertex d)) (x : Vertex d) :
    (regionOutgoingBonds P x).card ≤ 2 * d := by
  classical
  unfold regionOutgoingBonds
  calc
    _ ≤ (((nearestNeighborGraph d).neighborFinset x).attach.filter
      fun y => y.1 ∉ P).card := Finset.card_image_le
    _ ≤ ((nearestNeighborGraph d).neighborFinset x).attach.card := Finset.card_filter_le _ _
    _ = 2 * d := by
      rw [Finset.card_attach, SimpleGraph.card_neighborFinset_eq_degree,
        LatticeProb.Graph.Zd.degree_eq]

/-- Outgoing bonds of an interior vertex are not internal to the region. -/
theorem disjoint_regionOutgoingBonds_localBonds {d : ℕ} (P : Set (Vertex d))
    {x : Vertex d} (hx : x ∈ P) :
    Disjoint (↑(regionOutgoingBonds P x) : Set (Bond d)) (localBonds P) := by
  classical
  rw [Set.disjoint_left]
  intro e he heP
  change e ∈ regionOutgoingBonds P x at he
  unfold regionOutgoingBonds at he
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
  have hyP : y.1 ∉ P := (Finset.mem_filter.mp hy).2
  have hdisj : Disjoint P Pᶜ := by
    rw [Set.disjoint_left]
    intro z hz hznot
    exact hznot hz
  exact (bondOfAdjacent_not_mem_localBonds hdisj
    hx hyP ((SimpleGraph.mem_neighborFinset _ _ _).mp y.2)).1 heP

/-- A seed with at most `m` reached boundary contacts can be cut off at
finite-energy cost `(1-p)^(2dm)`. -/
theorem finiteEnergy_seed_extinction_lattice {d : ℕ} (p : unitInterval)
    {P D : Set (Vertex d)} (roots face outer : Finset (Vertex d))
    (hP : P.Finite) (hroots : ∀ z ∈ roots, z ∈ P)
    (hfaceP : ∀ x ∈ face, x ∈ P)
    (hface : ∀ x ∈ P, ∀ y, y ∉ P →
      (nearestNeighborGraph d).Adj x y → x ∈ face)
    (houter : ∀ w ∈ outer, w ∉ P) (m : ℕ)
    {A : Set (Configuration d)} (hA : MeasurableSet[bondSigma (localBonds P)] A)
    (hcard : ∀ ω ∈ A, (seedReachableContacts P roots face ω).card ≤ m) :
    ENNReal.ofReal ((1 - (p : ℝ)) ^ (m * (2 * d))) * latticeBondLaw d p A ≤
      latticeBondLaw d p (A ∩ {ω | seedReachableContacts D roots outer ω = ∅}) :=
  finiteEnergy_seed_extinction p roots face outer hP hroots hfaceP hface houter
    (regionOutgoingBonds P) (2 * d) m
    (fun x hx => disjoint_regionOutgoingBonds_localBonds P (hfaceP x hx))
    (fun x _ => card_regionOutgoingBonds_le P x)
    (fun _ _ _ hy hxy => bondOfAdjacent_mem_regionOutgoingBonds P hy hxy) hA hcard

end Rigidity.Percolation

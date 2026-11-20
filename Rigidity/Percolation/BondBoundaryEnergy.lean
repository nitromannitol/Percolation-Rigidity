import Rigidity.Percolation.BondBoundaryExtinction
import Rigidity.Percolation.BondClosingEnergy

/-!
# Finite energy at reachable boundary contacts

Reachable contacts of a finite region are determined by its internal bonds.
Closing a bounded family of fresh boundary bonds therefore prevents the
starting seed from reaching outside the region at a controlled cost.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The contacts reached from a finite seed are determined by the bonds
internal to the finite region. -/
theorem measurable_seedReachableContacts_local {d : ℕ} (P : Set (Vertex d))
    (roots face : Finset (Vertex d)) (hP : P.Finite)
    (hroots : ∀ z ∈ roots, z ∈ P) (hface : ∀ x ∈ face, x ∈ P) :
    @Measurable _ _ (bondSigma (localBonds P)) _
      (seedReachableContacts P roots face) := by
  classical
  letI : MeasurableSpace (Configuration d) := bondSigma (localBonds P)
  apply measurable_finset_iff.mpr
  intro x
  apply measurableSet_setOf.mp
  by_cases hx : x ∈ face
  · have heq : {ω : Configuration d | x ∈ seedReachableContacts P roots face ω} =
        ⋃ z ∈ roots, {ω | (openIn ω P).Reachable z x} := by
      ext ω
      simp only [Set.mem_setOf_eq, mem_seedReachableContacts, hx, true_and, Set.mem_iUnion]
      constructor
      · rintro ⟨z, hz, h⟩
        exact ⟨z, hz, h⟩
      · rintro ⟨z, hz, h⟩
        exact ⟨z, hz, h⟩
    rw [heq]
    exact MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun hz =>
      measurableSet_reachable_openIn_bondSigma P hP (hroots z hz) (hface x hx)
  · have heq : {ω : Configuration d | x ∈ seedReachableContacts P roots face ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, mem_seedReachableContacts, hx, false_and,
        Set.mem_empty_iff_false]
    rw [heq]
    exact MeasurableSet.empty

/-- A union of uniformly bounded bond families has at most the product of
the number of contacts and the per-contact bound. -/
theorem card_contactBondUnion_le {d : ℕ} (contacts : Finset (Vertex d))
    (bonds : Vertex d → Finset (Bond d)) (N : ℕ)
    (hN : ∀ x ∈ contacts, (bonds x).card ≤ N) :
    (contacts.biUnion bonds).card ≤ contacts.card * N := by
  classical
  exact Finset.card_biUnion_le_card_mul contacts bonds N hN

/-- Closing fresh outgoing bonds from the reached contacts bounds the cost
of preventing all connections to a specified exterior face. -/
theorem finiteEnergy_seed_extinction {d : ℕ} (p : unitInterval)
    {P D : Set (Vertex d)} (roots face outer : Finset (Vertex d))
    (hP : P.Finite) (hroots : ∀ z ∈ roots, z ∈ P)
    (hfaceP : ∀ x ∈ face, x ∈ P)
    (hface : ∀ x ∈ P, ∀ y, y ∉ P →
      (nearestNeighborGraph d).Adj x y → x ∈ face)
    (houter : ∀ w ∈ outer, w ∉ P)
    (bonds : Vertex d → Finset (Bond d)) (N m : ℕ)
    (hfresh : ∀ x ∈ face, Disjoint (↑(bonds x) : Set (Bond d)) (localBonds P))
    (hN : ∀ x ∈ face, (bonds x).card ≤ N)
    (houtgoing : ∀ x ∈ face, ∀ y, y ∉ P →
      ∀ hxy : (nearestNeighborGraph d).Adj x y, bondOfAdjacent hxy ∈ bonds x)
    {A : Set (Configuration d)} (hA : MeasurableSet[bondSigma (localBonds P)] A)
    (hcard : ∀ ω ∈ A, (seedReachableContacts P roots face ω).card ≤ m) :
    ENNReal.ofReal ((1 - (p : ℝ)) ^ (m * N)) * latticeBondLaw d p A ≤
      latticeBondLaw d p (A ∩ {ω | seedReachableContacts D roots outer ω = ∅}) := by
  classical
  let Ψ := seedReachableContacts P roots face
  let φ : Finset (Vertex d) → Finset (Bond d) := fun contacts => contacts.biUnion bonds
  have hΨ := measurable_seedReachableContacts_local P roots face hP hroots hfaceP
  have henergy := latticeBondLaw_finiteEnergy_close p (localBonds P) Ψ φ (m * N)
    (fun b => hA.inter (hΨ (measurableSet_singleton b)))
    (by
      intro ω hω
      rw [Set.disjoint_left]
      intro e he heP
      obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp he
      exact Set.disjoint_left.mp (hfresh x ((mem_seedReachableContacts P roots face ω x).mp hx).1)
        he heP)
    (by
      intro ω hω
      exact (card_contactBondUnion_le _ bonds N fun x hx =>
        hN x ((mem_seedReachableContacts P roots face ω x).mp hx).1).trans
          (Nat.mul_le_mul_right N (hcard ω hω)))
  refine henergy.trans (measure_mono ?_)
  rintro ω ⟨hω, hclosed⟩
  refine ⟨hω, seedReachableContacts_eq_empty_of_closed_contacts hroots hface ?_ houter⟩
  intro x hx y hy hxy
  exact hclosed _ (Finset.mem_biUnion.mpr ⟨x, hx,
    houtgoing x ((mem_seedReachableContacts P roots face ω x).mp hx).1 y hy hxy⟩)

end Rigidity.Percolation

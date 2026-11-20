import Rigidity.Percolation.BoundaryCandidateGeometry

/-!
# Paths through exterior-reaching boundary bonds

A path from an explored region to an exterior target has a last exit from
the region. That exit is an open candidate boundary bond.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- An exterior target is reachable from the explored region precisely when
at least one exterior-reaching boundary candidate is open. -/
theorem exists_reachable_exterior_target_iff_candidate_open {d : ℕ}
    (R D : Set (Vertex d)) (hRD : R ⊆ D) (F : Finset (Bond d))
    (hF : ∀ x ∈ R, ∀ y ∈ D \ R, ∀ hxy : (nearestNeighborGraph d).Adj x y,
      bondOfAdjacent hxy ∈ F) (K : Configuration d → Finset (Vertex d))
    (ω : Configuration d) :
    (∃ x ∈ R, ∃ z ∈ K ω, z ∈ D \ R ∧ (openIn ω D).Reachable x z) ↔
      ∃ e ∈ boundaryCandidateBonds R D F K ω, ω e = true := by
  constructor
  · rintro ⟨x, hx, z, hzK, hz, hreach⟩
    have hdisj : Disjoint (D \ R) R := by
      rw [Set.disjoint_left]
      intro v hv hvr
      exact hv.2 hvr
    have hcover : D ⊆ (D \ R) ∪ R := by
      intro v hv
      by_cases hvr : v ∈ R
      · exact Or.inr hvr
      · exact Or.inl ⟨hv, hvr⟩
    obtain ⟨u, hu, v, hv, huv, hzu, hopen⟩ :=
      exists_slab_attachment_of_reachable hdisj hcover hz hx hreach.symm
    have hvu : (nearestNeighborGraph d).Adj v u := huv.symm
    have hopen' : ω (bondOfAdjacent hvu) = true := by
      rw [bondOfAdjacent_symm]
      exact hopen
    refine ⟨bondOfAdjacent hvu, ?_, hopen'⟩
    exact (mem_boundaryCandidateBonds R D F K ω _).mpr
      ⟨hF v hv u hu hvu, v, hv, u, hu, hvu, rfl, z, hzK, hz, hzu.symm⟩
  · rintro ⟨e, he, hopen⟩
    obtain ⟨_, x, hx, y, hy, hxy, rfl, z, hzK, hz, hreach⟩ :=
      (mem_boundaryCandidateBonds R D F K ω e).mp he
    have hedge : (openIn ω D).Adj x y :=
      ⟨(openGraph_adj_iff ω x y).mpr ⟨hxy, hopen⟩, hRD hx, hy.1⟩
    have htail : (openIn ω D).Reachable y z := hreach.mono (by
      intro a b hab
      exact ⟨hab.1, hab.2.1.1, hab.2.2.1⟩)
    exact ⟨x, hx, z, hzK, hz, hedge.reachable.trans htail⟩

/-- All candidate boundary bonds are closed exactly when no exterior target
is reachable from the explored region. -/
theorem allBondsClosed_boundaryCandidateBonds_iff_not_reachable {d : ℕ}
    (R D : Set (Vertex d)) (hRD : R ⊆ D) (F : Finset (Bond d))
    (hF : ∀ x ∈ R, ∀ y ∈ D \ R, ∀ hxy : (nearestNeighborGraph d).Adj x y,
      bondOfAdjacent hxy ∈ F) (K : Configuration d → Finset (Vertex d))
    (ω : Configuration d) :
    ω ∈ allBondsClosed (boundaryCandidateBonds R D F K ω) ↔
      ¬ ∃ x ∈ R, ∃ z ∈ K ω, z ∈ D \ R ∧ (openIn ω D).Reachable x z := by
  rw [exists_reachable_exterior_target_iff_candidate_open R D hRD F hF K ω]
  change (∀ e ∈ boundaryCandidateBonds R D F K ω, ω e = false) ↔ _
  constructor
  · intro h ⟨e, he, ho⟩
    rw [h e he] at ho
    cases ho
  · intro h e he
    cases ho : ω e with
    | false => rfl
    | true => exact (h ⟨e, he, ho⟩).elim

end Rigidity.Percolation

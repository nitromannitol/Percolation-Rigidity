import Rigidity.Percolation.TriadicStopping

/-!
# Witnesses for differences between stopping partitions

When a collection of good cubes is enlarged, a change in the maximal stopping
cube forces a newly good cube in an influence set associated with one of the
stopping cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- Enlarging the good collection can change the stopping cube only if a newly
good cube influences the smaller partition's cube or a child of the other cube. -/
theorem TriadicCube.exists_new_good_of_stopping_ne {d : ℕ}
    {G H : Set (TriadicCube d)} (hGH : G ⊆ H)
    {Q R : TriadicCube d} {x : Vertex d}
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H) (hne : Q ≠ R) :
    ∃ T : TriadicCube d,
      (T ∈ R.influence ∨ 0 < Q.scale ∧ ∃ digits, T ∈ (Q.child digits).influence) ∧
        T ∉ G ∧ T ∈ H := by
  classical
  have hmono : ∀ S : TriadicCube d, S ∈ stableGood G → S ∈ stableGood H :=
    fun _ hS => hS.trans hGH
  by_cases hstable : R ∈ stableGood G
  · have hstop : R.IsStopping G := by
      refine ⟨hstable, ?_⟩
      rcases hR.1.2 with hz | ⟨digits, hbad⟩
      · exact Or.inl hz
      · exact Or.inr ⟨digits, fun h => hbad (hmono _ h)⟩
    have hlt : R.scale < Q.scale := by
      by_contra h
      have hle : Q.scale ≤ R.scale := by omega
      have hsub := vertices_subset_of_mem_of_scale_le hxQ hxR hle
      have hrev := hQ.2 R hstop hsub
      exact hne (eq_of_mem_of_scale_eq (Nat.le_antisymm hle hrev) hxQ hxR)
    have hsub := vertices_subset_of_mem_of_scale_le hxR hxQ (Nat.le_of_lt hlt)
    have hnotstop : ¬ Q.IsStopping H := by
      intro hstopQ
      have := hR.2 Q hstopQ hsub
      omega
    obtain ⟨digits, hbad⟩ : ∃ digits, Q.child digits ∉ stableGood G := by
      rcases hQ.1.2 with hz | h
      · omega
      · exact h
    have hgoodH : Q.child digits ∈ stableGood H := by
      by_contra h
      exact hnotstop ⟨hmono _ hQ.1.1, Or.inr ⟨digits, h⟩⟩
    simp only [stableGood, Set.mem_setOf_eq, Set.not_subset] at hbad
    obtain ⟨T, hT, hTG⟩ := hbad
    exact ⟨T, Or.inr ⟨by omega, digits, hT⟩, hTG, hgoodH hT⟩
  · simp only [stableGood, Set.mem_setOf_eq, Set.not_subset] at hstable
    obtain ⟨T, hT, hTG⟩ := hstable
    exact ⟨T, Or.inl hT, hTG, hR.1.1 hT⟩

end Rigidity.Percolation

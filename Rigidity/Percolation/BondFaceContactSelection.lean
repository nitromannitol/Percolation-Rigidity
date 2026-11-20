import Rigidity.Percolation.BondFaceSeedSelection

/-!
# Selecting separated face contacts

A lower bound on the number of contacts yields a family indexed by a finite
interval whose members occupy different grid cells.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A finite set with at least `m * k ^ d` vertices contains `m` contacts
in different grid cells. -/
theorem exists_contacts_distinct_seedGridIndex {d k m : ℕ} (hk : 0 < k)
    (s : Finset (Vertex d)) (hcard : m * k ^ d ≤ s.card) :
    ∃ x : Fin m → Vertex d, (∀ t, x t ∈ s) ∧
      Function.Injective (fun t => seedGridIndex k (x t)) := by
  classical
  have hp : 0 < k ^ d := pow_pos hk _
  have hm : m ≤ (s.image (seedGridIndex k)).card := by
    apply Nat.le_of_mul_le_mul_right _ hp
    exact hcard.trans (card_le_card_seedGridIndex_mul hk s)
  have hc : Fintype.card (Fin m) ≤ Fintype.card ↥(s.image (seedGridIndex k)) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hm
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  have hw (t : Fin m) : ∃ x ∈ s, seedGridIndex k x = (e t : Vertex d) :=
    Finset.mem_image.mp (e t).property
  let x : Fin m → Vertex d := fun t => Classical.choose (hw t)
  have hx (t : Fin m) : x t ∈ s ∧ seedGridIndex k (x t) = (e t : Vertex d) :=
    Classical.choose_spec (hw t)
  refine ⟨x, fun t => (hx t).1, ?_⟩
  intro t u htu
  apply e.injective
  apply Subtype.ext
  exact (hx t).2.symm.trans (htu.trans (hx u).2)

end Rigidity.Percolation

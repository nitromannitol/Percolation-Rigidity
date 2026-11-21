import Rigidity.Percolation.TriadicStopping

/-!
# Partitions of larger collections of good cubes are finer

If every cube good for a collection `G` is good for a collection `G'`, then every cube of the
partition of `G'` is contained in the cube of the partition of `G` meeting it. Armstrong and Dario
use this to compare the partitions `𝒫`, `ℛ` and `𝒬` of Section 3: the stable cubes of `G` are
stable for `G'`, so a stopping cube of `G'` is either a stopping cube of `G` or lies below the
cubes stable for `G`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

variable {d : ℕ}

/-- Stability is monotone in the collection of good cubes. -/
theorem TriadicCube.stableGood_mono {G G' : Set (TriadicCube d)} (h : G ⊆ G') :
    stableGood G ⊆ stableGood G' := fun _ hQ => hQ.trans h

/-- **The partition of a larger collection is finer.** If `G ⊆ G'`, the maximal stopping cube of
`G'` at a point lies in the maximal stopping cube of `G` at that point. -/
theorem TriadicCube.IsMaximalStopping.vertices_subset_of_subset {G G' : Set (TriadicCube d)}
    (hGG' : G ⊆ G') {Q Q' : TriadicCube d} {x : Vertex d} (hQ : Q.IsMaximalStopping G)
    (hxQ : x ∈ Q.vertices) (hQ' : Q'.IsMaximalStopping G') (hxQ' : x ∈ Q'.vertices) :
    Q'.vertices ⊆ Q.vertices := by
  apply TriadicCube.vertices_subset_of_mem_of_scale_le hxQ' hxQ
  by_contra hlt
  have hlt' : Q.scale < Q'.scale := not_le.1 hlt
  have hsub : Q.vertices ⊆ Q'.vertices :=
    TriadicCube.vertices_subset_of_mem_of_scale_le hxQ hxQ' hlt'.le
  obtain ⟨-, hstop⟩ := hQ'.1
  rcases hstop with h0 | ⟨digits, hbad⟩
  · omega
  have hbadG : Q'.child digits ∉ stableGood G := fun h => hbad (stableGood_mono hGG' h)
  by_cases hstab : Q' ∈ stableGood G
  · exact absurd (hQ.2 Q' ⟨hstab, Or.inr ⟨digits, hbadG⟩⟩ hsub) (not_le.2 hlt')
  · apply hstab
    rw [TriadicCube.eq_ancestor_of_mem hxQ hxQ' hlt'.le]
    exact TriadicCube.ancestor_mem_stableGood hQ.1.1 _

end Rigidity.Percolation

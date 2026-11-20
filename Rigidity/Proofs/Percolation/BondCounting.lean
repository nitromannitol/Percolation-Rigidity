import Rigidity.Proofs.Percolation.BoundedDegreeLattice
import Rigidity.Proofs.S3.ChemicalDistance

/-!
# Counting lattice bonds incident to finite vertex sets

The number of bonds incident to a finite vertex set is bounded by the vertex count times the
lattice degree.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation OAI.CriticalPercolation Rigidity.External

/-- A finite family of bonds incident to a vertex set has size at most the sum of the degrees. -/
theorem card_bonds_incident_le (d : ℕ) (S : Finset (Bond d)) (V : Finset (Vertex d))
    (hS : ∀ e ∈ S, ∃ v ∈ V, v ∈ e.val) : S.card ≤ 2 * d * V.card := by
  classical
  let I (v : Vertex d) : Finset (Bond d) := (labelledLattice_locallyFinite d v).toFinset
  have hI (v : Vertex d) : (I v).card = 2 * d := by
    have heq : {e : Bond d | v ∈ e.val} = (labelledLattice d).incidentEdges {v} := by
      ext e
      simp only [BondGraph.incidentEdges, Set.mem_setOf_eq, Set.mem_singleton_iff,
        exists_eq_left, labelledLattice]
    rw [← labelledLattice_incidentEdges_ncard d v, ← heq]
    exact (Set.ncard_eq_toFinset_card _ (labelledLattice_locallyFinite d v)).symm
  have hsub : S ⊆ V.biUnion I := by
    intro e he
    obtain ⟨v, hv, he'⟩ := hS e he
    exact Finset.mem_biUnion.mpr ⟨v, hv, (Set.Finite.mem_toFinset _).2 he'⟩
  calc
    _ ≤ (V.biUnion I).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ V, (I v).card := Finset.card_biUnion_le
    _ = 2 * d * V.card := by simp [hI, mul_comm]

/-- All bonds with an endpoint in a finite vertex set. -/
noncomputable def bondsIncidentTo (d : ℕ) (V : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact V.biUnion fun v => (labelledLattice_locallyFinite d v).toFinset

/-- Membership in the finite collection of incident bonds. -/
theorem mem_bondsIncidentTo (d : ℕ) (V : Finset (Vertex d)) (e : Bond d) :
    e ∈ bondsIncidentTo d V ↔ ∃ v ∈ V, v ∈ e.val := by
  classical
  simp only [bondsIncidentTo, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    labelledLattice]

/-- The incident-bond collection is bounded by the total lattice degree. -/
theorem card_bondsIncidentTo_le (d : ℕ) (V : Finset (Vertex d)) :
    (bondsIncidentTo d V).card ≤ 2 * d * V.card :=
  card_bonds_incident_le d _ V fun e he => (mem_bondsIncidentTo d V e).1 he

/-- A family of bonds touching a lattice cube has at most degree times volume members. -/
theorem card_bonds_incident_cube_le (d : ℕ) (S : Finset (Bond d)) (z : Vertex d) (r : ℕ)
    (hS : ∀ e ∈ S, ∃ v ∈ cubeAt z r, v ∈ e.val) :
    S.card ≤ 2 * d * (2 * r + 1) ^ d := by
  have h := card_bonds_incident_le d S (Rigidity.Proofs.S3.cubeFinset z r) fun e he => by
    obtain ⟨v, hv, hev⟩ := hS e he
    exact ⟨v, Rigidity.Proofs.S3.mem_cubeFinset.mpr hv, hev⟩
  simpa only [Rigidity.Proofs.S3.card_cubeFinset] using h

end Rigidity.Percolation

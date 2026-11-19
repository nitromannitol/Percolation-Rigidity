import Rigidity.Proofs.S3.ChemicalDistance

/-!
# Cardinality of paths in planar cubes

An injective path contained in a cube has at most as many vertices as the cube.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S3

namespace Rigidity.Percolation

/-- An injective planar path contained in a cube has at most `(2r + 1)²` vertices. -/
theorem path_card_le_cube {n r : ℕ} {z : Vertex 2} (γ : Fin (n + 1) → Vertex 2)
    (hγ : Function.Injective γ) (hmem : ∀ i, γ i ∈ cubeAt z r) :
    n + 1 ≤ (2 * r + 1) ^ 2 := by
  classical
  have hsub : Finset.univ.image γ ⊆ cubeFinset z r := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact mem_cubeFinset.mpr (hmem i)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hγ, Finset.card_univ, Fintype.card_fin,
    card_cubeFinset] at hcard
  exact hcard

/-- A sufficiently long injective path has a vertex outside a cube. -/
theorem exists_path_vertex_outside_cube {n r : ℕ} {z : Vertex 2}
    (γ : Fin (n + 1) → Vertex 2) (hγ : Function.Injective γ)
    (hn : (2 * r + 1) ^ 2 < n + 1) : ∃ i, γ i ∉ cubeAt z r := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hn) (path_card_le_cube γ hγ h)

/-- A sufficiently long injective path has a large coordinate displacement from its start. -/
theorem exists_path_coordinate_displacement {n r : ℕ}
    (γ : Fin (n + 1) → Vertex 2) (hγ : Function.Injective γ)
    (hn : (2 * r + 1) ^ 2 < n + 1) :
    ∃ (i : Fin (n + 1)) (j : Fin 2), (r : ℤ) < |γ i j - γ 0 j| := by
  obtain ⟨i, hi⟩ := exists_path_vertex_outside_cube γ hγ hn (z := γ 0)
  simp only [cubeAt, Set.mem_setOf_eq, not_forall, not_le] at hi
  exact ⟨i, hi⟩

end Rigidity.Percolation

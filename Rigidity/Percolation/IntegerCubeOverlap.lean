import Rigidity.Percolation.IntegerCube

/-!
# Overlap of lattice cubes

A cube meeting a sufficiently deep point of another cube contains a
prescribed smaller cube inside their intersection.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- If a cube meets a point at depth at least `k` inside another cube, and its
side is at least `k`, their intersection contains a cube of side `k`. -/
theorem IntegerCube.exists_cube_in_intersection {d : ℕ}
    (Q R : IntegerCube d) (x : Vertex d) (k : ℕ)
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices) (hk : k ≤ R.size)
    (hdeep : ∀ i, Q.corner i + (k : ℤ) ≤ x i ∧
      x i + (k : ℤ) ≤ Q.corner i + (Q.size : ℤ)) :
    ∃ T : IntegerCube d, T.size = k ∧
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices ∧
      (↑T.vertices : Set (Vertex d)) ⊆ R.vertices := by
  let T : IntegerCube d := ⟨fun i => max (Q.corner i) (R.corner i), k⟩
  have hQ := (IntegerCube.mem_vertices Q x).mp hxQ
  have hR := (IntegerCube.mem_vertices R x).mp hxR
  have hcast : (k : ℤ) ≤ (R.size : ℤ) := by exact_mod_cast hk
  refine ⟨T, rfl, ?_, ?_⟩
  · intro y hy
    change y ∈ T.vertices at hy
    change y ∈ Q.vertices
    rw [IntegerCube.mem_vertices] at hy ⊢
    intro i
    have h := hy i
    have hdeep' := hdeep i
    have hx := hR i
    dsimp only [T] at h
    constructor
    · exact le_trans (le_max_left _ _) h.1
    · have htop : max (Q.corner i) (R.corner i) + (k : ℤ) ≤
          Q.corner i + (Q.size : ℤ) := by
        have := hQ i
        omega
      omega
  · intro y hy
    change y ∈ T.vertices at hy
    change y ∈ R.vertices
    rw [IntegerCube.mem_vertices] at hy ⊢
    intro i
    have h := hy i
    have hdeep' := hdeep i
    have hx := hR i
    dsimp only [T] at h
    constructor
    · exact le_trans (le_max_right _ _) h.1
    · have htop : max (Q.corner i) (R.corner i) + (k : ℤ) ≤
          R.corner i + (R.size : ℤ) := by
        omega
      omega

end Rigidity.Percolation

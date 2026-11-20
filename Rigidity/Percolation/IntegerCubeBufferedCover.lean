import Rigidity.Percolation.PathSegmentGeometry

/-!
# Buffered covers of integer cubes

Every point of a cube is contained in a smaller cube that also contains its
coordinate neighborhood relative to the ambient cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- A subcube whose corner is obtained by clamping a point-centered corner to
the range of corners of subcubes of the prescribed size. -/
def IntegerCube.bufferedSubcube {d : ℕ} (Q : IntegerCube d) (s : ℕ)
    (R : ℤ) (x : Vertex d) : IntegerCube d where
  corner k := max (Q.corner k) (min (x k - R) (Q.corner k + Q.size - s))
  size := s

/-- The clamped cube lies inside the ambient cube and contains the intersection
of the ambient cube with the coordinate box of radius `R` around `x`. -/
theorem IntegerCube.bufferedSubcube_spec {d : ℕ} (Q : IntegerCube d) (s : ℕ)
    (R : ℤ) (hs : 2 * R + 1 ≤ (s : ℤ))
    (hsQ : s ≤ Q.size) (x : Vertex d) (hx : x ∈ Q.vertices) :
    (↑(Q.bufferedSubcube s R x).vertices : Set (Vertex d)) ⊆ Q.vertices ∧
    ∀ y ∈ Q.vertices, (∀ k, |y k - x k| ≤ R) → y ∈ (Q.bufferedSubcube s R x).vertices := by
  have hcast : (s : ℤ) ≤ Q.size := by exact_mod_cast hsQ
  constructor
  · intro y hy
    change y ∈ (Q.bufferedSubcube s R x).vertices at hy
    change y ∈ Q.vertices
    rw [IntegerCube.mem_vertices] at hy ⊢
    intro k
    have hk := hy k
    dsimp only [bufferedSubcube] at hk
    simp only [max_def, min_def] at hk
    split_ifs at hk <;> omega
  · intro y hy hnear
    rw [IntegerCube.mem_vertices] at hx hy ⊢
    intro k
    have hxk := hx k
    have hyk := hy k
    have hnk := abs_le.mp (hnear k)
    dsimp only [bufferedSubcube]
    simp only [max_def, min_def]
    split_ifs <;> omega

/-- A long open path in a cube has a long segment in a subcube of any
sufficiently large prescribed side length. -/
theorem IntegerCube.exists_subcube_segment {d n : ℕ} (Q : IntegerCube d)
    (s : ℕ) (R : ℤ) (hR : 0 < R) (hs : 2 * R + 1 ≤ (s : ℤ))
    (hsQ : s ≤ Q.size) {ω : Configuration d}
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {γ : Fin (n + 1) → Vertex d}
    (hγ : IsSelectedOpenPath ω (↑Q.vertices) large n γ)
    (hdiam : pathDiameterAtLeast R n γ) :
    ∃ T : IntegerCube d, T.size = s ∧
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices ∧
      ∃ a m, ∃ h : a + m ≤ n,
        pathDiameterAtLeast R m (pathSegment γ a m h) ∧
        ∀ j, pathSegment γ a m h j ∈ T.vertices := by
  let ι := {T : IntegerCube d // T.size = s ∧
    (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices}
  let B : ι → Set (Vertex d) := fun T => T.val.vertices
  have hcover : ∀ x ∈ (↑Q.vertices : Set (Vertex d)), ∃ i : ι,
      ∀ y ∈ (↑Q.vertices : Set (Vertex d)), (∀ k, |y k - x k| ≤ R) → y ∈ B i := by
    intro x hx
    have hspec := Q.bufferedSubcube_spec s R hs hsQ x hx
    exact ⟨⟨Q.bufferedSubcube s R x, rfl, hspec.1⟩, hspec.2⟩
  obtain ⟨T, a, m, h, hlarge, hmem⟩ :=
    hγ.exists_segment_of_buffered_cover B R hR hdiam hcover
  exact ⟨T.val, T.property.1, T.property.2, a, m, h, hlarge, hmem⟩

end Rigidity.Percolation

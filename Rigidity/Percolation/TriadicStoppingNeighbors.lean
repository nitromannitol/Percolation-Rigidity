import Rigidity.Percolation.TriadicStopping

/-!
# Neighboring stopping cubes

A stable cube and a neighboring stopping cube have comparable scales. In
particular, neighboring maximal stopping cubes differ by at most one scale.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- If a stable cube is close to a cube two scales larger, every child of the
larger cube is stable. -/
theorem TriadicCube.child_mem_stableGood_of_near {d : ℕ} {G : Set (TriadicCube d)}
    {Q R : TriadicCube d} (hQ : Q ∈ stableGood G)
    (hscale : Q.scale + 2 ≤ R.scale)
    {x y : Vertex d} (hx : x ∈ Q.vertices) (hy : y ∈ R.vertices)
    (hnear : ∀ i, |x i - y i| ≤ 1) (digits : Fin d → Fin 3) :
    R.child digits ∈ stableGood G := by
  let T := Q.ancestor (R.scale - Q.scale - 2)
  have hT : T ∈ stableGood G := ancestor_mem_stableGood hQ _
  have hxT : x ∈ T.vertices := Q.vertices_subset_ancestor _ hx
  apply influence_subset_stableGood hT
  apply Relation.ReflTransGen.single
  constructor
  · change R.scale - 1 = T.scale + 1
    dsimp only [T]
    rw [scale_ancestor]
    omega
  · refine ⟨x, hxT, y, ?_, hnear⟩
    rw [child_parent R digits (by omega)]
    exact hy

/-- A stopping cube near a stable cube has scale at most one greater. -/
theorem TriadicCube.IsStopping.scale_le_of_near {d : ℕ} {G : Set (TriadicCube d)}
    {Q R : TriadicCube d} (hQ : Q ∈ stableGood G) (hR : R.IsStopping G)
    {x y : Vertex d} (hx : x ∈ Q.vertices) (hy : y ∈ R.vertices)
    (hnear : ∀ i, |x i - y i| ≤ 1) : R.scale ≤ Q.scale + 1 := by
  rcases hR.2 with hz | ⟨digits, hbad⟩
  · omega
  · by_contra h
    exact hbad (child_mem_stableGood_of_near hQ (by omega) hx hy hnear digits)

/-- Neighboring stopping cubes differ by at most one triadic scale. -/
theorem TriadicCube.IsStopping.scales_close_of_near {d : ℕ} {G : Set (TriadicCube d)}
    {Q R : TriadicCube d} (hQ : Q.IsStopping G) (hR : R.IsStopping G)
    {x y : Vertex d} (hx : x ∈ Q.vertices) (hy : y ∈ R.vertices)
    (hnear : ∀ i, |x i - y i| ≤ 1) :
    Q.scale ≤ R.scale + 1 ∧ R.scale ≤ Q.scale + 1 := by
  constructor
  · apply hQ.scale_le_of_near hR.1 hy hx
    intro i
    rw [abs_sub_comm]
    exact hnear i
  · exact hR.scale_le_of_near hQ.1 hx hy hnear

end Rigidity.Percolation

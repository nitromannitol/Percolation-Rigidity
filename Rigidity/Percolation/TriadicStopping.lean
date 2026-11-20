import Rigidity.Percolation.TriadicStableAncestors

/-!
# Stopping cubes

Stable cubes with a nonstable child, together with stable singletons, form
candidates for the maximal stopping cubes of the triadic partition.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A stable cube which is a singleton or has a nonstable child. -/
def TriadicCube.IsStopping {d : ℕ} (G : Set (TriadicCube d)) (Q : TriadicCube d) : Prop :=
  Q ∈ stableGood G ∧ (Q.scale = 0 ∨ ∃ digits, Q.child digits ∉ stableGood G)

/-- Every point of a stable cube lies in a stopping cube. -/
theorem TriadicCube.exists_stopping_of_mem_stableGood {d : ℕ}
    {G : Set (TriadicCube d)} {Q : TriadicCube d} {x : Vertex d}
    (hQ : Q ∈ stableGood G) (hx : x ∈ Q.vertices) :
    ∃ R : TriadicCube d, x ∈ R.vertices ∧ R.IsStopping G := by
  induction hn : Q.scale using Nat.strong_induction_on generalizing Q with
  | h n ih =>
    by_cases hz : Q.scale = 0
    · exact ⟨Q, hx, hQ, Or.inl hz⟩
    · have hp : 0 < Q.scale := Nat.pos_of_ne_zero hz
      obtain ⟨digits, hmem⟩ := Q.mem_child_of_mem hp hx
      by_cases hchild : Q.child digits ∈ stableGood G
      · refine ih (Q.child digits).scale ?_ hchild hmem rfl
        change Q.scale - 1 < n
        omega
      · exact ⟨Q, hx, hQ, Or.inr ⟨digits, hchild⟩⟩

/-- A stopping cube meeting a stable cube has scale at most one greater. -/
theorem TriadicCube.IsStopping.scale_le_of_mem {d : ℕ} {G : Set (TriadicCube d)}
    {Q R : TriadicCube d} {x : Vertex d} (hQ : Q ∈ stableGood G)
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices) (hR : R.IsStopping G) :
    R.scale ≤ Q.scale + 1 := by
  rcases hR.2 with hz | ⟨digits, hbad⟩
  · omega
  · exact scale_le_of_not_child_mem_stableGood hQ hxQ hxR digits hbad

/-- A largest stopping cube exists at each point covered by a stable cube. -/
theorem TriadicCube.exists_largest_stopping_of_mem_stableGood {d : ℕ}
    {G : Set (TriadicCube d)} {Q : TriadicCube d} {x : Vertex d}
    (hQ : Q ∈ stableGood G) (hx : x ∈ Q.vertices) :
    ∃ R : TriadicCube d, x ∈ R.vertices ∧ R.IsStopping G ∧
      ∀ S : TriadicCube d, x ∈ S.vertices → S.IsStopping G → S.scale ≤ R.scale := by
  classical
  let P : ℕ → Prop := fun n => ∃ R : TriadicCube d, R.scale = n ∧ x ∈ R.vertices ∧ R.IsStopping G
  obtain ⟨T, hxT, hT⟩ := exists_stopping_of_mem_stableGood hQ hx
  have hTle : T.scale ≤ Q.scale + 1 := hT.scale_le_of_mem hQ hx hxT
  have hP : P T.scale := ⟨T, rfl, hxT, hT⟩
  obtain ⟨R, hscale, hxR, hR⟩ := Nat.findGreatest_spec hTle hP
  refine ⟨R, hxR, hR, ?_⟩
  intro S hxS hS
  rw [hscale]
  exact Nat.le_findGreatest (hS.scale_le_of_mem hQ hx hxS) ⟨S, rfl, hxS, hS⟩

/-- A stopping cube maximal among stopping cubes that contain it. -/
def TriadicCube.IsMaximalStopping {d : ℕ} (G : Set (TriadicCube d))
    (Q : TriadicCube d) : Prop :=
  Q.IsStopping G ∧ ∀ R : TriadicCube d, R.IsStopping G → Q.vertices ⊆ R.vertices →
    R.scale ≤ Q.scale

/-- Intersecting triadic cubes are nested in order of scale. -/
theorem TriadicCube.vertices_subset_of_mem_of_scale_le {d : ℕ}
    {Q R : TriadicCube d} {x : Vertex d} (hxQ : x ∈ Q.vertices)
    (hxR : x ∈ R.vertices) (hscale : Q.scale ≤ R.scale) : Q.vertices ⊆ R.vertices := by
  rw [eq_ancestor_of_mem hxQ hxR hscale]
  exact Q.vertices_subset_ancestor _

/-- Largest stopping cubes at a point are maximal among all stopping cubes. -/
theorem TriadicCube.isMaximalStopping_of_largest {d : ℕ} {G : Set (TriadicCube d)}
    {Q : TriadicCube d} {x : Vertex d} (hx : x ∈ Q.vertices) (hQ : Q.IsStopping G)
    (hlargest : ∀ R : TriadicCube d, x ∈ R.vertices → R.IsStopping G → R.scale ≤ Q.scale) :
    Q.IsMaximalStopping G := by
  refine ⟨hQ, ?_⟩
  intro R hR hsub
  exact hlargest R (hsub hx) hR

/-- Intersecting maximal stopping cubes coincide. -/
theorem TriadicCube.eq_of_isMaximalStopping_of_mem {d : ℕ}
    {G : Set (TriadicCube d)} {Q R : TriadicCube d} {x : Vertex d}
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping G)
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices) : Q = R := by
  rcases le_total Q.scale R.scale with hle | hle
  · have hsub := vertices_subset_of_mem_of_scale_le hxQ hxR hle
    have hrev := hQ.2 R hR.1 hsub
    exact eq_of_mem_of_scale_eq (Nat.le_antisymm hle hrev) hxQ hxR
  · have hsub := vertices_subset_of_mem_of_scale_le hxR hxQ hle
    have hrev := hR.2 Q hQ.1 hsub
    exact eq_of_mem_of_scale_eq (Nat.le_antisymm hrev hle) hxQ hxR

/-- A point covered by a stable cube lies in a unique maximal stopping cube. -/
theorem TriadicCube.existsUnique_isMaximalStopping_of_mem_stableGood {d : ℕ}
    {G : Set (TriadicCube d)} {Q : TriadicCube d} {x : Vertex d}
    (hQ : Q ∈ stableGood G) (hx : x ∈ Q.vertices) :
    ∃! R : TriadicCube d, x ∈ R.vertices ∧ R.IsMaximalStopping G := by
  obtain ⟨R, hxR, hR, hlargest⟩ := exists_largest_stopping_of_mem_stableGood hQ hx
  have hmax := isMaximalStopping_of_largest hxR hR hlargest
  refine ⟨R, ⟨hxR, hmax⟩, ?_⟩
  intro S hS
  exact eq_of_isMaximalStopping_of_mem hS.2 hmax hS.1 hxR

end Rigidity.Percolation

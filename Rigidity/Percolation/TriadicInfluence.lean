import Rigidity.Percolation.TriadicCube

/-!
# Influence of triadic cubes

A cube influences each next-scale cube whose parent meets it or is at lattice
neighbor distance one. Iterating this relation gives the influence set used in
the construction of a partition into good cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- One step of the influence relation between triadic cubes. -/
def TriadicCube.InfluenceStep {d : ℕ} (Q R : TriadicCube d) : Prop :=
  R.scale = Q.scale + 1 ∧
    ∃ a ∈ Q.vertices, ∃ b ∈ R.parent.vertices,
      a = b ∨ (nearestNeighborGraph d).Adj a b

/-- The cubes reachable by finitely many influence steps. -/
def TriadicCube.influence {d : ℕ} (Q : TriadicCube d) : Set (TriadicCube d) :=
  {R | Relation.ReflTransGen InfluenceStep Q R}

/-- Cubes whose entire influence set consists of good cubes. -/
def TriadicCube.stableGood {d : ℕ} (G : Set (TriadicCube d)) : Set (TriadicCube d) :=
  {Q | Q.influence ⊆ G}

/-- A cube belongs to its own influence set. -/
theorem TriadicCube.mem_influence_self {d : ℕ} (Q : TriadicCube d) : Q ∈ Q.influence :=
  Relation.ReflTransGen.refl

/-- The influence set of an influenced cube is contained in the original influence set. -/
theorem TriadicCube.influence_subset {d : ℕ} {Q R : TriadicCube d} (h : R ∈ Q.influence) :
    R.influence ⊆ Q.influence := fun _ h' => h.trans h'

/-- Stability under influence implies the original goodness condition. -/
theorem TriadicCube.stableGood_subset {d : ℕ} (G : Set (TriadicCube d)) : stableGood G ⊆ G :=
  fun Q hQ => hQ Q.mem_influence_self

/-- The good cubes stable under influence are themselves closed under influence. -/
theorem TriadicCube.influence_subset_stableGood {d : ℕ} {G : Set (TriadicCube d)}
    {Q : TriadicCube d} (hQ : Q ∈ stableGood G) : Q.influence ⊆ stableGood G := by
  intro R hR
  exact (influence_subset hR).trans hQ

/-- The center of a cube is one of its lattice points. -/
theorem TriadicCube.center_mem {d : ℕ} (Q : TriadicCube d) :
    (fun i => Q.side * Q.index i) ∈ Q.vertices := by
  intro i
  simpa only [sub_self, mul_zero, abs_zero] using Q.side_pos

/-- A cube influences its parent. -/
theorem TriadicCube.influenceStep_parent {d : ℕ} (Q : TriadicCube d) :
    Q.InfluenceStep Q.parent := by
  refine ⟨rfl, _, Q.center_mem, _, ?_, Or.inl rfl⟩
  exact Q.parent.vertices_subset_parent (Q.vertices_subset_parent Q.center_mem)

/-- Stability under influence passes to the parent of a cube. -/
theorem TriadicCube.parent_mem_stableGood {d : ℕ} {G : Set (TriadicCube d)}
    {Q : TriadicCube d} (hQ : Q ∈ stableGood G) : Q.parent ∈ stableGood G :=
  influence_subset_stableGood hQ (Relation.ReflTransGen.single Q.influenceStep_parent)

/-- Influence never decreases the scale. -/
theorem TriadicCube.scale_le_of_mem_influence {d : ℕ} {Q R : TriadicCube d}
    (h : R ∈ Q.influence) : Q.scale ≤ R.scale := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    rcases hstep with ⟨hscale, _⟩
    omega

/-- An influenced cube at the same scale is the original cube. -/
theorem TriadicCube.eq_of_mem_influence_of_scale_eq {d : ℕ} {Q R : TriadicCube d}
    (h : R ∈ Q.influence) (hscale : R.scale = Q.scale) : R = Q := by
  induction h with
  | refl => rfl
  | tail hreach hstep _ =>
    have hle := scale_le_of_mem_influence hreach
    have ht := hstep.1
    omega

/-- Every influence-closed collection contained in `G` is contained in `stableGood G`. -/
theorem TriadicCube.subset_stableGood {d : ℕ} {G H : Set (TriadicCube d)}
    (hHG : H ⊆ G) (hclosed : ∀ Q ∈ H, Q.influence ⊆ H) : H ⊆ stableGood G := by
  intro Q hQ R hR
  exact hHG (hclosed Q hQ hR)

/-- Stabilizing the good cubes twice does not change them. -/
theorem TriadicCube.stableGood_idem {d : ℕ} (G : Set (TriadicCube d)) :
    stableGood (stableGood G) = stableGood G := by
  apply Set.Subset.antisymm (stableGood_subset _)
  apply subset_stableGood (Set.Subset.rfl)
  intro Q hQ
  exact influence_subset_stableGood hQ

end Rigidity.Percolation

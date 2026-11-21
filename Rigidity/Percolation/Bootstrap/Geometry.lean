import Rigidity.Percolation.Bootstrap.Relay

/-!
# Geometry of the bootstrap

The bootstrap compares connection probabilities of seeds at scales `3m'` and `m'`. Fix two
distinct coordinate axes `a` (the long axis) and `b` (the offset axis). At scale `m` the region
is the cube `Q_{6m}`; its left zone is `{z_a ≤ -4m}` and its right zone `{z_a ≥ 4m}`. The left
anchor consists of the vertices of the left zone at distance at least `m/8` from the outside of
the zone. A left seed at scale `m` is a set inside the left zone containing a seed path at a
vertex of the left anchor.

At scale `m = 3m'` the two subregions are the cubes `±9m' e_b + Q_{6m'}`; they are disjoint and
contained in `Q_{18m'}`. The left exploration region `{z ∈ Q_{18m'} : z_a ≤ -4m'}` meets each
subregion exactly in its left zone, and it is far from the left zone of `Q_{18m'}` minus nothing:
left seeds of scale `3m'` lie in `{z_a ≤ -12m'}`, at distance `6m'` from the subregions.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- The left zone `{z ∈ Q_{6m} : z_a ≤ -4m}`. -/
def leftZone (a : Fin d) (m : ℕ) : Set (Vertex d) :=
  {z | z ∈ cubeAt 0 (6 * m) ∧ z a ≤ -(4 * m : ℤ)}

/-- The left anchor: vertices of the left zone at distance at least `m / 8` from its outside. -/
def leftAnchor (a : Fin d) (m : ℕ) : Set (Vertex d) :=
  {z | (-(6 * m : ℤ) + (m / 8 : ℕ) ≤ z a ∧ z a ≤ -(4 * m : ℤ) - (m / 8 : ℕ)) ∧
    ∀ j, j ≠ a → |z j| ≤ (6 * m : ℤ) - (m / 8 : ℕ)}

/-- A left seed of scale `m` and radius `u`: a finite set inside the left zone containing a seed
path at a vertex of the left anchor. -/
def LeftSeed (a : Fin d) (u m : ℕ) (S : Finset (Vertex d)) : Prop :=
  (S : Set (Vertex d)) ⊆ leftZone a m ∧ ∃ s ∈ leftAnchor a m, HasSeedPath (S : Set (Vertex d)) s u

/-- The left exploration region `{z ∈ Q_{18m'} : z_a ≤ -4m'}` at scale `3m'`. -/
def leftExplore (a : Fin d) (m' : ℕ) : Set (Vertex d) :=
  {z | z ∈ cubeAt 0 (18 * m') ∧ z a ≤ -(4 * m' : ℤ)}

/-- The left exploration region as a finite set. -/
def leftExploreFinset (a : Fin d) (m' : ℕ) : Finset (Vertex d) := by
  classical
  exact (cubeFinset 0 (18 * m')).filter fun z => z a ≤ -(4 * m' : ℤ)

/-- The finite left exploration region is the left exploration region. -/
theorem coe_leftExploreFinset (a : Fin d) (m' : ℕ) :
    ((leftExploreFinset a m' : Finset (Vertex d)) : Set (Vertex d)) = leftExplore a m' := by
  classical
  ext z
  simp only [leftExploreFinset, Finset.coe_filter, Set.mem_setOf_eq, leftExplore, mem_cubeFinset]

/-- The offset vector `k e_b`. -/
def offsetVec (b : Fin d) (k : ℤ) : Vertex d := Pi.single b k

/-- The left anchor of the subregion `σ 9m' e_b + Q_{6m'}`, as a finite set. -/
def shiftedAnchorFinset (a b : Fin d) (sg : ℤˣ) (m' : ℕ) : Finset (Vertex d) := by
  classical
  exact (cubeFinset 0 (18 * m')).filter fun z =>
    z - offsetVec b ((sg : ℤ) * (9 * m' : ℕ)) ∈ leftAnchor a m'

/-- A seed path contains a finite seed path. -/
theorem HasSeedPath.exists_finset_seed {S : Set (Vertex d)} {s : Vertex d} {u : ℕ}
    (h : HasSeedPath S s u) :
    ∃ γ : Finset (Vertex d), (↑γ : Set (Vertex d)) ⊆ S ∩ cubeAt s u ∧
      HasSeedPath (γ : Set (Vertex d)) s u := by
  classical
  obtain ⟨hs, v, hv, ⟨w⟩⟩ := h
  have hsC : s ∈ S ∩ cubeAt s u := ⟨hs, fun i => by simp⟩
  have hsupp := support_subset_of_walk_openIn w hsC
  refine ⟨w.support.toFinset, fun z hz => hsupp z (List.mem_toFinset.1 hz), ?_⟩
  refine ⟨List.mem_toFinset.2 w.start_mem_support, v, hv, ?_⟩
  have hsub : ∀ z ∈ w.support, z ∈ ((w.support.toFinset : Finset (Vertex d)) : Set (Vertex d)) ∩
      cubeAt s u := fun z hz => ⟨List.mem_toFinset.2 hz, (hsupp z hz).2⟩
  refine ⟨(w.transfer _ ?_)⟩
  intro e he
  obtain ⟨x, y, rfl⟩ : ∃ x y, e = s(x, y) := Sym2.inductionOn e (fun x y => ⟨x, y, rfl⟩)
  have hxy := w.adj_of_mem_edges he
  refine ⟨hxy.1, hsub x ?_, hsub y ?_⟩
  · exact w.fst_mem_support_of_mem_edges he
  · exact w.snd_mem_support_of_mem_edges he

end Rigidity.Percolation

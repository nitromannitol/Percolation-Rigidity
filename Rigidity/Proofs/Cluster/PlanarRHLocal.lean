import Rigidity.Proofs.Cluster.MeyersUniform
import Rigidity.Percolation.TriadicWellConnectedEdgeSigma

/-!
# The local family of cubes on which the reverse Hölder inequality holds, in dimension two

Armstrong and Dario (Definition 3.7) apply Proposition 2.1 to the family `{RH ≤ C}` of the cubes on
which a deterministic reverse Hölder inequality holds for the harmonic functions on the clusters of
the triple `3□`; this family is local (AD18.tex:1436-1447). Here a cube `□ = cube k x` satisfies
the reverse Hölder inequality (`PlanarRHCube A₀ ω k x`) when, for every set `C ⊆ 3□` closed under
the open edges inside `3□` and every function `u` harmonic at the points of `C` all of whose open
edges stay in `C`,
`|□|⁻¹ ∑_{□} |∇u 1_{𝐚 ≠ 0}|²_C ≤ A₀ (|3□|⁻¹ ∑_{3□} |∇u 1_{𝐚 ≠ 0}|_C^{4/3})^{3/2}`,
the exponent `2d/(d+1) = 4/3` of Definition 3.7. A triadic cube `T` of positive scale is good
(`planarRHGood`) when the inequality holds on each of its nine children; cubes of scale zero are
good. The inequality on a child reads only the open edges between vertices of its triple and their
lattice neighbours, which lie in the threefold enlargement of `T`; hence the failure event of `T`
belongs to the σ-algebra of the open edges inside `3T` (`measurableSet_not_mem_planarRHGood_local`),
the hypothesis (2.1) of Proposition 2.1.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- **The reverse Hölder inequality on `cube k x`** for every set of the triple closed under its
open edges and every function harmonic on it, with constant `A₀` and the exponents of
Definition 3.7 of Armstrong and Dario in dimension two. -/
def PlanarRHCube (A₀ : ℝ) (ω : Configuration 2) (k : ℕ) (x : Vertex 2) : Prop :=
  ∀ C : Finset (Vertex 2), C ⊆ enl 1 k x →
    (∀ z ∈ C, ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k x → w ∈ C) →
    ∀ u : Vertex 2 → ℝ, (∀ z ∈ C, (∀ w, (openGraph ω).Adj z w → w ∈ C) → openLaplacian ω u z = 0) →
      avg (cube k x) (clusterEnergy ω C u) ≤
        A₀ * avg (enl 1 k x) (fun z => clusterEnergy ω C u z ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1))) ^
          ((((2 : ℕ) : ℝ) + 1) / (2 : ℕ))

/-- **The local family of good cubes for the reverse Hölder inequality**: the cubes of scale zero,
and the cubes of positive scale on each of whose children `PlanarRHCube` holds. -/
def planarRHGood (A₀ : ℝ) (ω : Configuration 2) : Set (TriadicCube 2) :=
  {T | ∀ k : ℕ, T.scale = k + 1 → ∀ x ∈ T.vertices, PlanarRHCube A₀ ω k x}

variable {ω ω' : Configuration 2}

theorem neighborFinset_eq_of_adj_iff {z : Vertex 2}
    (h : ∀ w, ((openGraph ω').Adj z w ↔ (openGraph ω).Adj z w)) :
    (openGraph ω').neighborFinset z = (openGraph ω).neighborFinset z := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
  exact h w

theorem openLaplacian_eq_of_adj_iff {z : Vertex 2}
    (h : ∀ w, ((openGraph ω').Adj z w ↔ (openGraph ω).Adj z w)) (u : Vertex 2 → ℝ) :
    openLaplacian ω' u z = openLaplacian ω u z := by
  unfold openLaplacian
  rw [neighborFinset_eq_of_adj_iff h]

theorem clusterEnergy_eq_of_adj_iff {z : Vertex 2}
    (h : ∀ w, ((openGraph ω').Adj z w ↔ (openGraph ω).Adj z w)) (C : Finset (Vertex 2))
    (u : Vertex 2 → ℝ) : clusterEnergy ω' C u z = clusterEnergy ω C u z := by
  unfold clusterEnergy clusterGradSq
  rw [neighborFinset_eq_of_adj_iff h]

/-- Agreement of the open edges inside a region containing the lattice neighbours of the points of
`3□` gives agreement of the open edges at those points. -/
theorem adj_iff_of_near {R : Set (Vertex 2)}
    (hagree : ∀ a ∈ R, ∀ b ∈ R, ((openGraph ω').Adj a b ↔ (openGraph ω).Adj a b)) {z : Vertex 2}
    (hz : ∀ w : Vertex 2, (∀ i, |w i - z i| ≤ 1) → w ∈ R) (w : Vertex 2) :
    (openGraph ω').Adj z w ↔ (openGraph ω).Adj z w := by
  have hzR : z ∈ R := hz z fun i => by simp
  constructor
  · intro h
    have hw : w ∈ R := hz w fun i => by
      rw [abs_sub_comm]; exact abs_sub_le_one_of_openGraph_adj h i
    exact (hagree z hzR w hw).1 h
  · intro h
    have hw : w ∈ R := hz w fun i => by
      rw [abs_sub_comm]; exact abs_sub_le_one_of_openGraph_adj h i
    exact (hagree z hzR w hw).2 h

/-- One direction of the locality of `PlanarRHCube`. -/
theorem planarRHCube_of_adj_iff {A₀ : ℝ} {k : ℕ} {x : Vertex 2}
    (h : ∀ z ∈ enl 1 k x, ∀ w, ((openGraph ω').Adj z w ↔ (openGraph ω).Adj z w))
    (hω : PlanarRHCube A₀ ω k x) : PlanarRHCube A₀ ω' k x := by
  intro C hC hcl u hu
  have hcl' : ∀ z ∈ C, ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k x → w ∈ C :=
    fun z hz w hadj hw => hcl z hz w ((h z (hC hz) w).2 hadj) hw
  have hu' : ∀ z ∈ C, (∀ w, (openGraph ω).Adj z w → w ∈ C) → openLaplacian ω u z = 0 := by
    intro z hz hall
    rw [← openLaplacian_eq_of_adj_iff (h z (hC hz))]
    exact hu z hz fun w hw => hall w ((h z (hC hz) w).1 hw)
  have hE : ∀ z ∈ enl 1 k x, clusterEnergy ω' C u z = clusterEnergy ω C u z :=
    fun z hz => clusterEnergy_eq_of_adj_iff (h z hz) C u
  have h1 := hω C hC hcl' u hu'
  have e1 : avg (cube k x) (clusterEnergy ω' C u) = avg (cube k x) (clusterEnergy ω C u) := by
    unfold avg
    rw [Finset.sum_congr rfl fun z hz => hE z (cube_subset_enl 1 k x hz)]
  have e2 : avg (enl 1 k x) (fun z => clusterEnergy ω' C u z ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1))) =
      avg (enl 1 k x) (fun z => clusterEnergy ω C u z ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1))) := by
    unfold avg
    congr 1
    exact Finset.sum_congr rfl fun z hz => by simp only [hE z hz]
  rw [e1, e2]
  exact h1

/-- **Locality of `PlanarRHCube`.** -/
theorem planarRHCube_iff_of_adj_iff {A₀ : ℝ} {k : ℕ} {x : Vertex 2}
    (h : ∀ z ∈ enl 1 k x, ∀ w, ((openGraph ω').Adj z w ↔ (openGraph ω).Adj z w)) :
    PlanarRHCube A₀ ω' k x ↔ PlanarRHCube A₀ ω k x :=
  ⟨planarRHCube_of_adj_iff fun z hz w => (h z hz w).symm, planarRHCube_of_adj_iff h⟩

/-- The triple of a child, with the lattice neighbours of its points, lies in the threefold
enlargement of the cube. -/
theorem mem_centeredTriple_of_near_enl {T : TriadicCube 2} {k : ℕ} (hk : T.scale = k + 1)
    {x : Vertex 2} (hx : x ∈ T.vertices) {z w : Vertex 2} (hz : z ∈ enl 1 k x)
    (hw : ∀ i, |w i - z i| ≤ 1) : w ∈ T.centeredTriple := by
  intro i
  rw [enl, mem_box] at hz
  have h1 := hz i
  have h2 := hx i
  have h3 := hw i
  have hs : T.side = 3 ^ (k + 1) := by rw [TriadicCube.side, hk]
  have hcx : |center k x i - x i| ≤ halfSide k := by
    have := (mem_cube_iff (k := k) (x := x) (y := x)).2 rfl
    rw [cube, mem_box] at this
    rw [abs_sub_comm]
    exact this i
  have hh1 := two_mul_halfSide_add_one k
  have hh2 := two_mul_halfSide_add_one (k + 1)
  have hc : T.center i = T.side * T.index i := rfl
  rw [hc, hs]
  rw [hs] at h2
  have hp : (3 : ℤ) ^ (k + 1) = 3 * 3 ^ k := by ring
  rw [hp] at h2 ⊢
  rw [hp] at hh2
  rw [abs_lt] at h2 ⊢
  rw [abs_le] at h1 h3 hcx
  constructor <;> nlinarith [h1.1, h1.2, h3.1, h3.2, hcx.1, hcx.2, h2.1, h2.2]

/-- **Locality of the good cubes**: membership of `T` depends only on the open edges between
vertices of its threefold enlargement. -/
theorem mem_planarRHGood_iff_of_adj_iff {A₀ : ℝ} {T : TriadicCube 2}
    (hagree : ∀ a ∈ T.centeredTriple, ∀ b ∈ T.centeredTriple,
      ((openGraph ω').Adj a b ↔ (openGraph ω).Adj a b)) :
    T ∈ planarRHGood A₀ ω' ↔ T ∈ planarRHGood A₀ ω := by
  simp only [planarRHGood, Set.mem_setOf_eq]
  refine forall_congr' fun k => forall_congr' fun hk => forall₂_congr fun x hx => ?_
  exact planarRHCube_iff_of_adj_iff fun z hz w =>
    adj_iff_of_near hagree (fun w' hw' => mem_centeredTriple_of_near_enl hk hx hz hw') w

/-- **The hypothesis (2.1) of Proposition 2.1** for the good cubes of the reverse Hölder
inequality: the failure event of `T` belongs to the σ-algebra of the open edges inside `3T`. -/
theorem measurableSet_not_mem_planarRHGood_local (A₀ : ℝ) (T : TriadicCube 2) :
    MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ planarRHGood A₀ ω} := by
  refine localGraphSigma_le_localEdgeSigma _ T.finite_centeredTriple _ ?_
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{g | ∃ ω' : Configuration 2, (openGraph ω').induce T.centeredTriple = g ∧
    T ∉ planarRHGood A₀ ω'}, MeasurableSpace.measurableSet_top, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ω', hind, hω'⟩
    intro hω
    apply hω'
    refine (mem_planarRHGood_iff_of_adj_iff fun a ha b hb => ?_).2 hω
    have := congrArg (fun g : SimpleGraph T.centeredTriple => g.Adj ⟨a, ha⟩ ⟨b, hb⟩) hind
    simpa using this
  · intro hω
    exact ⟨ω, rfl, hω⟩

theorem localEdgeSigma_le (U : Set (Vertex 2)) :
    localEdgeSigma U ≤ (inferInstance : MeasurableSpace (Configuration 2)) := by
  refine MeasurableSpace.generateFrom_le fun E hE => ?_
  obtain ⟨x, _, y, _, rfl⟩ := hE
  exact measurableSet_openGraph_adj x y

theorem measurableSet_mem_planarRHGood (A₀ : ℝ) (T : TriadicCube 2) :
    MeasurableSet {ω : Configuration 2 | T ∈ planarRHGood A₀ ω} := by
  have h := localEdgeSigma_le _ _ (measurableSet_not_mem_planarRHGood_local A₀ T)
  have : {ω : Configuration 2 | T ∈ planarRHGood A₀ ω} = {ω | T ∉ planarRHGood A₀ ω}ᶜ := by
    ext ω; simp
  rw [this]
  exact h.compl

end Rigidity.Proofs.Cluster

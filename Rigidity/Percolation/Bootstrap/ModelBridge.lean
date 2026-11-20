import Rigidity.Proofs.Percolation.ClusterComparison
import Rigidity.Percolation.BondContactSymmetry
import Rigidity.Percolation.BondMarkSymmetry
import Rigidity.Vendor.FormalMathPercolation.Literature.GMFiniteSize
import Rigidity.External.WellConnected

/-!
# Lattice bond configurations and edge-set configurations

A Boolean bond configuration of the lattice determines the set of its open edges. Its law is
the edge-set Bernoulli law of the vendored percolation library and its open graph is the same,
so connections inside a vertex region correspond and probability bounds transfer between the
two descriptions. The cubes, their shells and the lattice symmetries are set up for both.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open _root_.Percolation.Literature

variable {d : ℕ}

/-- The set of open lattice edges of a Boolean bond configuration. -/
def edgeConfig (d : ℕ) (ω : Configuration d) :
    _root_.Percolation.Literature.BondConfig (Vertex d) :=
  extendEdges (LatticeModels.zdGraph d) (toEdgeConfig d ω)

/-- The open-edge set depends measurably on the configuration. -/
theorem measurable_edgeConfig (d : ℕ) : Measurable (edgeConfig d) :=
  (measurable_extendEdges _).comp (by unfold toEdgeConfig; fun_prop)

/-- The open-edge set of the Bernoulli lattice configuration has the edge-set Bernoulli law. -/
theorem latticeBondLaw_map_edgeConfig (d : ℕ) (p : unitInterval) :
    (latticeBondLaw d p).map (edgeConfig d) =
      _root_.Percolation.Literature.bondPercolation (LatticeModels.zdGraph d) p :=
  map_latticeBondLaw (d := d) (p := p)

/-- Probabilities of events of open-edge sets are probabilities of their preimages. -/
theorem latticeBondLaw_preimage_edgeConfig (p : unitInterval)
    {A : Set (_root_.Percolation.Literature.BondConfig (Vertex d))} (hA : MeasurableSet A) :
    latticeBondLaw d p (edgeConfig d ⁻¹' A) =
      _root_.Percolation.Literature.bondPercolation (LatticeModels.zdGraph d) p A := by
  rw [← latticeBondLaw_map_edgeConfig, Measure.map_apply (measurable_edgeConfig d) hA]

/-- Real form of the transfer of probabilities. -/
theorem latticeBondLaw_real_preimage_edgeConfig (p : unitInterval)
    {A : Set (_root_.Percolation.Literature.BondConfig (Vertex d))} (hA : MeasurableSet A) :
    (latticeBondLaw d p).real (edgeConfig d ⁻¹' A) =
      (_root_.Percolation.Literature.bondPercolation (LatticeModels.zdGraph d) p).real A := by
  rw [measureReal_def, measureReal_def, latticeBondLaw_preimage_edgeConfig p hA]

/-- The open graph of the open-edge set is the open graph of the configuration. -/
theorem openGraph_edgeConfig (ω : Configuration d) :
    _root_.Percolation.Literature.openGraph (edgeConfig d ω) =
      LatticeProb.Percolation.openGraph ω :=
  openGraph_eq d ω

/-- A walk of the restricted open graph between vertices of the region is a walk of the
induced open graph. -/
theorem reachable_induce_of_walk (ω : Configuration d) {S : Set (Vertex d)} :
    ∀ {x y : Vertex d} (_w : (openIn ω S).Walk x y) (hx : x ∈ S) (hy : y ∈ S),
      ((LatticeProb.Percolation.openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil, _, _ => SimpleGraph.Reachable.refl _
  | _, _, .cons h w, hx, hy =>
      (SimpleGraph.Adj.reachable
        (show ((LatticeProb.Percolation.openGraph ω).induce S).Adj ⟨_, hx⟩ ⟨_, h.2.2⟩ from h.1)).trans
        (reachable_induce_of_walk ω w h.2.2 hy)

/-- Reachability in the induced open graph is reachability in the restricted open graph. -/
theorem reachable_induce_iff_openIn (ω : Configuration d) {S : Set (Vertex d)} {x y : Vertex d}
    (hx : x ∈ S) (hy : y ∈ S) :
    ((LatticeProb.Percolation.openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ ↔ (openIn ω S).Reachable x y := by
  constructor
  · rintro ⟨w⟩
    let φ : (LatticeProb.Percolation.openGraph ω).induce S →g openIn ω S :=
      { toFun := Subtype.val
        map_rel' := fun {a b} h => ⟨h, a.2, b.2⟩ }
    exact ⟨w.map φ⟩
  · rintro ⟨w⟩
    exact reachable_induce_of_walk ω w hx hy

/-- Connections inside a region in the two descriptions agree. -/
theorem edgeConfig_mem_openConnIn_iff (ω : Configuration d) (S : Set (Vertex d))
    (x y : Vertex d) :
    edgeConfig d ω ∈ _root_.Percolation.Literature.openConnIn S x y ↔
      x ∈ S ∧ y ∈ S ∧ (openIn ω S).Reachable x y := by
  change (∃ (hx : x ∈ S) (hy : y ∈ S),
      ((_root_.Percolation.Literature.openGraph (edgeConfig d ω)).induce S).Reachable
        ⟨x, hx⟩ ⟨y, hy⟩) ↔ _
  rw [openGraph_edgeConfig]
  constructor
  · rintro ⟨hx, hy, h⟩
    exact ⟨hx, hy, (reachable_induce_iff_openIn ω hx hy).1 h⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨hx, hy, (reachable_induce_iff_openIn ω hx hy).2 h⟩

/-! ### Cubes and their shells -/

/-- The shell of the cube `x + Q_n`: its vertices with a coordinate at distance exactly `n`. -/
def cubeShell (x : Vertex d) (n : ℕ) : Set (Vertex d) :=
  {y | y ∈ cubeAt x n ∧ ∃ i, |y i - x i| = n}

/-- Membership in a cube. -/
theorem mem_cubeAt {x y : Vertex d} {n : ℕ} : y ∈ cubeAt x n ↔ ∀ i, |y i - x i| ≤ n :=
  Iff.rfl

/-- The vendored centred box is the cube at the origin. -/
theorem coe_box_eq_cubeAt (n : ℕ) :
    ((LatticeModels.box d n : Finset (Vertex d)) : Set (Vertex d)) = cubeAt 0 n := by
  ext y
  simp only [Finset.mem_coe, LatticeModels.mem_box, mem_cubeAt, Pi.zero_apply, sub_zero,
    abs_le]

/-- Adjacent lattice vertices differ by at most one in every coordinate. -/
theorem abs_sub_le_one_of_nearestNeighbor_adj {u v : Vertex d}
    (h : (nearestNeighborGraph d).Adj u v) (i : Fin d) : |u i - v i| ≤ 1 := by
  have hsum := lattice_adj_iff_l1Dist.mp h
  unfold latticeL1Dist at hsum
  have := Finset.single_le_sum (fun j _ => abs_nonneg (u j - v j)) (Finset.mem_univ i)
  omega

/-- The inner vertex boundary of the vendored box is the shell of the cube at the origin. -/
theorem coe_innerBoundary_box_eq_cubeShell [NeZero d] (n : ℕ) :
    ((LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d n) :
      Finset (Vertex d)) : Set (Vertex d)) = cubeShell 0 n := by
  ext y
  simp only [Finset.mem_coe, LatticeModels.mem_innerBoundary_iff]
  rw [← Finset.mem_coe, coe_box_eq_cubeAt]
  constructor
  · rintro ⟨hy, z, hz, hadj⟩
    refine ⟨hy, ?_⟩
    rw [← Finset.mem_coe, coe_box_eq_cubeAt, mem_cubeAt] at hz
    push Not at hz
    obtain ⟨i, hi⟩ := hz
    refine ⟨i, ?_⟩
    have h1 : |y i - z i| ≤ 1 := by
      rw [← nearestNeighborGraph_eq_zdGraph] at hadj
      exact abs_sub_le_one_of_nearestNeighbor_adj hadj i
    have h2 := hy i
    simp only [Pi.zero_apply, sub_zero] at hi h2 ⊢
    have h3 : |y i| ≤ n := h2
    rw [abs_le] at h1 h2
    rw [lt_abs] at hi
    apply le_antisymm h3
    rcases hi with hi | hi
    · rw [le_abs]; left; omega
    · rw [le_abs]; right; omega
  · rintro ⟨hy, i, hi⟩
    refine ⟨hy, ?_⟩
    simp only [Pi.zero_apply, sub_zero] at hi
    by_cases hpos : 0 ≤ y i
    · refine ⟨y + Pi.single i 1, ?_, ?_⟩
      · rw [← Finset.mem_coe, coe_box_eq_cubeAt, mem_cubeAt]
        intro h
        have := h i
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply, sub_zero] at this
        rw [abs_of_nonneg hpos] at hi
        rw [abs_le] at this
        omega
      · rw [LatticeModels.zdGraph_adj_iff]
        exact ⟨i, Or.inl rfl⟩
    · refine ⟨y - Pi.single i 1, ?_, ?_⟩
      · rw [← Finset.mem_coe, coe_box_eq_cubeAt, mem_cubeAt]
        intro h
        have := h i
        simp only [Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply, sub_zero] at this
        rw [abs_of_neg (lt_of_not_ge hpos)] at hi
        rw [abs_le] at this
        omega
      · rw [LatticeModels.zdGraph_adj_iff]
        exact ⟨i, Or.inr (by abel)⟩

/-! ### Lattice symmetries -/

/-- A lattice symmetry preserves every probability of the Bernoulli bond law. -/
theorem latticeBondLaw_preimage_latticeConfigurationEquiv (p : unitInterval)
    (f : Vertex d ≃ Vertex d) (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (A : Set (Configuration d)) :
    latticeBondLaw d p (latticeConfigurationEquiv f hf ⁻¹' A) = latticeBondLaw d p A := by
  have hmp : MeasurePreserving (latticeConfigurationEquiv f hf) (latticeBondLaw d p)
      (latticeBondLaw d p) :=
    ⟨(latticeConfigurationEquiv f hf).measurable,
      latticeBondLaw_map_piCongrLeft p (latticeBondEquiv f hf)⟩
  exact hmp.measure_preimage_equiv A

/-- A lattice symmetry carries connections inside a region to connections inside its image. -/
theorem openIn_reachable_latticeConfigurationEquiv_iff (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (ω : Configuration d)
    (B : Set (Vertex d)) (x y : Vertex d) :
    (openIn (latticeConfigurationEquiv f hf ω) (f '' B)).Reachable (f x) (f y) ↔
      (openIn ω B).Reachable x y :=
  (openInLatticeEquiv f hf ω B).reachable_iff

/-- Translation of the lattice. -/
abbrev translateEquiv (c : Vertex d) : Vertex d ≃ Vertex d := latticeVertexTranslation c

/-- Translation preserves lattice distance. -/
theorem translateEquiv_dist (c : Vertex d) :
    ∀ x y, latticeL1Dist (translateEquiv c x) (translateEquiv c y) = latticeL1Dist x y :=
  latticeL1Dist_latticeVertexTranslation c

/-- Translating a cube moves its centre. -/
theorem image_translate_cubeAt (c x : Vertex d) (n : ℕ) :
    translateEquiv c '' cubeAt x n = cubeAt (x + c) n := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    simpa [translateEquiv, latticeVertexTranslation] using hz i
  · intro hy
    refine ⟨y - c, fun i => ?_, by simp [translateEquiv, latticeVertexTranslation]⟩
    have := hy i
    simp only [Pi.add_apply] at this
    simpa [sub_sub, add_comm] using this

/-- Translating a shell moves its centre. -/
theorem image_translate_cubeShell (c x : Vertex d) (n : ℕ) :
    translateEquiv c '' cubeShell x n = cubeShell (x + c) n := by
  ext y
  constructor
  · rintro ⟨z, ⟨hz, i, hi⟩, rfl⟩
    refine ⟨fun j => ?_, i, ?_⟩
    · simpa [translateEquiv, latticeVertexTranslation] using hz j
    · simpa [translateEquiv, latticeVertexTranslation] using hi
  · rintro ⟨hy, i, hi⟩
    refine ⟨y - c, ⟨fun j => ?_, i, ?_⟩, by simp [translateEquiv, latticeVertexTranslation]⟩
    · have := hy j
      simp only [Pi.add_apply] at this
      simpa [sub_sub, add_comm] using this
    · simp only [Pi.add_apply] at hi
      simpa [sub_sub, add_comm] using hi

end Rigidity.Percolation

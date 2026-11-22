import Rigidity.Proofs.Percolation.GeneralDim.CubeEnergyBounds
import Rigidity.Proofs.Partition.Translation
import Rigidity.Percolation.RestrictedReachability
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw

/-!
# Locality, measurability and stationarity of `ν` on triadic cubes of `ℤ^d`

`ν(U, p)` is defined through the crossing cluster `C_*(U)` and the open edges between its
vertices, and does not involve the partition. If a bijection between the clusters of two cubes
preserves the open edges, the lattice interiors and the increments of affine functions, and the
cubes have the same volume, the two values of `ν` agree. Consequently:

* `ν(U, p)` depends only on the open edges with both endpoints in `U`, hence is a measurable
  function of the configuration;
* `ν(U + c, p)` at the configuration translated by `c` equals `ν(U, p)`, for every `c` in
  `size(U) ℤ^d`, so the expectation of `ν(U, p)` under the bond law is the same for all triadic
  cubes of a given scale.

In Armstrong and Dario the quantity `ν(U, p)` is defined on `cl_𝒫(U)` and is neither local nor
stationary (Section 4.1, after Definition 4.1); on resolved cubes `cl_𝒫(U) = U` and the definition
used here is both. These are the forms of their Proposition 4.9 and (4.40) that we use for `ν`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Transport of `ν` along a bijection of clusters** (one inequality). -/
theorem cubeNu_le_of_equiv {ω ω' : Configuration d} {U U' : TriadicCube d} (p : Fin d → ℝ)
    (e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U'))
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hint : ∀ x, U'.IsLatticeInterior (e x).1 ↔ U.IsLatticeInterior x.1)
    (hflux : ∀ x y, ∑ i, p i * (((e y).1 i : ℝ) - (e x).1 i) =
      ∑ i, p i * ((y.1 i : ℝ) - x.1 i))
    (hvol : U'.latticeVolume = U.latticeVolume) :
    cubeNu ω U p ≤ cubeNu ω' U' p := by
  obtain ⟨v, hv, -, hν⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) p
  obtain ⟨g, hg⟩ : ∃ g : CubeFun ω' U', g = fun y => v (e.symm y) := ⟨_, rfl⟩
  have hge : ∀ x, g (e x) = v x := fun x => by simp [hg]
  have hB : cubeForm ω' U' g g = cubeForm ω U v v := by
    rw [cubeForm_apply, cubeForm_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [cubeFormTerm, hge, hadj]
  have hF : cubeFluxPairing ω' U' p g = cubeFluxPairing ω U p v := by
    rw [cubeFluxPairing_apply, cubeFluxPairing_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hge, hadj, hflux]
  have hgA : g ∈ cubeHarmonic ω' U' := by
    rw [mem_cubeHarmonic]
    intro y' hy'
    obtain ⟨x, rfl⟩ := e.surjective y'
    rw [hint] at hy'
    have h0 := mem_cubeHarmonic.1 hv x hy'
    rw [cubeLaplacianAt_apply] at h0 ⊢
    rw [← e.sum_comp]
    simp only [hge, hadj]
    exact h0
  have h := le_cubeNu (ω := ω') (U := U') p hgA
  rw [hF, hB, hvol, ← hν] at h
  exact h

/-- **Transport of `ν` along a bijection of clusters.** -/
theorem cubeNu_eq_of_equiv {ω ω' : Configuration d} {U U' : TriadicCube d} (p : Fin d → ℝ)
    (e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U'))
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hint : ∀ x, U'.IsLatticeInterior (e x).1 ↔ U.IsLatticeInterior x.1)
    (hflux : ∀ x y, ∑ i, p i * (((e y).1 i : ℝ) - (e x).1 i) =
      ∑ i, p i * ((y.1 i : ℝ) - x.1 i))
    (hvol : U'.latticeVolume = U.latticeVolume) :
    cubeNu ω U p = cubeNu ω' U' p := by
  refine le_antisymm (cubeNu_le_of_equiv p e hadj hint hflux hvol)
    (cubeNu_le_of_equiv p e.symm (fun x' y' => ?_) (fun x' => ?_) (fun x' y' => ?_) hvol.symm)
  · rw [← hadj, e.apply_symm_apply, e.apply_symm_apply]
  · rw [← hint, e.apply_symm_apply]
  · rw [← hflux, e.apply_symm_apply, e.apply_symm_apply]

/-- The crossing cluster of a cube depends only on the open edges inside the cube. -/
theorem TriadicCube.crossingCluster_eq_of_adj_iff {ω ω' : Configuration d} {U : TriadicCube d}
    (h : ∀ x ∈ U.vertices, ∀ y ∈ U.vertices, (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y) :
    U.crossingCluster ω = U.crossingCluster ω' := by
  have hG : openIn ω U.vertices = openIn ω' U.vertices := by
    ext x y
    change (openGraph ω).Adj x y ∧ x ∈ U.vertices ∧ y ∈ U.vertices ↔
      (openGraph ω').Adj x y ∧ x ∈ U.vertices ∧ y ∈ U.vertices
    constructor
    · rintro ⟨hxy, hx, hy⟩
      exact ⟨(h x hx y hy).1 hxy, hx, hy⟩
    · rintro ⟨hxy, hx, hy⟩
      exact ⟨(h x hx y hy).2 hxy, hx, hy⟩
  simp only [TriadicCube.crossingCluster, IsCrossingRoot, hG]

/-- **Locality of `ν`.** `ν(U, p)` depends only on the open edges with both endpoints in `U`. -/
theorem cubeNu_eq_of_adj_iff {ω ω' : Configuration d} {U : TriadicCube d} (p : Fin d → ℝ)
    (h : ∀ x ∈ U.vertices, ∀ y ∈ U.vertices, (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y) :
    cubeNu ω U p = cubeNu ω' U p := by
  have hC : ∀ x, x ∈ crossingClusterVertices ω U ↔ x ∈ crossingClusterVertices ω' U := by
    intro x
    rw [mem_crossingClusterVertices, mem_crossingClusterVertices,
      TriadicCube.crossingCluster_eq_of_adj_iff h]
  refine cubeNu_eq_of_equiv p (Equiv.subtypeEquivRight hC) (fun x y => ?_) (fun x => Iff.rfl)
    (fun x y => rfl) rfl
  exact (h x.1 (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 x.2)) y.1
    (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 y.2))).symm

/-- A function constant on the fibres of a map to a countable type with measurable fibres is
measurable. -/
theorem measurable_of_constant_on_fibres {Ω β T : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [Countable T] (φ : Ω → T) (hφ : ∀ t, MeasurableSet (φ ⁻¹' {t})) {g : Ω → β}
    (hg : ∀ ω ω', φ ω = φ ω' → g ω = g ω') : Measurable g := by
  intro s _
  have heq : g ⁻¹' s = ⋃ t ∈ φ '' (g ⁻¹' s), φ ⁻¹' {t} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · intro h
      exact ⟨φ ω, ⟨ω, h, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨ω', h', rfl⟩, h⟩
      rw [hg ω ω' h]
      exact h'
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable _) fun t _ => hφ t

/-- **Measurability of `ν`.** -/
theorem measurable_cubeNu (U : TriadicCube d) (p : Fin d → ℝ) :
    Measurable fun ω : Configuration d => cubeNu ω U p := by
  set S := U.toIntegerCube.vertices ×ˢ U.toIntegerCube.vertices
  refine measurable_of_constant_on_fibres
    (fun ω : Configuration d => S.filter fun e => (openGraph ω).Adj e.1 e.2) (fun C => ?_) ?_
  · have heq : (fun ω : Configuration d => S.filter fun e => (openGraph ω).Adj e.1 e.2) ⁻¹' {C} =
        {ω | ∀ e : Vertex d × Vertex d, (e ∈ S ∧ (openGraph ω).Adj e.1 e.2) ↔ e ∈ C} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, Finset.ext_iff,
        Finset.mem_filter]
    rw [heq]
    exact measurableSet_setOf.2 (Measurable.forall fun e =>
      (measurable_const.and (measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2))).iff
        measurable_const)
  · intro ω ω' hφ
    refine cubeNu_eq_of_adj_iff p fun x hx y hy => ?_
    have hxy : (x, y) ∈ S := Finset.mem_product.2
      ⟨(U.mem_toIntegerCube_vertices x).2 hx, (U.mem_toIntegerCube_vertices y).2 hy⟩
    have h := congrArg (fun F : Finset (Vertex d × Vertex d) => (x, y) ∈ F) hφ
    simp only [Finset.mem_filter, hxy, true_and, eq_iff_iff] at h
    exact h

/-- Lattice adjacency is invariant under translations. -/
theorem nearestNeighborGraph_adj_add_iff (c x y : Vertex d) :
    (nearestNeighborGraph d).Adj (x + c) (y + c) ↔ (nearestNeighborGraph d).Adj x y := by
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inl (add_right_cancel (h.trans (by abel)))⟩
    · exact ⟨i, Or.inr (add_right_cancel (h.trans (by abel)))⟩
  · rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inl (by rw [h]; abel)⟩
    · exact ⟨i, Or.inr (by rw [h]; abel)⟩

/-- The lattice interior of a translated cube is the translate of the lattice interior. -/
theorem TriadicCube.isLatticeInterior_shift_iff {U : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, U.side ∣ c i) (x : Vertex d) :
    (U.shift c).IsLatticeInterior (x + c) ↔ U.IsLatticeInterior x := by
  constructor
  · intro h y hxy
    have := h (y + c) ((nearestNeighborGraph_adj_add_iff c x y).2 hxy)
    exact (TriadicCube.add_mem_shift_iff hc y).1 this
  · intro h y hxy
    have hy : y = (y - c) + c := (sub_add_cancel y c).symm
    rw [hy] at hxy ⊢
    exact (TriadicCube.add_mem_shift_iff hc _).2 (h _ ((nearestNeighborGraph_adj_add_iff c x _).1
      hxy))

/-- Translation of the clusters of a cube and of its translate. -/
noncomputable def crossingClusterVerticesShiftEquiv (ω : Configuration d) {U : TriadicCube d}
    {c : Vertex d} (hc : ∀ i, U.side ∣ c i) :
    ↥(crossingClusterVertices ω U) ≃
      ↥(crossingClusterVertices (configurationTranslation c ω) (U.shift c)) where
  toFun x := ⟨x.1 + c, mem_crossingClusterVertices.2
    ((TriadicCube.add_mem_crossingCluster_shift_iff hc ω x.1).2
      (mem_crossingClusterVertices.1 x.2))⟩
  invFun y := ⟨y.1 - c, mem_crossingClusterVertices.2
    ((TriadicCube.add_mem_crossingCluster_shift_iff hc ω (y.1 - c)).1
      (by rw [sub_add_cancel]; exact mem_crossingClusterVertices.1 y.2))⟩
  left_inv x := Subtype.ext (add_sub_cancel_right x.1 c)
  right_inv y := Subtype.ext (sub_add_cancel y.1 c)

/-- **Translation covariance of `ν`.** For `c ∈ size(U) ℤ^d`, `ν(U + c, p)` at the configuration
translated by `c` equals `ν(U, p)`. -/
theorem cubeNu_shift (ω : Configuration d) {U : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, U.side ∣ c i) (p : Fin d → ℝ) :
    cubeNu (configurationTranslation c ω) (U.shift c) p = cubeNu ω U p := by
  refine (cubeNu_eq_of_equiv p (crossingClusterVerticesShiftEquiv ω hc) (fun x y => ?_)
    (fun x => ?_) (fun x y => ?_) ?_).symm
  · exact openGraph_adj_translation_iff c ω x.1 y.1
  · exact TriadicCube.isLatticeInterior_shift_iff hc x.1
  · refine Finset.sum_congr rfl fun i _ => ?_
    change p i * (((y.1 + c) i : ℝ) - ((x.1 + c) i : ℝ)) = _
    simp only [Pi.add_apply, Int.cast_add]
    ring
  · rfl

/-- **Stationarity of the expectation of `ν`.** -/
theorem integral_cubeNu_shift (prob : unitInterval) {U : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, U.side ∣ c i) (p : Fin d → ℝ) :
    ∫ ω, cubeNu ω (U.shift c) p ∂(latticeBondLaw d prob) =
      ∫ ω, cubeNu ω U p ∂(latticeBondLaw d prob) := by
  have hmp := measurePreserving_configurationTranslation prob c
  have hemb : MeasurableEmbedding (configurationTranslation c : Configuration d →
      Configuration d) := (configurationTranslationMeasurableEquiv c).measurableEmbedding
  rw [← hmp.integral_comp hemb]
  exact integral_congr_ae (ae_of_all _ fun ω => cubeNu_shift ω hc p)

/-- Two triadic cubes of the same scale differ by a translation by a multiple of their side. -/
theorem TriadicCube.shift_index_sub_eq {U U' : TriadicCube d} (h : U.scale = U'.scale) :
    U.shift (fun i => U.side * (U'.index i - U.index i)) = U' := by
  apply TriadicCube.ext
  · rw [TriadicCube.scale_shift, h]
  · funext i
    change U.index i + U.side * (U'.index i - U.index i) / U.side = U'.index i
    rw [Int.mul_ediv_cancel_left _ U.side_pos.ne']
    ring

/-- **The expectation of `ν` is the same on all triadic cubes of a given scale.** -/
theorem integral_cubeNu_eq_of_scale_eq (prob : unitInterval) {U U' : TriadicCube d}
    (h : U.scale = U'.scale) (p : Fin d → ℝ) :
    ∫ ω, cubeNu ω U' p ∂(latticeBondLaw d prob) = ∫ ω, cubeNu ω U p ∂(latticeBondLaw d prob) := by
  rw [← TriadicCube.shift_index_sub_eq h]
  exact integral_cubeNu_shift prob (fun i => dvd_mul_right _ _) p

/-- `ν(U, p)` is integrable under the bond law. -/
theorem integrable_cubeNu (prob : unitInterval) (U : TriadicCube d) (p : Fin d → ℝ) :
    Integrable (fun ω => cubeNu ω U p) (latticeBondLaw d prob) := by
  refine (integrable_const (3 ^ d / 4 * (∑ i, |p i|) ^ 2)).mono'
    (measurable_cubeNu U p).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (cubeNu_nonneg p)]
  exact cubeNu_le p

end Rigidity.Percolation

import Rigidity.Proofs.S3.SlopeSetMeasurable
import PercolationClusterHomogenization.Proofs.Lattice.Reflection

/-!
# Lemma 3.1: the dihedral symmetry of the lattice and of the corrected planes

Step `step:3.1-reflection` of Lemma 3.1 (paper L841-859 of the corrected draft).

* An automorphism `φ` of the nearest-neighbor graph of `ℤ^d` permutes the bonds, hence acts on
  the configurations by permuting coordinates; this action preserves the product Bernoulli law
  (`Measure.infinitePi_map_piCongrLeft`), and `φ` is a graph isomorphism from the open graph of
  `ω` onto the open graph of the transported configuration. It therefore transports the open
  components, their infinitude, the unique infinite cluster, the Laplacian and the Lipschitz
  bounds for the graph distance.
* The signed permutations `x ↦ (sᵢ x_{π i})ᵢ` of the coordinates are such automorphisms; they
  are Euclidean isometries fixing the origin and transport the affine function `x ↦ q · x` to
  `x ↦ q' · x` with `q'ᵢ = sᵢ q_{π i}`. Hence they transport corrected planes of slope `q` to
  corrected planes of slope `q'`, and the set of `L`-Lipschitz slopes covariantly.
* The reflections `T_j` and the coordinate transpositions are signed permutations; since the law
  is invariant, a slope which is almost surely `L`-Lipschitz has almost surely `L`-Lipschitz
  images.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

section Automorphism

variable (φ : nearestNeighborGraph d ≃g nearestNeighborGraph d)

/-- The open components are transported by a lattice automorphism. -/
def openComponentMap (ω : Configuration d) :
    OpenComponent ω ≃ OpenComponent (configurationMap φ ω) :=
  (openGraphMap φ ω).connectedComponentEquiv

/-- The restriction of a lattice automorphism to an open component and its image. -/
def openComponentMapIso {ω : Configuration d} (C : OpenComponent ω) :
    componentGraph C ≃g componentGraph (openComponentMap φ ω C) where
  toEquiv := SimpleGraph.ConnectedComponent.isoEquivSupp (openGraphMap φ ω) C
  map_rel_iff' := (openGraphMap φ ω).map_rel_iff

/-- The component isomorphism is the lattice automorphism on vertices. -/
theorem openComponentMapIso_val {ω : Configuration d} (C : OpenComponent ω) (x : C) :
    (openComponentMapIso φ C x).val = φ x.val := rfl

/-- Infinitude of open components is preserved and reflected. -/
theorem openComponentMap_infinite_iff {ω : Configuration d} (C : OpenComponent ω) :
    (openComponentMap φ ω C).supp.Infinite ↔ C.supp.Infinite := by
  rw [← Set.infinite_coe_iff, ← Set.infinite_coe_iff]
  exact (SimpleGraph.ConnectedComponent.isoEquivSupp (openGraphMap φ ω) C).infinite_iff.symm

/-- Existence and uniqueness of an infinite open component is invariant under lattice
automorphisms. -/
theorem hasUniqueInfiniteOpenComponent_configurationMap_iff (ω : Configuration d) :
    HasUniqueInfiniteOpenComponent (configurationMap φ ω) ↔
      HasUniqueInfiniteOpenComponent ω :=
  ((openComponentMap φ ω).existsUnique_congr
    (fun C => (openComponentMap_infinite_iff φ C).symm)).symm

/-- The unique infinite cluster is carried to the unique infinite cluster. -/
theorem openComponentMap_uniqueInfiniteComponent {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) :
    openComponentMap φ ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent ((hasUniqueInfiniteOpenComponent_configurationMap_iff φ ω).mpr h) :=
  (eq_uniqueInfiniteComponent_iff _ _).mpr
    ((openComponentMap_infinite_iff φ _).mpr (uniqueInfiniteComponent_infinite h))

end Automorphism

section Iso

variable {ω ω' : Configuration d} {C : OpenComponent ω} {D : OpenComponent ω'}

/-- The Laplacian commutes with the pullback by a graph isomorphism of components. -/
theorem componentLaplacian_comp_iso (e : componentGraph C ≃g componentGraph D) (v : D → ℝ)
    (x : C) : componentLaplacian C (fun y => v (e y)) x = componentLaplacian D v (e x) := by
  classical
  unfold componentLaplacian
  apply Finset.sum_bij (fun y _ => e y)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact e.map_rel_iff.mpr hy
  · intro y _ y' _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact e.map_rel_iff.mp (by simpa only [e.apply_symm_apply] using hy)
  · intro y _
    rfl

/-- Lipschitz bounds are pulled back by graph isomorphisms of components. -/
theorem isLipschitzWith_comp_iso (e : componentGraph C ≃g componentGraph D) (L : ℝ)
    (v : D → ℝ) : IsLipschitzWith C L (fun x => v (e x)) ↔ IsLipschitzWith D L v := by
  have hv : (fun y => (fun x => v (e x)) (e.symm y)) = v :=
    funext fun y => congrArg v (e.apply_symm_apply y)
  rw [← isLipschitzWith_iso e L, hv]

end Iso

section SignedPermutation

variable (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)

/-- Signed permutations are Euclidean isometries. -/
theorem dist_signedPermIso (x y : Vertex d) :
    dist (latticeEuclideanEmbedding (signedPermIso π s x))
      (latticeEuclideanEmbedding (signedPermIso π s y)) =
      dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) := by
  have hs (i : Fin d) (a b : ℤ) : |(((s i : ℤ) * a : ℤ) : ℝ) - (((s i : ℤ) * b : ℤ) : ℝ)| =
      |(a : ℝ) - (b : ℝ)| := by
    push_cast
    rw [← mul_sub, abs_mul, ← Int.cast_abs, abs_units_int, Int.cast_one, one_mul]
  simp only [EuclideanSpace.dist_eq, Real.dist_eq, latticeEuclideanEmbedding,
    Function.Embedding.coeFn_mk]
  congr 1
  change ∑ i, |(((s i : ℤ) * x (π i) : ℤ) : ℝ) - (((s i : ℤ) * y (π i) : ℤ) : ℝ)| ^ 2 = _
  simp only [hs]
  exact Equiv.sum_comp π (fun i => |(x i : ℝ) - (y i : ℝ)| ^ 2)

variable {ω : Configuration d}

/-- Corrected planes are pulled back along signed permutations: if `v` is a corrected plane of
slope `q'ᵢ = sᵢ q_{π i}` on the image of `C`, then `v ∘ φ` is a corrected plane of slope `q`
on `C`. -/
theorem isCorrectedPlane_comp_signedPerm (C : OpenComponent ω) (q : Fin d → ℝ)
    (v : openComponentMap (signedPermIso π s) ω C → ℝ)
    (hv : IsCorrectedPlane (openComponentMap (signedPermIso π s) ω C) (signedPermSlope π s q) v) :
    IsCorrectedPlane C q (fun x => v (openComponentMapIso (signedPermIso π s) C x)) := by
  let e := openComponentMapIso (signedPermIso π s) C
  rw [isCorrectedPlane_iff_harmonic_and_slope_asymptotics] at hv ⊢
  refine ⟨fun x => (componentLaplacian_comp_iso e v x).trans (hv.1 (e x)), ?_⟩
  intro ε hε
  obtain ⟨R₀, hR₀, htail⟩ := hv.2 ε hε
  refine ⟨R₀, hR₀, fun R hR x hx => ?_⟩
  have hx' : e x ∈ componentEuclideanBall _ 0 R := by
    rw [mem_componentEuclideanBall] at hx ⊢
    rw [openComponentMapIso_val, ← signedPermIso_zero π s, dist_signedPermIso]
    exact hx
  have hslope : componentSlope _ (signedPermSlope π s q) (e x) = componentSlope C q x :=
    sum_signedPermSlope_mul π s q x.val
  have := htail R hR (e x) hx'
  rwa [hslope] at this

/-- If every corrected plane of slope `q` on `C` is `L`-Lipschitz, so is every corrected plane
of slope `q'` on the image of `C`. -/
theorem forall_correctedPlane_isLipschitzWith_signedPerm (C : OpenComponent ω)
    (q : Fin d → ℝ) (L : ℝ) (h : ∀ u : C → ℝ, IsCorrectedPlane C q u → IsLipschitzWith C L u) :
    ∀ v : openComponentMap (signedPermIso π s) ω C → ℝ,
      IsCorrectedPlane (openComponentMap (signedPermIso π s) ω C) (signedPermSlope π s q) v →
        IsLipschitzWith (openComponentMap (signedPermIso π s) ω C) L v := fun v hv =>
  (isLipschitzWith_comp_iso (openComponentMapIso (signedPermIso π s) C) L v).mp
    (h _ (isCorrectedPlane_comp_signedPerm π s C q v hv))

/-- The set of `L`-Lipschitz slopes is covariant under signed permutations. -/
theorem signedPermSlope_mem_lipschitzSlopeSet (L : ℝ) {q : Fin d → ℝ}
    (hq : q ∈ lipschitzSlopeSet ω L) :
    signedPermSlope π s q ∈ lipschitzSlopeSet (configurationMap (signedPermIso π s) ω) L := by
  obtain ⟨h, hq⟩ := hq
  refine ⟨(hasUniqueInfiniteOpenComponent_configurationMap_iff _ ω).mpr h, ?_⟩
  have hv := forall_correctedPlane_isLipschitzWith_signedPerm π s _ q L hq
  rw [openComponentMap_uniqueInfiniteComponent] at hv
  exact hv

/-- A slope which is almost surely `L`-Lipschitz has an almost surely `L`-Lipschitz image under
every signed permutation. -/
theorem ae_signedPermSlope_mem_lipschitzSlopeSet (p : unitInterval) (L : ℝ) {q : Fin d → ℝ}
    (hq : ∀ᵐ ω ∂latticeBondLaw d p, q ∈ lipschitzSlopeSet ω L) :
    ∀ᵐ ω ∂latticeBondLaw d p, signedPermSlope π s q ∈ lipschitzSlopeSet ω L := by
  let Φ := configurationMap (signedPermIso π s)
  have hsymm := (measurePreserving_configurationMap (signedPermIso π s) p).symm Φ
  have hq' : ∀ᵐ ω ∂latticeBondLaw d p, q ∈ lipschitzSlopeSet (Φ.symm ω) L :=
    ae_of_ae_map hsymm.measurable.aemeasurable (by rw [hsymm.map_eq]; exact hq)
  filter_upwards [hq'] with ω hω
  simpa only [Φ, MeasurableEquiv.apply_symm_apply] using
    signedPermSlope_mem_lipschitzSlopeSet π s L hω

end SignedPermutation

/-- The reflection `T_j` of slopes is the signed permutation with the sign `-1` at `j`. -/
theorem reflectSlope_eq_signedPermSlope (j : Fin d) (q : Fin d → ℝ) :
    reflectSlope j q = signedPermSlope (Equiv.refl _) (Function.update 1 j (-1)) q := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [reflectSlope, signedPermSlope]
  · simp [reflectSlope, signedPermSlope, Function.update_of_ne hij]

/-- A coordinate transposition of slopes is the signed permutation with all signs `1`. -/
theorem comp_swap_eq_signedPermSlope (i j : Fin d) (q : Fin d → ℝ) :
    q ∘ Equiv.swap i j = signedPermSlope (Equiv.swap i j) 1 q := by
  funext k
  simp [signedPermSlope]

/-- Step `step:3.1-reflection`: by the invariance of the bond law under the reflections `T_j`
and the coordinate transpositions of `ℤ^d`, and the covariance of the corrected planes and of
their Lipschitz bounds, an almost surely `L`-Lipschitz slope has almost surely `L`-Lipschitz
reflected and transposed images. -/
theorem reflectionStep [NeZero d] (p : unitInterval) : ReflectionStep d p := by
  intro L q hq
  refine ⟨fun j => ?_, fun i j => ?_⟩
  · rw [reflectSlope_eq_signedPermSlope]
    exact ae_signedPermSlope_mem_lipschitzSlopeSet _ _ p L hq
  · rw [comp_swap_eq_signedPermSlope]
    exact ae_signedPermSlope_mem_lipschitzSlopeSet _ _ p L hq

end Rigidity.Proofs.S3

import Rigidity.Percolation.Bootstrap.TwoChances
import Rigidity.Percolation.BondMarkSymmetry
import Rigidity.Percolation.VertexCutSymmetry
import Rigidity.Percolation.SignedCoordinateSymmetry

/-!
# Transport of the bootstrap events by lattice symmetries

Translations and coordinate reflections move every coordinate difference by at most a sign. They
carry cubes and their shells to cubes and shells, seed paths to seed paths, closed cuts to closed
cuts and connections between regions to connections between the image regions, and they preserve
the law of the uniform marks and the Bernoulli bond law.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

variable {d : ℕ}

/-- A vertex bijection preserving the absolute value of every coordinate difference. -/
def CoordIsometry (f : Vertex d ≃ Vertex d) : Prop :=
  ∀ x y : Vertex d, ∀ i, |f x i - f y i| = |x i - y i|

namespace CoordIsometry

variable {f : Vertex d ≃ Vertex d}

/-- A coordinate isometry preserves lattice distance. -/
theorem dist (hf : CoordIsometry f) :
    ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y := by
  intro x y
  unfold latticeL1Dist
  exact Finset.sum_congr rfl fun i _ => hf x y i

/-- The inverse of a coordinate isometry is a coordinate isometry. -/
theorem symm (hf : CoordIsometry f) : CoordIsometry f.symm := by
  intro x y i
  have := hf (f.symm x) (f.symm y) i
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

/-- A coordinate isometry carries cubes onto cubes. -/
theorem image_cubeAt (hf : CoordIsometry f) (s : Vertex d) (u : ℕ) :
    f '' cubeAt s u = cubeAt (f s) u := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    rw [hf x s i]
    exact hx i
  · intro hy
    refine ⟨f.symm y, fun i => ?_, f.apply_symm_apply y⟩
    have := hf (f.symm y) s i
    rw [f.apply_symm_apply] at this
    rw [← this]
    exact hy i

/-- A coordinate isometry carries shells onto shells. -/
theorem image_cubeShell (hf : CoordIsometry f) (s : Vertex d) (u : ℕ) :
    f '' cubeShell s u = cubeShell (f s) u := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, i, hi⟩, rfl⟩
    refine ⟨fun j => ?_, i, ?_⟩
    · rw [hf x s j]
      exact hx j
    · rw [hf x s i]
      exact hi
  · rintro ⟨hy, i, hi⟩
    have key : ∀ j, |f.symm y j - s j| = |y j - f s j| := by
      intro j
      have := hf (f.symm y) s j
      rw [f.apply_symm_apply] at this
      exact this.symm
    refine ⟨f.symm y, ⟨fun j => ?_, i, ?_⟩, f.apply_symm_apply y⟩
    · rw [key j]
      exact hy j
    · rw [key i]
      exact hi

end CoordIsometry

/-- Translations are coordinate isometries. -/
theorem coordIsometry_translateEquiv (c : Vertex d) : CoordIsometry (translateEquiv c) := by
  intro x y i
  simp [translateEquiv, latticeVertexTranslation]

/-- Coordinate sign reversals are coordinate isometries. -/
theorem coordIsometry_coordinateSignFlip (s : Fin d → Bool) :
    CoordIsometry (coordinateSignFlip s) := by
  intro x y i
  change |(if s i then -(x i) else x i) - (if s i then -(y i) else y i)| = |x i - y i|
  split_ifs
  · rw [← abs_neg]
    ring_nf
  · rfl

/-- A lattice symmetry fixes the configuration with all bonds open. -/
theorem latticeConfigurationEquiv_allOpen (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) :
    latticeConfigurationEquiv f hf (allOpen d) = allOpen d := by
  funext e
  obtain ⟨a, rfl⟩ := (latticeBondEquiv f hf).surjective e
  rw [latticeConfigurationEquiv_apply_bond]
  rfl

/-- A coordinate isometry carries seed paths to seed paths. -/
theorem HasSeedPath.image {f : Vertex d ≃ Vertex d} (hf : CoordIsometry f) {S : Set (Vertex d)}
    {s : Vertex d} {u : ℕ} (h : HasSeedPath S s u) : HasSeedPath (f '' S) (f s) u := by
  obtain ⟨hs, v, hv, hr⟩ := h
  refine ⟨⟨s, hs, rfl⟩, f v, hf.image_cubeShell s u ▸ ⟨v, hv, rfl⟩, ?_⟩
  have h' := (openIn_reachable_latticeConfigurationEquiv_iff f hf.dist (allOpen d)
    (S ∩ cubeAt s u) s v).2 hr
  rw [latticeConfigurationEquiv_allOpen, Set.image_inter f.injective, hf.image_cubeAt] at h'
  exact h'

/-- A lattice symmetry carries connections between regions to connections between their
images. -/
theorem connectsRegions_latticeConfigurationEquiv_iff (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (η : Configuration d)
    (B L R : Set (Vertex d)) :
    ConnectsRegions (latticeConfigurationEquiv f hf η) (f '' B) (f '' L) (f '' R) ↔
      ConnectsRegions η B L R := by
  have hinj := f.injective
  constructor
  · rintro ⟨x', ⟨x, hxB, rfl⟩, hxL, y', ⟨y, hyB, rfl⟩, hyR, h⟩
    exact ⟨x, hxB, hinj.mem_set_image.1 hxL, y, hyB, hinj.mem_set_image.1 hyR,
      (openIn_reachable_latticeConfigurationEquiv_iff f hf η B x y).1 h⟩
  · rintro ⟨x, hxB, hxL, y, hyB, hyR, h⟩
    exact ⟨_, ⟨x, hxB, rfl⟩, ⟨x, hxL, rfl⟩, _, ⟨y, hyB, rfl⟩, ⟨y, hyR, rfl⟩,
      (openIn_reachable_latticeConfigurationEquiv_iff f hf η B x y).2 h⟩

/-- A lattice symmetry preserves the Bernoulli probability of a connection between regions. -/
theorem latticeBondLaw_real_connectsRegions_image (p : unitInterval) (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (B L R : Set (Vertex d)) :
    (latticeBondLaw d p).real {η | ConnectsRegions η (f '' B) (f '' L) (f '' R)} =
      (latticeBondLaw d p).real {η | ConnectsRegions η B L R} := by
  have h := latticeBondLaw_preimage_latticeConfigurationEquiv p f hf
    {η | ConnectsRegions η (f '' B) (f '' L) (f '' R)}
  have hpre : latticeConfigurationEquiv f hf ⁻¹'
      {η | ConnectsRegions η (f '' B) (f '' L) (f '' R)} = {η | ConnectsRegions η B L R} := by
    ext η
    exact connectsRegions_latticeConfigurationEquiv_iff f hf η B L R
  rw [hpre] at h
  rw [measureReal_def, measureReal_def, h]

/-- A lattice symmetry preserves the law of the marks. -/
theorem bondMarkLaw_real_preimage_latticeBondMarkEquiv (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (E : Set (BondMarks d)) :
    (bondMarkLaw d).real (latticeBondMarkEquiv f hf ⁻¹' E) = (bondMarkLaw d).real E := by
  have hmp : MeasurePreserving (latticeBondMarkEquiv f hf) (bondMarkLaw d) (bondMarkLaw d) :=
    ⟨(latticeBondMarkEquiv f hf).measurable, bondMarkLaw_map_latticeBondMarkEquiv f hf⟩
  rw [measureReal_def, measureReal_def, hmp.measure_preimage_equiv E]

/-- Closed cuts are carried to closed cuts of the image sets. -/
theorem latticeBondMarkEquiv_preimage_cutClosed (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (p : unitInterval)
    (S Z : Finset (Vertex d)) :
    latticeBondMarkEquiv f hf ⁻¹' cutClosed p (S.image f) (Z.image f) = cutClosed p S Z := by
  classical
  have hcut : vertexCutBondsIn (S.image f) ((Z.image f : Finset (Vertex d)) : Set (Vertex d)) =
      (vertexCutBondsIn S (Z : Set (Vertex d))).image (latticeBondEquiv f hf) := by
    rw [image_vertexCutBondsIn_latticeEquiv f hf S (Z : Set (Vertex d)), Finset.coe_image]
  ext ω
  simp only [Set.mem_preimage, cutClosed, bondMarksAbove, Set.mem_setOf_eq, hcut,
    constThreshold]
  constructor
  · intro h e he
    have := h _ (Finset.mem_image_of_mem _ he)
    rwa [latticeBondMarkEquiv_apply_bond] at this
  · intro h e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    rw [latticeBondMarkEquiv_apply_bond]
    exact h e' he'

/-- Connections at a level are carried to connections between the image regions. -/
theorem latticeBondMarkEquiv_preimage_connectsRegions (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (q : unitInterval)
    (B L R : Set (Vertex d)) :
    latticeBondMarkEquiv f hf ⁻¹'
        {ω | ConnectsRegions (thresholdBondMarks q ω) (f '' B) (f '' L) (f '' R)} =
      {ω | ConnectsRegions (thresholdBondMarks q ω) B L R} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, thresholdBondMarks_latticeBondMarkEquiv]
  exact connectsRegions_latticeConfigurationEquiv_iff f hf _ B L R

end Rigidity.Percolation

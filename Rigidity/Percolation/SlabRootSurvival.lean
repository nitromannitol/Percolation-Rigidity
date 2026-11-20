import Rigidity.Percolation.SlabPrefixSurvival

/-!
# Crossing components from slab exploration

A component with a past-measurable boundary candidate has a conditional
chance of attaching to a crossing component in the next fresh slab.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped MeasureTheory

/-- A component with a boundary candidate joins a crossing component in the
next region with conditional probability at least `p * δ`. -/
theorem condExp_crossingRoot_lower_of_boundary_candidate {d : ℕ}
    (p : unitInterval) (P S D : Set (Vertex d))
    (hP : P.Finite) (hS : S.Finite) (hPS : Disjoint P S)
    (hPD : P ⊆ D) (hSD : S ⊆ D) (z : Vertex d) (hz : z ∈ P)
    (lower upper : Fin d → Set (Vertex d)) (δ : ℝ)
    (hprob : ∀ y ∈ S, δ ≤ (latticeBondLaw d p).real
      {ω | IsCrossingRoot ω S lower upper y}) :
    ∀ᵐ ω ∂(latticeBondLaw d p).restrict {ω | slabBoundaryReachable P S z ω},
      (p : ℝ) * δ ≤ (latticeBondLaw d p)[
        ({ω | IsCrossingRoot ω D lower upper z} : Set (Configuration d)).indicator
          (fun _ => (1 : ℝ)) | bondSigma (localBonds P)] ω := by
  let I := {pair : Vertex d × Vertex d //
    pair.1 ∈ P ∧ pair.2 ∈ S ∧ (nearestNeighborGraph d).Adj pair.1 pair.2}
  let x : I → Vertex d := fun i => i.val.1
  let y : I → Vertex d := fun i => i.val.2
  have hx : ∀ i, x i ∈ P := fun i => i.property.1
  have hy : ∀ i, y i ∈ S := fun i => i.property.2.1
  have hxy : ∀ i, (nearestNeighborGraph d).Adj (x i) (y i) := fun i => i.property.2.2
  apply ae_restrict_of_ae_restrict_of_subset (t := ⋃ i : I,
    {ω | (openIn ω P).Reachable z (x i)})
  · rintro ω ⟨a, ha, b, hb, hab, hza⟩
    exact Set.mem_iUnion.mpr ⟨⟨(a, b), ha, hb, hab⟩, hza⟩
  · exact condExp_crossingRoot_lower_of_slab_attachments p P S D hP hS hPS hPD hSD
      z hz x y hx hy hxy lower upper δ (fun i => hprob (y i) (hy i))

/-- The root reaches the next slab while its explored component has not yet
crossed all marked faces. -/
def IntegerCube.slabRootSurvival {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    (width k : ℕ) (z : Vertex d) (lower upper : Fin d → Set (Vertex d)) :
    Set (Configuration d) :=
  {ω | slabBoundaryReachable (Q.slabPrefix j width k) (Q.slab j width k) z ω ∧
    ¬ IsCrossingRoot ω (Q.slabPrefix j width k) lower upper z}

/-- Root survival depends only on bonds in the explored prefix. -/
theorem IntegerCube.measurableSet_slabRootSurvival {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k : ℕ) {z : Vertex d} (hz : z ∈ Q.slabPrefix j width k)
    (lower upper : Fin d → Set (Vertex d)) :
    MeasurableSet[bondSigma (localBonds (Q.slabPrefix j width k))]
      (Q.slabRootSurvival j width k z lower upper) := by
  exact (measurableSet_slabBoundaryReachable_bondSigma _ _
    (Q.finite_slabPrefix j width k) hz).inter
    (measurableSet_isCrossingRoot_bondSigma _ lower upper
      (Q.finite_slabPrefix j width k) hz).compl

/-- Root survival decreases as the explored prefix grows. -/
theorem IntegerCube.slabRootSurvival_succ_subset {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {width k : ℕ} (hwidth : 0 < width) (hsize : k * width < Q.size)
    {z : Vertex d} (hz : z ∈ Q.slabPrefix j width k)
    (lower upper : Fin d → Set (Vertex d)) :
    Q.slabRootSurvival j width (k + 1) z lower upper ⊆
      Q.slabRootSurvival j width k z lower upper := by
  intro ω h
  refine ⟨Q.slabBoundaryReachable_of_next j hwidth hsize hz h.1, ?_⟩
  intro hroot
  have hmono := Q.slabPrefix_mono j width (Nat.le_succ k)
  exact h.2 (hroot.of_reachable_in_larger_region hmono (hmono hz)
    (SimpleGraph.Reachable.refl z))

/-- A uniform rooted crossing bound in each fresh slab gives geometric decay
for the root's failure to cross the marked faces. -/
theorem IntegerCube.measureReal_slabRootSurvival_le {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hsize : ∀ n < N, (k₀ + n) * width < Q.size)
    (z : Vertex d) (hz : z ∈ Q.slabPrefix j width k₀)
    (lower upper : Fin d → Set (Vertex d)) (p : unitInterval) (δ : ℝ) (hδ : δ ≤ 1)
    (hprob : ∀ n < N, ∀ y ∈ Q.slab j width (k₀ + n), δ ≤ (latticeBondLaw d p).real
      {ω | IsCrossingRoot ω (Q.slab j width (k₀ + n)) lower upper y}) :
    ∀ n ≤ N, (latticeBondLaw d p).real
      (Q.slabRootSurvival j width (k₀ + n) z lower upper) ≤ (1 - (p : ℝ) * δ) ^ n := by
  have hpδ : (p : ℝ) * δ ≤ 1 := by
    calc
      (p : ℝ) * δ ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hδ p.property.1
      _ ≤ 1 := by simpa using p.property.2
  have hq : 0 ≤ 1 - (p : ℝ) * δ := sub_nonneg.mpr hpδ
  intro n hn
  induction n with
  | zero => simpa only [Nat.add_zero, pow_zero] using
      (measureReal_le_one (μ := latticeBondLaw d p)
        (s := Q.slabRootSurvival j width k₀ z lower upper))
  | succ n ih =>
    have hn' : n < N := by omega
    have hzₙ : z ∈ Q.slabPrefix j width (k₀ + n) :=
      Q.slabPrefix_mono j width (Nat.le_add_right k₀ n) hz
    have hznext : z ∈ Q.slabPrefix j width (k₀ + n + 1) :=
      Q.slabPrefix_mono j width (Nat.le_succ _) hzₙ
    let P := Q.slabPrefix j width (k₀ + n)
    let S := Q.slab j width (k₀ + n)
    let D := Q.slabPrefix j width (k₀ + n + 1)
    let G := Q.slabRootSurvival j width (k₀ + n) z lower upper
    let H := Q.slabRootSurvival j width (k₀ + n + 1) z lower upper
    let C : Set (Configuration d) := {ω | IsCrossingRoot ω D lower upper z}
    have hG : MeasurableSet[bondSigma (localBonds P)] G :=
      Q.measurableSet_slabRootSurvival j width (k₀ + n) hzₙ lower upper
    have hH : MeasurableSet H := bondSigma_le _ _
      (Q.measurableSet_slabRootSurvival j width (k₀ + n + 1) hznext lower upper)
    have hC : MeasurableSet C := measurableSet_isCrossingRoot D lower upper z
    have hHG : H ⊆ G := Q.slabRootSurvival_succ_subset j hwidth (hsize n hn')
      hzₙ lower upper
    have hHC : Disjoint H C := by
      rw [Set.disjoint_left]
      intro ω hω hcross
      exact hω.2 hcross
    have hcond : ∀ᵐ ω ∂(latticeBondLaw d p).restrict G,
        (p : ℝ) * δ ≤ (latticeBondLaw d p)[
          C.indicator (fun _ => (1 : ℝ)) | bondSigma (localBonds P)] ω := by
      apply ae_restrict_of_ae_restrict_of_subset (fun _ h => h.1)
      exact condExp_crossingRoot_lower_of_boundary_candidate p P S D
        (Q.finite_slabPrefix j width (k₀ + n)) (Q.finite_slab j width (k₀ + n))
        (Q.disjoint_slabPrefix_slab j width (k₀ + n))
        (Q.slabPrefix_mono j width (Nat.le_succ _))
        (Q.slab_subset_slabPrefix_succ j width (k₀ + n))
        z hzₙ lower upper δ (hprob n hn')
    have hupper := condExp_indicator_le_one_sub_of_disjoint (latticeBondLaw d p)
      (bondSigma_le (localBonds P)) hH hC hHC ((p : ℝ) * δ) hcond
    have hstep := measureReal_le_mul_of_condExp_indicator_le (latticeBondLaw d p)
      (bondSigma_le (localBonds P)) hG hH hHG (1 - (p : ℝ) * δ) hupper
    have ih' := ih (by omega)
    change (latticeBondLaw d p).real H ≤ _
    calc
      (latticeBondLaw d p).real H ≤ (1 - (p : ℝ) * δ) *
          (latticeBondLaw d p).real G := hstep
      _ ≤ (1 - (p : ℝ) * δ) ^ (n + 1) := by
        simpa only [pow_succ, mul_comm] using mul_le_mul_of_nonneg_left ih' hq

/-- A root that escapes the prefix but does not cross the marked faces in the
cube survives at the prefix boundary. -/
theorem IntegerCube.slabRootSurvival_of_escape {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {width k : ℕ} (hwidth : 0 < width) (hsize : k * width < Q.size)
    {ω : Configuration d} {z : Vertex d} (hz : z ∈ Q.slabPrefix j width k)
    (lower upper : Fin d → Set (Vertex d))
    (hescape : targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width k) z ω)
    (hfail : ¬ IsCrossingRoot ω Q.vertices lower upper z) :
    ω ∈ Q.slabRootSurvival j width k z lower upper := by
  obtain ⟨w, _, hw, hzw⟩ := hescape
  refine ⟨Q.slabBoundaryReachable_of_reachable_outside_prefix j hwidth hsize hz hw.2 hzw, ?_⟩
  intro hroot
  have hsub : Q.slabPrefix j width k ⊆ Q.vertices := fun _ hx => hx.1
  exact hfail (hroot.of_reachable_in_larger_region hsub (hsub hz)
    (SimpleGraph.Reachable.refl z))

/-- A root that escapes a distant prefix without crossing the marked faces
has geometrically small probability. -/
theorem IntegerCube.measureReal_escape_without_crossing_le {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (z : Vertex d) (hz : z ∈ Q.slabPrefix j width k₀)
    (lower upper : Fin d → Set (Vertex d)) (p : unitInterval) (δ : ℝ) (hδ : δ ≤ 1)
    (hprob : ∀ n < N, ∀ y ∈ Q.slab j width (k₀ + n), δ ≤ (latticeBondLaw d p).real
      {ω | IsCrossingRoot ω (Q.slab j width (k₀ + n)) lower upper y}) :
    (latticeBondLaw d p).real {ω |
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z ω ∧
      ¬ IsCrossingRoot ω Q.vertices lower upper z} ≤ (1 - (p : ℝ) * δ) ^ N := by
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (Q.measureReal_slabRootSurvival_le j width k₀ N hwidth
      (fun n hn => hsize n (Nat.le_of_lt hn)) z hz lower upper p δ hδ hprob N le_rfl)
  intro ω hω
  exact Q.slabRootSurvival_of_escape j hwidth (hsize N le_rfl)
    (Q.slabPrefix_mono j width (Nat.le_add_right k₀ N) hz) lower upper hω.1 hω.2

/-- A connection from a finite set of roots to a distant region, without a
root crossing the marked faces, is controlled by the root escape bound. -/
theorem IntegerCube.measureReal_connection_without_crossing_le {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (A : Finset (Vertex d)) (hA : (↑A : Set (Vertex d)) ⊆ Q.slabPrefix j width k₀)
    (L R : Set (Vertex d)) (hL : L ⊆ A)
    (hR : R ⊆ Q.vertices \ Q.slabPrefix j width (k₀ + N))
    (lower upper : Fin d → Set (Vertex d)) (p : unitInterval) (δ : ℝ) (hδ : δ ≤ 1)
    (hprob : ∀ n < N, ∀ y ∈ Q.slab j width (k₀ + n), δ ≤ (latticeBondLaw d p).real
      {ω | IsCrossingRoot ω (Q.slab j width (k₀ + n)) lower upper y}) :
    (latticeBondLaw d p).real {ω | ConnectsRegions ω Q.vertices L R ∧
      ¬ ∃ z, IsCrossingRoot ω Q.vertices lower upper z} ≤
      (A.card : ℝ) * (1 - (p : ℝ) * δ) ^ N := by
  classical
  let E : Vertex d → Set (Configuration d) := fun z => {ω |
    targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z ω ∧
    ¬ IsCrossingRoot ω Q.vertices lower upper z}
  have hcover : {ω | ConnectsRegions ω Q.vertices L R ∧
      ¬ ∃ z, IsCrossingRoot ω Q.vertices lower upper z} ⊆ ⋃ z ∈ A, E z := by
    rintro ω ⟨⟨z, _, hzL, w, hwQ, hwR, hzw⟩, hfail⟩
    refine Set.mem_iUnion₂.mpr ⟨z, hL hzL, ⟨w, hwQ, hR hwR, hzw⟩, ?_⟩
    intro hcross
    exact hfail ⟨z, hcross⟩
  calc
    _ ≤ (latticeBondLaw d p).real (⋃ z ∈ A, E z) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ z ∈ A, (latticeBondLaw d p).real (E z) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ A, (1 - (p : ℝ) * δ) ^ N := by
      apply Finset.sum_le_sum
      intro z hz
      exact Q.measureReal_escape_without_crossing_le j width k₀ N hwidth hsize
        z (hA hz) lower upper p δ hδ hprob
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end Rigidity.Percolation

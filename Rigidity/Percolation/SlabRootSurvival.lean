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

end Rigidity.Percolation

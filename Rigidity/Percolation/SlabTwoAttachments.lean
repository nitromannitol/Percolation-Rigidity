import Rigidity.Percolation.SlabAttachmentGeometry

/-!
# Joining explored components through a fresh slab

Two past components with distinct boundary bonds connect with a conditional
probability bounded below by the product of the two bond probabilities and a
uniform two-point connection probability in the slab.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped MeasureTheory

/-- Reaching two distinct boundary bonds from two explored roots gives a
conditional lower bound for their connection through a fresh slab. -/
theorem condExp_reachable_lower_of_two_slab_attachments {d : ℕ} {ι : Type*}
    [Countable ι] (p : unitInterval) (P S D : Set (Vertex d))
    (hP : P.Finite) (hS : S.Finite) (hPS : Disjoint P S)
    (hPD : P ⊆ D) (hSD : S ⊆ D) (z z' : Vertex d) (hz : z ∈ P) (hz' : z' ∈ P)
    (x y x' y' : ι → Vertex d) (hx : ∀ i, x i ∈ P) (hy : ∀ i, y i ∈ S)
    (hx' : ∀ i, x' i ∈ P) (hy' : ∀ i, y' i ∈ S)
    (hxy : ∀ i, (nearestNeighborGraph d).Adj (x i) (y i))
    (hx'y' : ∀ i, (nearestNeighborGraph d).Adj (x' i) (y' i))
    (hne : ∀ i, bondOfAdjacent (hxy i) ≠ bondOfAdjacent (hx'y' i))
    (δ : ℝ) (hprob : ∀ i, δ ≤ (latticeBondLaw d p).real
      {ω | (openIn ω S).Reachable (y i) (y' i)}) :
    ∀ᵐ ω ∂(latticeBondLaw d p).restrict
      (⋃ i, ({ω | (openIn ω P).Reachable z (x i)} ∩
        {ω | (openIn ω P).Reachable z' (x' i)})),
      (p : ℝ) * ((p : ℝ) * δ) ≤ (latticeBondLaw d p)[
        ({ω | (openIn ω D).Reachable z z'} : Set (Configuration d)).indicator
          (fun _ => (1 : ℝ)) | bondSigma (localBonds P)] ω := by
  let A : ι → Set (Configuration d) := fun i =>
    {ω | (openIn ω P).Reachable z (x i)} ∩ {ω | (openIn ω P).Reachable z' (x' i)}
  let B : ι → Set (Configuration d) := fun i => {ω | (openIn ω S).Reachable (y i) (y' i)}
  have hA : ∀ i, MeasurableSet[bondSigma (localBonds P)] (A i) := fun i =>
    (measurableSet_reachable_openIn_bondSigma P hP hz (hx i)).inter
      (measurableSet_reachable_openIn_bondSigma P hP hz' (hx' i))
  have hB : ∀ i, MeasurableSet[bondSigma (localBonds S)] (B i) := fun i =>
    measurableSet_reachable_openIn_bondSigma S hS (hy i) (hy' i)
  have hG : MeasurableSet (⋃ i, A i) :=
    bondSigma_le (localBonds P) _ (MeasurableSet.iUnion hA)
  apply condExp_indicator_lower_of_two_fresh_attachments p (localBonds P)
    (fun _ => localBonds S) (fun i => bondOfAdjacent (hxy i))
    (fun i => bondOfAdjacent (hx'y' i)) (fun _ => (disjoint_localBonds hPS).symm)
    (fun i => (bondOfAdjacent_not_mem_localBonds hPS (hx i) (hy i) (hxy i)).1)
    (fun i => (bondOfAdjacent_not_mem_localBonds hPS (hx' i) (hy' i) (hx'y' i)).1)
    (fun i => (bondOfAdjacent_not_mem_localBonds hPS (hx i) (hy i) (hxy i)).2)
    (fun i => (bondOfAdjacent_not_mem_localBonds hPS (hx' i) (hy' i) (hx'y' i)).2)
    hne A B hA hB (measurableSet_openIn_reachable D z z') hG
    (Set.Subset.refl _) (fun i => ?_) δ hprob
  rintro ω ⟨⟨hzx, hz'x'⟩, hopen, hopen', hyy'⟩
  exact reachable_openIn_of_two_slab_attachments hPD hSD (hx i) (hy i) (hx' i) (hy' i)
    (hxy i) (hx'y' i) hopen hopen' hzx hyy' hz'x'


/-- If two distinct explored components both reach a fresh slab, their
conditional probability of connecting in the ambient region is at least
`p * (p * δ)`, assuming a uniform slab two-point lower bound. -/
theorem condExp_reachable_lower_of_two_components_entering_slab {d : ℕ}
    (p : unitInterval) (P S D : Set (Vertex d))
    (hP : P.Finite) (hS : S.Finite) (hPS : Disjoint P S)
    (hPD : P ⊆ D) (hSD : S ⊆ D) (hDS : D ⊆ P ∪ S)
    (z z' : Vertex d) (hz : z ∈ P) (hz' : z' ∈ P)
    (δ : ℝ) (hprob : ∀ y ∈ S, ∀ y' ∈ S, δ ≤ (latticeBondLaw d p).real
      {ω | (openIn ω S).Reachable y y'}) :
    ∀ᵐ ω ∂(latticeBondLaw d p).restrict
      (targetConnection D S z ∩ targetConnection D S z' ∩
        {ω | ¬ (openIn ω P).Reachable z z'}),
      (p : ℝ) * ((p : ℝ) * δ) ≤ (latticeBondLaw d p)[
        ({ω | (openIn ω D).Reachable z z'} : Set (Configuration d)).indicator
          (fun _ => (1 : ℝ)) | bondSigma (localBonds P)] ω := by
  let E := {pair : Vertex d × Vertex d //
    pair.1 ∈ P ∧ pair.2 ∈ S ∧ (nearestNeighborGraph d).Adj pair.1 pair.2}
  let I := {pair : E × E // bondOfAdjacent pair.1.property.2.2 ≠
    bondOfAdjacent pair.2.property.2.2}
  let x : I → Vertex d := fun i => i.val.1.val.1
  let y : I → Vertex d := fun i => i.val.1.val.2
  let x' : I → Vertex d := fun i => i.val.2.val.1
  let y' : I → Vertex d := fun i => i.val.2.val.2
  have hx : ∀ i, x i ∈ P := fun i => i.val.1.property.1
  have hy : ∀ i, y i ∈ S := fun i => i.val.1.property.2.1
  have hx' : ∀ i, x' i ∈ P := fun i => i.val.2.property.1
  have hy' : ∀ i, y' i ∈ S := fun i => i.val.2.property.2.1
  have hxy : ∀ i, (nearestNeighborGraph d).Adj (x i) (y i) :=
    fun i => i.val.1.property.2.2
  have hx'y' : ∀ i, (nearestNeighborGraph d).Adj (x' i) (y' i) :=
    fun i => i.val.2.property.2.2
  have hne : ∀ i, bondOfAdjacent (hxy i) ≠ bondOfAdjacent (hx'y' i) :=
    fun i => i.property
  apply ae_restrict_of_ae_restrict_of_subset (t := ⋃ i : I,
    ({ω | (openIn ω P).Reachable z (x i)} ∩
      {ω | (openIn ω P).Reachable z' (x' i)}))
  · rintro ω ⟨⟨⟨w, _, hw, hzw⟩, ⟨w', _, hw', hz'w'⟩⟩, hsep⟩
    obtain ⟨a, ha, b, hb, hab, a', ha', b', hb', ha'b', hza, hz'a', _, _, hne'⟩ :=
      exists_distinct_slab_attachments_of_reachable hPS hDS hz hz' hw hw' hzw hz'w' hsep
    exact Set.mem_iUnion.mpr ⟨⟨(⟨(a, b), ha, hb, hab⟩,
      ⟨(a', b'), ha', hb', ha'b'⟩), hne'⟩, hza, hz'a'⟩
  · exact condExp_reachable_lower_of_two_slab_attachments p P S D hP hS hPS hPD hSD
      z z' hz hz' x y x' y' hx hy hx' hy' hxy hx'y' hne δ
      (fun i => hprob (y i) (hy i) (y' i) (hy' i))

end Rigidity.Percolation

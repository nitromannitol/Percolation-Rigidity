import Rigidity.Percolation.SlabTwoComponentDecay

/-!
# Boundary candidates for slab exploration

An explored component has a boundary candidate if it reaches an endpoint of
a bond leading into the fresh slab. Distinct components have distinct
boundary bonds, before any of those bonds are exposed.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped MeasureTheory

/-- A root reaches a vertex in the explored region adjacent to the fresh slab. -/
def slabBoundaryReachable {d : ℕ} (P S : Set (Vertex d)) (z : Vertex d)
    (ω : Configuration d) : Prop :=
  ∃ x ∈ P, ∃ y ∈ S, (nearestNeighborGraph d).Adj x y ∧ (openIn ω P).Reachable z x

/-- Boundary reachability in a finite explored region depends only on its
internal bonds. -/
theorem measurableSet_slabBoundaryReachable_bondSigma {d : ℕ} (P S : Set (Vertex d))
    (hP : P.Finite) {z : Vertex d} (hz : z ∈ P) :
    MeasurableSet[bondSigma (localBonds P)] {ω | slabBoundaryReachable P S z ω} := by
  have heq : {ω | slabBoundaryReachable P S z ω} = ⋃ x ∈ P, ⋃ y ∈ S,
      ⋃ (_ : (nearestNeighborGraph d).Adj x y), {ω | (openIn ω P).Reachable z x} := by
    ext ω
    simp only [slabBoundaryReachable, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor <;> rintro ⟨a, ha, b, hb, hab, h⟩ <;> exact ⟨a, ha, b, hb, hab, h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun hx =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun _ => measurableSet_reachable_openIn_bondSigma P hP hz hx

/-- Two disconnected explored components with boundary candidates have
conditional connection probability at least `p * (p * δ)`. -/
theorem condExp_reachable_lower_of_two_boundary_candidates {d : ℕ}
    (p : unitInterval) (P S D : Set (Vertex d))
    (hP : P.Finite) (hS : S.Finite) (hPS : Disjoint P S)
    (hPD : P ⊆ D) (hSD : S ⊆ D)
    (z z' : Vertex d) (hz : z ∈ P) (hz' : z' ∈ P)
    (δ : ℝ) (hprob : ∀ y ∈ S, ∀ y' ∈ S, δ ≤ (latticeBondLaw d p).real
      {ω | (openIn ω S).Reachable y y'}) :
    ∀ᵐ ω ∂(latticeBondLaw d p).restrict
      {ω | slabBoundaryReachable P S z ω ∧ slabBoundaryReachable P S z' ω ∧
        ¬ (openIn ω P).Reachable z z'},
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
  · rintro ω ⟨⟨a, ha, b, hb, hab, hza⟩, ⟨a', ha', b', hb', ha'b', hz'a'⟩, hsep⟩
    have hne' : bondOfAdjacent hab ≠ bondOfAdjacent ha'b' := by
      intro heq
      have hedge : s(a, b) = s(a', b') := congrArg Subtype.val heq
      rcases Sym2.eq_iff.mp hedge with ⟨haa', _⟩ | ⟨hab', _⟩
      · subst a'
        exact hsep (hza.trans hz'a'.symm)
      · subst b'
        exact Set.disjoint_left.mp hPS ha hb'
    exact Set.mem_iUnion.mpr ⟨⟨(⟨(a, b), ha, hb, hab⟩,
      ⟨(a', b'), ha', hb', ha'b'⟩), hne'⟩, hza, hz'a'⟩
  · exact condExp_reachable_lower_of_two_slab_attachments p P S D hP hS hPS hPD hSD
      z z' hz hz' x y x' y' hx hy hx' hy' hxy hx'y' hne δ
      (fun i => hprob (y i) (hy i) (y' i) (hy' i))


/-- If two disconnected explored components have boundary candidates at every
step, their survival probability decays geometrically. -/
theorem measureReal_le_pow_of_two_boundary_candidates {d : ℕ}
    (p : unitInterval) (P S D : ℕ → Set (Vertex d))
    (hP : ∀ n, (P n).Finite) (hS : ∀ n, (S n).Finite)
    (hPS : ∀ n, Disjoint (P n) (S n))
    (hPD : ∀ n, P n ⊆ D n) (hSD : ∀ n, S n ⊆ D n)
    (z z' : Vertex d) (hz : ∀ n, z ∈ P n) (hz' : ∀ n, z' ∈ P n)
    (δ : ℝ) (hδ : δ ≤ 1)
    (hprob : ∀ n, ∀ y ∈ S n, ∀ y' ∈ S n, δ ≤ (latticeBondLaw d p).real
      {ω | (openIn ω (S n)).Reachable y y'})
    (G : ℕ → Set (Configuration d))
    (hG : ∀ n, MeasurableSet[bondSigma (localBonds (P n))] (G n))
    (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hcover : ∀ n, G n ⊆ {ω | slabBoundaryReachable (P n) (S n) z ω ∧
      slabBoundaryReachable (P n) (S n) z' ω ∧ ¬ (openIn ω (P n)).Reachable z z'})
    (hdisj : ∀ n, Disjoint (G (n + 1)) {ω | (openIn ω (D n)).Reachable z z'}) :
    ∀ n, (latticeBondLaw d p).real (G n) ≤
      (1 - (p : ℝ) * ((p : ℝ) * δ)) ^ n := by
  have hfirst : (p : ℝ) * δ ≤ 1 := by
    calc
      (p : ℝ) * δ ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hδ p.property.1
      _ ≤ 1 := by simpa using p.property.2
  have hsecond : (p : ℝ) * ((p : ℝ) * δ) ≤ 1 := by
    calc
      (p : ℝ) * ((p : ℝ) * δ) ≤ (p : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hfirst p.property.1
      _ ≤ 1 := by simpa using p.property.2
  apply measureReal_le_pow_one_sub_of_condExp_success (latticeBondLaw d p)
    (fun n => bondSigma (localBonds (P n))) (fun n => bondSigma_le _)
    G (fun n => {ω | (openIn ω (D n)).Reachable z z'}) hG
    (fun n => measurableSet_openIn_reachable (D n) z z') hdecr hdisj
    ((p : ℝ) * ((p : ℝ) * δ)) hsecond
  intro n
  apply ae_restrict_of_ae_restrict_of_subset (hcover n)
  exact condExp_reachable_lower_of_two_boundary_candidates p (P n) (S n) (D n)
    (hP n) (hS n) (hPS n) (hPD n) (hSD n) z z' (hz n) (hz' n) δ (hprob n)

end Rigidity.Percolation

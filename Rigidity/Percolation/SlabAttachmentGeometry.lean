import Rigidity.Percolation.SlabAttachment
import Rigidity.Percolation.SlabCrossings
import Rigidity.Percolation.CoalescenceCover
import Rigidity.Percolation.TargetConnectionHarris

/-!
# Gluing paths across slab boundaries

Open boundary bonds join paths in an explored region to paths in a fresh slab.
Two such bonds join two previously explored components through the slab.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped MeasureTheory

/-- Reachability between vertices of a finite region depends only on its
internal bonds. -/
theorem measurableSet_reachable_openIn_bondSigma {d : ℕ} (B : Set (Vertex d))
    (hB : B.Finite) {x y : Vertex d} (hx : x ∈ B) (hy : y ∈ B) :
    MeasurableSet[bondSigma (localBonds B)] {ω | (openIn ω B).Reachable x y} := by
  have heq : {ω | (openIn ω B).Reachable x y} =
      {ω | ConnectsRegions ω B {x} {y}} := by
    ext ω
    simp only [Set.mem_setOf_eq, ConnectsRegions, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨x, hx, rfl, y, hy, rfl, h⟩
    · rintro ⟨a, _, rfl, b, _, rfl, h⟩
      exact h
  rw [heq]
  exact measurableSet_connectsRegions_localBond B {x} {y} hB

/-- Connection to a target from a vertex of a finite region depends only on
the region's internal bonds. -/
theorem measurableSet_targetConnection_bondSigma {d : ℕ} (B T : Set (Vertex d))
    (hB : B.Finite) {x : Vertex d} (hx : x ∈ B) :
    MeasurableSet[bondSigma (localBonds B)] (targetConnection B T x) := by
  have heq : targetConnection B T x = ⋃ y ∈ B, ⋃ (_ : y ∈ T),
      {ω | (openIn ω B).Reachable x y} := by
    ext ω
    simp only [targetConnection, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hyB, hyT, h⟩
      exact ⟨y, hyB, hyT, h⟩
    · rintro ⟨y, hyB, hyT, h⟩
      exact ⟨y, hyB, hyT, h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy =>
    MeasurableSet.iUnion fun _ => measurableSet_reachable_openIn_bondSigma B hB hx hy

/-- The event that a vertex's component crosses every marked face of a finite
region is measurable in its internal bonds. -/
theorem measurableSet_isCrossingRoot_bondSigma {d : ℕ} (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) (hB : B.Finite) {x : Vertex d} (hx : x ∈ B) :
    MeasurableSet[bondSigma (localBonds B)] {ω | IsCrossingRoot ω B lower upper x} := by
  have heq : {ω | IsCrossingRoot ω B lower upper x} =
      ⋂ i, (targetConnection B (lower i) x ∩ targetConnection B (upper i) x) := by
    ext ω
    simp only [IsCrossingRoot, hx, true_and, targetConnection, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_targetConnection_bondSigma B (lower i) hB hx).inter
      (measurableSet_targetConnection_bondSigma B (upper i) hB hx)

/-- A bond crossing between disjoint vertex regions is internal to neither. -/
theorem bondOfAdjacent_not_mem_localBonds {d : ℕ} {P S : Set (Vertex d)}
    (hPS : Disjoint P S) {x y : Vertex d} (hx : x ∈ P) (hy : y ∈ S)
    (hxy : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent hxy ∉ localBonds P ∧ bondOfAdjacent hxy ∉ localBonds S := by
  constructor
  · intro h
    exact Set.disjoint_left.mp hPS (h y (Sym2.mem_mk_right x y)) hy
  · intro h
    exact Set.disjoint_left.mp hPS hx (h x (Sym2.mem_mk_left x y))

/-- An open boundary bond joins a past path to a slab path in the ambient
region. -/
theorem reachable_openIn_of_slab_attachment {d : ℕ} {ω : Configuration d}
    {P S D : Set (Vertex d)} (hPD : P ⊆ D) (hSD : S ⊆ D)
    {z x y w : Vertex d} (hx : x ∈ P) (hy : y ∈ S)
    (hxy : (nearestNeighborGraph d).Adj x y) (hopen : ω (bondOfAdjacent hxy) = true)
    (hzx : (openIn ω P).Reachable z x) (hyw : (openIn ω S).Reachable y w) :
    (openIn ω D).Reachable z w := by
  have hbond : (openIn ω D).Adj x y :=
    ⟨(openGraph_adj_iff ω x y).mpr ⟨hxy, hopen⟩, hPD hx, hSD hy⟩
  exact ((reachable_openIn_mono hPD hzx).trans hbond.reachable).trans
    (reachable_openIn_mono hSD hyw)

/-- A vertex connected to a crossing root in a larger region also connects to
all of the marked faces. -/
theorem IsCrossingRoot.of_reachable_in_larger_region {d : ℕ} {ω : Configuration d}
    {S D : Set (Vertex d)} {lower upper : Fin d → Set (Vertex d)}
    {y z : Vertex d} (hroot : IsCrossingRoot ω S lower upper y) (hSD : S ⊆ D)
    (hz : z ∈ D) (hzy : (openIn ω D).Reachable z y) :
    IsCrossingRoot ω D lower upper z := by
  refine ⟨hz, fun i => ?_⟩
  obtain ⟨⟨a, haS, ha, hya⟩, ⟨b, hbS, hb, hyb⟩⟩ := hroot.2 i
  exact ⟨⟨a, hSD haS, ha, hzy.trans (reachable_openIn_mono hSD hya)⟩,
    ⟨b, hSD hbS, hb, hzy.trans (reachable_openIn_mono hSD hyb)⟩⟩

/-- Two open boundary bonds and a slab path join the past components of their
endpoints in the ambient region. -/
theorem reachable_openIn_of_two_slab_attachments {d : ℕ} {ω : Configuration d}
    {P S D : Set (Vertex d)} (hPD : P ⊆ D) (hSD : S ⊆ D)
    {z x y y' x' z' : Vertex d}
    (hx : x ∈ P) (hy : y ∈ S) (hx' : x' ∈ P) (hy' : y' ∈ S)
    (hxy : (nearestNeighborGraph d).Adj x y) (hx'y' : (nearestNeighborGraph d).Adj x' y')
    (hopen : ω (bondOfAdjacent hxy) = true)
    (hopen' : ω (bondOfAdjacent hx'y') = true)
    (hzx : (openIn ω P).Reachable z x) (hyy' : (openIn ω S).Reachable y y')
    (hz'x' : (openIn ω P).Reachable z' x') : (openIn ω D).Reachable z z' := by
  have hleft := reachable_openIn_of_slab_attachment hPD hSD hx hy hxy hopen hzx hyy'
  have hright := reachable_openIn_of_slab_attachment hPD hSD hx' hy' hx'y' hopen'
    hz'x' (SimpleGraph.Reachable.refl y')
  exact hleft.trans hright.symm

/-- If an explored root reaches one of the candidate boundary vertices, then
the conditional probability that it crosses the ambient region is at least
`p * δ`, provided every corresponding fresh-slab root crosses with probability
at least `δ`. -/
theorem condExp_crossingRoot_lower_of_slab_attachments {d : ℕ} {ι : Type*}
    [Countable ι] (p : unitInterval) (P S D : Set (Vertex d))
    (hP : P.Finite) (hS : S.Finite) (hPS : Disjoint P S)
    (hPD : P ⊆ D) (hSD : S ⊆ D) (z : Vertex d) (hz : z ∈ P)
    (x y : ι → Vertex d) (hx : ∀ i, x i ∈ P) (hy : ∀ i, y i ∈ S)
    (hxy : ∀ i, (nearestNeighborGraph d).Adj (x i) (y i))
    (lower upper : Fin d → Set (Vertex d)) (δ : ℝ)
    (hprob : ∀ i, δ ≤ (latticeBondLaw d p).real
      {ω | IsCrossingRoot ω S lower upper (y i)}) :
    ∀ᵐ ω ∂(latticeBondLaw d p).restrict
      (⋃ i, {ω | (openIn ω P).Reachable z (x i)}),
      (p : ℝ) * δ ≤ (latticeBondLaw d p)[
        ({ω | IsCrossingRoot ω D lower upper z} : Set (Configuration d)).indicator
          (fun _ => (1 : ℝ)) |
          bondSigma (localBonds P)] ω := by
  let A : ι → Set (Configuration d) := fun i => {ω | (openIn ω P).Reachable z (x i)}
  let B : ι → Set (Configuration d) := fun i => {ω | IsCrossingRoot ω S lower upper (y i)}
  have hA : ∀ i, MeasurableSet[bondSigma (localBonds P)] (A i) := fun i =>
    measurableSet_reachable_openIn_bondSigma P hP hz (hx i)
  have hB : ∀ i, MeasurableSet[bondSigma (localBonds S)] (B i) := fun i =>
    measurableSet_isCrossingRoot_bondSigma S lower upper hS (hy i)
  have hG : MeasurableSet (⋃ i, A i) :=
    bondSigma_le (localBonds P) _ (MeasurableSet.iUnion hA)
  apply condExp_indicator_lower_of_fresh_attachment p (localBonds P)
    (fun _ => localBonds S) (fun i => bondOfAdjacent (hxy i))
    (fun _ => (disjoint_localBonds hPS).symm)
    (fun i => (bondOfAdjacent_not_mem_localBonds hPS (hx i) (hy i) (hxy i)).1)
    (fun i => (bondOfAdjacent_not_mem_localBonds hPS (hx i) (hy i) (hxy i)).2)
    A B hA hB (measurableSet_isCrossingRoot D lower upper z) hG
    (Set.Subset.refl _) (fun i => ?_) δ hprob
  rintro ω ⟨hzx, hopen, hroot⟩
  have hzy := reachable_openIn_of_slab_attachment hPD hSD (hx i) (hy i) (hxy i)
    hopen hzx (SimpleGraph.Reachable.refl (y i))
  exact hroot.of_reachable_in_larger_region hSD (hPD hz) hzy

end Rigidity.Percolation

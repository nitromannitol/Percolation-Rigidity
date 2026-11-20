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

end Rigidity.Percolation

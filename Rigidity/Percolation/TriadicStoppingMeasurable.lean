import Rigidity.Percolation.TriadicStopping
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of stopping partitions

If membership in each good-cube event is measurable, then stability, stopping,
and maximal stopping are measurable events.
-/

namespace Rigidity.Percolation

open MeasureTheory

instance {d : ℕ} : Countable (TriadicCube d) := by
  let f : TriadicCube d → ℕ × (Fin d → ℤ) := fun Q => (Q.scale, Q.index)
  have hf : Function.Injective f := by
    intro Q R h
    exact TriadicCube.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact hf.countable

/-- Stability is measurable when goodness of each cube is measurable. -/
theorem TriadicCube.measurableSet_mem_stableGood {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (G : Ω → Set (TriadicCube d))
    (hG : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω}) (Q : TriadicCube d) :
    MeasurableSet {ω | Q ∈ stableGood (G ω)} := by
  have heq : {ω | Q ∈ stableGood (G ω)} =
      ⋂ T : {T // T ∈ Q.influence}, {ω | T.1 ∈ G ω} := by
    ext ω
    simp only [stableGood, Set.mem_setOf_eq, Set.mem_iInter, Set.subset_def]
    constructor
    · intro h T
      exact h T.1 T.2
    · intro h T hT
      exact h ⟨T, hT⟩
  rw [heq]
  exact MeasurableSet.iInter (fun T => hG T.1)

/-- The event that a cube is stopping is measurable. -/
theorem TriadicCube.measurableSet_isStopping {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (G : Ω → Set (TriadicCube d))
    (hG : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω}) (Q : TriadicCube d) :
    MeasurableSet {ω | Q.IsStopping (G ω)} := by
  classical
  by_cases hz : Q.scale = 0
  · have heq : {ω | Q.IsStopping (G ω)} = {ω | Q ∈ stableGood (G ω)} := by
      ext ω
      simp only [Set.mem_setOf_eq, IsStopping, hz, true_or, and_true]
    rw [heq]
    exact measurableSet_mem_stableGood G hG Q
  · have heq : {ω | Q.IsStopping (G ω)} =
        {ω | Q ∈ stableGood (G ω)} ∩
          ⋃ digits : Fin d → Fin 3, {ω | Q.child digits ∉ stableGood (G ω)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, IsStopping, hz, false_or]
    rw [heq]
    exact (measurableSet_mem_stableGood G hG Q).inter
      (MeasurableSet.iUnion fun digits => (measurableSet_mem_stableGood G hG _).compl)

/-- The event that a cube belongs to the maximal stopping partition is measurable. -/
theorem TriadicCube.measurableSet_isMaximalStopping {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (G : Ω → Set (TriadicCube d))
    (hG : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω}) (Q : TriadicCube d) :
    MeasurableSet {ω | Q.IsMaximalStopping (G ω)} := by
  classical
  let Larger := {R : TriadicCube d // Q.vertices ⊆ R.vertices ∧ Q.scale < R.scale}
  have heq : {ω | Q.IsMaximalStopping (G ω)} = {ω | Q.IsStopping (G ω)} ∩
      ⋂ R : Larger, {ω | ¬ R.1.IsStopping (G ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, IsMaximalStopping]
    constructor
    · rintro ⟨hQ, hmax⟩
      refine ⟨hQ, ?_⟩
      intro R hR
      exact (not_lt_of_ge (hmax R.1 hR R.2.1)) R.2.2
    · rintro ⟨hQ, hmax⟩
      refine ⟨hQ, ?_⟩
      intro R hR hsub
      by_contra h
      exact hmax ⟨R, hsub, by omega⟩ hR
  rw [heq]
  exact (measurableSet_isStopping G hG Q).inter
    (MeasurableSet.iInter fun R => (measurableSet_isStopping G hG R.1).compl)


/-- Declare cubes good whenever their parents are not contained in a region. -/
def TriadicCube.localGood {d : ℕ} (G : Set (TriadicCube d))
    (U : Set (LatticeProb.Percolation.Vertex d)) : Set (TriadicCube d) :=
  G ∪ {T | ¬ T.parent.vertices ⊆ U}

/-- The localized collection contains the original good cubes. -/
theorem TriadicCube.subset_localGood {d : ℕ} (G : Set (TriadicCube d))
    (U : Set (LatticeProb.Percolation.Vertex d)) : G ⊆ localGood G U :=
  Set.subset_union_left

/-- Local and original goodness agree for cubes whose parents lie in the region. -/
theorem TriadicCube.mem_of_mem_localGood {d : ℕ} {G : Set (TriadicCube d)}
    {U : Set (LatticeProb.Percolation.Vertex d)} {T : TriadicCube d}
    (hT : T.parent.vertices ⊆ U) (h : T ∈ localGood G U) : T ∈ G := by
  rcases h with h | h
  · exact h
  · exact (h hT).elim

/-- Localized goodness is measurable if the original goodness events for
cubes supported inside the region are measurable. -/
theorem TriadicCube.measurableSet_mem_localGood {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (G : Ω → Set (TriadicCube d))
    (U : Set (LatticeProb.Percolation.Vertex d))
    (hG : ∀ T : TriadicCube d, T.parent.vertices ⊆ U → MeasurableSet {ω | T ∈ G ω})
    (Q : TriadicCube d) : MeasurableSet {ω | Q ∈ localGood (G ω) U} := by
  classical
  by_cases hQ : Q.parent.vertices ⊆ U
  · have heq : {ω | Q ∈ localGood (G ω) U} = {ω | Q ∈ G ω} := by
      ext ω
      simp only [localGood, Set.mem_setOf_eq, Set.mem_union, hQ, not_true_eq_false, or_false]
    rw [heq]
    exact hG Q hQ
  · have heq : {ω | Q ∈ localGood (G ω) U} = Set.univ := by
      ext ω
      simp only [localGood, Set.mem_setOf_eq, Set.mem_union, hQ, not_false_eq_true, or_true,
        Set.mem_univ]
    rw [heq]
    exact MeasurableSet.univ

/-- The localized maximal-stopping event is measurable in the local environment. -/
theorem TriadicCube.measurableSet_isMaximalStopping_localGood {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (G : Ω → Set (TriadicCube d))
    (U : Set (LatticeProb.Percolation.Vertex d))
    (hG : ∀ T : TriadicCube d, T.parent.vertices ⊆ U → MeasurableSet {ω | T ∈ G ω})
    (Q : TriadicCube d) : MeasurableSet {ω | Q.IsMaximalStopping (localGood (G ω) U)} :=
  measurableSet_isMaximalStopping (fun ω => localGood (G ω) U)
    (measurableSet_mem_localGood G U hG) Q

end Rigidity.Percolation

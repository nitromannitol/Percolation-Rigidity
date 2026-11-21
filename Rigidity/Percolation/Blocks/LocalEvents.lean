import Rigidity.Percolation.Bootstrap.Link
import Rigidity.Percolation.TriadicGoodJointIndependence

/-!
# Local events of the bond configuration

Connections inside a finite region and the uniqueness zone of a cube depend only on the bonds
internal to the region. Events of pairwise disjoint regions are jointly independent, and
finitely many increasing events are positively correlated.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

variable {d : ℕ}

/-- A connection inside a finite region depends only on the bonds internal to the region. -/
theorem measurableSet_reachable_local {B : Set (Vertex d)} (hB : B.Finite) (x y : Vertex d) :
    MeasurableSet[localBondSigma B] {ω : Configuration d | (openIn ω B).Reachable x y} := by
  by_cases hx : x ∈ B
  · by_cases hy : y ∈ B
    · exact measurableSet_reachable_openIn_bondSigma B hB hx hy
    · have : {ω : Configuration d | (openIn ω B).Reachable x y} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hy (mem_of_openIn_reachable h.symm hx)
      rw [this]
      exact @MeasurableSet.empty _ (localBondSigma B)
  · have : {ω : Configuration d | (openIn ω B).Reachable x y} = if x = y then Set.univ else ∅ := by
      ext ω
      split_ifs with hxy
      · simp [hxy]
      · simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        by_cases hy : y ∈ B
        · exact hx (mem_of_openIn_reachable h hy)
        · obtain ⟨w⟩ := h
          cases w with
          | nil => exact hxy rfl
          | cons h _ => exact hx h.2.1
    rw [this]
    split_ifs
    · exact @MeasurableSet.univ _ (localBondSigma B)
    · exact @MeasurableSet.empty _ (localBondSigma B)

/-- The uniqueness zone depends only on the bonds internal to the outer cube. -/
theorem measurableSet_uniqueZone_local (c : Vertex d) (k n : ℕ) :
    MeasurableSet[localBondSigma (cubeAt c n)] {ω : Configuration d | UniqueZone ω c k n} := by
  have hfin : (cubeAt c n).Finite := by
    rw [← coe_cubeFinset]
    exact Finset.finite_toSet _
  have hshell : ∀ x : Vertex d, MeasurableSet[localBondSigma (cubeAt c n)]
      {ω : Configuration d | ∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v} := by
    intro x
    have : {ω : Configuration d | ∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v} =
        ⋃ v ∈ cubeShell c n, {ω | (openIn ω (cubeAt c n)).Reachable x v} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun v _ =>
      measurableSet_reachable_local hfin x v
  have heq : {ω : Configuration d | UniqueZone ω c k n} =
      ⋂ x : Vertex d, ⋂ y : Vertex d,
        ({ω | x ∈ cubeAt c k ∧ y ∈ cubeAt c k ∧
            (∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v) ∧
            (∃ w ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable y w)}ᶜ ∪
          {ω | (openIn ω (cubeAt c n)).Reachable x y}) := by
    ext ω
    simp only [UniqueZone, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    constructor
    · intro h x y
      by_cases hc : x ∈ cubeAt c k ∧ y ∈ cubeAt c k ∧
          (∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v) ∧
          (∃ w ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable y w)
      · exact Or.inr (h x hc.1 y hc.2.1 hc.2.2.1 hc.2.2.2)
      · exact Or.inl hc
    · intro h x hx y hy hxv hyw
      rcases h x y with h | h
      · exact absurd ⟨hx, hy, hxv, hyw⟩ h
      · exact h
  rw [heq]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  refine MeasurableSet.union (MeasurableSet.compl ?_) (measurableSet_reachable_local hfin x y)
  simp only [Set.setOf_and]
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter ((hshell x).inter (hshell y)))

/-- Events of pairwise disjoint finite regions are jointly independent. -/
theorem latticeBondLaw_biInter_eq_prod (p : unitInterval) {ι : Type*} (U : ι → Set (Vertex d))
    (A : ι → Set (Configuration d)) (hA : ∀ i, MeasurableSet[localBondSigma (U i)] (A i))
    (s : Finset ι) (hU : (s : Set ι).Pairwise fun i j => Disjoint (U i) (U j)) :
    latticeBondLaw d p (⋂ i ∈ s, A i) = ∏ i ∈ s, latticeBondLaw d p (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hUs : (s : Set ι).Pairwise fun i j => Disjoint (U i) (U j) :=
      hU.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    have hdisj : Disjoint (U i) (⋃ j ∈ s, U j) := by
      rw [Set.disjoint_left]
      intro x hx hy
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hy
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      exact Set.disjoint_left.mp (hU (Finset.mem_insert_self i s)
        (Finset.mem_insert_of_mem hj) hij) hx hxj
    have hsmeas : MeasurableSet[localBondSigma (⋃ j ∈ s, U j)] (⋂ j ∈ s, A j) := by
      apply Finset.measurableSet_biInter s
      intro j hj
      have hsub : U j ⊆ ⋃ k ∈ s, U k := fun x hx => Set.mem_iUnion₂.mpr ⟨j, hj, hx⟩
      exact localBondSigma_mono hsub _ (hA j)
    have hind := (Indep_iff _ _ _).mp (indep_localBondSigma p hdisj) (A i) (⋂ j ∈ s, A j)
      (hA i) hsmeas
    rw [Finset.set_biInter_insert, Finset.prod_insert hi, hind, ih hUs]

/-- Finitely many increasing events are positively correlated. -/
theorem prod_le_latticeBondLaw_real_biInter (p : unitInterval) {ι : Type*}
    (A : ι → Set (Configuration d)) (hA : ∀ i, IsUpperSet (A i)) (hAm : ∀ i, MeasurableSet (A i))
    (s : Finset ι) :
    ∏ i ∈ s, (latticeBondLaw d p).real (A i) ≤ (latticeBondLaw d p).real (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.set_biInter_insert]
    calc _ ≤ (latticeBondLaw d p).real (A i) * (latticeBondLaw d p).real (⋂ j ∈ s, A j) :=
          mul_le_mul_of_nonneg_left ih measureReal_nonneg
      _ ≤ _ := LatticeProb.infinitePi_harris_bool (fun _ : Bond d => bernoulliMeasure true false p)
          (hA i) (isUpperSet_iInter₂ fun j _ => hA j) (hAm i)
          (s.measurableSet_biInter fun j _ => hAm j)

end Rigidity.Percolation

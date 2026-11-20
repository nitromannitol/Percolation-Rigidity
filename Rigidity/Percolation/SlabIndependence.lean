import Rigidity.Percolation.TriadicGoodIndependence

/-!
# Independent local events

Events determined by bonds in disjoint regions are mutually independent. A
uniform lower bound for their probabilities gives a geometric bound for the
probability that none of them occurs.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory

/-- Local events in pairwise disjoint regions have the product law on every
finite family. -/
theorem measure_biInter_localBond {d : ℕ} {ι : Type*} (p : unitInterval)
    (U : ι → Set (Vertex d)) (A : ι → Set (Configuration d))
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hA : ∀ i, MeasurableSet[localBondSigma (U i)] (A i)) (s : Finset ι) :
    latticeBondLaw d p (⋂ i ∈ s, A i) = ∏ i ∈ s, latticeBondLaw d p (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert hi]
    let V : Set (Vertex d) := ⋃ j ∈ s, U j
    have hUV : Disjoint (U i) V := by
      rw [Set.disjoint_left]
      intro x hx hxV
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxV
      exact Set.disjoint_left.mp (hdisj (by rintro rfl; exact hi hj)) hx hxj
    have hmeas : MeasurableSet[localBondSigma V] (⋂ j ∈ s, A j) := by
      apply s.measurableSet_biInter
      intro j hj
      apply localBondSigma_mono (show U j ⊆ V from Set.subset_iUnion_of_subset j
        (Set.subset_iUnion_of_subset hj (Set.Subset.refl _))) _ (hA j)
    rw [(Indep_iff _ _ _).mp (indep_localBondSigma p hUV) _ _ (hA i) hmeas, ih]

/-- A uniform positive probability of success gives geometric decay for
simultaneous failure in disjoint regions. -/
theorem measureReal_no_local_success_le {d : ℕ} {ι : Type*} (p : unitInterval)
    (U : ι → Set (Vertex d)) (A : ι → Set (Configuration d))
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hA : ∀ i, MeasurableSet[localBondSigma (U i)] (A i))
    (δ : ℝ) (hprob : ∀ i, δ ≤ (latticeBondLaw d p).real (A i))
    (s : Finset ι) :
    (latticeBondLaw d p).real (⋂ i ∈ s, (A i)ᶜ) ≤ (1 - δ) ^ s.card := by
  classical
  have heq := measure_biInter_localBond p U (fun i => (A i)ᶜ) hdisj
    (fun i => (hA i).compl) s
  have heq' : (latticeBondLaw d p).real (⋂ i ∈ s, (A i)ᶜ) =
      ∏ i ∈ s, (latticeBondLaw d p).real ((A i)ᶜ) := by
    simpa only [measureReal_def, ENNReal.toReal_prod] using congrArg ENNReal.toReal heq
  rw [heq']
  calc
    _ ≤ ∏ _i ∈ s, (1 - δ) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact measureReal_nonneg
      · intro i hi
        have hm : MeasurableSet (A i) := by
          exact (iSup₂_le fun e _ => (measurable_pi_apply e).comap_le) _ (hA i)
        rw [measureReal_compl hm, probReal_univ]
        linarith [hprob i]
    _ = (1 - δ) ^ s.card := by simp

end Rigidity.Percolation

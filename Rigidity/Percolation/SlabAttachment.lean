import Rigidity.Percolation.SlabFreshBonds

/-!
# Fresh-bond attachment to slab events

A past-measurable choice of a boundary bond and an independent slab event
retains the product of their probabilities after conditioning on the past.
This is the attachment estimate used in slab exploration.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory
open scoped MeasureTheory

/-- Enlarging the set of bonds enlarges the generated sigma algebra. -/
theorem bondSigma_mono {d : ℕ} {E F : Set (Bond d)} (hEF : E ⊆ F) :
    bondSigma E ≤ bondSigma F :=
  iSup₂_le fun e he => le_iSup_of_le e (le_iSup_of_le (hEF he) le_rfl)

/-- An individual bond's open event is measurable in its coordinate. -/
theorem measurableSet_bond_open {d : ℕ} (e : Bond d) :
    MeasurableSet[bondSigma {e}] {ω : Configuration d | ω e = true} := by
  have hle : MeasurableSpace.comap (fun ω : Configuration d => ω e) inferInstance ≤
      bondSigma {e} := le_iSup_of_le e (le_iSup_of_le (Set.mem_singleton e) le_rfl)
  apply hle
  exact MeasurableSpace.measurableSet_comap.mpr
    ⟨{true}, measurableSet_singleton true, rfl⟩

/-- Opening a fresh bond and realizing an independent fresh event has the
product probability. -/
theorem measureReal_bond_open_inter {d : ℕ} (p : unitInterval) (e : Bond d)
    {E : Set (Bond d)} (he : e ∉ E) {B : Set (Configuration d)}
    (hB : MeasurableSet[bondSigma E] B) :
    (latticeBondLaw d p).real ({ω | ω e = true} ∩ B) =
      (p : ℝ) * (latticeBondLaw d p).real B := by
  have hdisj : Disjoint ({e} : Set (Bond d)) E := by
    simpa only [Set.disjoint_singleton_left] using he
  have h := (Indep_iff _ _ _).mp (indep_bondSigma p hdisj)
    {ω | ω e = true} B (measurableSet_bond_open e) hB
  simp only [measureReal_def, h, ENNReal.toReal_mul, latticeBondLaw_open,
    ENNReal.toReal_ofReal p.property.1]

/-- A past-measurable selection of an unexposed attachment bond and a disjoint
fresh event gives conditional success probability at least `p * δ`. -/
theorem condExp_indicator_lower_of_fresh_attachment {d : ℕ} {ι : Type*}
    [Countable ι] (p : unitInterval) (F : Set (Bond d)) (E : ι → Set (Bond d))
    (e : ι → Bond d) (hE : ∀ i, Disjoint (E i) F)
    (heF : ∀ i, e i ∉ F) (heE : ∀ i, e i ∉ E i)
    (A B : ι → Set (Configuration d)) {G C : Set (Configuration d)}
    (hA : ∀ i, MeasurableSet[bondSigma F] (A i))
    (hB : ∀ i, MeasurableSet[bondSigma (E i)] (B i))
    (hC : MeasurableSet C) (hG : MeasurableSet G) (hcover : G ⊆ ⋃ i, A i)
    (hsubset : ∀ i, A i ∩ ({ω | ω (e i) = true} ∩ B i) ⊆ C)
    (δ : ℝ) (hprob : ∀ i, δ ≤ (latticeBondLaw d p).real (B i)) :
    ∀ᵐ ω ∂(latticeBondLaw d p).restrict G,
      (p : ℝ) * δ ≤ (latticeBondLaw d p)[C.indicator (fun _ => (1 : ℝ)) | bondSigma F] ω := by
  apply condExp_indicator_lower_of_fresh_bond_selection p F (fun i => {e i} ∪ E i)
    (fun i => ?_) A (fun i => {ω | ω (e i) = true} ∩ B i)
    hA (fun i => ?_) hC hG hcover hsubset ((p : ℝ) * δ) (fun i => ?_)
  · exact Set.disjoint_union_left.mpr
      ⟨by simpa only [Set.disjoint_singleton_left] using heF i, hE i⟩
  · exact (bondSigma_mono Set.subset_union_left _ (measurableSet_bond_open (e i))).inter
      (bondSigma_mono Set.subset_union_right _ (hB i))
  · rw [measureReal_bond_open_inter p (e i) (heE i) (hB i)]
    exact mul_le_mul_of_nonneg_left (hprob i) p.property.1

end Rigidity.Percolation

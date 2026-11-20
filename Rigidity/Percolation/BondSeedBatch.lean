import Rigidity.Percolation.BondSeedExploration

/-!
# Batches of sprinkled bond seeds

A finite family of disjoint seed regions selected by the base configuration
retains the product-law bound for simultaneous failure in the added layer.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped MeasureTheory

/-- An event in the added field retains its probability after the base field
is revealed. -/
theorem condExp_indicator_added_event (d : ℕ) (q r : unitInterval)
    {B : Set (Configuration d)} (hB : MeasurableSet B) :
    (bondPairLaw d q r)[(addedBondConfiguration ⁻¹' B).indicator
      (fun _ => (1 : ℝ)) | baseBondSigma d] =ᵐ[bondPairLaw d q r]
      fun _ => (latticeBondLaw d r).real B := by
  have hbase : Measurable (@baseBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_fst.comp (measurable_pi_apply e)
  have hadd : Measurable (@addedBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_snd.comp (measurable_pi_apply e)
  have haddB : MeasurableSet[addedBondSigma d] (addedBondConfiguration ⁻¹' B) :=
    MeasurableSpace.measurableSet_comap.mpr ⟨_, hB, rfl⟩
  have hstrong : StronglyMeasurable[addedBondSigma d]
      ((addedBondConfiguration ⁻¹' B).indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator haddB
  haveI : IsProbabilityMeasure (bondPairLaw d q r) := by
    dsimp only [bondPairLaw]
    infer_instance
  have hind := condExp_indep_eq hadd.comap_le hbase.comap_le hstrong
    (bondPairLaw_indep_layers d q r).symm
  have hmeasure : (bondPairLaw d q r).real (addedBondConfiguration ⁻¹' B) =
      (latticeBondLaw d r).real B := by
    rw [measureReal_def, measureReal_def, ← Measure.map_apply hadd hB, bondPairLaw_map_added]
  simpa only [integral_indicator_const (1 : ℝ) (hadd hB), smul_eq_mul, mul_one, hmeasure]
    using hind

/-- A base-measurable choice of a batch of disjoint finite regions inherits
the geometric bound for failure of all the added-layer seeds. -/
theorem condExp_indicator_lower_of_base_seed_batch {d : ℕ} {ι : Type*}
    [Countable ι] (q r : unitInterval) (n N : ℕ)
    (U : ι → Fin n → Set (Vertex d))
    (hU : ∀ i j, (U i j).Finite)
    (hdisj : ∀ i, Pairwise fun j k => Disjoint (U i j) (U i k))
    (hN : ∀ i j, (finite_localBonds (hU i j)).toFinset.card ≤ N)
    (A : ι → Set (Bond d → Bool × Bool)) {G C : Set (Bond d → Bool × Bool)}
    (hA : ∀ i, MeasurableSet[baseBondSigma d] (A i))
    (hG : MeasurableSet G) (hC : MeasurableSet C) (hcover : G ⊆ ⋃ i, A i)
    (hsubset : ∀ i, A i ∩ (addedBondConfiguration ⁻¹'
      (⋃ j, fullyOpenRegion (U i j))) ⊆ C) :
    ∀ᵐ ω ∂(bondPairLaw d q r).restrict G,
      1 - (1 - (r : ℝ) ^ N) ^ n ≤
        (bondPairLaw d q r)[C.indicator (fun _ => (1 : ℝ)) | baseBondSigma d] ω := by
  have hbase : Measurable (@baseBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_fst.comp (measurable_pi_apply e)
  have hadd : Measurable (@addedBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_snd.comp (measurable_pi_apply e)
  have hB (i : ι) : MeasurableSet (⋃ j, fullyOpenRegion (U i j)) :=
    MeasurableSet.iUnion fun j => bondSigma_le (localBonds (U i j)) _
      (measurableSet_fullyOpenRegion_localBond (U i j))
  haveI : IsProbabilityMeasure (bondPairLaw d q r) := by
    dsimp only [bondPairLaw]
    infer_instance
  apply condExp_indicator_lower_of_measurable_selection (bondPairLaw d q r)
    hbase.comap_le A (fun i => addedBondConfiguration ⁻¹' (⋃ j, fullyOpenRegion (U i j)))
    hA (fun i => hadd (hB i)) hC hG hcover hsubset
  intro i
  filter_upwards [condExp_indicator_added_event d q r (hB i)] with ω hω
  rw [hω]
  have hfail := measureReal_no_fullyOpenRegion_le r (U i) (hdisj i) ((r : ℝ) ^ N)
    (fun j => latticeBondLaw_real_fullyOpenRegion_lower r (U i j) (hU i j) N (hN i j))
    (Finset.univ : Finset (Fin n))
  have heq : (⋂ j ∈ (Finset.univ : Finset (Fin n)), (fullyOpenRegion (U i j))ᶜ) =
      (⋃ j, fullyOpenRegion (U i j))ᶜ := by
    ext ω
    simp only [Set.mem_iInter, Finset.mem_univ, true_implies, Set.mem_compl_iff,
      Set.mem_iUnion, not_exists]
  rw [heq, measureReal_compl (hB i), probReal_univ] at hfail
  simp only [Finset.card_univ, Fintype.card_fin] at hfail
  linarith

end Rigidity.Percolation

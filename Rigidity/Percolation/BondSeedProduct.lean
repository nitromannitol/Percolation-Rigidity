import Rigidity.Percolation.BondSeedFresh

/-!
# Adaptive seed exploration with a base field

A geometric survival estimate for each fixed base configuration lifts to the
joint law of the base and sprinkling fields.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped MeasureTheory

/-- A uniform real-valued bound on the sections of a measurable set bounds its
probability under a product of probability measures. -/
theorem measureReal_prod_le_of_sections {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {S : Set (α × β)}
    (hS : MeasurableSet S) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ x, ν.real (Prod.mk x ⁻¹' S) ≤ c) :
    (μ.prod ν).real S ≤ c := by
  have h : μ.prod ν S ≤ ENNReal.ofReal c := by
    rw [Measure.prod_apply hS]
    calc
      ∫⁻ x, ν (Prod.mk x ⁻¹' S) ∂μ ≤ ∫⁻ _, ENNReal.ofReal c ∂μ := by
        apply lintegral_mono
        intro x
        change ν (Prod.mk x ⁻¹' S) ≤ ENNReal.ofReal c
        have hb := ENNReal.ofReal_le_ofReal (hbound x)
        rw [ofReal_measureReal (measure_ne_top ν _)] at hb
        exact hb
      _ = ENNReal.ofReal c := by simp
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [measureReal_def, ENNReal.toReal_ofReal hc] using ht

/-- Uniform fresh-seed survival bounds hold after averaging over an arbitrary
independent base configuration. Each selection may depend on that full base
configuration and on the previously exposed added bonds. -/
theorem measureReal_prod_survival_le_of_fresh_seed_selection {d : ℕ} {ι : Type*}
    [Countable ι] (q r : unitInterval) (N : ℕ)
    (F : ℕ → Set (Bond d)) (U : Configuration d → ℕ → ι → Set (Vertex d))
    (hU : ∀ b n i, (U b n i).Finite)
    (hN : ∀ b n i, (finite_localBonds (hU b n i)).toFinset.card ≤ N)
    (hfresh : ∀ b n i, Disjoint (localBonds (U b n i)) (F n))
    (A : Configuration d → ℕ → ι → Set (Configuration d))
    (G : ℕ → Set (Configuration d × Configuration d))
    (C : Configuration d → ℕ → Set (Configuration d))
    (hA : ∀ b n i, MeasurableSet[bondSigma (F n)] (A b n i))
    (hG : ∀ n, MeasurableSet (G n))
    (hGsection : ∀ b n, MeasurableSet[bondSigma (F n)] (Prod.mk b ⁻¹' G n))
    (hC : ∀ b n, MeasurableSet (C b n))
    (hcover : ∀ b n, Prod.mk b ⁻¹' G n ⊆ ⋃ i, A b n i)
    (hsubset : ∀ b n i, A b n i ∩ fullyOpenRegion (U b n i) ⊆ C b n)
    (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hdisj : ∀ b n, Disjoint (Prod.mk b ⁻¹' G (n + 1)) (C b n)) :
    ∀ n, ((latticeBondLaw d q).prod (latticeBondLaw d r)).real (G n) ≤
      (1 - (r : ℝ) ^ N) ^ n := by
  intro n
  apply measureReal_prod_le_of_sections (latticeBondLaw d q) (latticeBondLaw d r)
    (hG n) (pow_nonneg (sub_nonneg.mpr (pow_le_one₀ r.property.1 r.property.2)) n)
  intro b
  exact measureReal_survival_le_of_fresh_seed_selection r N F (U b) (hU b) (hN b)
    (hfresh b) (A b) (fun n => Prod.mk b ⁻¹' G n) (C b) (hA b) (hGsection b)
    (hC b) (hcover b) (hsubset b) (fun n => Set.preimage_mono (hdecr n)) (hdisj b) n

/-- The paired-bond law assigns the same probability to an event expressed
in its two layers as the product law of those layers. -/
theorem bondPairLaw_real_layers_preimage (d : ℕ) (q r : unitInterval)
    {S : Set (Configuration d × Configuration d)} (hS : MeasurableSet S) :
    (bondPairLaw d q r).real
        ((fun ω => (baseBondConfiguration ω, addedBondConfiguration ω)) ⁻¹' S) =
      ((latticeBondLaw d q).prod (latticeBondLaw d r)).real S := by
  have hbase : Measurable (@baseBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_fst.comp (measurable_pi_apply e)
  have hadd : Measurable (@addedBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_snd.comp (measurable_pi_apply e)
  rw [← map_measureReal_apply_of_aemeasurable (hbase.prodMk hadd).aemeasurable hS,
    bondPairLaw_map_layers]

end Rigidity.Percolation

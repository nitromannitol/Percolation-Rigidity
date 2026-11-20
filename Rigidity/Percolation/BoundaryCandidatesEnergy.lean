import Rigidity.Percolation.BondClosingEnergy

/-!
# Finite energy for exterior-selected boundary candidates

If a family of boundary bonds is selected using only bonds outside the
boundary, closing every selected bond has a controlled probability cost.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory

/-- A boundary family selected without revealing boundary bonds satisfies
the finite-energy bound used to estimate the number of candidate exits. -/
theorem latticeBondLaw_few_boundaryCandidates_le_closed {d : ℕ} (p : unitInterval)
    (F : Set (Bond d)) (U : Configuration d → Finset (Bond d)) (t : ℕ)
    (hU : @Measurable _ _ (bondSigma Fᶜ) _ U)
    (hsub : ∀ ω, (↑(U ω) : Set (Bond d)) ⊆ F) :
    ENNReal.ofReal ((1 - (p : ℝ)) ^ t) *
      latticeBondLaw d p {ω | (U ω).card ≤ t} ≤
    latticeBondLaw d p {ω | ω ∈ allBondsClosed (U ω)} := by
  let A : Set (Configuration d) := {ω | (U ω).card ≤ t}
  have hcard : @Measurable _ _ (bondSigma Fᶜ) _ (fun ω => (U ω).card) :=
    (measurable_of_countable Finset.card).comp hU
  have hA : MeasurableSet[bondSigma Fᶜ] A :=
    hcard (Set.to_countable {n : ℕ | n ≤ t}).measurableSet
  have h := latticeBondLaw_finiteEnergy_close p Fᶜ U id t
    (fun b => hA.inter (hU (measurableSet_singleton b)))
    (by
      intro ω _
      rw [Set.disjoint_left]
      intro e he hec
      exact hec (hsub ω he))
    (by intro ω hω; exact hω)
  exact h.trans (measure_mono Set.inter_subset_right)

/-- When `p < 1`, the probability of at most `t` candidate exits is bounded
by the probability that every candidate bond is closed, divided by the
finite-energy factor. -/
theorem measureReal_few_boundaryCandidates_le {d : ℕ} (p : unitInterval)
    (hp : (p : ℝ) < 1) (F : Set (Bond d)) (U : Configuration d → Finset (Bond d))
    (t : ℕ) (hU : @Measurable _ _ (bondSigma Fᶜ) _ U)
    (hsub : ∀ ω, (↑(U ω) : Set (Bond d)) ⊆ F) :
    (latticeBondLaw d p).real {ω | (U ω).card ≤ t} ≤
      (latticeBondLaw d p).real {ω | ω ∈ allBondsClosed (U ω)} / (1 - (p : ℝ)) ^ t := by
  have h := latticeBondLaw_few_boundaryCandidates_le_closed p F U t hU hsub
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr p.property.2) _)] at hreal
  have hpos : 0 < (1 - (p : ℝ)) ^ t := pow_pos (sub_pos.mpr hp) _
  apply (le_div_iff₀ hpos).mpr
  simpa only [measureReal_def, mul_comm] using hreal

end Rigidity.Percolation

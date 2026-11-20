import Rigidity.Percolation.BondMarkIndependence

/-!
# Thresholds on exterior-selected bonds

A finite family of candidate bonds selected using exterior marks retains the
uniform product bound for raised thresholds on the candidate family.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Raise the thresholds by `δ` on a finite selected family. -/
noncomputable def raisedBondThreshold {d : ℕ} (β : Bond d → unitInterval)
    (δ : ℝ) (hδ : 0 ≤ δ) (hβ : ∀ e, (β e : ℝ) + δ ≤ 1)
    (s : Finset (Bond d)) (e : Bond d) : unitInterval :=
  if e ∈ s then ⟨(β e : ℝ) + δ, add_nonneg (β e).property.1 hδ, hβ e⟩ else β e

/-- If a candidate family is selected from exterior marks, the joint
probability of its having at least `t` members and all its raised-threshold
tests failing, together with the original boundary constraints, is at most
`(1 - δ)^t` times the probability of those constraints. -/
theorem bondMarkLaw_real_selected_raised_le {d : ℕ} (F : Finset (Bond d))
    (U : BondMarks d → Finset (Bond d))
    (hU : @Measurable _ _ (bondMarkSigma (↑F : Set (Bond d))ᶜ) _ U)
    (hsub : ∀ ω, U ω ⊆ F) (β : Bond d → unitInterval) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hβ : ∀ e, (β e : ℝ) + δ ≤ 1) (t : ℕ) :
    (bondMarkLaw d).real {ω | t ≤ (U ω).card ∧
      ω ∈ bondMarksAbove F (raisedBondThreshold β δ hδ hβ (U ω))} ≤
        (1 - δ) ^ t * (bondMarkLaw d).real (bondMarksAbove F β) := by
  classical
  haveI : IsProbabilityMeasure (bondMarkLaw d) := by
    dsimp only [bondMarkLaw]
    infer_instance
  let μ := bondMarkLaw d
  let S : Finset (Finset (Bond d)) := F.powerset.filter fun s => t ≤ s.card
  let A : Finset (Bond d) → Set (BondMarks d) := fun s => U ⁻¹' {s}
  let B : Finset (Bond d) → Set (BondMarks d) := fun s =>
    bondMarksAbove F (raisedBondThreshold β δ hδ hβ s)
  have hA : ∀ s, MeasurableSet[bondMarkSigma (↑F : Set (Bond d))ᶜ] (A s) :=
    fun s => hU (measurableSet_singleton s)
  have hpair : Set.PairwiseDisjoint (↑S : Set (Finset (Bond d))) A := by
    intro a _ b _ hab
    change Disjoint (A a) (A b)
    rw [Set.disjoint_left]
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have hsum : ∑ s ∈ S, μ.real (A s) ≤ 1 := by
    rw [← measureReal_biUnion_finset hpair
      (fun s _ => bondMarkSigma_le _ _ (hA s))]
    exact measureReal_le_one
  have hbranch : ∀ s ∈ S, μ.real (A s ∩ B s) ≤
      μ.real (A s) * ((1 - δ) ^ t * μ.real (bondMarksAbove F β)) := by
    intro s hs
    have hsF : s ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    have hst : t ≤ s.card := (Finset.mem_filter.mp hs).2
    have hdisj : Disjoint (↑F : Set (Bond d))ᶜ (↑F : Set (Bond d)) := by
      rw [Set.disjoint_left]
      intro e he hf
      exact he hf
    have hind := (Indep_iff _ _ _).mp (indep_bondMarkSigma hdisj) _ _ (hA s)
      (measurableSet_bondMarksAbove_local F (raisedBondThreshold β δ hδ hβ s))
    have hreal : μ.real (A s ∩ B s) = μ.real (A s) * μ.real (B s) := by
      change ((μ (A s ∩ B s)).toReal) = _
      rw [hind, ENNReal.toReal_mul]
      rfl
    rw [hreal]
    apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
    have hraise := bondMarkLaw_real_raised_thresholds_le F s hsF β δ hδ
      (fun e _ => hβ e)
    have hpows : (1 - δ) ^ s.card ≤ (1 - δ) ^ t :=
      pow_le_pow_of_le_one (sub_nonneg.mpr hδ1) (sub_le_self _ hδ) hst
    exact hraise.trans (mul_le_mul_of_nonneg_right hpows measureReal_nonneg)
  have hcover : {ω | t ≤ (U ω).card ∧ ω ∈ B (U ω)} ⊆ ⋃ s ∈ S, A s ∩ B s := by
    intro ω hω
    apply Set.mem_iUnion.mpr
    refine ⟨U ω, Set.mem_iUnion.mpr ⟨?_, rfl, hω.2⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hsub ω), hω.1⟩
  calc
    _ ≤ μ.real (⋃ s ∈ S, A s ∩ B s) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ s ∈ S, μ.real (A s ∩ B s) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ s ∈ S, μ.real (A s) * ((1 - δ) ^ t * μ.real (bondMarksAbove F β)) :=
      Finset.sum_le_sum hbranch
    _ = (∑ s ∈ S, μ.real (A s)) * ((1 - δ) ^ t * μ.real (bondMarksAbove F β)) := by
      rw [Finset.sum_mul]
    _ ≤ 1 * ((1 - δ) ^ t * μ.real (bondMarksAbove F β)) :=
      mul_le_mul_of_nonneg_right hsum (mul_nonneg (pow_nonneg (sub_nonneg.mpr hδ1) _) measureReal_nonneg)
    _ = _ := one_mul _

end Rigidity.Percolation

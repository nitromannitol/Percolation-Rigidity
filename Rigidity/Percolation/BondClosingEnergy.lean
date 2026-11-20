import Rigidity.Percolation.BondSeeds

/-!
# Finite energy for closing selected bonds

A bounded family of fresh bonds can be closed at a uniformly positive cost.
The family may depend on a countably valued statistic of the exposed field.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory

/-- Every bond in a finite family is closed. -/
def allBondsClosed {d : ℕ} (s : Finset (Bond d)) : Set (Configuration d) :=
  {ω | ∀ e ∈ s, ω e = false}

/-- The closed-bond event is measurable in the sigma algebra of those bonds. -/
theorem measurableSet_allBondsClosed {d : ℕ} (s : Finset (Bond d)) :
    MeasurableSet[bondSigma (s : Set (Bond d))] (allBondsClosed s) := by
  have heq : allBondsClosed s = ⋂ e ∈ s, {ω : Configuration d | ω e = true}ᶜ := by
    ext ω
    simp only [allBondsClosed, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    exact forall₂_congr fun e he => by cases h : ω e <;> simp
  rw [heq]
  exact s.measurableSet_biInter fun e he =>
    (bondSigma_mono (Set.singleton_subset_iff.mpr he) _ (measurableSet_bond_open e)).compl

/-- A finite family of bonds is entirely closed with probability `(1-p)^|s|`. -/
theorem latticeBondLaw_allBondsClosed {d : ℕ} (p : unitInterval) (s : Finset (Bond d)) :
    latticeBondLaw d p (allBondsClosed s) = ENNReal.ofReal (1 - (p : ℝ)) ^ s.card := by
  have heq : allBondsClosed s = (↑s : Set (Bond d)).pi (fun _ => ({false} : Set Bool)) := by
    ext ω
    simp only [allBondsClosed, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
      Set.mem_singleton_iff]
  have hpoint : (bernoulliMeasure true false p) {false} = ENNReal.ofReal (1 - (p : ℝ)) := by
    rw [bernoulliMeasure_apply_of_notMem_of_mem p (measurableSet_singleton false) (by simp)
      (by simp)]
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  rw [heq, latticeBondLaw, Measure.infinitePi_pi]
  · simp only [Finset.prod_const, hpoint]
  · exact fun _ _ => measurableSet_singleton false

/-- Closing at most `k` fresh bonds selected by an exposed statistic costs at
most the factor `(1-p)^k`. -/
theorem latticeBondLaw_finiteEnergy_close {d : ℕ} {β : Type*} [Countable β]
    (p : unitInterval) {A : Set (Configuration d)} (S : Set (Bond d))
    (Ψ : Configuration d → β) (φ : β → Finset (Bond d)) (k : ℕ)
    (hmeas : ∀ b, MeasurableSet[bondSigma S] (A ∩ Ψ ⁻¹' {b}))
    (hdisj : ∀ ω ∈ A, Disjoint (↑(φ (Ψ ω)) : Set (Bond d)) S)
    (hcard : ∀ ω ∈ A, (φ (Ψ ω)).card ≤ k) :
    ENNReal.ofReal ((1 - (p : ℝ)) ^ k) * latticeBondLaw d p A ≤
      latticeBondLaw d p (A ∩ {ω | ω ∈ allBondsClosed (φ (Ψ ω))}) := by
  classical
  have hA : A = ⋃ b, (A ∩ Ψ ⁻¹' {b}) := by
    ext ω
    simp
  have hAC : A ∩ {ω | ω ∈ allBondsClosed (φ (Ψ ω))} =
      ⋃ b, (A ∩ Ψ ⁻¹' {b}) ∩ allBondsClosed (φ b) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hω, hc⟩
      exact ⟨Ψ ω, ⟨hω, rfl⟩, hc⟩
    · rintro ⟨b, ⟨hω, rfl⟩, hc⟩
      exact ⟨hω, hc⟩
  have hdisjA : Pairwise (Function.onFun Disjoint fun b => A ∩ Ψ ⁻¹' {b}) := by
    intro b b' hbb'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, hb⟩ ⟨-, hb'⟩
    exact hbb' (hb.symm.trans hb')
  have hdisjAC : Pairwise (Function.onFun Disjoint
      fun b => (A ∩ Ψ ⁻¹' {b}) ∩ allBondsClosed (φ b)) := fun b b' hbb' =>
    (hdisjA hbb').mono Set.inter_subset_left Set.inter_subset_left
  have hterm : ∀ b, ENNReal.ofReal ((1 - (p : ℝ)) ^ k) *
      latticeBondLaw d p (A ∩ Ψ ⁻¹' {b}) ≤
      latticeBondLaw d p ((A ∩ Ψ ⁻¹' {b}) ∩ allBondsClosed (φ b)) := by
    intro b
    rcases (A ∩ Ψ ⁻¹' {b}).eq_empty_or_nonempty with hemp | ⟨ω₀, hω₀⟩
    · simp [hemp]
    · have hb : Ψ ω₀ = b := hω₀.2
      have hdj : Disjoint S (↑(φ b) : Set (Bond d)) := by
        have h := hdisj ω₀ hω₀.1
        rw [hb] at h
        exact h.symm
      have hk : (φ b).card ≤ k := by
        have h := hcard ω₀ hω₀.1
        rwa [hb] at h
      rw [(Indep_iff _ _ _).mp (indep_bondSigma p hdj) _ _ (hmeas b)
        (measurableSet_allBondsClosed (φ b)), latticeBondLaw_allBondsClosed, mul_comm]
      refine mul_le_mul_right ?_ _
      rw [← ENNReal.ofReal_pow (sub_nonneg.mpr p.property.2)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one (sub_nonneg.mpr p.property.2)
        (sub_le_self _ p.property.1) hk)
  have hmeasA : ∀ b, MeasurableSet (A ∩ Ψ ⁻¹' {b}) :=
    fun b => bondSigma_le S _ (hmeas b)
  have hmeasC : ∀ b, MeasurableSet ((A ∩ Ψ ⁻¹' {b}) ∩ allBondsClosed (φ b)) :=
    fun b => (hmeasA b).inter (bondSigma_le _ _ (measurableSet_allBondsClosed (φ b)))
  calc
    _ = ENNReal.ofReal ((1 - (p : ℝ)) ^ k) * ∑' b, latticeBondLaw d p (A ∩ Ψ ⁻¹' {b}) := by
      conv_lhs => rw [hA]
      rw [measure_iUnion hdisjA hmeasA]
    _ = ∑' b, ENNReal.ofReal ((1 - (p : ℝ)) ^ k) *
        latticeBondLaw d p (A ∩ Ψ ⁻¹' {b}) := by rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' b, latticeBondLaw d p ((A ∩ Ψ ⁻¹' {b}) ∩ allBondsClosed (φ b)) :=
      ENNReal.tsum_le_tsum hterm
    _ = _ := by rw [hAC, measure_iUnion hdisjAC hmeasC]

end Rigidity.Percolation

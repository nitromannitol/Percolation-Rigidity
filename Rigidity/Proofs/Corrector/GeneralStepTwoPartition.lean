import Rigidity.Proofs.Corrector.GeneralStepTwoWeightMeas
import Rigidity.Proofs.Corrector.DarioStepTwoPartition

/-!
# The partition of the good cubes of the summation of estimate (2) on `ℤᵈ`

A triadic cube fails to be a good cube of the summation of estimate (2) if its children fail the
Meyers estimate (Armstrong and Dario, (3.17), `exists_meyersFailureBound`) or if it fails the weight
bound with the exponent `q = (1 + ε/2)'` dual to the Meyers exponent. Given a stretched exponential
failure bound for the weight bound at every exponent `q ≥ 1` (`WeightFailureBound`), both failures
have stretched exponential probability in the side of the cube
(`exists_measure_not_mem_stepTwoGood_le_of_weightFailure`), so Proposition 2.1 of Armstrong and
Dario (`partition_estimates_general`) gives, almost surely, a partition of `ℤᵈ` into maximal good
cubes with stretched exponential moments of their sizes
(`exists_stepTwoGood_partition_of_weightFailure`).

This is the planar file `DarioStepTwoPartition` on `ℤᵈ`, `d ≥ 2`, with the failure bound of the
weight bound as a hypothesis: the planar file proves it (`exists_measure_not_weightGood_le`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ}

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The weight bound `Σ_T W^q ≤ M |T|` with exponent `q` fails on a triadic cube `T` with
probability at most `C₁ exp(−c (3ⁿ)^{s₀})`, `3ⁿ` the side of `T`, for some `M`. -/
def WeightFailureBound (p : unitInterval) (κ : ℕ) (q : ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∃ C1 c s0 : ℝ, 0 ≤ C1 ∧ 0 < c ∧ 0 < s0 ∧ ∀ (i : Fin d) (T : TriadicCube d),
    latticeBondLaw d p {ω | ¬ weightGood hG hGv κ i q M ω T} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0))

/-- **The failure bound for the good cubes of the summation of estimate (2)**, given the failure
bound of the weight bound. -/
theorem exists_measure_not_mem_stepTwoGood_le_of_weightFailure [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) {κ : ℕ}
    (hw : ∀ q : ℝ, 1 ≤ q → WeightFailureBound hG hGv p κ q) :
    ∃ ε CM M : ℝ, 0 < ε ∧ 0 ≤ CM ∧ 0 ≤ M ∧ ∃ C1 c s0 : ℝ, 0 ≤ C1 ∧ 0 < c ∧ 0 < s0 ∧
      ∀ (i : Fin d) (T : TriadicCube d),
        latticeBondLaw d p {ω | T ∉ stepTwoGood hG hGv κ i ε CM M ω} ≤
          ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)) := by
  obtain ⟨ε, CM, hε, hCM, C1, c, s0, hC1, hc, hs0, -, hfail⟩ :=
    Rigidity.Proofs.Cluster.GeneralDim.exists_meyersFailureBound hd hpc
  obtain ⟨M, hM, C1', c', s0', hC1', hc', hs0', hwf⟩ :=
    hw _ (Rigidity.Corrector.one_le_conjExponent hε)
  refine ⟨ε, CM, M, hε, hCM, hM, C1 + C1', min c c', min s0 s0', by positivity, lt_min hc hc',
    lt_min hs0 hs0', fun i T => ?_⟩
  have hX : 1 ≤ (3 : ℝ) ^ T.scale := one_le_pow₀ (by norm_num)
  have hsub : {ω | T ∉ stepTwoGood hG hGv κ i ε CM M ω} ⊆
      {ω | T ∉ Rigidity.Proofs.Cluster.GeneralDim.meyersGood ε CM ω} ∪
        {ω | ¬ weightGood hG hGv κ i (Real.conjExponent (1 + ε / 2)) M ω T} := by
    intro ω hω
    by_cases h : T ∈ Rigidity.Proofs.Cluster.GeneralDim.meyersGood ε CM ω
    · exact Or.inr fun hwg => hω ⟨h, hwg⟩
    · exact Or.inl h
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add (hfail T) (hwf i T)).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := Rigidity.Corrector.exp_neg_mul_rpow_le_of_le hX (min_le_left s0 s0')
    (lt_min hc hc').le (min_le_left c c')
  have h2 := Rigidity.Corrector.exp_neg_mul_rpow_le_of_le hX (min_le_right s0 s0')
    (lt_min hc hc').le (min_le_right c c')
  calc C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0) +
        C1' * Real.exp (-c' * ((3 : ℝ) ^ T.scale) ^ s0')
      ≤ C1 * Real.exp (-min c c' * ((3 : ℝ) ^ T.scale) ^ min s0 s0') +
        C1' * Real.exp (-min c c' * ((3 : ℝ) ^ T.scale) ^ min s0 s0') :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC1) (mul_le_mul_of_nonneg_left h2 hC1')
    _ = _ := by ring

/-- **The partition of the good cubes of the summation of estimate (2)** on `ℤᵈ` (Proposition 2.1
of Armstrong and Dario), given the failure bound of the weight bound, in place of the partition `𝒰`
of Definition 3.8 of Dario: almost surely every vertex lies in exactly one maximal good cube, and
the sizes of the cubes have stretched exponential moments. -/
theorem exists_stepTwoGood_partition_of_weightFailure [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {κ : ℕ}
    (hw : ∀ q : ℝ, 1 ≤ q → WeightFailureBound hG hGv p κ q) :
    ∃ ε CM M : ℝ, 0 < ε ∧ 0 ≤ CM ∧ 0 ≤ M ∧ ∃ s0 : ℝ, 0 < s0 ∧ ∀ i : Fin d,
      (∀ᵐ ω ∂latticeBondLaw d p, ∀ x : Vertex d, ∃! Q : TriadicCube d,
        x ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω)) ∧
      ∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
        Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize
          (stepTwoGood hG hGv κ i ε CM M ω) x / θ) ^ s0)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp ((TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) x / θ) ^ s0)
          ∂latticeBondLaw d p) ≤ 2 := by
  obtain ⟨ε, CM, M, hε, hCM, hM, C1, c, s0, hC1, hc, hs0, hfail⟩ :=
    exists_measure_not_mem_stepTwoGood_le_of_weightFailure hG hGv hd hpc hw
  refine ⟨ε, CM, M, hε, hCM, hM, s0, hs0, fun i => ?_⟩
  obtain ⟨hae, hmom, -⟩ := partition_estimates_general (d := d) (by omega)
    (latticeBondLaw d p) (stepTwoGood hG hGv κ i ε CM M)
    (measurableSet_mem_stepTwoGood hG hGv κ i ε CM M) hC1 hc hs0 (hfail i)
  exact ⟨hae, hmom⟩

end Grad

end Rigidity.Corrector.GeneralDim

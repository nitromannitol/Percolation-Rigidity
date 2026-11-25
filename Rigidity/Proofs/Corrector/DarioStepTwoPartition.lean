import Rigidity.Proofs.Corrector.DarioStepTwoWeightScale
import PercolationClusterHomogenization.Proofs.Partition.GeneralPartition

/-!
# The partition of the good cubes of the summation of estimate (2)

A triadic cube fails to be a good cube of the summation of estimate (2) if its children fail the
Meyers estimate (Armstrong and Dario, (3.17), `exists_meyersFailureBound`) or if it fails the weight
bound (`exists_measure_not_weightGood_le`, with the exponent `q = (1 + ε/2)'` dual to the Meyers
exponent). Both have stretched exponential probability in the side of the cube
(`exists_measure_not_mem_stepTwoGood_le`), so Proposition 2.1 of Armstrong and Dario
(`partition_estimates_general`) gives, almost surely, a partition of `ℤ²` into maximal good cubes
with stretched exponential moments of their sizes (`exists_stepTwoGood_partition`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem one_le_conjExponent {ε : ℝ} (hε : 0 < ε) : 1 ≤ Real.conjExponent (1 + ε / 2) := by
  unfold Real.conjExponent
  rw [show 1 + ε / 2 - 1 = ε / 2 by ring, le_div_iff₀ (by positivity)]
  linarith

theorem exp_neg_mul_rpow_le_of_le {X a b s t : ℝ} (hX : 1 ≤ X) (hts : t ≤ s) (hb0 : 0 ≤ b)
    (hb : b ≤ a) : Real.exp (-a * X ^ s) ≤ Real.exp (-b * X ^ t) := by
  rw [neg_mul, neg_mul]
  exact exp_neg_rpow_le_exp_neg_rpow hX hts hb0 hb

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The failure bound for the good cubes of the summation of estimate (2).** -/
theorem exists_measure_not_mem_stepTwoGood_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ ε CM M : ℝ, 0 < ε ∧ 0 ≤ CM ∧ 0 ≤ M ∧ ∃ C1 c s0 : ℝ, 0 ≤ C1 ∧ 0 < c ∧ 0 < s0 ∧
      ∀ (i : Fin 2) (T : TriadicCube 2),
        latticeBondLaw 2 p {ω | T ∉ stepTwoGood hG hGv κ i ε CM M ω} ≤
          ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)) := by
  obtain ⟨ε, CM, hε, hCM, C1, c, s0, hC1, hc, hs0, -, hfail⟩ :=
    GeneralDim.exists_meyersFailureBound (d := 2) le_rfl hpc
  obtain ⟨M, hM, C1', c', s0', hC1', hc', hs0', hw⟩ :=
    exists_measure_not_weightGood_le hG hGv hpc hp1 hGae hκ (one_le_conjExponent hε)
  refine ⟨ε, CM, M, hε, hCM, hM, C1 + C1', min c c', min s0 s0', by positivity, lt_min hc hc',
    lt_min hs0 hs0', fun i T => ?_⟩
  have hX : 1 ≤ (3 : ℝ) ^ T.scale := one_le_pow₀ (by norm_num)
  have hsub : {ω | T ∉ stepTwoGood hG hGv κ i ε CM M ω} ⊆
      {ω | T ∉ GeneralDim.meyersGood ε CM ω} ∪
        {ω | ¬ weightGood hG hGv κ i (Real.conjExponent (1 + ε / 2)) M ω T} := by
    intro ω hω
    by_cases h : T ∈ GeneralDim.meyersGood ε CM ω
    · exact Or.inr fun hwg => hω ⟨h, hwg⟩
    · exact Or.inl h
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add (hfail T) (hw i T)).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := exp_neg_mul_rpow_le_of_le hX (min_le_left s0 s0') (lt_min hc hc').le
    (min_le_left c c')
  have h2 := exp_neg_mul_rpow_le_of_le hX (min_le_right s0 s0') (lt_min hc hc').le
    (min_le_right c c')
  calc C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0) +
        C1' * Real.exp (-c' * ((3 : ℝ) ^ T.scale) ^ s0')
      ≤ C1 * Real.exp (-min c c' * ((3 : ℝ) ^ T.scale) ^ min s0 s0') +
        C1' * Real.exp (-min c c' * ((3 : ℝ) ^ T.scale) ^ min s0 s0') :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC1) (mul_le_mul_of_nonneg_left h2 hC1')
    _ = _ := by ring

/-- **The partition of the good cubes of the summation of estimate (2)** (Proposition 2.1 of
Armstrong and Dario), in place of the partition `𝒰` of Definition 3.8 of Dario: almost surely every
vertex lies in exactly one maximal good cube, and the sizes of the cubes have stretched exponential
moments. Dario's good cubes carry (3.30) and (3.31); here they carry the homogeneous Meyers estimate
on their children, from which `meyers_source` gives estimate (2) in place of (3.30), and the weight
bound of `exists_measure_not_weightGood_le` in place of (3.31). -/
theorem exists_stepTwoGood_partition {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ ε CM M : ℝ, 0 < ε ∧ 0 ≤ CM ∧ 0 ≤ M ∧ ∃ s0 : ℝ, 0 < s0 ∧ ∀ i : Fin 2,
      (∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x : Vertex 2, ∃! Q : TriadicCube 2,
        x ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω)) ∧
      ∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex 2,
        Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize
          (stepTwoGood hG hGv κ i ε CM M ω) x / θ) ^ s0)) (latticeBondLaw 2 p) ∧
        (∫ ω, Real.exp ((TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) x / θ) ^ s0)
          ∂latticeBondLaw 2 p) ≤ 2 := by
  obtain ⟨ε, CM, M, hε, hCM, hM, C1, c, s0, hC1, hc, hs0, hfail⟩ :=
    exists_measure_not_mem_stepTwoGood_le hG hGv hpc hp1 hGae hκ
  refine ⟨ε, CM, M, hε, hCM, hM, s0, hs0, fun i => ?_⟩
  obtain ⟨hae, hmom, -⟩ := partition_estimates_general (d := 2) (by norm_num)
    (latticeBondLaw 2 p) (stepTwoGood hG hGv κ i ε CM M)
    (measurableSet_mem_stepTwoGood hG hGv κ i ε CM M) hC1 hc hs0 (hfail i)
  exact ⟨hae, hmom⟩

end Grad

end Rigidity.Corrector

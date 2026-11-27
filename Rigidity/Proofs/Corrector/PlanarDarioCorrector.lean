import Rigidity.Proofs.Corrector.PlanarPartitionComparison

/-!
# Dario's Theorem 1 in dimension two from Theorem 2 at the origin

With the measurable corrector, the translated partitions and the coarsened correctors
(`coarseField`), the hypotheses of `DarioCoarsenedCorrectorTwo` other than Theorem 2 are proved:
the stationarity (2.3) (`linftyIterationData_recentred`), the comparison (5.7) of the translated
partitions (`baseComparison`) and the coarsening error (5.10) (`baseCoarseningError`), from the
qualitative corrector input `SupercriticalBondCorrectorInputTwo`, the order-zero regularity input
`ArmstrongDarioOrderZeroTwo` and the exponential moments of the partition sizes.

The remaining input of this reduction is the moment form (5.5) of Theorem 2 for the coarsened
corrector at the origin (`DarioTheoremTwoOriginTwo`), which Step 1 of the proof of Theorem 2
derives from the multiscale Poincaré inequality and Proposition 3.1
(`lintegral_boxOsc_le_of_poincare`). It follows from `DarioPoincareInputsTwo`
(`darioTheoremTwoOriginTwo_of_poincare`), which is established from the multiscale Poincaré
inequality (`multiscalePoincareTwo_holds`) and Proposition 3.1 in
`darioOptimalCorrectorTwo_of_prop31`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External
open scoped ENNReal

section Mono

variable {G : Set (Configuration 2)} {hG : MeasurableSet G} {hGv : G ⊆ correctorValidEvent 2}
  {p : unitInterval}

theorem rpow_le_rpow_of_exponent_le_mul {A k k' q : ℝ} (hA : 0 ≤ A) (hkk' : k ≤ k') (hq : 1 ≤ q) :
    (A * q ^ k) ^ q ≤ (A * q ^ k') ^ q :=
  Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hq hkk') hA) (by linarith)

theorem BaseTheoremTwo.mono_exponent {A k k' : ℝ} (hA : 0 ≤ A) (h : BaseTheoremTwo hG hGv p A k)
    (hkk' : k ≤ k') : BaseTheoremTwo hG hGv p A k' := fun i m hm q hq =>
  (h i m hm q hq).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (rpow_le_rpow_of_exponent_le_mul hA hkk' hq) (by positivity)))

theorem BaseComparison.mono_exponent {B k k' : ℝ} (hB : 0 ≤ B) (h : BaseComparison hG hGv p B k)
    (hkk' : k ≤ k') : BaseComparison hG hGv p B k' := fun i y' z q hq =>
  (h i y' z q hq).trans (ENNReal.ofReal_le_ofReal (rpow_le_rpow_of_exponent_le_mul hB hkk' hq))

end Mono

/-- **Theorem 2 of Dario at the origin for the coarsened correctors, in dimension two, moment
form** (a hypothesis of this reduction; (5.5)): on every measurable conull carrier of the
qualitative corrector input, the box oscillations of the coarsened correctors `coarseField i 0`
have moments `(A q^k)^q m^{q/2}`. -/
def DarioTheoremTwoOriginTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
      (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ A k : ℝ, 0 ≤ A ∧ BaseTheoremTwo hG hGv p A k

/-- `DarioCoarsenedCorrectorTwo` from the qualitative corrector input, the order-zero regularity
input and Theorem 2 at the origin. -/
theorem darioCoarsenedCorrectorTwo_of_orderZero (hR2 : SupercriticalBondCorrectorInputTwo)
    (hR3 : ArmstrongDarioOrderZeroTwo) (hT : DarioTheoremTwoOriginTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : DarioCoarsenedCorrectorTwo p := by
  obtain ⟨G, hG, hGae, hGv⟩ := exists_measurable_correctorValid_two hR2 hpc hp1
  obtain ⟨A, kT, hA, h2⟩ := hT p hpc hp1 G hG hGv hGae
  obtain ⟨B, kC, hB, -, hc⟩ := baseComparison hG hGv hR3 hpc hp1 hGae
  obtain ⟨s₆, C₆, hs₆, hC₆, h6⟩ := baseCoarseningError hG hGv hR3 hpc hp1 hGae
  exact darioCoarsenedCorrectorTwo_of_base hG hGv hpc hGae hA hB.le hs₆ hC₆
    (h2.mono_exponent hA (le_max_left kT kC)) (hc.mono_exponent hB.le (le_max_right kT kC)) h6

/-- **Dario's Theorem 1 in dimension two** (`DarioOptimalCorrectorTwo`) from the qualitative
corrector input (R2), the order-zero regularity input (R3) and Theorem 2 at the origin for the
coarsened correctors. -/
theorem darioOptimalCorrectorTwo_of_orderZero (hR2 : SupercriticalBondCorrectorInputTwo)
    (hR3 : ArmstrongDarioOrderZeroTwo) (hT : DarioTheoremTwoOriginTwo) :
    DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_coarsened
    (fun _ hpc hp1 => darioCoarsenedCorrectorTwo_of_orderZero hR2 hR3 hT hpc hp1) hR2

/-- Step 1 of the proof of Theorem 2 for the coarsened correctors: (5.5) from the multiscale
Poincaré inequality, Proposition 3.1 and the Lipschitz bound for smoothed gradients `S i`. -/
theorem baseTheoremTwo_of_poincare {G : Set (Configuration 2)} (hG : MeasurableSet G)
    (hGv : G ⊆ correctorValidEvent 2) {p : unitInterval}
    {S : Fin 2 → ℝ → Vertex 2 → Configuration 2 → ℝ} {A₀ C s : ℝ} (hA₀ : 0 < A₀) (hC : 0 < C)
    (hs : 0 < s) (hSm : ∀ i x, Measurable fun rω : ℝ × Configuration 2 => S i rω.1 x rω.2)
    (hS0 : ∀ i r x ω, 0 ≤ S i r x ω)
    (hmsp : ∀ i, PoincareCubeTwo p (coarseField hG hGv i 0) (S i) A₀)
    (h31 : ∀ i (r : ℝ), 1 ≤ r → ∀ x, IsOsBond 2 p (S i r x) s (C / r))
    (hlip : ∀ i (r : ℝ), 0 < r → r ≤ 1 → ∀ x, IsOsBond 2 p (S i r x) s C) :
    BaseTheoremTwo hG hGv p (poincareStepConst A₀ C s) (3 / 2 + 1 / s) := fun i _ hm _ hq =>
  lintegral_boxOsc_le_of_poincare hA₀ hC hs (fun z => measurable_coarseField hG hGv i 0 z)
    (hSm i) (hS0 i) (hmsp i) (h31 i) (hlip i) hm hq

/-- **The inputs of Step 1 of the proof of Theorem 2** for the coarsened correctors
(a hypothesis of this reduction; `darioOptimalCorrectorTwo_of_prop31` establishes it from
`MultiscalePoincareTwo` and `DarioPropThreeOneTwo`): smoothed gradients `S i r x` (standing for
`|Φ_{r²} * ∇[χ_{e_i}]_𝒫(x)|`) satisfying the multiscale Poincaré inequality (Proposition 2.19 in
cube form), Proposition 3.1 and the Lipschitz bound (2.22) for `r ≤ 1`. -/
def DarioPoincareInputsTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
      (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) →
      ∃ (S : Fin 2 → ℝ → Vertex 2 → Configuration 2 → ℝ) (A₀ C s : ℝ), 0 < A₀ ∧ 0 < C ∧ 0 < s ∧
        (∀ i x, Measurable fun rω : ℝ × Configuration 2 => S i rω.1 x rω.2) ∧
        (∀ i r x ω, 0 ≤ S i r x ω) ∧
        (∀ i, PoincareCubeTwo p (coarseField hG hGv i 0) (S i) A₀) ∧
        (∀ i (r : ℝ), 1 ≤ r → ∀ x, IsOsBond 2 p (S i r x) s (C / r)) ∧
        (∀ i (r : ℝ), 0 < r → r ≤ 1 → ∀ x, IsOsBond 2 p (S i r x) s C)

theorem darioTheoremTwoOriginTwo_of_poincare (h : DarioPoincareInputsTwo) :
    DarioTheoremTwoOriginTwo := by
  intro p hpc hp1 G hG hGv hGae
  obtain ⟨S, A₀, C, s, hA₀, hC, hs, hSm, hS0, hmsp, h31, hlip⟩ := h p hpc hp1 G hG hGv hGae
  refine ⟨poincareStepConst A₀ C s, 3 / 2 + 1 / s, ?_,
    baseTheoremTwo_of_poincare hG hGv hA₀ hC hs hSm hS0 hmsp h31 hlip⟩
  unfold poincareStepConst
  positivity

/-- **Dario's Theorem 1 in dimension two** from R2, R3 and the inputs of Step 1 of the proof of
Theorem 2 (the multiscale Poincaré inequality, Proposition 3.1 and the Lipschitz bound of the
smoothed gradients). -/
theorem darioOptimalCorrectorTwo_of_poincareInputs (hR2 : SupercriticalBondCorrectorInputTwo)
    (hR3 : ArmstrongDarioOrderZeroTwo) (h : DarioPoincareInputsTwo) : DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_orderZero hR2 hR3 (darioTheoremTwoOriginTwo_of_poincare h)

end Rigidity.Corrector

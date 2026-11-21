import Rigidity.Proofs.S2.DensityRealEncoding
import Rigidity.Proofs.S2.WeightedMomentHolder
import Rigidity.Proofs.S2.PowerRecursionAlgebra
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# Moment growth of the triadic cluster density in every dimension

If the moment roots of the single-bond influences are summable with sum `C r^{2γ} (3^m + 1)^d`,
the power-variance inequality and Hölder's inequality give the recursion
`‖X‖_{2n}^2 ≤ ‖X‖_n^2 + C n^{2γ+2} 3^{-dm}` for the centered density `X` of a triadic cube of size
`3^m`. Hence `‖X‖_n ≤ C n^{γ+1} 3^{-dm/2}` for every `n ≥ 1`, and `X` has geometric tails on the
grid of thresholds `C n^{γ+1} 3^{-dm/2}`.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

variable {d : ℕ} {p : unitInterval} {γ : ℕ}

/-- The density moments satisfy the spectral-gap power recursion. -/
theorem density_moment_recursion (h : DensityInfluenceRootBound d p (2 * γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m : ℕ) (k : Vertex d),
      let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
      let X := densityRealObservable p m k
      (∫ ω, |X ω| ^ (2 * n) ∂P) ≤ (∫ ω, |X ω| ^ n ∂P) ^ 2 +
        (C * (n : ℝ) ^ (2 * γ + 2) / (((3 ^ m : ℕ) : ℝ) ^ d)) *
          (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) := by
  obtain ⟨C, hC, hmom⟩ := density_conditional_influence_energy_moments h
  refine ⟨C, hC, fun n hn m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw d p
  let T := bernoulliRealConfiguration (d := d)
  let X := densityRealObservable p m k
  let W := densityConditionalInfluenceEnergy p m k
  let Y : (Bond d → ℝ) → ℝ := W ∘ T
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration d p
  have hXprop := density_real_observable_properties p m k
  have hXm : Measurable X := hXprop.1
  have hXb : ∀ ω, |X ω| ≤ 1 := hXprop.2.1
  have hWm : Measurable W := measurable_densityConditionalInfluenceEnergy p m k
  have hW0 (η : Configuration d) : 0 ≤ W η := densityConditionalInfluenceEnergy_nonneg p m k η
  obtain ⟨hWmem, hWnorm⟩ := hmom n (by omega) m k
  have hYmem : MemLp Y n P := by
    have h1 : MemLp W n (Measure.map T P) := by rw [hT.map_eq]; exact hWmem
    exact h1.comp_of_map hT.measurable.aemeasurable
  have hYnorm : lpNorm Y n P = lpNorm W n μ := by
    rw [← toReal_eLpNorm hYmem.aestronglyMeasurable,
      ← toReal_eLpNorm hWm.aestronglyMeasurable,
      eLpNorm_comp_measurePreserving hWm.aestronglyMeasurable hT]
  have hXnpow : MemLp (fun ω => X ω ^ n) 2 P := by
    refine MemLp.of_bound (hXm.pow_const n).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hXb ω)
  have hIntAbs : 0 ≤ ∫ ω, |X ω| ^ n ∂P := integral_nonneg fun _ => by positivity
  have hIntBound : |∫ ω, X ω ^ n ∂P| ≤ ∫ ω, |X ω| ^ n ∂P := by
    have h1 := norm_integral_le_integral_norm (μ := P) (fun ω => X ω ^ n)
    simpa only [Real.norm_eq_abs, abs_pow] using h1
  have hIntSq : (∫ ω, X ω ^ n ∂P) ^ 2 ≤ (∫ ω, |X ω| ^ n ∂P) ^ 2 := by
    have h1 := (sq_le_sq₀ (abs_nonneg _) hIntAbs).2 hIntBound
    simpa only [sq_abs] using h1
  have hPowEq (ω) : (X ω ^ n) ^ 2 = |X ω| ^ (2 * n) := by
    rw [← sq_abs, abs_pow, ← pow_mul, show n * 2 = 2 * n by omega]
  have hVar := density_power_variance_le h m k n
  dsimp only at hVar
  rw [variance_eq_sub hXnpow] at hVar
  have hIntEq : (∫ ω, (X ω ^ n) ^ 2 ∂P) = ∫ ω, |X ω| ^ (2 * n) ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hPowEq
  simp only [Pi.pow_apply] at hVar
  rw [hIntEq] at hVar
  change (∫ ω, |X ω| ^ (2 * n) ∂P) - (∫ ω, X ω ^ n ∂P) ^ 2 ≤
    (n : ℝ) ^ 2 * ∫ ω, |X ω| ^ (2 * (n - 1)) * Y ω ∂P at hVar
  have hHolder := weighted_moment_holder P X Y hXm hXb (fun ω => hW0 (T ω)) n hn hYmem
  have hM0 : 0 ≤ (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) :=
    Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  have hprod := mul_le_mul_of_nonneg_left (hYnorm ▸ hWnorm) hM0
  have hNN : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hest : (n : ℝ) ^ 2 * (∫ ω, |X ω| ^ (2 * (n - 1)) * Y ω ∂P) ≤
      (C * (n : ℝ) ^ (2 * γ + 2) / (((3 ^ m : ℕ) : ℝ) ^ d)) *
        (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) := by
    calc
      _ ≤ (n : ℝ) ^ 2 * ((∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) *
          lpNorm Y n P) := mul_le_mul_of_nonneg_left hHolder hNN
      _ ≤ (n : ℝ) ^ 2 * ((∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n) *
          (C * (n : ℝ) ^ (2 * γ) / (((3 ^ m : ℕ) : ℝ) ^ d))) :=
        mul_le_mul_of_nonneg_left hprod hNN
      _ = _ := by ring
  change (∫ ω, |X ω| ^ (2 * n) ∂P) ≤ (∫ ω, |X ω| ^ n ∂P) ^ 2 +
    (C * (n : ℝ) ^ (2 * γ + 2) / (((3 ^ m : ℕ) : ℝ) ^ d)) *
      (∫ ω, |X ω| ^ (2 * n) ∂P) ^ (((n : ℝ) - 1) / n)
  linarith

/-- The squared `Lⁿ` moment norm of the centered triadic density. -/
noncomputable def densityMomentRoot (p : unitInterval) (m : ℕ) (k : Vertex d) (n : ℕ) : ℝ :=
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  (∫ ω, |densityRealObservable p m k ω| ^ n ∂P) ^ (2 / (n : ℝ))

/-- Consecutive dyadic moment roots differ by at most the influence-energy bound. -/
theorem density_moment_root_recursion (h : DensityInfluenceRootBound d p (2 * γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m : ℕ) (k : Vertex d),
      densityMomentRoot p m k (2 * n) ≤ densityMomentRoot p m k n +
        C * (n : ℝ) ^ (2 * γ + 2) / (((3 ^ m : ℕ) : ℝ) ^ d) := by
  obtain ⟨C, hC, hrec⟩ := density_moment_recursion h
  refine ⟨C, hC, fun n hn m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let X := densityRealObservable p m k
  let A : ℝ := ∫ ω, |X ω| ^ (2 * n) ∂P
  let B : ℝ := ∫ ω, |X ω| ^ n ∂P
  let a : ℝ := A ^ (1 / (n : ℝ))
  let b : ℝ := B ^ (2 / (n : ℝ))
  let c : ℝ := C * (n : ℝ) ^ (2 * γ + 2) / (((3 ^ m : ℕ) : ℝ) ^ d)
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hA : 0 ≤ A := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ B := integral_nonneg fun _ => by positivity
  have hb : 0 ≤ b := Real.rpow_nonneg hB _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have haN : a ^ n = A := by
    dsimp only [a]
    simpa only [one_div] using Real.rpow_inv_natCast_pow hA hn0
  have hbN : b ^ n = B ^ 2 := by
    dsimp only [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    have h2 : (2 / (n : ℝ)) * n = 2 := by field_simp
    rw [h2, Real.rpow_two]
  have haPred : a ^ (n - 1) = A ^ (((n : ℝ) - 1) / n) := by
    dsimp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    congr 1
    ring
  have hpow : a ^ n ≤ b ^ n + c * a ^ (n - 1) := by
    rw [haN, hbN, haPred]
    exact hrec n hn m k
  have hroot := le_add_of_pow_le_pow_add_mul hb hc n (by omega) hpow
  have heq : densityMomentRoot p m k (2 * n) = a := by
    dsimp only [densityMomentRoot, a, A, X, P]
    congr 1
    push_cast
    field_simp
  change densityMomentRoot p m k (2 * n) ≤ b + c
  rw [heq]
  exact hroot

/-- The squared second-moment norm is bounded at inverse-volume scale. -/
theorem density_moment_root_two (h : DensityInfluenceRootBound d p (2 * γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex d),
      densityMomentRoot p m k 2 ≤ C / (((3 ^ m : ℕ) : ℝ) ^ d) := by
  obtain ⟨C, hC, hmom⟩ := density_conditional_influence_energy_moments h
  refine ⟨C, hC, fun m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw d p
  let T := bernoulliRealConfiguration (d := d)
  let X := densityRealObservable p m k
  let W := densityConditionalInfluenceEnergy p m k
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration d p
  have hWm : Measurable W := measurable_densityConditionalInfluenceEnergy p m k
  have hW0 (η : Configuration d) : 0 ≤ W η := densityConditionalInfluenceEnergy_nonneg p m k η
  have hWnorm : lpNorm W 1 μ ≤ C / (((3 ^ m : ℕ) : ℝ) ^ d) := by
    simpa using (hmom 1 (by norm_num) m k).2
  have hWint : (∫ η, W η ∂μ) = lpNorm W 1 μ := by
    rw [lpNorm_one_eq_integral_norm hWm.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun η => (Real.norm_of_nonneg (hW0 η)).symm
  have hmap : (∫ ω, W (T ω) ∂P) = ∫ η, W η ∂μ := by
    have hm : AEStronglyMeasurable W (Measure.map T P) := by
      rw [hT.map_eq]
      exact hWm.aestronglyMeasurable
    have h1 := integral_map hT.measurable.aemeasurable hm
    rw [hT.map_eq] at h1
    exact h1.symm
  have hXprop := density_real_observable_properties p m k
  have hV := density_power_variance_le h m k 1
  dsimp only at hV
  have hVar : variance X P = ∫ ω, X ω ^ 2 ∂P := by
    rw [variance_eq_integral hXprop.1.aemeasurable, hXprop.2.2.2]
    simp only [sub_zero]
    rfl
  have hM : densityMomentRoot p m k 2 = ∫ ω, X ω ^ 2 ∂P := by
    dsimp only [densityMomentRoot]
    norm_num
    rfl
  rw [hM, ← hVar]
  calc
    _ ≤ ∫ ω, W (T ω) ∂P := by simpa [X, W, T, P] using hV
    _ = ∫ η, W η ∂μ := hmap
    _ = lpNorm W 1 μ := hWint
    _ ≤ _ := hWnorm

/-- Dyadic squared moment norms grow at most like the power `2γ + 2` of the order. -/
theorem density_dyadic_moment_roots (h : DensityInfluenceRootBound d p (2 * γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j m : ℕ) (k : Vertex d),
      densityMomentRoot p m k (2 ^ (j + 1)) ≤
        C * (((2 ^ (j + 1) : ℕ) : ℝ) ^ (2 * γ + 2)) / (((3 ^ m : ℕ) : ℝ) ^ d) := by
  obtain ⟨A, hA, hbase⟩ := density_moment_root_two h
  obtain ⟨B, hB, hrec⟩ := density_moment_root_recursion h
  let C := A + B
  have hC : 0 < C := by dsimp [C]; positivity
  have htwo : (2 : ℝ) ≤ 2 ^ (2 * γ + 2) := by
    calc
      (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (2 * γ + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨C, hC, fun j m k => ?_⟩
  let v : ℝ := ((3 ^ m : ℕ) : ℝ) ^ d
  have hv : 0 < v := by dsimp [v]; positivity
  induction j with
  | zero =>
      have h0 := hbase m k
      change densityMomentRoot p m k 2 ≤ C * (((2 ^ (0 + 1) : ℕ) : ℝ) ^ (2 * γ + 2)) / v
      have hscale : A / v ≤ C * (((2 ^ (0 + 1) : ℕ) : ℝ) ^ (2 * γ + 2)) / v := by
        apply (div_le_div_iff_of_pos_right hv).2
        have h2 : (((2 ^ (0 + 1) : ℕ) : ℝ) ^ (2 * γ + 2)) = 2 ^ (2 * γ + 2) := by norm_num
        rw [h2]
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_left htwo (add_pos hA hB).le]
      exact h0.trans hscale
  | succ j ih =>
      let n : ℕ := 2 ^ (j + 1)
      have hn : 2 ≤ n := by
        dsimp [n]
        exact Nat.le_pow (by omega : 1 ≤ j + 1)
      have hstep := hrec n hn m k
      have hpow : (((2 ^ (j + 1 + 1) : ℕ) : ℝ) ^ (2 * γ + 2)) =
          (2 : ℝ) ^ (2 * γ + 2) * ((n : ℝ) ^ (2 * γ + 2)) := by
        rw [show 2 ^ (j + 1 + 1) = n * 2 from pow_succ 2 (j + 1), Nat.cast_mul, mul_pow]
        push_cast
        ring
      have hindex : 2 ^ (j + 1 + 1) = 2 * n := by
        dsimp [n]
        rw [pow_succ]
        omega
      change densityMomentRoot p m k (2 ^ (j + 1 + 1)) ≤
        C * (((2 ^ (j + 1 + 1) : ℕ) : ℝ) ^ (2 * γ + 2)) / v
      rw [hpow, hindex]
      have ih' : densityMomentRoot p m k n ≤ C * ((n : ℝ) ^ (2 * γ + 2)) / v := ih
      have hn0 : 0 ≤ (n : ℝ) ^ (2 * γ + 2) := by positivity
      calc
        _ ≤ densityMomentRoot p m k n + B * (n : ℝ) ^ (2 * γ + 2) / v := hstep
        _ ≤ C * (n : ℝ) ^ (2 * γ + 2) / v + B * (n : ℝ) ^ (2 * γ + 2) / v := add_le_add ih' le_rfl
        _ ≤ C * ((2 : ℝ) ^ (2 * γ + 2) * (n : ℝ) ^ (2 * γ + 2)) / v := by
          rw [← add_div]
          apply (div_le_div_iff_of_pos_right hv).2
          dsimp [C] at *
          nlinarith [mul_nonneg hA.le hn0, mul_nonneg hB.le hn0,
            mul_le_mul_of_nonneg_right htwo (mul_nonneg (add_pos hA hB).le hn0)]

/-- A density moment root is the square of its `Lⁿ` norm. -/
theorem density_moment_root_eq_lpNorm_sq (p : unitInterval) (m : ℕ) (k : Vertex d)
    (n : ℕ) (hn : 1 ≤ n) :
    let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
    densityMomentRoot p m k n = lpNorm (densityRealObservable p m k) n P ^ 2 := by
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let X := densityRealObservable p m k
  let M : ℝ := ∫ ω, |X ω| ^ n ∂P
  have hn0 : n ≠ 0 := by omega
  have hM : 0 ≤ M := integral_nonneg fun _ => by positivity
  have hm : Measurable X := (density_real_observable_properties p m k).1
  change M ^ (2 / (n : ℝ)) = lpNorm X n P ^ 2
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hn0)
    (ENNReal.natCast_ne_top n) hm.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
  change M ^ (2 / (n : ℝ)) = (M ^ (n : ℝ)⁻¹) ^ 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
  congr 1
  field_simp
  norm_num

/-- All squared moment norms grow at most like the power `2γ + 2` of the order. -/
theorem density_moment_roots (h : DensityInfluenceRootBound d p (2 * γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (k : Vertex d),
      densityMomentRoot p m k n ≤
        C * (n : ℝ) ^ (2 * γ + 2) / (((3 ^ m : ℕ) : ℝ) ^ d) := by
  obtain ⟨C, hC, hdyad⟩ := density_dyadic_moment_roots h
  refine ⟨C * (2 : ℝ) ^ (2 * γ + 2), by positivity, fun n hn m k => ?_⟩
  let j := Nat.log 2 n
  let N : ℕ := 2 ^ (j + 1)
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let X := densityRealObservable p m k
  let v : ℝ := ((3 ^ m : ℕ) : ℝ) ^ d
  have hn0 : n ≠ 0 := by omega
  have hnN : n ≤ N := by
    dsimp [N, j]
    exact (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n).le
  have hNle : N ≤ 2 * n := by
    dsimp [N, j]
    rw [pow_succ]
    have h1 := Nat.pow_log_le_self 2 hn0
    omega
  have hXm : Measurable X := (density_real_observable_properties p m k).1
  have hXb : ∀ ω, |X ω| ≤ 1 := (density_real_observable_properties p m k).2.1
  have hXN : MemLp X N P := by
    refine MemLp.of_bound hXm.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hXb ω
  have hnorm : lpNorm X n P ≤ lpNorm X N P := by
    rw [← toReal_eLpNorm hXm.aestronglyMeasurable,
      ← toReal_eLpNorm hXm.aestronglyMeasurable]
    exact ENNReal.toReal_mono hXN.2.ne
      (eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast hnN) hXm.aestronglyMeasurable)
  have hroot : densityMomentRoot p m k n ≤ densityMomentRoot p m k N := by
    rw [density_moment_root_eq_lpNorm_sq p m k n hn,
      density_moment_root_eq_lpNorm_sq p m k N (by omega)]
    exact pow_le_pow_left₀ lpNorm_nonneg hnorm 2
  have hpow : (N : ℝ) ^ (2 * γ + 2) ≤ (2 * (n : ℝ)) ^ (2 * γ + 2) := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg N)
    exact_mod_cast hNle
  have hv0 : 0 ≤ v := by positivity
  calc
    _ ≤ densityMomentRoot p m k N := hroot
    _ ≤ C * (N : ℝ) ^ (2 * γ + 2) / v := hdyad j m k
    _ ≤ C * (2 * (n : ℝ)) ^ (2 * γ + 2) / v :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) hv0
    _ = _ := by rw [mul_pow]; ring

/-- The centered density has `Lⁿ` norm at most `C n^{γ+1} 3^{-dm/2}`. -/
theorem density_moment_norms (h : DensityInfluenceRootBound d p (2 * γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (k : Vertex d),
      let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
      MemLp (densityRealObservable p m k) n P ∧
      lpNorm (densityRealObservable p m k) n P ≤
        C * (n : ℝ) ^ (γ + 1) / Real.sqrt ((((3 ^ m : ℕ) : ℝ)) ^ d) := by
  obtain ⟨C, hC, hmom⟩ := density_moment_roots h
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, fun n hn m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let X := densityRealObservable p m k
  let v : ℝ := ((3 ^ m : ℕ) : ℝ) ^ d
  let b : ℝ := Real.sqrt C * (n : ℝ) ^ (γ + 1) / Real.sqrt v
  have hv : 0 < v := by dsimp [v]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hXm : Measurable X := (density_real_observable_properties p m k).1
  have hXb : ∀ ω, |X ω| ≤ 1 := (density_real_observable_properties p m k).2.1
  have hXmem : MemLp X n P := by
    refine MemLp.of_bound hXm.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hXb ω
  have hsq : lpNorm X n P ^ 2 ≤ C * (n : ℝ) ^ (2 * γ + 2) / v := by
    rw [← density_moment_root_eq_lpNorm_sq p m k n hn]
    exact hmom n hn m k
  have hbSq : b ^ 2 = C * (n : ℝ) ^ (2 * γ + 2) / v := by
    dsimp only [b]
    rw [div_pow, mul_pow, Real.sq_sqrt hC.le, Real.sq_sqrt hv.le, ← pow_mul]
    ring
  refine ⟨hXmem, ?_⟩
  exact (sq_le_sq₀ lpNorm_nonneg hb).mp (by rwa [hbSq])

/-- The centered density has geometric tails on the grid of thresholds
`C n^{γ+1} 3^{-dm/2}`. -/
theorem density_moment_tail (h : DensityInfluenceRootBound d p (2 * γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (k : Vertex d),
      (Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p))
        {ω | C * (n : ℝ) ^ (γ + 1) / Real.sqrt ((((3 ^ m : ℕ) : ℝ)) ^ d) ≤
          |densityRealObservable p m k ω|} ≤ (1 / 2 : ℝ≥0∞) ^ n := by
  obtain ⟨C, hC, hmom⟩ := density_moment_norms h
  refine ⟨2 * C, by positivity, fun n hn m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let X := densityRealObservable p m k
  let w : ℝ := Real.sqrt ((((3 ^ m : ℕ) : ℝ)) ^ d)
  let N : ℝ := C * (n : ℝ) ^ (γ + 1) / w
  let t : ℝ := 2 * N
  have hn0 : n ≠ 0 := by omega
  have hp0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn0
  have hw : 0 < w := by dsimp [w]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨hX, hnorm⟩ := hmom n hn m k
  have hnorm' : eLpNorm X n P ≤ ENNReal.ofReal N := by
    rw [← ofReal_lpNorm hX]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hmark := meas_ge_le_mul_pow_eLpNorm_enorm P hp0 (ENNReal.natCast_ne_top n)
    hX.aestronglyMeasurable (ε := ENNReal.ofReal t) (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
    (by simp)
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast] at hmark
  have hevent : {ω | t ≤ |X ω|} = {ω | ENNReal.ofReal t ≤ ‖X ω‖ₑ} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  have htEq : t = 2 * C * (n : ℝ) ^ (γ + 1) / w := by dsimp [t, N]; ring
  change P {ω | 2 * C * (n : ℝ) ^ (γ + 1) / w ≤ |X ω|} ≤ _
  rw [← htEq, hevent]
  calc
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ n * eLpNorm X n P ^ n := hmark
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ n * (ENNReal.ofReal N) ^ n := by gcongr
    _ = (1 / 2 : ℝ≥0∞) ^ n := by
      rw [← mul_pow, ← ENNReal.ofReal_inv_of_pos ht,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
      have hhalf : t⁻¹ * N = (1 : ℝ) / 2 := by dsimp [t]; field_simp
      rw [hhalf]
      simp only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

end Rigidity.Proofs.S2

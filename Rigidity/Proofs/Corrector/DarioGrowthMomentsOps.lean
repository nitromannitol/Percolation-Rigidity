import Rigidity.Proofs.Corrector.DarioStepTwoPartition

/-!
# Operations on moments with polynomial growth

Moments `E[Y^q] ≤ (B q^κ)^q` for all `q ≥ 1` (`GrowthMoments`) pass to smaller variables and larger
constants (`GrowthMoments.mono`, `GrowthMoments.of_le`), to sums (`GrowthMoments.add`, constant
`2B`), to multiples (`GrowthMoments.const_mul`), and to products by the Cauchy–Schwarz inequality
(`GrowthMoments.mul`, constant `B B' 2^{κ+κ'}` and exponent `κ + κ'`). A nonnegative variable `X`
with `E[exp((X/θ)^s)] ≤ 2` has such moments with `B = 2θ (1/s)^{1/s}` and `κ = 1/s`
(`growthMoments_of_exp_moment`), since `y^a e^{-y} ≤ a^a`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

variable {p : unitInterval}

theorem GrowthMoments.mono {X Y : Configuration 2 → ℝ≥0∞} {B κ : ℝ} (h : GrowthMoments p Y B κ)
    (hle : ∀ ω, X ω ≤ Y ω) : GrowthMoments p X B κ := fun q hq =>
  (lintegral_mono fun ω => ENNReal.rpow_le_rpow (hle ω) (by linarith)).trans (h q hq)

theorem GrowthMoments.of_le {Y : Configuration 2 → ℝ≥0∞} {B κ B' κ' : ℝ}
    (h : GrowthMoments p Y B κ) (hB0 : 0 ≤ B) (hB : B ≤ B') (hκ : κ ≤ κ') :
    GrowthMoments p Y B' κ' := fun q hq => by
  refine (h q hq).trans (ENNReal.ofReal_le_ofReal ?_)
  have hq0 : 0 ≤ q := by linarith
  have h1 : q ^ κ ≤ q ^ κ' := Real.rpow_le_rpow_of_exponent_le hq hκ
  have h2 : B * q ^ κ ≤ B' * q ^ κ' :=
    mul_le_mul hB h1 (Real.rpow_nonneg hq0 κ) (hB0.trans hB)
  exact Real.rpow_le_rpow (mul_nonneg hB0 (Real.rpow_nonneg hq0 κ)) h2 hq0

theorem GrowthMoments.add {X Y : Configuration 2 → ℝ≥0∞} {B κ : ℝ} (hX : AEMeasurable X
    (latticeBondLaw 2 p)) (hgX : GrowthMoments p X B κ) (hgY : GrowthMoments p Y B κ)
    (hB : 0 ≤ B) : GrowthMoments p (fun ω => X ω + Y ω) (2 * B) κ := fun q hq => by
  have hq0 : 0 ≤ q := by linarith
  have h2 : (2 : ℝ≥0∞) ^ (q - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hY0 : 0 ≤ (B * q ^ κ) ^ q := Real.rpow_nonneg (by positivity) q
  calc ∫⁻ ω, (X ω + Y ω) ^ q ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ (q - 1) * (X ω ^ q + Y ω ^ q) ∂latticeBondLaw 2 p :=
        lintegral_mono fun ω => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
    _ = (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ ω, X ω ^ q ∂latticeBondLaw 2 p +
          ∫⁻ ω, Y ω ^ q ∂latticeBondLaw 2 p) := by
        rw [lintegral_const_mul' _ _ h2, lintegral_add_left' (hX.pow_const q)]
    _ ≤ (2 : ℝ≥0∞) ^ (q - 1) * (ENNReal.ofReal ((B * q ^ κ) ^ q) +
          ENNReal.ofReal ((B * q ^ κ) ^ q)) := by gcongr <;> [exact hgX q hq; exact hgY q hq]
    _ = ENNReal.ofReal ((2 * B * q ^ κ) ^ q) := by
        have e2 : (2 : ℝ≥0∞) ^ (q - 1) * 2 = 2 ^ q := by
          calc (2 : ℝ≥0∞) ^ (q - 1) * 2 = 2 ^ (q - 1) * 2 ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
            _ = 2 ^ (q - 1 + 1) := (ENNReal.rpow_add _ _ (by norm_num) (by norm_num)).symm
            _ = 2 ^ q := by rw [sub_add_cancel]
        have e3 : ENNReal.ofReal ((2 * B * q ^ κ) ^ q) =
            2 ^ q * ENNReal.ofReal ((B * q ^ κ) ^ q) := by
          rw [mul_assoc 2 B, Real.mul_rpow (by norm_num) (by positivity),
            ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq0]
          norm_num
        rw [e3, ← e2, ← two_mul, mul_assoc]

theorem GrowthMoments.const_mul {Y : Configuration 2 → ℝ≥0∞} {B κ c : ℝ}
    (h : GrowthMoments p Y B κ) (hc : 0 ≤ c) (hB : 0 ≤ B) :
    GrowthMoments p (fun ω => ENNReal.ofReal c * Y ω) (c * B) κ := fun q hq => by
  have hq0 : 0 ≤ q := by linarith
  have hcq : ENNReal.ofReal c ^ q ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top
  calc ∫⁻ ω, (ENNReal.ofReal c * Y ω) ^ q ∂latticeBondLaw 2 p
      = ENNReal.ofReal c ^ q * ∫⁻ ω, Y ω ^ q ∂latticeBondLaw 2 p := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hq0]
        exact lintegral_const_mul' _ _ hcq
    _ ≤ ENNReal.ofReal c ^ q * ENNReal.ofReal ((B * q ^ κ) ^ q) := by gcongr; exact h q hq
    _ = ENNReal.ofReal ((c * B * q ^ κ) ^ q) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hc hq0, ← ENNReal.ofReal_mul (by positivity),
          mul_assoc, Real.mul_rpow hc (by positivity)]

theorem GrowthMoments.mul {X Y : Configuration 2 → ℝ≥0∞} {B κ B' κ' : ℝ}
    (hX : AEMeasurable X (latticeBondLaw 2 p)) (hY : AEMeasurable Y (latticeBondLaw 2 p))
    (hgX : GrowthMoments p X B κ) (hgY : GrowthMoments p Y B' κ') (hB : 0 ≤ B) (hB' : 0 ≤ B') :
    GrowthMoments p (fun ω => X ω * Y ω) (B * B' * 2 ^ (κ + κ')) (κ + κ') := fun q hq => by
  have hq0 : 0 < q := by linarith
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (latticeBondLaw 2 p)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (hX.pow_const q) (hY.pow_const q)
  have hsq : ∀ (Z : Configuration 2 → ℝ≥0∞) (A k : ℝ), 0 ≤ A → GrowthMoments p Z A k →
      (∫⁻ ω, (Z ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw 2 p) ^ (1 / (2 : ℝ)) ≤
        ENNReal.ofReal ((A * (2 * q) ^ k) ^ q) := by
    intro Z A k hA hZ
    have e : ∀ ω, (Z ω ^ q) ^ (2 : ℝ) = Z ω ^ (2 * q) := fun ω => by
      rw [← ENNReal.rpow_mul, mul_comm]
    simp only [e]
    refine (ENNReal.rpow_le_rpow (hZ (2 * q) (by linarith)) (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul
      (by positivity), show 2 * q * (1 / 2) = q by ring]
  calc ∫⁻ ω, (X ω * Y ω) ^ q ∂latticeBondLaw 2 p
      = ∫⁻ ω, ((fun ω => X ω ^ q) * fun ω => Y ω ^ q) ω ∂latticeBondLaw 2 p := by
        refine lintegral_congr fun ω => ?_
        simp only [Pi.mul_apply]
        exact ENNReal.mul_rpow_of_nonneg _ _ hq0.le
    _ ≤ (∫⁻ ω, (X ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw 2 p) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, (Y ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw 2 p) ^ (1 / (2 : ℝ)) := hcs
    _ ≤ ENNReal.ofReal ((B * (2 * q) ^ κ) ^ q) * ENNReal.ofReal ((B' * (2 * q) ^ κ') ^ q) :=
        mul_le_mul' (hsq X B κ hB hgX) (hsq Y B' κ' hB' hgY)
    _ = ENNReal.ofReal ((B * B' * 2 ^ (κ + κ') * q ^ (κ + κ')) ^ q) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity)
          (by positivity)]
        congr 2
        rw [Real.mul_rpow (by norm_num) hq0.le, Real.mul_rpow (by norm_num) hq0.le,
          Real.rpow_add (by norm_num), Real.rpow_add hq0]
        ring

/-- **Moments with polynomial growth from a stretched exponential moment.** -/
theorem growthMoments_of_exp_moment {X : Configuration 2 → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) {θ s : ℝ}
    (hθ : 0 < θ) (hs : 0 < s)
    (hint : Integrable (fun ω => Real.exp ((X ω / θ) ^ s)) (latticeBondLaw 2 p))
    (hb : ∫ ω, Real.exp ((X ω / θ) ^ s) ∂latticeBondLaw 2 p ≤ 2) :
    GrowthMoments p (fun ω => ENNReal.ofReal (X ω)) (2 * θ * (1 / s) ^ (1 / s)) (1 / s) :=
    fun q hq => by
  have hq0 : 0 < q := by linarith
  set K : ℝ := θ ^ q * (q / s) ^ (q / s) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ ω, X ω ^ q ≤ K * Real.exp ((X ω / θ) ^ s) := by
    intro ω
    have hy0 : 0 ≤ (X ω / θ) ^ s := Real.rpow_nonneg (div_nonneg (hX0 ω) hθ.le) s
    have h := rpow_mul_exp_neg_le hy0 (by positivity : 0 < q / s) (c := 1) one_pos
    rw [div_one, one_mul] at h
    have e1 : X ω ^ q = θ ^ q * ((X ω / θ) ^ s) ^ (q / s) := by
      rw [← Real.rpow_mul (div_nonneg (hX0 ω) hθ.le), show s * (q / s) = q by field_simp,
        Real.div_rpow (hX0 ω) hθ.le]
      field_simp
    have e2 : ((X ω / θ) ^ s) ^ (q / s) = ((X ω / θ) ^ s) ^ (q / s) *
        Real.exp (-(X ω / θ) ^ s) * Real.exp ((X ω / θ) ^ s) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [e1, e2, hK, mul_assoc (θ ^ q)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hint' : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / θ) ^ s)) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hb
  calc ∫⁻ ω, ENNReal.ofReal (X ω) ^ q ∂latticeBondLaw 2 p
      = ∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂latticeBondLaw 2 p :=
        lintegral_congr fun ω => ENNReal.ofReal_rpow_of_nonneg (hX0 ω) hq0.le
    _ ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (Real.exp ((X ω / θ) ^ s))
          ∂latticeBondLaw 2 p := lintegral_mono fun ω => by
        rw [← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / θ) ^ s))
          ∂latticeBondLaw 2 p := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal 2 := by gcongr
    _ = ENNReal.ofReal (2 * K) := by rw [← ENNReal.ofReal_mul hK0, mul_comm]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : (2 : ℝ) ≤ 2 ^ q := by
          calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
            _ ≤ 2 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
        have e : (2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q = 2 ^ q * K := by
          rw [hK, Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hθ.le,
            ← Real.rpow_mul (by positivity), ← Real.rpow_mul hq0.le,
            Real.div_rpow hq0.le hs.le]
          rw [show 1 / s * q = q / s by ring, show q / s = q * (1 / s) by ring,
            Real.rpow_mul hq0.le, Real.div_rpow (by norm_num) hs.le, Real.one_rpow]
          rw [← Real.rpow_mul hq0.le, show q * (1 / s) = q / s by ring]
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_right h2 hK0

end Rigidity.Corrector

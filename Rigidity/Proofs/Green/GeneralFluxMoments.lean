import Rigidity.Proofs.Corrector.DarioGrowthMomentsOps

/-!
# Moments with polynomial growth on the bond configurations of `ℤ^d`

The extension of `DarioGrowthMomentsOps.lean` from `ℤ²` to `ℤ^d`: moments `E[Y^q] ≤ (B q^κ)^q` for
all `q ≥ 1` (`GrowthMomentsD`) pass to smaller variables and larger constants
(`GrowthMomentsD.mono`, `GrowthMomentsD.of_le`, `GrowthMomentsD.mono_ae`), to sums
(`GrowthMomentsD.add`, constant `2B`), to multiples (`GrowthMomentsD.const_mul`), and to products
by the Cauchy–Schwarz inequality (`GrowthMomentsD.mul`). A nonnegative variable `X` with
`E[exp((X/θ)^s)] ≤ 2` has such moments with `B = 2θ (1/s)^{1/s}` and `κ = 1/s`
(`growthMomentsD_of_exp_moment`, `growthMomentsD_of_isOsBond`).
-/

namespace Rigidity.Green.GeneralFlux

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Corrector Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ} {p : unitInterval}

/-- Moments with polynomial growth: `E[Y^q] ≤ (B q^κ)^q` for every `q ≥ 1`. -/
def GrowthMomentsD (p : unitInterval) (Y : Configuration d → ℝ≥0∞) (B κ : ℝ) : Prop :=
  ∀ q : ℝ, 1 ≤ q → ∫⁻ ω, Y ω ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal ((B * q ^ κ) ^ q)

theorem GrowthMomentsD.mono {X Y : Configuration d → ℝ≥0∞} {B κ : ℝ} (h : GrowthMomentsD p Y B κ)
    (hle : ∀ ω, X ω ≤ Y ω) : GrowthMomentsD p X B κ := fun q hq =>
  (lintegral_mono fun ω => ENNReal.rpow_le_rpow (hle ω) (by linarith)).trans (h q hq)

theorem GrowthMomentsD.of_le {Y : Configuration d → ℝ≥0∞} {B κ B' κ' : ℝ}
    (h : GrowthMomentsD p Y B κ) (hB0 : 0 ≤ B) (hB : B ≤ B') (hκ : κ ≤ κ') :
    GrowthMomentsD p Y B' κ' := fun q hq => by
  refine (h q hq).trans (ENNReal.ofReal_le_ofReal ?_)
  have hq0 : 0 ≤ q := by linarith
  have h1 : q ^ κ ≤ q ^ κ' := Real.rpow_le_rpow_of_exponent_le hq hκ
  have h2 : B * q ^ κ ≤ B' * q ^ κ' :=
    mul_le_mul hB h1 (Real.rpow_nonneg hq0 κ) (hB0.trans hB)
  exact Real.rpow_le_rpow (mul_nonneg hB0 (Real.rpow_nonneg hq0 κ)) h2 hq0

theorem GrowthMomentsD.add {X Y : Configuration d → ℝ≥0∞} {B κ : ℝ} (hX : AEMeasurable X
    (latticeBondLaw d p)) (hgX : GrowthMomentsD p X B κ) (hgY : GrowthMomentsD p Y B κ)
    (hB : 0 ≤ B) : GrowthMomentsD p (fun ω => X ω + Y ω) (2 * B) κ := fun q hq => by
  have hq0 : 0 ≤ q := by linarith
  have h2 : (2 : ℝ≥0∞) ^ (q - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hY0 : 0 ≤ (B * q ^ κ) ^ q := Real.rpow_nonneg (by positivity) q
  calc ∫⁻ ω, (X ω + Y ω) ^ q ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ (q - 1) * (X ω ^ q + Y ω ^ q) ∂latticeBondLaw d p :=
        lintegral_mono fun ω => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
    _ = (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ ω, X ω ^ q ∂latticeBondLaw d p +
          ∫⁻ ω, Y ω ^ q ∂latticeBondLaw d p) := by
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

theorem GrowthMomentsD.const_mul {Y : Configuration d → ℝ≥0∞} {B κ c : ℝ}
    (h : GrowthMomentsD p Y B κ) (hc : 0 ≤ c) (hB : 0 ≤ B) :
    GrowthMomentsD p (fun ω => ENNReal.ofReal c * Y ω) (c * B) κ := fun q hq => by
  have hq0 : 0 ≤ q := by linarith
  have hcq : ENNReal.ofReal c ^ q ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top
  calc ∫⁻ ω, (ENNReal.ofReal c * Y ω) ^ q ∂latticeBondLaw d p
      = ENNReal.ofReal c ^ q * ∫⁻ ω, Y ω ^ q ∂latticeBondLaw d p := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hq0]
        exact lintegral_const_mul' _ _ hcq
    _ ≤ ENNReal.ofReal c ^ q * ENNReal.ofReal ((B * q ^ κ) ^ q) := by gcongr; exact h q hq
    _ = ENNReal.ofReal ((c * B * q ^ κ) ^ q) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hc hq0, ← ENNReal.ofReal_mul (by positivity),
          mul_assoc, Real.mul_rpow hc (by positivity)]

theorem GrowthMomentsD.mul {X Y : Configuration d → ℝ≥0∞} {B κ B' κ' : ℝ}
    (hX : AEMeasurable X (latticeBondLaw d p)) (hY : AEMeasurable Y (latticeBondLaw d p))
    (hgX : GrowthMomentsD p X B κ) (hgY : GrowthMomentsD p Y B' κ') (hB : 0 ≤ B) (hB' : 0 ≤ B') :
    GrowthMomentsD p (fun ω => X ω * Y ω) (B * B' * 2 ^ (κ + κ')) (κ + κ') := fun q hq => by
  have hq0 : 0 < q := by linarith
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (latticeBondLaw d p)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (hX.pow_const q) (hY.pow_const q)
  have hsq : ∀ (Z : Configuration d → ℝ≥0∞) (A k : ℝ), 0 ≤ A → GrowthMomentsD p Z A k →
      (∫⁻ ω, (Z ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw d p) ^ (1 / (2 : ℝ)) ≤
        ENNReal.ofReal ((A * (2 * q) ^ k) ^ q) := by
    intro Z A k hA hZ
    have e : ∀ ω, (Z ω ^ q) ^ (2 : ℝ) = Z ω ^ (2 * q) := fun ω => by
      rw [← ENNReal.rpow_mul, mul_comm]
    simp only [e]
    refine (ENNReal.rpow_le_rpow (hZ (2 * q) (by linarith)) (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul
      (by positivity), show 2 * q * (1 / 2) = q by ring]
  calc ∫⁻ ω, (X ω * Y ω) ^ q ∂latticeBondLaw d p
      = ∫⁻ ω, ((fun ω => X ω ^ q) * fun ω => Y ω ^ q) ω ∂latticeBondLaw d p := by
        refine lintegral_congr fun ω => ?_
        simp only [Pi.mul_apply]
        exact ENNReal.mul_rpow_of_nonneg _ _ hq0.le
    _ ≤ (∫⁻ ω, (X ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw d p) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, (Y ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw d p) ^ (1 / (2 : ℝ)) := hcs
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
theorem growthMomentsD_of_exp_moment {X : Configuration d → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) {θ s : ℝ}
    (hθ : 0 < θ) (hs : 0 < s)
    (hint : Integrable (fun ω => Real.exp ((X ω / θ) ^ s)) (latticeBondLaw d p))
    (hb : ∫ ω, Real.exp ((X ω / θ) ^ s) ∂latticeBondLaw d p ≤ 2) :
    GrowthMomentsD p (fun ω => ENNReal.ofReal (X ω)) (2 * θ * (1 / s) ^ (1 / s)) (1 / s) :=
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
  have hint' : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / θ) ^ s)) ∂latticeBondLaw d p ≤
      ENNReal.ofReal 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hb
  calc ∫⁻ ω, ENNReal.ofReal (X ω) ^ q ∂latticeBondLaw d p
      = ∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂latticeBondLaw d p :=
        lintegral_congr fun ω => ENNReal.ofReal_rpow_of_nonneg (hX0 ω) hq0.le
    _ ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (Real.exp ((X ω / θ) ^ s))
          ∂latticeBondLaw d p := lintegral_mono fun ω => by
        rw [← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / θ) ^ s))
          ∂latticeBondLaw d p := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
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

theorem GrowthMomentsD.mono_ae {X Y : Configuration d → ℝ≥0∞} {B κ : ℝ}
    (h : GrowthMomentsD p Y B κ) (hle : ∀ᵐ ω ∂latticeBondLaw d p, X ω ≤ Y ω) :
    GrowthMomentsD p X B κ := fun q hq =>
  (lintegral_mono_ae (hle.mono fun _ h => ENNReal.rpow_le_rpow h (by linarith))).trans (h q hq)

theorem growthMomentsD_of_isOsBond {X : Configuration d → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) {s θ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (h : IsOsBond d p X s θ) :
    GrowthMomentsD p (fun ω => ENNReal.ofReal (X ω)) (2 * θ * (1 / s) ^ (1 / s)) (1 / s) := by
  have e : (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) =
      fun ω => Real.exp ((X ω / θ) ^ s) := by
    funext ω
    rw [max_eq_left (div_nonneg (hX0 ω) hθ.le)]
    rfl
  obtain ⟨h1, h2⟩ := h
  rw [e] at h1 h2
  exact growthMomentsD_of_exp_moment hX0 hθ hs h1 h2

end Rigidity.Green.GeneralFlux

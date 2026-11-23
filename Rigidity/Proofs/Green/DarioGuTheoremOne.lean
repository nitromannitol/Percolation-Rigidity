import Rigidity.Proofs.Green.DarioGuStep

/-!
# Theorem 1 of Dario–Gu in dimension two from the results of §3–§4 and Appendix A

The proof of §4.3 of Dario–Gu: the statement (4.45) holds at exponent `0` by Theorem 4 (Barlow)
and the Gaussian bound (`heatLevel_zero`); the iteration step (`heatLevel_step`) improves the
exponent `k` to `min((1 - κ) k + κ/2, 1/2 - δ)` (the recursion (4.43), here started at `k = 0`,
whose first step is `κ_0 = κ/2`); after finitely many steps the exponent is `1/2 - δ`
(`exists_dgKappa_ge`), which is Theorem 1 (`darioGuHeatKernelTwo_of_sections`).

Hypotheses: the results of §4.1–§4.2 and Proposition A.7 (`DarioGuSectionFourTwo`), Theorem 4
(`BarlowGaussianUpperBoundTwo`, cited), Proposition 2.15 (`CarneVaropoulosTwo`, cited) and the
qualitative corrector input (`SupercriticalBondCorrectorInputTwo`, for the normalized correctors
of §2.3.1).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Green

variable {p : unitInterval}

/-- The exponents `k_0 = 0`, `k_{n+1} = min((1 - δ/4) k_n + δ/8, 1/2 - δ)` ((4.43), shifted). -/
noncomputable def dgKappa (δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => min ((1 - δ / 4) * dgKappa δ n + δ / 4 / 2) (1 / 2 - δ)

theorem dgKappa_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (n : ℕ) : 0 ≤ dgKappa δ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [dgKappa]
    exact le_min (by nlinarith) (by linarith)

theorem dgKappa_le {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (n : ℕ) : dgKappa δ n ≤ 1 / 2 - δ := by
  cases n with
  | zero => simp only [dgKappa]; linarith
  | succ n => exact min_le_right _ _

theorem le_dgKappa {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (n : ℕ) :
    min ((1 - (1 - δ / 4) ^ n) / 2) (1 / 2 - δ) ≤ dgKappa δ n := by
  induction n with
  | zero => simp only [dgKappa, pow_zero, sub_self, zero_div]; exact min_le_left _ _
  | succ n ih =>
    simp only [dgKappa]
    have hκ : 0 ≤ 1 - δ / 4 := by linarith
    have hu : (1 - (1 - δ / 4) ^ (n + 1)) / 2 =
        (1 - δ / 4) * ((1 - (1 - δ / 4) ^ n) / 2) + δ / 4 / 2 := by ring
    apply le_min _ (min_le_right _ _)
    rcases le_total ((1 - (1 - δ / 4) ^ n) / 2) (1 / 2 - δ) with h | h
    · rw [min_eq_left h] at ih
      calc min ((1 - (1 - δ / 4) ^ (n + 1)) / 2) (1 / 2 - δ)
          ≤ (1 - (1 - δ / 4) ^ (n + 1)) / 2 := min_le_left _ _
        _ = (1 - δ / 4) * ((1 - (1 - δ / 4) ^ n) / 2) + δ / 4 / 2 := hu
        _ ≤ (1 - δ / 4) * dgKappa δ n + δ / 4 / 2 :=
          add_le_add_left (mul_le_mul_of_nonneg_left ih hκ) _
    · rw [min_eq_right h] at ih
      calc min ((1 - (1 - δ / 4) ^ (n + 1)) / 2) (1 / 2 - δ) ≤ 1 / 2 - δ := min_le_right _ _
        _ ≤ (1 - δ / 4) * (1 / 2 - δ) + δ / 4 / 2 := by nlinarith
        _ ≤ (1 - δ / 4) * dgKappa δ n + δ / 4 / 2 :=
          add_le_add_left (mul_le_mul_of_nonneg_left ih hκ) _

theorem exists_dgKappa_ge {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∃ n, 1 / 2 - δ ≤ dgKappa δ n := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 2 * δ)
    (by linarith : 1 - δ / 4 < 1)
  refine ⟨n, le_trans ?_ (le_dgKappa hδ hδ4 n)⟩
  apply le_min _ le_rfl
  linarith

theorem HeatLevel.mono_exponent {σ c k k' : ℝ} {T : Vertex 2 → Configuration 2 → ℝ}
    (h : HeatLevel p σ c k T) (hc : 0 < c) (hkk : k' ≤ k) : HeatLevel p σ c k' T := by
  filter_upwards [h] with ω hω
  intro hu z hz t ht hT x hx
  refine (hω hu z hz t ht hT x hx).trans ?_
  have ht0 : 0 < t := by linarith
  apply mul_le_mul_of_nonneg_right _ (dgPhi_nonneg hc.le ht0.le _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) hc.le

/-- **(4.45) at exponent `0`**, from Theorem 4 and the Gaussian bound. -/
theorem heatLevel_zero (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hσ : 0 < σ) (hBar : BarlowGaussianUpperBoundTwo) :
    ∃ c, 0 < c ∧ ∃ T, GoodTimes p T ∧ HeatLevel p σ c 0 T := by
  set θ := theta 2 p
  have hθ : 0 < θ := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨sB, CB, hsB, hCB, hB'⟩ := hBar p hpc hp1
  choose TB hTBm hTB0 hTBos hTBae using hB'
  set CG := max (2 * σ) (θ⁻¹ / (2 * Real.pi * σ))
  have hCG : 0 < CG := lt_max_of_lt_left (by positivity)
  set c := 2 * max (max CB CG) 1
  have hc : 0 < c := by positivity
  refine ⟨c, hc, TB, goodTimes_of_isOsBond hsB hCB hTBm hTB0 hTBos, ?_⟩
  filter_upwards [ae_all_iff.2 hTBae] with ω hω
  intro h z hz t ht hT x hx
  have ht0 : 0 < t := by linarith
  have hr := latticeDist_nonneg x z
  have hP := hω z h hz t ht0 hT x hx
  have hP0 : 0 ≤ openHeat ω t x z := openHeat_nonneg' ω ht0.le x z
  have hG : θ⁻¹ * latticeGaussian σ t x z ≤ dgPhi CG t (latticeDist x z) :=
    const_mul_latticeGaussian_le_dgPhi (c := θ⁻¹) hσ ht0 (le_max_left _ _) (le_max_right _ _) x z
  have hG0 : 0 ≤ θ⁻¹ * latticeGaussian σ t x z := by
    have := latticeGaussian_pos hσ ht0 x z; positivity
  have hm1 : 1 ≤ max (max CB CG) 1 := le_max_right _ _
  have hmax : max CB CG ≤ c := by
    have := le_max_left (max CB CG) 1
    simp only [c]; linarith
  have h1 : dgPhi CB t (latticeDist x z) ≤ dgPhi c t (latticeDist x z) :=
    dgPhi_mono hCB ((le_max_left _ _).trans hmax) ht0 hr
  have h2 : dgPhi CG t (latticeDist x z) ≤ dgPhi c t (latticeDist x z) :=
    dgPhi_mono hCG ((le_max_right _ _).trans hmax) ht0 hr
  have hφ := dgPhi_nonneg hc.le ht0.le (latticeDist x z)
  have hc2 : 2 ≤ c := by simp only [c]; linarith
  rw [neg_zero, Real.rpow_zero, mul_one]
  calc |openHeat ω t x z - θ⁻¹ * latticeGaussian σ t x z|
      ≤ openHeat ω t x z + θ⁻¹ * latticeGaussian σ t x z := by
        rw [abs_le]; constructor <;> linarith
    _ ≤ dgPhi c t (latticeDist x z) + dgPhi c t (latticeDist x z) := by linarith
    _ ≤ c * dgPhi c t (latticeDist x z) := by nlinarith

/-- `H` at every exponent `k_n`. -/
theorem heatLevel_iterate (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hσ : 0 < σ) (hSec : DarioGuSectionFourTwo p σ) (hBar : BarlowGaussianUpperBoundTwo)
    (hCV : CarneVaropoulosTwo) (hCorr : SupercriticalBondCorrectorInputTwo) {δ : ℝ}
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (n : ℕ) :
    ∃ c, 0 < c ∧ ∃ T, GoodTimes p T ∧ HeatLevel p σ c (dgKappa δ n) T := by
  induction n with
  | zero => exact heatLevel_zero hpc hp1 hσ hBar
  | succ n ih =>
    obtain ⟨c, hc, T, hT, hH⟩ := ih
    exact heatLevel_step hpc hp1 hσ hSec hBar hCV hCorr hδ hδ4 hc (dgKappa_nonneg hδ hδ4 n)
      (dgKappa_le hδ hδ4 n) hT hH

/-- **Dario–Gu, Theorem 1** in dimension two (`DarioGuHeatKernelTwo`, as stated by rigr57), from
the results of §4.1–§4.2 and Proposition A.7 for some diffusivity `σ > 0`, Theorem 4 (Barlow),
Proposition 2.15 (Carne–Varopoulos) and the qualitative corrector input. -/
theorem darioGuHeatKernelTwo_of_sections
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuSectionFourTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hCorr : SupercriticalBondCorrectorInputTwo) : DarioGuHeatKernelTwo := by
  intro p hpc hp1
  obtain ⟨σ, hσ, hS⟩ := hSec p hpc hp1
  refine ⟨σ, hσ, fun δ hδ => ?_⟩
  set δ' := min δ (1 / 4) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'4 : δ' ≤ 1 / 4 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  obtain ⟨n, hn⟩ := exists_dgKappa_ge hδ'0 hδ'4
  obtain ⟨c, hc, T, ⟨hTm, hT0, Ct, st, hCt, hst, hTt⟩, hH⟩ :=
    heatLevel_iterate hpc hp1 hσ hS hBar hCV hCorr hδ'0 hδ'4 n
  have hH' := hH.mono_exponent hc hn
  set C := max (max Ct (c * c)) c with hC
  have hC0 : 0 < C := lt_max_of_lt_right hc
  refine ⟨C, st, hC0, hst, fun y => ⟨T y, hTm y, hT0 y,
    fun R hR => (hTt y).mono (by linarith) ((le_max_left _ _).trans (le_max_left _ _)) R hR, ?_⟩⟩
  filter_upwards [hH'] with ω hω
  intro h hy x hx t ht1 hTt' hdist
  have ht0 : 0 < t := by linarith
  have hb := hω h y hy t ht1 hTt' x hx
  have hd : latticeDist x y ≤ t := hdist
  have hphi : dgPhi c t (latticeDist x y) =
      c * t⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (c * t))) := by
    simp only [dgPhi, dgExponent, if_pos hd]
  rw [hphi] at hb
  change |openHeat ω t x y - (theta 2 p)⁻¹ * latticeGaussian σ t x y| ≤ _
  refine hb.trans ?_
  have hcC : c ≤ C := le_max_right _ _
  have hc2 : c * c ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hexp : Real.exp (-(latticeDist x y ^ 2 / (c * t))) ≤
      Real.exp (-(latticeDist x y ^ 2 / (C * t))) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have hpow : t ^ (-(1 / 2 - δ')) * t⁻¹ ≤ t ^ (-1 - (1 / 2 - δ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hE := Real.exp_pos (-(latticeDist x y ^ 2 / (c * t)))
  calc c * t ^ (-(1 / 2 - δ')) * (c * t⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (c * t))))
      = (c * c) * (t ^ (-(1 / 2 - δ')) * t⁻¹) * Real.exp (-(latticeDist x y ^ 2 / (c * t))) := by
        ring
    _ ≤ C * t ^ (-1 - (1 / 2 - δ)) * Real.exp (-(latticeDist x y ^ 2 / (C * t))) := by
        gcongr

end Rigidity.Green

import Rigidity.Proofs.Green.PointSourceInputsD

/-!
# The tails of the differences from the Carne–Varopoulos bound

With the two branches of the Carne–Varopoulos bound with constant `C` from every point of `K`
(`CVBranches`), `l = √s L` and the Gaussian masses `M_s, M_{3s} ≥ θ/2`:

* `tsum_out_gaussFlowDiff_le_of_cv`: `Σ_{x ∉ V_l(y)} |D_s(x)| ≤ C (4πCs)^{d/2} M_C e^{-L²/(16C)} +
  C E_C e^{-s/C} + (2/θ) 2^{d/2} M_σ (e^{-L²/(16σ)} + e^{-L²/(12σ)})`;
* `tsum_out_initialError_le_of_cv`: `Σ_{x ∉ V_l(y)} |E(x)| ≤ C (2πCs)^{d/2} M_C e^{-L²/(2C)} +
  C E_C e^{-s/(2C)} + (2/θ) 2^{d/2} M_σ e^{-L²/(4σ)}`.
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.WeakPoincare

namespace Rigidity.Green

local notation "ldist" => Rigidity.WeakPoincare.latticeDist

variable {d : ℕ} [NeZero d] {ω : Configuration d}

/-- The two branches of the Carne–Varopoulos bound with constant `C` at time `u` from `w`. -/
def CVBranches (ω : Configuration d) (C u : ℝ) (w : Vertex d) : Prop :=
  ∀ x, vsrwHeat (openGraph ω) (2 * d) u w x ≤
    C * Real.exp (-(ldist x w ^ 2 / (C * u))) +
      (if u ≤ ldist x w then C * Real.exp (-(ldist x w / C)) else 0)

variable {K : OpenComponent ω} {σ θ : ℝ} {y : Vertex d}

theorem inv_le_two_div_of_half_le {M θ : ℝ} (hθ : 0 < θ) (hM : θ / 2 ≤ M) : M⁻¹ ≤ 2 / θ := by
  have hM0 : 0 < M := by linarith
  rw [inv_le_comm₀ hM0 (by positivity)]; field_simp; linarith

/-- **The tail of `D_s`.** -/
theorem tsum_out_gaussFlowDiff_le_of_cv (hσ : 0 < σ) (hθ : 0 < θ) {s L C : ℝ} (hs : 1 ≤ s)
    (hL : 0 ≤ L) (hC : 0 < C) (hcv : ∀ w ∈ K.supp, CVBranches ω C (2 * s) w)
    (hM1 : θ / 2 ≤ clusterGaussMass K σ s y) (hM3 : θ / 2 ≤ clusterGaussMass K σ (3 * s) y) :
    ∑' x, (if x ∈ clusterBall K y (Real.sqrt s * L) then 0 else |gaussFlowDiff K σ s y x|) ≤
      C * (4 * Real.pi * C * s) ^ ((d : ℝ) / 2) * gaussMassBoundD d C *
          Real.exp (-(L ^ 2 / (16 * C))) + C * expMassBoundD d C * Real.exp (-(s / C)) +
        2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
          (Real.exp (-(L ^ 2 / (16 * σ))) + Real.exp (-(L ^ 2 / (12 * σ)))) := by
  have hs0 : 0 < s := by linarith
  have hl : 0 ≤ Real.sqrt s * L := by positivity
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hdisp : ∀ w ∈ K.supp, ∑' x, (if Real.sqrt s * L / 2 ≤ ldist x w then
      vsrwHeat (openGraph ω) (2 * d) (2 * s) w x else 0) ≤
      C * (2 * Real.pi * C * (2 * s)) ^ ((d : ℝ) / 2) * gaussMassBoundD d C *
          Real.exp (-((Real.sqrt s * L / 2) ^ 2 / (2 * C * (2 * s)))) +
        C * expMassBoundD d C * Real.exp (-(2 * s / (2 * C))) := fun w hw =>
    tsum_far_vsrwHeat_le (L := Real.sqrt s * L / 2) (by linarith) (by positivity) hC (hcv w hw)
  have h := tsum_out_abs_gaussFlowDiff_le (K := K) (y := y) hσ hs hl
    (by linarith) (by linarith)
    (add_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (by linarith [one_le_gaussMassBoundD (d := d) hC])) (Real.exp_pos _).le)
      (mul_nonneg (mul_nonneg hC.le (expMassBoundD_nonneg d C)) (Real.exp_pos _).le)) hdisp
  have e1 : (Real.sqrt s * L / 2) ^ 2 / (2 * C * (2 * s)) = L ^ 2 / (16 * C) := by
    rw [div_pow, mul_pow, hsq]; field_simp; ring
  have e2 : 2 * Real.pi * C * (2 * s) = 4 * Real.pi * C * s := by ring
  have e3 : 2 * s / (2 * C) = s / C := by field_simp
  have e4 : (Real.sqrt s * L / 2) ^ 2 / (4 * σ * s) = L ^ 2 / (16 * σ) := by
    rw [div_pow, mul_pow, hsq]; field_simp; ring
  have e5 : (Real.sqrt s * L) ^ 2 / (4 * σ * (3 * s)) = L ^ 2 / (12 * σ) := by
    rw [mul_pow, hsq]; field_simp; ring
  rw [e1, e2, e3, e4, e5] at h
  have hi1 := inv_le_two_div_of_half_le hθ hM1
  have hi3 := inv_le_two_div_of_half_le hθ hM3
  have hG : 0 ≤ 2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ := by
    have := one_le_gaussMassBoundD (d := d) hσ
    positivity
  have hx1 : 0 ≤ 2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * Real.exp (-(L ^ 2 / (16 * σ))) := by
    positivity
  have hx3 : 0 ≤ 2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * Real.exp (-(L ^ 2 / (12 * σ))) := by
    positivity
  have h1 := mul_le_mul_of_nonneg_right hi1 hx1
  have h3 := mul_le_mul_of_nonneg_right hi3 hx3
  nlinarith

/-- **The tail of the initial error.** -/
theorem tsum_out_initialError_le_of_cv (hσ : 0 < σ) (hθ : 0 < θ) {s L C : ℝ} (hs : 1 ≤ s)
    (hL : 0 ≤ L) (hC : 0 < C) (hy : y ∈ K.supp) (hcv : CVBranches ω C s y)
    (hM : θ / 2 ≤ clusterGaussMass K σ s y) :
    ∑' x, (if x ∈ clusterBall K y (Real.sqrt s * L) then 0 else
        |vsrwHeat (openGraph ω) (2 * d) s x y - clusterGaussNorm K σ s y x|) ≤
      C * (2 * Real.pi * C * s) ^ ((d : ℝ) / 2) * gaussMassBoundD d C *
          Real.exp (-(L ^ 2 / (2 * C))) + C * expMassBoundD d C * Real.exp (-(s / (2 * C))) +
        2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (4 * σ))) := by
  have hs0 : 0 < s := by linarith
  have hl : 0 ≤ Real.sqrt s * L := by positivity
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hdisp := tsum_far_vsrwHeat_le (ω := ω) (L := Real.sqrt s * L) hs hl hC hcv
  have h := tsum_out_abs_initialError_le (K := K) (y := y) hσ hs hl hy (by linarith) hdisp
  have e1 : (Real.sqrt s * L) ^ 2 / (2 * C * s) = L ^ 2 / (2 * C) := by
    rw [mul_pow, hsq]; field_simp
  have e4 : (Real.sqrt s * L) ^ 2 / (4 * σ * s) = L ^ 2 / (4 * σ) := by
    rw [mul_pow, hsq]; field_simp
  rw [e1, e4] at h
  have hi := inv_le_two_div_of_half_le hθ hM
  have hx : 0 ≤ 2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * Real.exp (-(L ^ 2 / (4 * σ))) := by
    have := one_le_gaussMassBoundD (d := d) hσ
    positivity
  have h1 := mul_le_mul_of_nonneg_right hi hx
  nlinarith

end Rigidity.Green

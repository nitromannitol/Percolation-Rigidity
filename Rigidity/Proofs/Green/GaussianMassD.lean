import Rigidity.Proofs.Green.LatticeGaussianD
import Rigidity.Proofs.WeakPoincare.Balls

/-!
# The mass of the Gaussian kernel on `ℤ^d`

`|Σ_{x ∈ ℤ^d} p̄(t, x - y) - 1| ≤ C t^{-1/2}` for `t ≥ 1` (`abs_tsum_gaussianHeatD_sub_one_le`), the
`d`-dimensional form of `abs_tsum_latticeGaussian_sub_one_le`: by the Poisson summation formula the
sum is `Θ_t^d` with `1 ≤ Θ_t ≤ 1 + e^{-2π²σ(t - 1)} Θ_1`, and `Θ^d - 1 = (Θ - 1) Σ_{i < d} Θ^i`.
The mass at distance at least `t` from `y` is at most `C t^{-1/2}` (`sum_gaussianHeatD_far_le`).
-/

open LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- **The mass of the Gaussian kernel on `ℤ^d`.** -/
theorem abs_tsum_gaussianHeatD_sub_one_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ y : Vertex d,
      |∑' x, gaussianHeatD d σ t (edzD x y) - 1| ≤ C / Real.sqrt t := by
  set b₀ := 2 * Real.pi ^ 2 * σ with hb₀
  have hb₀0 : 0 < b₀ := by positivity
  set Θ₀ := ∑' n : ℤ, Real.exp (-b₀ * (n : ℝ) ^ 2) with hΘ₀
  have hΘ₀1 : 1 ≤ Θ₀ := one_le_tsum_exp_neg_mul_int_sq hb₀0
  set lam := min 1 b₀ with hlam
  have hlam0 : 0 < lam := lt_min one_pos hb₀0
  refine ⟨d * (1 + Θ₀) ^ d * Θ₀ / lam + 1, by positivity, fun t ht y => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hsqt : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left ht0.le]
    nlinarith
  rw [(hasSum_gaussianHeatD hσ ht0 y).tsum_eq]
  set b := 2 * Real.pi ^ 2 * σ * t with hb
  have hbb : b₀ ≤ b := by
    rw [hb, hb₀]
    have : 0 < 2 * Real.pi ^ 2 * σ := by positivity
    nlinarith
  set Θ := ∑' n : ℤ, Real.exp (-b * (n : ℝ) ^ 2) with hΘ
  set ε := Real.exp (-(b - b₀)) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hΘ1 : 1 ≤ Θ := one_le_tsum_exp_neg_mul_int_sq (by linarith)
  have hΘu : Θ ≤ 1 + ε * Θ₀ := tsum_exp_neg_mul_int_sq_le hb₀0 hbb
  have hεt : ε ≤ 1 / (lam * Real.sqrt t) := by
    have h1 : 1 + (b - b₀) ≤ Real.exp (b - b₀) := by
      have := Real.add_one_le_exp (b - b₀)
      linarith
    have h2 : lam * t ≤ 1 + (b - b₀) := by
      have hbt : b - b₀ = b₀ * (t - 1) := by rw [hb, hb₀]; ring
      rw [hbt]
      have hl1 : lam ≤ 1 := min_le_left _ _
      have hl2 : lam ≤ b₀ := min_le_right _ _
      nlinarith
    rw [hε, Real.exp_neg]
    calc (Real.exp (b - b₀))⁻¹ ≤ (lam * t)⁻¹ :=
          inv_anti₀ (by positivity) (h2.trans h1)
      _ ≤ (lam * Real.sqrt t)⁻¹ :=
          inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hsqt hlam0.le)
      _ = 1 / (lam * Real.sqrt t) := (one_div _).symm
  -- `Θ^d - 1 = (Θ - 1) Σ_{i < d} Θ^i ≤ (Θ - 1) d (1 + Θ₀)^d`
  have hΘle : Θ ≤ 1 + Θ₀ := by nlinarith
  have hgeom : Θ ^ d - 1 = (∑ i ∈ Finset.range d, Θ ^ i) * (Θ - 1) := (geom_sum_mul Θ d).symm
  have hsum : ∑ i ∈ Finset.range d, Θ ^ i ≤ d * (1 + Θ₀) ^ d := by
    calc ∑ i ∈ Finset.range d, Θ ^ i ≤ ∑ _i ∈ Finset.range d, (1 + Θ₀) ^ d :=
          Finset.sum_le_sum fun i hi => by
            calc Θ ^ i ≤ (1 + Θ₀) ^ i := pow_le_pow_left₀ (by linarith) hΘle i
              _ ≤ (1 + Θ₀) ^ d := pow_le_pow_right₀ (by linarith)
                  (Finset.mem_range.1 hi).le
      _ = d * (1 + Θ₀) ^ d := by simp
  have hpow1 : 1 ≤ Θ ^ d := one_le_pow₀ hΘ1
  rw [abs_of_nonneg (by linarith), hgeom]
  have hS0 : 0 ≤ ∑ i ∈ Finset.range d, Θ ^ i :=
    Finset.sum_nonneg fun i _ => pow_nonneg (by linarith) i
  calc (∑ i ∈ Finset.range d, Θ ^ i) * (Θ - 1) ≤ (d * (1 + Θ₀) ^ d) * (ε * Θ₀) :=
        mul_le_mul hsum (by linarith) (by linarith) (by positivity)
    _ ≤ (d * (1 + Θ₀) ^ d) * (1 / (lam * Real.sqrt t) * Θ₀) := by gcongr
    _ = d * (1 + Θ₀) ^ d * Θ₀ / lam / Real.sqrt t := by field_simp
    _ ≤ (d * (1 + Θ₀) ^ d * Θ₀ / lam + 1) / Real.sqrt t := by
        apply div_le_div_of_nonneg_right _ hst.le
        linarith

/-- **The mass far from `y`**: for `t ≥ 1` the mass of `p̄(t, · - y)` on a finite set of vertices
at distance at least `t` from `y` is at most `C t^{-1/2}`. -/
theorem sum_gaussianHeatD_far_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ (y : Vertex d) (S : Finset (Vertex d)),
      (∀ x ∈ S, t ≤ Rigidity.WeakPoincare.latticeDist x y) →
      ∑ x ∈ S, gaussianHeatD d σ t (edzD x y) ≤ C / Real.sqrt t := by
  have hM := one_le_gaussMassBoundD (d := d) hσ
  refine ⟨2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * (4 * σ), by positivity,
    fun t ht y S hS => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hsqt : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left ht0.le]; nlinarith
  have hfar := tsum_gaussianHeatD_far_le (d := d) hσ ht ht0.le y
  have hs := summable_gaussianHeatD (d := d) hσ ht0 y
  have hsI : Summable fun x => (if t ≤ ‖edzD x y‖ then gaussianHeatD d σ t (edzD x y) else 0) :=
    hs.of_nonneg_of_le (fun x => by split_ifs <;> simp [gaussianHeatD_nonneg' σ t (by positivity)])
      (fun x => by split_ifs <;> simp [gaussianHeatD_nonneg' σ t (by positivity)])
  have h1 : ∑ x ∈ S, gaussianHeatD d σ t (edzD x y) =
      ∑ x ∈ S, (if t ≤ ‖edzD x y‖ then gaussianHeatD d σ t (edzD x y) else 0) :=
    Finset.sum_congr rfl fun x hx => by rw [if_pos (show t ≤ ‖edzD x y‖ from hS x hx)]
  have h2 : ∑ x ∈ S, (if t ≤ ‖edzD x y‖ then gaussianHeatD d σ t (edzD x y) else 0) ≤
      ∑' x, (if t ≤ ‖edzD x y‖ then gaussianHeatD d σ t (edzD x y) else 0) :=
    hsI.sum_le_tsum S fun x _ => by split_ifs <;> simp [gaussianHeatD_nonneg' σ t (by positivity)]
  have hexp : Real.exp (-(t ^ 2 / (4 * σ * t))) ≤ 4 * σ / Real.sqrt t := by
    have e : t ^ 2 / (4 * σ * t) = t / (4 * σ) := by field_simp; try ring
    rw [e, Real.exp_neg]
    have h3 : t / (4 * σ) ≤ Real.exp (t / (4 * σ)) := by
      have := Real.add_one_le_exp (t / (4 * σ)); linarith
    have h4 : 0 < t / (4 * σ) := by positivity
    calc (Real.exp (t / (4 * σ)))⁻¹ ≤ (t / (4 * σ))⁻¹ := inv_anti₀ h4 h3
      _ = 4 * σ / t := by rw [inv_div]
      _ ≤ 4 * σ / Real.sqrt t := div_le_div_of_nonneg_left (by positivity) hst hsqt
  rw [h1]
  calc _ ≤ _ := h2
    _ ≤ 2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * Real.exp (-(t ^ 2 / (4 * σ * t))) := hfar
    _ ≤ 2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * (4 * σ / Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end Rigidity.Green

import Rigidity.Proofs.Green.DarioGuTwoScaleFluxPieces

/-!
# The multiscale estimate of Step 3 of Proposition 4.3 of Dario–Gu

This file proves the estimate (4.33) of Step 3 of the proof of Proposition 4.3 of Dario–Gu (lines
2333-2412 of the source) for one component `(k, i)` of the flux: if the weak norm of the
centered flux `g̃_{k,i}` on `𝒞 ∩ B_ρ(y)` is at most `C_f ρ^α` for the radii `ρ = 2^{m+2} √r`
(Proposition 2.13), then

`-Σ_x g̃_{k,i} (D_i D_k p̄ ψ) u ≤ L C_f r^{α/2} (r^{-2} ‖u‖₂ + r^{-3/2} E(u)^{1/2})`

(`neg_tsum_flux_le`), which is the bound `C Ξ₁ ‖∇(wψ)‖ + C Ξ₂ ‖wψ‖` of (4.33) with the estimates
(4.35) of `Ξ₁`, `Ξ₂`. The scales are summed with `sum_dyDecay_le`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The weighted sum of the decay factors of the scales. -/
theorem sum_dyDecay_le {σ : ℝ} (hσ : 0 < σ) (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), (4 : ℝ) ^ (m + 2) * dyDecay σ m ≤
      16 + 4 ^ 3 * Real.exp (1 / (64 * σ)) * (2 * (512 * σ) ^ 2) * (4 / 3) := by
  set A := (4 : ℝ) ^ 3 * Real.exp (1 / (64 * σ)) * (2 * (512 * σ) ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ m : ℕ, (4 : ℝ) ^ (m + 1 + 2) * dyDecay σ (m + 1) ≤ A * (1 / 4) ^ m := by
    intro m
    simp only [dyDecay]
    set t := (4 : ℝ) ^ m with ht
    have ht0 : 0 < t := by positivity
    set x := t / (512 * σ) with hx
    have hx0 : 0 < x := by positivity
    have hq := Real.quadratic_le_exp_of_nonneg hx0.le
    have hexp : Real.exp (-x) ≤ 2 / x ^ 2 := by
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      nlinarith
    have e4 : (4 : ℝ) ^ (m + 1 + 2) = 64 * t := by
      rw [ht, show m + 1 + 2 = m + 3 by ring, pow_add]
      norm_num
      ring
    rw [e4]
    calc 64 * t * (Real.exp (1 / (64 * σ)) * Real.exp (-x))
        ≤ 64 * t * (Real.exp (1 / (64 * σ)) * (2 / x ^ 2)) := by gcongr
      _ = A * (1 / 4) ^ m := by
          rw [hA, one_div_pow, ← ht, hx]
          field_simp
          ring
  rw [Finset.sum_range_succ']
  have hs : ∑ m ∈ Finset.range M, (4 : ℝ) ^ (m + 1 + 2) * dyDecay σ (m + 1) ≤ A * (4 / 3) := by
    calc ∑ m ∈ Finset.range M, (4 : ℝ) ^ (m + 1 + 2) * dyDecay σ (m + 1)
        ≤ ∑ m ∈ Finset.range M, A * (1 / 4 : ℝ) ^ m := Finset.sum_le_sum fun m _ => hterm m
      _ = A * ∑ m ∈ Finset.range M, (1 / 4 : ℝ) ^ m := by rw [Finset.mul_sum]
      _ ≤ A * (4 / 3) := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          rw [Finset.range_eq_Ico]
          refine (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans ?_
          norm_num
  simp only [dyDecay, zero_add] at hs ⊢
  norm_num at hs ⊢
  linarith

/-- `|𝒞 ∩ B_ρ(y)| ≤ 25 ρ²` for `ρ ≥ 1`. -/
theorem card_dgClusterBall_le {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2) {ρ : ℝ}
    (hρ : 1 ≤ ρ) : ((dgClusterBall K y ρ).card : ℝ) ≤ 25 * ρ ^ 2 := by
  have h1 : (dgClusterBall K y ρ).card ≤ (componentEuclideanBall K y ρ).card := by
    unfold dgClusterBall
    exact Finset.card_image_le
  have h2 := Rigidity.Proofs.S2.card_componentEuclideanBall_le K y hρ
  calc ((dgClusterBall K y ρ).card : ℝ) ≤ (componentEuclideanBall K y ρ).card := by
        exact_mod_cast h1
    _ ≤ 5 ^ 2 * ρ ^ 2 := h2
    _ = 25 * ρ ^ 2 := by norm_num

/-- `(2^{m+2} √r)^α ≤ 2^{m+2} r^{α/2}` for `0 ≤ α ≤ 1`. -/
theorem rpow_two_pow_mul_sqrt_le {r α : ℝ} (hr : 0 ≤ r) (hα1 : α ≤ 1) (m : ℕ) :
    ((2 : ℝ) ^ (m + 2) * Real.sqrt r) ^ α ≤ 2 ^ (m + 2) * r ^ (α / 2) := by
  rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg r)]
  have h1 : ((2 : ℝ) ^ (m + 2)) ^ α ≤ 2 ^ (m + 2) := by
    calc ((2 : ℝ) ^ (m + 2)) ^ α ≤ ((2 : ℝ) ^ (m + 2)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hα1
      _ = 2 ^ (m + 2) := Real.rpow_one _
  have h2 : Real.sqrt r ^ α = r ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr]
    ring_nf
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hr _)

/-- **Step 3 for one component of the flux** ((4.33) with (4.35)). -/
theorem neg_tsum_flux_le {σ C : ℝ} (hσ : 0 < σ) (hC : 128 * σ ≤ C) : ∃ L : ℝ, 0 < L ∧
    ∀ (ω : Configuration 2) (K : OpenComponent ω) (y : Vertex 2) (χ : Fin 2 → Vertex 2 → ℝ)
      (k i : Fin 2) (Cf α r R : ℝ) (u : Vertex 2 → ℝ),
      0 ≤ Cf → 0 < α → α ≤ 1 → 1 ≤ r → 0 ≤ R → Summable (fun x => u x ^ 2) →
      (∀ x, x ∉ K.supp → u x = 0) →
      (∀ m : ℕ, WeakNormLe ω (dgClusterBall K y (2 ^ (m + 2) * Real.sqrt r))
        (centeredFlux ω σ χ k i) (Cf * (2 ^ (m + 2) * Real.sqrt r) ^ α)) →
      Summable (fun x => |centeredFlux ω σ χ k i x *
        ((fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x) *
          u x)|) →
      -(∑' x, centeredFlux ω σ χ k i x *
        ((fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x) *
          u x)) ≤
        L * Cf * r ^ (α / 2) * (Real.sqrt (∑' x, u x ^ 2) / r ^ 2 +
          Real.sqrt (openEnergy ω u) / (r * Real.sqrt r)) := by
  obtain ⟨Ka, Kb, hKa, hKb, hcoef⟩ := dyCoeff_bounds hσ hC
  set S₀ := 16 + 4 ^ 3 * Real.exp (1 / (64 * σ)) * (2 * (512 * σ) ^ 2) * (4 / 3) with hS₀
  have hS₀0 : 0 < S₀ := by positivity
  refine ⟨(Ka + 30 * Kb + 20 * Ka) * S₀, by positivity,
    fun ω K y χ k i Cf α r R u hCf hα hα1 hr hR hu huK hW hGW => ?_⟩
  have hr0 : 0 < r := by linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hsr2 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
  set U := Real.sqrt (∑' x, u x ^ 2) with hU
  set E := Real.sqrt (openEnergy ω u) with hE
  have hU0 : 0 ≤ U := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  set W : Vertex 2 → ℝ := fun x =>
    (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x) * u x
    with hWdef
  set ρ : ℕ → ℝ := fun m => (2 : ℝ) ^ (m + 2) * Real.sqrt r with hρ
  have hρ1 : ∀ m, 1 ≤ ρ m := fun m => one_le_two_pow_mul_sqrt hr (m + 2)
  set T := (Ka + 30 * Kb) * U / r ^ 2 + 20 * Ka * E / (r * Real.sqrt r) with hT
  have hT0 : 0 ≤ T := by positivity
  set c : ℕ → ℝ := fun m => Cf * ρ m ^ α * ((Ka / r ^ 2 * dyDecay σ m) * U +
    Real.sqrt (25 * ρ m ^ 2) * (4 * (Ka / r ^ 2 * dyDecay σ m) * E +
      6 * (Kb / (r ^ 2 * Real.sqrt r) * dyDecay σ m) * U)) with hc
  have hpieceEq : ∀ m x, centeredFlux ω σ χ k i x * (dyPiece r y m x * W x) =
      centeredFlux ω σ χ k i x * (dyCoeff σ C r R y i k m x * u x) := by
    intro m x
    simp only [hWdef, dyCoeff]
    ring
  -- every piece is finitely supported
  have hpiece : ∀ m, Summable fun x => centeredFlux ω σ χ k i x * (dyPiece r y m x * W x) := by
    intro m
    refine summable_of_ne_finset_zero (s := dgClusterBall K y (ρ m)) fun x hx => ?_
    rw [hpieceEq]
    by_contra h0
    have h1 : dyCoeff σ C r R y i k m x * u x ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    exact hx (dyCoeff_support K hr huK x h1).1
  -- every piece is estimated by the weak norm
  have hcm : ∀ m, -(∑' x, centeredFlux ω σ χ k i x * (dyPiece r y m x * W x)) ≤ c m := by
    intro m
    rw [tsum_congr (hpieceEq m)]
    obtain ⟨ha, hb⟩ := hcoef r R y i k m hr hR
    exact neg_tsum_le_of_weakNormLe_coeff (hW m) (by have := hρ1 m; positivity)
      (card_dgClusterBall_le K y (hρ1 m)) hu ha hb (dyCoeff_support K hr huK)
  -- the sum over the scales
  have hcle : ∀ m, c m ≤ Cf * r ^ (α / 2) * T * ((4 : ℝ) ^ (m + 2) * dyDecay σ m) := by
    intro m
    have hδ := dyDecay_nonneg σ m
    have hρα := rpow_two_pow_mul_sqrt_le hr0.le hα1 m
    have h25 : Real.sqrt (25 * ρ m ^ 2) = 5 * ρ m := by
      rw [show 25 * ρ m ^ 2 = (5 * ρ m) ^ 2 by ring, Real.sqrt_sq (by have := hρ1 m; linarith)]
    have h2 : (1 : ℝ) ≤ 2 ^ (m + 2) := one_le_pow₀ (by norm_num)
    set X := (Ka / r ^ 2 * dyDecay σ m) * U + Real.sqrt (25 * ρ m ^ 2) *
      (4 * (Ka / r ^ 2 * dyDecay σ m) * E + 6 * (Kb / (r ^ 2 * Real.sqrt r) * dyDecay σ m) * U)
      with hX
    have hX0 : 0 ≤ X := by
      rw [hX, h25]
      have := hρ1 m
      positivity
    have hXe : X = dyDecay σ m * (Ka * U / r ^ 2 +
        2 ^ (m + 2) * (20 * Ka * E / (r * Real.sqrt r) + 30 * Kb * U / r ^ 2)) := by
      rw [hX, h25]
      simp only [hρ]
      set s := Real.sqrt r with hsdef
      rw [← hsr2]
      field_simp
      ring
    have hXle : X ≤ dyDecay σ m * (2 ^ (m + 2) * T) := by
      rw [hXe]
      refine mul_le_mul_of_nonneg_left ?_ hδ
      have hk : Ka * U / r ^ 2 ≤ 2 ^ (m + 2) * (Ka * U / r ^ 2) :=
        le_mul_of_one_le_left (by positivity) h2
      have e : 2 ^ (m + 2) * T = 2 ^ (m + 2) * (Ka * U / r ^ 2) +
          2 ^ (m + 2) * (20 * Ka * E / (r * Real.sqrt r) + 30 * Kb * U / r ^ 2) := by
        rw [hT]
        ring
      rw [e]
      linarith
    have h4 : (4 : ℝ) ^ (m + 2) = 2 ^ (m + 2) * 2 ^ (m + 2) := by
      rw [← mul_pow]
      norm_num
    calc c m = Cf * ρ m ^ α * X := rfl
      _ ≤ Cf * (2 ^ (m + 2) * r ^ (α / 2)) * (dyDecay σ m * (2 ^ (m + 2) * T)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hρα hCf) hXle hX0
          exact mul_nonneg hCf (by positivity)
      _ = Cf * r ^ (α / 2) * T * ((4 : ℝ) ^ (m + 2) * dyDecay σ m) := by
          rw [h4]
          ring
  have hS : ∀ M, ∑ m ∈ Finset.range (M + 1), c m ≤ Cf * r ^ (α / 2) * T * S₀ := by
    intro M
    calc ∑ m ∈ Finset.range (M + 1), c m
        ≤ ∑ m ∈ Finset.range (M + 1), Cf * r ^ (α / 2) * T * ((4 : ℝ) ^ (m + 2) * dyDecay σ m) :=
          Finset.sum_le_sum fun m _ => hcle m
      _ = Cf * r ^ (α / 2) * T * ∑ m ∈ Finset.range (M + 1), (4 : ℝ) ^ (m + 2) * dyDecay σ m := by
          rw [Finset.mul_sum]
      _ ≤ Cf * r ^ (α / 2) * T * S₀ :=
          mul_le_mul_of_nonneg_left (sum_dyDecay_le hσ M) (by positivity)
  have hmain := neg_tsum_le_of_pieces hr0 hGW hpiece hcm hS
  refine hmain.trans ?_
  have hTle : T ≤ (Ka + 30 * Kb + 20 * Ka) * (U / r ^ 2 + E / (r * Real.sqrt r)) := by
    rw [hT]
    have a1 : 0 ≤ Ka * U / r ^ 2 := by positivity
    have a2 : 0 ≤ (Ka + 30 * Kb) * E / (r * Real.sqrt r) := by positivity
    have e : (Ka + 30 * Kb + 20 * Ka) * (U / r ^ 2 + E / (r * Real.sqrt r)) =
        (Ka + 30 * Kb) * U / r ^ 2 + 20 * Ka * E / (r * Real.sqrt r) +
          (20 * Ka * U / r ^ 2 + (Ka + 30 * Kb) * E / (r * Real.sqrt r)) := by ring
    rw [e]
    have a3 : 0 ≤ 20 * Ka * U / r ^ 2 := by positivity
    linarith
  have hpos : 0 ≤ Cf * r ^ (α / 2) := mul_nonneg hCf (Real.rpow_nonneg hr0.le _)
  calc Cf * r ^ (α / 2) * T * S₀
      ≤ Cf * r ^ (α / 2) * ((Ka + 30 * Kb + 20 * Ka) * (U / r ^ 2 + E / (r * Real.sqrt r))) *
          S₀ := by gcongr
    _ = (Ka + 30 * Kb + 20 * Ka) * S₀ * Cf * r ^ (α / 2) *
          (U / r ^ 2 + E / (r * Real.sqrt r)) := by ring

end Rigidity.Green

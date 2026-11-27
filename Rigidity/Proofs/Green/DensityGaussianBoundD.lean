import Rigidity.Proofs.Green.GaussianRegionD
import Rigidity.Proofs.Green.DarioGuDensityGaussianBound
import Rigidity.Proofs.Green.GaussianShiftSumD

/-!
# The Gaussian mass of the cluster of `ℤ^d` from the densities on triadic cubes

The `d`-dimensional form of `DarioGuDensityGaussianBound.lean`, the deterministic part of the proof
of Proposition A.7 of Dario–Gu: for `t ≥ 81`, `3^K ≤ √t < 3^{K+1}`, a finite union `S` of cubes of
scale `K` and `u : ℤ^d → ℝ` with `|u| ≤ 1` whose averages on the cubes of scale `k ≤ K` meeting `S`
are at most `(3^k)^{α - 1}` whenever `3^k ≥ t^α`,

`|Σ_{x ∈ S} p̄(t, x - y) u(x)| ≤ C t^{-(1/2 - α)}` (`abs_sum_gaussianHeatD_mul_le`),

by the multiscale decomposition `abs_sum_mul_le_multiscaleD` and the oscillation bound
`abs_gaussianHeatD_sub_le_of_near` of `p̄` on the cubes of scale `k + 1` (of diameter at most
`d 3^{k+1} ≤ d √t`).
-/

open Finset LatticeProb.Percolation Rigidity.Proofs.S2

namespace Rigidity.Green

variable {d : ℕ}

/-! ### Sums on cubes -/

/-- On a union of cubes of scale `k`, `Σ_{x ∈ S} A_k f(x) = Σ_{x ∈ S} f(x)`. -/
theorem sum_cubeMean_eqD {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnionD k S)
    (f : Vertex d → ℝ) : ∑ x ∈ S, cubeMeanD f k (cubeIndexD k x) = ∑ x ∈ S, f x := by
  have h1 := sum_comp_cubeIndex_mulD hS (cubeMeanD f k) (fun _ => (1 : ℝ))
  have h2 := sum_comp_cubeIndex_mulD hS (fun _ => (1 : ℝ)) f
  simp only [mul_one, one_mul] at h1 h2
  rw [h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_triadicCubeFinsetD,
    sum_triadicCubeFinset_eq_mul_cubeMeanD]
  ring

theorem abs_cubeMean_le_oneD {u : Vertex d → ℝ} (hu : ∀ x, |u x| ≤ 1) (k : ℕ) (j : Vertex d) :
    |cubeMeanD u k j| ≤ 1 := by
  rw [cubeMeanD, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((3 : ℝ) ^ d) ^ k),
    div_le_one (by positivity)]
  calc |∑ x ∈ triadicCubeFinset d k j, u x| ≤ ∑ x ∈ triadicCubeFinset d k j, |u x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ triadicCubeFinset d k j, (1 : ℝ) := Finset.sum_le_sum fun x _ => hu x
    _ = (3 ^ d) ^ k := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_triadicCubeFinsetD]

theorem cubeMean_nonnegD {f : Vertex d → ℝ} (hf : ∀ x, 0 ≤ f x) (k : ℕ) (j : Vertex d) :
    0 ≤ cubeMeanD f k j :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (by positivity)

/-- Two vertices of the same cube of scale `k` are at distance less than `d · 3^k`. -/
theorem norm_sub_lt_of_cubeIndex_eqD [NeZero d] {k : ℕ} {x x' : Vertex d}
    (h : cubeIndexD k x = cubeIndexD k x') :
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding x'‖ < d * 3 ^ k := by
  rw [← dist_eq_norm]
  have hQ := three_pow_eq_two_mul_half_add_one k
  have hc : ∀ i, |(latticeEuclideanEmbedding x).ofLp i - (latticeEuclideanEmbedding x').ofLp i| <
      3 ^ k := by
    intro i
    have h1 := abs_sub_mul_cubeIndex_leD k x i
    have h2 := abs_sub_mul_cubeIndex_leD k x' i
    rw [h] at h1
    have hi : |x i - x' i| < 3 ^ k := by
      have a1 := abs_le.1 h1
      have a2 := abs_le.1 h2
      rw [abs_lt]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    have hi' : ((|x i - x' i| : ℤ) : ℝ) < ((3 ^ k : ℤ) : ℝ) := by exact_mod_cast hi
    push_cast at hi'
    exact hi'
  exact dist_lt_of_forall_abs_sub_lt (d := d) hc

/-! ### The deterministic estimate -/


/-- **The Gaussian mass of `u` from its averages on triadic cubes.** For `t ≥ 81`,
`3^K ≤ √t < 3^{K+1}`, a finite union `S` of cubes of scale `K` and `|u| ≤ 1` with
`|A_k u| ≤ (3^k)^{α - 1}` on `S` whenever `k ≤ K` and `t^α ≤ 3^k`:
`|Σ_{x ∈ S} p̄(t, x - y) u(x)| ≤ C t^{-(1/2 - α)}`. -/
theorem abs_sum_gaussianHeatD_mul_le [NeZero d] {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    (hα1 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (K : ℕ), 81 ≤ t → (3 : ℝ) ^ K ≤ Real.sqrt t →
      Real.sqrt t < 3 ^ (K + 1) → ∀ (y : Vertex d) (S : Finset (Vertex d)),
      IsCubeUnionD K S →
      ∀ u : Vertex d → ℝ, (∀ x, |u x| ≤ 1) →
      (∀ k ≤ K, t ^ α ≤ (3 : ℝ) ^ k → ∀ x ∈ S,
        |cubeMeanD u k (cubeIndexD k x)| ≤ ((3 : ℝ) ^ k) ^ (α - 1)) →
      |∑ x ∈ S, gaussianHeatD d σ t (edzD x y) * u x| ≤ C * t ^ (-(1 / 2 - α)) := by
  set Kσ := gaussOscConstD σ d with hKσ
  have hKσ0 : 0 < Kσ := by rw [hKσ]; unfold gaussOscConstD; positivity
  set L₀ := 3 * (d : ℝ) * 8 ^ ((d : ℝ) / 2) with hL₀
  have hL₀0 : 0 < L₀ := by have := NeZero.pos d; positivity
  set q := (3 : ℝ) ^ α with hq
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) hα
  set M := gaussMassBoundD d σ with hM
  have hM0 : 0 < M := by linarith [one_le_gaussMassBoundD (d := d) hσ]
  refine ⟨3 * M + Kσ * L₀ * M * (3 / 2 + 1 / (q - 1)), by
    have : 0 < q - 1 := by linarith
    positivity, ?_⟩
  intro t K ht hK1 hK2 y S hS u hu hgood
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hss := Real.mul_self_sqrt ht0.le
  set f : Vertex d → ℝ := fun x => gaussianHeatD d σ t (edzD x y) with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => gaussianHeatD_nonneg' σ t (by positivity) _
  have hfS : ∀ S' : Finset (Vertex d), ∑ x ∈ S', f x ≤ M := fun S' =>
    ((summable_gaussianHeatD (d := d) hσ ht0 y).sum_le_tsum S' fun x _ => hf0 x).trans
      (tsum_gaussianHeatD_le hσ ht1 y)
  -- `t^α ≤ 3^K`
  have h14 : (3 : ℝ) ≤ t ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) ht (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have e : (81 : ℝ) ^ (1 / 4 : ℝ) = 3 := by
      rw [show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    linarith
  have hsq4 : Real.sqrt t = t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add ht0, Real.sqrt_eq_rpow]
    norm_num
  have hXK : t ^ α ≤ (3 : ℝ) ^ K := by
    have h1 : t ^ α ≤ t ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 hα1
    have h2 : 3 * t ^ α ≤ Real.sqrt t := by
      rw [hsq4]
      have := Real.rpow_nonneg ht0.le α
      nlinarith
    rw [pow_succ] at hK2
    linarith
  have hX0 : 0 ≤ t ^ α := Real.rpow_nonneg ht0.le α
  -- the bound on the averages of `u`
  set δ : ℕ → ℝ := fun k => if t ^ α ≤ (3 : ℝ) ^ k then ((3 : ℝ) ^ k) ^ (α - 1) else 1 with hδ
  have hδu : ∀ k ≤ K, ∀ x ∈ S, |cubeMeanD u k (cubeIndexD k x)| ≤ δ k := by
    intro k hk x hx
    simp only [hδ]
    split_ifs with h
    · exact hgood k hk h x hx
    · exact abs_cubeMean_le_oneD hu k _
  have hmain := abs_sum_mul_le_multiscaleD hS f u
  -- the top term
  have hT1 : ∑ x ∈ S, |cubeMeanD f K (cubeIndexD K x)| * |cubeMeanD u K (cubeIndexD K x)| ≤
      ((3 : ℝ) ^ K) ^ (α - 1) * M := by
    calc ∑ x ∈ S, |cubeMeanD f K (cubeIndexD K x)| * |cubeMeanD u K (cubeIndexD K x)|
        ≤ ∑ x ∈ S, cubeMeanD f K (cubeIndexD K x) * ((3 : ℝ) ^ K) ^ (α - 1) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [abs_of_nonneg (cubeMean_nonnegD hf0 K _)]
          exact mul_le_mul_of_nonneg_left (hgood K le_rfl hXK x hx) (cubeMean_nonnegD hf0 K _)
      _ = ((3 : ℝ) ^ K) ^ (α - 1) * ∑ x ∈ S, f x := by
          rw [← Finset.sum_mul, sum_cubeMean_eqD hS, mul_comm]
      _ ≤ ((3 : ℝ) ^ K) ^ (α - 1) * M :=
          mul_le_mul_of_nonneg_left (hfS S) (by positivity)
  -- the terms of scale `k < K`
  set P := (2 * Real.pi * σ * t) ^ (-((d : ℝ) / 2)) with hP
  have hP0 : 0 ≤ P := by positivity
  have hsumP : ∑ x ∈ S, P * Real.exp (-(‖edzD x y‖ ^ 2 / (16 * σ * t))) ≤
      8 ^ ((d : ℝ) / 2) * M := by
    have e : ∀ x, P * Real.exp (-(‖edzD x y‖ ^ 2 / (16 * σ * t))) =
        8 ^ ((d : ℝ) / 2) * gaussianHeatD d σ (8 * t) (edzD x y) := fun x => by
      rw [← rpow_mul_exp_eq_gaussianHeatD hσ ht0 (by norm_num : (0 : ℝ) < 8),
        show 2 * σ * (8 * t) = 16 * σ * t by ring]
    have hs8 := summable_gaussianHeatD (d := d) hσ (by linarith : (0 : ℝ) < 8 * t) y
    calc ∑ x ∈ S, P * Real.exp (-(‖edzD x y‖ ^ 2 / (16 * σ * t)))
        = 8 ^ ((d : ℝ) / 2) * ∑ x ∈ S, gaussianHeatD d σ (8 * t) (edzD x y) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => e x
      _ ≤ 8 ^ ((d : ℝ) / 2) * M := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (hs8.sum_le_tsum S fun x _ =>
            gaussianHeatD_nonneg' σ (8 * t) (by positivity) _).trans
              (tsum_gaussianHeatD_le hσ (by linarith) y)
  have hT2 : ∀ k ∈ range K, ∑ x ∈ S,
      |cubeMeanD f k (cubeIndexD k x) - cubeMeanD f (k + 1) (cubeIndexD (k + 1) x)| *
        |cubeMeanD u k (cubeIndexD k x)| ≤
      Kσ * L₀ * M / Real.sqrt t * ((3 : ℝ) ^ k * δ k) := by
    intro k hk
    have hkK : k + 1 ≤ K := Finset.mem_range.1 hk
    have hδ0 : 0 ≤ δ k := by
      simp only [hδ]
      split_ifs <;> positivity
    have hL : (d : ℝ) * 3 ^ (k + 1) ≤ d * Real.sqrt t := by
      have : (3 : ℝ) ^ (k + 1) ≤ 3 ^ K := pow_le_pow_right₀ (by norm_num) hkK
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg d)
    have hosc : ∀ x, |cubeMeanD f k (cubeIndexD k x) - cubeMeanD f (k + 1) (cubeIndexD (k + 1) x)| ≤
        Kσ * ((d * 3 ^ (k + 1)) / Real.sqrt t) *
          (P * Real.exp (-(‖edzD x y‖ ^ 2 / (16 * σ * t)))) := by
      intro x
      apply abs_cubeMean_sub_cubeMean_succ_leD
      intro x' hx' x'' hx''
      rw [mem_triadicCubeFinset_iffD] at hx' hx''
      have hn : ∀ w, cubeIndexD (k + 1) w = cubeIndexD (k + 1) x →
          ‖edzD w y - edzD x y‖ ≤ d * 3 ^ (k + 1) := by
        intro w hw
        simp only [edzD]
        rw [sub_sub_sub_cancel_right]
        exact (norm_sub_lt_of_cubeIndex_eqD hw).le
      exact abs_gaussianHeatD_sub_le_of_near hσ ht0 (by positivity) (Nat.cast_nonneg d) hL
        (hn x' hx') (hn x'' hx'')
    calc ∑ x ∈ S, |cubeMeanD f k (cubeIndexD k x) - cubeMeanD f (k + 1) (cubeIndexD (k + 1) x)| *
          |cubeMeanD u k (cubeIndexD k x)|
        ≤ ∑ x ∈ S, Kσ * ((d * 3 ^ (k + 1)) / Real.sqrt t) *
            (P * Real.exp (-(‖edzD x y‖ ^ 2 / (16 * σ * t)))) * δ k :=
          Finset.sum_le_sum fun x hx => mul_le_mul (hosc x)
            (hδu k (Nat.le_of_succ_le hkK) x hx) (abs_nonneg _) (by positivity)
      _ = Kσ * ((d * 3 ^ (k + 1)) / Real.sqrt t) * δ k *
            ∑ x ∈ S, P * Real.exp (-(‖edzD x y‖ ^ 2 / (16 * σ * t))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ Kσ * ((d * 3 ^ (k + 1)) / Real.sqrt t) * δ k * (8 ^ ((d : ℝ) / 2) * M) :=
          mul_le_mul_of_nonneg_left hsumP (by positivity)
      _ = Kσ * L₀ * M / Real.sqrt t * ((3 : ℝ) ^ k * δ k) := by
          rw [hL₀, pow_succ]
          ring
  -- the sum over scales
  have hT3 : ∑ k ∈ range K, (3 : ℝ) ^ k * δ k ≤ 3 * t ^ α / 2 + t ^ α / (q - 1) := by
    have hpt : ∀ k, (3 : ℝ) ^ k * δ k ≤
        (if t ^ α ≤ (3 : ℝ) ^ k then 0 else (3 : ℝ) ^ k) + q ^ k := by
      intro k
      simp only [hδ]
      split_ifs with h
      · rw [pow_mul_rpow_sub_one, zero_add]
      · rw [mul_one]
        have : 0 ≤ q ^ k := by positivity
        linarith
    have hqK : q ^ K ≤ t ^ α := by
      rw [hq, Real.rpow_pow_comm (by norm_num)]
      calc ((3 : ℝ) ^ K) ^ α ≤ (Real.sqrt t) ^ α :=
            Real.rpow_le_rpow (by positivity) hK1 hα.le
        _ ≤ t ^ α := Real.rpow_le_rpow hst.le
            (by rw [Real.sqrt_le_left ht0.le]; nlinarith) hα.le
    calc ∑ k ∈ range K, (3 : ℝ) ^ k * δ k
        ≤ ∑ k ∈ range K, ((if t ^ α ≤ (3 : ℝ) ^ k then 0 else (3 : ℝ) ^ k) + q ^ k) :=
          Finset.sum_le_sum fun k _ => hpt k
      _ = ∑ k ∈ range K, (if t ^ α ≤ (3 : ℝ) ^ k then 0 else (3 : ℝ) ^ k) +
            ∑ k ∈ range K, q ^ k := Finset.sum_add_distrib
      _ ≤ 3 * t ^ α / 2 + q ^ K / (q - 1) :=
          add_le_add (sum_ite_pow_lt_le hX0 K).2 (sum_rpow_pow_le hα K)
      _ ≤ 3 * t ^ α / 2 + t ^ α / (q - 1) := by
          gcongr
  -- the exponents
  have hE1 : ((3 : ℝ) ^ K) ^ (α - 1) ≤ 3 * t ^ (-(1 / 2 - α)) := by
    have hK3 : Real.sqrt t / 3 ≤ (3 : ℝ) ^ K := by
      rw [pow_succ] at hK2
      linarith
    calc ((3 : ℝ) ^ K) ^ (α - 1) ≤ (Real.sqrt t / 3) ^ (α - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hK3 (by linarith)
      _ = (Real.sqrt t) ^ (α - 1) * (3 : ℝ) ^ (1 - α) := by
          rw [Real.div_rpow hst.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
            neg_sub]
      _ ≤ t ^ (-(1 / 2 - α)) * 3 := by
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
            exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
          · calc (3 : ℝ) ^ (1 - α) ≤ 3 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 3 := Real.rpow_one 3
      _ = 3 * t ^ (-(1 / 2 - α)) := by ring
  have hE2 : t ^ α / Real.sqrt t = t ^ (-(1 / 2 - α)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht0]
    congr 1
    ring
  have hE0 : 0 ≤ t ^ (-(1 / 2 - α)) := Real.rpow_nonneg ht0.le _
  calc |∑ x ∈ S, gaussianHeatD d σ t (edzD x y) * u x| = |∑ x ∈ S, f x * u x| := rfl
    _ ≤ ((3 : ℝ) ^ K) ^ (α - 1) * M +
          ∑ k ∈ range K, Kσ * L₀ * M / Real.sqrt t * ((3 : ℝ) ^ k * δ k) :=
        hmain.trans (add_le_add hT1 (Finset.sum_le_sum hT2))
    _ = ((3 : ℝ) ^ K) ^ (α - 1) * M +
          Kσ * L₀ * M / Real.sqrt t * ∑ k ∈ range K, (3 : ℝ) ^ k * δ k := by
        rw [Finset.mul_sum]
    _ ≤ 3 * t ^ (-(1 / 2 - α)) * M +
          Kσ * L₀ * M / Real.sqrt t * (3 * t ^ α / 2 + t ^ α / (q - 1)) := by
        gcongr
    _ = 3 * M * t ^ (-(1 / 2 - α)) +
          Kσ * L₀ * M * (3 / 2 + 1 / (q - 1)) * (t ^ α / Real.sqrt t) := by
        field_simp
    _ = (3 * M + Kσ * L₀ * M * (3 / 2 + 1 / (q - 1))) * t ^ (-(1 / 2 - α)) := by
        rw [hE2]
        ring

end Rigidity.Green

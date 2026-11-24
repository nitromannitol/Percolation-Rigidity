import Rigidity.Proofs.Green.DarioGuTwoScaleStepFour

/-!
# The duality step of Step 3 of Proposition 4.3 of Dario–Gu

Step 3 of the proof of Proposition 4.3 of Dario–Gu (lines 2333-2405 of the source) tests the
centered flux against the functions `(η_m - η_{m-1}) D_i D_k p̄ ψ² w` on the balls
`𝒞_∞ ∩ B_{2^{m+1}√t}(y)` and uses the bound of Proposition 2.13 on the weak norm. This file
proves the single-scale form of this duality with the normalizations of (1.32)-(1.33):

* `neg_sum_le_of_weakNormLe`: if `‖g‖_{H̲^{-1}(V)} ≤ B` and `φ` vanishes on `V \ int_a(V)`, then
  `-Σ_{x ∈ V} g φ ≤ B (‖φ‖_{L²(V)} + |V|^{1/2} ‖∇φ‖_{L²(V)})`;
* `openGradNorm_le`, `openGradNorm_sq_le`: `|∇φ|(x)` is bounded by the differences of `φ` along
  the open edges at `x`, and `|∇φ|(x)² ≤ 4 Σ_i (a_i(x) (φ(x + e_i) - φ(x))² +
  a_i(x - e_i) (φ(x - e_i) - φ(x))²)`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem openGradNorm_neg (ω : Configuration 2) (V : Finset (Vertex 2)) (φ : Vertex 2 → ℝ)
    (x : Vertex 2) : openGradNorm ω V (fun z => -φ z) x = openGradNorm ω V φ x := by
  unfold openGradNorm
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs
  · rw [show -φ z - -φ x = -(φ z - φ x) by ring, abs_neg]
  · rfl

theorem clusterH1Norm_neg (ω : Configuration 2) (V : Finset (Vertex 2)) (φ : Vertex 2 → ℝ) :
    clusterH1Norm ω V (fun z => -φ z) = clusterH1Norm ω V φ := by
  unfold clusterH1Norm
  simp only [openGradNorm_neg, neg_sq]

theorem clusterH1Norm_nonneg (ω : Configuration 2) (V : Finset (Vertex 2)) (φ : Vertex 2 → ℝ) :
    0 ≤ clusterH1Norm ω V φ := by
  unfold clusterH1Norm
  positivity

/-- `|V| ‖φ‖_{H̲¹(V)} = ‖φ‖_{L²(V)} + |V|^{1/2} ‖∇φ‖_{L²(V)}` for `V ≠ ∅`. -/
theorem card_mul_clusterH1Norm {ω : Configuration 2} {V : Finset (Vertex 2)}
    (hV : 0 < (V.card : ℝ)) (φ : Vertex 2 → ℝ) :
    (V.card : ℝ) * clusterH1Norm ω V φ = Real.sqrt (∑ x ∈ V, φ x ^ 2) +
      Real.sqrt (V.card : ℝ) * Real.sqrt (∑ x ∈ V, openGradNorm ω V φ x ^ 2) := by
  set n : ℝ := (V.card : ℝ) with hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hV
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hV.le
  unfold clusterH1Norm
  rw [← hn, rpow_neg_half_eq hV, Real.sqrt_mul (inv_nonneg.2 hV.le),
    Real.sqrt_mul (inv_nonneg.2 hV.le), Real.sqrt_inv]
  field_simp
  rw [Real.sq_sqrt hV.le]

/-- **The duality with the weak norm** on a finite set `V`: if `‖g‖_{H̲^{-1}(V)} ≤ B`, `|V| ≤ Λ`
and `φ` vanishes on `V \ int_a(V)`, then
`-Σ_{x ∈ V} g φ ≤ B (‖φ‖_{L²(V)} + Λ^{1/2} ‖∇φ‖_{L²(V)})`. -/
theorem neg_sum_le_of_weakNormLe {ω : Configuration 2} {V : Finset (Vertex 2)}
    {g φ : Vertex 2 → ℝ} {B Λ : ℝ} (h : WeakNormLe ω V g B) (hB : 0 ≤ B)
    (hΛ : (V.card : ℝ) ≤ Λ) (hφ : ∀ x ∈ V, x ∉ openInterior ω V → φ x = 0) :
    -(∑ x ∈ V, g x * φ x) ≤ B * (Real.sqrt (∑ x ∈ V, φ x ^ 2) +
      Real.sqrt Λ * Real.sqrt (∑ x ∈ V, openGradNorm ω V φ x ^ 2)) := by
  have hR : 0 ≤ B * (Real.sqrt (∑ x ∈ V, φ x ^ 2) +
      Real.sqrt Λ * Real.sqrt (∑ x ∈ V, openGradNorm ω V φ x ^ 2)) := by positivity
  rcases Nat.eq_zero_or_pos V.card with h0 | hpos
  · have hV0 : V = ∅ := Finset.card_eq_zero.1 h0
    have hs : ∑ x ∈ V, g x * φ x = 0 := by rw [hV0, Finset.sum_empty]
    rw [hs, neg_zero]
    exact hR
  have hV : 0 < (V.card : ℝ) := by exact_mod_cast hpos
  have h1 := h (fun z => -φ z) (fun x hx hx' => by rw [hφ x hx hx', neg_zero])
  rw [clusterH1Norm_neg] at h1
  have e : (V.card : ℝ)⁻¹ * ∑ x ∈ V, g x * -φ x = -((V.card : ℝ)⁻¹ * ∑ x ∈ V, g x * φ x) := by
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hV.le
  rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul, mul_left_comm,
    card_mul_clusterH1Norm hV] at h2
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ hB)
  gcongr

/-- `|∇φ|(x)` is at most the sum of the differences of `φ` along the open edges at `x`. -/
theorem openGradNorm_le (ω : Configuration 2) (V : Finset (Vertex 2)) (φ : Vertex 2 → ℝ)
    (x : Vertex 2) : openGradNorm ω V φ x ≤ ∑ i : Fin 2,
      (openCond ω i x * |φ (x + unit i) - φ x| +
        openCond ω i (x - unit i) * |φ (x - unit i) - φ x|) := by
  unfold openGradNorm
  rw [Rigidity.Proofs.Regularity.sum_nbrFinset]
  refine Finset.sum_le_sum fun i _ => add_le_add ?_ ?_
  · unfold openCond
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.1 h2
    · rw [one_mul]
      exact abs_nonneg _
    · rw [zero_mul]
  · have hc2 : openCond ω i (x - unit i) =
        if (openGraph ω).Adj x (x - unit i) then 1 else 0 := by
      unfold openCond
      rw [sub_add_cancel]
      by_cases h : (openGraph ω).Adj x (x - unit i)
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg fun h' => h h'.symm]
    rw [hc2]
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.1 h2
    · rw [one_mul]
      exact abs_nonneg _
    · rw [zero_mul]

/-- `|∇φ|(x)² ≤ 4 Σ_i (a_i(x) (φ(x + e_i) - φ(x))² + a_i(x - e_i) (φ(x - e_i) - φ(x))²)`. -/
theorem openGradNorm_sq_le (ω : Configuration 2) (V : Finset (Vertex 2)) (φ : Vertex 2 → ℝ)
    (x : Vertex 2) : openGradNorm ω V φ x ^ 2 ≤ 4 * ∑ i : Fin 2,
      (openCond ω i x * (φ (x + unit i) - φ x) ^ 2 +
        openCond ω i (x - unit i) * (φ (x - unit i) - φ x) ^ 2) := by
  have h0 : 0 ≤ openGradNorm ω V φ x := by
    unfold openGradNorm
    exact Finset.sum_nonneg fun z _ => by split_ifs <;> positivity
  have h1 := pow_le_pow_left₀ h0 (openGradNorm_le ω V φ x) 2
  refine h1.trans ?_
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have key : ∀ (i : Fin 2) (z : Vertex 2) (u : ℝ), (openCond ω i z * |u|) ^ 2 =
      openCond ω i z * u ^ 2 := by
    intro i z u
    rw [mul_pow, openCond_sq, sq_abs]
  have k1 := key 0 x (φ (x + unit 0) - φ x)
  have k2 := key 0 (x - unit 0) (φ (x - unit 0) - φ x)
  have k3 := key 1 x (φ (x + unit 1) - φ x)
  have k4 := key 1 (x - unit 1) (φ (x - unit 1) - φ x)
  set a := openCond ω 0 x * |φ (x + unit 0) - φ x|
  set b := openCond ω 0 (x - unit 0) * |φ (x - unit 0) - φ x|
  set c := openCond ω 1 x * |φ (x + unit 1) - φ x|
  set d := openCond ω 1 (x - unit 1) * |φ (x - unit 1) - φ x|
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

end Rigidity.Green

import Rigidity.Proofs.Green.DarioGuTwoScaleHeatFlow
import Rigidity.Proofs.Green.DarioGuTwoScaleWeightTrunc

/-!
# The time derivative of the weighted energy of Step 2 of Proposition 4.3

Step 2 of the proof of Proposition 4.3 of Dario–Gu differentiates `s ↦ ∫_{𝒞_∞} ψ² w²` in time.
For a bounded weight `ψ` (the truncated weight `ψ_R`) and a function `u` dominated, together with
its time derivative, by square summable functions uniformly on an open time interval, the series
`Σ_x (ψ u)²` is differentiable term by term (`hasDerivAt_tsum_sq_mul`). The Laplacian of the open
graph is dominated by the neighbour envelope `nbrEnv D` of a dominating function `D`, which stays
square summable (`abs_openLaplacian_le_nbrEnv`, `summable_sq_nbrEnv`).
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- **Differentiation of the weighted energy under the sum**: if `|u| ≤ D`, `|∂_s u| ≤ D'`,
`|ψ| ≤ B`, `|∂_s ψ| ≤ B'` on `(a, b) × ℤ²` with `D, D'` square summable, then
`∂_s Σ_x (ψ u)² = Σ_x 2 (ψ u) (∂_s ψ u + ψ ∂_s u)` on `(a, b)`. -/
theorem hasDerivAt_tsum_sq_mul {ψ u ψ' u' : ℝ → Vertex 2 → ℝ} {a b s B B' : ℝ}
    {D D' : Vertex 2 → ℝ} (hD : Summable fun x => D x ^ 2) (hD' : Summable fun x => D' x ^ 2)
    (hu : ∀ r ∈ Set.Ioo a b, ∀ x, |u r x| ≤ D x)
    (hu' : ∀ r ∈ Set.Ioo a b, ∀ x, |u' r x| ≤ D' x)
    (hψ : ∀ r ∈ Set.Ioo a b, ∀ x, |ψ r x| ≤ B) (hψ' : ∀ r ∈ Set.Ioo a b, ∀ x, |ψ' r x| ≤ B')
    (hdu : ∀ r ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun r => u r x) (u' r x) r)
    (hdψ : ∀ r ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun r => ψ r x) (ψ' r x) r)
    (hs : s ∈ Set.Ioo a b) :
    HasDerivAt (fun r => ∑' x, (ψ r x * u r x) ^ 2)
      (∑' x, 2 * (ψ s x * u s x) * (ψ' s x * u s x + ψ s x * u' s x)) s := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hψ s hs 0)
  have hB' : 0 ≤ B' := (abs_nonneg _).trans (hψ' s hs 0)
  set v : Vertex 2 → ℝ := fun x => 2 * (B * B') * D x ^ 2 + B ^ 2 * (D x ^ 2 + D' x ^ 2)
    with hv
  have hvs : Summable v := (hD.mul_left (2 * (B * B'))).add ((hD.add hD').mul_left (B ^ 2))
  refine hasDerivAt_tsum_of_isPreconnected (u := v) hvs isOpen_Ioo isPreconnected_Ioo
    (g := fun x r => (ψ r x * u r x) ^ 2)
    (g' := fun x r => 2 * (ψ r x * u r x) * (ψ' r x * u r x + ψ r x * u' r x))
    (fun x r hr => ?_) (fun x r hr => ?_) hs ?_ hs
  · exact (((hdψ r hr x).mul (hdu r hr x)).pow 2).congr_deriv (by norm_num)
  · rw [Real.norm_eq_abs]
    have h1 := hψ r hr x
    have h2 := hu r hr x
    have h3 := hψ' r hr x
    have h4 := hu' r hr x
    have hDx : 0 ≤ D x := (abs_nonneg _).trans h2
    have hD'x : 0 ≤ D' x := (abs_nonneg _).trans h4
    have e1 : |2 * (ψ r x * u r x) * (ψ' r x * u r x + ψ r x * u' r x)| ≤
        2 * (|ψ r x| * |u r x|) * (|ψ' r x| * |u r x| + |ψ r x| * |u' r x|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_mul]))
    have k1 : |ψ r x| * |ψ' r x| * (|u r x| * |u r x|) ≤ B * B' * (D x * D x) :=
      mul_le_mul (mul_le_mul h1 h3 (abs_nonneg _) hB) (mul_le_mul h2 h2 (abs_nonneg _) hDx)
        (by positivity) (by positivity)
    have k2 : |ψ r x| * |ψ r x| * (|u r x| * |u' r x|) ≤ B * B * (D x * D' x) :=
      mul_le_mul (mul_le_mul h1 h1 (abs_nonneg _) hB) (mul_le_mul h2 h4 (abs_nonneg _) hDx)
        (by positivity) (by positivity)
    have k3 : 2 * (D x * D' x) ≤ D x ^ 2 + D' x ^ 2 := by nlinarith [sq_nonneg (D x - D' x)]
    have k4 := mul_le_mul_of_nonneg_left k3 (sq_nonneg B)
    calc |2 * (ψ r x * u r x) * (ψ' r x * u r x + ψ r x * u' r x)|
        ≤ 2 * (|ψ r x| * |u r x|) * (|ψ' r x| * |u r x| + |ψ r x| * |u' r x|) := e1
      _ = 2 * (|ψ r x| * |ψ' r x| * (|u r x| * |u r x|)) +
          2 * (|ψ r x| * |ψ r x| * (|u r x| * |u' r x|)) := by ring
      _ ≤ v x := by
        simp only [hv]
        nlinarith [k1, k2, k4]
  · refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
      (hD.mul_left (B ^ 2))
    have h1 := hψ s hs x
    have h2 := hu s hs x
    rw [mul_pow]
    exact mul_le_mul (sq_le_sq' (by linarith [neg_abs_le (ψ s x)]) (le_of_abs_le h1))
      (sq_le_sq' (by linarith [neg_abs_le (u s x)]) (le_of_abs_le h2)) (sq_nonneg _)
      (sq_nonneg _)

/-- The neighbour envelope `Σ_i (D(x + e_i) + D(x - e_i)) + 4 D(x)` of `D`. -/
noncomputable def nbrEnv (D : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  ∑ i : Fin 2, (D (x + unit i) + D (x - unit i)) + 4 * D x

theorem abs_openCond_mul_sub_le (ω : Configuration 2) (i : Fin 2) (x : Vertex 2) (a b : ℝ) :
    |openCond ω i x * (a - b)| ≤ |a| + |b| := by
  rw [abs_mul]
  calc |openCond ω i x| * |a - b| ≤ 1 * |a - b| :=
        mul_le_mul_of_nonneg_right (abs_openCond_le ω i x) (abs_nonneg _)
    _ ≤ |a| + |b| := by
        rw [one_mul]
        have := abs_add_le a (-b)
        rwa [abs_neg, ← sub_eq_add_neg] at this

/-- The Laplacian of the open graph is dominated by the neighbour envelope. -/
theorem abs_openLaplacian_le_nbrEnv (ω : Configuration 2) {u D : Vertex 2 → ℝ}
    (h : ∀ x, |u x| ≤ D x) (x : Vertex 2) : |openLaplacian ω u x| ≤ nbrEnv D x := by
  rw [openLaplacian_eq_sum]
  simp only [nbrEnv, Fin.sum_univ_two]
  have a1 := abs_openCond_mul_sub_le ω 0 x (u (x + unit 0)) (u x)
  have a2 := abs_openCond_mul_sub_le ω 0 (x - unit 0) (u (x - unit 0)) (u x)
  have a3 := abs_openCond_mul_sub_le ω 1 x (u (x + unit 1)) (u x)
  have a4 := abs_openCond_mul_sub_le ω 1 (x - unit 1) (u (x - unit 1)) (u x)
  have b1 := h (x + unit 0)
  have b2 := h (x - unit 0)
  have b3 := h (x + unit 1)
  have b4 := h (x - unit 1)
  have b5 := h x
  refine (abs_add_le _ _).trans ?_
  have c1 := abs_add_le (openCond ω 0 x * (u (x + unit 0) - u x))
    (openCond ω 0 (x - unit 0) * (u (x - unit 0) - u x))
  have c2 := abs_add_le (openCond ω 1 x * (u (x + unit 1) - u x))
    (openCond ω 1 (x - unit 1) * (u (x - unit 1) - u x))
  linarith

theorem summable_sq_nbrEnv {D : Vertex 2 → ℝ} (hD : Summable fun x => D x ^ 2) :
    Summable fun x => nbrEnv D x ^ 2 := by
  have h1 := summable_sq_add_shift hD (unit 0)
  have h2 := summable_sq_sub_shift hD (unit 0)
  have h3 := summable_sq_add_shift hD (unit 1)
  have h4 := summable_sq_sub_shift hD (unit 1)
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
    (((((h1.add h2).add h3).add h4).add hD).mul_left 20)
  simp only [nbrEnv, Fin.sum_univ_two]
  set a := D (x + unit 0)
  set b := D (x - unit 0)
  set c := D (x + unit 1)
  set d := D (x - unit 1)
  set e := D x
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (4 * a - e), sq_nonneg (4 * b - e),
    sq_nonneg (4 * c - e), sq_nonneg (4 * d - e)]

end Rigidity.Green

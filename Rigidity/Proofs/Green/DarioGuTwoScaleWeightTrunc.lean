import Rigidity.Proofs.Green.DarioGuTwoScaleWeightLattice

/-!
# The weight of Proposition 4.3 of Dario–Gu truncated at a radius

The weight `ψ(x) = exp(g(t, |x - y|)/C)` of the proof of Proposition 4.3 of Dario–Gu grows faster
than any Gaussian decays far from `y`, so the series `Σ_x ψ(x)² w(x)²` of Step 2 need not converge
for `w ∈ ℓ²`. The energy argument is run with the truncated weight
`ψ_R(x) = exp(g(t, min(|x - y|, R))/C)` (`dgWeightTrunc`), which is bounded, and `R → ∞` is taken
in the finite sums of `WeightedL2Le`:

* `dgWeightTrunc_edgeKappa_bound`: the discrete (4.41) holds for `ψ_R` with constants independent
  of `R`, since `r ↦ min(r, R)` is `1`-Lipschitz;
* `dgWeightTrunc_le`, `hasDerivAt_dgWeightTrunc`, `abs_dgShapeTimeDeriv_le`: the bounds and the
  time derivative used in the summability layer;
* `weightedL2Le_of_trunc`: bounds on the truncated weighted sums, uniform in `R`, give the bound
  of `WeightedL2Le`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The weight truncated at radius `R`: `ψ_R(x) = exp(g(t, min(|x - y|, R))/C)`. -/
noncomputable def dgWeightTrunc (C t R : ℝ) (y x : Vertex 2) : ℝ :=
  Real.exp (dgShape t (min (latticeDist x y) R) / C)

theorem abs_min_sub_min_le (a b R : ℝ) : |min b R - min a R| ≤ |b - a| := by
  have h5 := le_abs_self (b - a)
  have h6 := neg_abs_le (b - a)
  rw [min_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- **The discrete form of (4.41) for the truncated weight**, with constants independent of `R`. -/
theorem dgWeightTrunc_edgeKappa_bound {K A : ℝ} (hK : 0 < K) (hA : 0 ≤ A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (ω : Configuration 2) (t R : ℝ) (y x : Vertex 2), 1 ≤ t → 0 ≤ R →
        dgWeightTrunc C t R y x ^ 2 *
            (dgShapeTimeDeriv t (min (latticeDist x y) R) / C + A / t) +
          K * edgeKappa ω (dgWeightTrunc C t R y) x ≤ C₁ / t := by
  obtain ⟨C₀, hC₀, h⟩ := dgWeight_bound (K := 2 * K) (A := A) (by positivity) hA
  refine ⟨C₀, hC₀, fun C hC => ?_⟩
  obtain ⟨C₁, hC₁, h1⟩ := h C hC
  refine ⟨C₁, hC₁, fun ω t R y x ht hR => ?_⟩
  set ψ := dgWeightTrunc C t R y with hψ
  set T := dgWeightTrunc C t R y x ^ 2 *
    (dgShapeTimeDeriv t (min (latticeDist x y) R) / C + A / t) with hT
  have hz : ∀ z : Vertex 2, |latticeDist z y - latticeDist x y| ≤ 1 →
      T + 2 * K * (ψ z - ψ x) ^ 2 ≤ C₁ / t := fun z hzd =>
    h1 t (min (latticeDist x y) R) (min (latticeDist z y) R) ht
      (le_min (latticeDist_nonneg _ _) hR) (le_min (latticeDist_nonneg _ _) hR)
      ((abs_min_sub_min_le _ _ R).trans hzd)
  have hk := edgeKappa_le ω ψ x
  simp only [Fin.sum_univ_two] at hk
  have a1 := hz _ (abs_latticeDist_add_unit_sub_le x y 0)
  have a2 := hz _ (abs_latticeDist_sub_unit_sub_le x y 0)
  have a3 := hz _ (abs_latticeDist_add_unit_sub_le x y 1)
  have a4 := hz _ (abs_latticeDist_sub_unit_sub_le x y 1)
  have hKk := mul_le_mul_of_nonneg_left hk hK.le
  nlinarith

theorem dgWeightTrunc_pos (C t R : ℝ) (y x : Vertex 2) : 0 < dgWeightTrunc C t R y x :=
  Real.exp_pos _

/-- `ψ_R ≤ exp(R²/(C t))`. -/
theorem dgWeightTrunc_le {C t R : ℝ} (hC : 0 < C) (ht : 0 < t) (hR : 0 ≤ R) (y x : Vertex 2) :
    dgWeightTrunc C t R y x ≤ Real.exp (R ^ 2 / t / C) := by
  unfold dgWeightTrunc
  refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hC.le)
  have hm0 : 0 ≤ min (latticeDist x y) R := le_min (latticeDist_nonneg _ _) hR
  refine (dgShape_le_sq ht hm0).trans (div_le_div_of_nonneg_right ?_ ht.le)
  exact pow_le_pow_left₀ hm0 (min_le_right _ _) 2

/-- On the ball of radius `R` the truncated weight is `exp(dgExponent C t |x - y|)`. -/
theorem dgWeightTrunc_eq {C t R : ℝ} {y x : Vertex 2} (h : latticeDist x y ≤ R) :
    dgWeightTrunc C t R y x = Real.exp (dgExponent C t (latticeDist x y)) := by
  rw [dgWeightTrunc, min_eq_left h, dgExponent_eq]

/-- `|∂_t g(t, r)| ≤ r²/t² + r/t`. -/
theorem abs_dgShapeTimeDeriv_le {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    |dgShapeTimeDeriv t r| ≤ r ^ 2 / t ^ 2 + r / t := by
  have h1 : 0 ≤ r ^ 2 / t ^ 2 := by positivity
  have h2 : 0 ≤ r / t := div_nonneg hr ht.le
  unfold dgShapeTimeDeriv
  split_ifs
  · rw [abs_neg, abs_of_nonneg h1]; linarith
  · rw [abs_neg, abs_of_nonneg h2]; linarith

/-- The time derivative of the truncated weight:
`∂_t ψ_R(x) = ψ_R(x) ∂_t g(t, min(|x - y|, R))/C`. -/
theorem hasDerivAt_dgWeightTrunc {C t R : ℝ} (ht : 0 < t) (y x : Vertex 2) :
    HasDerivAt (fun s => dgWeightTrunc C s R y x)
      (dgWeightTrunc C t R y x * (dgShapeTimeDeriv t (min (latticeDist x y) R) / C)) t :=
  ((hasDerivAt_dgShape_time (r := min (latticeDist x y) R) ht).div_const C).exp

/-- **From the truncated weights to `WeightedL2Le`**: bounds on the finite sums with the weight
`ψ_R`, uniform in `R ≥ 0`, give the bound with the weight `exp(dgExponent)`. -/
theorem weightedL2Le_of_trunc {K : Set (Vertex 2)} {C t : ℝ} {y : Vertex 2} {f : Vertex 2 → ℝ}
    {B : ℝ}
    (h : ∀ R : ℝ, 0 ≤ R → ∀ S : Finset (Vertex 2), (∀ x ∈ S, x ∈ K) →
      ∑ x ∈ S, (f x * dgWeightTrunc C t R y x) ^ 2 ≤ B ^ 2) :
    WeightedL2Le K C t y f B := by
  intro S hS
  have hR : 0 ≤ ∑ x ∈ S, latticeDist x y := Finset.sum_nonneg fun x _ => latticeDist_nonneg _ _
  refine le_of_eq_of_le (Finset.sum_congr rfl fun x hx => ?_) (h _ hR S hS)
  rw [dgWeightTrunc_eq (Finset.single_le_sum (fun z _ => latticeDist_nonneg z y) hx)]

/-- Bounds on the full series give bounds on the finite sums. -/
theorem sum_le_of_tsum_le {S : Finset (Vertex 2)} {g : Vertex 2 → ℝ} {B : ℝ}
    (hg : Summable fun x => g x ^ 2) (h : ∑' x, g x ^ 2 ≤ B) : ∑ x ∈ S, g x ^ 2 ≤ B :=
  (hg.sum_le_tsum S fun _ _ => sq_nonneg _).trans h

end Rigidity.Green

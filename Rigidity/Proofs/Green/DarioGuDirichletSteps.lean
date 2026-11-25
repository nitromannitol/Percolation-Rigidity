import Rigidity.Proofs.Green.ClusterDirichletPoincare

/-!
# Steps 1, 2 and 5 of the proof of Theorem 5 of Dario–Gu

This file records the parts of Steps 1, 2 and 5 of the proof of Theorem 5 of Dario–Gu (lines
1404-1452 and 1655-1684 of the source) that hold as printed, for unit conductances on the planar
cluster.

* `sum_sq_twoScale_sub_le` (Step 1, lines 1404-1414): if `|F_k| ≤ A` on `V`, the corrector term
  `Σ_k F_k χ_k = w - ū` of (3.22) satisfies `Σ_V (Σ_k F_k χ_k)² ≤ 2 A² Σ_k Σ_V χ_k²`.
* `gradEnergy_eq_clusterGradSq` and `integral_sum_sq_le_of_dirichletPoincare` (Step 2, lines
  1418-1452): with the Poincaré inequality `Σ_V v² ≤ (C r)² E_V(v)` of
  `clusterDirichletPoincareTwo_holds` on `V = 𝒞_∞ ∩ B_r(y)`, a function `v` vanishing on `∂_a V` and
  at the initial time with `‖(∂_t - Δ) v‖_{H̲^{-1}(V)} ≤ B(t)` satisfies
  `∫_{-r²}^0 Σ_V v² ≤ 64 (C r)² (C r + |V|^{1/2})² ∫_{-r²}^0 B²`.
* `dgStepFive` (Step 5, lines 1655-1684, in dimension two): with `β = 1/16`,
  `q = 48 (4 + 2δ')/δ'` and `α = δ'/(128 (2 + δ'))`, the quantity
  `𝓔(r, β, q) = r^{-1/2 + 4β} + log^{1/2}(1 + r) r^{3/(2q) - βδ'/(4 + 2δ')}` of (3.39) is at most
  `C r^{-α}` for `r ≥ 1` (the source's choice of `β`, `q` and `α`).
-/

open MeasureTheory Finset LatticeProb.Percolation

namespace Rigidity.Green

/-! ### Step 1 -/

/-- **Step 1 of the proof of Theorem 5**: `Σ_V (Σ_k F_k χ_k)² ≤ 2 A² Σ_k Σ_V χ_k²` when
`|F_k| ≤ A` on `V`. -/
theorem sum_sq_twoScale_sub_le (V : Finset (Vertex 2)) {F χ : Fin 2 → Vertex 2 → ℝ} {A : ℝ}
    (hF : ∀ k, ∀ x ∈ V, |F k x| ≤ A) :
    ∑ x ∈ V, (∑ k : Fin 2, F k x * χ k x) ^ 2 ≤ 2 * A ^ 2 * ∑ k : Fin 2, ∑ x ∈ V, χ k x ^ 2 := by
  have hpt : ∀ x ∈ V, (∑ k : Fin 2, F k x * χ k x) ^ 2 ≤ 2 * A ^ 2 * (χ 0 x ^ 2 + χ 1 x ^ 2) := by
    intro x hx
    simp only [Fin.sum_univ_two]
    have h0 : (F 0 x) ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hF 0 x hx) 2
    have h1 : (F 1 x) ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hF 1 x hx) 2
    nlinarith [sq_nonneg (F 0 x * χ 0 x - F 1 x * χ 1 x), mul_le_mul_of_nonneg_right h0
      (sq_nonneg (χ 0 x)), mul_le_mul_of_nonneg_right h1 (sq_nonneg (χ 1 x))]
  calc ∑ x ∈ V, (∑ k : Fin 2, F k x * χ k x) ^ 2
      ≤ ∑ x ∈ V, 2 * A ^ 2 * (χ 0 x ^ 2 + χ 1 x ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * A ^ 2 * ∑ k : Fin 2, ∑ x ∈ V, χ k x ^ 2 := by
        rw [← Finset.mul_sum, Fin.sum_univ_two, Finset.sum_add_distrib]

/-! ### Step 2 -/

theorem gradEnergy_eq_clusterGradSq (ω : Configuration 2) (V : Finset (Vertex 2))
    (u : Vertex 2 → ℝ) : gradEnergy ω V u = clusterGradSq ω V u := by
  unfold gradEnergy clusterGradSq
  simp only [openGradNorm_eq_sum_filter]

/-- **Step 2 of the proof of Theorem 5** with the Poincaré inequality of
`ClusterDirichletPoincareTwo` (in the deterministic form `Σ_V v² ≤ (C r)² E_V(v)` for functions
vanishing on `∂_a V`). -/
theorem integral_sum_sq_le_of_dirichletPoincare (ω : Configuration 2) {V : Finset (Vertex 2)}
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hpoinc : ∀ u : Vertex 2 → ℝ, (∀ x ∈ V, x ∉ openInterior ω V → u x = 0) →
      ∑ x ∈ V, u x ^ 2 ≤ (C * r) ^ 2 * gradEnergy ω V u)
    {v dv g : ℝ → Vertex 2 → ℝ} {B : ℝ → ℝ}
    (hcont : ∀ x ∈ V, ContinuousOn (fun t => v t x) (Set.Icc (-r ^ 2) 0))
    (hderiv : ∀ x ∈ V, ∀ t ∈ Set.Ioo (-r ^ 2) 0, HasDerivAt (fun s => v s x) (dv t x) t)
    (hdv : ∀ x ∈ V, IntervalIntegrable (fun t => dv t x) volume (-r ^ 2) 0)
    (hbd : ∀ t ∈ Set.Icc (-r ^ 2) 0, ∀ x ∈ V, x ∉ openInterior ω V → v t x = 0)
    (hinit : ∀ x ∈ V, v (-r ^ 2) x = 0)
    (heq : ∀ t ∈ Set.Ioo (-r ^ 2) 0, ∀ x ∈ openInterior ω V,
      dv t x - openLaplacian ω (v t) x = g t x)
    (hweak : ∀ t ∈ Set.Ioo (-r ^ 2) 0, WeakNormLe ω V (g t) (B t))
    (hB : IntervalIntegrable (fun t => B t ^ 2) volume (-r ^ 2) 0) :
    ∫ t in (-r ^ 2)..0, ∑ x ∈ V, v t x ^ 2 ≤
      64 * (C * r) ^ 2 * (C * r + Real.sqrt V.card) ^ 2 * ∫ t in (-r ^ 2)..0, B t ^ 2 := by
  refine integral_sum_sq_le_of_energy ω (by nlinarith [sq_nonneg r]) (mul_nonneg hC hr) hcont
    hderiv hdv hbd hinit heq hweak hB fun t ht => ?_
  rw [← gradEnergy_eq_clusterGradSq]
  exact hpoinc (v t) (hbd t (Set.Ioo_subset_Icc_self ht))

/-! ### Step 5 -/

/-- **Step 5 of the proof of Theorem 5** in dimension two: the choice `β = 1/16`,
`q = 48 (4 + 2δ')/δ'` gives `𝓔(r, β, q) ≤ C r^{-α}` with `α = δ'/(128 (2 + δ'))`. -/
theorem dgStepFive {δ' : ℝ} (hδ : 0 < δ') :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      r ^ (-(1 / 2 : ℝ) + 4 * (1 / 16)) + Real.sqrt (Real.log (1 + r)) *
          r ^ (3 / (2 * (48 * (4 + 2 * δ') / δ')) - 1 / 16 * δ' / (4 + 2 * δ')) ≤
        C * r ^ (-(δ' / (128 * (2 + δ')))) := by
  set α := δ' / (128 * (2 + δ')) with hα
  have hα0 : 0 < α := by positivity
  have hα4 : α ≤ 1 / 4 := by
    rw [hα, div_le_iff₀ (by positivity)]
    nlinarith
  have hexp1 : -(1 / 2 : ℝ) + 4 * (1 / 16) = -(1 / 4) := by norm_num
  have hexp2 : 3 / (2 * (48 * (4 + 2 * δ') / δ')) - 1 / 16 * δ' / (4 + 2 * δ') = -(2 * α) := by
    rw [hα]
    field_simp
    ring
  refine ⟨1 + 2 ^ α / Real.sqrt (2 * α), by positivity, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  rw [hexp1, hexp2]
  have h1 : r ^ (-(1 / 4 : ℝ)) ≤ r ^ (-α) :=
    Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have hlog : Real.log (1 + r) ≤ (1 + r) ^ (2 * α) / (2 * α) :=
    Real.log_le_rpow_div (by linarith) (by positivity)
  have hsq : Real.sqrt ((1 + r) ^ (2 * α) / (2 * α)) = (1 + r) ^ α / Real.sqrt (2 * α) := by
    rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 2 * α)]
    congr 1
    rw [show 2 * α = α * 2 by ring, Real.rpow_mul (by linarith), Real.rpow_two,
      Real.sqrt_sq (by positivity)]
  have h2 : Real.sqrt (Real.log (1 + r)) ≤ (2 * r) ^ α / Real.sqrt (2 * α) := by
    calc Real.sqrt (Real.log (1 + r)) ≤ Real.sqrt ((1 + r) ^ (2 * α) / (2 * α)) :=
          Real.sqrt_le_sqrt hlog
      _ = (1 + r) ^ α / Real.sqrt (2 * α) := hsq
      _ ≤ (2 * r) ^ α / Real.sqrt (2 * α) := by
          gcongr
          linarith
  have h3 : (2 * r) ^ α * r ^ (-(2 * α)) = 2 ^ α * r ^ (-α) := by
    rw [Real.mul_rpow (by norm_num) hr0.le, mul_assoc, ← Real.rpow_add hr0]
    congr 2
    ring
  have hpos : 0 ≤ r ^ (-(2 * α)) := Real.rpow_nonneg hr0.le _
  calc r ^ (-(1 / 4 : ℝ)) + Real.sqrt (Real.log (1 + r)) * r ^ (-(2 * α))
      ≤ r ^ (-α) + (2 * r) ^ α / Real.sqrt (2 * α) * r ^ (-(2 * α)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_right h2 hpos)
    _ = r ^ (-α) + 2 ^ α / Real.sqrt (2 * α) * r ^ (-α) := by
        rw [div_mul_eq_mul_div, h3, mul_div_right_comm]
    _ = (1 + 2 ^ α / Real.sqrt (2 * α)) * r ^ (-α) := by ring

end Rigidity.Green

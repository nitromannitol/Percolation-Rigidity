import Rigidity.Proofs.Green.OpenHeatSemigroup
import Rigidity.Proofs.Green.DarioGuGaussian

/-!
# From the weighted `L²` estimate to the pointwise estimate (Dario–Gu, (4.48))

For `x, z` in an open component `K`, the semigroup property and the symmetry of the heat kernel
split `p(2s, x, z) - θ^{-1} p̄(2s, x - z)` into (4.48)-a1, (4.48)-a2 and (4.48)-b:

`Σ_{y ∈ K} (p(s, y, x) - θ^{-1} p̄(s, y - x)) p(s, y, z)
  + θ^{-1} Σ_{y ∈ K} p̄(s, x - y) (p(s, y, z) - θ^{-1} p̄(s, y - z))
  + θ^{-1} (θ^{-1} Σ_{y ∈ K} p̄(s, x - y) p̄(s, y - z) - p̄(2s, x - z))`.

The first two are bounded by the Cauchy–Schwarz inequality against the weights centred at `x` and
`z`, with the weighted `L²` estimate at `x` and `z`, Barlow's bound at `z` (Theorem 4) for the
first and the Gaussian bound for the second (`pointwise_of_weightedL2`).
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

theorem openHeat_eq_zero_of_mem_of_notMem {ω : Configuration 2} {K : OpenComponent ω}
    {x y : Vertex 2} (hx : x ∈ K.supp) (hy : y ∉ K.supp) (t : ℝ) : openHeat ω t x y = 0 := by
  apply openHeat_eq_zero_of_not_reachable
  intro hr
  apply hy
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  rw [← hx]
  exact (SimpleGraph.ConnectedComponent.sound hr).symm

/-- The semigroup property on a component. -/
theorem hasSum_openHeat_mul_supp {ω : Configuration 2} {K : OpenComponent ω} {x : Vertex 2}
    (hx : x ∈ K.supp) (z : Vertex 2) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    HasSum (fun y : K.supp => openHeat ω s x y * openHeat ω t y z) (openHeat ω (s + t) x z) := by
  have h := hasSum_openHeat_mul ω hs ht x z
  have hsupp : Function.support (fun y => openHeat ω s x y * openHeat ω t y z) ⊆ K.supp := by
    intro y hy
    by_contra hy'
    apply hy
    simp [openHeat_eq_zero_of_mem_of_notMem hx hy' s]
  exact (hasSum_subtype_iff_of_support_subset hsupp).2 h

theorem openHeat_nonneg' (ω : Configuration 2) {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) :
    0 ≤ openHeat ω t x y :=
  vsrwHeat_nonneg (by norm_num) (openGraph_degree_le_four ω) ht x y

/-- **Dario–Gu, (4.48)**: the pointwise estimate from the weighted `L²` estimates at `x` and `z`
at time `s`, Barlow's bound at `z` and a bound `Dd` of the term (4.48)-b. -/
theorem pointwise_of_weightedL2 {θ σ Cw CB : ℝ} (hθ : 0 < θ) (hσ : 0 < σ) (hCw : 0 < Cw)
    (hCB : 0 < CB) : ∃ M C₃ : ℝ, 0 < M ∧ 0 < C₃ ∧
    ∀ (ω : Configuration 2) (K : OpenComponent ω) (s B Dd : ℝ), 1 ≤ s → 0 ≤ B →
      ∀ x ∈ K.supp, ∀ z ∈ K.supp,
      WeightedL2Le K.supp Cw s x (fun y => openHeat ω s y x - θ⁻¹ * latticeGaussian σ s y x) B →
      WeightedL2Le K.supp Cw s z (fun y => openHeat ω s y z - θ⁻¹ * latticeGaussian σ s y z) B →
      (∀ y ∈ K.supp, openHeat ω s y z ≤ dgPhi CB s (latticeDist y z)) →
      |θ⁻¹ * ∑' y : K.supp, latticeGaussian σ s x y * latticeGaussian σ s y z -
          latticeGaussian σ (s + s) x z| ≤ Dd →
      |openHeat ω (s + s) x z - θ⁻¹ * latticeGaussian σ (s + s) x z| ≤
        M * B * s ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(dgShape (2 * s) (latticeDist x z) / (4 * C₃))) + θ⁻¹ * Dd := by
  set CG := max (2 * σ) (1 / (2 * Real.pi * σ)) with hCG
  have hCG0 : 0 < CG := lt_max_of_lt_left (by positivity)
  obtain ⟨M₁, hM₁, h₁⟩ := sum_sq_dgPhi_mul_exp_le hCB hCw
  obtain ⟨M₂, hM₂, h₂⟩ := sum_sq_dgPhi_mul_exp_le hCG0 hCw
  set C₃ := max CB (max CG Cw) with hC₃
  have hC₃0 : 0 < C₃ := lt_max_of_lt_left hCB
  refine ⟨Real.sqrt M₁ + θ⁻¹ * Real.sqrt M₂, C₃, by positivity, hC₃0, ?_⟩
  intro ω K s B Dd hs hB x hx z hz hLx hLz hBar hb
  have hs0 : 0 < s := by linarith
  set P := fun (a b : Vertex 2) => openHeat ω s a b with hP
  set G := fun (a b : Vertex 2) => latticeGaussian σ s a b with hG
  set r := latticeDist x z with hr
  set g2s := dgShape (2 * s) r
  have hg0 : 0 ≤ g2s := dgShape_nonneg (by positivity) (latticeDist_nonneg x z)
  -- the bounds of the second factors
  set B₁ := Real.sqrt M₁ * s ^ (-(1 / 2 : ℝ)) * Real.exp (-(g2s / (4 * max CB Cw))) with hB₁
  set B₂ := Real.sqrt M₂ * s ^ (-(1 / 2 : ℝ)) * Real.exp (-(g2s / (4 * max CG Cw))) with hB₂
  have hB₁sq : B₁ ^ 2 = M₁ * s⁻¹ * Real.exp (-(g2s / (2 * max CB Cw))) := by
    rw [hB₁, mul_pow, mul_pow, Real.sq_sqrt hM₁.le, rpow_neg_half_sq hs0, exp_sq]
    congr 2
    field_simp
    ring
  have hB₂sq : B₂ ^ 2 = M₂ * s⁻¹ * Real.exp (-(g2s / (2 * max CG Cw))) := by
    rw [hB₂, mul_pow, mul_pow, Real.sq_sqrt hM₂.le, rpow_neg_half_sq hs0, exp_sq]
    congr 2
    field_simp
    ring
  have hwpos : ∀ (c : Vertex 2) (y : Vertex 2), 0 < Real.exp (dgExponent Cw s (latticeDist y c)) :=
    fun _ _ => Real.exp_pos _
  -- first term
  have hg1 : ∀ S : Finset (Vertex 2), (∀ y ∈ S, y ∈ K.supp) →
      ∑ y ∈ S, (P y z / Real.exp (dgExponent Cw s (latticeDist y x))) ^ 2 ≤ B₁ ^ 2 := by
    intro S hS
    rw [hB₁sq]
    refine le_trans (Finset.sum_le_sum fun y hy => ?_) (h₁ s hs x z S)
    rw [div_eq_mul_inv, ← Real.exp_neg]
    have h0 : 0 ≤ P y z := openHeat_nonneg' ω hs0.le y z
    exact pow_le_pow_left₀ (mul_nonneg h0 (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_right (hBar y (hS y hy)) (Real.exp_pos _).le) 2
  have hg2 : ∀ S : Finset (Vertex 2), (∀ y ∈ S, y ∈ K.supp) →
      ∑ y ∈ S, (G x y / Real.exp (dgExponent Cw s (latticeDist y z))) ^ 2 ≤ B₂ ^ 2 := by
    intro S _
    rw [hB₂sq]
    have := h₂ s hs z x S
    rw [latticeDist_comm z x] at this
    refine le_trans (Finset.sum_le_sum fun y _ => ?_) this
    rw [div_eq_mul_inv, ← Real.exp_neg]
    have h0 : 0 ≤ G x y := (latticeGaussian_pos hσ hs0 x y).le
    have hGle : G x y ≤ dgPhi CG s (latticeDist y x) := by
      have h1 := const_mul_latticeGaussian_le_dgPhi (c := 1) (C := CG) hσ hs0 (le_max_left _ _)
        (le_max_right _ _) y x
      rw [one_mul] at h1
      exact (latticeGaussian_symm σ s x y).trans_le h1
    exact pow_le_pow_left₀ (mul_nonneg h0 (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_right hGle (Real.exp_pos _).le) 2
  obtain ⟨hS1, hT1⟩ := summable_tsum_abs_mul_le (K := K.supp)
    (f := fun y => openHeat ω s y x - θ⁻¹ * latticeGaussian σ s y x) (g := fun y => P y z)
    (hwpos x) (fun S hS => hLx S hS) hg1 hB (by positivity)
  obtain ⟨hS2, hT2⟩ := summable_tsum_abs_mul_le (K := K.supp)
    (f := fun y => openHeat ω s y z - θ⁻¹ * latticeGaussian σ s y z) (g := fun y => G x y)
    (hwpos z) (fun S hS => hLz S hS) hg2 hB (by positivity)
  -- the decomposition
  have hsg := hasSum_openHeat_mul_supp hx z hs0.le hs0.le
  set f1 := fun y : K.supp => (openHeat ω s y x - θ⁻¹ * latticeGaussian σ s y x) * P y z
  set f2 := fun y : K.supp => (openHeat ω s y z - θ⁻¹ * latticeGaussian σ s y z) * G x y
  have hsum1 : Summable f1 := hS1.of_abs
  have hsum2 : Summable f2 := hS2.of_abs
  have hdec : ∀ y : K.supp, openHeat ω s x y * openHeat ω s y z =
      f1 y + θ⁻¹ * f2 y + θ⁻¹ * (θ⁻¹ * (G x y * G y z)) := by
    intro y
    simp only [f1, f2, hP, hG]
    rw [openHeat_symm ω s x y, latticeGaussian_symm σ s y x]
    ring
  have hgg : HasSum (fun y : K.supp => θ⁻¹ * (θ⁻¹ * (G x y * G y z)))
      (openHeat ω (s + s) x z - ∑' y, f1 y - θ⁻¹ * ∑' y, f2 y) := by
    have h0 := (hsg.sub hsum1.hasSum).sub (hsum2.hasSum.mul_left θ⁻¹)
    have heq : (fun y : K.supp => θ⁻¹ * (θ⁻¹ * (G x y * G y z))) =
        fun y : K.supp => openHeat ω s x y * openHeat ω s y z - f1 y - θ⁻¹ * f2 y := by
      funext y
      rw [hdec y]
      ring
    rw [heq]
    exact h0
  have hgg' : θ⁻¹ * (θ⁻¹ * ∑' y : K.supp, G x y * G y z) =
      openHeat ω (s + s) x z - ∑' y, f1 y - θ⁻¹ * ∑' y, f2 y := by
    rw [← hgg.tsum_eq, tsum_mul_left, tsum_mul_left]
  have hkey : openHeat ω (s + s) x z - θ⁻¹ * latticeGaussian σ (s + s) x z =
      ∑' y, f1 y + θ⁻¹ * ∑' y, f2 y +
        θ⁻¹ * (θ⁻¹ * ∑' y : K.supp, G x y * G y z - latticeGaussian σ (s + s) x z) := by
    rw [mul_sub, hgg']
    ring
  have hA1 : |∑' y, f1 y| ≤ B * B₁ :=
    (abs_tsum_le_tsum_abs hS1).trans hT1
  have hA2 : |∑' y, f2 y| ≤ B * B₂ :=
    (abs_tsum_le_tsum_abs hS2).trans hT2
  have hB₁le : B₁ ≤ Real.sqrt M₁ * s ^ (-(1 / 2 : ℝ)) * Real.exp (-(g2s / (4 * C₃))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hg0 (by positivity)
      (by have : max CB Cw ≤ C₃ := max_le (le_max_left _ _)
              ((le_max_right _ _).trans (le_max_right _ _))
          linarith)
  have hB₂le : B₂ ≤ Real.sqrt M₂ * s ^ (-(1 / 2 : ℝ)) * Real.exp (-(g2s / (4 * C₃))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hg0 (by positivity)
      (by have : max CG Cw ≤ C₃ := max_le ((le_max_left _ _).trans (le_max_right _ _))
              ((le_max_right _ _).trans (le_max_right _ _))
          linarith)
  rw [hkey]
  have hθi : 0 < θ⁻¹ := inv_pos.2 hθ
  calc |∑' y, f1 y + θ⁻¹ * ∑' y, f2 y +
        θ⁻¹ * (θ⁻¹ * ∑' y : K.supp, G x y * G y z - latticeGaussian σ (s + s) x z)|
      ≤ |∑' y, f1 y| + θ⁻¹ * |∑' y, f2 y| +
          θ⁻¹ * |θ⁻¹ * ∑' y : K.supp, G x y * G y z - latticeGaussian σ (s + s) x z| := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans ?_) ?_
        · rw [abs_mul, abs_of_pos hθi]
        · rw [abs_mul, abs_of_pos hθi]
    _ ≤ B * B₁ + θ⁻¹ * (B * B₂) + θ⁻¹ * Dd := by
        gcongr
    _ ≤ B * (Real.sqrt M₁ * s ^ (-(1 / 2 : ℝ)) * Real.exp (-(g2s / (4 * C₃)))) +
          θ⁻¹ * (B * (Real.sqrt M₂ * s ^ (-(1 / 2 : ℝ)) * Real.exp (-(g2s / (4 * C₃))))) +
          θ⁻¹ * Dd := by
        gcongr
    _ = (Real.sqrt M₁ + θ⁻¹ * Real.sqrt M₂) * B * s ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(g2s / (4 * C₃))) + θ⁻¹ * Dd := by ring

end Rigidity.Green

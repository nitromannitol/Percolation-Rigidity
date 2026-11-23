import Rigidity.Proofs.Regularity.PlanarCorrectorL2

/-!
# The maximum of the minimal scales over a box, by Borel–Cantelli

For random scales `𝒳_z`, `z ∈ ℤ²`, with `E[exp((𝒳_z/θ)^s)] ≤ 2` uniformly in `z`, and every
`γ > 0`, almost surely `𝒳_z ≤ 2^{kγ}` for all `z` in the box `{|z_i| ≤ 2^{k+3}}` and all large `k`
(`ae_eventually_scale_le`). The Chebyshev bound `P(𝒳_z > t) ≤ 2 e^{-(t/θ)^s}`, the bound
`e^{-x} ≤ n!/x^n` and the union over the `(2^{k+4}+1)²` points of the box give
`P(∃ z, 𝒳_z > 2^{kγ}) ≤ A 2^{-k}`, which is summable. This is the step from the minimal scale at
one point to its maximum over `𝒞_∞ ∩ B_r` in the Remark after (1.19) of Armstrong and Dario
(arXiv:1609.09431v2), with the Borel–Cantelli lemma in place of (1.8).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory Filter LatticeProb.Percolation
open scoped ENNReal Nat

/-- The box `{z ∈ ℤ² : |z_i| ≤ 2^{k+3}}`. -/
noncomputable def scaleBox (k : ℕ) : Finset (Vertex 2) :=
  Fintype.piFinset fun _ => Finset.Icc (-(2 : ℤ) ^ (k + 3)) (2 ^ (k + 3))

theorem mem_scaleBox {k : ℕ} {z : Vertex 2} : z ∈ scaleBox k ↔ ∀ i, |z i| ≤ 2 ^ (k + 3) := by
  simp only [scaleBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem card_scaleBox_le (k : ℕ) : ((scaleBox k).card : ℝ) ≤ 4 ^ 5 * 4 ^ k := by
  have hI : ((Finset.Icc (-(2 : ℤ) ^ (k + 3)) (2 ^ (k + 3))).card : ℝ) =
      2 * (2 : ℝ) ^ (k + 3) + 1 := by
    rw [Int.card_Icc, show (2 : ℤ) ^ (k + 3) + 1 - -(2 : ℤ) ^ (k + 3) = 2 * 2 ^ (k + 3) + 1 by ring]
    have h0 : (0 : ℤ) ≤ 2 * 2 ^ (k + 3) + 1 := by positivity
    have e := Int.toNat_of_nonneg h0
    have : (((2 * 2 ^ (k + 3) + 1 : ℤ).toNat : ℕ) : ℝ) = (((2 * 2 ^ (k + 3) + 1 : ℤ).toNat : ℤ) : ℝ) :=
      rfl
    rw [this, e]
    push_cast
    ring
  have h1 : ((scaleBox k).card : ℝ) = (2 * (2 : ℝ) ^ (k + 3) + 1) ^ 2 := by
    rw [scaleBox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [hI]
  rw [h1]
  have h2 : (2 * (2 : ℝ) ^ (k + 3) + 1) ≤ 2 ^ (k + 5) := by
    have : (1 : ℝ) ≤ 2 ^ (k + 3) := one_le_pow₀ (by norm_num)
    have e : (2 : ℝ) ^ (k + 5) = 4 * 2 ^ (k + 3) := by ring
    linarith
  calc (2 * (2 : ℝ) ^ (k + 3) + 1) ^ 2 ≤ ((2 : ℝ) ^ (k + 5)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
    _ = 4 ^ 5 * 4 ^ k := by
        rw [← pow_mul, show (k + 5) * 2 = 2 * (k + 5) by ring, pow_mul]
        norm_num
        ring

/-- The Chebyshev bound for a random variable with an exponential moment. -/
theorem measureReal_lt_le {p : unitInterval} {Y : Configuration 2 → ℝ} {s θ t : ℝ} (hs : 0 < s)
    (hθ : 0 < θ) (ht : 0 ≤ t)
    (hYi : Integrable (fun ω => Real.exp (Real.rpow (Y ω / θ) s)) (latticeBondLaw 2 p))
    (hYb : (∫ ω, Real.exp (Real.rpow (Y ω / θ) s) ∂latticeBondLaw 2 p) ≤ 2) :
    (latticeBondLaw 2 p).real {ω | t < Y ω} ≤ 2 / Real.exp (Real.rpow (t / θ) s) := by
  have hE : 0 < Real.exp (Real.rpow (t / θ) s) := Real.exp_pos _
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := latticeBondLaw 2 p)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hYi
    (Real.exp (Real.rpow (t / θ) s))
  have hsub : {ω | t < Y ω} ⊆
      {ω | Real.exp (Real.rpow (t / θ) s) ≤ Real.exp (Real.rpow (Y ω / θ) s)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    refine Real.exp_le_exp.2 (Real.rpow_le_rpow (div_nonneg ht hθ.le) ?_ hs.le)
    exact div_le_div_of_nonneg_right hω.le hθ.le
  have hmono : (latticeBondLaw 2 p).real {ω | t < Y ω} ≤ (latticeBondLaw 2 p).real
      {ω | Real.exp (Real.rpow (t / θ) s) ≤ Real.exp (Real.rpow (Y ω / θ) s)} :=
    measureReal_mono hsub
  rw [le_div_iff₀ hE]
  calc (latticeBondLaw 2 p).real {ω | t < Y ω} * Real.exp (Real.rpow (t / θ) s)
      ≤ Real.exp (Real.rpow (t / θ) s) * (latticeBondLaw 2 p).real
          {ω | Real.exp (Real.rpow (t / θ) s) ≤ Real.exp (Real.rpow (Y ω / θ) s)} := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hmono hE.le
    _ ≤ _ := hM
    _ ≤ 2 := hYb

/-- `e^{-x} ≤ n! / x^n` for `x > 0`. -/
theorem inv_exp_le_factorial_div_pow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    1 / Real.exp x ≤ (n ! : ℝ) / x ^ n := by
  have h := Real.pow_div_factorial_le_exp x hx.le n
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_div_iff₀ (Real.exp_pos x) (by positivity)]
  rw [div_le_iff₀ hf] at h
  linarith

/-- **The maximum of the minimal scales over the boxes**, almost surely for all large `k`. -/
theorem ae_eventually_scale_le {p : unitInterval} {Y : Vertex 2 → Configuration 2 → ℝ}
    {s θ γ : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hγ : 0 < γ)
    (hYi : ∀ z, Integrable (fun ω => Real.exp (Real.rpow (Y z ω / θ) s)) (latticeBondLaw 2 p))
    (hYb : ∀ z, (∫ ω, Real.exp (Real.rpow (Y z ω / θ) s) ∂latticeBondLaw 2 p) ≤ 2) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ k : ℕ in atTop, ∀ z ∈ scaleBox k,
      Y z ω ≤ (2 : ℝ) ^ ((k : ℝ) * γ) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 3 ≤ γ * s * n := by
    obtain ⟨n, hn⟩ := exists_nat_ge (3 / (γ * s))
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  set E : ℕ → Set (Configuration 2) := fun k =>
    ⋃ z ∈ scaleBox k, {ω | (2 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} with hEdef
  set A : ℝ := 2 * 4 ^ 5 * (n ! : ℝ) * θ ^ (s * n) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hbound : ∀ k : ℕ, (latticeBondLaw 2 p) (E k) ≤ ENNReal.ofReal (A * (1 / 2) ^ k) := by
    intro k
    have ht0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * γ) := by positivity
    have hx : 0 < Real.rpow ((2 : ℝ) ^ ((k : ℝ) * γ) / θ) s :=
      Real.rpow_pos_of_pos (by positivity) _
    have hxpow : Real.rpow ((2 : ℝ) ^ ((k : ℝ) * γ) / θ) s ^ n =
        (2 : ℝ) ^ ((k : ℝ) * (γ * s * n)) / θ ^ (s * n) := by
      change (((2 : ℝ) ^ ((k : ℝ) * γ) / θ) ^ s) ^ n = _
      rw [Real.div_rpow (by positivity) hθ.le, div_pow, ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul hθ.le]
      congr 2
      ring
    have hpt : ∀ z ∈ scaleBox k, (latticeBondLaw 2 p).real
        {ω | (2 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} ≤
          2 * (n ! : ℝ) * θ ^ (s * n) / (2 : ℝ) ^ ((k : ℝ) * (γ * s * n)) := by
      intro z _
      refine (measureReal_lt_le hs hθ ht0 (hYi z) (hYb z)).trans ?_
      have h1 := inv_exp_le_factorial_div_pow hx n
      rw [hxpow] at h1
      have e : 2 / Real.exp (Real.rpow ((2 : ℝ) ^ ((k : ℝ) * γ) / θ) s) =
          2 * (1 / Real.exp (Real.rpow ((2 : ℝ) ^ ((k : ℝ) * γ) / θ) s)) := by ring
      rw [e]
      calc 2 * (1 / Real.exp (Real.rpow ((2 : ℝ) ^ ((k : ℝ) * γ) / θ) s))
          ≤ 2 * ((n ! : ℝ) / ((2 : ℝ) ^ ((k : ℝ) * (γ * s * n)) / θ ^ (s * n))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 2 * (n ! : ℝ) * θ ^ (s * n) / (2 : ℝ) ^ ((k : ℝ) * (γ * s * n)) := by
            field_simp
    have h8 : (8 : ℝ) ^ k ≤ (2 : ℝ) ^ ((k : ℝ) * (γ * s * n)) := by
      calc (8 : ℝ) ^ k = ((2 : ℝ) ^ (3 : ℝ)) ^ (k : ℝ) := by
            rw [show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num, Real.rpow_natCast]
        _ = (2 : ℝ) ^ ((k : ℝ) * 3) := by rw [← Real.rpow_mul (by norm_num), mul_comm]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg k))
    have hunion : (latticeBondLaw 2 p) (E k) ≤ ∑ z ∈ scaleBox k,
        (latticeBondLaw 2 p) {ω | (2 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} :=
      measure_biUnion_finset_le _ _
    refine hunion.trans ?_
    have hfin : ∀ z ∈ scaleBox k, (latticeBondLaw 2 p) {ω | (2 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} =
        ENNReal.ofReal ((latticeBondLaw 2 p).real {ω | (2 : ℝ) ^ ((k : ℝ) * γ) < Y z ω}) :=
      fun z _ => (ofReal_measureReal (measure_ne_top _ _)).symm
    rw [Finset.sum_congr rfl hfin, ← ENNReal.ofReal_sum_of_nonneg fun _ _ => measureReal_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∑ z ∈ scaleBox k, (latticeBondLaw 2 p).real {ω | (2 : ℝ) ^ ((k : ℝ) * γ) < Y z ω}
        ≤ ∑ _z ∈ scaleBox k, 2 * (n ! : ℝ) * θ ^ (s * n) / (2 : ℝ) ^ ((k : ℝ) * (γ * s * n)) :=
          Finset.sum_le_sum hpt
      _ = (scaleBox k).card * (2 * (n ! : ℝ) * θ ^ (s * n) /
            (2 : ℝ) ^ ((k : ℝ) * (γ * s * n))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 ^ 5 * 4 ^ k * (2 * (n ! : ℝ) * θ ^ (s * n) / 8 ^ k) := by
          gcongr
          · exact card_scaleBox_le k
      _ = A * (1 / 2) ^ k := by
          rw [hAdef, div_pow, one_pow, show (8 : ℝ) ^ k = 4 ^ k * 2 ^ k by
            rw [← mul_pow]; norm_num]
          field_simp
  have hsum : ∑' k, (latticeBondLaw 2 p) (E k) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with k hk z hz
  by_contra hlt
  push Not at hlt
  exact hk (Set.mem_biUnion hz hlt)

end Rigidity.Proofs.Regularity

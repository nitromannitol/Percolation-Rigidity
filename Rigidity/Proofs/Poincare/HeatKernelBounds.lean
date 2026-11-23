import Rigidity.Proofs.Poincare.LatticeHeatKernel

/-!
# Upper bounds for the tilted heat kernel of `ℤ²`

For the weighted maximal inequality of the lattice form of Armstrong, Kuusi and Mourrat,
Proposition D.2 (Step 2, the maximal bound (D.9) with the weights of Remark D.6), the heat
kernel at times `s ≤ T` is multiplied by `e^{a|z|₁}` with `a max(√T, 1) ≤ 1` and `a ≤ 1/6`.
With `σ = max(√s, 1)`:

* `exists_lineKernel_mul_exp_le`: `q_{2s}(k) e^{a|k|} ≤ (C/σ) e^{-|k|/σ}`, from the local limit
  theorem of Lattice-Probability (`exists_abs_lineKernel_sub_lineGauss_le`) when `|k| < 20 s`,
  `s ≥ 1`, and from the Chernoff bound `q_{2s}(k) ≤ e^{-2|k| + 2s(cosh 2 - 1)}` when `|k| ≥ 20 s`;
* `exists_openHeat_mul_exp_le`: `Φ_s(x, y) e^{a|y - x|₁} ≤ (C²/σ²) e^{-|y - x|₁/σ}`.
-/

open LatticeProb LatticeProb.Percolation Rigidity.Green LatticeProb.ContinuousTime

namespace Rigidity.Poincare

theorem cosh_two_sub_one_le : Real.cosh 2 - 1 ≤ 4 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have h4 : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.cosh_eq]
  nlinarith

/-- `√s ≤ 1 + s`. -/
theorem sqrt_le_one_add (s : ℝ) (hs : 0 ≤ s) : Real.sqrt s ≤ 1 + s := by
  rcases le_total s 1 with h | h
  · have := Real.sqrt_le_one.2 h
    linarith
  · have h1 : 1 ≤ Real.sqrt s := Real.one_le_sqrt.2 h
    nlinarith [Real.mul_self_sqrt hs]

/-- **The tilted one-dimensional kernel**: there is `C` such that for `s ≥ 0`, `0 ≤ a ≤ 1/6` with
`a max(√s, 1) ≤ 1`, `q_{2s}(k) e^{a|k|} ≤ (C/σ) e^{-|k|/σ}`, `σ = max(√s, 1)`. -/
theorem exists_lineKernel_mul_exp_le : ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → ∀ a : ℝ, 0 ≤ a →
    a ≤ 1 / 6 → a * max (Real.sqrt s) 1 ≤ 1 → ∀ k : ℤ,
      lineKernel (2 * s) k * Real.exp (a * |(k : ℝ)|) ≤
        C / max (Real.sqrt s) 1 * Real.exp (-|(k : ℝ)| / max (Real.sqrt s) 1) := by
  obtain ⟨C₀, hC₀, hlclt⟩ := exists_abs_lineKernel_sub_lineGauss_le
  refine ⟨(1 + C₀) * Real.exp 220, ?_, fun s hs a ha0 ha6 haσ k => ?_⟩
  · have : (1 : ℝ) ≤ Real.exp 220 := Real.one_le_exp (by norm_num)
    nlinarith
  set K := |(k : ℝ)| with hK
  set σ := max (Real.sqrt s) 1 with hσ
  have hK0 : 0 ≤ K := abs_nonneg _
  have hσ1 : 1 ≤ σ := le_max_right _ _
  have hσ0 : 0 < σ := by linarith
  have hC1 : Real.exp 40 ≤ (1 + C₀) * Real.exp 220 := by
    have : Real.exp 40 ≤ Real.exp 220 := Real.exp_le_exp.2 (by norm_num)
    nlinarith [Real.exp_pos 220]
  have hq0 : 0 ≤ lineKernel (2 * s) k := lineKernel_nonneg (by linarith) k
  have hexpK : Real.exp (-K) ≤ Real.exp (-K / σ) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hσ0]
    nlinarith
  rcases le_or_gt (20 * s) K with hKL | hKL
  · -- the Chernoff regime
    have hq := lineKernel_le_exp_abs (by linarith : 0 ≤ 2 * s) k 2
    have hc := cosh_two_sub_one_le
    have h1 : lineKernel (2 * s) k * Real.exp (a * K) ≤ Real.exp (-(7 / 5) * K) := by
      calc lineKernel (2 * s) k * Real.exp (a * K)
          ≤ Real.exp (-(2 * K) + 2 * s * (Real.cosh 2 - 1)) * Real.exp (a * K) :=
            mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
        _ = Real.exp (-(2 * K) + 2 * s * (Real.cosh 2 - 1) + a * K) := by rw [← Real.exp_add]
        _ ≤ Real.exp (-(7 / 5) * K) := by
            refine Real.exp_le_exp.2 ?_
            nlinarith
    have hσle : σ ≤ 1 + 2 / 5 * K := by
      have := sqrt_le_one_add s hs
      exact max_le (by linarith) (by linarith)
    have h2 : σ * Real.exp (-(2 / 5) * K) ≤ 1 := by
      have h3 : 1 + 2 / 5 * K ≤ Real.exp (2 / 5 * K) := by
        have := Real.add_one_le_exp (2 / 5 * K)
        linarith
      have h4 : Real.exp (2 / 5 * K) * Real.exp (-(2 / 5) * K) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      nlinarith [Real.exp_pos (-(2 / 5) * K)]
    calc lineKernel (2 * s) k * Real.exp (a * K) ≤ Real.exp (-(7 / 5) * K) := h1
      _ = Real.exp (-K) * Real.exp (-(2 / 5) * K) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-K / σ) * (1 / σ) := by
          refine mul_le_mul hexpK ?_ (Real.exp_pos _).le (Real.exp_pos _).le
          rw [le_div_iff₀ hσ0]
          linarith
      _ ≤ (1 + C₀) * Real.exp 220 / σ * Real.exp (-K / σ) := by
          rw [mul_comm, div_eq_mul_one_div ((1 + C₀) * Real.exp 220)]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have : (1 : ℝ) ≤ (1 + C₀) * Real.exp 220 := by
            have : (1 : ℝ) ≤ Real.exp 220 := Real.one_le_exp (by norm_num)
            nlinarith
          nlinarith [one_div_pos.2 hσ0]
  · rcases le_or_gt 1 s with hs1 | hs1
    · -- the Gaussian regime: the local limit theorem
      have hsq : Real.sqrt s = σ := by
        rw [hσ, max_eq_left]
        exact Real.one_le_sqrt.2 hs1
      have hsqpos : 0 < Real.sqrt s := by rw [hsq]; exact hσ0
      have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs
      have h2s : 0 < 2 * s := by linarith
      have hl := hlclt (2 * s) h2s k
      have hg : lineGauss (2 * s) k ≤ 1 / Real.sqrt s *
          Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + K))) := by
        rw [lineGauss]
        refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (by positivity)
        · rw [one_div]
          refine inv_anti₀ hsqpos (Real.sqrt_le_sqrt ?_)
          nlinarith [Real.pi_gt_three]
        · refine Real.exp_le_exp.2 ?_
          rw [neg_div, neg_div, neg_le_neg_iff]
          refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
          nlinarith
      have herr : C₀ * (2 * s) ^ (-(3 : ℝ) / 2) ≤ C₀ * (1 / Real.sqrt s) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₀.le
        rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hs]
        refine (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith : s ≤ 2 * s)
          (by norm_num)).trans ?_
        exact Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
      have hq : lineKernel (2 * s) k ≤ (1 + C₀) / Real.sqrt s *
          Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + K))) := by
        have := (le_abs_self _).trans hl
        have h5 : C₀ * (2 * s) ^ (-(3 : ℝ) / 2) * Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + K)))
            ≤ C₀ * (1 / Real.sqrt s) * Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + K))) :=
          mul_le_mul_of_nonneg_right herr (Real.exp_pos _).le
        rw [hK] at h5 hg
        rw [hK]
        calc lineKernel (2 * s) k ≤ lineGauss (2 * s) k + C₀ * (2 * s) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + |(k : ℝ)|))) := by linarith
          _ ≤ (1 + C₀) / Real.sqrt s *
              Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + |(k : ℝ)|))) := by
              have e : (1 + C₀) / Real.sqrt s *
                  Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + |(k : ℝ)|))) =
                  1 / Real.sqrt s * Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + |(k : ℝ)|))) +
                  C₀ * (1 / Real.sqrt s) *
                    Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + |(k : ℝ)|))) := by ring
              rw [e]
              linarith
      have hk2 : (k : ℝ) ^ 2 = K ^ 2 := by rw [hK, sq_abs]
      have hexp1 : Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + K))) * Real.exp (a * K) ≤
          Real.exp 220 * Real.exp (-K / σ) := by
        rw [← Real.exp_add, ← Real.exp_add, hk2]
        refine Real.exp_le_exp.2 ?_
        have hden : 10 * (2 * s + K) ≤ 220 * s := by linarith
        have hfrac : K ^ 2 / (220 * s) ≤ K ^ 2 / (10 * (2 * s + K)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
        have haK : a * K ≤ K / σ := by
          rw [le_div_iff₀ hσ0]
          nlinarith
        -- with `r = K/σ`: `2r - r²/220 ≤ 220`
        set r := K / σ with hr
        have hK2 : K ^ 2 / (220 * s) = r ^ 2 / 220 := by
          rw [hr, div_pow, ← hss, hsq]
          field_simp
        have key : 2 * r - r ^ 2 / 220 ≤ 220 := by nlinarith [sq_nonneg (r - 220)]
        rw [neg_div, neg_div]
        linarith
      calc lineKernel (2 * s) k * Real.exp (a * K)
          ≤ (1 + C₀) / Real.sqrt s * Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + K))) *
              Real.exp (a * K) := mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
        _ = (1 + C₀) / Real.sqrt s *
            (Real.exp (-(k : ℝ) ^ 2 / (10 * (2 * s + K))) * Real.exp (a * K)) := by ring
        _ ≤ (1 + C₀) / Real.sqrt s * (Real.exp 220 * Real.exp (-K / σ)) :=
            mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = (1 + C₀) * Real.exp 220 / σ * Real.exp (-K / σ) := by rw [hsq]; ring
    · -- small times
      have hσ' : σ = 1 := by
        rw [hσ, max_eq_right]
        exact Real.sqrt_le_one.2 hs1.le
      have hq1 : lineKernel (2 * s) k ≤ 1 :=
        (le_abs_self _).trans (abs_lineKernel_le_one (by linarith) k)
      have hK20 : K < 20 := by linarith
      rw [hσ', div_one, div_one]
      calc lineKernel (2 * s) k * Real.exp (a * K) ≤ 1 * Real.exp K :=
            mul_le_mul hq1 (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le zero_le_one
        _ = Real.exp 40 * Real.exp (-K) * Real.exp (K - 40 + K) := by
            rw [← Real.exp_add, ← Real.exp_add, one_mul]; ring_nf
        _ ≤ Real.exp 40 * Real.exp (-K) * 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by linarith)) (by positivity)
        _ ≤ (1 + C₀) * Real.exp 220 * Real.exp (-K) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_right hC1 (Real.exp_pos _).le

/-- **The tilted heat kernel of `ℤ²`**: `Φ_s(x, y) e^{a|y - x|₁} ≤ (C/σ²) e^{-|y - x|₁/σ}` for
`0 ≤ a ≤ 1/6`, `a max(√s, 1) ≤ 1`, `σ = max(√s, 1)`. -/
theorem exists_openHeat_mul_exp_le : ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → ∀ a : ℝ, 0 ≤ a →
    a ≤ 1 / 6 → a * max (Real.sqrt s) 1 ≤ 1 → ∀ x y : Vertex 2,
      openHeat (allOpen 2) s x y *
          Real.exp (a * (|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|)) ≤
        C / max (Real.sqrt s) 1 ^ 2 *
          Real.exp (-(|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|) /
            max (Real.sqrt s) 1) := by
  obtain ⟨C, hC, h⟩ := exists_lineKernel_mul_exp_le
  refine ⟨C ^ 2, by nlinarith, fun s hs a ha0 ha6 haσ x y => ?_⟩
  have h0 := h s hs a ha0 ha6 haσ ((y - x) 0)
  have h1 := h s hs a ha0 ha6 haσ ((y - x) 1)
  have hq0 := lineKernel_nonneg (by linarith : 0 ≤ 2 * s) ((y - x) 0)
  have hq1 := lineKernel_nonneg (by linarith : 0 ≤ 2 * s) ((y - x) 1)
  rw [openHeat_allOpen_eq_lineKernel]
  calc lineKernel (2 * s) ((y - x) 0) * lineKernel (2 * s) ((y - x) 1) *
        Real.exp (a * (|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|))
      = (lineKernel (2 * s) ((y - x) 0) * Real.exp (a * |(((y - x) 0 : ℤ) : ℝ)|)) *
          (lineKernel (2 * s) ((y - x) 1) * Real.exp (a * |(((y - x) 1 : ℤ) : ℝ)|)) := by
        rw [mul_add, Real.exp_add]; ring
    _ ≤ (C / max (Real.sqrt s) 1 * Real.exp (-|(((y - x) 0 : ℤ) : ℝ)| / max (Real.sqrt s) 1)) *
          (C / max (Real.sqrt s) 1 *
            Real.exp (-|(((y - x) 1 : ℤ) : ℝ)| / max (Real.sqrt s) 1)) :=
        mul_le_mul h0 h1 (mul_nonneg hq1 (Real.exp_pos _).le) (by positivity)
    _ = C ^ 2 / max (Real.sqrt s) 1 ^ 2 *
          Real.exp (-(|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|) /
            max (Real.sqrt s) 1) := by
        rw [neg_add, add_div, Real.exp_add]; ring

end Rigidity.Poincare

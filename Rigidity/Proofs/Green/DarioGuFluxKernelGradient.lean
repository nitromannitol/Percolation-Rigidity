import Rigidity.Proofs.Poincare.LatticeHeatKernel
import Rigidity.Proofs.Corrector.DarioPoincareMoments
import Rigidity.Proofs.Corrector.PlanarHeatSmoothing

/-!
# The `ℓ¹` norm of the gradient of the heat kernel of `ℤ²`

For the duality between the heat averages of the flux and the test functions of the `H̲^{-1}`
norm (Dario–Gu, Appendix B, the estimate (B.4)), the gradient of the heat kernel
`Φ_t(0, ·)` of `ℤ²` is summed over the lattice:

* `tsum_ofReal_abs_lineGauss_sub_le`: the increments of the Gaussian `g_s(k)` sum to `2 g_s(0)`
  at most, since `g_s` is even and decreasing in `|k|`;
* `exists_tsum_ofReal_abs_lineKernel_sub_le`: `Σ_k |q_s(k + 1) - q_s(k)| ≤ C/√s` for `s ≥ 1`,
  from the local limit theorem of Lattice-Probability
  (`exists_abs_lineKernel_sub_lineGauss_le`, error `C s^{-3/2} e^{-k²/(10(s + |k|))}`);
* `exists_tsum_ofReal_abs_openHeat_grad_le`: `Σ_v |Φ_t(0, v + e_j) - Φ_t(0, v)| ≤ C/√t` for
  `t > 0`, by the product form `Φ_t(0, v) = q_{2t}(v₀) q_{2t}(v₁)`;
* `heatGradKernel j a b v = ∫_a^b |Φ_t(0, v + e_j) - Φ_t(0, v)| dt` and its total mass
  `(b - a) C/√a` (`tsum_heatGradKernel_le`), or `2(b - a)` (`tsum_heatGradKernel_le_two`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation LatticeProb.ContinuousTime Rigidity.Poincare
open scoped ENNReal

namespace Rigidity.Green

/-! ### The Gaussian -/

theorem lineGauss_neg (s : ℝ) (k : ℤ) : lineGauss s (-k) = lineGauss s k := by
  simp [lineGauss]

theorem lineGauss_succ_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    lineGauss s ((n : ℤ) + 1) ≤ lineGauss s n := by
  unfold lineGauss
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  rw [div_le_div_iff_of_pos_right (by positivity)]
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith

theorem lineGauss_nonneg (s : ℝ) (k : ℤ) : 0 ≤ lineGauss s k := by
  unfold lineGauss
  positivity

/-- **The increments of the Gaussian**: `Σ_k |g_s(k + 1) - g_s(k)| ≤ 2 g_s(0)`. -/
theorem tsum_ofReal_abs_lineGauss_sub_le {s : ℝ} (hs : 0 < s) :
    ∑' k : ℤ, ENNReal.ofReal |lineGauss s (k + 1) - lineGauss s k| ≤
      ENNReal.ofReal (2 * lineGauss s 0) := by
  set f : ℕ → ℝ := fun n => lineGauss s n with hf
  have hstep : ∀ n : ℕ, f (n + 1) ≤ f n := by
    intro n
    simp only [hf]
    push_cast
    exact lineGauss_succ_le hs n
  have hnat : ∑' n : ℕ, ENNReal.ofReal (f n - f (n + 1)) ≤ ENNReal.ofReal (lineGauss s 0) := by
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => sub_nonneg.2 (hstep n)),
      Finset.sum_range_sub']
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ f N := lineGauss_nonneg s _
    simp only [hf, Nat.cast_zero] at this ⊢
    linarith
  have e1 : ∀ n : ℕ, ENNReal.ofReal |lineGauss s ((n : ℤ) + 1) - lineGauss s n| =
      ENNReal.ofReal (f n - f (n + 1)) := by
    intro n
    have h := hstep n
    simp only [hf] at h ⊢
    push_cast at h ⊢
    rw [abs_of_nonpos (by linarith)]
    ring_nf
  have e2 : ∀ n : ℕ, ENNReal.ofReal |lineGauss s (-((n : ℤ) + 1) + 1) - lineGauss s (-((n : ℤ) + 1))| =
      ENNReal.ofReal (f n - f (n + 1)) := by
    intro n
    have h := hstep n
    have ea : -((n : ℤ) + 1) + 1 = -(n : ℤ) := by ring
    rw [ea, lineGauss_neg, lineGauss_neg]
    simp only [hf] at h ⊢
    push_cast at h ⊢
    rw [abs_of_nonneg (by linarith)]
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  simp only [e1, e2]
  calc ∑' n : ℕ, ENNReal.ofReal (f n - f (n + 1)) + ∑' n : ℕ, ENNReal.ofReal (f n - f (n + 1))
      ≤ ENNReal.ofReal (lineGauss s 0) + ENNReal.ofReal (lineGauss s 0) := add_le_add hnat hnat
    _ = ENNReal.ofReal (2 * lineGauss s 0) := by
        rw [← ENNReal.ofReal_add (lineGauss_nonneg s 0) (lineGauss_nonneg s 0), two_mul]

/-! ### The error of the local limit theorem -/

theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h1 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1 / 2)]

/-- `e^{-k²/(10(s + |k|))} ≤ 2 e^{-|k|/(20√s)}` for `s ≥ 1`. -/
theorem exp_neg_sq_div_le {s : ℝ} (hs : 1 ≤ s) (k : ℤ) :
    Real.exp (-(k : ℝ) ^ 2 / (10 * (s + |(k : ℝ)|))) ≤
      2 * Real.exp (-(1 / (20 * Real.sqrt s) * |(k : ℝ)|)) := by
  set K := |(k : ℝ)| with hK
  set σ := Real.sqrt s with hσ
  have hK0 : 0 ≤ K := abs_nonneg _
  have hσ1 : 1 ≤ σ := by rw [hσ]; exact Real.one_le_sqrt.2 hs
  have hσ0 : 0 < σ := by linarith
  have hsσ : s = σ ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hk2 : (k : ℝ) ^ 2 = K ^ 2 := (sq_abs _).symm
  have hden : 0 < 10 * (s + K) := by positivity
  have e : K / (20 * σ) * (10 * (s + K)) = K * σ / 2 + K ^ 2 / (2 * σ) := by
    rw [hsσ]
    field_simp
    ring
  have h2 : K ^ 2 / (2 * σ) ≤ K ^ 2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg K) (by norm_num) (by linarith)
  have key : (K / (20 * σ) - 1 / 2) * (10 * (s + K)) ≤ K ^ 2 := by
    rw [sub_mul, e, hsσ]
    nlinarith [sq_nonneg (K - σ / 2)]
  have hle : -(k : ℝ) ^ 2 / (10 * (s + K)) ≤ 1 / 2 + -(1 / (20 * σ) * K) := by
    have h3 : K / (20 * σ) - 1 / 2 ≤ K ^ 2 / (10 * (s + K)) := by
      rw [le_div_iff₀ hden]
      exact key
    rw [hk2, neg_div]
    have : 1 / (20 * σ) * K = K / (20 * σ) := by ring
    rw [this]
    linarith
  calc Real.exp (-(k : ℝ) ^ 2 / (10 * (s + K)))
      ≤ Real.exp (1 / 2 + -(1 / (20 * σ) * K)) := Real.exp_le_exp.2 hle
    _ = Real.exp (1 / 2) * Real.exp (-(1 / (20 * σ) * K)) := Real.exp_add _ _
    _ ≤ 2 * Real.exp (-(1 / (20 * σ) * K)) :=
        mul_le_mul_of_nonneg_right exp_half_lt_two.le (Real.exp_pos _).le

theorem tsum_ofReal_exp_neg_sq_div_le {s : ℝ} (hs : 1 ≤ s) :
    ∑' k : ℤ, ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / (10 * (s + |(k : ℝ)|)))) ≤
      ENNReal.ofReal (4 * (1 + 20 * Real.sqrt s)) := by
  have hσ0 : 0 < Real.sqrt s := Real.sqrt_pos.2 (by linarith)
  have hc : 0 < 1 / (20 * Real.sqrt s) := by positivity
  calc ∑' k : ℤ, ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / (10 * (s + |(k : ℝ)|))))
      ≤ ∑' k : ℤ, ENNReal.ofReal 2 *
          ENNReal.ofReal (Real.exp (-(1 / (20 * Real.sqrt s) * |(k : ℝ)|))) :=
        ENNReal.tsum_le_tsum fun k => by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (exp_neg_sq_div_le hs k)
    _ = ENNReal.ofReal 2 *
          ∑' k : ℤ, ENNReal.ofReal (Real.exp (-(1 / (20 * Real.sqrt s) * |(k : ℝ)|))) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (2 * (1 + 1 / (1 / (20 * Real.sqrt s)))) :=
        mul_le_mul_right (Rigidity.Corrector.tsum_int_exp_neg_le hc) _
    _ = ENNReal.ofReal (4 * (1 + 20 * Real.sqrt s)) := by
        rw [← ENNReal.ofReal_mul (by norm_num), one_div_one_div]
        ring_nf

/-! ### The increments of the one-dimensional kernel -/

theorem rpow_neg_three_halves_eq_inv_sqrt_pow {s : ℝ} (hs : 0 < s) :
    s ^ (-(3 : ℝ) / 2) = (Real.sqrt s ^ 3)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_neg hs.le]
  norm_num

/-- **The `ℓ¹` norm of the increments of the one-dimensional kernel**: `≤ C/√s` for `s ≥ 1`. -/
theorem exists_tsum_ofReal_abs_lineKernel_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 ≤ s →
      ∑' k : ℤ, ENNReal.ofReal |lineKernel s (k + 1) - lineKernel s k| ≤
        ENNReal.ofReal (C / Real.sqrt s) := by
  obtain ⟨C₀, hC₀, hL⟩ := exists_abs_lineKernel_sub_lineGauss_le
  refine ⟨1 + 168 * C₀, by positivity, fun s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  set σ := Real.sqrt s with hσ
  have hσ1 : 1 ≤ σ := by rw [hσ]; exact Real.one_le_sqrt.2 hs
  have hσ0 : 0 < σ := by linarith
  set E : ℤ → ℝ := fun k => C₀ * s ^ (-(3 : ℝ) / 2) *
    Real.exp (-(k : ℝ) ^ 2 / (10 * (s + |(k : ℝ)|))) with hE
  have hE0 : ∀ k, 0 ≤ E k := fun k => by simp only [hE]; positivity
  have hpt : ∀ k : ℤ, ENNReal.ofReal |lineKernel s (k + 1) - lineKernel s k| ≤
      ENNReal.ofReal |lineGauss s (k + 1) - lineGauss s k| + ENNReal.ofReal (E (k + 1)) +
        ENNReal.ofReal (E k) := by
    intro k
    have h1 := hL s hs0 (k + 1)
    have h2 := hL s hs0 k
    have htri : |lineKernel s (k + 1) - lineKernel s k| ≤
        |lineGauss s (k + 1) - lineGauss s k| + E (k + 1) + E k := by
      have := abs_sub_le (lineKernel s (k + 1)) (lineGauss s (k + 1)) (lineKernel s k)
      have h3 := abs_sub_le (lineGauss s (k + 1)) (lineGauss s k) (lineKernel s k)
      rw [abs_sub_comm (lineGauss s k)] at h3
      simp only [hE]
      push_cast at h1 h2 ⊢
      linarith
    rw [← ENNReal.ofReal_add (abs_nonneg _) (hE0 _), ← ENNReal.ofReal_add (by positivity) (hE0 _)]
    exact ENNReal.ofReal_le_ofReal htri
  have hEsum : ∑' k : ℤ, ENNReal.ofReal (E k) ≤
      ENNReal.ofReal (C₀ * s ^ (-(3 : ℝ) / 2) * (4 * (1 + 20 * σ))) := by
    calc ∑' k : ℤ, ENNReal.ofReal (E k)
        = ∑' k : ℤ, ENNReal.ofReal (C₀ * s ^ (-(3 : ℝ) / 2)) *
            ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / (10 * (s + |(k : ℝ)|)))) := by
          refine tsum_congr fun k => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (C₀ * s ^ (-(3 : ℝ) / 2)) *
            ∑' k : ℤ, ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / (10 * (s + |(k : ℝ)|)))) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (C₀ * s ^ (-(3 : ℝ) / 2)) * ENNReal.ofReal (4 * (1 + 20 * σ)) :=
          mul_le_mul_right (tsum_ofReal_exp_neg_sq_div_le hs) _
      _ = ENNReal.ofReal (C₀ * s ^ (-(3 : ℝ) / 2) * (4 * (1 + 20 * σ))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hshift : ∑' k : ℤ, ENNReal.ofReal (E (k + 1)) = ∑' k : ℤ, ENNReal.ofReal (E k) :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => ENNReal.ofReal (E k))
  have hg0 : lineGauss s 0 ≤ 1 / (2 * σ) := by
    unfold lineGauss
    have hπ : 2 ≤ Real.sqrt (2 * Real.pi) := by
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      calc (2 : ℝ) = Real.sqrt 4 := h4.symm
        _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    have e : Real.sqrt (2 * Real.pi * s) = Real.sqrt (2 * Real.pi) * σ :=
      Real.sqrt_mul (by positivity) s
    simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
      zero_div, Real.exp_zero, mul_one]
    rw [e, one_div]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hfin : 2 * lineGauss s 0 + 2 * (C₀ * s ^ (-(3 : ℝ) / 2) * (4 * (1 + 20 * σ))) ≤
      (1 + 168 * C₀) / σ := by
    rw [rpow_neg_three_halves_eq_inv_sqrt_pow hs0]
    have h1 : (σ ^ 3)⁻¹ * (1 + 20 * σ) ≤ 21 / σ := by
      have hσ2 : 1 ≤ σ ^ 2 := one_le_pow₀ hσ1
      have h3 : σ ≤ σ ^ 3 := by
        calc σ = σ * 1 := (mul_one σ).symm
          _ ≤ σ * σ ^ 2 := mul_le_mul_of_nonneg_left hσ2 hσ0.le
          _ = σ ^ 3 := by ring
      have h4 : σ ^ 2 ≤ σ ^ 3 := by
        calc σ ^ 2 = σ ^ 2 * 1 := (mul_one _).symm
          _ ≤ σ ^ 2 * σ := mul_le_mul_of_nonneg_left hσ1 (by positivity)
          _ = σ ^ 3 := by ring
      rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) hσ0]
      nlinarith
    have h2 : 2 * lineGauss s 0 ≤ 1 / σ := by
      calc 2 * lineGauss s 0 ≤ 2 * (1 / (2 * σ)) := by linarith
        _ = 1 / σ := by field_simp
    have h3 : 2 * (C₀ * (σ ^ 3)⁻¹ * (4 * (1 + 20 * σ))) ≤ 168 * C₀ / σ := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * C₀)
      calc 2 * (C₀ * (σ ^ 3)⁻¹ * (4 * (1 + 20 * σ))) = 8 * C₀ * ((σ ^ 3)⁻¹ * (1 + 20 * σ)) := by
            ring
        _ ≤ 8 * C₀ * (21 / σ) := this
        _ = 168 * C₀ / σ := by ring
    calc 2 * lineGauss s 0 + 2 * (C₀ * (σ ^ 3)⁻¹ * (4 * (1 + 20 * σ)))
        ≤ 1 / σ + 168 * C₀ / σ := add_le_add h2 h3
      _ = (1 + 168 * C₀) / σ := by ring
  calc ∑' k : ℤ, ENNReal.ofReal |lineKernel s (k + 1) - lineKernel s k|
      ≤ ∑' k : ℤ, (ENNReal.ofReal |lineGauss s (k + 1) - lineGauss s k| +
          ENNReal.ofReal (E (k + 1)) + ENNReal.ofReal (E k)) := ENNReal.tsum_le_tsum hpt
    _ = ∑' k : ℤ, ENNReal.ofReal |lineGauss s (k + 1) - lineGauss s k| +
          ∑' k : ℤ, ENNReal.ofReal (E (k + 1)) + ∑' k : ℤ, ENNReal.ofReal (E k) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal (2 * lineGauss s 0) +
          ENNReal.ofReal (C₀ * s ^ (-(3 : ℝ) / 2) * (4 * (1 + 20 * σ))) +
          ENNReal.ofReal (C₀ * s ^ (-(3 : ℝ) / 2) * (4 * (1 + 20 * σ))) := by
        rw [hshift]
        exact add_le_add (add_le_add (tsum_ofReal_abs_lineGauss_sub_le hs0) hEsum) hEsum
    _ = ENNReal.ofReal (2 * lineGauss s 0 +
          2 * (C₀ * s ^ (-(3 : ℝ) / 2) * (4 * (1 + 20 * σ)))) := by
        have hA : 0 ≤ 2 * lineGauss s 0 := by have := lineGauss_nonneg s 0; positivity
        have hB : 0 ≤ C₀ * s ^ (-(3 : ℝ) / 2) * (4 * (1 + 20 * σ)) := by positivity
        rw [← ENNReal.ofReal_add hA hB, ← ENNReal.ofReal_add (add_nonneg hA hB) hB]
        ring_nf
    _ ≤ ENNReal.ofReal ((1 + 168 * C₀) / σ) := ENNReal.ofReal_le_ofReal hfin

/-! ### The heat kernel of `ℤ²` -/

theorem le_one_of_mul_self_eq_one {a : ℝ≥0∞} (h : a * a = 1) : a ≤ 1 := by
  by_contra hlt'
  have hlt : 1 < a := not_le.1 hlt'
  have : 1 < a * a := lt_of_lt_of_le hlt (le_mul_of_one_le_right' hlt.le)
  rw [h] at this
  exact lt_irrefl _ this

theorem openHeat_zero_left_eq (t : ℝ) (v : Vertex 2) :
    openHeat (allOpen 2) t 0 v = lineKernel (2 * t) (v 0) * lineKernel (2 * t) (v 1) := by
  rw [openHeat_allOpen_eq_lineKernel, sub_zero]

theorem tsum_ofReal_prod_eq (F H : ℤ → ℝ≥0∞) :
    ∑' v : Vertex 2, F (v 0) * H (v 1) = (∑' n : ℤ, F n) * ∑' n : ℤ, H n := by
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  exact (finTwoArrowEquiv ℤ).tsum_eq (fun ab => F ab.1 * H ab.2)

/-- The one-dimensional kernel has mass at most one. -/
theorem tsum_ofReal_lineKernel_le_one {s : ℝ} (hs : 0 ≤ s) :
    ∑' n : ℤ, ENNReal.ofReal (lineKernel s n) ≤ 1 := by
  have h := Rigidity.Corrector.tsum_ofReal_latticeHeat (by linarith : 0 ≤ s / 2) (0 : Vertex 2)
  have e : ∀ v : Vertex 2, ENNReal.ofReal (Rigidity.Corrector.latticeHeat (s / 2) 0 v) =
      ENNReal.ofReal (lineKernel s (v 0)) * ENNReal.ofReal (lineKernel s (v 1)) := by
    intro v
    change ENNReal.ofReal (openHeat (allOpen 2) (s / 2) 0 v) = _
    rw [openHeat_zero_left_eq, show 2 * (s / 2) = s by ring,
      ENNReal.ofReal_mul (lineKernel_nonneg hs _)]
  simp only [e] at h
  have h' := tsum_ofReal_prod_eq (fun n => ENNReal.ofReal (lineKernel s n))
    (fun n => ENNReal.ofReal (lineKernel s n))
  rw [h'] at h
  exact le_one_of_mul_self_eq_one h

theorem unit_zero_apply_zero : (unit (0 : Fin 2) : Vertex 2) 0 = 1 := by
  simp [unit]

theorem unit_zero_apply_one : (unit (0 : Fin 2) : Vertex 2) 1 = 0 := by
  simp [unit]

theorem unit_one_apply_zero : (unit (1 : Fin 2) : Vertex 2) 0 = 0 := by
  simp [unit]

theorem unit_one_apply_one : (unit (1 : Fin 2) : Vertex 2) 1 = 1 := by
  simp [unit]

/-- **The `ℓ¹` norm of the gradient of the heat kernel of `ℤ²`**: `≤ C/√t` for `t > 0`. -/
theorem exists_tsum_ofReal_abs_openHeat_grad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ j : Fin 2,
      ∑' v : Vertex 2, ENNReal.ofReal
          |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v| ≤
        ENNReal.ofReal (C / Real.sqrt t) := by
  obtain ⟨C₁, hC₁, h1⟩ := exists_tsum_ofReal_abs_lineKernel_sub_le
  refine ⟨max C₁ 2, by positivity, fun t ht j => ?_⟩
  have hst : Real.sqrt t ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt (by linarith)
  have hsq0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  set q : ℤ → ℝ := fun k => lineKernel (2 * t) k with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => lineKernel_nonneg (by linarith) k
  -- the gradient as a product
  have hprod : ∑' v : Vertex 2, ENNReal.ofReal
      |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v| ≤
      ∑' n : ℤ, ENNReal.ofReal |q (n + 1) - q n| := by
    have hm := tsum_ofReal_lineKernel_le_one (by linarith : 0 ≤ 2 * t)
    fin_cases j
    · have e : ∀ v : Vertex 2, ENNReal.ofReal
          |openHeat (allOpen 2) t 0 (v + unit 0) - openHeat (allOpen 2) t 0 v| =
          ENNReal.ofReal |q (v 0 + 1) - q (v 0)| * ENNReal.ofReal (q (v 1)) := by
        intro v
        rw [openHeat_zero_left_eq, openHeat_zero_left_eq, Pi.add_apply, Pi.add_apply,
          unit_zero_apply_zero, unit_zero_apply_one, add_zero, ← sub_mul, abs_mul,
          abs_of_nonneg (hq0 _), ENNReal.ofReal_mul (abs_nonneg _)]
      simp only [Fin.zero_eta, e]
      rw [tsum_ofReal_prod_eq (fun n => ENNReal.ofReal |q (n + 1) - q n|)
        (fun n => ENNReal.ofReal (q n))]
      calc (∑' n : ℤ, ENNReal.ofReal |q (n + 1) - q n|) * ∑' n : ℤ, ENNReal.ofReal (q n)
          ≤ (∑' n : ℤ, ENNReal.ofReal |q (n + 1) - q n|) * 1 := mul_le_mul_right hm _
        _ = _ := mul_one _
    · have e : ∀ v : Vertex 2, ENNReal.ofReal
          |openHeat (allOpen 2) t 0 (v + unit 1) - openHeat (allOpen 2) t 0 v| =
          ENNReal.ofReal (q (v 0)) * ENNReal.ofReal |q (v 1 + 1) - q (v 1)| := by
        intro v
        rw [openHeat_zero_left_eq, openHeat_zero_left_eq, Pi.add_apply, Pi.add_apply,
          unit_one_apply_zero, unit_one_apply_one, add_zero, ← mul_sub, abs_mul,
          abs_of_nonneg (hq0 _), ENNReal.ofReal_mul (hq0 _)]
      simp only [Fin.mk_one, e]
      rw [tsum_ofReal_prod_eq (fun n => ENNReal.ofReal (q n))
        (fun n => ENNReal.ofReal |q (n + 1) - q n|)]
      calc (∑' n : ℤ, ENNReal.ofReal (q n)) * ∑' n : ℤ, ENNReal.ofReal |q (n + 1) - q n|
          ≤ 1 * ∑' n : ℤ, ENNReal.ofReal |q (n + 1) - q n| := mul_le_mul_left hm _
        _ = _ := one_mul _
  refine hprod.trans ?_
  rcases le_or_gt 1 (2 * t) with h2t | h2t
  · refine (h1 (2 * t) h2t).trans (ENNReal.ofReal_le_ofReal ?_)
    calc C₁ / Real.sqrt (2 * t) ≤ C₁ / Real.sqrt t :=
          div_le_div_of_nonneg_left hC₁.le hsq0 hst
      _ ≤ max C₁ 2 / Real.sqrt t :=
          div_le_div_of_nonneg_right (le_max_left _ _) hsq0.le
  · -- small times: the trivial bound `2`
    have hm := tsum_ofReal_lineKernel_le_one (by linarith : 0 ≤ 2 * t)
    have hsh : ∑' n : ℤ, ENNReal.ofReal (q (n + 1)) = ∑' n : ℤ, ENNReal.ofReal (q n) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => ENNReal.ofReal (q n))
    calc ∑' n : ℤ, ENNReal.ofReal |q (n + 1) - q n|
        ≤ ∑' n : ℤ, (ENNReal.ofReal (q (n + 1)) + ENNReal.ofReal (q n)) :=
          ENNReal.tsum_le_tsum fun n => by
            rw [← ENNReal.ofReal_add (hq0 _) (hq0 _)]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [abs_le]
            constructor <;> linarith [hq0 n, hq0 (n + 1)]
      _ = ∑' n : ℤ, ENNReal.ofReal (q (n + 1)) + ∑' n : ℤ, ENNReal.ofReal (q n) :=
          ENNReal.tsum_add
      _ ≤ 1 + 1 := by rw [hsh]; exact add_le_add hm hm
      _ = ENNReal.ofReal 2 := by norm_num
      _ ≤ ENNReal.ofReal (max C₁ 2 / Real.sqrt t) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 (by linarith)
          rw [le_div_iff₀ hsq0]
          nlinarith [le_max_right C₁ 2]

/-! ### The time-integrated kernel -/

/-- `∫_a^b |Φ_t(0, v + e_j) - Φ_t(0, v)| dt`. -/
noncomputable def heatGradKernel (j : Fin 2) (a b : ℝ) (v : Vertex 2) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc a b,
    ENNReal.ofReal |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v|

theorem measurable_ofReal_abs_openHeat_grad (j : Fin 2) (v : Vertex 2) :
    Measurable fun t => ENNReal.ofReal
      |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v| :=
  ENNReal.measurable_ofReal.comp
    (((continuous_openHeat _ 0 _).sub (continuous_openHeat _ 0 _)).abs.measurable)

theorem tsum_heatGradKernel_eq (j : Fin 2) (a b : ℝ) :
    ∑' v, heatGradKernel j a b v = ∫⁻ t in Set.Ioc a b, ∑' v : Vertex 2,
      ENNReal.ofReal |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v| :=
  (lintegral_tsum fun v => (measurable_ofReal_abs_openHeat_grad j v).aemeasurable).symm

/-- **The mass of the time-integrated kernel**, `(b - a) C/√a`. -/
theorem tsum_heatGradKernel_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∀ j : Fin 2, ∑' v : Vertex 2, ENNReal.ofReal
      |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v| ≤
        ENNReal.ofReal (C / Real.sqrt t))
    {a b : ℝ} (ha : 0 < a) (j : Fin 2) :
    ∑' v, heatGradKernel j a b v ≤ ENNReal.ofReal ((b - a) * (C / Real.sqrt a)) := by
  rw [tsum_heatGradKernel_eq]
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  calc ∫⁻ t in Set.Ioc a b, ∑' v : Vertex 2, ENNReal.ofReal
        |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v|
      ≤ ∫⁻ _ in Set.Ioc a b, ENNReal.ofReal (C / Real.sqrt a) := by
        refine setLIntegral_mono measurable_const fun t ht => ?_
        have ht0 : 0 < t := ha.trans ht.1
        refine (hC t ht0 j).trans (ENNReal.ofReal_le_ofReal ?_)
        exact div_le_div_of_nonneg_left hC0 hsa (Real.sqrt_le_sqrt ht.1.le)
    _ = ENNReal.ofReal (C / Real.sqrt a) * ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Ioc]
    _ = ENNReal.ofReal ((b - a) * (C / Real.sqrt a)) := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- **The mass of the time-integrated kernel**, `2(b - a)`. -/
theorem tsum_heatGradKernel_le_two {a b : ℝ} (ha : 0 ≤ a) (j : Fin 2) :
    ∑' v, heatGradKernel j a b v ≤ ENNReal.ofReal (2 * (b - a)) := by
  rw [tsum_heatGradKernel_eq]
  calc ∫⁻ t in Set.Ioc a b, ∑' v : Vertex 2, ENNReal.ofReal
        |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v|
      ≤ ∫⁻ _ in Set.Ioc a b, (2 : ℝ≥0∞) := by
        refine setLIntegral_mono measurable_const fun t ht => ?_
        have ht0 : 0 ≤ t := ha.trans ht.1.le
        have hsh : ∑' v : Vertex 2, ENNReal.ofReal (openHeat (allOpen 2) t 0 (v + unit j)) =
            ∑' v : Vertex 2, ENNReal.ofReal (openHeat (allOpen 2) t 0 v) :=
          (Equiv.addRight (unit j)).tsum_eq (fun v => ENNReal.ofReal (openHeat (allOpen 2) t 0 v))
        have hm : ∑' v : Vertex 2, ENNReal.ofReal (openHeat (allOpen 2) t 0 v) = 1 :=
          Rigidity.Corrector.tsum_ofReal_latticeHeat ht0 0
        calc ∑' v : Vertex 2, ENNReal.ofReal
              |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v|
            ≤ ∑' v : Vertex 2, (ENNReal.ofReal (openHeat (allOpen 2) t 0 (v + unit j)) +
                ENNReal.ofReal (openHeat (allOpen 2) t 0 v)) :=
              ENNReal.tsum_le_tsum fun v => by
                have h1 := openHeat_nonneg (allOpen 2) ht0 0 (v + unit j)
                have h2 := openHeat_nonneg (allOpen 2) ht0 0 v
                rw [← ENNReal.ofReal_add h1 h2]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [abs_le]
                constructor <;> linarith
          _ = 2 := by rw [ENNReal.tsum_add, hsh, hm]; norm_num
    _ = 2 * ENNReal.ofReal (b - a) := by rw [setLIntegral_const, Real.volume_Ioc]
    _ = ENNReal.ofReal (2 * (b - a)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

end Rigidity.Green

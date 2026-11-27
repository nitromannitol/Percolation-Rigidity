import Rigidity.Proofs.Corrector.GeneralStepOneLipschitz
import Rigidity.Proofs.Corrector.GeneralHeatSmoothing
import Rigidity.Proofs.Poincare.GeneralHeatKernelBounds

/-!
# Heat-kernel square sums on `ℤᵈ` from moments of the local sums

Summing the bounds of Step 1 (or Step 2) of Lemma 3.3 of Dario over the bonds gives sums
`Σ_y Φ_{r²}(x, y)² W(y)`, with `W(y)` built from local factors (Dario's (3.18)). Since
`Φ_{r²}(x, y) ≤ C r^{-d}` (`exists_zdHeat_le_div_rpow`, from the Gaussian bound
`exists_zdHeat_mul_exp_le`) and `Σ_y Φ_{r²}(x, y) = 1`, uniform moments `E[W(y)^q] ≤ (A q^k)^q`
give, by Jensen's inequality for the weights `Φ_{r²}(x, ·)` (`lintegral_heatSum_rpow_le`), the bound
`Σ_y Φ_{r²}(x, y)² W(y) ≤ O_s(C r^{-d})` with `s = 1/(2k)` (`isOsBond_heatSqSum_of_moments`); this
replaces (3.19)-(3.20) and `Σ_y ζ_r(y)² ≤ C r^{-d}`, as in the planar
`Rigidity.Corrector.isOsBond_heatSqSum_of_moments`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.S2 Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ} [NeZero d]

/-- **On-diagonal bound of the heat kernel of `ℤᵈ`**: `Φ_{r²}(x, y) ≤ C r^{-d}` for `r ≥ 1`. -/
theorem exists_zdHeat_le_div_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ∀ x y : Vertex d,
      zdHeat d (r ^ 2) x y ≤ C / r ^ (d : ℝ) := by
  obtain ⟨C, hC, h⟩ := exists_zdHeat_mul_exp_le (d := d)
  refine ⟨C ^ d, by positivity, fun r hr x y => ?_⟩
  have hr0 : 0 ≤ r := by linarith
  have hσ : max (Real.sqrt (r ^ 2)) 1 = r := by
    rw [Real.sqrt_sq hr0]
    exact max_eq_left hr
  have h1 := h (r ^ 2) (sq_nonneg r) 0 le_rfl (by norm_num) (by rw [zero_mul]; norm_num) x y
  rw [zero_mul, Real.exp_zero, mul_one, hσ] at h1
  rw [Real.rpow_natCast]
  refine h1.trans ?_
  have hexp : Real.exp (-(∑ i, |(((y - x) i : ℤ) : ℝ)|) / r) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.2 (Finset.sum_nonneg fun i _ => abs_nonneg _)) hr0
  calc C ^ d / r ^ d * Real.exp (-(∑ i, |(((y - x) i : ℤ) : ℝ)|) / r)
      ≤ C ^ d / r ^ d * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = C ^ d / r ^ d := mul_one _

/-- **`O_s` bound of a heat-kernel square sum from uniform moments**: if
`Y ≤ Σ_y Φ_{r²}(x, y)² W(y)` almost surely and `E[W(y)^q] ≤ (A q^k)^q` for all `y` and `q ≥ 1`, then
`Y < ∞` almost surely and `Y ≤ O_s(C' r^{-d})` for `r ≥ 1`, with `s, C'` depending only on
`d, A, k`. -/
theorem isOsBond_heatSqSum_of_moments {p : unitInterval} {A k : ℝ} (hA : 0 < A) (hk : 0 < k) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (r : ℝ), 1 ≤ r → ∀ (x : Vertex d)
      (W : Vertex d → Configuration d → ℝ≥0∞), (∀ y, Measurable (W y)) →
      (∀ y (q : ℝ), 1 ≤ q →
        ∫⁻ ω, W y ω ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) →
      ∀ Y : Configuration d → ℝ≥0∞, Measurable Y →
      (∀ᵐ ω ∂latticeBondLaw d p, Y ω ≤ ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) * W y ω) →
      (∀ᵐ ω ∂latticeBondLaw d p, Y ω < ∞) ∧
        IsOsBond d p (fun ω => (Y ω).toReal) s (C / r ^ (d : ℝ)) := by
  obtain ⟨CH, hCH, hheat⟩ := exists_zdHeat_le_div_rpow (d := d)
  have hs0 : 0 < 1 / (2 * k) := by positivity
  have hsk : 1 / (2 * k) * k < 1 := by field_simp; linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨C, hC, hmom⟩ := isOsBond_of_moment_le (d := d) (p := p)
    (mul_pos (mul_pos two_pos hd0) hA : 0 < 2 * d * A) hs0 hsk
  refine ⟨1 / (2 * k), CH * C, hs0, by positivity, fun r hr x W hWm hWmom Y hYm hY => ?_⟩
  have hr0 : 0 < r := by linarith
  have hrd : 0 < r ^ (d : ℝ) := Real.rpow_pos_of_pos hr0 _
  -- the Jensen sum with the weights `Φ`
  set T : Configuration d → ℝ≥0∞ := fun ω => ∑ j : Fin d, ∑' y,
    ENNReal.ofReal (zdHeat d (r ^ 2) x y) * (W (y + LatticeProb.unit j) ω + W y ω) with hT
  have hTm : Measurable T := Finset.measurable_sum _ fun j _ =>
    Measurable.tsum fun y => ((hWm _).add (hWm y)).const_mul _
  have hTmom : ∀ q : ℝ, 1 ≤ q → ∫⁻ ω, T ω ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((2 * d * A * q ^ k) ^ q) := fun q hq =>
    lintegral_heatSum_rpow_le (tsum_ofReal_zdHeat (sq_nonneg r) x) hWm hq hA.le
      (fun y => hWmom y q hq)
  -- `Σ_y Φ² W ≤ (C_H/r^d) T`
  have hcmp : ∀ ω, ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) * W y ω ≤
      ENNReal.ofReal (CH / r ^ (d : ℝ)) * T ω := by
    intro ω
    have h1 : ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) * W y ω ≤
        ∑' y, ENNReal.ofReal (CH / r ^ (d : ℝ)) *
          (ENNReal.ofReal (zdHeat d (r ^ 2) x y) * W y ω) :=
      ENNReal.tsum_le_tsum fun y => by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have h0 := zdHeat_nonneg (sq_nonneg r) x y
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hheat r hr x y) h0
    refine h1.trans ?_
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ?_
    have h2 : ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y) * W y ω ≤
        ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y) *
          (W (y + LatticeProb.unit 0) ω + W y ω) :=
      ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl le_add_self
    refine h2.trans ?_
    simp only [hT]
    exact Finset.single_le_sum (f := fun j : Fin d => ∑' y,
      ENNReal.ofReal (zdHeat d (r ^ 2) x y) * (W (y + LatticeProb.unit j) ω + W y ω))
      (fun _ _ => zero_le) (Finset.mem_univ 0)
  -- `T` is almost surely finite
  have hTfin : ∀ᵐ ω ∂latticeBondLaw d p, T ω < ∞ := by
    refine ae_lt_top hTm ?_
    have h1 := hTmom 1 le_rfl
    simp only [ENNReal.rpow_one] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hle : ∀ᵐ ω ∂latticeBondLaw d p, Y ω ≤ ENNReal.ofReal (CH / r ^ (d : ℝ)) * T ω := by
    filter_upwards [hY] with ω hω
    exact hω.trans (hcmp ω)
  have hfin : ∀ᵐ ω ∂latticeBondLaw d p, Y ω < ∞ := by
    filter_upwards [hle, hTfin] with ω h1 h2
    exact h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2)
  refine ⟨hfin, ?_⟩
  -- the rescaled variable `(r^d/C_H) Y ≤ T`
  set E : Configuration d → ℝ := fun ω => r ^ (d : ℝ) / CH * (Y ω).toReal with hE
  have hEm : Measurable E := hYm.ennreal_toReal.const_mul _
  have hE0 : ∀ ω, 0 ≤ E ω := fun ω => by positivity
  have hpt : ∀ᵐ ω ∂latticeBondLaw d p, ENNReal.ofReal (E ω) ≤ T ω := by
    filter_upwards [hle, hfin] with ω h1 h2
    rw [hE, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal h2.ne]
    calc ENNReal.ofReal (r ^ (d : ℝ) / CH) * Y ω
        ≤ ENNReal.ofReal (r ^ (d : ℝ) / CH) * (ENNReal.ofReal (CH / r ^ (d : ℝ)) * T ω) :=
          mul_le_mul' le_rfl h1
      _ = T ω := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          rw [show r ^ (d : ℝ) / CH * (CH / r ^ (d : ℝ)) = 1 by field_simp, ENNReal.ofReal_one,
            one_mul]
  have hEos := isOsBond_of_ae_ofReal_le (by positivity) hmom hEm hE0 hpt hTmom
  have h := IsOsBond.const_mul (d := d) (p := p) (c := CH / r ^ (d : ℝ)) (by positivity) hEos
  have e : (fun ω => CH / r ^ (d : ℝ) * E ω) = fun ω => (Y ω).toReal := by
    funext ω
    simp only [hE]
    field_simp
  rw [e, show CH / r ^ (d : ℝ) * C = CH * C / r ^ (d : ℝ) by ring] at h
  exact h

end Rigidity.Corrector.GeneralDim

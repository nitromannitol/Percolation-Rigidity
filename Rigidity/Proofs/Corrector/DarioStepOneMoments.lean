import Rigidity.Proofs.Corrector.DarioStepOneLipschitz
import Rigidity.Proofs.Corrector.DarioHeatSquareSum

/-!
# The sum over bonds of Step 1 of Lemma 3.3 of Dario from moments of the local sums

Summing `flipTermOne_sq_le` over the bonds gives `Σ_e T₁(e)² ≤ Σ_y Φ_{r²}(x, y)² W(y)`, with `W(y)`
the sum over the bonds `e` whose box of Lemma 3.5 contains `y` of the local factors of `e` (Dario's
(3.18)). Since `Φ_{r²}(x, y) ≤ C/r²` (`exists_latticeHeat_le_div_sq`) and `Σ_y Φ_{r²}(x, y) = 1`,
uniform moments `E[W(y)^q] ≤ (A q^k)^q` give, by Jensen's inequality for the weights `Φ_{r²}(x, ·)`
(`lintegral_heatSum_rpow_le`), the bound `Σ_e T₁(e)² ≤ O_s(C/r²)` with `s = 1/(2k)`
(`flipSumOne_isOsBond_of_moments`); this replaces (3.19)-(3.20) and `Σ_y ζ_r(y)² ≤ C r^{-d}`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.S2
open scoped Classical ENNReal

/-- **`O_s` bound of a heat-kernel square sum from uniform moments**: if
`Y ≤ Σ_y Φ_{r²}(x, y)² W(y)` almost surely and `E[W(y)^q] ≤ (A q^k)^q` for all `y` and `q ≥ 1`, then
`Y < ∞` almost surely and `Y ≤ O_s(C'/r²)` for `r ≥ 1`, with `s, C'` depending only on `A, k`. -/
theorem isOsBond_heatSqSum_of_moments {p : unitInterval} {A k : ℝ} (hA : 0 < A) (hk : 0 < k) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (r : ℝ), 1 ≤ r → ∀ (x : Vertex 2)
      (W : Vertex 2 → Configuration 2 → ℝ≥0∞), (∀ y, Measurable (W y)) →
      (∀ y (q : ℝ), 1 ≤ q →
        ∫⁻ ω, W y ω ^ q ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) →
      ∀ Y : Configuration 2 → ℝ≥0∞, Measurable Y →
      (∀ᵐ ω ∂latticeBondLaw 2 p, Y ω ≤ ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * W y ω) →
      (∀ᵐ ω ∂latticeBondLaw 2 p, Y ω < ∞) ∧ IsOsBond 2 p (fun ω => (Y ω).toReal) s (C / r ^ 2) := by
  obtain ⟨CH, hCH, hheat⟩ := exists_latticeHeat_le_div_sq
  have hs0 : 0 < 1 / (2 * k) := by positivity
  have hsk : 1 / (2 * k) * k < 1 := by field_simp; linarith
  obtain ⟨C, hC, hmom⟩ := isOsBond_of_moment_le (d := 2) (p := p) (by positivity : 0 < 4 * A)
    hs0 hsk
  refine ⟨1 / (2 * k), CH * C, hs0, by positivity, fun r hr x W hWm hWmom Y hYm hY => ?_⟩
  have hr0 : 0 < r := by linarith
  -- the Jensen sum with the weights `Φ`
  set T : Configuration 2 → ℝ≥0∞ := fun ω => ∑ j : Fin 2, ∑' y,
    ENNReal.ofReal (latticeHeat (r ^ 2) x y) * (W (y + LatticeProb.unit j) ω + W y ω) with hT
  have hTm : Measurable T := Finset.measurable_sum _ fun j _ =>
    Measurable.tsum fun y => ((hWm _).add (hWm y)).const_mul _
  have hTmom : ∀ q : ℝ, 1 ≤ q → ∫⁻ ω, T ω ^ q ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal ((4 * A * q ^ k) ^ q) := fun q hq =>
    lintegral_heatSum_rpow_le (tsum_ofReal_latticeHeat (sq_nonneg r) x) hWm hq hA.le
      (fun y => hWmom y q hq)
  -- `Σ_y Φ² W ≤ (C_H/r²) T`
  have hcmp : ∀ ω, ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * W y ω ≤
      ENNReal.ofReal (CH / r ^ 2) * T ω := by
    intro ω
    have h1 : ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * W y ω ≤
        ∑' y, ENNReal.ofReal (CH / r ^ 2) * (ENNReal.ofReal (latticeHeat (r ^ 2) x y) * W y ω) :=
      ENNReal.tsum_le_tsum fun y => by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have h0 := latticeHeat_nonneg (sq_nonneg r) x y
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hheat r hr x y) h0
    refine h1.trans ?_
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ?_
    have h2 : ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y) * W y ω ≤
        ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y) *
          (W (y + LatticeProb.unit 0) ω + W y ω) :=
      ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl le_add_self
    refine h2.trans ?_
    simp only [hT]
    exact Finset.single_le_sum (f := fun j : Fin 2 => ∑' y,
      ENNReal.ofReal (latticeHeat (r ^ 2) x y) * (W (y + LatticeProb.unit j) ω + W y ω))
      (fun _ _ => zero_le) (Finset.mem_univ 0)
  -- `T` is almost surely finite
  have hTfin : ∀ᵐ ω ∂latticeBondLaw 2 p, T ω < ∞ := by
    refine ae_lt_top hTm ?_
    have h1 := hTmom 1 le_rfl
    simp only [ENNReal.rpow_one] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hle : ∀ᵐ ω ∂latticeBondLaw 2 p, Y ω ≤ ENNReal.ofReal (CH / r ^ 2) * T ω := by
    filter_upwards [hY] with ω hω
    exact hω.trans (hcmp ω)
  have hfin : ∀ᵐ ω ∂latticeBondLaw 2 p, Y ω < ∞ := by
    filter_upwards [hle, hTfin] with ω h1 h2
    exact h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2)
  refine ⟨hfin, ?_⟩
  -- the rescaled variable `(r²/C_H) Y ≤ T`
  set E : Configuration 2 → ℝ := fun ω => r ^ 2 / CH * (Y ω).toReal with hE
  have hEm : Measurable E := hYm.ennreal_toReal.const_mul _
  have hE0 : ∀ ω, 0 ≤ E ω := fun ω => by positivity
  have hpt : ∀ᵐ ω ∂latticeBondLaw 2 p, ENNReal.ofReal (E ω) ≤ T ω := by
    filter_upwards [hle, hfin] with ω h1 h2
    have hCH0 : 0 < CH := by linarith
    rw [hE, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal h2.ne]
    calc ENNReal.ofReal (r ^ 2 / CH) * Y ω
        ≤ ENNReal.ofReal (r ^ 2 / CH) * (ENNReal.ofReal (CH / r ^ 2) * T ω) :=
          mul_le_mul' le_rfl h1
      _ = T ω := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          rw [show r ^ 2 / CH * (CH / r ^ 2) = 1 by field_simp, ENNReal.ofReal_one, one_mul]
  have hEos := isOsBond_of_ae_ofReal_le (by positivity) hmom hEm hE0 hpt hTmom
  have h := IsOsBond.const_mul (d := 2) (p := p) (c := CH / r ^ 2) (by positivity) hEos
  have e : (fun ω => CH / r ^ 2 * E ω) = fun ω => (Y ω).toReal := by
    funext ω
    simp only [hE]
    field_simp
  rw [e, show CH / r ^ 2 * C = CH * C / r ^ 2 by ring] at h
  exact h

end Rigidity.Corrector

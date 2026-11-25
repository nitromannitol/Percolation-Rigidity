import Rigidity.Proofs.Poincare.MultiscalePoincareHolds
import Rigidity.Proofs.Poincare.GeneralDualityTerms

/-!
# Dario's multiscale Poincaré inequality (2.26) on `ℤ^d`

**Dario, Proposition 2.19, (2.26)**, on `ℤ^d`, `d ≥ 1`, in the cube form of
`MultiscalePoincare`: for `u : ℤ^d → ℝ` whose gradient is summable against the heat kernel,
`R = 3^m`, `q ≥ 2`,

  `3^{-dm} Σ_{□_m} |u - (u)_{□_m}|^q ≤ (A₀ q^{3/2})^q Σ_x R^{-d} e^{-|x|/(2R)}
    (∫_0^{2R} r |Φ_{r²} * ∇u(x)|² dr)^{q/2}`

(`multiscalePoincare_holds`). The proof is the one of `MultiscalePoincareHolds.lean` in dimension
`d`: the duality identity (`GeneralHeatDuality.lean`) for the test function `g` of
`GeneralDualTestFunction.lean`, written through the field `boxField` of divergence `g` along the
coordinate paths (`GeneralBoxField.lean`); the bilinear term is bounded by the weighted
Littlewood-Paley bound (`GeneralDualityTerms.lean`) and the low-frequency term by the heat kernel at
the diffusive scale (`GeneralDualityLowFreq.lean`).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ} {u : Vertex d → ℝ}

/-- **The low-frequency term** with the weights of (2.26). -/
theorem ofReal_abs_termII_le [NeZero d] {Kl : ℝ} (hKl : 0 < Kl)
    (hLow : ∀ u : Vertex d → ℝ, HeatSummable u → ∀ (j : Fin d) (R : ℝ), 3 ≤ R → ∀ q : ℝ,
      2 ≤ q → ∀ y : Vertex d, ∑ i, |((y i : ℤ) : ℝ)| ≤ d * R →
        ENNReal.ofReal (heatGrad u j (8 * R ^ 2) y ^ 2) ≤ ENNReal.ofReal (Kl / R ^ 2) *
          (∑' w, dwt R w * sqInt u (2 * R) w ^ (q / 2)) ^ (2 / q))
    (hu : HeatSummable u) {ρ : ℕ} (hρ : 1 ≤ ρ) {q : ℝ} (hq : 2 ≤ q) {g : Vertex d → ℝ} :
    ENNReal.ofReal |∑ j : Fin d, ∑' y, boxField ρ g j y *
        heatGrad u j (8 * (2 * ρ + 1 : ℝ) ^ 2) y| ≤
      ENNReal.ofReal (d * Real.sqrt Kl * ∑ y ∈ supBox 0 ρ, |g y|) *
        (∑' x, dwt (2 * ρ + 1) x * sqInt u (2 * (2 * ρ + 1)) x ^ (q / 2)) ^ (1 / q) := by
  set R : ℝ := 2 * ρ + 1 with hRdef
  have hR3 : 3 ≤ R := by
    have : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
    linarith
  have hR0 : 0 < R := by linarith
  have hq0 : 0 < q := by linarith
  set B := supBox 0 ρ with hB
  set RHS := ∑' x, dwt R x * sqInt u (2 * R) x ^ (q / 2) with hRHS
  set A := fun j y => heatGrad u j (8 * R ^ 2) y with hA
  have hAy : ∀ j, ∀ y ∈ B, ENNReal.ofReal |A j y| ≤
      ENNReal.ofReal (Real.sqrt Kl / R) * RHS ^ (1 / q) := by
    intro j y hy
    have h := hLow u hu j R hR3 q hq y (abs_coord_le_of_mem hy)
    have e1 : ENNReal.ofReal |A j y| = ENNReal.ofReal (A j y ^ 2) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq_eq_abs]
    rw [e1]
    refine (ENNReal.rpow_le_rpow h (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hR0.le]
    congr 2
    field_simp
  have hG : ∀ j, ∀ y ∉ B, boxField ρ g j y = 0 := fun j y hy => boxField_eq_zero j hy
  have hfin : ∀ j, ∑' y, boxField ρ g j y * A j y = ∑ y ∈ B, boxField ρ g j y * A j y :=
    fun j => tsum_eq_sum fun y hy => by rw [hG j y hy, zero_mul]
  have hGsum : ∑ j : Fin d, ∑ y ∈ B, |boxField ρ g j y| ≤ d * R * ∑ y ∈ B, |g y| := by
    have hg0 : 0 ≤ ∑ y ∈ B, |g y| := Finset.sum_nonneg fun y _ => abs_nonneg _
    calc ∑ j : Fin d, ∑ y ∈ B, |boxField ρ g j y| ≤ ∑ _j : Fin d, (ρ : ℝ) * ∑ y ∈ B, |g y| :=
          Finset.sum_le_sum fun j _ => sum_abs_boxField_le j
      _ = d * (ρ * ∑ y ∈ B, |g y|) := by simp
      _ ≤ d * R * ∑ y ∈ B, |g y| := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ hg0
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
          linarith
  calc ENNReal.ofReal |∑ j : Fin d, ∑' y, boxField ρ g j y * A j y|
      ≤ ENNReal.ofReal (∑ j : Fin d, ∑ y ∈ B, |boxField ρ g j y| * |A j y|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [hfin]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun y _ => abs_mul _ _
    _ = ∑ j : Fin d, ∑ y ∈ B, ENNReal.ofReal |boxField ρ g j y| * ENNReal.ofReal |A j y| := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun y _ => by positivity]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun y _ => by positivity]
        exact Finset.sum_congr rfl fun y _ => ENNReal.ofReal_mul (abs_nonneg _)
    _ ≤ ∑ j : Fin d, ∑ y ∈ B, ENNReal.ofReal |boxField ρ g j y| *
          (ENNReal.ofReal (Real.sqrt Kl / R) * RHS ^ (1 / q)) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun y hy =>
          mul_le_mul_of_nonneg_left (hAy j y hy) (by positivity)
    _ = ENNReal.ofReal (Real.sqrt Kl / R * ∑ j : Fin d, ∑ y ∈ B, |boxField ρ g j y|) *
          RHS ^ (1 / q) := by
        simp only [← Finset.sum_mul]
        have e : ∑ j : Fin d, ∑ y ∈ B, ENNReal.ofReal |boxField ρ g j y| =
            ENNReal.ofReal (∑ j : Fin d, ∑ y ∈ B, |boxField ρ g j y|) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun y _ => abs_nonneg _]
          exact Finset.sum_congr rfl fun j _ =>
            (ENNReal.ofReal_sum_of_nonneg fun y _ => abs_nonneg _).symm
        rw [e, ENNReal.ofReal_mul (p := Real.sqrt Kl / R) (div_nonneg (Real.sqrt_nonneg _) hR0.le)]
        ring
    _ ≤ ENNReal.ofReal (d * Real.sqrt Kl * ∑ y ∈ B, |g y|) * RHS ^ (1 / q) := by
        have hineq : Real.sqrt Kl / R * ∑ j : Fin d, ∑ y ∈ B, |boxField ρ g j y| ≤
            d * Real.sqrt Kl * ∑ y ∈ B, |g y| := by
          calc Real.sqrt Kl / R * ∑ j : Fin d, ∑ y ∈ B, |boxField ρ g j y|
              ≤ Real.sqrt Kl / R * (d * R * ∑ y ∈ B, |g y|) :=
                mul_le_mul_of_nonneg_left hGsum (div_nonneg (Real.sqrt_nonneg _) hR0.le)
            _ = d * Real.sqrt Kl * ∑ y ∈ B, |g y| := by field_simp
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hineq) (by simp)

/-- Hölder on the box: `Σ_B |g| ≤ |B|^{1/q} (Σ_B |g|^p)^{1/p}`. -/
theorem sum_abs_le_card_rpow_mul {B : Finset (Vertex d)} (g : Vertex d → ℝ) {q : ℝ}
    (hq : 1 < q) :
    ∑ y ∈ B, |g y| ≤ (B.card : ℝ) ^ (1 / q) *
      (∑ y ∈ B, |g y| ^ (q / (q - 1))) ^ (1 / (q / (q - 1))) := by
  have hpq := Rigidity.Poincare.holderConjugate_conj hq
  have h := Real.inner_le_Lp_mul_Lq B (fun y => |g y|) (fun _ => (1 : ℝ)) hpq
  simp only [mul_one, abs_abs, abs_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul,
    mul_one] at h
  rw [mul_comm]
  exact h

/-- The last step: from `V ≤ c R^{d/q} V^{1/p} Q^{1/q}` to `V / R^d ≤ c^q Q`. -/
theorem div_pow_le_of_le_rpow {V Q R c p q : ℝ} (hV : 0 < V) (hQ : 0 ≤ Q) (hR : 0 < R)
    (hc : 0 ≤ c) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1)
    (h : V ≤ c * R ^ ((d : ℝ) / q) * V ^ (1 / p) * Q ^ (1 / q)) : V / R ^ d ≤ c ^ q * Q := by
  have hVsplit : V = V ^ (1 / p) * V ^ (1 / q) := by
    rw [← Real.rpow_add hV, hpq, Real.rpow_one]
  have hVp : 0 < V ^ (1 / p) := Real.rpow_pos_of_pos hV _
  have hRq : 0 ≤ R ^ ((d : ℝ) / q) := Real.rpow_nonneg hR.le _
  have hQq : 0 ≤ Q ^ (1 / q) := Real.rpow_nonneg hQ _
  have h1 : V ^ (1 / q) ≤ c * R ^ ((d : ℝ) / q) * Q ^ (1 / q) := by
    have h' : V ^ (1 / p) * V ^ (1 / q) ≤
        V ^ (1 / p) * (c * R ^ ((d : ℝ) / q) * Q ^ (1 / q)) := by
      calc V ^ (1 / p) * V ^ (1 / q) = V := hVsplit.symm
        _ ≤ c * R ^ ((d : ℝ) / q) * V ^ (1 / p) * Q ^ (1 / q) := h
        _ = V ^ (1 / p) * (c * R ^ ((d : ℝ) / q) * Q ^ (1 / q)) := by ring
    exact le_of_mul_le_mul_left h' hVp
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hV.le _) h1 hq.le
  rw [← Real.rpow_mul hV.le, one_div_mul_cancel hq.ne', Real.rpow_one,
    Real.mul_rpow (mul_nonneg hc hRq) hQq, Real.mul_rpow hc hRq, ← Real.rpow_mul hR.le,
    ← Real.rpow_mul hQ, one_div_mul_cancel hq.ne', Real.rpow_one,
    show (d : ℝ) / q * q = d by field_simp, Real.rpow_natCast] at h2
  rw [div_le_iff₀ (pow_pos hR d)]
  nlinarith

/-- **The multiscale Poincaré inequality on boxes `[-ρ, ρ]^d`**, `R = 2ρ + 1`, with the constant
`(K q)^q`. -/
theorem exists_multiscalePoincare_box [NeZero d] : ∃ K : ℝ, 0 < K ∧ ∀ u : Vertex d → ℝ,
    HeatSummable u →
    ∀ ρ : ℕ, 1 ≤ ρ → ∀ q : ℝ, 2 ≤ q →
      ENNReal.ofReal ((∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q) /
          (2 * ρ + 1 : ℝ) ^ d) ≤
        ENNReal.ofReal ((K * q) ^ q) *
          ∑' x, dwt (2 * ρ + 1) x * sqInt u (2 * (2 * ρ + 1)) x ^ (q / 2) := by
  obtain ⟨Cs, hCs, hStein⟩ := exists_steinSigned (d := d)
  obtain ⟨Kl, hKl, hLow⟩ := exists_ofReal_sq_heatGrad_le (d := d)
  have hCs0 : 0 < Cs := by linarith
  have hsK : 0 ≤ Real.sqrt Kl := Real.sqrt_nonneg Kl
  have hc1 : 0 < 2 * Real.sqrt 2 * (2 ^ (d + 1) * Real.exp d) * Cs := by positivity
  have hdK : 0 ≤ d * Real.sqrt Kl := by positivity
  have hK₁ : 0 < 2 * Real.sqrt 2 * (2 ^ (d + 1) * Real.exp d) * Cs + d * Real.sqrt Kl := by
    linarith
  refine ⟨6 * (2 * Real.sqrt 2 * (2 ^ (d + 1) * Real.exp d) * Cs + d * Real.sqrt Kl), by linarith,
    fun u hu ρ hρ q hq => ?_⟩
  have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hR0 : (0 : ℝ) < 2 * ρ + 1 := by linarith
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hq10 : 0 < q - 1 := by linarith
  have hp1 : 1 < q / (q - 1) := by rw [lt_div_iff₀ hq10]; linarith
  have hp0 : 0 < q / (q - 1) := by linarith
  have hpq : 1 / (q / (q - 1)) + 1 / q = 1 := by field_simp; ring
  have hBne : (supBox (0 : Vertex d) ρ).Nonempty := ⟨0, self_mem_supBox 0 ρ⟩
  have hcard : ((supBox (0 : Vertex d) ρ).card : ℝ) = (2 * ρ + 1 : ℝ) ^ d := by
    rw [card_supBox]
    push_cast
    ring
  have hV0 : 0 ≤ ∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q :=
    Finset.sum_nonneg fun z _ => Real.rpow_nonneg (abs_nonneg _) _
  have hKq :
      0 < (6 * (2 * Real.sqrt 2 * (2 ^ (d + 1) * Real.exp d) * Cs + d * Real.sqrt Kl) * q) ^ q :=
    Real.rpow_pos_of_pos (mul_pos (by linarith) hq0) _
  by_cases htop : ∑' x, dwt (2 * ρ + 1) x * sqInt u (2 * (2 * ρ + 1)) x ^ (q / 2) = ⊤
  · rw [htop, ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hKq)]
    exact le_top
  rcases hV0.lt_or_eq with hVpos | hVz
  swap
  · rw [← hVz, zero_div, ENNReal.ofReal_zero]
    exact zero_le
  -- the test function and its field
  have hgS : ∀ y ∉ supBox 0 ρ, dualTest (supBox 0 ρ) u q y = 0 := fun y hy => dualTest_eq_zero hy
  have hgsum : ∑ y ∈ supBox 0 ρ, dualTest (supBox 0 ρ) u q y = 0 := sum_dualTest hBne u q
  have hgu : ∑' y, dualTest (supBox 0 ρ) u q y * u y =
      ∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q := by
    rw [tsum_eq_sum (s := supBox 0 ρ) fun y hy => by rw [hgS y hy, zero_mul]]
    exact sum_dualTest_mul hBne u hq
  have hGS : ∀ j, ∀ y ∉ supBox 0 ρ, boxField ρ (dualTest (supBox 0 ρ) u q) j y = 0 :=
    fun j y hy => boxField_eq_zero j hy
  have hdiv : divField (boxField ρ (dualTest (supBox 0 ρ) u q)) = dualTest (supBox 0 ρ) u q :=
    funext fun y => divField_boxField hgS hgsum y
  have hT : (0 : ℝ) ≤ 2 * (4 * (2 * ρ + 1 : ℝ) ^ 2) := by positivity
  have hid := tsum_mul_eq_add_integral hu hGS hT
  rw [hdiv, hgu] at hid
  -- the two terms
  have hII := ofReal_abs_termII_le hKl hLow hu hρ hq (g := dualTest (supBox 0 ρ) u q)
  have hI := ofReal_abs_termI_le hCs hStein hu hρ hq hgS
  rw [show 8 * (2 * (ρ : ℝ) + 1) ^ 2 = 2 * (4 * (2 * ρ + 1 : ℝ) ^ 2) by ring] at hII
  -- the real bound
  have hG0 : 0 ≤ ∑ y ∈ supBox 0 ρ, |dualTest (supBox 0 ρ) u q y| ^ (q / (q - 1)) :=
    Finset.sum_nonneg fun y _ => Real.rpow_nonneg (abs_nonneg _) _
  have hGp : (∑ y ∈ supBox 0 ρ, |dualTest (supBox 0 ρ) u q y| ^ (q / (q - 1))) ^
      (1 / (q / (q - 1))) ≤
      6 * (∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q) ^ (1 / (q / (q - 1))) := by
    have h := sum_abs_dualTest_rpow_le hBne u hq
    calc _ ≤ (2 * 3 ^ (q / (q - 1)) * ∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q) ^
          (1 / (q / (q - 1))) := Real.rpow_le_rpow hG0 h (by positivity)
      _ = 2 ^ (1 / (q / (q - 1))) * 3 *
          (∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q) ^ (1 / (q / (q - 1))) := by
          rw [Real.mul_rpow (by positivity) hV0, Real.mul_rpow (by norm_num) (by positivity),
            ← Real.rpow_mul (by norm_num), mul_one_div_cancel hp0.ne', Real.rpow_one]
      _ ≤ 2 * 3 * (∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q) ^
          (1 / (q / (q - 1))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by norm_num))
            (Real.rpow_nonneg hV0 _)
          calc (2 : ℝ) ^ (1 / (q / (q - 1))) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num)
                  (by rw [div_le_one hp0]; linarith)
            _ = 2 := Real.rpow_one 2
      _ = _ := by ring
  have hgabs : ∑ y ∈ supBox 0 ρ, |dualTest (supBox 0 ρ) u q y| ≤
      (2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) *
        (∑ y ∈ supBox 0 ρ, |dualTest (supBox 0 ρ) u q y| ^ (q / (q - 1))) ^
          (1 / (q / (q - 1))) := by
    have h := sum_abs_le_card_rpow_mul (B := supBox 0 ρ) (dualTest (supBox 0 ρ) u q) hq1
    rw [hcard, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le] at h
    rw [show (d : ℝ) * (1 / q) = (d : ℝ) / q by ring] at h
    exact h
  set Vp := (∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q) ^ (1 / (q / (q - 1)))
    with hVpdef
  have hVp0 : 0 ≤ Vp := Real.rpow_nonneg hV0 _
  have hRq : 0 ≤ (2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) := Real.rpow_nonneg hR0.le _
  have hreal : d * Real.sqrt Kl * ∑ y ∈ supBox 0 ρ, |dualTest (supBox 0 ρ) u q y| +
      2 * Real.sqrt 2 * (2 ^ (d + 1) * Real.exp d) * Cs * q * (2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) *
        (∑ y ∈ supBox 0 ρ, |dualTest (supBox 0 ρ) u q y| ^ (q / (q - 1))) ^ (1 / (q / (q - 1)))
      ≤ 6 * (2 * Real.sqrt 2 * (2 ^ (d + 1) * Real.exp d) * Cs + d * Real.sqrt Kl) * q *
        (2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) * Vp := by
    have a1 := hgabs.trans (mul_le_mul_of_nonneg_left hGp hRq)
    have t1 := mul_le_mul_of_nonneg_left a1 hdK
    have hX : 0 ≤ (2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) * Vp := mul_nonneg hRq hVp0
    have t1' : d * Real.sqrt Kl * ((2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) * (6 * Vp)) ≤
        d * Real.sqrt Kl * q * ((2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) * (6 * Vp)) := by
      have : 0 ≤ d * Real.sqrt Kl * ((2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) * (6 * Vp)) := by positivity
      nlinarith
    have t2 := mul_le_mul_of_nonneg_left hGp
      (mul_nonneg hc1.le (mul_nonneg hq0.le hRq) :
        (0 : ℝ) ≤ 2 * Real.sqrt 2 * (2 ^ (d + 1) * Real.exp d) * Cs *
          (q * (2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q)))
    nlinarith
  have hsum : ENNReal.ofReal (∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q) ≤
      ENNReal.ofReal (6 * (2 * Real.sqrt 2 * (2 ^ (d + 1) * Real.exp d) * Cs + d * Real.sqrt Kl) *
        q *
        (2 * ρ + 1 : ℝ) ^ ((d : ℝ) / q) * Vp) *
      (∑' x, dwt (2 * ρ + 1) x * sqInt u (2 * (2 * ρ + 1)) x ^ (q / 2)) ^ (1 / q) := by
    rw [hid]
    refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
    refine (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans ?_
    rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine (add_le_add hII hI).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (mul_nonneg (mul_nonneg hc1.le
        (mul_nonneg hq0.le hRq) |>.trans_eq (by ring)) (Real.rpow_nonneg hG0 _))]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) (by simp)
  -- conclude
  set RHS := ∑' x, dwt (2 * ρ + 1) x * sqInt u (2 * (2 * ρ + 1)) x ^ (q / 2) with hRHS
  have hRHSeq : RHS = ENNReal.ofReal RHS.toReal := (ENNReal.ofReal_toReal htop).symm
  have hQ0 : 0 ≤ RHS.toReal := ENNReal.toReal_nonneg
  rw [hRHSeq, ENNReal.ofReal_rpow_of_nonneg hQ0 (by positivity),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hq0.le) hRq)
      hVp0)] at hsum
  have hsumR := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by linarith) hq0.le) hRq) hVp0) (Real.rpow_nonneg hQ0 _))).1 hsum
  rw [hRHSeq, ← ENNReal.ofReal_mul hKq.le]
  exact ENNReal.ofReal_le_ofReal (div_pow_le_of_le_rpow hVpos hQ0 hR0
    (mul_nonneg (by linarith) hq0.le) hq0 hpq hsumR)

/-- `|Φ_{r²} * ∇u(x)| = Σ_j |Σ_y Φ_{r²}(x, y) ∇_j u(y)|`, the integrand of Dario's (2.26). -/
noncomputable def heatGradient (u : Vertex d → ℝ) (r : ℝ) (x : Vertex d) : ℝ :=
  ∑ j : Fin d, |∑' y, zdHeat d (r ^ 2) x y * (u (y + unit j) - u y)|

/-- The `L^q` oscillation `3^{-dm} Σ_{□_m} |u - (u)_{□_m}|^q` of `u` on the cube `□_m` of side
`3^m` centred at the origin. -/
noncomputable def boxOscFun (u : Vertex d → ℝ) (m : ℕ) (q : ℝ) : ℝ :=
  (∑ z ∈ supBox 0 (3 ^ m / 2),
    |u z - (∑ w ∈ supBox 0 (3 ^ m / 2), u w) / ((3 : ℝ) ^ m) ^ d| ^ q) / ((3 : ℝ) ^ m) ^ d

/-- **The multiscale Poincaré inequality of Dario, Proposition 2.19 (2.26), in cube form at
`R = 3^m` on `ℤ^d`**, with the bound `C(d, q) ≤ A₀ q^{3/2}` for `q ≥ 2`. The convolutions
`Φ_{r²} * ∇u` of (2.26) are required to converge absolutely. -/
def MultiscalePoincare (d : ℕ) (A₀ : ℝ) : Prop :=
  ∀ u : Vertex d → ℝ, (∀ (x : Vertex d) (j : Fin d) (r : ℝ), 0 < r →
      Summable fun y => zdHeat d (r ^ 2) x y * (u (y + unit j) - u y)) →
    ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ, 2 ≤ q →
    ENNReal.ofReal (boxOscFun u m q) ≤
      ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q) *
        ∑' x : Vertex d, ENNReal.ofReal
          (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / ((3 : ℝ) ^ m) ^ d) *
          (∫⁻ r in Set.Ioc 0 (2 * 3 ^ m), ENNReal.ofReal (r * heatGradient u r x ^ 2)) ^ (q / 2)

/-- **Dario's multiscale Poincaré inequality, Proposition 2.19 (2.26), on `ℤ^d`**, `d ≥ 1`, with
a constant `A₀ q^{3/2}` for every `q ≥ 2`. -/
theorem multiscalePoincare_holds [NeZero d] : ∃ A₀ : ℝ, 0 < A₀ ∧ MultiscalePoincare d A₀ := by
  obtain ⟨K, hK, hkey⟩ := exists_multiscalePoincare_box (d := d)
  refine ⟨K, hK, fun u hsum m hm q hq => ?_⟩
  have hu : HeatSummable u := by
    intro x j t ht
    have h := hsum x j (Real.sqrt t) (Real.sqrt_pos.2 ht)
    rwa [Real.sq_sqrt ht.le] at h
  set ρ : ℕ := 3 ^ m / 2 with hρ
  have hodd : Odd (3 ^ m) := Odd.pow (by decide)
  have hρ2 : 2 * ρ + 1 = 3 ^ m := Nat.two_mul_div_two_add_one_of_odd hodd
  have hρ1 : 1 ≤ ρ := by
    have h3 : 3 ≤ 3 ^ m := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hRreal : (2 * (ρ : ℝ) + 1) = 3 ^ m := by exact_mod_cast hρ2
  have hcard : ((supBox (0 : Vertex d) ρ).card : ℝ) = ((3 : ℝ) ^ m) ^ d := by
    rw [card_supBox]
    push_cast
    rw [hRreal]
  have hLHS : boxOscFun u m q =
      (∑ z ∈ supBox 0 ρ, |u z - boxMean (supBox 0 ρ) u| ^ q) / (2 * ρ + 1 : ℝ) ^ d := by
    rw [boxOscFun, hRreal, boxMean, hcard]
  have hRHS : ∀ x, dwt (2 * ρ + 1) x * sqInt u (2 * (2 * ρ + 1)) x ^ (q / 2) =
      ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) /
          ((3 : ℝ) ^ m) ^ d) *
        (∫⁻ r in Set.Ioc 0 (2 * 3 ^ m),
          ENNReal.ofReal (r * heatGradient u r x ^ 2)) ^ (q / 2) := by
    intro x
    rw [dwt, sqInt, hRreal]
    rfl
  have h := hkey u hu ρ hρ1 q hq
  rw [← hLHS] at h
  simp only [hRHS] at h
  refine h.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by simp))
  have hq1 : (1 : ℝ) ≤ q := by linarith
  refine Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left ?_ hK.le) (by linarith)
  calc q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
    _ ≤ q ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)

end Rigidity.Poincare.GeneralDim

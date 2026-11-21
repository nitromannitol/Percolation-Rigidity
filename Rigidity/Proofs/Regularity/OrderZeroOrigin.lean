import Rigidity.Proofs.Regularity.KIteration
import Rigidity.Proofs.Regularity.SinglePolynomial

/-!
# Excess decay of order zero at the origin

Armstrong and Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(arXiv:1609.09431v2), Section 7: Lemma 7.2 for `k = 0` bounds the distance `D_0(r)` of `u` to the
constants on each ball `B_r`, `r ∈ [X ∨ C, R / 2]`, by `C (r / R) D_0(R) + C r ^ (1 - α) (D_0(R) / R +
E / r)`. For `r ≥ 1` both error terms are at most `(r / R) (D_0(R) + R E)`, so the excess decays
linearly in `r / R`, and the Campanato argument of `Rigidity.Proofs.Regularity.SinglePolynomial`
gives one constant `φ` with `‖u - φ‖_{L̲²(B_r)} ≤ C (r / R) (D_0(R) + R E)` for all these radii: the
form of the order-zero regularity (Theorem 2 (iii), `k = 0`) at the origin.

The result `armstrongDario_orderZero_origin` is stated in the abstract setting of
`Rigidity.Proofs.Regularity.BallExcess`, for any bound `B > 0` of `D_0(R) + R E`; it uses in
addition that the constants have comparable norms on comparable balls (`PolynomialGrowth` with
`k = 0`; on nonempty cluster balls the normalized norm of a constant is its absolute value).
-/

namespace Rigidity.Proofs.Regularity

universe u

/-- **Excess decay of order zero at the origin** from Armstrong–Dario, Lemma 7.2 (`k = 0`) and
the Campanato argument. -/
theorem armstrongDario_orderZero_origin {A α γ CV CP CH CG : ℝ} (hA : 2 ≤ A) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) (hCG : 0 ≤ CG) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type u} [AddCommGroup F] (N : ℝ → AddGroupSeminorm F)
      (P₀ P₁ : AddSubgroup F) (Abar : ℝ → Set F) (R X E : ℝ) (u : F),
      P₀ ≤ P₁ → 1 ≤ X → X ≤ R / A → 0 ≤ E →
      RadiusMonotone N X R CV γ → PolynomialComparison N P₀ P₁ 1 X R CP →
      HarmonicRegularity N Abar P₁ 1 X R CH → (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation N Abar P₀ A α X R E u → PolynomialGrowth N P₀ 0 X R CG →
      ∀ B : ℝ, 0 < B → ballExcess N P₀ R u + R * E ≤ B →
        ∃ φ ∈ P₀, ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 → N r (u - φ) ≤ C * (r / R) * B := by
  obtain ⟨C₁, hC₁, hlemma⟩ := armstrongDario_lemma_7_2_zero.{u} hA hα hγ hCV hCP hCH
  set K := singlePolynomialConst CV CG γ 0 with hK
  have hK0 : 0 ≤ K := by
    rw [hK, singlePolynomialConst]
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) γ
    positivity
  refine ⟨C₁ + 2 * C₁ * K + 1, by positivity, ?_⟩
  intro F _ N P₀ P₁ Abar R X E u hP hX hXR hE hmono hpc hreg hne happ hgrowth B hB hBu
  have hX0 : 0 < X := by linarith
  set X' := max X C₁ with hX'
  have hX'0 : 0 < X' := hX0.trans_le (le_max_left _ _)
  have hX'1 : 1 ≤ X' := hX.trans (le_max_left _ _)
  by_cases hXR2 : X' ≤ R / 2
  · have hR0 : 0 < R := by linarith
    have hD : ∀ ρ : ℝ, X' ≤ ρ → ρ ≤ R / 2 →
        ballExcess N P₀ ρ u ≤ 2 * C₁ * B * (ρ / R) ^ (0 + 1) := by
      intro ρ hρ hρR
      have hρ1 : 1 ≤ ρ := hX'1.trans hρ
      have hρ0 : 0 < ρ := by linarith
      have h1 := hlemma N P₀ P₁ Abar R X E u hP hX hXR hE hmono hpc hreg hne happ ρ hρ hρR
      have hDR := ballExcess_nonneg N P₀ R u
      have hpow : ρ ^ (1 - α) ≤ ρ := by
        calc ρ ^ (1 - α) ≤ ρ ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)
          _ = ρ := Real.rpow_one ρ
      have hpowE : ρ ^ (1 - α) * (E / ρ) ≤ ρ / R * (R * E) := by
        have : ρ ^ (1 - α) * (E / ρ) ≤ ρ * (E / ρ) :=
          mul_le_mul_of_nonneg_right hpow (div_nonneg hE hρ0.le)
        have e : ρ * (E / ρ) = E := by field_simp
        have e2 : ρ / R * (R * E) = ρ * E := by field_simp
        rw [e] at this
        rw [e2]
        nlinarith
      have hpowG : ρ ^ (1 - α) * (ballExcess N P₀ R u / R) ≤ ρ / R * ballExcess N P₀ R u := by
        have := mul_le_mul_of_nonneg_right hpow (div_nonneg hDR hR0.le)
        have e : ρ * (ballExcess N P₀ R u / R) = ρ / R * ballExcess N P₀ R u := by ring
        linarith
      have h2 : ballExcess N P₀ ρ u ≤
          C₁ * (ρ / R) * (2 * ballExcess N P₀ R u + R * E) := by
        have e : C₁ * ρ ^ (1 - α) * (ballExcess N P₀ R u / R + E / ρ) =
            C₁ * (ρ ^ (1 - α) * (ballExcess N P₀ R u / R) + ρ ^ (1 - α) * (E / ρ)) := by ring
        rw [e] at h1
        have h3 := mul_le_mul_of_nonneg_left (add_le_add hpowG hpowE) hC₁.le
        linarith
      have hρR' : 0 ≤ ρ / R := div_nonneg hρ0.le hR0.le
      have hRE : 0 ≤ R * E := mul_nonneg hR0.le hE
      have h4 : 2 * ballExcess N P₀ R u + R * E ≤ 2 * B := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hC₁.le hρR')
      rw [zero_add, pow_one]
      linarith
    obtain ⟨φ, hφ, hφbound⟩ := exists_mem_forall_le_of_ballExcess_le N P₀ hX'0 hXR2 hR0
      (by positivity : 0 < 2 * C₁ * B) hCV hCG hγ
      (fun f s r hs hsr hr => hmono f s r ((le_max_left _ _).trans hs) hsr (by linarith))
      (fun w hw ρ r hρ hρr hr => hgrowth w hw ρ r ((le_max_left _ _).trans hρ) hρr
        (by linarith)) u hD
    refine ⟨φ, hφ, fun r hr hrR => ?_⟩
    have hrX' : X' ≤ r := max_le ((le_max_left _ _).trans hr)
      (by linarith [le_max_right X (C₁ + 2 * C₁ * K + 1), mul_nonneg hC₁.le hK0])
    have h1 := hφbound r hrX' hrR
    rw [← hK, zero_add, pow_one] at h1
    have hr0 : 0 < r := hX'0.trans_le hrX'
    have hrR' : 0 ≤ r / R := div_nonneg hr0.le hR0.le
    calc N r (u - φ) ≤ K * (2 * C₁ * B) * (r / R) := h1
      _ = 2 * C₁ * K * (r / R) * B := by ring
      _ ≤ (C₁ + 2 * C₁ * K + 1) * (r / R) * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hrR') hB.le
  · refine ⟨0, P₀.zero_mem, fun r hr hrR => absurd (le_trans ?_ hrR) hXR2⟩
    exact max_le ((le_max_left _ _).trans hr)
      (by linarith [le_max_right X (C₁ + 2 * C₁ * K + 1), mul_nonneg hC₁.le hK0])

end Rigidity.Proofs.Regularity

import Rigidity.Proofs.Regularity.KIteration

/-!
# Armstrong–Dario Lemma 7.2 for every order `k`

Armstrong and Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(arXiv:1609.09431v2), Lemma 7.2, for every `k ∈ ℕ`, in the abstract setting of
`Rigidity.Proofs.Regularity.BallExcess`: the polynomial spaces of degrees `0 ≤ 1` (for the bound of
the supremum in the harmonic approximation hypothesis, Step 3 of the proof for `k = 0`) and of
degrees `k ≤ k + 1` (for the iteration of `D_{k+1}`, Step 3 of the proof of Armstrong–Kuusi–Mourrat,
Lemma 2.4, to which the paper refers) are additive subgroups `P₀ ≤ P₁` and `Pk ≤ Pk₁`. The cases
`k = 0` and `k = 1` are also `armstrongDario_lemma_7_2_zero` and `armstrongDario_lemma_7_2_one`.
-/

namespace Rigidity.Proofs.Regularity

universe u

/-- **Armstrong–Dario, Lemma 7.2**, for every `k`: for `r ∈ [X ∨ C, R / 2]`,
`D_k(r) ≤ C (r / R) ^ (k + 1) D_k(R) + C r ^ (1 - α) (D_0(R) / R + E / r)`. -/
theorem armstrongDario_lemma_7_2 (k : ℕ) {A α γ CV CP CH : ℝ} (hA : 2 ≤ A) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type u} [AddCommGroup F] (N : ℝ → AddGroupSeminorm F)
      (P₀ P₁ Pk Pk₁ : AddSubgroup F) (Abar : ℝ → Set F) (R X E : ℝ) (u : F),
      P₀ ≤ P₁ → Pk ≤ Pk₁ → 1 ≤ X → X ≤ R / A → 0 ≤ E →
      RadiusMonotone N X R CV γ → PolynomialComparison N P₀ P₁ 1 X R CP →
      PolynomialComparison N Pk Pk₁ (k + 1) X R CP →
      HarmonicRegularity N Abar P₁ 1 X R CH → HarmonicRegularity N Abar Pk₁ (k + 1) X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation N Abar P₀ A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess N Pk r u ≤ C * (r / R) ^ (k + 1) * ballExcess N Pk R u +
          C * r ^ (1 - α) * (ballExcess N P₀ R u / R + E / r) := by
  set r₀ := absorptionRadius CV CP CH γ α
  set K := slopeConst A CV CP CH γ
  set K₂ := scaleConstTwo CV CP CH γ α 1
  set K'' := K + 2 * K₂ + 1
  set S₁ := scaleConstOne A CV CP CH γ (k + 1)
  set S₂ := scaleConstTwo CV CP CH γ α (k + 1)
  have hA0 : 0 < A := by linarith
  have hK0 : 0 ≤ K := slopeConst_nonneg hA0.le hCV hCP hCH
  have hK₂0 : 0 ≤ K₂ := scaleConstTwo_nonneg hCV hCP hCH hα le_rfl
  have hr₀ : 1 ≤ r₀ := one_le_absorptionRadius hCV hCP hCH hα
  have hS₁ : 0 ≤ S₁ := scaleConstOne_nonneg hA0.le hCV hCP hCH (k + 1)
  have hS₂ : 0 ≤ S₂ := scaleConstTwo_nonneg hCV hCP hCH hα (Nat.le_add_left 1 k)
  have hVA : 0 ≤ CV * A ^ γ * A ^ (k + 1) := by
    have := Real.rpow_nonneg hA0.le γ
    positivity
  set C := r₀ + S₁ + CV * A ^ γ * A ^ (k + 1) + S₂ * K'' + 1 with hC
  have hK''0 : 0 ≤ K'' := by positivity
  have hSK : 0 ≤ S₂ * K'' := mul_nonneg hS₂ hK''0
  have hC1 : S₁ ≤ C := by have := mul_nonneg hS₂ hK''0; linarith
  have hC2 : CV * A ^ γ * A ^ (k + 1) ≤ C := by have := mul_nonneg hS₂ hK''0; linarith
  have hC3 : S₂ * K'' ≤ C := by linarith
  refine ⟨C, by have := mul_nonneg hS₂ hK''0; linarith, ?_⟩
  intro F _ N P₀ P₁ Pk Pk₁ Abar R X E u hP₀ hP₁ hX hXR hE hmono hpc₁ hpc₂ hreg₁ hreg₂ hne happ r
    hr hrR
  have hX0 : 0 < X := by linarith
  have hrX : max X r₀ ≤ r :=
    max_le (le_max_left _ _ |>.trans hr) (by linarith [le_max_right X C])
  have hr0 : 0 < r := hX0.trans_le ((le_max_left _ _).trans hrX)
  have hR0 : 0 < R := by linarith
  have hDR := ballExcess_nonneg N Pk R u
  have hG := div_nonneg (ballExcess_nonneg N P₀ R u) hR0.le
  have hrα := Real.rpow_nonneg hr0.le (1 - α)
  have hrR2 : 0 ≤ (r / R) ^ (k + 1) := pow_nonneg (div_nonneg hr0.le hR0.le) _
  by_cases hrA : r ≤ R / A
  · set X' := max X r₀ with hX'
    have hX'0 : 0 < X' := hX0.trans_le (le_max_left _ _)
    have hΓ : 0 ≤ K'' * (ballExcess N P₀ R u / R + E / r) :=
      mul_nonneg hK''0 (add_nonneg hG (div_nonneg hE hr0.le))
    have hthrough := ballExcess_le_of_ballDist_le N hP₁ (Nat.le_add_left 1 k) hA hX'0 hCV hCP
      hCH hγ hα hΓ (hmono.of_le N (le_max_left _ _)) (hpc₂.of_le N (le_max_left _ _))
      (hreg₂.of_le N (le_max_left _ _)) u hrX hrA
      (fun ρ hρ hρ' => hne ρ ((le_max_left _ _).trans (hrX.trans hρ)) hρ')
      (fun ρ hρ hρ' => by
        have hρX : max X r₀ ≤ ρ := hrX.trans hρ
        have hρ0 : 0 < ρ := hr0.trans_le hρ
        have hAρ : A * ρ ≤ R := by rw [le_div_iff₀ hA0] at hρ'; linarith
        have h1 := happ ρ ((le_max_left _ _).trans hρX) hρ'
        have h2 := iSup_ballExcess_div_le N hP₀ hA hX0 hE hCV hCP hCH hγ hα hmono hpc₁ hreg₁ hne u
          happ hρX hAρ
        have h3 : E / ρ ≤ E / r := div_le_div_of_nonneg_left hE hr0 hρ
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hρ0.le _))
        have hEρ : 0 ≤ E / ρ := div_nonneg hE hρ0.le
        have h4 : K * (ballExcess N P₀ R u / R) + 2 * K₂ * (E / ρ) + E / ρ ≤
            K'' * (ballExcess N P₀ R u / R + E / r) := by
          have : K * (ballExcess N P₀ R u / R) ≤ K'' * (ballExcess N P₀ R u / R) :=
            mul_le_mul_of_nonneg_right (by linarith) hG
          have h5 : (2 * K₂ + 1) * (E / ρ) ≤ (2 * K₂ + 1) * (E / r) :=
            mul_le_mul_of_nonneg_left h3 (by linarith)
          have h6 : (2 * K₂ + 1) * (E / r) ≤ K'' * (E / r) :=
            mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hE hr0.le)
          nlinarith
        linarith)
    have h1 : S₁ * (r / R) ^ (k + 1) * ballExcess N Pk R u ≤
        C * (r / R) ^ (k + 1) * ballExcess N Pk R u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hrR2) hDR
    have h2 : S₂ * r ^ (1 - α) * (K'' * (ballExcess N P₀ R u / R + E / r)) ≤
        C * r ^ (1 - α) * (ballExcess N P₀ R u / R + E / r) := by
      have := mul_le_mul_of_nonneg_right hC3
        (mul_nonneg hrα (add_nonneg hG (div_nonneg hE hr0.le)))
      nlinarith
    linarith
  · have hrA' : R / A < r := not_le.1 hrA
    have hXr : X ≤ r := (le_max_left _ _).trans hrX
    have h1 := ballExcess_le_of_radiusMonotone N Pk hCV hmono hXr (by linarith) le_rfl hr0 u
    have hRr : R / r ≤ A := by
      rw [div_lt_iff₀ hA0] at hrA'
      rw [div_le_iff₀ hr0]; linarith
    have h2 : (R / r) ^ γ ≤ A ^ γ := Real.rpow_le_rpow (div_nonneg hR0.le hr0.le) hRr hγ
    have h3 : 1 ≤ A ^ (k + 1) * (r / R) ^ (k + 1) := by
      rw [← mul_pow]
      have : 1 ≤ A * (r / R) := by
        rw [div_lt_iff₀ hA0] at hrA'
        rw [mul_div_assoc', le_div_iff₀ hR0]; linarith
      exact one_le_pow₀ this
    have h4 : ballExcess N Pk r u ≤ CV * A ^ γ * ballExcess N Pk R u :=
      h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCV) hDR)
    have h5 : CV * A ^ γ * ballExcess N Pk R u ≤
        CV * A ^ γ * A ^ (k + 1) * (r / R) ^ (k + 1) * ballExcess N Pk R u := by
      have hc : 0 ≤ CV * A ^ γ * ballExcess N Pk R u :=
        mul_nonneg (mul_nonneg hCV (Real.rpow_nonneg hA0.le γ)) hDR
      have := mul_le_mul_of_nonneg_left h3 hc
      calc CV * A ^ γ * ballExcess N Pk R u = CV * A ^ γ * ballExcess N Pk R u * 1 := by ring
        _ ≤ CV * A ^ γ * ballExcess N Pk R u * (A ^ (k + 1) * (r / R) ^ (k + 1)) := this
        _ = CV * A ^ γ * A ^ (k + 1) * (r / R) ^ (k + 1) * ballExcess N Pk R u := by ring
    have h6 : CV * A ^ γ * A ^ (k + 1) * (r / R) ^ (k + 1) * ballExcess N Pk R u ≤
        C * (r / R) ^ (k + 1) * ballExcess N Pk R u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hrR2) hDR
    have h7 : 0 ≤ C * r ^ (1 - α) * (ballExcess N P₀ R u / R + E / r) := by
      have hC0 : 0 ≤ C := by linarith
      exact mul_nonneg (mul_nonneg hC0 hrα) (add_nonneg hG (div_nonneg hE hr0.le))
    linarith

end Rigidity.Proofs.Regularity

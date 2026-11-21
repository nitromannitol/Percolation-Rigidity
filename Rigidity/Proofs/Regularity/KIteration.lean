import Rigidity.Proofs.Regularity.KIterationCore

/-!
# Armstrong–Dario Lemma 7.2 for `k = 0` and `k = 1`

Armstrong and Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(arXiv:1609.09431v2), Lemma 7.2: fix `A ≥ 2`, `α > 0` and `u` on `B_R`; write
`D_k(s) = inf_{w ∈ Ā_k} ‖u - w‖_{L̲²(B_s)}`. If `X ∈ [1, R / A]` and `E ≥ 0` are such that for
every `r ∈ [X, R / A]`
`inf_{v ∈ Ā(B_r)} ‖u - v‖_{L̲²(B_r)} ≤ r ^ (1 - α) (sup_{A r ≤ s ≤ R} D_0(s) / s + E / r)`,
then for each `k` there is `C`, depending only on `k`, `A`, `α` and the constants of the
harmonic regularity, such that for every `r ∈ [X ∨ C, R / 2]`
`D_k(r) ≤ C (r / R) ^ (k + 1) D_k(R) + C r ^ (1 - α) (D_0(R) / R + E / r)`.

We prove it for `k = 0` (`armstrongDario_lemma_7_2_zero`) and `k = 1`
(`armstrongDario_lemma_7_2_one`) in the abstract setting of `Rigidity.Proofs.Regularity.BallExcess`:
the normalized norms on balls are a family of seminorms `N s` with the properties
`RadiusMonotone` (on Euclidean balls in dimension `d`: `CV = 1`, `γ = d / 2`),
`PolynomialComparison` and `HarmonicRegularity`, and the polynomial spaces `Ā_0 ≤ Ā_1 ≤ Ā_2` are
additive subgroups. The constants depend only on `A`, `α`, `γ`, `CV`, `CP`, `CH`.

The case `k = 0` is Step 3 of the proof in the paper: the iteration for `D_1` and the summation of
the slopes over the scales give `D_0(r) / r ≤ C (D_0(R) / R + E / r ^ (1 + α))`
(`armstrongDario_lemma_7_2_zero_slope`), where the supremum in the hypothesis is absorbed for
`r ≥ C` by an induction over the scales `R / A ^ n`. For `k = 1` the paper refers to Step 3 of the
proof of Armstrong–Kuusi–Mourrat, Lemma 2.4: the bound for `k = 0` turns the hypothesis into
`inf_{v ∈ Ā(B_r)} ‖u - v‖_{L̲²(B_r)} ≤ C r ^ (1 - α) (D_0(R) / R + E / r)`, and the same iteration,
now for `D_2` with the quadratic `ā`-harmonic polynomials `Ā_2`, gives the rate `(r / R) ^ 2`.
-/

universe u

namespace Rigidity.Proofs.Regularity

open Finset

variable {F : Type*} [AddCommGroup F] (N : ℝ → AddGroupSeminorm F)

/-- The harmonic approximation hypothesis of Lemma 7.2: for every `r ∈ [X, R / A]`, `u` is within
`r ^ (1 - α) (sup_{A r ≤ s ≤ R} D_0(s) / s + E / r)` of `Abar r`. -/
def HarmonicApproximation (Abar : ℝ → Set F) (P₀ : AddSubgroup F) (A α X R E : ℝ) (u : F) :
    Prop :=
  ∀ r : ℝ, X ≤ r → r ≤ R / A →
    ballDist N (Abar r) r u ≤
      r ^ (1 - α) * ((⨆ s : Set.Icc (A * r) R, ballExcess N P₀ s u / s) + E / r)

theorem RadiusMonotone.of_le {X X' R CV γ : ℝ} (h : RadiusMonotone N X R CV γ) (hX : X ≤ X') :
    RadiusMonotone N X' R CV γ :=
  fun f s r hs hsr hr => h f s r (hX.trans hs) hsr hr

theorem PolynomialComparison.of_le {Plow Phigh : AddSubgroup F} {j : ℕ} {X X' R CP : ℝ}
    (h : PolynomialComparison N Plow Phigh j X R CP) (hX : X ≤ X') :
    PolynomialComparison N Plow Phigh j X' R CP :=
  fun w hw ρ ρ' hρ hρρ' hρ' => h w hw ρ ρ' (hX.trans hρ) hρρ' hρ'

theorem HarmonicRegularity.of_le {Abar : ℝ → Set F} {P : AddSubgroup F} {j : ℕ} {X X' R CH : ℝ}
    (h : HarmonicRegularity N Abar P j X R CH) (hX : X ≤ X') :
    HarmonicRegularity N Abar P j X' R CH :=
  fun r hr v hv s hs hsr => h r hr v hv s (hX.trans hs) hsr

/-- The ratio `θ = 1 / (2 (CH + 1))` of consecutive radii in the iteration. -/
noncomputable def iterationRatio (CH : ℝ) : ℝ := 1 / (2 * (CH + 1))

theorem iterationRatio_pos {CH : ℝ} (hCH : 0 ≤ CH) : 0 < iterationRatio CH := by
  unfold iterationRatio; positivity

theorem iterationRatio_le_half {CH : ℝ} (hCH : 0 ≤ CH) : iterationRatio CH ≤ 1 / 2 := by
  unfold iterationRatio
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem mul_iterationRatio_le_half {CH : ℝ} (hCH : 0 ≤ CH) : CH * iterationRatio CH ≤ 1 / 2 := by
  unfold iterationRatio
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The constant in front of `(r / R) ^ j D(R)` in `ballExcess_le_of_ballDist_le`. -/
noncomputable def scaleConstOne (A CV CP CH γ : ℝ) (j : ℕ) : ℝ :=
  geometricConstOne CV CP γ (iterationRatio CH) j * CV * (A / iterationRatio CH) ^ γ *
    (A / iterationRatio CH) ^ j

/-- The constant in front of `r ^ (1 - α) Γ` in `ballExcess_le_of_ballDist_le`. -/
noncomputable def scaleConstTwo (CV CP CH γ α : ℝ) (j : ℕ) : ℝ :=
  geometricConstTwo CV CP CH γ α (iterationRatio CH) j

theorem geometricConstOne_nonneg {CV CP γ θ : ℝ} (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hθ : 0 < θ)
    (j : ℕ) : 0 ≤ geometricConstOne CV CP γ θ j := by
  unfold geometricConstOne
  have : 0 ≤ θ⁻¹ ^ γ := Real.rpow_nonneg (inv_nonneg.2 hθ.le) _
  positivity

theorem geometricConstTwo_nonneg {CV CP CH γ α θ : ℝ} (hCV : 0 ≤ CV) (hCP : 0 ≤ CP)
    (hCH : 0 ≤ CH) (hα : 0 < α) (hθ0 : 0 < θ) (hθ1 : θ < 1) {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ geometricConstTwo CV CP CH γ α θ j := by
  unfold geometricConstTwo
  have : 0 ≤ θ⁻¹ ^ γ := Real.rpow_nonneg (inv_nonneg.2 hθ0.le) _
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hq : θ ^ ((j : ℝ) + α - 1) < 1 := Real.rpow_lt_one hθ0.le hθ1 (by linarith)
  have : 0 < 1 - θ ^ ((j : ℝ) + α - 1) := by linarith
  positivity

theorem scaleConstOne_nonneg {A CV CP CH γ : ℝ} (hA : 0 ≤ A) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP)
    (hCH : 0 ≤ CH) (j : ℕ) : 0 ≤ scaleConstOne A CV CP CH γ j := by
  unfold scaleConstOne
  have hθ := iterationRatio_pos hCH
  have := geometricConstOne_nonneg (γ := γ) hCV hCP hθ j
  have : 0 ≤ (A / iterationRatio CH) ^ γ := Real.rpow_nonneg (div_nonneg hA hθ.le) _
  positivity

theorem scaleConstTwo_nonneg {CV CP CH γ α : ℝ} (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH)
    (hα : 0 < α) {j : ℕ} (hj : 1 ≤ j) : 0 ≤ scaleConstTwo CV CP CH γ α j :=
  geometricConstTwo_nonneg hCV hCP hCH hα (iterationRatio_pos hCH)
    ((iterationRatio_le_half hCH).trans_lt (by norm_num)) hj

/-- **Excess decay at a radius `r ∈ [X, R / A]`.** If `u` is within `ρ ^ (1 - α) Γ` of `Abar ρ` for
every `ρ ∈ [r, R / A]`, then `D(r) ≤ C₁ (r / R) ^ j D(R) + C₂ r ^ (1 - α) Γ` for the excess `D`
over `Plow`. The radii `θ^i ρ₀` of the iteration are chosen to end at `r`, with
`ρ₀ ∈ (θ R / A, R / A]`. -/
theorem ballExcess_le_of_ballDist_le {Plow Phigh : AddSubgroup F} (hP : Plow ≤ Phigh)
    {Abar : ℝ → Set F} {j : ℕ} (hj : 1 ≤ j) {A X R CV CP CH γ α Γ : ℝ} (hA : 2 ≤ A)
    (hX0 : 0 < X) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) (hγ : 0 ≤ γ) (hα : 0 < α)
    (hΓ : 0 ≤ Γ) (hmono : RadiusMonotone N X R CV γ)
    (hpc : PolynomialComparison N Plow Phigh j X R CP)
    (hreg : HarmonicRegularity N Abar Phigh j X R CH) (u : F) {r : ℝ} (hXr : X ≤ r)
    (hrA : r ≤ R / A) (hne : ∀ ρ : ℝ, r ≤ ρ → ρ ≤ R / A → (Abar ρ).Nonempty)
    (happ : ∀ ρ : ℝ, r ≤ ρ → ρ ≤ R / A → ballDist N (Abar ρ) ρ u ≤ ρ ^ (1 - α) * Γ) :
    ballExcess N Plow r u ≤ scaleConstOne A CV CP CH γ j * (r / R) ^ j * ballExcess N Plow R u +
      scaleConstTwo CV CP CH γ α j * r ^ (1 - α) * Γ := by
  set θ := iterationRatio CH with hθdef
  have hθ0 : 0 < θ := iterationRatio_pos hCH
  have hθ : θ ≤ 1 / 2 := iterationRatio_le_half hCH
  have hθ1 : θ < 1 := hθ.trans_lt (by norm_num)
  have hCHθ : CH * θ ≤ 1 / 2 := mul_iterationRatio_le_half hCH
  have hA0 : 0 < A := by linarith
  have hr0 : 0 < r := hX0.trans_le hXr
  have htop : 0 < R / A := hr0.trans_le hrA
  have hR0 : 0 < R := by
    have := mul_pos htop hA0
    rwa [div_mul_cancel₀ R hA0.ne'] at this
  have htopR : R / A ≤ R := div_le_self hR0.le (by linarith)
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one (div_pos hr0 htop)
    ((div_le_one htop).2 hrA) hθ0 hθ1
  have hθn : 0 < θ ^ n := pow_pos hθ0 n
  set ρ₀ := r / θ ^ n with hρ₀def
  have hρr : θ ^ n * ρ₀ = r := by rw [hρ₀def]; field_simp [hθn.ne']
  have hρtop : ρ₀ ≤ R / A := by
    rw [hρ₀def, div_le_iff₀ hθn]
    rw [div_le_iff₀ htop] at hn2
    linarith
  have hρlow : θ * (R / A) < ρ₀ := by
    rw [hρ₀def, lt_div_iff₀ hθn]
    rw [lt_div_iff₀ htop, pow_succ] at hn1
    linarith
  have hρ₀ : 0 < ρ₀ := by rw [hρ₀def]; positivity
  have hrρ : r ≤ ρ₀ := by
    rw [← hρr]
    exact mul_le_of_le_one_left hρ₀.le (pow_le_one₀ hθ0.le hθ1.le)
  have hi : ∀ i < n, r ≤ θ ^ i * ρ₀ ∧ θ ^ i * ρ₀ ≤ R / A := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← hρr]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0.le hθ1.le hi.le) hρ₀.le
    · exact (mul_le_of_le_one_left hρ₀.le (pow_le_one₀ hθ0.le hθ1.le)).trans hρtop
  have hgeo := ballExcess_geometric_le N hP hj hX0 hCV hCP hCH hα hθ0 hθ hCHθ hΓ hmono hpc hreg
    (hρtop.trans htopR) (by rw [hρr]; exact hXr) u (fun i hi' => hne _ (hi i hi').1 (hi i hi').2)
    (fun i hi' => happ _ (hi i hi').1 (hi i hi').2)
  rw [hρr] at hgeo
  -- compare the excess at `ρ₀` with the excess at `R`
  have hRρ : R / ρ₀ ≤ A / θ := by
    rw [div_le_div_iff₀ hρ₀ hθ0]
    have : θ * R = A * (θ * (R / A)) := by field_simp
    nlinarith
  have hD := ballExcess_le_of_radiusMonotone N Plow hCV hmono (hXr.trans hrρ)
    (hρtop.trans htopR) le_rfl hρ₀ u
  have hγpow : (R / ρ₀) ^ γ ≤ (A / θ) ^ γ :=
    Real.rpow_le_rpow (div_nonneg hR0.le hρ₀.le) hRρ hγ
  have hθnj : (θ ^ n) ^ j ≤ (A / θ) ^ j * (r / R) ^ j := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ hθn.le
    have : θ ^ n = r / ρ₀ := by rw [← hρr]; field_simp
    rw [this]
    have h1 : r / ρ₀ = (R / ρ₀) * (r / R) := by field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_right hRρ (div_nonneg hr0.le hR0.le)
  have hK1 := geometricConstOne_nonneg (γ := γ) hCV hCP hθ0 j
  have hDR := ballExcess_nonneg N Plow R u
  have hDρ := ballExcess_nonneg N Plow ρ₀ u
  have hstep1 : ballExcess N Plow ρ₀ u ≤ CV * (A / θ) ^ γ * ballExcess N Plow R u :=
    hD.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγpow hCV) hDR)
  have hstep2 : geometricConstOne CV CP γ θ j * (θ ^ n) ^ j * ballExcess N Plow ρ₀ u ≤
      scaleConstOne A CV CP CH γ j * (r / R) ^ j * ballExcess N Plow R u := by
    have h1 := mul_le_mul_of_nonneg_left hstep1 (mul_nonneg hK1 (pow_nonneg hθn.le j))
    have h2 := mul_le_mul_of_nonneg_left hθnj hK1
    have h3 := mul_le_mul_of_nonneg_right h2
      (mul_nonneg (mul_nonneg hCV (Real.rpow_nonneg (div_nonneg hA0.le hθ0.le) γ)) hDR)
    calc geometricConstOne CV CP γ θ j * (θ ^ n) ^ j * ballExcess N Plow ρ₀ u
        ≤ geometricConstOne CV CP γ θ j * (θ ^ n) ^ j *
            (CV * (A / θ) ^ γ * ballExcess N Plow R u) := h1
      _ ≤ geometricConstOne CV CP γ θ j * ((A / θ) ^ j * (r / R) ^ j) *
            (CV * (A / θ) ^ γ * ballExcess N Plow R u) := h3
      _ = scaleConstOne A CV CP CH γ j * (r / R) ^ j * ballExcess N Plow R u := by
        simp only [scaleConstOne, hθdef]; ring
  have : scaleConstTwo CV CP CH γ α j = geometricConstTwo CV CP CH γ α θ j := rfl
  rw [this]
  linarith

/-- The supremum `sup_{A r ≤ s ≤ R} D(s) / s` is over a set bounded above, for `X ≤ r`. -/
theorem bddAbove_range_ballExcess_div (P : AddSubgroup F) {A X R CV γ : ℝ} (hA : 1 ≤ A)
    (hX0 : 0 < X) (hCV : 0 ≤ CV) (hγ : 0 ≤ γ) (hmono : RadiusMonotone N X R CV γ) (u : F) {r : ℝ}
    (hXr : X ≤ r) :
    BddAbove (Set.range fun s : Set.Icc (A * r) R => ballExcess N P s u / s) := by
  have hr0 : 0 < r := hX0.trans_le hXr
  have hAr : r ≤ A * r := le_mul_of_one_le_left hr0.le hA
  refine ⟨CV * (R / (A * r)) ^ γ * ballExcess N P R u / (A * r), ?_⟩
  rintro _ ⟨⟨s, hs1, hs2⟩, rfl⟩
  have hs0 : 0 < s := hr0.trans_le (hAr.trans hs1)
  have hAr0 : 0 < A * r := hr0.trans_le hAr
  have h1 := ballExcess_le_of_radiusMonotone N P hCV hmono (hXr.trans (hAr.trans hs1)) hs2 le_rfl
    hs0 u
  have hR0 : 0 < R := hs0.trans_le hs2
  have h2 : (R / s) ^ γ ≤ (R / (A * r)) ^ γ :=
    Real.rpow_le_rpow (div_nonneg hR0.le hs0.le) (div_le_div_of_nonneg_left hR0.le hAr0 hs1) hγ
  have hDR := ballExcess_nonneg N P R u
  have h3 : ballExcess N P s u ≤ CV * (R / (A * r)) ^ γ * ballExcess N P R u :=
    h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCV) hDR)
  have h4 : 0 ≤ CV * (R / (A * r)) ^ γ * ballExcess N P R u :=
    mul_nonneg (mul_nonneg hCV (Real.rpow_nonneg (div_nonneg hR0.le hAr0.le) _)) hDR
  calc ballExcess N P s u / s ≤ CV * (R / (A * r)) ^ γ * ballExcess N P R u / s :=
        div_le_div_of_nonneg_right h3 hs0.le
    _ ≤ CV * (R / (A * r)) ^ γ * ballExcess N P R u / (A * r) :=
        div_le_div_of_nonneg_left h4 hAr0 hs1

/-- The supremum `sup_{A r ≤ s ≤ R} D(s) / s` decreases in `r`. -/
theorem iSup_ballExcess_div_anti (P : AddSubgroup F) {A X R CV γ : ℝ} (hA : 1 ≤ A)
    (hX0 : 0 < X) (hCV : 0 ≤ CV) (hγ : 0 ≤ γ) (hmono : RadiusMonotone N X R CV γ) (u : F)
    {r r' : ℝ} (hXr : X ≤ r) (hrr' : r ≤ r') (hr'R : A * r' ≤ R) :
    (⨆ s : Set.Icc (A * r') R, ballExcess N P s u / s) ≤
      ⨆ s : Set.Icc (A * r) R, ballExcess N P s u / s := by
  have hA0 : 0 ≤ A := by linarith
  haveI : Nonempty (Set.Icc (A * r') R) := ⟨⟨A * r', le_rfl, hr'R⟩⟩
  exact ciSup_le fun s => le_ciSup_of_le
    (bddAbove_range_ballExcess_div N P hA hX0 hCV hγ hmono u hXr)
    ⟨s, (mul_le_mul_of_nonneg_left hrr' hA0).trans s.2.1, s.2.2⟩ le_rfl

/-- The threshold radius above which the supremum in the hypothesis of Lemma 7.2 is absorbed. -/
noncomputable def absorptionRadius (CV CP CH γ α : ℝ) : ℝ :=
  (2 * (scaleConstTwo CV CP CH γ α 1 + 1)) ^ (1 / α)

/-- The constant of the slope bound `armstrongDario_lemma_7_2_zero_slope`. -/
noncomputable def slopeConst (A CV CP CH γ : ℝ) : ℝ :=
  2 * scaleConstOne A CV CP CH γ 1 + CV * A ^ γ * A

/-- **Armstrong–Dario, proof of Lemma 7.2, Step 3 (the case `k = 0`)**, the bound
`D_0(r) / r ≤ K D_0(R) / R + K' E r ^ (-α) / r` for `r ∈ [max X r₀, R]`. -/
theorem ballExcess_div_le_of_harmonicApproximation {P₀ P₁ : AddSubgroup F} (hP : P₀ ≤ P₁)
    {Abar : ℝ → Set F} {A X R E CV CP CH γ α : ℝ} (hA : 2 ≤ A) (hX0 : 0 < X) (hE : 0 ≤ E)
    (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) (hγ : 0 ≤ γ) (hα : 0 < α)
    (hmono : RadiusMonotone N X R CV γ) (hpc : PolynomialComparison N P₀ P₁ 1 X R CP)
    (hreg : HarmonicRegularity N Abar P₁ 1 X R CH)
    (hne : ∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) (u : F)
    (happ : HarmonicApproximation N Abar P₀ A α X R E u) {r : ℝ}
    (hr : max X (absorptionRadius CV CP CH γ α) ≤ r) (hrR : r ≤ R) :
    ballExcess N P₀ r u / r ≤ slopeConst A CV CP CH γ * (ballExcess N P₀ R u / R) +
      2 * scaleConstTwo CV CP CH γ α 1 * E * r ^ (-α) / r := by
  set K₄ := scaleConstOne A CV CP CH γ 1 with hK₄
  set K₂ := scaleConstTwo CV CP CH γ α 1 with hK₂
  set K := slopeConst A CV CP CH γ with hK
  set r₀ := absorptionRadius CV CP CH γ α with hr₀
  set G := ballExcess N P₀ R u / R with hG
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hK₄0 : 0 ≤ K₄ := scaleConstOne_nonneg hA0.le hCV hCP hCH 1
  have hK₂0 : 0 ≤ K₂ := scaleConstTwo_nonneg hCV hCP hCH hα le_rfl
  have hCVA : 0 ≤ CV * A ^ γ * A := by
    have := Real.rpow_nonneg hA0.le γ
    positivity
  have hKdef : K = 2 * K₄ + CV * A ^ γ * A := by rw [hK, slopeConst, hK₄]
  -- large radii: `s ∈ (R / A, R]`
  have hlarge : ∀ s : ℝ, X ≤ s → R / A < s → s ≤ R →
      ballExcess N P₀ s u / s ≤ CV * A ^ γ * A * G := by
    intro s hXs hs hsR
    have hs0 : 0 < s := hX0.trans_le hXs
    have hR0 : 0 < R := hs0.trans_le hsR
    have h1 := ballExcess_le_of_radiusMonotone N P₀ hCV hmono hXs hsR le_rfl hs0 u
    have hRs : R / s ≤ A := by
      rw [div_lt_iff₀ hA0] at hs
      rw [div_le_iff₀ hs0]; linarith
    have h2 : (R / s) ^ γ ≤ A ^ γ := Real.rpow_le_rpow (div_nonneg hR0.le hs0.le) hRs hγ
    have hDR := ballExcess_nonneg N P₀ R u
    have h3 : ballExcess N P₀ s u ≤ CV * A ^ γ * ballExcess N P₀ R u :=
      h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCV) hDR)
    have h4 : 1 / s ≤ A / R := by
      rw [div_lt_iff₀ hA0] at hs
      rw [div_le_div_iff₀ hs0 hR0]; linarith
    calc ballExcess N P₀ s u / s = ballExcess N P₀ s u * (1 / s) := by ring
      _ ≤ CV * A ^ γ * ballExcess N P₀ R u * (A / R) :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = CV * A ^ γ * A * G := by rw [hG]; ring
  have hR0 : 0 < R := hX0.trans_le (((le_max_left _ _).trans hr).trans hrR)
  have hG0 : 0 ≤ G := div_nonneg (ballExcess_nonneg N P₀ R u) hR0.le
  have hKbig : CV * A ^ γ * A * G ≤ K * G := by
    apply mul_le_mul_of_nonneg_right _ hG0
    rw [hKdef]; linarith
  -- the claim at the scales `R / A / A ^ n`
  have hclaim : ∀ n : ℕ, ∀ s : ℝ, max X r₀ ≤ s → s ≤ R / A → R / A / A ^ n < s →
      ballExcess N P₀ s u / s ≤ K * G + 2 * K₂ * E * s ^ (-α) / s := by
    intro n
    induction n with
    | zero =>
      intro s _ hs hs'
      rw [pow_zero, div_one] at hs'
      exact absurd hs (not_le.2 hs')
    | succ n ih =>
      intro s hs hsA hs'
      have hXs : X ≤ s := (le_max_left _ _).trans hs
      have hr₀s : r₀ ≤ s := (le_max_right _ _).trans hs
      have hs0 : 0 < s := hX0.trans_le hXs
      have hAs : A * s ≤ R := by rw [le_div_iff₀ hA0] at hsA; linarith
      have hsAs : s ≤ A * s := le_mul_of_one_le_left hs0.le hA1
      have hbdd := bddAbove_range_ballExcess_div N P₀ hA1 hX0 hCV hγ hmono u hXs
      set M := ⨆ t : Set.Icc (A * s) R, ballExcess N P₀ t u / t with hM
      have hdec : ∀ t : ℝ, s ≤ t → E * t ^ (-α) / t ≤ E * s ^ (-α) / s := by
        intro t hst
        have ht0 : 0 < t := hs0.trans_le hst
        have h1 : t ^ (-α) ≤ s ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hs0 hst (by linarith)
        have h2 : E * t ^ (-α) ≤ E * s ^ (-α) := mul_le_mul_of_nonneg_left h1 hE
        calc E * t ^ (-α) / t ≤ E * s ^ (-α) / t := div_le_div_of_nonneg_right h2 ht0.le
          _ ≤ E * s ^ (-α) / s := div_le_div_of_nonneg_left
              (mul_nonneg hE (Real.rpow_nonneg hs0.le _)) hs0 hst
      have hMle : M ≤ K * G + 2 * K₂ * E * s ^ (-α) / s := by
        haveI : Nonempty (Set.Icc (A * s) R) := ⟨⟨A * s, le_rfl, hAs⟩⟩
        refine ciSup_le fun t => ?_
        obtain ⟨t, ht1, ht2⟩ := t
        have hst : s ≤ t := hsAs.trans ht1
        have hXt : X ≤ t := hXs.trans hst
        by_cases htA : t ≤ R / A
        · have hlev : R / A / A ^ n < t := by
            have : R / A / A ^ n = A * (R / A / A ^ (n + 1)) := by
              rw [pow_succ]; field_simp
            rw [this]
            exact (mul_lt_mul_of_pos_left hs' hA0).trans_le ht1
          have := ih t (hs.trans hst) htA hlev
          have h2 := mul_le_mul_of_nonneg_left (hdec t hst) (by linarith : (0 : ℝ) ≤ 2 * K₂)
          have e1 : 2 * K₂ * E * t ^ (-α) / t = 2 * K₂ * (E * t ^ (-α) / t) := by ring
          have e2 : 2 * K₂ * E * s ^ (-α) / s = 2 * K₂ * (E * s ^ (-α) / s) := by ring
          show ballExcess N P₀ t u / t ≤ _
          linarith
        · have := hlarge t hXt (not_le.1 htA) ht2
          have h3 : 0 ≤ 2 * K₂ * E * s ^ (-α) / s := by
            have := Real.rpow_nonneg hs0.le (-α)
            positivity
          show ballExcess N P₀ t u / t ≤ _
          linarith
      have hM0 : 0 ≤ M := le_ciSup_of_le hbdd ⟨A * s, le_rfl, hAs⟩
        (div_nonneg (ballExcess_nonneg N P₀ _ _) (hs0.trans_le hsAs).le)
      have hΓ : 0 ≤ M + E / s := add_nonneg hM0 (div_nonneg hE hs0.le)
      have hthrough := ballExcess_le_of_ballDist_le N hP le_rfl hA hX0 hCV hCP hCH hγ hα hΓ
        hmono hpc hreg u hXs hsA (fun ρ hρ hρ' => hne ρ (hXs.trans hρ) hρ')
        (fun ρ hρ hρ' => by
          have hρ0 : 0 < ρ := hs0.trans_le hρ
          have h1 := happ ρ (hXs.trans hρ) hρ'
          have hAρ : A * ρ ≤ R := by rw [le_div_iff₀ hA0] at hρ'; linarith
          have h2 := iSup_ballExcess_div_anti N P₀ hA1 hX0 hCV hγ hmono u hXs hρ hAρ
          have h3 : E / ρ ≤ E / s := div_le_div_of_nonneg_left hE hs0 hρ
          refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hρ0.le _))
          rw [← hM] at h2
          linarith)
      rw [← hK₄, ← hK₂, pow_one] at hthrough
      -- divide by `s`
      set t := s ^ (-α) with ht
      have ht0 : 0 ≤ t := Real.rpow_nonneg hs0.le _
      have hst : s ^ (1 - α) / s = t := by
        rw [ht, ← Real.rpow_sub_one hs0.ne']; congr 1; ring
      have hdiv : ballExcess N P₀ s u / s ≤ K₄ * G + K₂ * t * M + K₂ * t * (E / s) := by
        rw [div_le_iff₀ hs0]
        have e1 : (K₄ * G + K₂ * t * M + K₂ * t * (E / s)) * s =
            K₄ * (s / R) * ballExcess N P₀ R u + K₂ * (s ^ (1 - α) / s * s) * (M + E / s) := by
          rw [hst, hG]; ring
        rw [e1, div_mul_cancel₀ _ hs0.ne']
        exact hthrough
      -- smallness of `t` above the absorption radius
      have hr₀pos : 0 < 2 * (K₂ + 1) := by linarith
      have hsα : 2 * (K₂ + 1) ≤ s ^ α := by
        have h1 : r₀ ^ α ≤ s ^ α :=
          Real.rpow_le_rpow (Real.rpow_nonneg hr₀pos.le _) hr₀s hα.le
        have h2 : r₀ ^ α = 2 * (K₂ + 1) := by
          rw [hr₀, absorptionRadius, ← hK₂, one_div, Real.rpow_inv_rpow hr₀pos.le hα.ne']
        linarith
      have htle : t ≤ 1 / (2 * (K₂ + 1)) := by
        rw [ht, Real.rpow_neg hs0.le, one_div]
        exact inv_anti₀ hr₀pos hsα
      have hK₂t : K₂ * t ≤ 1 / 2 := by
        calc K₂ * t ≤ K₂ * (1 / (2 * (K₂ + 1))) := mul_le_mul_of_nonneg_left htle hK₂0
          _ ≤ 1 / 2 := by
            rw [mul_one_div, div_le_div_iff₀ hr₀pos (by norm_num)]; linarith
      have hMt := mul_le_mul_of_nonneg_left hMle (mul_nonneg hK₂0 ht0)
      have hKG0 : 0 ≤ K * G := mul_nonneg (by rw [hKdef]; linarith) hG0
      have hEt0 : 0 ≤ 2 * K₂ * E * t / s := by positivity
      have h1 : K₂ * t * (K * G) ≤ 1 / 2 * (K * G) := mul_le_mul_of_nonneg_right hK₂t hKG0
      have h2 : K₂ * t * (2 * K₂ * E * t / s) ≤ 1 / 2 * (2 * K₂ * E * t / s) :=
        mul_le_mul_of_nonneg_right hK₂t hEt0
      have h3 : K₂ * t * (E / s) = K₂ * E * t / s := by ring
      have h4 : K₄ * G ≤ 1 / 2 * (K * G) := by
        rw [hKdef]; nlinarith [mul_nonneg hCVA hG0]
      have e3 : K₂ * t * (K * G + 2 * K₂ * E * t / s) =
          K₂ * t * (K * G) + K₂ * t * (2 * K₂ * E * t / s) := by ring
      rw [e3] at hMt
      calc ballExcess N P₀ s u / s ≤ K₄ * G + K₂ * t * M + K₂ * t * (E / s) := hdiv
        _ ≤ 1 / 2 * (K * G) + (1 / 2 * (K * G) + 1 / 2 * (2 * K₂ * E * t / s)) +
            K₂ * E * t / s := add_le_add (add_le_add h4 (hMt.trans (add_le_add h1 h2))) h3.le
        _ = K * G + 2 * K₂ * E * s ^ (-α) / s := by rw [ht]; ring
  by_cases hrA : r ≤ R / A
  · have hr0 : 0 < r := hX0.trans_le ((le_max_left _ _).trans hr)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / A / r) (by linarith : (1 : ℝ) < A)
    have hn' : R / A / A ^ n < r := by
      rw [div_lt_iff₀ hr0] at hn
      rw [div_lt_iff₀ (pow_pos hA0 n)]; linarith
    exact hclaim n r hr hrA hn'
  · have := hlarge r ((le_max_left _ _).trans hr) (not_le.1 hrA) hrR
    have h3 : 0 ≤ 2 * K₂ * E * r ^ (-α) / r := by
      have hr0 : 0 < r := hX0.trans_le ((le_max_left _ _).trans hr)
      have := Real.rpow_nonneg hr0.le (-α)
      positivity
    linarith

theorem one_le_absorptionRadius {CV CP CH γ α : ℝ} (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH)
    (hα : 0 < α) : 1 ≤ absorptionRadius CV CP CH γ α := by
  have := scaleConstTwo_nonneg (γ := γ) hCV hCP hCH hα le_rfl
  unfold absorptionRadius
  exact Real.one_le_rpow (by linarith) (by positivity)

theorem slopeConst_nonneg {A CV CP CH γ : ℝ} (hA : 0 ≤ A) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP)
    (hCH : 0 ≤ CH) : 0 ≤ slopeConst A CV CP CH γ := by
  unfold slopeConst
  have := scaleConstOne_nonneg (γ := γ) hA hCV hCP hCH 1
  have := Real.rpow_nonneg hA γ
  positivity

/-- The supremum in the hypothesis of Lemma 7.2 is bounded by the slope bound for `k = 0`. -/
theorem iSup_ballExcess_div_le {P₀ P₁ : AddSubgroup F} (hP : P₀ ≤ P₁)
    {Abar : ℝ → Set F} {A X R E CV CP CH γ α : ℝ} (hA : 2 ≤ A) (hX0 : 0 < X) (hE : 0 ≤ E)
    (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) (hγ : 0 ≤ γ) (hα : 0 < α)
    (hmono : RadiusMonotone N X R CV γ) (hpc : PolynomialComparison N P₀ P₁ 1 X R CP)
    (hreg : HarmonicRegularity N Abar P₁ 1 X R CH)
    (hne : ∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) (u : F)
    (happ : HarmonicApproximation N Abar P₀ A α X R E u) {ρ : ℝ}
    (hρ : max X (absorptionRadius CV CP CH γ α) ≤ ρ) (hρA : A * ρ ≤ R) :
    (⨆ s : Set.Icc (A * ρ) R, ballExcess N P₀ s u / s) ≤
      slopeConst A CV CP CH γ * (ballExcess N P₀ R u / R) +
        2 * scaleConstTwo CV CP CH γ α 1 * (E / ρ) := by
  have hρ0 : 0 < ρ := hX0.trans_le ((le_max_left _ _).trans hρ)
  have hA1 : 1 ≤ A := by linarith
  have hr₀ := one_le_absorptionRadius (γ := γ) hCV hCP hCH hα
  have hρ1 : 1 ≤ ρ := hr₀.trans ((le_max_right _ _).trans hρ)
  have hK₂ := scaleConstTwo_nonneg (γ := γ) hCV hCP hCH hα le_rfl
  haveI : Nonempty (Set.Icc (A * ρ) R) := ⟨⟨A * ρ, le_rfl, hρA⟩⟩
  refine ciSup_le fun s => ?_
  obtain ⟨s, hs1, hs2⟩ := s
  have hρs : ρ ≤ s := (le_mul_of_one_le_left hρ0.le hA1).trans hs1
  have hs0 : 0 < s := hρ0.trans_le hρs
  have h1 := ballExcess_div_le_of_harmonicApproximation N hP hA hX0 hE hCV hCP hCH hγ hα hmono
    hpc hreg hne u happ (hρ.trans hρs) hs2
  have h2 : s ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hρ1.trans hρs) (by linarith)
  have h3 : E * s ^ (-α) / s ≤ E / ρ := by
    calc E * s ^ (-α) / s ≤ E * 1 / s :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hE) hs0.le
      _ = E / s := by ring
      _ ≤ E / ρ := div_le_div_of_nonneg_left hE hρ0 hρs
  have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * scaleConstTwo CV CP CH γ α 1)
  have e1 : 2 * scaleConstTwo CV CP CH γ α 1 * E * s ^ (-α) / s =
      2 * scaleConstTwo CV CP CH γ α 1 * (E * s ^ (-α) / s) := by ring
  show ballExcess N P₀ s u / s ≤ _
  linarith


/-- **Armstrong–Dario, Lemma 7.2, slope form of the case `k = 0`** (the bound
`D_0(r) / r ≤ C (D_0(R) / R + E / r ^ (1 + α))` of Step 3 of its proof), in the abstract setting of
`Rigidity.Proofs.Regularity.BallExcess`. -/
theorem armstrongDario_lemma_7_2_zero_slope {A α γ CV CP CH : ℝ} (hA : 2 ≤ A) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type u} [AddCommGroup F] (N : ℝ → AddGroupSeminorm F)
      (P₀ P₁ : AddSubgroup F) (Abar : ℝ → Set F) (R X E : ℝ) (u : F),
      P₀ ≤ P₁ → 1 ≤ X → X ≤ R / A → 0 ≤ E →
      RadiusMonotone N X R CV γ → PolynomialComparison N P₀ P₁ 1 X R CP →
      HarmonicRegularity N Abar P₁ 1 X R CH → (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation N Abar P₀ A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess N P₀ r u / r ≤ C * (ballExcess N P₀ R u / R + E / r ^ (1 + α)) := by
  set r₀ := absorptionRadius CV CP CH γ α
  set K := slopeConst A CV CP CH γ
  set K₂ := scaleConstTwo CV CP CH γ α 1
  have hK0 : 0 ≤ K := slopeConst_nonneg (by linarith) hCV hCP hCH
  have hK₂0 : 0 ≤ K₂ := scaleConstTwo_nonneg hCV hCP hCH hα le_rfl
  have hr₀ : 1 ≤ r₀ := one_le_absorptionRadius hCV hCP hCH hα
  refine ⟨r₀ + K + 2 * K₂ + 1, by linarith, ?_⟩
  intro F _ N P₀ P₁ Abar R X E u hP hX hXR hE hmono hpc hreg hne happ r hr hrR
  have hX0 : 0 < X := by linarith
  have hrX : max X r₀ ≤ r :=
    max_le (le_max_left _ _ |>.trans hr) (by linarith [le_max_right X (r₀ + K + 2 * K₂ + 1)])
  have hr0 : 0 < r := hX0.trans_le ((le_max_left _ _).trans hrX)
  have hR0 : 0 < R := by linarith
  have h1 := ballExcess_div_le_of_harmonicApproximation N hP hA hX0 hE hCV hCP hCH hγ hα hmono
    hpc hreg hne u happ hrX (by linarith)
  have hpow : r ^ (-α) / r = 1 / r ^ (1 + α) := by
    rw [Real.rpow_add hr0, Real.rpow_one, Real.rpow_neg hr0.le]
    have := Real.rpow_pos_of_pos hr0 α
    field_simp
  have e1 : 2 * K₂ * E * r ^ (-α) / r = 2 * K₂ * (E / r ^ (1 + α)) := by
    rw [mul_div_assoc, hpow]; ring
  have hG := div_nonneg (ballExcess_nonneg N P₀ R u) hR0.le
  have hEr : 0 ≤ E / r ^ (1 + α) := div_nonneg hE (Real.rpow_nonneg hr0.le _)
  rw [e1] at h1
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r₀) hG, mul_nonneg hK₂0 hG,
    mul_nonneg hK0 hEr, mul_nonneg (by linarith : (0 : ℝ) ≤ r₀) hEr]

/-- **Armstrong–Dario, Lemma 7.2, case `k = 0`**, in the abstract setting of
`Rigidity.Proofs.Regularity.BallExcess`: for `r ∈ [X ∨ C, R / 2]`,
`D_0(r) ≤ C (r / R) D_0(R) + C r ^ (1 - α) (D_0(R) / R + E / r)`. -/
theorem armstrongDario_lemma_7_2_zero {A α γ CV CP CH : ℝ} (hA : 2 ≤ A) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type u} [AddCommGroup F] (N : ℝ → AddGroupSeminorm F)
      (P₀ P₁ : AddSubgroup F) (Abar : ℝ → Set F) (R X E : ℝ) (u : F),
      P₀ ≤ P₁ → 1 ≤ X → X ≤ R / A → 0 ≤ E →
      RadiusMonotone N X R CV γ → PolynomialComparison N P₀ P₁ 1 X R CP →
      HarmonicRegularity N Abar P₁ 1 X R CH → (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation N Abar P₀ A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess N P₀ r u ≤ C * (r / R) * ballExcess N P₀ R u +
          C * r ^ (1 - α) * (ballExcess N P₀ R u / R + E / r) := by
  set r₀ := absorptionRadius CV CP CH γ α
  set K := slopeConst A CV CP CH γ
  set K₂ := scaleConstTwo CV CP CH γ α 1
  have hK0 : 0 ≤ K := slopeConst_nonneg (by linarith) hCV hCP hCH
  have hK₂0 : 0 ≤ K₂ := scaleConstTwo_nonneg hCV hCP hCH hα le_rfl
  have hr₀ : 1 ≤ r₀ := one_le_absorptionRadius hCV hCP hCH hα
  refine ⟨r₀ + K + 2 * K₂ + 1, by linarith, ?_⟩
  intro F _ N P₀ P₁ Abar R X E u hP hX hXR hE hmono hpc hreg hne happ r hr hrR
  have hX0 : 0 < X := by linarith
  have hrX : max X r₀ ≤ r :=
    max_le (le_max_left _ _ |>.trans hr) (by linarith [le_max_right X (r₀ + K + 2 * K₂ + 1)])
  have hr0 : 0 < r := hX0.trans_le ((le_max_left _ _).trans hrX)
  have hR0 : 0 < R := by linarith
  have h1 := ballExcess_div_le_of_harmonicApproximation N hP hA hX0 hE hCV hCP hCH hγ hα hmono
    hpc hreg hne u happ hrX (by linarith)
  rw [div_le_iff₀ hr0] at h1
  have e1 : (K * (ballExcess N P₀ R u / R) + 2 * K₂ * E * r ^ (-α) / r) * r =
      K * (r / R) * ballExcess N P₀ R u + 2 * K₂ * (r ^ (1 - α) * (E / r)) := by
    have : r ^ (1 - α) = r ^ (-α) * r := by
      rw [show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add_one hr0.ne']
    rw [this]; ring
  rw [e1] at h1
  have hDR := ballExcess_nonneg N P₀ R u
  have hG := div_nonneg hDR hR0.le
  have hrα := Real.rpow_nonneg hr0.le (1 - α)
  have hEr : 0 ≤ r ^ (1 - α) * (E / r) := mul_nonneg hrα (div_nonneg hE hr0.le)
  have h2 : K * (r / R) * ballExcess N P₀ R u ≤
      (r₀ + K + 2 * K₂ + 1) * (r / R) * ballExcess N P₀ R u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
      (div_nonneg hr0.le hR0.le)) hDR
  have h3 : 2 * K₂ * (r ^ (1 - α) * (E / r)) ≤
      (r₀ + K + 2 * K₂ + 1) * r ^ (1 - α) * (ballExcess N P₀ R u / R + E / r) := by
    have : 2 * K₂ * (r ^ (1 - α) * (E / r)) ≤ (r₀ + K + 2 * K₂ + 1) * (r ^ (1 - α) * (E / r)) :=
      mul_le_mul_of_nonneg_right (by linarith) hEr
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r₀ + K + 2 * K₂ + 1) (mul_nonneg hrα hG)]
  linarith

/-- **Armstrong–Dario, Lemma 7.2, case `k = 1`**, in the abstract setting of
`Rigidity.Proofs.Regularity.BallExcess`, with `Ā_2 = P₂` the quadratic `ā`-harmonic polynomials:
for `r ∈ [X ∨ C, R / 2]`, `D_1(r) ≤ C (r / R) ^ 2 D_1(R) + C r ^ (1 - α) (D_0(R) / R + E / r)`. -/
theorem armstrongDario_lemma_7_2_one {A α γ CV CP CH : ℝ} (hA : 2 ≤ A) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type u} [AddCommGroup F] (N : ℝ → AddGroupSeminorm F)
      (P₀ P₁ P₂ : AddSubgroup F) (Abar : ℝ → Set F) (R X E : ℝ) (u : F),
      P₀ ≤ P₁ → P₁ ≤ P₂ → 1 ≤ X → X ≤ R / A → 0 ≤ E →
      RadiusMonotone N X R CV γ → PolynomialComparison N P₀ P₁ 1 X R CP →
      PolynomialComparison N P₁ P₂ 2 X R CP →
      HarmonicRegularity N Abar P₁ 1 X R CH → HarmonicRegularity N Abar P₂ 2 X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation N Abar P₀ A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess N P₁ r u ≤ C * (r / R) ^ 2 * ballExcess N P₁ R u +
          C * r ^ (1 - α) * (ballExcess N P₀ R u / R + E / r) := by
  set r₀ := absorptionRadius CV CP CH γ α
  set K := slopeConst A CV CP CH γ
  set K₂ := scaleConstTwo CV CP CH γ α 1
  set K'' := K + 2 * K₂ + 1
  set S₁ := scaleConstOne A CV CP CH γ 2
  set S₂ := scaleConstTwo CV CP CH γ α 2
  have hA0 : 0 < A := by linarith
  have hK0 : 0 ≤ K := slopeConst_nonneg hA0.le hCV hCP hCH
  have hK₂0 : 0 ≤ K₂ := scaleConstTwo_nonneg hCV hCP hCH hα le_rfl
  have hr₀ : 1 ≤ r₀ := one_le_absorptionRadius hCV hCP hCH hα
  have hS₁ : 0 ≤ S₁ := scaleConstOne_nonneg hA0.le hCV hCP hCH 2
  have hS₂ : 0 ≤ S₂ := scaleConstTwo_nonneg hCV hCP hCH hα (by norm_num)
  have hVA : 0 ≤ CV * A ^ γ * A ^ 2 := by
    have := Real.rpow_nonneg hA0.le γ
    positivity
  set C := r₀ + S₁ + CV * A ^ γ * A ^ 2 + S₂ * K'' + 1 with hC
  have hK''0 : 0 ≤ K'' := by positivity
  have hSK : 0 ≤ S₂ * K'' := mul_nonneg hS₂ hK''0
  have hC1 : S₁ ≤ C := by have := mul_nonneg hS₂ hK''0; linarith
  have hC2 : CV * A ^ γ * A ^ 2 ≤ C := by have := mul_nonneg hS₂ hK''0; linarith
  have hC3 : S₂ * K'' ≤ C := by linarith
  refine ⟨C, by have := mul_nonneg hS₂ hK''0; linarith, ?_⟩
  intro F _ N P₀ P₁ P₂ Abar R X E u hP₀ hP₁ hX hXR hE hmono hpc₁ hpc₂ hreg₁ hreg₂ hne happ r
    hr hrR
  have hX0 : 0 < X := by linarith
  have hrX : max X r₀ ≤ r :=
    max_le (le_max_left _ _ |>.trans hr) (by linarith [le_max_right X C])
  have hr0 : 0 < r := hX0.trans_le ((le_max_left _ _).trans hrX)
  have hR0 : 0 < R := by linarith
  have hDR := ballExcess_nonneg N P₁ R u
  have hG := div_nonneg (ballExcess_nonneg N P₀ R u) hR0.le
  have hrα := Real.rpow_nonneg hr0.le (1 - α)
  have hrR2 : 0 ≤ (r / R) ^ 2 := sq_nonneg _
  by_cases hrA : r ≤ R / A
  · set X' := max X r₀ with hX'
    have hX'0 : 0 < X' := hX0.trans_le (le_max_left _ _)
    have hΓ : 0 ≤ K'' * (ballExcess N P₀ R u / R + E / r) :=
      mul_nonneg hK''0 (add_nonneg hG (div_nonneg hE hr0.le))
    have hthrough := ballExcess_le_of_ballDist_le N hP₁ (by norm_num : 1 ≤ 2) hA hX'0 hCV hCP
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
    have h1 : S₁ * (r / R) ^ 2 * ballExcess N P₁ R u ≤ C * (r / R) ^ 2 * ballExcess N P₁ R u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hrR2) hDR
    have h2 : S₂ * r ^ (1 - α) * (K'' * (ballExcess N P₀ R u / R + E / r)) ≤
        C * r ^ (1 - α) * (ballExcess N P₀ R u / R + E / r) := by
      have := mul_le_mul_of_nonneg_right hC3
        (mul_nonneg hrα (add_nonneg hG (div_nonneg hE hr0.le)))
      nlinarith
    linarith
  · have hrA' : R / A < r := not_le.1 hrA
    have hXr : X ≤ r := (le_max_left _ _).trans hrX
    have h1 := ballExcess_le_of_radiusMonotone N P₁ hCV hmono hXr (by linarith) le_rfl hr0 u
    have hRr : R / r ≤ A := by
      rw [div_lt_iff₀ hA0] at hrA'
      rw [div_le_iff₀ hr0]; linarith
    have h2 : (R / r) ^ γ ≤ A ^ γ := Real.rpow_le_rpow (div_nonneg hR0.le hr0.le) hRr hγ
    have h3 : 1 ≤ A ^ 2 * (r / R) ^ 2 := by
      rw [← mul_pow]
      have : 1 ≤ A * (r / R) := by
        rw [div_lt_iff₀ hA0] at hrA'
        rw [mul_div_assoc', le_div_iff₀ hR0]; linarith
      exact one_le_pow₀ this
    have h4 : ballExcess N P₁ r u ≤ CV * A ^ γ * ballExcess N P₁ R u :=
      h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCV) hDR)
    have h5 : CV * A ^ γ * ballExcess N P₁ R u ≤
        CV * A ^ γ * A ^ 2 * (r / R) ^ 2 * ballExcess N P₁ R u := by
      have hc : 0 ≤ CV * A ^ γ * ballExcess N P₁ R u :=
        mul_nonneg (mul_nonneg hCV (Real.rpow_nonneg hA0.le γ)) hDR
      have := mul_le_mul_of_nonneg_left h3 hc
      calc CV * A ^ γ * ballExcess N P₁ R u = CV * A ^ γ * ballExcess N P₁ R u * 1 := by ring
        _ ≤ CV * A ^ γ * ballExcess N P₁ R u * (A ^ 2 * (r / R) ^ 2) := this
        _ = CV * A ^ γ * A ^ 2 * (r / R) ^ 2 * ballExcess N P₁ R u := by ring
    have h6 : CV * A ^ γ * A ^ 2 * (r / R) ^ 2 * ballExcess N P₁ R u ≤
        C * (r / R) ^ 2 * ballExcess N P₁ R u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hrR2) hDR
    have h7 : 0 ≤ C * r ^ (1 - α) * (ballExcess N P₀ R u / R + E / r) := by
      have hC0 : 0 ≤ C := by linarith
      exact mul_nonneg (mul_nonneg hC0 hrα) (add_nonneg hG (div_nonneg hE hr0.le))
    linarith

end Rigidity.Proofs.Regularity

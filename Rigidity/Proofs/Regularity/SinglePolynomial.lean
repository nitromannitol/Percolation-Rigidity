import Mathlib.Analysis.SpecificLimits.Basic
import Rigidity.Proofs.Regularity.BallExcess

/-!
# One polynomial at the origin from the excess decay at every scale

Armstrong and Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(arXiv:1609.09431v2), state their large-scale regularity (Theorem 2) with one function `φ`
approximating `u` on all the balls `B_r`, `X ≤ r ≤ R / 2`, at the rate `(r / R) ^ (k + 1)`, while
the iteration of Lemma 7.2 bounds the excess `D_k(r)` at each radius separately. The passage from
the second to the first is the classical Campanato argument: take for `φ` a near-best
approximation at the smallest dyadic radius `R₁ / 2 ^ n ≥ X` and sum the differences of the
near-best approximations at the dyadic radii, using that an element of `P` grows at most like the
`k`-th power of the radius (`PolynomialGrowth`).

`exists_mem_forall_le_of_ballExcess_le`: if `D_k(ρ) ≤ B (ρ / R) ^ (k + 1)` for every
`ρ ∈ [X, R₁]`, with `B > 0`, then some `φ ∈ P` satisfies
`N_r(u - φ) ≤ C B (r / R) ^ (k + 1)` for every `r ∈ [X, R₁]`, with `C` depending only on the
constants of `RadiusMonotone` and `PolynomialGrowth` and on `k`.
-/

namespace Rigidity.Proofs.Regularity

open Finset

variable {F : Type*} [AddCommGroup F] (N : ℝ → AddGroupSeminorm F)

/-- The elements of `P` grow at most like the `k`-th power of the radius between the radii
`X ≤ ρ ≤ r ≤ R`. -/
def PolynomialGrowth (P : AddSubgroup F) (k : ℕ) (X R CG : ℝ) : Prop :=
  ∀ w ∈ P, ∀ ρ r : ℝ, X ≤ ρ → ρ ≤ r → r ≤ R → N r w ≤ CG * (r / ρ) ^ k * N ρ w

/-- The constant of `exists_mem_forall_le_of_ballExcess_le`. -/
noncomputable def singlePolynomialConst (CV CG γ : ℝ) (k : ℕ) : ℝ :=
  CV * 2 ^ γ * (2 + 2 ^ (k + 2) * CG * (CV * 2 ^ γ + 1)) * 2 ^ (k + 1)

/-- **One polynomial at the origin.** Excess decay at the rate `(ρ / R) ^ (k + 1)` at every radius
`ρ ∈ [X, R₁]` gives one `φ ∈ P` with `N_r(u - φ) ≤ C B (r / R) ^ (k + 1)` on `[X, R₁]`. -/
theorem exists_mem_forall_le_of_ballExcess_le (P : AddSubgroup F) {k : ℕ}
    {X R₁ R B CV CG γ : ℝ} (hX0 : 0 < X) (hXR₁ : X ≤ R₁) (hR : 0 < R) (hB : 0 < B)
    (hCV : 0 ≤ CV) (hCG : 0 ≤ CG) (hγ : 0 ≤ γ) (hmono : RadiusMonotone N X R₁ CV γ)
    (hgrowth : PolynomialGrowth N P k X R₁ CG) (u : F)
    (hD : ∀ ρ : ℝ, X ≤ ρ → ρ ≤ R₁ → ballExcess N P ρ u ≤ B * (ρ / R) ^ (k + 1)) :
    ∃ φ ∈ P, ∀ r : ℝ, X ≤ r → r ≤ R₁ →
      N r (u - φ) ≤ singlePolynomialConst CV CG γ k * B * (r / R) ^ (k + 1) := by
  have hR₁ : 0 < R₁ := hX0.trans_le hXR₁
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ρ = fun i => R₁ / 2 ^ i := ⟨_, rfl⟩
  have hρi : ∀ i, ρ i = R₁ * (1 / 2) ^ i := fun i => by
    rw [hρ, one_div_pow, mul_one_div]
  clear hρ
  have hρpos : ∀ i, 0 < ρ i := fun i => by rw [hρi]; positivity
  have hρadd : ∀ i j, ρ (i + j) = ρ i / 2 ^ j := fun i j => by
    rw [hρi, hρi, pow_add, one_div_pow (2 : ℝ) j]; ring
  have hρanti : ∀ i j, i ≤ j → ρ j ≤ ρ i := fun i j h => by
    rw [hρi, hρi]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) hR₁.le
  have hρ0 : ρ 0 = R₁ := by rw [hρi, pow_zero, mul_one]
  have hρR₁ : ∀ i, ρ i ≤ R₁ := fun i => hρ0 ▸ hρanti 0 i (Nat.zero_le i)
  have hbracket : ∀ x : ℝ, 0 < x → x ≤ R₁ → ∃ m : ℕ, ρ (m + 1) < x ∧ x ≤ ρ m := by
    intro x hx hxR
    obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near_of_lt_one (div_pos hx hR₁)
      ((div_le_one hR₁).2 hxR) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨m, ?_, ?_⟩
    · rw [hρi]
      rw [lt_div_iff₀ hR₁] at hm1
      linarith
    · rw [hρi]
      rw [div_le_iff₀ hR₁] at hm2
      linarith
  obtain ⟨n, hn1, hn2⟩ := hbracket X hX0 hXR₁
  have hρX : ∀ i ≤ n, X ≤ ρ i := fun i hi => hn2.trans (hρanti i n hi)
  set η := B * (X / R) ^ (k + 1) with hηdef
  have hη : 0 < η := by positivity
  choose w hwP hw using fun i => exists_lt_ballExcess_add N P hη (ρ i) u
  refine ⟨w n, hwP n, ?_⟩
  intro r hXr hrR₁
  have hr0 : 0 < r := hX0.trans_le hXr
  obtain ⟨m, hm1, hm2⟩ := hbracket r hr0 hrR₁
  have hmn : m ≤ n := by
    by_contra h
    have := hρanti (n + 1) m (by omega)
    linarith
  set c := CV * 2 ^ γ + 1 with hc
  have h2γ : (0 : ℝ) ≤ 2 ^ γ := Real.rpow_nonneg (by norm_num) γ
  have hc0 : 0 ≤ c := by positivity
  -- the near-best approximations
  have hDi : ∀ i ≤ n, N (ρ i) (u - w i) ≤ 2 * B * (ρ i / R) ^ (k + 1) := by
    intro i hi
    have h1 := (hw i).le
    have h2 := hD (ρ i) (hρX i hi) (hρR₁ i)
    have h3 : η ≤ B * (ρ i / R) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg hX0.le hR.le)
        (div_le_div_of_nonneg_right (hρX i hi) hR.le) _) hB.le
    linarith
  -- one dyadic step
  have hmono2 : ∀ i, i + 1 ≤ n → ∀ f : F, N (ρ (i + 1)) f ≤ CV * 2 ^ γ * N (ρ i) f := by
    intro i hi f
    have := hmono f (ρ (i + 1)) (ρ i) (hρX _ hi) (hρanti _ _ (Nat.le_succ i)) (hρR₁ i)
    have e : ρ i / ρ (i + 1) = 2 := by rw [hρadd i 1]; field_simp [(hρpos i).ne']
    rwa [e] at this
  have hstep : ∀ j < n - m, N (ρ m) (w (m + j) - w (m + j + 1)) ≤
      2 ^ (k + 1) * CG * c * B * (ρ m / R) ^ (k + 1) * (1 / 2) ^ j := by
    intro j hj
    have hi : m + j + 1 ≤ n := by omega
    have hmem : w (m + j) - w (m + j + 1) ∈ P := P.sub_mem (hwP _) (hwP _)
    have h1 := hgrowth _ hmem (ρ (m + j + 1)) (ρ m) (hρX _ hi) (hρanti _ _ (by omega)) (hρR₁ m)
    have e1 : ρ m / ρ (m + j + 1) = 2 ^ (j + 1) := by
      rw [show m + j + 1 = m + (j + 1) by omega, hρadd]; field_simp [(hρpos m).ne']
    rw [e1] at h1
    have h2 : N (ρ (m + j + 1)) (w (m + j) - w (m + j + 1)) ≤
        N (ρ (m + j + 1)) (u - w (m + j + 1)) + N (ρ (m + j + 1)) (u - w (m + j)) := by
      have := map_sub_le_add (N (ρ (m + j + 1))) (u - w (m + j + 1)) (u - w (m + j))
      rwa [sub_sub_sub_cancel_left] at this
    have h3 := hmono2 (m + j) hi (u - w (m + j))
    have h4 := hDi (m + j) (by omega)
    have h5 := hDi (m + j + 1) hi
    have e2 : ρ (m + j + 1) = ρ (m + j) / 2 := by rw [hρadd (m + j) 1, pow_one]
    have e3 : ρ (m + j) = ρ m / 2 ^ j := hρadd m j
    have hpowle : (ρ (m + j + 1) / R) ^ (k + 1) ≤ (ρ (m + j) / R) ^ (k + 1) :=
      pow_le_pow_left₀ (div_nonneg (hρpos _).le hR.le)
        (div_le_div_of_nonneg_right (hρanti _ _ (Nat.le_succ _)) hR.le) _
    have hsum : N (ρ (m + j + 1)) (w (m + j) - w (m + j + 1)) ≤
        2 * c * B * (ρ (m + j) / R) ^ (k + 1) := by
      have h6 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hCV h2γ)
      have h7 := mul_le_mul_of_nonneg_left hpowle (by positivity : (0 : ℝ) ≤ 2 * B)
      rw [hc]
      nlinarith
    have hfinal : CG * (2 ^ (j + 1)) ^ k * (2 * c * B * (ρ (m + j) / R) ^ (k + 1)) =
        2 ^ (k + 1) * CG * c * B * (ρ m / R) ^ (k + 1) * (1 / 2) ^ j := by
      rw [e3, div_div, mul_comm (2 ^ j) R, ← div_div, div_pow, one_div_pow]
      field_simp
      ring
    calc N (ρ m) (w (m + j) - w (m + j + 1))
        ≤ CG * (2 ^ (j + 1)) ^ k * N (ρ (m + j + 1)) (w (m + j) - w (m + j + 1)) := h1
      _ ≤ CG * (2 ^ (j + 1)) ^ k * (2 * c * B * (ρ (m + j) / R) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := hfinal
  -- summation over the dyadic radii between `ρ n` and `ρ m`
  have htel : w m - w n = ∑ j ∈ range (n - m), (w (m + j) - w (m + j + 1)) := by
    have := sum_range_sub' (fun j => w (m + j)) (n - m)
    simp only [add_zero, Nat.add_sub_cancel' hmn, ← add_assoc] at this
    exact this.symm
  have hsumle : N (ρ m) (w m - w n) ≤ 2 ^ (k + 2) * CG * c * B * (ρ m / R) ^ (k + 1) := by
    rw [htel]
    refine (le_sum_of_subadditive (N (ρ m)) (map_zero _).le (map_add_le_add _) _ _).trans ?_
    refine (sum_le_sum fun j hj => hstep j (mem_range.1 hj)).trans ?_
    rw [← mul_sum]
    have hK : 0 ≤ 2 ^ (k + 1) * CG * c * B * (ρ m / R) ^ (k + 1) := by
      have := (hρpos m).le
      positivity
    calc 2 ^ (k + 1) * CG * c * B * (ρ m / R) ^ (k + 1) * ∑ j ∈ range (n - m), (1 / 2 : ℝ) ^ j
        ≤ 2 ^ (k + 1) * CG * c * B * (ρ m / R) ^ (k + 1) * 2 :=
          mul_le_mul_of_nonneg_left (sum_geometric_two_le _) hK
      _ = 2 ^ (k + 2) * CG * c * B * (ρ m / R) ^ (k + 1) := by ring
  have hm : N (ρ m) (u - w n) ≤ (2 + 2 ^ (k + 2) * CG * c) * B * (ρ m / R) ^ (k + 1) := by
    have h1 : N (ρ m) (u - w n) ≤ N (ρ m) (u - w m) + N (ρ m) (w m - w n) := by
      have := map_add_le_add (N (ρ m)) (u - w m) (w m - w n)
      rwa [sub_add_sub_cancel] at this
    have h2 := hDi m hmn
    linarith
  -- back to the radius `r`
  have hρmr : ρ m / r ≤ 2 := by
    rw [div_le_iff₀ hr0]
    have : ρ (m + 1) = ρ m / 2 := by rw [hρadd m 1, pow_one]
    linarith
  have hr1 := hmono (u - w n) r (ρ m) hXr hm2 (hρR₁ m)
  have hr2 : (ρ m / r) ^ γ ≤ 2 ^ γ :=
    Real.rpow_le_rpow (div_nonneg (hρpos m).le hr0.le) hρmr hγ
  have hr3 : (ρ m / R) ^ (k + 1) ≤ 2 ^ (k + 1) * (r / R) ^ (k + 1) := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (div_nonneg (hρpos m).le hR.le)
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hR]
    linarith [(div_le_iff₀ hr0).1 hρmr]
  have hK0 : 0 ≤ (2 + 2 ^ (k + 2) * CG * c) * B := by positivity
  calc N r (u - w n) ≤ CV * (ρ m / r) ^ γ * N (ρ m) (u - w n) := hr1
    _ ≤ CV * 2 ^ γ * ((2 + 2 ^ (k + 2) * CG * c) * B * (2 ^ (k + 1) * (r / R) ^ (k + 1))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hr2 hCV) _ (apply_nonneg _ _)
          (mul_nonneg hCV h2γ)
        exact hm.trans (mul_le_mul_of_nonneg_left hr3 hK0)
    _ = singlePolynomialConst CV CG γ k * B * (r / R) ^ (k + 1) := by
        rw [singlePolynomialConst, hc]; ring

end Rigidity.Proofs.Regularity

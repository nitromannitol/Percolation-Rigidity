import Rigidity.Proofs.S2.InfluenceFactorialGrowth

/-!
# Growth of density influence moment roots

The factorial moment bounds obtained from finite-cluster tails have fourth-order polynomial growth
after taking the relevant moment roots.
-/

namespace Rigidity.Proofs.S2

/-- The factorial majorant for squared-influence moments has fourth-order root growth. -/
theorem influence_factorial_root_growth (a A a' A' B : ℝ)
    (ha : 0 < a) (hA : 0 < A) (ha' : 0 < a') (hA' : 0 < A') (hB : 0 < B) :
    ∃ L : ℝ, 0 < L ∧ ∀ r : ℕ, 1 ≤ r →
      ((4 : ℝ) ^ (2 * r + 1) * (((2 * (2 * r)).factorial : ℝ) / a ^ (2 * (2 * r))) * A +
        Real.sqrt ((4 : ℝ) ^ (2 * (2 * r) + 1) *
          (((2 * (2 * (2 * r))).factorial : ℝ) / a' ^ (2 * (2 * (2 * r)))) * A') *
          Real.sqrt B + 1) ^ (1 / (r : ℝ)) ≤ L * (r : ℝ) ^ 4 := by
  obtain ⟨L1, hL1, hfac1⟩ := factorial_moment_le_order_pow a A ha hA
  obtain ⟨L2, hL2, hfac2⟩ := factorial_moment_le_order_pow a' A' ha' hA'
  let L0 : ℝ := max 1 (max L1 L2)
  let L : ℝ := (8 * L0) ^ 4 * (2 + Real.sqrt B)
  have hL01 : 1 ≤ L0 := le_max_left _ _
  have hL0 : 0 < L0 := zero_lt_one.trans_le hL01
  have h1 : L1 ≤ L0 := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : L2 ≤ L0 := (le_max_right _ _).trans (le_max_right _ _)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, fun r hr => ?_⟩
  let u : ℝ := r
  let x : ℝ := 8 * L0 * u
  let Q : ℝ := (4 : ℝ) ^ (2 * r + 1) * (((2 * (2 * r)).factorial : ℝ) / a ^ (2 * (2 * r))) * A
  let T : ℝ := (4 : ℝ) ^ (2 * (2 * r) + 1) *
    (((2 * (2 * (2 * r))).factorial : ℝ) / a' ^ (2 * (2 * (2 * r)))) * A'
  let K : ℝ := Q + Real.sqrt T * Real.sqrt B + 1
  have hu1 : 1 ≤ u := by dsimp [u]; exact_mod_cast hr
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hx1 : 1 ≤ x := by dsimp [x]; nlinarith
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hQ : Q ≤ x ^ (4 * r) := by
    have hfactor := hfac1 (4 * r) (by omega)
    have hpref : (4 : ℝ) ^ (2 * r + 1) ≤ (4 : ℝ) ^ (4 * r + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hQ' : Q ≤ (L1 * ((4 * r : ℕ) : ℝ)) ^ (4 * r) := by
      dsimp only [Q]
      have hprebound := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref (by positivity : 0 ≤ ((2 * (2 * r)).factorial : ℝ) / a ^ (2 * (2 * r)))) hA.le
      rw [show 2 * (2 * r) = 4 * r by omega] at hprebound
      simpa only [show 2 * (2 * r) = 4 * r by omega] using hprebound.trans hfactor
    have hbase : L1 * ((4 * r : ℕ) : ℝ) ≤ x := by
      dsimp [x, u]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (Nat.cast_nonneg r),
        mul_nonneg hL0.le (Nat.cast_nonneg r)]
    exact hQ'.trans (pow_le_pow_left₀ (by positivity) hbase _)
  have hT : T ≤ x ^ (8 * r) := by
    have hfactor := hfac2 (8 * r) (by omega)
    have hpref : (4 : ℝ) ^ (2 * (2 * r) + 1) ≤ (4 : ℝ) ^ (8 * r + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hT' : T ≤ (L2 * ((8 * r : ℕ) : ℝ)) ^ (8 * r) := by
      dsimp only [T]
      have hprebound := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref (by positivity : 0 ≤ ((2 * (2 * (2 * r))).factorial : ℝ) / a' ^ (2 * (2 * (2 * r))))) hA'.le
      rw [show 2 * (2 * (2 * r)) = 8 * r by omega] at hprebound
      simpa only [show 2 * (2 * (2 * r)) = 8 * r by omega] using hprebound.trans hfactor
    have hbase : L2 * ((8 * r : ℕ) : ℝ) ≤ x := by
      dsimp [x, u]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (Nat.cast_nonneg r)]
    exact hT'.trans (pow_le_pow_left₀ (by positivity) hbase _)
  have hsqrt : Real.sqrt T ≤ x ^ (4 * r) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, hT.trans_eq ?_⟩
    rw [← pow_mul]
    congr 1
    omega
  have hxpow : 1 ≤ x ^ (4 * r) := one_le_pow₀ hx1
  have hcoef : 1 ≤ 2 + Real.sqrt B := by linarith [Real.sqrt_nonneg B]
  have hcoefpow : 2 + Real.sqrt B ≤ (2 + Real.sqrt B) ^ r :=
    le_self_pow₀ hcoef (by omega)
  have hKbound : K ≤ (x ^ 4 * (2 + Real.sqrt B)) ^ r := by
    calc
      K ≤ x ^ (4 * r) * (2 + Real.sqrt B) := by
        dsimp [K]
        have hmul := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg B)
        nlinarith
      _ ≤ x ^ (4 * r) * (2 + Real.sqrt B) ^ r :=
        mul_le_mul_of_nonneg_left hcoefpow (by positivity)
      _ = (x ^ 4) ^ r * (2 + Real.sqrt B) ^ r := by rw [pow_mul]
      _ = (x ^ 4 * (2 + Real.sqrt B)) ^ r := (mul_pow _ _ _).symm
  have hbase0 : 0 ≤ x ^ 4 * (2 + Real.sqrt B) := by positivity
  have ht0 : 0 ≤ 1 / u := by positivity
  have hroot := Real.rpow_le_rpow hK0 hKbound ht0
  have hrootEq : ((x ^ 4 * (2 + Real.sqrt B)) ^ r) ^ (1 / u) =
      x ^ 4 * (2 + Real.sqrt B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0]
    have hu0 : (r : ℝ) ≠ 0 := ne_of_gt hu
    simp only [u, mul_one_div, div_self hu0, Real.rpow_one]
  rw [hrootEq] at hroot
  change K ^ (1 / u) ≤ L * u ^ 4
  calc
    _ ≤ x ^ 4 * (2 + Real.sqrt B) := hroot
    _ = L * u ^ 4 := by dsimp [L, x]; ring

end Rigidity.Proofs.S2

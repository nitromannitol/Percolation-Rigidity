import Rigidity.Proofs.Regularity.PlanarFlatnessPathwise

/-!
# The decay of the pathwise bound of (5.33)

With the reach at most `S = (3^m)^{1/40}` on `□_m` and the subadditivity errors at most
`ε = (3^m)^{-γ}`, the bound of `exists_planarFlatness_le_of_reach` on the flatness error of the
coarsened maximizer of `ν(□_m, e_i)` is at most `2 · 9^{m-1} μ^{m-1}` for some `μ < 1` and all
large `m` (`exists_flatnessBound_le`): every term is at most a constant times
`m (3^m)^{2 - β}` with `β = min(1/8, γ)`, and `m ≤ C (3^m)^{β/2}`.
-/

namespace Rigidity.Proofs.Regularity

/-- `3^j ≤ 3^d (3^m)^c` when `j ≤ c m + d`. -/
theorem three_pow_le_mul_rpow {j m : ℕ} {c d : ℝ} (h : (j : ℝ) ≤ c * m + d) :
    (3 : ℝ) ^ j ≤ 3 ^ d * ((3 : ℝ) ^ m) ^ c := by
  rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_natCast (3 : ℝ) j]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- `3^d (3^m)^c ≤ 3^j` when `c m + d ≤ j`. -/
theorem mul_rpow_le_three_pow {j m : ℕ} {c d : ℝ} (h : c * m + d ≤ (j : ℝ)) :
    3 ^ d * ((3 : ℝ) ^ m) ^ c ≤ (3 : ℝ) ^ j := by
  rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_natCast (3 : ℝ) j]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- `m ≤ (3^m)^δ / (δ log 3)`. -/
theorem natCast_le_rpow_div {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (m : ℝ) ≤ ((3 : ℝ) ^ m) ^ δ / (δ * Real.log 3) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h := Real.log_le_rpow_div (x := (3 : ℝ) ^ m) (by positivity) hδ
  rw [Real.log_pow] at h
  rw [le_div_iff₀ (by positivity)]
  have : (m : ℝ) * Real.log 3 * δ ≤ ((3 : ℝ) ^ m) ^ δ := by
    rw [le_div_iff₀ hδ] at h
    exact h
  linarith

/-- The sum over `k ∈ [n₀, m)` of a bound is at most `m` times the bound. -/
theorem sum_Ico_le_mul {n₀ m : ℕ} {f : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ k ∈ Finset.Ico n₀ m, f k ≤ B) : ∑ k ∈ Finset.Ico n₀ m, f k ≤ m * B := by
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le m n₀) hB

/-- **The decay of the pathwise bound of (5.33).** -/
theorem exists_flatnessBound_le {CM KE Λ CN γ : ℝ} (hCM : 0 ≤ CM) (hKE : 0 ≤ KE) (hΛ : 0 ≤ Λ)
    (hCN : 0 ≤ CN) (hγ : 0 < γ) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      CM * (9 : ℝ) ^ ((9 * m + 9) / 10) *
          (KE * (3 * ((3 : ℝ) ^ m) ^ (1 / 40 : ℝ)) ^ 3 * (9 / 2)) +
        ∑ k ∈ Finset.Ico ((9 * m + 9) / 10) m,
          3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
            (Λ * (2 * ((3 : ℝ) ^ m) ^ (-γ) +
                4365 * ((3 : ℝ) ^ m) ^ (1 / 40 : ℝ) / (4 * 3 ^ (k / 2))) +
              CN * (16 * (((3 : ℝ) ^ m) ^ (1 / 40 : ℝ)) ^ 8 + 1) / 3 ^ k) +
        (CM * (9 : ℝ) ^ ((9 * m + 9) / 10) +
          ∑ k ∈ Finset.Ico ((9 * m + 9) / 10) m,
            CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * ((9 : ℝ) ^ k)⁻¹) ≤
      2 * 9 ^ (m - 1) * μ ^ (m - 1) := by
  set β : ℝ := min (1 / 8) γ with hβdef
  have hβ : 0 < β := lt_min (by norm_num) hγ
  have hβ8 : β ≤ 1 / 8 := min_le_left _ _
  have hβγ : β ≤ γ := min_le_right _ _
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c1 : ℝ := CM * KE * 27 * 81 / 2 with hc1
  set c2 : ℝ := CM + 3 * CM * (2185 * Λ + 17 * CN) with hc2
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (c1 + 9 * CM) + c2 / (β / 2 * Real.log 3) := ⟨_, rfl⟩
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set μ : ℝ := (3 : ℝ) ^ (-(β / 4)) with hμ
  have hμ0 : 0 < μ := by positivity
  have hμ1 : μ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h3b : 1 < (3 : ℝ) ^ (β / 4) := Real.one_lt_rpow (by norm_num) (by positivity)
  obtain ⟨m₁, hm₁⟩ := pow_unbounded_of_one_lt (9 * A / 2) h3b
  refine ⟨μ, hμ0, hμ1, m₁ + 1, fun m hm => ?_⟩
  set y : ℝ := (3 : ℝ) ^ m with hy
  have hy1 : 1 ≤ y := one_le_pow₀ (by norm_num)
  have hy0 : 0 < y := by linarith
  set n₀ := (9 * m + 9) / 10 with hn₀
  -- powers of `y`
  have rp : ∀ a b : ℝ, a ≤ b → y ^ a ≤ y ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le hy1 hab
  have radd : ∀ a b : ℝ, y ^ a * y ^ b = y ^ (a + b) := fun a b => (Real.rpow_add hy0 a b).symm
  have y2 : y ^ (2 : ℝ) = y ^ 2 := Real.rpow_natCast y 2
  have y1 : y ^ (1 : ℝ) = y := Real.rpow_one y
  set S : ℝ := y ^ (1 / 40 : ℝ) with hS
  have hS3 : S ^ 3 = y ^ (3 / 40 : ℝ) := by
    rw [hS, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  have hS8 : S ^ 8 = y ^ (1 / 5 : ℝ) := by
    rw [hS, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  -- the elementary bounds
  have F1 : (9 : ℝ) ^ n₀ ≤ 9 * y ^ (9 / 5 : ℝ) := by
    rw [show (9 : ℝ) ^ n₀ = 3 ^ (2 * n₀) by rw [pow_mul]; norm_num]
    have h : ((2 * n₀ : ℕ) : ℝ) ≤ 9 / 5 * m + 9 / 5 := by
      have : 10 * n₀ ≤ 9 * m + 9 := Nat.mul_div_le (9 * m + 9) 10
      have h' : ((10 * n₀ : ℕ) : ℝ) ≤ ((9 * m + 9 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h' ⊢
      linarith
    refine (three_pow_le_mul_rpow h).trans ?_
    have h93 : (3 : ℝ) ^ (9 / 5 : ℝ) ≤ 9 := by
      rw [show (9 : ℝ) = 3 ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    exact mul_le_mul_of_nonneg_right h93 (by positivity)
  have F2 : ∀ k ∈ Finset.Ico n₀ m, (3 : ℝ) ^ k ≤ y := fun k hk =>
    pow_le_pow_right₀ (by norm_num) (Finset.mem_Ico.1 hk).2.le
  have hk10 : ∀ k ∈ Finset.Ico n₀ m, 9 * m ≤ 10 * k := fun k hk => by
    have := (Finset.mem_Ico.1 hk).1
    omega
  have F3 : ∀ k ∈ Finset.Ico n₀ m, (3 : ℝ) ^ (-(1 / 2 : ℝ)) * y ^ (9 / 20 : ℝ) ≤ 3 ^ (k / 2) := by
    intro k hk
    refine mul_rpow_le_three_pow ?_
    have h1 := hk10 k hk
    have h2 : k ≤ 2 * (k / 2) + 1 := by omega
    have h1' : (9 * m : ℝ) ≤ 10 * k := by exact_mod_cast h1
    have h2' : (k : ℝ) ≤ 2 * ((k / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    linarith
  have F4 : ∀ k ∈ Finset.Ico n₀ m, y ^ (9 / 10 : ℝ) ≤ (3 : ℝ) ^ k := by
    intro k hk
    have h := mul_rpow_le_three_pow (j := k) (m := m) (c := 9 / 10) (d := 0) (by
      have h1' : (9 * m : ℝ) ≤ 10 * k := by exact_mod_cast hk10 k hk
      linarith)
    rwa [Real.rpow_zero, one_mul] at h
  -- the terms
  have T1 : CM * (9 : ℝ) ^ n₀ * (KE * (3 * S) ^ 3 * (9 / 2)) ≤ c1 * y ^ (2 - β) := by
    have e : CM * (9 : ℝ) ^ n₀ * (KE * (3 * S) ^ 3 * (9 / 2)) =
        CM * KE * 27 * 9 / 2 * (9 : ℝ) ^ n₀ * S ^ 3 := by ring
    rw [e, hS3]
    calc CM * KE * 27 * 9 / 2 * (9 : ℝ) ^ n₀ * y ^ (3 / 40 : ℝ)
        ≤ CM * KE * 27 * 9 / 2 * (9 * y ^ (9 / 5 : ℝ)) * y ^ (3 / 40 : ℝ) := by gcongr
      _ = c1 * (y ^ (9 / 5 : ℝ) * y ^ (3 / 40 : ℝ)) := by rw [hc1]; ring
      _ ≤ c1 * y ^ (2 - β) := by
          rw [radd]; exact mul_le_mul_of_nonneg_left (rp _ _ (by linarith)) hc10
  have T3a : CM * (9 : ℝ) ^ n₀ ≤ 9 * CM * y ^ (2 - β) := by
    calc CM * (9 : ℝ) ^ n₀ ≤ CM * (9 * y ^ (9 / 5 : ℝ)) := mul_le_mul_of_nonneg_left F1 hCM
      _ ≤ CM * (9 * y ^ (2 - β)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rp _ _ (by linarith)) (by norm_num))
            hCM
      _ = 9 * CM * y ^ (2 - β) := by ring
  have T3b : ∀ k ∈ Finset.Ico n₀ m, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * ((9 : ℝ) ^ k)⁻¹ ≤
      CM * y ^ (2 - β) := by
    intro k hk
    have e : CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * ((9 : ℝ) ^ k)⁻¹ = CM * y / 3 ^ k := by
      rw [show (9 : ℝ) ^ k = 3 ^ k * 3 ^ k by rw [← mul_pow]; norm_num]
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : y ≤ y ^ (2 - β) * 3 ^ k := by
      calc y = y ^ (1 : ℝ) := y1.symm
        _ ≤ y ^ (2 - β) := rp _ _ (by linarith)
        _ ≤ y ^ (2 - β) * 3 ^ k := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
    calc CM * y ≤ CM * (y ^ (2 - β) * 3 ^ k) := mul_le_mul_of_nonneg_left h1 hCM
      _ = CM * y ^ (2 - β) * 3 ^ k := by ring
  have T2 : ∀ k ∈ Finset.Ico n₀ m, 3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
      (Λ * (2 * y ^ (-γ) + 4365 * S / (4 * 3 ^ (k / 2))) + CN * (16 * S ^ 8 + 1) / 3 ^ k) ≤
      3 * CM * (2185 * Λ + 17 * CN) * y ^ (2 - β) := by
    intro k hk
    have hk3 := F2 k hk
    have hk0 : (0 : ℝ) < 3 ^ k := by positivity
    have hkh : (0 : ℝ) < 3 ^ (k / 2) := by positivity
    -- the three parts
    have P1 : y * 3 ^ k * (2 * y ^ (-γ)) ≤ 2 * y ^ (2 - β) := by
      calc y * 3 ^ k * (2 * y ^ (-γ)) ≤ y * y * (2 * y ^ (-γ)) := by gcongr
        _ = 2 * (y ^ (2 : ℝ) * y ^ (-γ)) := by rw [y2]; ring
        _ = 2 * y ^ (2 - γ) := by rw [radd]; ring_nf
        _ ≤ 2 * y ^ (2 - β) := mul_le_mul_of_nonneg_left (rp _ _ (by linarith)) (by norm_num)
    have P2 : y * 3 ^ k * (4365 * S / (4 * 3 ^ (k / 2))) ≤ 2183 * y ^ (2 - β) := by
      have h3 : (3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
        constructor <;> norm_num
      have h4 : (1 / 2 : ℝ) ≤ 3 ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg (by norm_num)]
        calc (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
          _ ≤ ((3 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := inv_anti₀ (by positivity) h3
      have hd : y ^ (9 / 20 : ℝ) / 2 ≤ 3 ^ (k / 2) := by
        have := F3 k hk
        have hy920 : 0 ≤ y ^ (9 / 20 : ℝ) := by positivity
        nlinarith
      have hpos : 0 < y ^ (9 / 20 : ℝ) / 2 := by positivity
      have e1 : 4365 * S / (4 * 3 ^ (k / 2)) ≤ 4365 * S / (4 * (y ^ (9 / 20 : ℝ) / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      have e2 : 4365 * S / (4 * (y ^ (9 / 20 : ℝ) / 2)) = 4365 / 2 * y ^ (-(17 / 40) : ℝ) := by
        rw [show 4365 * S / (4 * (y ^ (9 / 20 : ℝ) / 2)) = 4365 / 2 * (S / y ^ (9 / 20 : ℝ)) by
          field_simp; ring]
        rw [hS, ← Real.rpow_sub hy0]
        norm_num
      calc y * 3 ^ k * (4365 * S / (4 * 3 ^ (k / 2)))
          ≤ y * y * (4365 / 2 * y ^ (-(17 / 40) : ℝ)) := by
            rw [← e2]; gcongr
        _ = 4365 / 2 * (y ^ (2 : ℝ) * y ^ (-(17 / 40) : ℝ)) := by rw [y2]; ring
        _ = 4365 / 2 * y ^ (2 - 17 / 40 : ℝ) := by rw [radd]; ring_nf
        _ ≤ 4365 / 2 * y ^ (2 - β) :=
            mul_le_mul_of_nonneg_left (rp _ _ (by linarith)) (by norm_num)
        _ ≤ 2183 * y ^ (2 - β) := by
            have : 0 ≤ y ^ (2 - β) := by positivity
            linarith
    have P3 : y * 3 ^ k * (CN * (16 * S ^ 8 + 1) / 3 ^ k) ≤ 17 * CN * y ^ (2 - β) := by
      have key : ∀ u v w : ℝ, v ≠ 0 → u * v * (CN * w / v) = CN * (u * w) := fun u v w hv => by
        have e : u * v * (CN * w / v) = v / v * (CN * (u * w)) := by ring
        rw [e, div_self hv, one_mul]
      rw [key _ _ _ hk0.ne', hS8]
      have h1 : y * (16 * y ^ (1 / 5 : ℝ) + 1) ≤ 17 * y ^ (2 - β) := by
        have a1 : y * y ^ (1 / 5 : ℝ) ≤ y ^ (2 - β) := by
          calc y * y ^ (1 / 5 : ℝ) = y ^ (1 : ℝ) * y ^ (1 / 5 : ℝ) := by rw [y1]
            _ = y ^ (6 / 5 : ℝ) := by rw [radd]; norm_num
            _ ≤ y ^ (2 - β) := rp _ _ (by linarith)
        have a2 : y ≤ y ^ (2 - β) := by
          calc y = y ^ (1 : ℝ) := y1.symm
            _ ≤ y ^ (2 - β) := rp _ _ (by linarith)
        linarith
      calc CN * (y * (16 * y ^ (1 / 5 : ℝ) + 1)) ≤ CN * (17 * y ^ (2 - β)) :=
            mul_le_mul_of_nonneg_left h1 hCN
        _ = 17 * CN * y ^ (2 - β) := by ring
    have key : ∀ u v a b c : ℝ, 3 * CM * u * v * (Λ * (a + b) + c) =
        3 * CM * (Λ * (u * v * a) + Λ * (u * v * b) + u * v * c) := fun u v a b c => by ring
    calc _ = 3 * CM * (Λ * (y * 3 ^ k * (2 * y ^ (-γ))) +
          Λ * (y * 3 ^ k * (4365 * S / (4 * 3 ^ (k / 2)))) +
          y * 3 ^ k * (CN * (16 * S ^ 8 + 1) / 3 ^ k)) := key _ _ _ _ _
      _ ≤ 3 * CM * (Λ * (2 * y ^ (2 - β)) + Λ * (2183 * y ^ (2 - β)) +
          17 * CN * y ^ (2 - β)) :=
          mul_le_mul_of_nonneg_left (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left P1 hΛ) (mul_le_mul_of_nonneg_left P2 hΛ)) P3) (by positivity)
      _ = 3 * CM * (2185 * Λ + 17 * CN) * y ^ (2 - β) := by ring
  -- the sum
  have hyβ : 0 ≤ y ^ (2 - β) := by positivity
  have hsum2 := sum_Ico_le_mul (n₀ := n₀) (m := m) (by positivity) T2
  have hsum3 := sum_Ico_le_mul (n₀ := n₀) (m := m) (by positivity) T3b
  have hm := natCast_le_rpow_div (δ := β / 2) (by positivity) m
  have htot : CM * (9 : ℝ) ^ n₀ * (KE * (3 * S) ^ 3 * (9 / 2)) +
      ∑ k ∈ Finset.Ico n₀ m, 3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (Λ * (2 * y ^ (-γ) + 4365 * S / (4 * 3 ^ (k / 2))) + CN * (16 * S ^ 8 + 1) / 3 ^ k) +
      (CM * (9 : ℝ) ^ n₀ + ∑ k ∈ Finset.Ico n₀ m,
        CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * ((9 : ℝ) ^ k)⁻¹) ≤
      (c1 + 9 * CM) * y ^ (2 - β) + m * c2 * y ^ (2 - β) := by
    calc _ ≤ c1 * y ^ (2 - β) + m * (3 * CM * (2185 * Λ + 17 * CN) * y ^ (2 - β)) +
          (9 * CM * y ^ (2 - β) + m * (CM * y ^ (2 - β))) :=
          add_le_add (add_le_add T1 hsum2) (add_le_add T3a hsum3)
      _ = _ := by rw [hc2]; ring
  have hmy : (m : ℝ) * c2 * y ^ (2 - β) ≤ c2 / (β / 2 * Real.log 3) * y ^ (2 - β / 2) := by
    calc (m : ℝ) * c2 * y ^ (2 - β)
        ≤ y ^ (β / 2) / (β / 2 * Real.log 3) * c2 * y ^ (2 - β) := by gcongr
      _ = c2 / (β / 2 * Real.log 3) * (y ^ (β / 2) * y ^ (2 - β)) := by ring
      _ = c2 / (β / 2 * Real.log 3) * y ^ (2 - β / 2) := by rw [radd]; ring_nf
  have hA2 : (c1 + 9 * CM) * y ^ (2 - β) ≤ (c1 + 9 * CM) * y ^ (2 - β / 2) :=
    mul_le_mul_of_nonneg_left (rp _ _ (by linarith)) (by positivity)
  -- the comparison with the target
  have hyb : ((3 : ℝ) ^ (β / 4)) ^ m = y ^ (β / 4) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (3 : ℝ) m,
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hAy : A ≤ 2 / 9 * y ^ (β / 4) := by
    have h1 : ((3 : ℝ) ^ (β / 4)) ^ m₁ ≤ ((3 : ℝ) ^ (β / 4)) ^ m :=
      pow_le_pow_right₀ h3b.le (by omega)
    rw [hyb] at h1
    linarith only [h1, hm₁]
  have hμm : y ^ (-(β / 4)) ≤ μ ^ (m - 1) := by
    rw [hμ, hy, ← Real.rpow_natCast ((3 : ℝ) ^ (-(β / 4))), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h1 : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ β / 4)
    linarith only [h2]
  have h9 : (9 : ℝ) ^ (m - 1) * 9 = y ^ 2 := by
    rw [hy, ← pow_mul, ← pow_succ, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
    congr 1; omega
  have hfin : A * y ^ (2 - β / 2) ≤ 2 * 9 ^ (m - 1) * μ ^ (m - 1) := by
    have hy0' : 0 < y ^ (-(β / 4)) := by positivity
    calc A * y ^ (2 - β / 2) = A * y ^ (-(β / 4)) * y ^ (2 - β / 4) := by
          rw [mul_assoc, radd]; ring_nf
      _ ≤ 2 / 9 * y ^ (β / 4) * y ^ (-(β / 4)) * y ^ (2 - β / 4) := by gcongr
      _ = 2 / 9 * y ^ (2 - β / 4) := by
          rw [mul_assoc (2 / 9), radd, add_neg_cancel, Real.rpow_zero, mul_one]
      _ = 2 / 9 * (y ^ (2 : ℝ) * y ^ (-(β / 4))) := by rw [radd]; ring_nf
      _ = 2 * ((9 : ℝ) ^ (m - 1)) * y ^ (-(β / 4)) := by rw [y2, ← h9]; ring
      _ ≤ 2 * 9 ^ (m - 1) * μ ^ (m - 1) := by gcongr
  calc _ ≤ (c1 + 9 * CM) * y ^ (2 - β) + m * c2 * y ^ (2 - β) := htot
    _ ≤ (c1 + 9 * CM) * y ^ (2 - β / 2) + c2 / (β / 2 * Real.log 3) * y ^ (2 - β / 2) :=
        add_le_add hA2 hmy
    _ = ((c1 + 9 * CM) + c2 / (β / 2 * Real.log 3)) * y ^ (2 - β / 2) := (add_mul _ _ _).symm
    _ = A * y ^ (2 - β / 2) := by rw [hA]
    _ ≤ _ := hfin

end Rigidity.Proofs.Regularity

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponent arithmetic for the passage from smooth initial data to a point source

With `l = √s L`, `Λ = C_B t^{-d/2}` and `N = C_N s^{η - d/4 - 1/2}`, the first part of the bound of
one term is

  `√((5l)^d) (κ l √Λ / √t) N = 5^{d/2} κ √C_B C_N L^{d/2+1} s^η t^{-d/4-1/2}`

(`caseA_eq`), which is at most the same with `t^η` for `s ≤ t` (`caseA_le`); the same computation
with `N = C_E s^{-d/4}` gives `s^{1/2}` in place of `s^η` (`caseE_eq`). For `s ≥ t/(4L²)` the
contraction bound `C_N s^{η - d/4 - 1/2}` is at most `C_N (4L²)^{d/4+1/2} t^{η - d/4 - 1/2}`
(`caseB_le`).
-/

namespace Rigidity.Green

theorem sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    Real.sqrt (x ^ d) = x ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  ring_nf

theorem sqrt_eq_rpow_half {x : ℝ} : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x

/-- The first part of one term, with a general power `s^c` of the norm. -/
theorem case_eq {s t L κ CB CN c : ℝ} (hs : 0 < s) (ht : 0 < t) (hL : 0 ≤ L) (hCB : 0 ≤ CB)
    (d : ℕ) :
    Real.sqrt ((5 * (Real.sqrt s * L)) ^ d) *
        (κ * (Real.sqrt s * L) * Real.sqrt (CB * t ^ (-((d : ℝ) / 2))) / Real.sqrt t) *
        (CN * s ^ c) =
      5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN * L ^ ((d : ℝ) / 2 + 1) *
        s ^ ((d : ℝ) / 4 + 1 / 2 + c) * t ^ (-((d : ℝ) / 4) - 1 / 2) := by
  have hs' := hs.le
  have ht' := ht.le
  rw [sqrt_pow_eq_rpow (by positivity), Real.mul_rpow (by norm_num) (by positivity),
    Real.mul_rpow (Real.sqrt_nonneg _) hL, Real.sqrt_mul hCB, sqrt_eq_rpow_half (x := s),
    sqrt_eq_rpow_half (x := t), sqrt_eq_rpow_half (x := t ^ (-((d : ℝ) / 2))),
    ← Real.rpow_mul hs', ← Real.rpow_mul ht']
  rw [Real.rpow_add hs, Real.rpow_add hs, Real.rpow_add_one' hL (by positivity),
    show -((d : ℝ) / 4) - 1 / 2 = -((d : ℝ) / 2) * (1 / 2) + -(1 / 2) by ring,
    Real.rpow_add ht, Real.rpow_neg ht' (1 / 2), show (1 : ℝ) / 2 * ((d : ℝ) / 2) = d / 4 by ring]
  field_simp

/-- **Case A**: `√((5l)^d) (κ l √Λ / √t) N ≤ 5^{d/2} κ √C_B C_N L^{d/2+1} t^{η-d/4-1/2}`. -/
theorem caseA_le {s t L κ CB CN η : ℝ} (hs : 0 < s) (hst : s ≤ t) (hL : 0 ≤ L) (hCB : 0 ≤ CB)
    (hκ : 0 ≤ κ) (hCN : 0 ≤ CN) (hη : 0 ≤ η) (d : ℕ) :
    Real.sqrt ((5 * (Real.sqrt s * L)) ^ d) *
        (κ * (Real.sqrt s * L) * Real.sqrt (CB * t ^ (-((d : ℝ) / 2))) / Real.sqrt t) *
        (CN * s ^ (η - (d : ℝ) / 4 - 1 / 2)) ≤
      5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN * L ^ ((d : ℝ) / 2 + 1) *
        t ^ (η - (d : ℝ) / 4 - 1 / 2) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  rw [case_eq hs ht hL hCB d, show (d : ℝ) / 4 + 1 / 2 + (η - d / 4 - 1 / 2) = η by ring,
    show η - (d : ℝ) / 4 - 1 / 2 = η + (-((d : ℝ) / 4) - 1 / 2) by ring, Real.rpow_add ht]
  have h1 : s ^ η ≤ t ^ η := Real.rpow_le_rpow hs.le hst hη
  have h0 : 0 ≤ 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN * L ^ ((d : ℝ) / 2 + 1) := by
    positivity
  have h2 : 0 ≤ t ^ (-((d : ℝ) / 4) - 1 / 2) := by positivity
  calc _ = 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN * L ^ ((d : ℝ) / 2 + 1) * s ^ η *
        t ^ (-((d : ℝ) / 4) - 1 / 2) := rfl
    _ ≤ 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN * L ^ ((d : ℝ) / 2 + 1) * t ^ η *
        t ^ (-((d : ℝ) / 4) - 1 / 2) := by gcongr
    _ = _ := by ring

/-- **The initial error**: with `N = C_E s^{-d/4}` the first part is
`5^{d/2} κ √C_B C_E L^{d/2+1} s^{1/2} t^{-d/4-1/2}`. -/
theorem caseE_eq {s t L κ CB CE : ℝ} (hs : 0 < s) (ht : 0 < t) (hL : 0 ≤ L) (hCB : 0 ≤ CB)
    (d : ℕ) :
    Real.sqrt ((5 * (Real.sqrt s * L)) ^ d) *
        (κ * (Real.sqrt s * L) * Real.sqrt (CB * t ^ (-((d : ℝ) / 2))) / Real.sqrt t) *
        (CE * s ^ (-((d : ℝ) / 4))) =
      5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CE * L ^ ((d : ℝ) / 2 + 1) *
        s ^ ((1 : ℝ) / 2) * t ^ (-((d : ℝ) / 4) - 1 / 2) := by
  rw [case_eq hs ht hL hCB d, show (d : ℝ) / 4 + 1 / 2 + -((d : ℝ) / 4) = 1 / 2 by ring]

/-- **Case B**: for `t/(4L²) ≤ s`, `C_N s^{η-d/4-1/2} ≤ C_N (4L²)^{d/4+1/2} t^{η-d/4-1/2}`. -/
theorem caseB_le {s t L CN η : ℝ} (ht : 0 < t) (hL : 1 ≤ L) (hCN : 0 ≤ CN) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2)
    (d : ℕ) (hs : t / (4 * L ^ 2) ≤ s) :
    CN * s ^ (η - (d : ℝ) / 4 - 1 / 2) ≤
      CN * (4 * L ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2) := by
  have hL2 : 0 < 4 * L ^ 2 := by positivity
  have hq : 0 < t / (4 * L ^ 2) := div_pos ht hL2
  have hexp : η - (d : ℝ) / 4 - 1 / 2 ≤ 0 := by
    have : (0 : ℝ) ≤ d / 4 := by positivity
    linarith
  have h1 : s ^ (η - (d : ℝ) / 4 - 1 / 2) ≤ (t / (4 * L ^ 2)) ^ (η - (d : ℝ) / 4 - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hq hs hexp
  have h2 : (t / (4 * L ^ 2)) ^ (η - (d : ℝ) / 4 - 1 / 2) =
      (4 * L ^ 2) ^ (-(η - (d : ℝ) / 4 - 1 / 2)) * t ^ (η - (d : ℝ) / 4 - 1 / 2) := by
    rw [Real.div_rpow ht.le hL2.le, Real.rpow_neg hL2.le]
    ring
  have h3 : (4 * L ^ 2) ^ (-(η - (d : ℝ) / 4 - 1 / 2)) ≤ (4 * L ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · nlinarith
    · linarith
  calc CN * s ^ (η - (d : ℝ) / 4 - 1 / 2)
      ≤ CN * ((4 * L ^ 2) ^ (-(η - (d : ℝ) / 4 - 1 / 2)) * t ^ (η - (d : ℝ) / 4 - 1 / 2)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hCN
    _ ≤ CN * ((4 * L ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2)) := by
        gcongr
    _ = _ := by ring

end Rigidity.Green

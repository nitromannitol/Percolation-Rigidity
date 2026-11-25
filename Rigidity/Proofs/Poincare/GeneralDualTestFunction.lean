import Rigidity.Proofs.Poincare.DualTestFunction
import Rigidity.Proofs.Poincare.GeneralSteinBound

/-!
# The extremal test function of the `L^q` oscillation on a box of `ℤ^d`

The statements of `DualTestFunction.lean` for functions on `ℤ^d`.

For `u` on a finite set `B` with mean `m` and `v = u - m`, the function
`g = sgn(v)|v|^{q-1} - mean` on `B` (zero outside) has `Σ_B g = 0`,
`Σ_B g u = Σ_B |v|^q` (`sum_dualTest_mul`) and `Σ_B |g|^p ≤ 2 · 3^p Σ_B |v|^q` for the dual
exponent `p = q/(q-1)` (`sum_abs_dualTest_rpow_le`): the duality `‖v‖_{L^q} = sup Σ v g/‖g‖_{L^p}`
used by Dario (Appendix A, Step 3) and by Armstrong, Kuusi and Mourrat, made explicit.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- The mean of `u` on `B`. -/
noncomputable def boxMean (B : Finset (Vertex d)) (u : Vertex d → ℝ) : ℝ :=
  (∑ z ∈ B, u z) / B.card

/-- `sgn(v) |v|^{q-1} = v |v|^{q-2}`. -/
noncomputable def dualSign (q v : ℝ) : ℝ := v * |v| ^ (q - 2)

/-- The test function `sgn(v)|v|^{q-1} - mean` on `B`, zero outside. -/
noncomputable def dualTest (B : Finset (Vertex d)) (u : Vertex d → ℝ) (q : ℝ) (z : Vertex d) : ℝ :=
  if z ∈ B then dualSign q (u z - boxMean B u) -
    (∑ w ∈ B, dualSign q (u w - boxMean B u)) / B.card else 0

theorem abs_dualSign {q : ℝ} (hq : 2 ≤ q) (v : ℝ) : |dualSign q v| = |v| ^ (q - 1) := by
  rw [dualSign, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg v) _)]
  rcases (abs_nonneg v).lt_or_eq with hv | hv
  · rw [show q - 1 = 1 + (q - 2) by ring, Real.rpow_add hv, Real.rpow_one]
  · rw [← hv, zero_mul, Real.zero_rpow (by linarith)]

theorem dualSign_mul_self {q : ℝ} (hq : 2 ≤ q) (v : ℝ) : dualSign q v * v = |v| ^ q := by
  rw [dualSign]
  rcases (abs_nonneg v).lt_or_eq with hv | hv
  · have e : v * |v| ^ (q - 2) * v = |v| ^ (2 : ℝ) * |v| ^ (q - 2) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]; ring
    rw [e, ← Real.rpow_add hv]
    congr 1
    ring
  · have h0 : v = 0 := abs_eq_zero.1 hv.symm
    rw [h0, zero_mul, zero_mul, abs_zero, Real.zero_rpow (by linarith)]

theorem dualTest_eq_zero {B : Finset (Vertex d)} {u : Vertex d → ℝ} {q : ℝ} {z : Vertex d}
    (hz : z ∉ B) : dualTest B u q z = 0 := by
  rw [dualTest, if_neg hz]

theorem sum_dualTest {B : Finset (Vertex d)} (hB : B.Nonempty) (u : Vertex d → ℝ) (q : ℝ) :
    ∑ z ∈ B, dualTest B u q z = 0 := by
  have hc : (B.card : ℝ) ≠ 0 := by
    have := Finset.card_pos.2 hB
    positivity
  rw [Finset.sum_congr rfl fun z hz => by rw [dualTest, if_pos hz], Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

theorem sum_sub_boxMean {B : Finset (Vertex d)} (hB : B.Nonempty) (u : Vertex d → ℝ) :
    ∑ z ∈ B, (u z - boxMean B u) = 0 := by
  have hc : (B.card : ℝ) ≠ 0 := by
    have := Finset.card_pos.2 hB
    positivity
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, boxMean]
  field_simp
  ring

/-- **The test function realizes the `L^q` norm**: `Σ_B g u = Σ_B |u - m|^q`. -/
theorem sum_dualTest_mul {B : Finset (Vertex d)} (hB : B.Nonempty) (u : Vertex d → ℝ) {q : ℝ}
    (hq : 2 ≤ q) :
    ∑ z ∈ B, dualTest B u q z * u z = ∑ z ∈ B, |u z - boxMean B u| ^ q := by
  set m := boxMean B u with hm
  set c := (∑ w ∈ B, dualSign q (u w - m)) / B.card with hc
  have e : ∀ z ∈ B, dualTest B u q z * u z =
      dualSign q (u z - m) * (u z - m) + m * dualSign q (u z - m) - c * (u z - m) - c * m := by
    intro z hz
    rw [dualTest, if_pos hz]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_sub_boxMean hB u,
    Finset.sum_const, nsmul_eq_mul]
  simp only [dualSign_mul_self hq]
  have hcard : (B.card : ℝ) ≠ 0 := by
    have := Finset.card_pos.2 hB
    positivity
  rw [hc]
  field_simp
  ring

/-- **The `L^p` norm of the test function**: `Σ_B |g|^p ≤ 2 · 3^p Σ_B |u - m|^q`, `p = q/(q-1)`. -/
theorem sum_abs_dualTest_rpow_le {B : Finset (Vertex d)} (hB : B.Nonempty) (u : Vertex d → ℝ)
    {q : ℝ} (hq : 2 ≤ q) :
    ∑ z ∈ B, |dualTest B u q z| ^ (q / (q - 1)) ≤
      2 * 3 ^ (q / (q - 1)) * ∑ z ∈ B, |u z - boxMean B u| ^ q := by
  set p := q / (q - 1) with hp
  have hq1 : 0 < q - 1 := by linarith
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ hq1]; linarith
  have hp0 : 0 < p := by linarith
  set m := boxMean B u with hm
  set s : Vertex d → ℝ := fun z => dualSign q (u z - m) with hs
  set N : ℝ := ((B.card : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast Finset.card_pos.2 hB
  set c := (∑ w ∈ B, s w) / N with hc
  have hsp : ∀ z, |s z| ^ p = |u z - m| ^ q := by
    intro z
    rw [hs, abs_dualSign hq, ← Real.rpow_mul (abs_nonneg _), hp]
    congr 1
    field_simp
  set V := ∑ z ∈ B, |u z - m| ^ q with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun z _ => Real.rpow_nonneg (abs_nonneg _) _
  -- Jensen for the mean
  have hJ : N * |c| ^ p ≤ V := by
    have hmean := Real.rpow_arith_mean_le_arith_mean_rpow B (fun _ => 1 / N)
      (fun z => |s z|) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul, ← hN]; field_simp) (fun z _ => abs_nonneg _) hp1
    have habs : |c| ≤ ∑ z ∈ B, 1 / N * |s z| := by
      rw [hc, abs_div, abs_of_pos hN0, ← Finset.mul_sum, div_eq_inv_mul, one_div]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    have h1 : |c| ^ p ≤ (∑ z ∈ B, 1 / N * |s z|) ^ p :=
      Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
    have h2 : ∑ z ∈ B, 1 / N * |s z| ^ p = V / N := by
      rw [← Finset.mul_sum, hV]
      simp only [hsp]
      ring
    rw [h2] at hmean
    have := mul_le_mul_of_nonneg_left (h1.trans hmean) hN0.le
    rwa [mul_div_cancel₀ _ hN0.ne'] at this
  have hpt : ∀ z ∈ B, |dualTest B u q z| ^ p ≤ 3 ^ p * (|s z| ^ p + |c| ^ p) := by
    intro z hz
    rw [dualTest, if_pos hz]
    have h := rpow_add_three_le (abs_nonneg (s z)) (abs_nonneg c) (le_refl (0 : ℝ)) hp0.le
    rw [add_zero, Real.zero_rpow hp0.ne', add_zero] at h
    refine le_trans (Real.rpow_le_rpow (abs_nonneg _) ?_ hp0.le) h
    exact abs_sub _ _
  calc ∑ z ∈ B, |dualTest B u q z| ^ p ≤ ∑ z ∈ B, 3 ^ p * (|s z| ^ p + |c| ^ p) :=
        Finset.sum_le_sum hpt
    _ = 3 ^ p * (V + N * |c| ^ p) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hV]
        simp only [hsp]
        rfl
    _ ≤ 3 ^ p * (V + V) := by gcongr
    _ = 2 * 3 ^ p * V := by ring

end Rigidity.Poincare.GeneralDim

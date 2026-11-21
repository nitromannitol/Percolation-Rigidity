import Mathlib

/-!
# A discrete Hardy inequality with power-type weights

For `0 < γ ≤ 1/16` the weight `w_0 = 1`, `w_{t+1} = w_t (1 − γ/(t + 1))` behaves like `(t + 1)^{-γ}`
and satisfies exact identities: `∇w_t = −γ w_t/(t + 1)` and
`Δw_{t+1} = w_{t+2} + w_t − 2 w_{t+1} = γ (1 + γ) w_{t+1} / ((t + 2)(t + 1 − γ)) > 0`. With the
edge averages `w̄_t = (w_t + w_{t+1})/2` and `R_t = (∇w_t)²/w̄_t`, the pointwise inequality
`R_{t+1} + R_t ≤ 4γ Δw_{t+1}` and summation by parts give the one-dimensional Hardy inequality
`Σ_{t} φ_{t+1}² Δw_{t+1} ≤ 8γ Σ_t w̄_t (φ_{t+1} − φ_t)²` for `φ_0 = φ_{m+1} = 0`.

This is the one-dimensional ingredient of a weighted energy estimate near the boundary of a cube
for the discrete homogenized Dirichlet problem, which replaces the global Meyers estimate used
in Armstrong–Dario, Lemma 6.3, Step 3, to show that the energy of the homogenized solution in a
thin boundary layer is small.
-/

namespace Rigidity.Dirichlet

/-- The weight `w_0 = 1`, `w_{t+1} = w_t (1 − γ/(t + 1))`. -/
noncomputable def hardyWeight (γ : ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => hardyWeight γ t * (1 - γ / ((t : ℝ) + 1))

theorem hardyWeight_zero (γ : ℝ) : hardyWeight γ 0 = 1 := rfl

theorem hardyWeight_succ (γ : ℝ) (t : ℕ) :
    hardyWeight γ (t + 1) = hardyWeight γ t * (1 - γ / ((t : ℝ) + 1)) := rfl

theorem one_sub_div_pos {γ : ℝ} (hγ : γ < 1) (t : ℕ) : 0 < 1 - γ / ((t : ℝ) + 1) := by
  have ht : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  rw [sub_pos, div_lt_one ht]
  have : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  linarith

theorem hardyWeight_pos {γ : ℝ} (hγ : γ < 1) (t : ℕ) : 0 < hardyWeight γ t := by
  induction t with
  | zero => simp [hardyWeight_zero]
  | succ t ih => rw [hardyWeight_succ]; exact mul_pos ih (one_sub_div_pos hγ t)

theorem hardyWeight_succ_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) (t : ℕ) :
    hardyWeight γ (t + 1) ≤ hardyWeight γ t := by
  rw [hardyWeight_succ]
  have h1 : 1 - γ / ((t : ℝ) + 1) ≤ 1 := by
    have : 0 ≤ γ / ((t : ℝ) + 1) := by positivity
    linarith
  calc hardyWeight γ t * (1 - γ / ((t : ℝ) + 1)) ≤ hardyWeight γ t * 1 :=
        mul_le_mul_of_nonneg_left h1 (hardyWeight_pos hγ t).le
    _ = hardyWeight γ t := mul_one _

/-- `∇w_t = −γ w_t/(t + 1)`. -/
theorem hardyWeight_succ_sub (γ : ℝ) (t : ℕ) :
    hardyWeight γ (t + 1) - hardyWeight γ t = -(γ * hardyWeight γ t / ((t : ℝ) + 1)) := by
  rw [hardyWeight_succ]
  ring

/-- The second difference: `w_{t+2} + w_t − 2 w_{t+1} = γ (1 + γ) w_t / ((t + 1)(t + 2))`. -/
theorem hardyWeight_secondDiff (γ : ℝ) (t : ℕ) :
    hardyWeight γ (t + 2) + hardyWeight γ t - 2 * hardyWeight γ (t + 1) =
      γ * (1 + γ) * hardyWeight γ t / (((t : ℝ) + 1) * ((t : ℝ) + 2)) := by
  have h2 : hardyWeight γ (t + 2) = hardyWeight γ (t + 1) * (1 - γ / (((t + 1 : ℕ) : ℝ) + 1)) :=
    hardyWeight_succ γ (t + 1)
  rw [h2, hardyWeight_succ]
  push_cast
  have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
  have ht2 : (t : ℝ) + 1 + 1 ≠ 0 := by positivity
  have ht2' : (t : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The edge average `w̄_t = (w_t + w_{t+1})/2`. -/
noncomputable def hardyEdgeWeight (γ : ℝ) (t : ℕ) : ℝ :=
  (hardyWeight γ t + hardyWeight γ (t + 1)) / 2

theorem hardyEdgeWeight_pos {γ : ℝ} (hγ : γ < 1) (t : ℕ) : 0 < hardyEdgeWeight γ t := by
  have := hardyWeight_pos hγ t
  have := hardyWeight_pos hγ (t + 1)
  unfold hardyEdgeWeight
  positivity

/-- The ratio `R_t = (∇w_t)²/w̄_t`. -/
noncomputable def hardyRatio (γ : ℝ) (t : ℕ) : ℝ :=
  (hardyWeight γ (t + 1) - hardyWeight γ t) ^ 2 / hardyEdgeWeight γ t

/-- **The pointwise inequality** `R_{t+1} + R_t ≤ 4γ Δw_{t+1}` for `0 < γ ≤ 1/16`. -/
theorem hardyRatio_add_le {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (t : ℕ) :
    hardyRatio γ (t + 1) + hardyRatio γ t ≤
      4 * γ * (hardyWeight γ (t + 2) + hardyWeight γ t - 2 * hardyWeight γ (t + 1)) := by
  have hγ1 : γ < 1 := by linarith
  set w := hardyWeight γ t with hw
  have hw0 : 0 < w := hardyWeight_pos hγ1 t
  have hT0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h1 : hardyWeight γ (t + 1) = w * (((t : ℝ) + 1 - γ) / ((t : ℝ) + 1)) := by
    rw [hardyWeight_succ, ← hw]
    congr 1
    field_simp
  have h2 : hardyWeight γ (t + 2) =
      w * (((t : ℝ) + 1 - γ) / ((t : ℝ) + 1)) * (((t : ℝ) + 2 - γ) / ((t : ℝ) + 2)) := by
    have : hardyWeight γ (t + 2) = hardyWeight γ (t + 1) * (1 - γ / (((t + 1 : ℕ) : ℝ) + 1)) :=
      hardyWeight_succ γ (t + 1)
    rw [this, h1]
    congr 1
    push_cast
    field_simp
    ring
  have hT1 : (t : ℝ) + 1 ≠ 0 := by positivity
  have hT2 : (t : ℝ) + 2 ≠ 0 := by positivity
  have hA : (t : ℝ) + 1 - γ ≠ 0 := by linarith
  have hB : 2 * (t : ℝ) + 2 - γ ≠ 0 := by linarith
  have hC : 2 * (t : ℝ) + 4 - γ ≠ 0 := by linarith
  have hw0' : w ≠ 0 := hw0.ne'
  have eR0 : hardyRatio γ t = 2 * γ ^ 2 * w / (((t : ℝ) + 1) * (2 * (t : ℝ) + 2 - γ)) := by
    unfold hardyRatio hardyEdgeWeight
    rw [h1, ← hw]
    field_simp
    ring
  have eR1 : hardyRatio γ (t + 1) =
      2 * γ ^ 2 * w * ((t : ℝ) + 1 - γ) /
        (((t : ℝ) + 1) * ((t : ℝ) + 2) * (2 * (t : ℝ) + 4 - γ)) := by
    unfold hardyRatio hardyEdgeWeight
    rw [show t + 1 + 1 = t + 2 by ring, h1, h2]
    field_simp
    ring
  have eD : hardyWeight γ (t + 2) + hardyWeight γ t - 2 * hardyWeight γ (t + 1) =
      γ * (1 + γ) * w / (((t : ℝ) + 1) * ((t : ℝ) + 2)) := by
    rw [hardyWeight_secondDiff, ← hw]
  set K : ℝ := 2 * γ ^ 2 * w / (((t : ℝ) + 1) * ((t : ℝ) + 2)) with hK
  have hK0 : 0 < K := by positivity
  have hsplit : 2 * γ ^ 2 * w * ((t : ℝ) + 1 - γ) /
        (((t : ℝ) + 1) * ((t : ℝ) + 2) * (2 * (t : ℝ) + 4 - γ)) +
      2 * γ ^ 2 * w / (((t : ℝ) + 1) * (2 * (t : ℝ) + 2 - γ)) =
      K * (((t : ℝ) + 1 - γ) / (2 * (t : ℝ) + 4 - γ) +
        ((t : ℝ) + 2) / (2 * (t : ℝ) + 2 - γ)) := by
    rw [hK]
    field_simp
  have hrhs : 4 * γ * (γ * (1 + γ) * w / (((t : ℝ) + 1) * ((t : ℝ) + 2))) =
      K * (2 * (1 + γ)) := by
    rw [hK]
    field_simp
    ring
  have f1 : ((t : ℝ) + 1 - γ) / (2 * (t : ℝ) + 4 - γ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have f2 : ((t : ℝ) + 2) / (2 * (t : ℝ) + 2 - γ) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  rw [eR0, eR1, eD, hsplit, hrhs]
  refine mul_le_mul_of_nonneg_left ?_ hK0.le
  linarith

/-- Young's inequality in the form used for the Hardy inequality:
`a b (−g) ≤ 4γ m a² + (16γ)⁻¹ (g²/m) b²` for `γ, m > 0`. -/
theorem mul_mul_neg_le_hardy {γ m : ℝ} (hγ : 0 < γ) (hm : 0 < m) (a b g : ℝ) :
    a * b * (-g) ≤ 4 * γ * (m * a ^ 2) + 1 / (16 * γ) * (g ^ 2 / m) * b ^ 2 := by
  rw [← sub_nonneg]
  have h : 4 * γ * (m * a ^ 2) + 1 / (16 * γ) * (g ^ 2 / m) * b ^ 2 - a * b * (-g) =
      (8 * γ * m * a + g * b) ^ 2 / (16 * γ * m) := by
    field_simp
    ring
  rw [h]
  positivity

/-- **One-dimensional discrete Hardy inequality**: for `0 < γ ≤ 1/16` and `φ` with
`φ_0 = φ_{m+1} = 0`, `Σ_{t<m} φ_{t+1}² Δw_{t+1} ≤ 8γ Σ_{t≤m} w̄_t (φ_{t+1} − φ_t)²`. -/
theorem sum_sq_mul_secondDiff_le {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (m : ℕ)
    (φ : ℕ → ℝ) (h0 : φ 0 = 0) (hm : φ (m + 1) = 0) :
    ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 *
        (hardyWeight γ (t + 2) + hardyWeight γ t - 2 * hardyWeight γ (t + 1)) ≤
      8 * γ * ∑ t ∈ Finset.range (m + 1), hardyEdgeWeight γ t * (φ (t + 1) - φ t) ^ 2 := by
  have hγ1 : γ < 1 := by linarith
  set g : ℕ → ℝ := fun t => hardyWeight γ (t + 1) - hardyWeight γ t with hg
  set H := ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 *
    (hardyWeight γ (t + 2) + hardyWeight γ t - 2 * hardyWeight γ (t + 1)) with hH
  set G := ∑ t ∈ Finset.range (m + 1), hardyEdgeWeight γ t * (φ (t + 1) - φ t) ^ 2 with hG
  -- summation by parts
  have habel : H = ∑ t ∈ Finset.range (m + 1), (φ t ^ 2 - φ (t + 1) ^ 2) * g t := by
    have e1 : ∑ t ∈ Finset.range (m + 1), φ t ^ 2 * g t =
        ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 * g (t + 1) := by
      rw [Finset.sum_range_succ']
      simp [h0]
    have e2 : ∑ t ∈ Finset.range (m + 1), φ (t + 1) ^ 2 * g t =
        ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 * g t := by
      rw [Finset.sum_range_succ]
      simp [hm]
    have e3 : H = ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 * g (t + 1) -
        ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 * g t := by
      rw [hH, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [hg, show t + 1 + 1 = t + 2 from rfl]
      ring
    rw [e3, ← e1, ← e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hR0 : ∀ t, 0 ≤ hardyRatio γ t := fun t =>
    div_nonneg (sq_nonneg _) (hardyEdgeWeight_pos hγ1 t).le
  -- the pointwise Young inequality
  have hpt : ∀ t ∈ Finset.range (m + 1), (φ t ^ 2 - φ (t + 1) ^ 2) * g t ≤
      4 * γ * (hardyEdgeWeight γ t * (φ (t + 1) - φ t) ^ 2) +
        1 / (16 * γ) * hardyRatio γ t * (2 * φ t ^ 2 + 2 * φ (t + 1) ^ 2) := by
    intro t _
    have hm0 := hardyEdgeWeight_pos hγ1 t
    have hy := mul_mul_neg_le_hardy hγ0 hm0 (φ (t + 1) - φ t) (φ (t + 1) + φ t) (g t)
    have hsq : (φ (t + 1) + φ t) ^ 2 ≤ 2 * φ t ^ 2 + 2 * φ (t + 1) ^ 2 := by
      nlinarith [sq_nonneg (φ (t + 1) - φ t)]
    have hRnn : 0 ≤ 1 / (16 * γ) * hardyRatio γ t := mul_nonneg (by positivity) (hR0 t)
    calc (φ t ^ 2 - φ (t + 1) ^ 2) * g t = (φ (t + 1) - φ t) * (φ (t + 1) + φ t) * (-g t) := by
          ring
      _ ≤ 4 * γ * (hardyEdgeWeight γ t * (φ (t + 1) - φ t) ^ 2) +
            1 / (16 * γ) * hardyRatio γ t * (φ (t + 1) + φ t) ^ 2 := hy
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hRnn)
  -- regrouping the ratio terms
  have hshift : ∑ t ∈ Finset.range (m + 1), hardyRatio γ t * (φ t ^ 2 + φ (t + 1) ^ 2) =
      ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 * (hardyRatio γ (t + 1) + hardyRatio γ t) := by
    have e1 : ∑ t ∈ Finset.range (m + 1), hardyRatio γ t * φ t ^ 2 =
        ∑ t ∈ Finset.range m, hardyRatio γ (t + 1) * φ (t + 1) ^ 2 := by
      rw [Finset.sum_range_succ']
      simp [h0]
    have e2 : ∑ t ∈ Finset.range (m + 1), hardyRatio γ t * φ (t + 1) ^ 2 =
        ∑ t ∈ Finset.range m, hardyRatio γ t * φ (t + 1) ^ 2 := by
      rw [Finset.sum_range_succ]
      simp [hm]
    have e0 : ∑ t ∈ Finset.range (m + 1), hardyRatio γ t * (φ t ^ 2 + φ (t + 1) ^ 2) =
        ∑ t ∈ Finset.range (m + 1), hardyRatio γ t * φ t ^ 2 +
          ∑ t ∈ Finset.range (m + 1), hardyRatio γ t * φ (t + 1) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [e0, e1, e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hRle : ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 * (hardyRatio γ (t + 1) + hardyRatio γ t) ≤
      4 * γ * H := by
    rw [hH, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    have := mul_le_mul_of_nonneg_left (hardyRatio_add_le hγ0 hγ t) (sq_nonneg (φ (t + 1)))
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [← habel] at hsum
  have hsplit : ∑ t ∈ Finset.range (m + 1), (4 * γ * (hardyEdgeWeight γ t *
      (φ (t + 1) - φ t) ^ 2) + 1 / (16 * γ) * hardyRatio γ t *
        (2 * φ t ^ 2 + 2 * φ (t + 1) ^ 2)) =
      4 * γ * G + 1 / (8 * γ) *
        ∑ t ∈ Finset.range (m + 1), hardyRatio γ t * (φ t ^ 2 + φ (t + 1) ^ 2) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [hG, Finset.mul_sum]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
  rw [hsplit, hshift] at hsum
  have hhalf : 1 / (8 * γ) *
      ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 * (hardyRatio γ (t + 1) + hardyRatio γ t) ≤ H / 2 := by
    calc 1 / (8 * γ) *
          ∑ t ∈ Finset.range m, φ (t + 1) ^ 2 * (hardyRatio γ (t + 1) + hardyRatio γ t)
        ≤ 1 / (8 * γ) * (4 * γ * H) := mul_le_mul_of_nonneg_left hRle (by positivity)
      _ = H / 2 := by
        field_simp
        ring
  linarith

/-- Sedrakyan's inequality: `(a₁ + a₂)²/(m₁ + m₂) ≤ a₁²/m₁ + a₂²/m₂` for `m₁, m₂ > 0`. -/
theorem sq_add_div_add_le {a₁ a₂ m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    (a₁ + a₂) ^ 2 / (m₁ + m₂) ≤ a₁ ^ 2 / m₁ + a₂ ^ 2 / m₂ := by
  rw [div_add_div _ _ hm₁.ne' hm₂.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (a₁ * m₂ - a₂ * m₁), mul_pos hm₁ hm₂]

/-- **The two-sided weight**: at a point at distance `s + 1` from the left end and `r + 1` from the
right end of a segment, the weight `Ω = w(dist to the left) + w(dist to the right)` takes the
values `Ω_{-} = w_s + w_{r+2}`, `Ω_0 = w_{s+1} + w_{r+1}`, `Ω_{+} = w_{s+2} + w_r`, and its
gradient ratios on the two adjacent edges are bounded by `4γ` times its second difference. -/
theorem twoSided_ratio_add_le {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (s r : ℕ) :
    ((hardyWeight γ (s + 2) + hardyWeight γ r) -
        (hardyWeight γ (s + 1) + hardyWeight γ (r + 1))) ^ 2 /
        (((hardyWeight γ (s + 1) + hardyWeight γ (r + 1)) +
          (hardyWeight γ (s + 2) + hardyWeight γ r)) / 2) +
      ((hardyWeight γ (s + 1) + hardyWeight γ (r + 1)) -
          (hardyWeight γ s + hardyWeight γ (r + 2))) ^ 2 /
        (((hardyWeight γ s + hardyWeight γ (r + 2)) +
          (hardyWeight γ (s + 1) + hardyWeight γ (r + 1))) / 2) ≤
      4 * γ * ((hardyWeight γ (s + 2) + hardyWeight γ r) +
        (hardyWeight γ s + hardyWeight γ (r + 2)) -
          2 * (hardyWeight γ (s + 1) + hardyWeight γ (r + 1))) := by
  have hγ1 : γ < 1 := by linarith
  have hm : ∀ t, 0 < hardyEdgeWeight γ t := hardyEdgeWeight_pos hγ1
  have h1 := sq_add_div_add_le (a₁ := hardyWeight γ (s + 2) - hardyWeight γ (s + 1))
    (a₂ := hardyWeight γ r - hardyWeight γ (r + 1)) (hm (s + 1)) (hm r)
  have h2 := sq_add_div_add_le (a₁ := hardyWeight γ (s + 1) - hardyWeight γ s)
    (a₂ := hardyWeight γ (r + 1) - hardyWeight γ (r + 2)) (hm s) (hm (r + 1))
  have hL := hardyRatio_add_le hγ0 hγ s
  have hR := hardyRatio_add_le hγ0 hγ r
  unfold hardyRatio hardyEdgeWeight at hL hR
  unfold hardyEdgeWeight at h1 h2
  have e1 : ((hardyWeight γ (s + 2) + hardyWeight γ r) -
      (hardyWeight γ (s + 1) + hardyWeight γ (r + 1))) ^ 2 /
        (((hardyWeight γ (s + 1) + hardyWeight γ (r + 1)) +
          (hardyWeight γ (s + 2) + hardyWeight γ r)) / 2) =
      (hardyWeight γ (s + 2) - hardyWeight γ (s + 1) +
          (hardyWeight γ r - hardyWeight γ (r + 1))) ^ 2 /
        ((hardyWeight γ (s + 1) + hardyWeight γ (s + 1 + 1)) / 2 +
          (hardyWeight γ r + hardyWeight γ (r + 1)) / 2) := by
    congr 1 <;> ring
  have e2 : ((hardyWeight γ (s + 1) + hardyWeight γ (r + 1)) -
      (hardyWeight γ s + hardyWeight γ (r + 2))) ^ 2 /
        (((hardyWeight γ s + hardyWeight γ (r + 2)) +
          (hardyWeight γ (s + 1) + hardyWeight γ (r + 1))) / 2) =
      (hardyWeight γ (s + 1) - hardyWeight γ s +
          (hardyWeight γ (r + 1) - hardyWeight γ (r + 2))) ^ 2 /
        ((hardyWeight γ s + hardyWeight γ (s + 1)) / 2 +
          (hardyWeight γ (r + 1) + hardyWeight γ (r + 1 + 1)) / 2) := by
    congr 1 <;> ring
  rw [e1, e2]
  have hsq1 : (hardyWeight γ r - hardyWeight γ (r + 1)) ^ 2 =
      (hardyWeight γ (r + 1) - hardyWeight γ r) ^ 2 := by ring
  have hsq2 : (hardyWeight γ (r + 1) - hardyWeight γ (r + 2)) ^ 2 =
      (hardyWeight γ (r + 1 + 1) - hardyWeight γ (r + 1)) ^ 2 := by ring
  rw [hsq1] at h1
  rw [hsq2] at h2
  linarith

end Rigidity.Dirichlet

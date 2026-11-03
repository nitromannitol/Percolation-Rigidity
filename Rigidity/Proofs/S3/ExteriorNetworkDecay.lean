import LatticeProb.Prob.Percolation.LatticeClusterBall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Decay of zero-sum combinations of Green columns in dimension two

In dimension two a Green column `g r` of a cluster has logarithmic asymptotics
`g r x = -log |x - r| / (2 π κ) + Kc r + O(|x - r|^{-3/4})`. A combination `∑ b r (g r x - Kc r)`
with `∑ b r = 0` has the logarithms cancelling at leading order, since `log |x - r| - log |x|`
is `O(1 / |x|)`; hence it decays like `(1 + |x|)^{-3/4}` on the whole cluster, the finitely many
vertices of a large ball being absorbed in the constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LatticeProb.Percolation

namespace Rigidity.Proofs.S3.NetworkTrace

/-- The Euclidean distance of a lattice point to the origin is its Euclidean norm. -/
theorem dist_embedding_zero_eq_norm {d : ℕ} (x : Vertex d) :
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding (0 : Vertex d)) =
      ‖latticeEuclideanEmbedding x‖ := by
  have hz : latticeEuclideanEmbedding (0 : Vertex d) = 0 := by
    ext i
    change ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero
  rw [dist_eq_norm, hz, sub_zero]

/-- Logarithms of two numbers bounded below by `m > 0` differ by at most `|a - ρ| / m`. -/
theorem abs_log_sub_log_le {a ρ m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hρ : m ≤ ρ) :
    |Real.log a - Real.log ρ| ≤ |a - ρ| / m := by
  have ha0 : 0 < a := hm.trans_le ha
  have hρ0 : 0 < ρ := hm.trans_le hρ
  have h1 : Real.log a - Real.log ρ ≤ (a - ρ) / ρ := by
    rw [← Real.log_div ha0.ne' hρ0.ne']
    calc Real.log (a / ρ) ≤ a / ρ - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hρ0)
      _ = (a - ρ) / ρ := by field_simp
  have h2 : Real.log ρ - Real.log a ≤ (ρ - a) / a := by
    rw [← Real.log_div hρ0.ne' ha0.ne']
    calc Real.log (ρ / a) ≤ ρ / a - 1 := Real.log_le_sub_one_of_pos (div_pos hρ0 ha0)
      _ = (ρ - a) / a := by field_simp
  have h3 : (a - ρ) / ρ ≤ |a - ρ| / m :=
    calc (a - ρ) / ρ ≤ |a - ρ| / ρ := div_le_div_of_nonneg_right (le_abs_self _) hρ0.le
      _ ≤ |a - ρ| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hρ
  have h4 : (ρ - a) / a ≤ |a - ρ| / m :=
    calc (ρ - a) / a ≤ |ρ - a| / a := div_le_div_of_nonneg_right (le_abs_self _) ha0.le
      _ = |a - ρ| / a := by rw [abs_sub_comm]
      _ ≤ |a - ρ| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm ha
  rw [abs_le]
  constructor <;> linarith

/-- Pointwise comparison of the two logarithmic profiles. -/
theorem term_bound {E : Type*} [NormedAddCommGroup E] {y p : E} {κ A s : ℝ} (hκ : 0 < κ)
    (hA : 0 ≤ A) (hp : 2 * ‖p‖ ≤ ‖y‖) (hy : 1 ≤ ‖y‖)
    (hs : |s + Real.log ‖y - p‖ / (2 * Real.pi * κ)| ≤ A / ‖y - p‖ ^ (3 / 4 : ℝ)) :
    |s + Real.log ‖y‖ / (2 * Real.pi * κ)| ≤
      (2 * A + ‖p‖ / (Real.pi * κ)) / ‖y‖ ^ (3 / 4 : ℝ) := by
  have hρ0 : 0 < ‖y‖ := by linarith
  have hc : 0 < 2 * Real.pi * κ := by positivity
  have hah : ‖y‖ / 2 ≤ ‖y - p‖ := by
    have := norm_sub_norm_le y p
    have := norm_nonneg p
    linarith
  have hlog : |Real.log ‖y - p‖ - Real.log ‖y‖| ≤ 2 * ‖p‖ / ‖y‖ := by
    have h1 := abs_log_sub_log_le (ρ := ‖y‖) (m := ‖y‖ / 2) (by positivity) hah (by linarith)
    have habs : |‖y - p‖ - ‖y‖| ≤ ‖p‖ := by
      have := abs_norm_sub_norm_le (y - p) y
      rwa [sub_sub_cancel_left, norm_neg] at this
    calc _ ≤ |‖y - p‖ - ‖y‖| / (‖y‖ / 2) := h1
      _ ≤ ‖p‖ / (‖y‖ / 2) := by gcongr
      _ = 2 * ‖p‖ / ‖y‖ := by field_simp
  have hQ : 0 < ‖y‖ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hρ0 _
  have hQa : ‖y‖ ^ (3 / 4 : ℝ) / 2 ≤ ‖y - p‖ ^ (3 / 4 : ℝ) := by
    have h1 : (‖y‖ / 2) ^ (3 / 4 : ℝ) ≤ ‖y - p‖ ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hah (by norm_num)
    have h2 : (‖y‖ / 2) ^ (3 / 4 : ℝ) = ‖y‖ ^ (3 / 4 : ℝ) / (2 : ℝ) ^ (3 / 4 : ℝ) :=
      Real.div_rpow hρ0.le (by norm_num) _
    have h3 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 :=
      calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h4 : ‖y‖ ^ (3 / 4 : ℝ) / 2 ≤ ‖y‖ ^ (3 / 4 : ℝ) / (2 : ℝ) ^ (3 / 4 : ℝ) :=
      div_le_div_of_nonneg_left hQ.le (Real.rpow_pos_of_pos (by norm_num) _) h3
    linarith
  have hfirst : A / ‖y - p‖ ^ (3 / 4 : ℝ) ≤ 2 * A / ‖y‖ ^ (3 / 4 : ℝ) :=
    calc A / ‖y - p‖ ^ (3 / 4 : ℝ) ≤ A / (‖y‖ ^ (3 / 4 : ℝ) / 2) :=
          div_le_div_of_nonneg_left hA (by positivity) hQa
      _ = 2 * A / ‖y‖ ^ (3 / 4 : ℝ) := by field_simp
  have hQy : ‖y‖ ^ (3 / 4 : ℝ) ≤ ‖y‖ := Real.rpow_le_self_of_one_le hy (by norm_num)
  have hsecond : |Real.log ‖y‖ / (2 * Real.pi * κ) - Real.log ‖y - p‖ / (2 * Real.pi * κ)| ≤
      ‖p‖ / (Real.pi * κ) / ‖y‖ ^ (3 / 4 : ℝ) := by
    have h1 : Real.log ‖y‖ / (2 * Real.pi * κ) - Real.log ‖y - p‖ / (2 * Real.pi * κ) =
        -((Real.log ‖y - p‖ - Real.log ‖y‖) / (2 * Real.pi * κ)) := by ring
    rw [h1, abs_neg, abs_div, abs_of_pos hc, div_le_div_iff₀ hc hQ]
    have h2 : |Real.log ‖y - p‖ - Real.log ‖y‖| * ‖y‖ ≤ 2 * ‖p‖ := by
      calc _ ≤ 2 * ‖p‖ / ‖y‖ * ‖y‖ := by gcongr
        _ = 2 * ‖p‖ := by field_simp
    have h3 : |Real.log ‖y - p‖ - Real.log ‖y‖| * ‖y‖ ^ (3 / 4 : ℝ) ≤ 2 * ‖p‖ :=
      le_trans (mul_le_mul_of_nonneg_left hQy (abs_nonneg _)) h2
    have h4 : ‖p‖ / (Real.pi * κ) * (2 * Real.pi * κ) = 2 * ‖p‖ := by
      field_simp
    rw [h4]
    exact h3
  calc |s + Real.log ‖y‖ / (2 * Real.pi * κ)|
      = |(s + Real.log ‖y - p‖ / (2 * Real.pi * κ)) +
          (Real.log ‖y‖ / (2 * Real.pi * κ) - Real.log ‖y - p‖ / (2 * Real.pi * κ))| := by
        congr 1; ring
    _ ≤ |s + Real.log ‖y - p‖ / (2 * Real.pi * κ)| +
          |Real.log ‖y‖ / (2 * Real.pi * κ) - Real.log ‖y - p‖ / (2 * Real.pi * κ)| :=
        abs_add_le _ _
    _ ≤ 2 * A / ‖y‖ ^ (3 / 4 : ℝ) + ‖p‖ / (Real.pi * κ) / ‖y‖ ^ (3 / 4 : ℝ) :=
        add_le_add (hs.trans hfirst) hsecond
    _ = (2 * A + ‖p‖ / (Real.pi * κ)) / ‖y‖ ^ (3 / 4 : ℝ) := by rw [add_div]

/-- A zero-sum combination of shifted logarithmic profiles is `O(‖y‖^{-3/4})`. -/
theorem sum_bound {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] {y : E} {κ : ℝ}
    (hκ : 0 < κ) (p : ι → E) (b s A : ι → ℝ) (hA : ∀ i, 0 ≤ A i) (hb : ∑ i, b i = 0)
    (hp : ∀ i, 2 * ‖p i‖ ≤ ‖y‖) (hy : 1 ≤ ‖y‖)
    (hs : ∀ i, |s i + Real.log ‖y - p i‖ / (2 * Real.pi * κ)| ≤
      A i / ‖y - p i‖ ^ (3 / 4 : ℝ)) :
    |∑ i, b i * s i| ≤
      (∑ i, |b i| * (2 * A i + ‖p i‖ / (Real.pi * κ))) / ‖y‖ ^ (3 / 4 : ℝ) := by
  have h0 : ∑ i, b i * s i =
      ∑ i, b i * (s i + Real.log ‖y‖ / (2 * Real.pi * κ)) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hb, zero_mul, add_zero]
  rw [h0]
  calc |∑ i, b i * (s i + Real.log ‖y‖ / (2 * Real.pi * κ))|
      ≤ ∑ i, |b i * (s i + Real.log ‖y‖ / (2 * Real.pi * κ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |b i| * ((2 * A i + ‖p i‖ / (Real.pi * κ)) / ‖y‖ ^ (3 / 4 : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (term_bound hκ (hA i) (hp i) hy (hs i)) (abs_nonneg _)
    _ = (∑ i, |b i| * (2 * A i + ‖p i‖ / (Real.pi * κ))) / ‖y‖ ^ (3 / 4 : ℝ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by rw [mul_div_assoc]

/-- Far comparison of `‖y‖^{-3/4}` with `(1 + ‖y‖)^{-3/4}`. -/
theorem inv_rpow_le_far {ρ : ℝ} (hρ : 1 ≤ ρ) :
    1 / ρ ^ (3 / 4 : ℝ) ≤ 2 * (1 + ρ) ^ (-(3 / 4 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  have hQ : 0 < ρ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hρ0 _
  have hP : 0 < (1 + ρ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 :=
    calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h1 : (1 + ρ) ^ (3 / 4 : ℝ) ≤ 2 * ρ ^ (3 / 4 : ℝ) :=
    calc (1 + ρ) ^ (3 / 4 : ℝ) ≤ (2 * ρ) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = (2 : ℝ) ^ (3 / 4 : ℝ) * ρ ^ (3 / 4 : ℝ) := Real.mul_rpow (by norm_num) hρ0.le
      _ ≤ 2 * ρ ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_right h2 hQ.le
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, div_le_div_iff₀ hQ hP]
  linarith

/-- Near comparison of `(1 + R)^{3/4}` with `(1 + ρ)^{3/4}` for `ρ ≤ R`. -/
theorem one_le_rpow_mul_near {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : ρ ≤ R) :
    1 ≤ (1 + R) ^ (3 / 4 : ℝ) * (1 + ρ) ^ (-(3 / 4 : ℝ)) := by
  have hP : 0 < (1 + ρ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hP, one_mul]
  exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)

/-- Zero-sum combinations of Green columns with logarithmic asymptotics decay like
`(1 + |x|)^{-3/4}`. -/
theorem greenCombination_decay {ω : Configuration 2} (C : OpenComponent ω) (T : Finset C)
    (g : C → C → ℝ) (Kc : C → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hg : ∀ r ∈ T, ∃ M A : ℝ, ∀ x : C, x ≠ r →
      M ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ →
      |g r x + Real.log ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ /
          (2 * Real.pi * κ) - Kc r| ≤
        A / ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ ^ (3 / 4 : ℝ))
    (b : T → ℝ) (hb : ∑ r, b r = 0) :
    ∃ A : ℝ, ∀ x : C, |∑ r, b r * (g r x - Kc r)| ≤
      A * (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) := by
  classical
  choose! M A hMA using hg
  -- the radius beyond which the asymptotics are available for every terminal
  set R0 : ℝ := 1 + ∑ r : T, (2 * ‖latticeEuclideanEmbedding (r : C).val‖ + 2 * |M r| + 1)
    with hR0
  have hw : ∀ r : T, 2 * ‖latticeEuclideanEmbedding (r : C).val‖ + 2 * |M r| + 1 ≤ R0 - 1 := by
    intro r
    have := Finset.single_le_sum (f := fun r : T =>
      2 * ‖latticeEuclideanEmbedding (r : C).val‖ + 2 * |M r| + 1)
      (fun r _ => by positivity) (Finset.mem_univ r)
    linarith
  have hR0one : 1 ≤ R0 := by
    have : 0 ≤ ∑ r : T, (2 * ‖latticeEuclideanEmbedding (r : C).val‖ + 2 * |M r| + 1) :=
      Finset.sum_nonneg fun r _ => by positivity
    linarith
  set Cfar : ℝ := ∑ r : T, |b r| * (2 * |A r| + ‖latticeEuclideanEmbedding (r : C).val‖ /
    (Real.pi * κ)) with hCfar
  have hCfar0 : 0 ≤ Cfar := Finset.sum_nonneg fun r _ => by positivity
  set Nnear : ℝ := ∑ x ∈ componentEuclideanBall C 0 R0, |∑ r, b r * (g r x - Kc r)|
    with hNnear
  have hNnear0 : 0 ≤ Nnear := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨max (2 * Cfar) (Nnear * (1 + R0) ^ (3 / 4 : ℝ)), fun x => ?_⟩
  have hpos : 0 ≤ (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  by_cases hfar : R0 ≤ ‖latticeEuclideanEmbedding x.val‖
  · -- far vertices
    have hρ1 : 1 ≤ ‖latticeEuclideanEmbedding x.val‖ := by linarith
    have hp : ∀ r : T, 2 * ‖latticeEuclideanEmbedding (r : C).val‖ ≤
        ‖latticeEuclideanEmbedding x.val‖ := fun r => by
      have := hw r
      have := abs_nonneg (M r)
      linarith
    have hdist : ∀ r : T, ‖latticeEuclideanEmbedding x.val‖ / 2 ≤
        ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (r : C).val‖ := fun r => by
      have := norm_sub_norm_le (latticeEuclideanEmbedding x.val)
        (latticeEuclideanEmbedding (r : C).val)
      have := hp r
      linarith
    have hs : ∀ r : T, |(g r x - Kc r) + Real.log ‖latticeEuclideanEmbedding x.val -
          latticeEuclideanEmbedding (r : C).val‖ / (2 * Real.pi * κ)| ≤
        |A r| / ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (r : C).val‖ ^
          (3 / 4 : ℝ) := fun r => by
      have hne : x ≠ r := fun h => by
        have h0 : ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (r : C).val‖ = 0 := by
          rw [h, sub_self, norm_zero]
        have := hdist r
        linarith
      have hM : M r ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (r : C).val‖ := by
        have := hw r
        have := hdist r
        have := le_abs_self (M r)
        have := norm_nonneg (latticeEuclideanEmbedding (r : C).val)
        linarith
      have h1 := hMA r r.property x hne hM
      have h2 : g r x - Kc r + Real.log ‖latticeEuclideanEmbedding x.val -
          latticeEuclideanEmbedding (r : C).val‖ / (2 * Real.pi * κ) =
          g r x + Real.log ‖latticeEuclideanEmbedding x.val -
          latticeEuclideanEmbedding (r : C).val‖ / (2 * Real.pi * κ) - Kc r := by ring
      rw [h2]
      refine h1.trans ?_
      exact div_le_div_of_nonneg_right (le_abs_self _)
        (Real.rpow_pos_of_pos (lt_of_lt_of_le (by linarith) (hdist r)) _).le
    have hsum := sum_bound hκ (fun r : T => latticeEuclideanEmbedding (r : C).val) b
      (fun r : T => g r x - Kc r) (fun r : T => |A r|) (fun r => abs_nonneg _) hb hp hρ1 hs
    have hfar' := inv_rpow_le_far hρ1
    calc |∑ r, b r * (g r x - Kc r)|
        ≤ Cfar / ‖latticeEuclideanEmbedding x.val‖ ^ (3 / 4 : ℝ) := hsum
      _ = Cfar * (1 / ‖latticeEuclideanEmbedding x.val‖ ^ (3 / 4 : ℝ)) := by
          rw [mul_one_div]
      _ ≤ Cfar * (2 * (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hfar' hCfar0
      _ = (2 * Cfar) * (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) := by ring
      _ ≤ max (2 * Cfar) (Nnear * (1 + R0) ^ (3 / 4 : ℝ)) *
            (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  · -- near vertices: finitely many
    have hlt : ‖latticeEuclideanEmbedding x.val‖ < R0 := not_le.mp hfar
    have hmem : x ∈ componentEuclideanBall C 0 R0 := by
      rw [mem_componentEuclideanBall, dist_embedding_zero_eq_norm]
      exact hlt
    have hle : |∑ r, b r * (g r x - Kc r)| ≤ Nnear :=
      Finset.single_le_sum (f := fun x : C => |∑ r, b r * (g r x - Kc r)|)
        (fun _ _ => abs_nonneg _) hmem
    have hnear := one_le_rpow_mul_near (norm_nonneg (latticeEuclideanEmbedding x.val)) hlt.le
    calc |∑ r, b r * (g r x - Kc r)| ≤ Nnear := hle
      _ = Nnear * 1 := (mul_one _).symm
      _ ≤ Nnear * ((1 + R0) ^ (3 / 4 : ℝ) *
            (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hnear hNnear0
      _ = (Nnear * (1 + R0) ^ (3 / 4 : ℝ)) *
            (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) := by ring
      _ ≤ max (2 * Cfar) (Nnear * (1 + R0) ^ (3 / 4 : ℝ)) *
            (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos

end Rigidity.Proofs.S3.NetworkTrace

import Rigidity.Proofs.Cluster.PlanarOmegaSupRate

/-!
# The deterministic content of Lemma 5.3 of Armstrong and Dario, in dimension two

Lemma 5.3 of Armstrong and Dario bounds `|μ(□, q) + (1/2) q · ā⁻¹ q|` and
`|ν(□, p) - (1/2) p · ā p|` by `C |q|² sup_e ω(□, e)₊^{1/2}` plus random errors. The argument is deterministic once the random
errors are named: for a quadratic `g` (here `-μ(□, ·)`) and a function `h` (here `ν(□, ·)`) with

* the comparison `p · q ≤ g(q) + h(p) + Y |p|₁ |q|₁` (Corollary 4.6),
* the upper bound `g(r) ≤ Λ |r|²` (Lemma 4.4), and
* `h(B q) + g(q) - q · B q ≤ ρ |q|²` (the definition of `ρ` with `B = ā⁻¹`),

one gets `|g(q) - (1/2) q · B q| ≤ (4 Y S + √(8 Λ (ρ + Y S))) |q|²`, `S` an `ℓ¹` bound of `B`
(`abs_quadratic_sub_half_le`). The proof is that of Armstrong and Dario: the function
`f(x) = h(p) + g(x) - x · p`, `p = B q`, is quadratic, is bounded below by the comparison, and
equals `ω(q) ≤ ρ |q|²` at `x = q`; a gradient step from `q` of length `1/(2Λ)` shows that the
gradient `r = ∇g(q) - p` is small, and `g(q) - (1/2) q · p = (1/2) q · r`. Here the gradient step
replaces the minimizer `q₀` of Armstrong and Dario, which needs the lower bound `k(□)` of `-μ`.
-/

namespace Rigidity.Proofs.Cluster

open Rigidity.Percolation
open scoped Matrix

/-- The gradient `∇g(x)` of the quadratic `g`, in coordinates. -/
noncomputable def quadGrad (g : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![2 * g (Pi.single 0 1) * x 0 +
      (g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1) - g (Pi.single 1 1)) * x 1,
    (g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1) - g (Pi.single 1 1)) * x 0 +
      2 * g (Pi.single 1 1) * x 1]

theorem IsPlanarQuadratic.eq_coord {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (x : Fin 2 → ℝ) :
    g x = x 0 ^ 2 * g (Pi.single 0 1) + x 1 ^ 2 * g (Pi.single 1 1) +
      x 0 * x 1 * (g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1) - g (Pi.single 1 1)) := by
  have h := hg (Pi.single 0 1) (Pi.single 1 1) (x 0) (x 1)
  rwa [← eq_smul_single_add_smul_single x] at h

/-- `g(x - t r) = g(x) - t r · ∇g(x) + t² g(r)`. -/
theorem IsPlanarQuadratic.sub_smul {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (x r : Fin 2 → ℝ) (t : ℝ) :
    g (x - t • r) = g x - t * ∑ i, r i * quadGrad g x i + t ^ 2 * g r := by
  rw [IsPlanarQuadratic.eq_coord hg (x - t • r), IsPlanarQuadratic.eq_coord hg x,
    IsPlanarQuadratic.eq_coord hg r]
  simp only [quadGrad, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `x · ∇g(x) = 2 g(x)`. -/
theorem IsPlanarQuadratic.dot_quadGrad {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (x : Fin 2 → ℝ) : ∑ i, x i * quadGrad g x i = 2 * g x := by
  rw [IsPlanarQuadratic.eq_coord hg x]
  simp only [quadGrad, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `x ≤ (β + √α) Q` when `x² ≤ α Q² + β Q x` with `x, Q, α, β ≥ 0`. -/
theorem le_of_sq_le_add_mul {x Q α β : ℝ} (hQ : 0 ≤ Q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : x ^ 2 ≤ α * Q ^ 2 + β * Q * x) : x ≤ (β + Real.sqrt α) * Q := by
  by_contra hlt
  have hlt := not_le.1 hlt
  have hs := Real.sq_sqrt hα
  have hs0 := Real.sqrt_nonneg α
  have h1 : Real.sqrt α * Q ≤ x := by nlinarith [mul_nonneg hβ hQ]
  have h2 : α * Q ^ 2 ≤ Real.sqrt α * Q * x := by
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hs0 hQ)
    nlinarith
  have h3 : (β + Real.sqrt α) * Q * x < x * x := mul_lt_mul_of_pos_right hlt
    (lt_of_le_of_lt (mul_nonneg (add_nonneg hβ hs0) hQ) hlt)
  nlinarith

/-- **The deterministic content of Lemma 5.3 of Armstrong and Dario** (dimension two). -/
theorem abs_quadratic_sub_half_le {g h : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (B : Matrix (Fin 2) (Fin 2) ℝ) {S Y Λ ρ : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin 2 → ℝ, |(B *ᵥ v) 0| + |(B *ᵥ v) 1| ≤ S * (|v 0| + |v 1|))
    (hY : 0 ≤ Y) (hΛ : 0 < Λ) (hρ : 0 ≤ ρ)
    (hcomp : ∀ p q : Fin 2 → ℝ,
      ∑ i, q i * p i ≤ g q + h p + Y * ((|p 0| + |p 1|) * (|q 0| + |q 1|)))
    (hup : ∀ r : Fin 2 → ℝ, g r ≤ Λ * (r 0 ^ 2 + r 1 ^ 2))
    (hω : ∀ q : Fin 2 → ℝ, h (B *ᵥ q) + g q - ∑ i, q i * (B *ᵥ q) i ≤ ρ * (q 0 ^ 2 + q 1 ^ 2))
    (q : Fin 2 → ℝ) :
    |g q - 1 / 2 * ∑ i, q i * (B *ᵥ q) i| ≤
      (4 * Y * S + Real.sqrt (8 * Λ * (ρ + Y * S))) * (q 0 ^ 2 + q 1 ^ 2) := by
  set p := B *ᵥ q with hp
  set r : Fin 2 → ℝ := quadGrad g q - p with hr
  set t : ℝ := 1 / (2 * Λ) with ht
  have ht0 : 0 < t := by positivity
  set Q := |q 0| + |q 1| with hQ
  set P := |p 0| + |p 1| with hP
  set R := |r 0| + |r 1| with hR
  have hQ0 : 0 ≤ Q := by positivity
  have hR0 : 0 ≤ R := by positivity
  have hPQ : P ≤ S * Q := hS q
  -- the gradient step
  have hstep : g (q - t • r) = g q - t * ∑ i, r i * quadGrad g q i + t ^ 2 * g r :=
    IsPlanarQuadratic.sub_smul hg q r t
  have hdot : ∑ i, (q - t • r) i * p i = ∑ i, q i * p i - t * ∑ i, r i * p i := by
    simp only [Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hrr : ∑ i, r i * quadGrad g q i - ∑ i, r i * p i = r 0 ^ 2 + r 1 ^ 2 := by
    simp only [hr, Fin.sum_univ_two, Pi.sub_apply]
    ring
  have hc := hcomp p (q - t • r)
  rw [hdot, hstep] at hc
  have hgr := hup r
  have hωq := hω q
  rw [← hp] at hωq
  -- the ℓ¹ norm of `q - t r`
  have hqr : |(q - t • r) 0| + |(q - t • r) 1| ≤ Q + t * R := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have a := abs_sub (q 0) (t * r 0)
    have b := abs_sub (q 1) (t * r 1)
    rw [abs_mul, abs_of_pos ht0] at a b
    rw [hQ, hR]
    linarith
  have hYP : 0 ≤ Y * P := mul_nonneg hY (by positivity)
  have hrr_t : t * ∑ i, r i * quadGrad g q i - t * ∑ i, r i * p i = t * (r 0 ^ 2 + r 1 ^ 2) := by
    rw [← hrr]
    ring
  have hc' : t * (r 0 ^ 2 + r 1 ^ 2) - t ^ 2 * (Λ * (r 0 ^ 2 + r 1 ^ 2)) ≤
      ρ * (q 0 ^ 2 + q 1 ^ 2) + Y * P * (Q + t * R) := by
    have a := mul_le_mul_of_nonneg_left hqr hYP
    have b := mul_le_mul_of_nonneg_left hgr (sq_nonneg t)
    linarith
  have htΛ : t * Λ = 1 / 2 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]
    ring
  have hrsq : R ^ 2 ≤ 2 * (r 0 ^ 2 + r 1 ^ 2) := abs_add_abs_sq_le r
  have hqsq : q 0 ^ 2 + q 1 ^ 2 ≤ Q ^ 2 := by
    rw [hQ]
    nlinarith [sq_abs (q 0), sq_abs (q 1), abs_nonneg (q 0), abs_nonneg (q 1)]
  -- `R² ≤ 8 Λ (ρ + Y S) Q² + 4 Y S Q R`
  have hmain : R ^ 2 ≤ 8 * Λ * (ρ + Y * S) * Q ^ 2 + 4 * Y * S * Q * R := by
    have e1 : t * (r 0 ^ 2 + r 1 ^ 2) - t ^ 2 * (Λ * (r 0 ^ 2 + r 1 ^ 2)) =
        t / 2 * (r 0 ^ 2 + r 1 ^ 2) := by
      have : t ^ 2 * (Λ * (r 0 ^ 2 + r 1 ^ 2)) = t * (t * Λ) * (r 0 ^ 2 + r 1 ^ 2) := by ring
      rw [this, htΛ]
      ring
    rw [e1] at hc'
    have hYPQ : Y * P ≤ Y * (S * Q) := mul_le_mul_of_nonneg_left hPQ hY
    have k1 : t / 2 * (R ^ 2 / 2) ≤ ρ * Q ^ 2 + Y * (S * Q) * (Q + t * R) := by
      have a : t / 2 * (R ^ 2 / 2) ≤ t / 2 * (r 0 ^ 2 + r 1 ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have b : ρ * (q 0 ^ 2 + q 1 ^ 2) ≤ ρ * Q ^ 2 := mul_le_mul_of_nonneg_left hqsq hρ
      have c : Y * P * (Q + t * R) ≤ Y * (S * Q) * (Q + t * R) :=
        mul_le_mul_of_nonneg_right hYPQ (by positivity)
      linarith
    have k2 : R ^ 2 ≤ 4 / t * (ρ * Q ^ 2 + Y * (S * Q) * (Q + t * R)) := by
      have e : R ^ 2 = 4 / t * (t / 2 * (R ^ 2 / 2)) := by
        rw [show 4 / t * (t / 2 * (R ^ 2 / 2)) = t / t * R ^ 2 by ring, div_self ht0.ne',
          one_mul]
      rw [e]
      exact mul_le_mul_of_nonneg_left k1 (by positivity)
    have h4 : 4 / t = 8 * Λ := by
      rw [div_eq_iff ht0.ne']
      linarith
    rw [h4] at k2
    have e3 : 8 * Λ * t = 4 := by linarith
    calc R ^ 2 ≤ 8 * Λ * (ρ * Q ^ 2 + Y * (S * Q) * (Q + t * R)) := k2
      _ = 8 * Λ * (ρ + Y * S) * Q ^ 2 + (8 * Λ * t) * Y * S * Q * R := by ring
      _ = 8 * Λ * (ρ + Y * S) * Q ^ 2 + 4 * Y * S * Q * R := by rw [e3]
  have hRle : R ≤ (4 * Y * S + Real.sqrt (8 * Λ * (ρ + Y * S))) * Q :=
    le_of_sq_le_add_mul hQ0 (by positivity) (by positivity) hmain
  -- `g(q) - (1/2) q · p = (1/2) q · r`
  have hid : g q - 1 / 2 * ∑ i, q i * p i = 1 / 2 * ∑ i, q i * r i := by
    have := IsPlanarQuadratic.dot_quadGrad hg q
    simp only [hr, Fin.sum_univ_two, Pi.sub_apply] at this ⊢
    linarith
  rw [hid]
  have hqr' : |∑ i, q i * r i| ≤ Q * R := by
    simp only [Fin.sum_univ_two]
    have a := abs_add_le (q 0 * r 0) (q 1 * r 1)
    rw [abs_mul, abs_mul] at a
    rw [hQ, hR]
    have b1 := mul_nonneg (abs_nonneg (q 0)) (abs_nonneg (r 1))
    have b2 := mul_nonneg (abs_nonneg (q 1)) (abs_nonneg (r 0))
    linarith
  have hK0 : 0 ≤ 4 * Y * S + Real.sqrt (8 * Λ * (ρ + Y * S)) := by positivity
  have hQ2 : Q ^ 2 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) := abs_add_abs_sq_le q
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc 1 / 2 * |∑ i, q i * r i| ≤ 1 / 2 * (Q * R) := by linarith
    _ ≤ 1 / 2 * (Q * ((4 * Y * S + Real.sqrt (8 * Λ * (ρ + Y * S))) * Q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRle hQ0) (by norm_num)
    _ = 1 / 2 * (4 * Y * S + Real.sqrt (8 * Λ * (ρ + Y * S))) * Q ^ 2 := by ring
    _ ≤ (4 * Y * S + Real.sqrt (8 * Λ * (ρ + Y * S))) * (q 0 ^ 2 + q 1 ^ 2) := by
        have := mul_le_mul_of_nonneg_left hQ2 hK0
        linarith

end Rigidity.Proofs.Cluster

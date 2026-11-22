import Rigidity.Proofs.Cluster.PlanarRhoLocal

/-!
# Lemma 5.3 of Armstrong and Dario in dimension two

Lemma 5.3 of Armstrong and Dario bounds `|μ(□, q) + (1/2) q · ā⁻¹ q|` and
`|ν(□, p) - (1/2) p · ā p|` by `C |q|² sup_e ω(□, e)₊^{1/2}` plus random errors. The argument is
deterministic once the random errors are named: for a quadratic `g` (here `-μ(□, ·)`) and a
function `h` (here `ν(□, ·)`) with

* the comparison `p · q ≤ g(q) + h(p) + Y |p|₁ |q|₁` (Corollary 4.6),
* the upper bound `g(r) ≤ Λ |r|²` (Lemma 4.4), and
* `h(B q) + g(q) - q · B q ≤ ρ |q|²` (the definition of `ρ` with `B = ā⁻¹`),

one gets `|g(q) - (1/2) q · B q| ≤ (4 Y S + √(8 Λ (ρ + Y S))) |q|²`, `S` an `ℓ¹` bound of `B`
(`abs_quadratic_sub_half_le`). The proof is that of Armstrong and Dario: the function
`f(x) = h(p) + g(x) - x · p`, `p = B q`, is quadratic, is bounded below by the comparison, and
equals `ω(q) ≤ ρ |q|²` at `x = q`; a gradient step from `q` of length `1/(2Λ)` shows that the
gradient `r = ∇g(q) - p` is small, and `g(q) - (1/2) q · p = (1/2) q · r`. Here the gradient step
replaces the minimizer `q₀` of Armstrong and Dario, which needs the lower bound `k(□)` of `-μ`.

For the planar quantities on a resolved cube (`planar_minimalset`), `Y = Y(U)` is the error of the
comparison (`planarComparisonError`), `Λ = Λ(U) + 1` with `Λ(U)` the bound of `-μ(U, ·)` by its
values at `e₀`, `e₁`, `e₀ + e₁` (`planarMuBound`), and `ρ = ρ(U)`. Armstrong and Dario write the
right side as `C sup_e ω(□, e)₊^{1/2}` plus `O_s` errors; here the factor `√(Λ(U) + 1)` of
`ρ^{1/2}` is random, and the tails of `Y(U)` and `Λ(U)` are not part of the statement.
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

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

variable {ω : Configuration 2}

/-- `ω(U, q) ≤ ρ(U) |q|²`. -/
theorem planarOmega_le_planarRho_mul (p : unitInterval) (ω : Configuration 2) (U : TriadicCube 2)
    (q : Fin 2 → ℝ) : planarOmega p ω U q ≤ planarRho p ω U * (q 0 ^ 2 + q 1 ^ 2) := by
  by_cases hq : q 0 ^ 2 + q 1 ^ 2 = 0
  · have h0 : q 0 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    have h1 : q 1 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    have hq0 : q = 0 := funext fun i => by fin_cases i <;> assumption
    rw [hq0, IsPlanarQuadratic.apply_zero (isPlanarQuadratic_planarOmega p ω U)]
    simp
  · have hpos : 0 < q 0 ^ 2 + q 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hq)
    have h := le_ciSup (bddAbove_planarOmega_ratio p ω U) q
    rw [div_le_iff₀ hpos] at h
    exact (le_max_left _ _).trans h

/-- The comparison of `μ` and `ν` in real form:
`q · ξ ≤ 1(-μ(U, q)) + 1 ν(U, ξ) + |q|₁ |ξ|₁ Y(U)`. -/
theorem sum_mul_le_of_planarComparisonError (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (hZ : planarComparisonError ω U ≠ ∞) (ξ q : Fin 2 → ℝ) :
    ∑ i, q i * ξ i ≤ (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then -planarMu ω U q
        else 0) + (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then planarNu ω U ξ else 0) +
      (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) * (planarComparisonError ω U).toReal := by
  have hX0 : 0 ≤ (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) := by positivity
  have hY0 : 0 ≤ (planarComparisonError ω U).toReal := ENNReal.toReal_nonneg
  have hI1 : 0 ≤ (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then -planarMu ω U q else 0) := by
    split_ifs with hc
    · exact neg_nonneg.2 (planarMu_nonpos hc.1 hc.2 q)
    · exact le_rfl
  have hI2 : 0 ≤ (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then planarNu ω U ξ else 0) := by
    split_ifs
    · exact planarNu_nonneg ξ
    · exact le_rfl
  by_cases hξ : 0 < |ξ 0| + |ξ 1|
  · have h := ofReal_sum_mul_le_planarComparisonError hP U ξ q hξ
    set Iμ : ℝ≥0∞ := if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (-planarMu ω U q) else 0 with hIμ
    set Iν : ℝ≥0∞ := if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (planarNu ω U ξ) else 0 with hIν
    have hIμf : Iμ ≠ ∞ := by rw [hIμ]; split_ifs <;> simp
    have hIνf : Iν ≠ ∞ := by rw [hIν]; split_ifs <;> simp
    have hXZ : ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) * planarComparisonError ω U ≠
        ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZ
    have h' := (ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hIμf, hIνf⟩, hXZ⟩)).1 h
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hIμf, hIνf⟩) hXZ, ENNReal.toReal_add hIμf hIνf,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hX0, hIμ, hIν, toReal_planarMu_indicator,
      toReal_planarNu_indicator] at h'
    exact h'
  · have h0 : |ξ 0| + |ξ 1| = 0 := le_antisymm (not_lt.1 hξ) (by positivity)
    have e0 : ξ 0 = 0 := abs_eq_zero.1 (le_antisymm (by linarith [abs_nonneg (ξ 1)])
      (abs_nonneg _))
    have e1 : ξ 1 = 0 := abs_eq_zero.1 (le_antisymm (by linarith [abs_nonneg (ξ 0)])
      (abs_nonneg _))
    have hl : ∑ i, q i * ξ i = 0 := by simp [Fin.sum_univ_two, e0, e1]
    rw [hl]
    have := mul_nonneg hX0 hY0
    linarith

/-- The bound `Λ(U)` of `-μ(U, ·)` by its values at `e₀`, `e₁` and `e₀ + e₁`. -/
noncomputable def planarMuBound (ω : Configuration 2) (U : TriadicCube 2) : ℝ :=
  |-planarMu ω U (Pi.single 0 1)| + |-planarMu ω U (Pi.single 1 1)| +
    |-planarMu ω U (Pi.single 0 1 + Pi.single 1 1) - -planarMu ω U (Pi.single 0 1) -
      -planarMu ω U (Pi.single 1 1)|

/-- **Lemma 5.3 of Armstrong and Dario** (dimension two, on the partition event, for a resolved
cube): with `Y(U)` the error of the comparison of `μ` and `ν`, `Λ(U)` the bound of `-μ(U, ·)` and
`S` an `ℓ¹` bound of `ā⁻¹`,
`|μ(U, q) + (1/2) q · ā⁻¹ q| ≤ (4 Y S + √(8 (Λ + 1) (ρ(U) + Y S))) |q|²` and
`|ν(U, ā⁻¹ q) - (1/2) q · ā⁻¹ q| ≤ (ρ(U) + 6 Y S + √(8 (Λ + 1) (ρ(U) + Y S))) |q|²`. -/
theorem planar_minimalset {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hP : PlanarPartitionEvent ω) {U : TriadicCube 2} (hU : PlanarResolved ω U)
    (hZ : planarComparisonError ω U ≠ ∞) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin 2 → ℝ, |((planarAhom p)⁻¹ *ᵥ v) 0| + |((planarAhom p)⁻¹ *ᵥ v) 1| ≤
      S * (|v 0| + |v 1|)) (q : Fin 2 → ℝ) :
    |planarMu ω U q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
        (4 * (planarComparisonError ω U).toReal * S +
          Real.sqrt (8 * (planarMuBound ω U + 1) *
            (planarRho p ω U + (planarComparisonError ω U).toReal * S))) * (q 0 ^ 2 + q 1 ^ 2) ∧
      |planarNu ω U ((planarAhom p)⁻¹ *ᵥ q) - 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
        (planarRho p ω U + 6 * (planarComparisonError ω U).toReal * S +
          Real.sqrt (8 * (planarMuBound ω U + 1) *
            (planarRho p ω U + (planarComparisonError ω U).toReal * S))) * (q 0 ^ 2 + q 1 ^ 2) := by
  have hc : PlanarPartitionEvent ω ∧ PlanarResolved ω U := ⟨hP, hU⟩
  set Y := (planarComparisonError ω U).toReal with hY
  have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
  have hg : IsPlanarQuadratic fun q => -planarMu ω U q :=
    IsPlanarQuadratic.neg (isPlanarQuadratic_planarMu hP hU)
  have hΛ0 : 0 ≤ planarMuBound ω U := by unfold planarMuBound; positivity
  have hρ := planarRho_nonneg p ω U
  have hcomp : ∀ p' q' : Fin 2 → ℝ, ∑ i, q' i * p' i ≤
      -planarMu ω U q' + planarNu ω U p' + Y * ((|p' 0| + |p' 1|) * (|q' 0| + |q' 1|)) :=
    fun p' q' => by
      have h := sum_mul_le_of_planarComparisonError hP U hZ p' q'
      rw [if_pos hc, if_pos hc] at h
      linarith
  have hup : ∀ r : Fin 2 → ℝ, -planarMu ω U r ≤ (planarMuBound ω U + 1) * (r 0 ^ 2 + r 1 ^ 2) :=
    fun r => by
      have h := IsPlanarQuadratic.abs_le hg r
      have hr : 0 ≤ r 0 ^ 2 + r 1 ^ 2 := by positivity
      have := (le_abs_self _).trans h
      unfold planarMuBound
      nlinarith
  have hω : ∀ q' : Fin 2 → ℝ, planarNu ω U ((planarAhom p)⁻¹ *ᵥ q') + -planarMu ω U q' -
      ∑ i, q' i * ((planarAhom p)⁻¹ *ᵥ q') i ≤ planarRho p ω U * (q' 0 ^ 2 + q' 1 ^ 2) :=
    fun q' => by
      have h := planarOmega_le_planarRho_mul p ω U q'
      simp only [planarOmega, if_pos hc] at h
      exact h
  have hmain := abs_quadratic_sub_half_le hg (planarAhom p)⁻¹ hS0 hS hY0
    (by positivity : (0 : ℝ) < planarMuBound ω U + 1) hρ hcomp hup hω q
  have hsq := Real.sqrt_nonneg (8 * (planarMuBound ω U + 1) * (planarRho p ω U + Y * S))
  have hq0 : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [show planarMu ω U q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i =
      -(-planarMu ω U q - 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i) by ring, abs_neg]
    exact hmain
  · have hlow := neg_le_planarOmega hpc hP U hZ hS0 hS q
    have hupω := planarOmega_le_planarRho_mul p ω U q
    simp only [planarOmega, if_pos hc] at hlow hupω
    rw [← hY] at hlow
    rw [abs_le] at hmain ⊢
    obtain ⟨hm1, hm2⟩ := hmain
    have k1 : 0 ≤ planarRho p ω U * (q 0 ^ 2 + q 1 ^ 2) := mul_nonneg hρ hq0
    have k2 : 0 ≤ Y * S * (q 0 ^ 2 + q 1 ^ 2) := mul_nonneg (mul_nonneg hY0 hS0) hq0
    constructor <;> nlinarith

end Rigidity.Proofs.Cluster

import Rigidity.Proofs.Dirichlet.HardyDirectional
import Rigidity.Proofs.Dirichlet.SecondDifferences

/-!
# A weighted energy estimate for the discrete Dirichlet problem

For constant diagonal conductances `a_k > 0`, a weight `W > 0` whose gradient ratios satisfy
`R_k(x) + R_k(x − e_k) ≤ κ Δ_k W(x)` on `U` with `κ ≤ 1/4`, and `u = f + φ` harmonic on `U` with
`φ = 0` off `U`, the weighted energies `X = Σ a_k W̄_k (∇_k φ)²` and `Y = Σ a_k W̄_k (∇_k f)²`
satisfy `X ≤ 11 Y`: test the equation with `φ W`, use the identity
`∇(φW) ∇φ = W̄ (∇φ)² + ½ ∇W ∇(φ²)`, summation by parts for the second term, the directional
Hardy inequality and Young's inequality.

With the two-sided power-type weights `W ≃ dist(x, ∂□)^{-γ}`, this is the weighted estimate that
gives the smallness of the energy of the homogenized solution in a boundary layer, in place of
the global Meyers estimate in the proof of Armstrong–Dario, Lemma 6.3, Step 3.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The edge identity `(B P' − A P)(B − A) = ½ (P + P') (B − A)² + ½ (P' − P)(B² − A²)`. -/
theorem edge_product_identity (A B P P' : ℝ) :
    (B * P' - A * P) * (B - A) =
      (P + P') / 2 * (B - A) ^ 2 + 1 / 2 * ((P' - P) * (B ^ 2 - A ^ 2)) := by
  ring

/-- The pointwise bound of the data term: with `m = (P + P')/2`,
`−(B P' − A P) F ≤ ¼ m (B − A)² + (9/2) m F² + ½ A² (P' − P)²/m` for `P, P' > 0`. -/
theorem neg_edge_data_le {A B P P' F : ℝ} (hP : 0 < P) (hP' : 0 < P') :
    -((B * P' - A * P) * F) ≤ 1 / 4 * ((P + P') / 2 * (B - A) ^ 2) +
      9 / 2 * ((P + P') / 2 * F ^ 2) + 1 / 2 * (A ^ 2 * ((P' - P) ^ 2 / ((P + P') / 2))) := by
  set m := (P + P') / 2 with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hPm : P' ≤ 2 * m := by rw [hm]; linarith
  -- the gradient part
  have b1 : -(P' * (B - A) * F) ≤ 1 / 4 * (m * (B - A) ^ 2) + 4 * (m * F ^ 2) := by
    by_cases huv : 0 ≤ (B - A) * F
    · have : 0 ≤ P' * ((B - A) * F) := mul_nonneg hP'.le huv
      nlinarith [sq_nonneg (B - A), sq_nonneg F, hm0]
    · push Not at huv
      have h1 : -(P' * (B - A) * F) ≤ -(2 * m * ((B - A) * F)) := by
        nlinarith
      nlinarith [mul_nonneg hm0.le (sq_nonneg ((B - A) / 2 + 2 * F))]
  -- the weight part
  have b2 : -(A * (P' - P) * F) ≤ 1 / 2 * (A ^ 2 * ((P' - P) ^ 2 / m)) + 1 / 2 * (m * F ^ 2) := by
    rw [← sub_nonneg]
    have h : 1 / 2 * (A ^ 2 * ((P' - P) ^ 2 / m)) + 1 / 2 * (m * F ^ 2) -
        -(A * (P' - P) * F) = (A * (P' - P) + m * F) ^ 2 / (2 * m) := by
      field_simp
      ring
    rw [h]
    positivity
  have hsplit : -((B * P' - A * P) * F) = -(P' * (B - A) * F) + -(A * (P' - P) * F) := by ring
  rw [hsplit]
  linarith

/-- **Weighted energy estimate for the discrete Dirichlet problem**: for constant conductances
`a_k > 0`, a weight `W > 0` with `R_k(x) + R_k(x − e_k) ≤ κ Δ_k W(x)` on `U` (`κ ≤ 1/4`), `U ⊆ Q`
with `U − e_k ⊆ Q`, and `f + φ` harmonic on `U` with `φ = 0` off `U`,
`Σ_{x∈Q} Σ_k a_k W̄_k(x) (∇_k φ(x))² ≤ 11 Σ_{x∈Q} Σ_k a_k W̄_k(x) (∇_k f(x))²`. -/
theorem sum_weighted_energy_le (a : Fin d → ℝ) (ha : ∀ k, 0 < a k) (W : Vertex d → ℝ)
    (hW : ∀ x, 0 < W x) {U Q : Finset (Vertex d)} (hUQ : U ⊆ Q)
    (hUk : ∀ y ∈ U, ∀ k : Fin d, y - unit k ∈ Q) {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ ≤ 1 / 4)
    (hR : ∀ k : Fin d, ∀ x ∈ U, (W (x + unit k) - W x) ^ 2 / ((W x + W (x + unit k)) / 2) +
      (W x - W (x - unit k)) ^ 2 / ((W (x - unit k) + W x) / 2) ≤
        κ * (W (x + unit k) + W (x - unit k) - 2 * W x))
    (f φ : Vertex d → ℝ) (hφ : ∀ x, x ∉ U → φ x = 0)
    (hu : ∀ x ∈ U, condLaplacian (constCond a) (f + φ) x = 0) :
    ∑ x ∈ Q, ∑ k : Fin d, a k * ((W x + W (x + unit k)) / 2 * (φ (x + unit k) - φ x) ^ 2) ≤
      11 * ∑ x ∈ Q, ∑ k : Fin d,
        a k * ((W x + W (x + unit k)) / 2 * (f (x + unit k) - f x) ^ 2) := by
  classical
  have hS : CoversEdges U Q := fun x j hx =>
    hx.elim (fun h => hUQ h) (fun h => by simpa using hUk _ h j)
  -- the directional quantities
  set Xk : Fin d → ℝ := fun k =>
    ∑ x ∈ Q, (W x + W (x + unit k)) / 2 * (φ (x + unit k) - φ x) ^ 2 with hXk
  set Yk : Fin d → ℝ := fun k =>
    ∑ x ∈ Q, (W x + W (x + unit k)) / 2 * (f (x + unit k) - f x) ^ 2 with hYk
  set Hk : Fin d → ℝ := fun k =>
    ∑ x ∈ Q, φ x ^ 2 * (W (x + unit k) + W (x - unit k) - 2 * W x) with hHk
  set Rk : Fin d → ℝ := fun k =>
    ∑ x ∈ Q, φ x ^ 2 * ((W (x + unit k) - W x) ^ 2 / ((W x + W (x + unit k)) / 2)) with hRk
  set Ek : Fin d → ℝ := fun k =>
    ∑ x ∈ Q, (φ (x + unit k) * W (x + unit k) - φ x * W x) * (f (x + unit k) - f x) with hEk
  set Pk : Fin d → ℝ := fun k =>
    ∑ x ∈ Q, (W (x + unit k) - W x) * (φ (x + unit k) ^ 2 - φ x ^ 2) with hPk
  have hXk0 : ∀ k, 0 ≤ Xk k := fun k => Finset.sum_nonneg fun x _ => by
    have := hW x; have := hW (x + unit k); positivity
  have hYk0 : ∀ k, 0 ≤ Yk k := fun k => Finset.sum_nonneg fun x _ => by
    have := hW x; have := hW (x + unit k); positivity
  -- the tested equation
  have key := sum_mul_condLaplacian_eq_sum_gradient_mul (constCond a) U Q
    (fun x => φ x * W x) (f + φ) (fun x hx => by simp [hφ x hx]) hS
  rw [Finset.sum_eq_zero fun x hx => by rw [hu x hx, mul_zero]] at key
  have hdir : ∀ k : Fin d, ∑ x ∈ Q, (φ (x + unit k) * W (x + unit k) - φ x * W x) *
      ((f + φ) (x + unit k) - (f + φ) x) = Xk k + 1 / 2 * Pk k + Ek k := by
    intro k
    simp only [hXk, hPk, hEk, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.add_apply]
    ring
  have hzero : 0 = ∑ k : Fin d, a k * (Xk k + 1 / 2 * Pk k + Ek k) := by
    rw [key, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hdir k, Finset.mul_sum]
    rfl
  -- summation by parts for the weight term
  have hPH : ∀ k : Fin d, Pk k = -Hk k := by
    intro k
    have hs := sum_add_eq_sum_of_support (fun y => (W y - W (y - unit k)) * φ y ^ 2) (unit k)
      (fun y hy => by simp [hφ y hy]) hUQ (fun y hy => hUk y hy k)
    simp only [add_sub_cancel_right] at hs
    have e1 : Pk k = ∑ x ∈ Q, (W (x + unit k) - W x) * φ (x + unit k) ^ 2 -
        ∑ x ∈ Q, (W (x + unit k) - W x) * φ x ^ 2 := by
      rw [hPk, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e1, hs, ← Finset.sum_sub_distrib, hHk, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  -- the Hardy inequality in each direction
  have hHX : ∀ k : Fin d, Hk k ≤ 2 * κ * Xk k := fun k =>
    sum_sq_mul_dirSecondDiff_le W hW k hUQ (fun y hy => hUk y hy k) hκ0 (hR k) φ hφ
  -- the ratio terms
  have hRH : ∀ k : Fin d, Rk k ≤ κ * Hk k := by
    intro k
    rw [hRk, hHk, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x ∈ U
    · have h := hR k x hx
      have h2 : 0 ≤ (W x - W (x - unit k)) ^ 2 / ((W (x - unit k) + W x) / 2) :=
        div_nonneg (sq_nonneg _) (by have := hW x; have := hW (x - unit k); positivity)
      have h3 : (W (x + unit k) - W x) ^ 2 / ((W x + W (x + unit k)) / 2) ≤
          κ * (W (x + unit k) + W (x - unit k) - 2 * W x) := by linarith
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (φ x))
      linarith
    · rw [hφ x hx]
      simp
  -- the data terms
  have hEY : ∀ k : Fin d, -Ek k ≤ 1 / 4 * Xk k + 9 / 2 * Yk k + 1 / 2 * Rk k := by
    intro k
    rw [hEk, hXk, hYk, hRk, ← Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => neg_edge_data_le (hW x) (hW (x + unit k))
  -- assembly
  have hX : ∑ x ∈ Q, ∑ k : Fin d, a k * ((W x + W (x + unit k)) / 2 * (φ (x + unit k) - φ x) ^ 2)
      = ∑ k : Fin d, a k * Xk k := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [hXk, Finset.mul_sum]
  have hY : ∑ x ∈ Q, ∑ k : Fin d, a k * ((W x + W (x + unit k)) / 2 * (f (x + unit k) - f x) ^ 2)
      = ∑ k : Fin d, a k * Yk k := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [hYk, Finset.mul_sum]
  rw [hX, hY]
  have hbound : ∑ k : Fin d, a k * Xk k ≤
      ∑ k : Fin d, a k * ((κ + 1 / 4 + κ ^ 2) * Xk k + 9 / 2 * Yk k) := by
    have hX' : ∑ k : Fin d, a k * Xk k =
        ∑ k : Fin d, a k * (1 / 2 * Hk k - Ek k) := by
      have h0 := hzero
      rw [← sub_eq_zero, zero_sub, neg_eq_zero] at h0
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
      rw [← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hPH k]
      ring
    rw [hX']
    refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (ha k).le
    have h1 := hHX k
    have h2 := hRH k
    have h3 := hEY k
    have hk2 : κ * Hk k ≤ κ * (2 * κ * Xk k) := mul_le_mul_of_nonneg_left h1 hκ0.le
    nlinarith
  have hcoef : κ + 1 / 4 + κ ^ 2 ≤ 9 / 16 := by nlinarith
  have hfin : ∑ k : Fin d, a k * ((κ + 1 / 4 + κ ^ 2) * Xk k + 9 / 2 * Yk k) ≤
      9 / 16 * ∑ k : Fin d, a k * Xk k + 9 / 2 * ∑ k : Fin d, a k * Yk k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (ha k).le (hXk0 k))
    nlinarith [mul_nonneg (ha k).le (hYk0 k)]
  have hY0 : 0 ≤ ∑ k : Fin d, a k * Yk k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (ha k).le (hYk0 k)
  linarith

end Rigidity.Dirichlet

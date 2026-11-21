import LatticeProb.Site
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# First-order Taylor expansion on the lattice

For a function `f` on `ℤ^d` and lattice points `c ≤ x` (coordinatewise) with `xᵢ - cᵢ ≤ s`, the
affine function `f(c) + ∑ᵢ (xᵢ - cᵢ) D_i f(c)`, `D_i f(y) = f(y + eᵢ) - f(y)`, approximates `f(x)`
up to `d (d + 1) s² M` when all second forward differences `D_a D_b f` are bounded by `M` on the
box `[c, x]` (`abs_sub_taylor_le`). The proof moves from `c` to `x` one coordinate at a time:
along each coordinate the increments of `f` are first differences, which move by second
differences from their values at `c`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb

variable {d : ℕ}

/-- The forward difference `D_i h(y) = h(y + eᵢ) - h(y)`. -/
def fwd (i : Fin d) (h : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) : ℝ := h (y + unit i) - h y

/-- Telescoping along one direction. -/
theorem abs_sub_le_of_fwd_le (ψ : (Fin d → ℤ) → ℝ) (q : Fin d → ℤ) (i : Fin d) {M : ℝ}
    (k : ℕ) (hM : ∀ t : ℕ, t < k → |fwd i ψ (q + (t : ℤ) • unit i)| ≤ M) :
    |ψ (q + (k : ℤ) • unit i) - ψ q| ≤ k * M := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := ih fun t ht => hM t (by omega)
    have h2 := hM k (by omega)
    have e : ψ (q + ((k + 1 : ℕ) : ℤ) • unit i) - ψ q =
        (ψ (q + (k : ℤ) • unit i) - ψ q) + fwd i ψ (q + (k : ℤ) • unit i) := by
      simp only [fwd]
      push_cast
      rw [add_smul, one_smul, ← add_assoc]
      ring
    rw [e]
    push_cast
    calc |ψ (q + (k : ℤ) • unit i) - ψ q + fwd i ψ (q + (k : ℤ) • unit i)|
        ≤ |ψ (q + (k : ℤ) • unit i) - ψ q| + |fwd i ψ (q + (k : ℤ) • unit i)| := abs_add_le _ _
      _ ≤ k * M + M := add_le_add h1 h2
      _ = (k + 1) * M := by ring

/-- **First-order Taylor expansion along one direction.** -/
theorem abs_sub_taylor_one_le (φ : (Fin d → ℤ) → ℝ) (q : Fin d → ℤ) (i : Fin d) {M : ℝ}
    (hM0 : 0 ≤ M) (n : ℕ)
    (hM : ∀ t : ℕ, t < n → |fwd i (fwd i φ) (q + (t : ℤ) • unit i)| ≤ M) :
    |φ (q + (n : ℤ) • unit i) - φ q - n * fwd i φ q| ≤ n ^ 2 * M := by
  have htel : ∀ k : ℕ, k ≤ n → φ (q + (k : ℤ) • unit i) - φ q =
      ∑ t ∈ range k, fwd i φ (q + (t : ℤ) • unit i) := by
    intro k _
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ← ih (by omega)]
      simp only [fwd]
      push_cast
      rw [add_smul, one_smul, ← add_assoc]
      ring
  rw [htel n le_rfl]
  have hdiff : ∀ t ∈ range n, |fwd i φ (q + (t : ℤ) • unit i) - fwd i φ q| ≤ t * M := by
    intro t ht
    have := abs_sub_le_of_fwd_le (fwd i φ) q i t fun t' ht' =>
      hM t' (by have := mem_range.1 ht; omega)
    exact this
  have e : ∑ t ∈ range n, fwd i φ (q + (t : ℤ) • unit i) - n * fwd i φ q =
      ∑ t ∈ range n, (fwd i φ (q + (t : ℤ) • unit i) - fwd i φ q) := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [e]
  calc |∑ t ∈ range n, (fwd i φ (q + (t : ℤ) • unit i) - fwd i φ q)|
      ≤ ∑ t ∈ range n, |fwd i φ (q + (t : ℤ) • unit i) - fwd i φ q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ range n, (t : ℝ) * M := sum_le_sum hdiff
    _ ≤ ∑ _t ∈ range n, (n : ℝ) * M := sum_le_sum fun t ht => by
        have := mem_range.1 ht
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this.le) hM0
    _ = n ^ 2 * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- The point `c + ∑_{i ∈ T} (xᵢ - cᵢ) eᵢ`, with the coordinates of `x` in `T` and of `c` outside. -/
def cornerPoint (c x : Fin d → ℤ) (T : Finset (Fin d)) : Fin d → ℤ :=
  c + ∑ i ∈ T, (x i - c i) • unit i

theorem cornerPoint_apply (c x : Fin d → ℤ) (T : Finset (Fin d)) (j : Fin d) :
    cornerPoint c x T j = if j ∈ T then x j else c j := by
  classical
  simp only [cornerPoint, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unit,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs <;> ring

theorem cornerPoint_insert (c x : Fin d → ℤ) {T : Finset (Fin d)} {j : Fin d} (hj : j ∉ T) :
    cornerPoint c x (insert j T) = cornerPoint c x T + (x j - c j) • unit j := by
  rw [cornerPoint, cornerPoint, sum_insert hj]
  abel

theorem cornerPoint_univ (c x : Fin d → ℤ) : cornerPoint c x univ = x := by
  funext j
  rw [cornerPoint_apply, if_pos (mem_univ j)]

end Rigidity.Proofs.Regularity

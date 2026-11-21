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

/-- The point `c + ∑_{i ∈ T} (xᵢ - cᵢ) eᵢ`, with the coordinates of `x` in `T` and of `c`
outside. -/
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

theorem cornerPoint_add_mem {c x : Fin d → ℤ} (hcx : ∀ i, c i ≤ x i) {T : Finset (Fin d)}
    {j : Fin d} (hj : j ∉ T) {t : ℕ} (ht : (t : ℤ) ≤ x j - c j) (i : Fin d) :
    c i ≤ (cornerPoint c x T + (t : ℤ) • unit j) i ∧
      (cornerPoint c x T + (t : ℤ) • unit j) i ≤ x i := by
  classical
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply, cornerPoint_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_neg hj, if_pos rfl]
    constructor <;> omega
  · rw [if_neg hij, mul_zero, add_zero]
    have := hcx i
    split_ifs <;> constructor <;> omega

/-- Telescoping from `c` to a corner point, one coordinate at a time. -/
theorem abs_cornerPoint_sub_le (ψ : (Fin d → ℤ) → ℝ) {c x : Fin d → ℤ}
    (hcx : ∀ i, c i ≤ x i) {s : ℕ} (hs : ∀ i, x i - c i ≤ s) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y : Fin d → ℤ, (∀ i, c i ≤ y i ∧ y i ≤ x i) → ∀ i, |fwd i ψ y| ≤ M)
    (T : Finset (Fin d)) : |ψ (cornerPoint c x T) - ψ c| ≤ T.card * s * M := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [cornerPoint]
  | insert j T hj ih =>
    rw [cornerPoint_insert c x hj, card_insert_of_notMem hj]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = x j - c j := ⟨(x j - c j).toNat, by
      have := hcx j; omega⟩
    rw [← hn]
    have hseg := abs_sub_le_of_fwd_le ψ (cornerPoint c x T) j n fun t ht =>
      hM _ (cornerPoint_add_mem hcx hj (by omega)) j
    have hns : (n : ℝ) ≤ s := by have := hs j; exact_mod_cast (by omega : n ≤ s)
    calc |ψ (cornerPoint c x T + (n : ℤ) • unit j) - ψ c|
        ≤ |ψ (cornerPoint c x T + (n : ℤ) • unit j) - ψ (cornerPoint c x T)| +
            |ψ (cornerPoint c x T) - ψ c| := abs_sub_le _ _ _
      _ ≤ n * M + T.card * s * M := add_le_add hseg ih
      _ ≤ s * M + T.card * s * M := by nlinarith
      _ = ((T.card + 1 : ℕ) : ℝ) * s * M := by push_cast; ring

/-- **First-order Taylor expansion on the lattice.** -/
theorem abs_sub_taylor_le (f : (Fin d → ℤ) → ℝ) {c x : Fin d → ℤ} (hcx : ∀ i, c i ≤ x i)
    {s : ℕ} (hs : ∀ i, x i - c i ≤ s) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y : Fin d → ℤ, (∀ i, c i ≤ y i ∧ y i ≤ x i) → ∀ a b, |fwd a (fwd b f) y| ≤ M) :
    |f x - f c - ∑ i, ((x i - c i : ℤ) : ℝ) * fwd i f c| ≤ d * (d + 1) * s ^ 2 * M := by
  classical
  have key : ∀ T : Finset (Fin d),
      |f (cornerPoint c x T) - f c - ∑ i ∈ T, ((x i - c i : ℤ) : ℝ) * fwd i f c| ≤
        T.card * (T.card + 1) * s ^ 2 * M := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [cornerPoint]
    | insert j T hj ih =>
      rw [cornerPoint_insert c x hj, card_insert_of_notMem hj, sum_insert hj]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = x j - c j := ⟨(x j - c j).toNat, by
        have := hcx j; omega⟩
      rw [← hn]
      set p := cornerPoint c x T
      have hns : (n : ℝ) ≤ s := by have := hs j; exact_mod_cast (by omega : n ≤ s)
      have h2 := abs_sub_taylor_one_le f p j hM0 n fun t ht =>
        hM _ (cornerPoint_add_mem hcx hj (by omega)) j j
      have h3 := abs_cornerPoint_sub_le (fwd j f) hcx hs hM0
        (fun y hy i => hM y hy i j) T
      have e : f (p + (n : ℤ) • unit j) - f c -
          (((n : ℤ) : ℝ) * fwd j f c + ∑ i ∈ T, ((x i - c i : ℤ) : ℝ) * fwd i f c) =
        (f p - f c - ∑ i ∈ T, ((x i - c i : ℤ) : ℝ) * fwd i f c) +
          (f (p + (n : ℤ) • unit j) - f p - n * fwd j f p) +
          n * (fwd j f p - fwd j f c) := by push_cast; ring
      rw [e]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h3' : |(n : ℝ) * (fwd j f p - fwd j f c)| ≤ s * (T.card * s * M) := by
        rw [abs_mul, abs_of_nonneg hn0]
        exact mul_le_mul hns h3 (abs_nonneg _) (by positivity)
      have h2' : (n : ℝ) ^ 2 * M ≤ (s : ℝ) ^ 2 * M :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn0 hns 2) hM0
      calc |(f p - f c - ∑ i ∈ T, ((x i - c i : ℤ) : ℝ) * fwd i f c) +
            (f (p + (n : ℤ) • unit j) - f p - n * fwd j f p) +
            n * (fwd j f p - fwd j f c)|
          ≤ |f p - f c - ∑ i ∈ T, ((x i - c i : ℤ) : ℝ) * fwd i f c| +
              |f (p + (n : ℤ) • unit j) - f p - n * fwd j f p| +
              |(n : ℝ) * (fwd j f p - fwd j f c)| := by
            refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ T.card * (T.card + 1) * s ^ 2 * M + s ^ 2 * M + s * (T.card * s * M) :=
            add_le_add (add_le_add ih (h2.trans h2')) h3'
        _ ≤ ((T.card + 1 : ℕ) : ℝ) * ((T.card + 1 : ℕ) + 1) * s ^ 2 * M := by
            push_cast
            have : 0 ≤ (s : ℝ) ^ 2 * M := by positivity
            nlinarith
  have := key univ
  rw [cornerPoint_univ, card_univ, Fintype.card_fin] at this
  exact this

end Rigidity.Proofs.Regularity

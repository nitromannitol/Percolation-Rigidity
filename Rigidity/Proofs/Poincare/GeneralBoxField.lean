import Rigidity.Proofs.Poincare.GeneralHeatDuality
import Rigidity.Proofs.Poincare.GeneralDualTestFunction

/-!
# A vector field with prescribed divergence on a box of `ℤ^d`

For `g` supported in the box `B = [-ρ, ρ]^d` with `Σ_B g = 0`, the field
`G_j(z) = Σ_{y ∈ B} g(y) w_j(y, z)` has divergence `divField G = g` (`divField_boxField`), is
supported in `B` (`boxField_eq_zero`) and satisfies `Σ_z |G_j(z)| ≤ ρ Σ_B |g|`
(`sum_abs_boxField_le`). Here `w_j(y, ·)` counts, with signs, the bonds in direction `j` of the
path from `0` to `y` that moves the coordinates one after the other: first `y_0` steps in direction
`0`, then `y_1` steps in direction `1`, and so on (`legWeight`). In the duality identity this is
the path integral `u(y) - u(0) = Σ_{path} ∇u` of the source, written through the heat averages of
`∇u` only; it replaces the planar row-and-column field of `BoxField.lean`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- The point `(y_0, …, y_{k-1}, 0, …, 0)` reached after the first `k` legs of the path. -/
def prefixPt (y : Vertex d) (k : ℕ) : Vertex d := fun i => if i.val < k then y i else 0

theorem prefixPt_zero (y : Vertex d) : prefixPt y 0 = 0 := by
  funext i
  simp [prefixPt]

theorem prefixPt_dim (y : Vertex d) : prefixPt y d = y := by
  funext i
  simp [prefixPt, i.isLt]

theorem prefixPt_succ (y : Vertex d) {k : ℕ} (hk : k < d) :
    prefixPt y (k + 1) = prefixPt y k + (y ⟨k, hk⟩) • unit ⟨k, hk⟩ := by
  funext i
  simp only [prefixPt, Pi.add_apply, Pi.smul_apply, unit, Pi.single_apply, smul_eq_mul]
  rcases lt_trichotomy i.val k with h | h | h
  · have hne : i ≠ ⟨k, hk⟩ := fun e => by rw [e] at h; exact lt_irrefl _ h
    simp [h, Nat.lt_succ_of_lt h, hne]
  · have he : i = ⟨k, hk⟩ := Fin.ext h
    subst he
    simp
  · have hne : i ≠ ⟨k, hk⟩ := fun e => by rw [e] at h; exact lt_irrefl _ h
    have h1 : ¬ i.val < k + 1 := by omega
    have h2 : ¬ i.val < k := by omega
    simp [h1, h2, hne]

/-- The signed count of the bonds `(z, z + e_j)` on the leg from `x` to `x + n e_j`. -/
noncomputable def legWeight (x : Vertex d) (j : Fin d) (n : ℤ) (z : Vertex d) : ℝ :=
  if 0 ≤ n then ∑ l ∈ Finset.range n.toNat, (if z = x + (l : ℤ) • unit j then 1 else 0)
  else -∑ l ∈ Finset.range (-n).toNat, (if z = x - ((l : ℤ) + 1) • unit j then 1 else 0)

theorem tsum_ite_mul (p : Vertex d) (F : Vertex d → ℝ) :
    ∑' z, (if z = p then (1 : ℝ) else 0) * F z = F p := by
  rw [tsum_eq_single p fun z hz => by rw [if_neg hz, zero_mul], if_pos rfl, one_mul]

theorem summable_ite_mul (p : Vertex d) (F : Vertex d → ℝ) :
    Summable fun z => (if z = p then (1 : ℝ) else 0) * F z :=
  summable_of_ne_finset_zero (s := {p}) fun z hz => by
    rw [if_neg (fun h => hz (by rw [h]; exact Finset.mem_singleton_self p)), zero_mul]

/-- **The leg identity**: `Σ_z w(z) ∇_j u(z) = u(x + n e_j) - u(x)`. -/
theorem tsum_legWeight_mul_fd (u : Vertex d → ℝ) (x : Vertex d) (j : Fin d) (n : ℤ) :
    ∑' z, legWeight x j n z * fd u j z = u (x + n • unit j) - u x := by
  unfold legWeight
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simp only [Int.toNat_natCast, Finset.sum_mul]
    rw [Summable.tsum_finsetSum fun l _ => summable_ite_mul _ _]
    simp only [tsum_ite_mul]
    have h := Finset.sum_range_sub (fun l : ℕ => u (x + (l : ℤ) • unit j)) m
    simp only [Nat.cast_zero, zero_smul, add_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [fd, Nat.cast_succ, add_smul, one_smul, add_assoc]
  · have hn' : n < 0 := not_le.1 hn
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    subst hm
    simp only [neg_neg, Int.toNat_natCast, neg_mul, Finset.sum_mul, tsum_neg]
    rw [Summable.tsum_finsetSum fun l _ => summable_ite_mul _ _]
    simp only [tsum_ite_mul]
    have h := Finset.sum_range_sub (fun l : ℕ => u (x - (l : ℤ) • unit j)) m
    simp only [Nat.cast_zero, zero_smul, sub_zero] at h
    have e : ∑ l ∈ Finset.range m, fd u j (x - ((l : ℤ) + 1) • unit j) =
        -∑ l ∈ Finset.range m, (u (x - ((l + 1 : ℕ) : ℤ) • unit j) - u (x - (l : ℤ) • unit j)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [fd, Nat.cast_succ, add_smul, one_smul]
      rw [show x - ((l : ℤ) • unit j + unit j) + unit j = x - (l : ℤ) • unit j by abel]
      ring
    rw [e, h, neg_smul, sub_eq_add_neg]
    ring

theorem legWeight_eq_zero {x : Vertex d} {j : Fin d} {n : ℤ} {z : Vertex d}
    (hz : ∀ l : ℤ, (0 ≤ l ∧ l < n) ∨ (n ≤ l ∧ l < 0) → z ≠ x + l • unit j) :
    legWeight x j n z = 0 := by
  unfold legWeight
  split_ifs with hn
  · refine Finset.sum_eq_zero fun l hl => if_neg (hz l (Or.inl ⟨by positivity, ?_⟩))
    rw [Finset.mem_range] at hl
    omega
  · rw [neg_eq_zero]
    refine Finset.sum_eq_zero fun l hl => if_neg ?_
    rw [Finset.mem_range] at hl
    have h := hz (-((l : ℤ) + 1)) (Or.inr ⟨by omega, by omega⟩)
    rwa [neg_smul, ← sub_eq_add_neg] at h

/-- `Σ_z |w(z)| ≤ |n|`. -/
theorem sum_abs_legWeight_le (s : Finset (Vertex d)) (x : Vertex d) (j : Fin d) (n : ℤ) :
    ∑ z ∈ s, |legWeight x j n z| ≤ |(n : ℝ)| := by
  have hcount : ∀ (m : ℕ) (p : ℕ → Vertex d),
      ∑ z ∈ s, |∑ l ∈ Finset.range m, (if z = p l then (1 : ℝ) else 0)| ≤ m := by
    intro m p
    calc ∑ z ∈ s, |∑ l ∈ Finset.range m, (if z = p l then (1 : ℝ) else 0)|
        = ∑ z ∈ s, ∑ l ∈ Finset.range m, (if z = p l then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun z _ => abs_of_nonneg ?_
          exact Finset.sum_nonneg fun l _ => by split_ifs <;> norm_num
      _ = ∑ l ∈ Finset.range m, ∑ z ∈ s, (if z = p l then (1 : ℝ) else 0) := Finset.sum_comm
      _ ≤ ∑ l ∈ Finset.range m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [Finset.sum_ite_eq']
          split_ifs <;> norm_num
      _ = m := by simp
  unfold legWeight
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simp only [Int.toNat_natCast, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m)]
    exact hcount m _
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    subst hm
    simp only [neg_neg, Int.toNat_natCast, abs_neg, Int.cast_neg, Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m)]
    exact hcount m _

/-- The field `G_j(z) = Σ_{y ∈ B} g(y) w_j(y, z)` with the leg weights of the axis path. -/
noncomputable def boxField (ρ : ℕ) (g : Vertex d → ℝ) (j : Fin d) (z : Vertex d) : ℝ :=
  ∑ y ∈ supBox 0 ρ, g y * legWeight (prefixPt y j.val) j (y j) z

variable {ρ : ℕ} {g : Vertex d → ℝ}

theorem prefixPt_mem_supBox {y : Vertex d} (hy : y ∈ supBox 0 ρ) (k : ℕ) :
    prefixPt y k ∈ supBox 0 ρ := by
  rw [mem_supBox] at hy ⊢
  intro i
  have := hy i
  simp only [prefixPt, Pi.zero_apply, sub_zero] at this ⊢
  split_ifs
  · exact this
  · simp

/-- The field is supported in the box. -/
theorem boxField_eq_zero (j : Fin d) {z : Vertex d} (hz : z ∉ supBox 0 ρ) :
    boxField ρ g j z = 0 := by
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [legWeight_eq_zero, mul_zero]
  rintro l hl rfl
  apply hz
  have hpre' := prefixPt_mem_supBox hy j.val
  rw [mem_supBox] at hy hpre' ⊢
  intro i
  have hyi := hy i
  have hpre := hpre' i
  simp only [Pi.zero_apply, sub_zero] at hyi hpre ⊢
  simp only [Pi.add_apply, Pi.smul_apply, unit, Pi.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    have h0 : prefixPt y i.val i = 0 := by simp [prefixPt]
    rw [h0, if_pos rfl, zero_add, mul_one]
    have := hyi
    rw [abs_le] at this ⊢
    omega
  · rw [if_neg hij, mul_zero, add_zero]
    exact hpre

theorem summable_legWeight_mul (x : Vertex d) (j : Fin d) (n : ℤ) (F : Vertex d → ℝ) :
    Summable fun z => legWeight x j n z * F z := by
  unfold legWeight
  split_ifs
  · simp only [Finset.sum_mul]
    exact summable_sum fun l _ => summable_ite_mul _ _
  · simp only [neg_mul, Finset.sum_mul]
    exact (summable_sum fun l _ => summable_ite_mul _ _).neg

/-- **The path identity**: `Σ_j Σ_z G_j(z) ∇_j u(z) = Σ_B g (u - u(0))`. -/
theorem sum_tsum_boxField_mul_fd (u : Vertex d → ℝ) :
    ∑ j : Fin d, ∑' z, boxField ρ g j z * fd u j z =
      ∑ y ∈ supBox 0 ρ, g y * (u y - u 0) := by
  have hj : ∀ j : Fin d, ∑' z, boxField ρ g j z * fd u j z =
      ∑ y ∈ supBox 0 ρ, g y * (u (prefixPt y (j.val + 1)) - u (prefixPt y j.val)) := by
    intro j
    simp only [boxField, Finset.sum_mul]
    rw [Summable.tsum_finsetSum fun y _ =>
      (summable_legWeight_mul (prefixPt y j.val) j (y j) (fd u j)).mul_left (g y) |>.congr
        fun z => by ring]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show (fun z => g y * legWeight (prefixPt y j.val) j (y j) z * fd u j z) =
        fun z => g y * (legWeight (prefixPt y j.val) j (y j) z * fd u j z) by
      funext z; ring, tsum_mul_left, tsum_legWeight_mul_fd, prefixPt_succ y j.isLt]
  simp only [hj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have h := Finset.sum_range_sub (fun k => u (prefixPt y k)) d
  rw [prefixPt_dim, prefixPt_zero] at h
  rw [← h]
  exact Fin.sum_univ_eq_sum_range (fun k => u (prefixPt y (k + 1)) - u (prefixPt y k)) d

/-- **The divergence of the field is `g`**. -/
theorem divField_boxField [NeZero d] (hg : ∀ y ∉ supBox 0 ρ, g y = 0)
    (hsum : ∑ y ∈ supBox 0 ρ, g y = 0) (w : Vertex d) : divField (boxField ρ g) w = g w := by
  set δ : Vertex d → ℝ := fun z => if z = w then 1 else 0 with hδ
  have h := tsum_divField_mul δ (S := supBox 0 ρ) (G := boxField ρ g)
    (fun j y hy => boxField_eq_zero j hy)
  have hL : ∑' y, divField (boxField ρ g) y * δ y = divField (boxField ρ g) w := by
    rw [tsum_eq_single w fun z hz => by simp [hδ, hz], hδ]
    simp
  rw [hL, sum_tsum_boxField_mul_fd δ] at h
  rw [h, Finset.sum_congr rfl fun y _ => mul_sub (g y) (δ y) (δ 0), Finset.sum_sub_distrib,
    ← Finset.sum_mul, hsum, zero_mul, sub_zero]
  simp only [hδ, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hw
  · rfl
  · exact (hg w hw).symm

/-- **The `ℓ¹` bound** `Σ_B |G_j| ≤ ρ Σ_B |g|`. -/
theorem sum_abs_boxField_le (j : Fin d) :
    ∑ z ∈ supBox 0 ρ, |boxField ρ g j z| ≤ ρ * ∑ y ∈ supBox 0 ρ, |g y| := by
  calc ∑ z ∈ supBox 0 ρ, |boxField ρ g j z|
      ≤ ∑ z ∈ supBox 0 ρ, ∑ y ∈ supBox 0 ρ,
          |g y| * |legWeight (prefixPt y j.val) j (y j) z| := by
        refine Finset.sum_le_sum fun z _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun y _ => abs_mul _ _
    _ = ∑ y ∈ supBox 0 ρ, |g y| *
          ∑ z ∈ supBox 0 ρ, |legWeight (prefixPt y j.val) j (y j) z| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ y ∈ supBox 0 ρ, |g y| * ρ := by
        refine Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (sum_abs_legWeight_le _ _ _ _).trans ?_
        have := mem_supBox.1 hy j
        simp only [Pi.zero_apply, sub_zero] at this
        exact_mod_cast this
    _ = ρ * ∑ y ∈ supBox 0 ρ, |g y| := by
        rw [← Finset.sum_mul, mul_comm]

end Rigidity.Poincare.GeneralDim

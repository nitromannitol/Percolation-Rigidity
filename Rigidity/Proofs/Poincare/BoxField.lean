import Rigidity.Proofs.Poincare.HeatDuality

/-!
# A vector field with prescribed divergence on a box of `ℤ²`

For `g` supported in the box `B = [-ρ, ρ]²` with `Σ_B g = 0`, the field
`G₀(y) = -Σ_{l ≤ y₀} (g(l, y₁) - 1_{l = 0} h(y₁))`, `G₁(y) = -1_{y₀ = 0} Σ_{k ≤ y₁} h(k)`, with the
row sums `h(k) = Σ_l g(l, k)`, is supported in `B`, has divergence `divField G = g`
(`divField_boxField`) and `Σ_y |G_j(y)| ≤ 2 (2ρ + 1) Σ_B |g|` (`sum_abs_boxField_le`). In the
duality identity this is the path integral `u(y) - u(0) = Σ_{path} ∇u` of the source, written
through the heat averages of `∇u` only.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Poincare

/-- The point `(l, k)` of `ℤ²`. -/
def pt (l k : ℤ) : Vertex 2 := ![l, k]

@[simp] theorem pt_zero (l k : ℤ) : pt l k 0 = l := rfl
@[simp] theorem pt_one (l k : ℤ) : pt l k 1 = k := rfl

theorem pt_eta (y : Vertex 2) : pt (y 0) (y 1) = y := by
  funext i
  fin_cases i <;> rfl

theorem sub_unit_zero (y : Vertex 2) : y - unit 0 = pt (y 0 - 1) (y 1) := by
  funext i
  fin_cases i <;> simp [pt, unit]

theorem sub_unit_one (y : Vertex 2) : y - unit 1 = pt (y 0) (y 1 - 1) := by
  funext i
  fin_cases i <;> simp [pt, unit]

/-- The interval `[-ρ, ρ]` of `ℤ`. -/
noncomputable def ival (ρ : ℕ) : Finset ℤ := Finset.Icc (-(ρ : ℤ)) ρ

theorem zero_mem_ival (ρ : ℕ) : (0 : ℤ) ∈ ival ρ := by
  simp [ival]

theorem mem_supBox_zero_iff {ρ : ℕ} {y : Vertex 2} :
    y ∈ supBox 0 ρ ↔ y 0 ∈ ival ρ ∧ y 1 ∈ ival ρ := by
  rw [mem_supBox]
  simp only [Pi.zero_apply, sub_zero, ival, Finset.mem_Icc, abs_le]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

theorem supBox_zero_eq_image (ρ : ℕ) :
    supBox 0 ρ = (ival ρ ×ˢ ival ρ).image fun q => pt q.1 q.2 := by
  ext y
  simp only [Finset.mem_image, Finset.mem_product, mem_supBox_zero_iff]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨(y 0, y 1), ⟨h0, h1⟩, pt_eta y⟩
  · rintro ⟨q, ⟨h0, h1⟩, rfl⟩
    exact ⟨h0, h1⟩

/-- Sums over the box `[-ρ, ρ]²` as double sums. -/
theorem sum_supBox_zero (ρ : ℕ) (F : Vertex 2 → ℝ) :
    ∑ y ∈ supBox 0 ρ, F y = ∑ k ∈ ival ρ, ∑ l ∈ ival ρ, F (pt l k) := by
  rw [supBox_zero_eq_image, Finset.sum_image, Finset.sum_product, Finset.sum_comm]
  intro a _ b _ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [pt_zero, pt_one] at h0 h1
  exact Prod.ext h0 h1

section Field

variable (ρ : ℕ) (g : Vertex 2 → ℝ)

/-- The row sums `h(k) = Σ_l g(l, k)`. -/
noncomputable def rowSum (k : ℤ) : ℝ := ∑ l ∈ ival ρ, g (pt l k)

/-- The field with divergence `g`. -/
noncomputable def boxField : Fin 2 → Vertex 2 → ℝ
  | 0 => fun y => -∑ l ∈ ival ρ,
      if l ≤ y 0 then g (pt l (y 1)) - (if l = 0 then rowSum ρ g (y 1) else 0) else 0
  | 1 => fun y => if y 0 = 0 then -∑ k ∈ ival ρ, (if k ≤ y 1 then rowSum ρ g k else 0) else 0

variable {ρ g}

theorem sum_ite_le_sub (I : Finset ℤ) (F : ℤ → ℝ) (a : ℤ) :
    ∑ l ∈ I, (if l ≤ a then F l else 0) - ∑ l ∈ I, (if l ≤ a - 1 then F l else 0) =
      if a ∈ I then F a else 0 := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_ite_eq' I a F]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h1 : l = a
  · subst h1
    simp
  · by_cases h2 : l ≤ a - 1
    · rw [if_pos (by omega), if_pos h2, if_neg h1, sub_self]
    · rw [if_neg (by omega), if_neg h2, if_neg h1, sub_zero]

theorem rowSum_eq_zero (hg : ∀ y ∉ supBox 0 ρ, g y = 0) {k : ℤ} (hk : k ∉ ival ρ) :
    rowSum ρ g k = 0 :=
  Finset.sum_eq_zero fun l _ => hg _ fun h => hk (by
    rw [mem_supBox_zero_iff] at h; simpa using h.2)

/-- **The divergence of the field is `g`**. -/
theorem divField_boxField (hg : ∀ y ∉ supBox 0 ρ, g y = 0) (y : Vertex 2) :
    divField (boxField ρ g) y = g y := by
  have hG0 : boxField ρ g 0 (y - unit 0) = -∑ l ∈ ival ρ, (if l ≤ y 0 - 1 then
      g (pt l (y 1)) - (if l = 0 then rowSum ρ g (y 1) else 0) else 0) := by
    rw [sub_unit_zero]; rfl
  have hG0' : boxField ρ g 0 y = -∑ l ∈ ival ρ, (if l ≤ y 0 then
      g (pt l (y 1)) - (if l = 0 then rowSum ρ g (y 1) else 0) else 0) := rfl
  have hG1 : boxField ρ g 1 (y - unit 1) = if y 0 = 0 then
      -∑ k ∈ ival ρ, (if k ≤ y 1 - 1 then rowSum ρ g k else 0) else 0 := by
    rw [sub_unit_one]; rfl
  have hG1' : boxField ρ g 1 y = if y 0 = 0 then
      -∑ k ∈ ival ρ, (if k ≤ y 1 then rowSum ρ g k else 0) else 0 := rfl
  rw [divField, Fin.sum_univ_two, hG0, hG0', hG1, hG1']
  have e0 := sum_ite_le_sub (ival ρ) (fun l => g (pt l (y 1)) -
    (if l = 0 then rowSum ρ g (y 1) else 0)) (y 0)
  have e1 := sum_ite_le_sub (ival ρ) (rowSum ρ g) (y 1)
  have hrow : (if y 1 ∈ ival ρ then rowSum ρ g (y 1) else 0) = rowSum ρ g (y 1) := by
    split_ifs with h
    · rfl
    · exact (rowSum_eq_zero hg h).symm
  by_cases h0 : y 0 = 0
  · have hy0 : y 0 ∈ ival ρ := h0 ▸ zero_mem_ival ρ
    rw [if_pos hy0, if_pos h0, pt_eta] at e0
    rw [hrow] at e1
    rw [if_pos h0, if_pos h0]
    linarith
  · rw [if_neg h0, if_neg h0]
    by_cases hy0 : y 0 ∈ ival ρ
    · rw [if_pos hy0, if_neg h0, pt_eta, sub_zero] at e0
      linarith
    · rw [if_neg hy0] at e0
      have hgy : g y = 0 := hg y fun h => hy0 (mem_supBox_zero_iff.1 h).1
      rw [hgy]
      linarith

theorem card_ival (ρ : ℕ) : ((ival ρ).card : ℝ) = 2 * ρ + 1 := by
  rw [ival, Int.card_Icc]
  have : ((ρ : ℤ) + 1 - -(ρ : ℤ)).toNat = 2 * ρ + 1 := by omega
  rw [this]
  push_cast
  ring

/-- **The field is supported in the box**. -/
theorem boxField_eq_zero (hg : ∀ y ∉ supBox 0 ρ, g y = 0)
    (hsum : ∑ y ∈ supBox 0 ρ, g y = 0) (j : Fin 2) {y : Vertex 2} (hy : y ∉ supBox 0 ρ) :
    boxField ρ g j y = 0 := by
  have hg' : ∀ l k, k ∉ ival ρ → g (pt l k) = 0 := fun l k hk =>
    hg _ fun h => hk (by rw [mem_supBox_zero_iff] at h; simpa using h.2)
  rw [mem_supBox_zero_iff, not_and_or] at hy
  have hrow0 : ∑ k ∈ ival ρ, rowSum ρ g k = 0 := by
    rw [← hsum, sum_supBox_zero]
    rfl
  fin_cases j
  · simp only [boxField, neg_eq_zero]
    rcases hy with hy0 | hy1
    · rcases lt_or_gt_of_ne (show y 0 ≠ 0 by
        intro h; exact hy0 (h ▸ zero_mem_ival ρ)) with hlt | hgt
      · by_cases hneg : y 0 < -(ρ : ℤ)
        · refine Finset.sum_eq_zero fun l hl => if_neg ?_
          simp only [ival, Finset.mem_Icc] at hl
          omega
        · exfalso
          exact hy0 (by simp only [ival, Finset.mem_Icc]; omega)
      · have hall : ∀ l ∈ ival ρ, l ≤ y 0 := by
          intro l hl
          simp only [ival, Finset.mem_Icc] at hl hy0
          omega
        rw [Finset.sum_congr rfl fun l hl => if_pos (hall l hl), Finset.sum_sub_distrib,
          Finset.sum_ite_eq' (ival ρ) 0, if_pos (zero_mem_ival ρ)]
        simp only [rowSum, sub_self]
    · refine Finset.sum_eq_zero fun l _ => ?_
      rw [hg' l (y 1) hy1, rowSum_eq_zero hg hy1]
      simp
  · simp only [boxField]
    split_ifs with h0
    · rw [neg_eq_zero]
      rcases hy with hy0 | hy1
      · exact absurd (h0 ▸ zero_mem_ival ρ) hy0
      · by_cases hneg : y 1 < -(ρ : ℤ)
        · refine Finset.sum_eq_zero fun k hk => if_neg ?_
          simp only [ival, Finset.mem_Icc] at hk
          omega
        · have hall : ∀ k ∈ ival ρ, k ≤ y 1 := by
            intro k hk
            simp only [ival, Finset.mem_Icc] at hk hy1
            omega
          rw [Finset.sum_congr rfl fun k hk => if_pos (hall k hk), hrow0]
    · rfl

/-- **The `ℓ¹` bound of the field**: `Σ_j Σ_y |G_j(y)| ≤ 3 (2ρ + 1) Σ |g|`. -/
theorem sum_abs_boxField_le (j : Fin 2) :
    ∑ y ∈ supBox 0 ρ, |boxField ρ g j y| ≤ 2 * (2 * ρ + 1) * ∑ y ∈ supBox 0 ρ, |g y| := by
  have habs : ∑ y ∈ supBox 0 ρ, |g y| = ∑ k ∈ ival ρ, ∑ l ∈ ival ρ, |g (pt l k)| :=
    sum_supBox_zero ρ fun y => |g y|
  have hrow : ∀ k, |rowSum ρ g k| ≤ ∑ l ∈ ival ρ, |g (pt l k)| := fun k =>
    Finset.abs_sum_le_sum_abs _ _
  have hnn : ∀ k, 0 ≤ ∑ l ∈ ival ρ, |g (pt l k)| := fun k =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have htot : ∀ k ∈ ival ρ, ∑ l ∈ ival ρ, |g (pt l k)| ≤ ∑ y ∈ supBox 0 ρ, |g y| := by
    intro k hk
    rw [habs]
    exact Finset.single_le_sum (f := fun k => ∑ l ∈ ival ρ, |g (pt l k)|)
      (fun k _ => hnn k) hk
  rw [sum_supBox_zero ρ fun y => |boxField ρ g j y|]
  fin_cases j
  · simp only [boxField, pt_zero, pt_one, abs_neg]
    have hpt : ∀ k (l' : ℤ), |∑ l ∈ ival ρ, (if l ≤ l' then g (pt l k) -
        (if l = 0 then rowSum ρ g k else 0) else 0)| ≤ 2 * ∑ l ∈ ival ρ, |g (pt l k)| := by
      intro k l'
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l ∈ ival ρ, |(if l ≤ l' then g (pt l k) -
            (if l = 0 then rowSum ρ g k else 0) else 0)|
          ≤ ∑ l ∈ ival ρ, (|g (pt l k)| + (if l = 0 then |rowSum ρ g k| else 0)) := by
            refine Finset.sum_le_sum fun l _ => ?_
            by_cases h1 : l ≤ l' <;> by_cases h2 : l = 0
            · rw [if_pos h1, if_pos h2, if_pos h2]; exact abs_sub _ _
            · rw [if_pos h1, if_neg h2, if_neg h2, sub_zero, add_zero]
            · rw [if_neg h1, if_pos h2, abs_zero]; positivity
            · rw [if_neg h1, if_neg h2, abs_zero, add_zero]; exact abs_nonneg _
        _ = ∑ l ∈ ival ρ, |g (pt l k)| + |rowSum ρ g k| := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (ival ρ) 0,
              if_pos (zero_mem_ival ρ)]
        _ ≤ 2 * ∑ l ∈ ival ρ, |g (pt l k)| := by linarith [hrow k]
    calc ∑ k ∈ ival ρ, ∑ l' ∈ ival ρ, |∑ l ∈ ival ρ, (if l ≤ l' then g (pt l k) -
          (if l = 0 then rowSum ρ g k else 0) else 0)|
        ≤ ∑ k ∈ ival ρ, ∑ _l' ∈ ival ρ, 2 * ∑ l ∈ ival ρ, |g (pt l k)| :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l' _ => hpt k l'
      _ = (2 * ρ + 1) * (2 * ∑ k ∈ ival ρ, ∑ l ∈ ival ρ, |g (pt l k)|) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul, card_ival]
      _ = 2 * (2 * ρ + 1) * ∑ y ∈ supBox 0 ρ, |g y| := by rw [habs]; ring
  · simp only [boxField, pt_zero, pt_one]
    have hpt : ∀ k (l' : ℤ), |(if l' = 0 then -∑ k' ∈ ival ρ,
        (if k' ≤ k then rowSum ρ g k' else 0) else 0)| ≤
        if l' = 0 then ∑ y ∈ supBox 0 ρ, |g y| else 0 := by
      intro k l'
      split_ifs
      · rw [abs_neg]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [habs]
        refine Finset.sum_le_sum fun k' _ => ?_
        split_ifs
        · exact hrow k'
        · simp only [abs_zero]; exact hnn k'
      · simp
    have hS0 : 0 ≤ ∑ y ∈ supBox 0 ρ, |g y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc ∑ k ∈ ival ρ, ∑ l' ∈ ival ρ, |(if l' = 0 then -∑ k' ∈ ival ρ,
          (if k' ≤ k then rowSum ρ g k' else 0) else 0)|
        ≤ ∑ k ∈ ival ρ, ∑ l' ∈ ival ρ, (if l' = 0 then ∑ y ∈ supBox 0 ρ, |g y| else 0) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l' _ => hpt k l'
      _ = (2 * ρ + 1) * ∑ y ∈ supBox 0 ρ, |g y| := by
          simp only [Finset.sum_ite_eq' (ival ρ) 0, if_pos (zero_mem_ival ρ),
            Finset.sum_const, nsmul_eq_mul, card_ival]
      _ ≤ 2 * (2 * ρ + 1) * ∑ y ∈ supBox 0 ρ, |g y| := by
          have : (0 : ℝ) ≤ 2 * ρ + 1 := by positivity
          nlinarith

end Field

end Rigidity.Poincare

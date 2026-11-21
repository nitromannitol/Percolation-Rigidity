import Rigidity.Proofs.Percolation.PlanarSolenoidalField

/-!
# Gradients are orthogonal to finitely supported solenoidal fields

For a finitely supported lattice vector field `F` which is divergence free,
`∑_x ∑_i (w(x + e_i) - w(x)) F(x, i) = 0` for every function `w` (summation by parts). Applied to
the solenoidal field of scale `n`, this is display (5.28) in the proof of Lemma 5.7 of Armstrong
and Dario, `|⟨∇w, g⟩| ≤ C 3⁻ⁿ ∑ |∇w|`, with right side `0` (in dimension two).
-/

open LatticeProb.Percolation

namespace Rigidity.Percolation

/-- **Summation by parts against a divergence-free field.** -/
theorem tsum_sum_grad_mul_eq_zero {F : Vertex 2 → Fin 2 → ℝ} (S : Finset (Vertex 2))
    (hS : ∀ x ∉ S, ∀ i, F x i = 0)
    (hdiv : ∀ x, ∑ i : Fin 2, (F x i - F (x - unitVertex i) i) = 0) (w : Vertex 2 → ℝ) :
    ∑' x, ∑ i : Fin 2, (w (x + unitVertex i) - w x) * F x i = 0 := by
  have hA : ∀ i, Summable fun x => w (x + unitVertex i) * F x i := fun i =>
    summable_of_ne_finset_zero (s := S) fun x hx => by rw [hS x hx i, mul_zero]
  have hB : ∀ i, Summable fun x => w x * F x i := fun i =>
    summable_of_ne_finset_zero (s := S) fun x hx => by rw [hS x hx i, mul_zero]
  have hC : ∀ i, Summable fun y => w y * F (y - unitVertex i) i := fun i =>
    summable_of_ne_finset_zero (s := S.image (· + unitVertex i)) fun y hy => by
      have : y - unitVertex i ∉ S := fun h =>
        hy (Finset.mem_image.2 ⟨_, h, sub_add_cancel y _⟩)
      rw [hS _ this i, mul_zero]
  have hshift : ∀ i, ∑' x, w (x + unitVertex i) * F x i =
      ∑' y, w y * F (y - unitVertex i) i := fun i => by
    rw [← (Equiv.subRight (unitVertex i)).tsum_eq]
    simp [Equiv.subRight_apply, sub_add_cancel]
  have hpt : (fun x => ∑ i : Fin 2, (w (x + unitVertex i) - w x) * F x i) = fun x =>
      (w (x + unitVertex 0) * F x 0 + w (x + unitVertex 1) * F x 1) -
        (w x * F x 0 + w x * F x 1) := by
    funext x
    rw [Fin.sum_univ_two]
    ring
  rw [hpt, Summable.tsum_sub ((hA 0).add (hA 1)) ((hB 0).add (hB 1)),
    Summable.tsum_add (hA 0) (hA 1), Summable.tsum_add (hB 0) (hB 1), hshift 0, hshift 1,
    ← Summable.tsum_add (hC 0) (hC 1), ← Summable.tsum_add (hB 0) (hB 1),
    ← Summable.tsum_sub ((hC 0).add (hC 1)) ((hB 0).add (hB 1))]
  have hz : ∀ y, w y * F (y - unitVertex 0) 0 + w y * F (y - unitVertex 1) 1 -
      (w y * F y 0 + w y * F y 1) = 0 := fun y => by
    have := hdiv y
    rw [Fin.sum_univ_two] at this
    linear_combination (-(w y)) * this
  simp only [hz, tsum_zero]

/-- The solenoidal field of scale `n` vanishes outside a finite box. -/
theorem solenoidalField_eq_zero_of_not_mem (n : ℕ) (e : Fin 2 → ℝ) {x : Vertex 2}
    (hx : x ∉ Finset.Icc (fun _ => -(2 * 3 ^ n + 1 : ℤ)) (fun _ => 2 * 3 ^ n + 1)) (i : Fin 2) :
    solenoidalField n e x i = 0 := by
  apply solenoidalField_eq_zero
  rw [Finset.mem_Icc, not_and_or] at hx
  have hR : ∃ j : Fin 2, (2 * 3 ^ n + 1 : ℤ) < |x j| := by
    rcases hx with h | h
    · rw [Pi.le_def] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, by rw [abs_of_neg (by linarith [pow_pos (by norm_num : (0 : ℤ) < 3) n])]; linarith⟩
    · rw [Pi.le_def] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, by rw [abs_of_pos (by linarith [pow_pos (by norm_num : (0 : ℤ) < 3) n])]; linarith⟩
  obtain ⟨j, hj⟩ := hR
  have hj' : (2 * 3 ^ n + 1 : ℝ) < |(x j : ℝ)| := by exact_mod_cast hj
  have hsup : |(x j : ℝ)| ≤ supNorm x := by
    unfold supNorm
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h3 : (0 : ℝ) ≤ 3 ^ n := by positivity
  linarith

/-- **Gradients are orthogonal to the solenoidal field** (Armstrong and Dario, display (5.28) with
right side `0`, in dimension two). -/
theorem tsum_sum_grad_mul_solenoidalField (n : ℕ) (e : Fin 2 → ℝ) (w : Vertex 2 → ℝ) :
    ∑' x, ∑ i : Fin 2, (w (x + unitVertex i) - w x) * solenoidalField n e x i = 0 :=
  tsum_sum_grad_mul_eq_zero _ (fun _ hx i => solenoidalField_eq_zero_of_not_mem n e hx i)
    (sum_solenoidalField_sub_eq_zero n e) w

end Rigidity.Percolation

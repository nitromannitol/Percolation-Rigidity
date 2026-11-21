import Rigidity.Proofs.Dirichlet.CubeCutoff

/-!
# The interior `H²` estimate on a cube

For constant conductances `λ ≤ a_j ≤ Λ`, `v` harmonic on a set containing the cube `Q` and
`r ≥ 1`, the second differences of `v` at the points `x` where the cutoff `η_Q` equals `1` at all
`x + e_j` are bounded by the first differences on a set `S'` containing the edges at `Q`:
`Σ_{x∈I} Σ_j (∇_j∇_i v(x))² ≤ 10 d Λ / (λ r²) Σ_{x∈S'} (∇_i v(x))²`.

This is the discrete form of the interior `H²` estimate (6.30) of Armstrong–Dario for the
homogenized solution, `3^l (⨍_{□°} |∇∇u_hom|²)^{1/2} ≤ C M`, with `r ≃ 3^l` the distance from
`□°` to `∂□_m`; the right side is the `L²` norm of the gradient, which is at most the `L^t` norm
used in the source.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Interior `H²` estimate on a cube.** -/
theorem sum_sq_second_difference_le (a : Fin d → ℝ) {lam Λ : ℝ} (hlam : 0 < lam)
    (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) {U : Finset (Site d)} (Q : IntegerCube d)
    (hQU : Q.vertices ⊆ U) {v : Site d → ℝ}
    (hv : ∀ x ∈ U, condLaplacian (constCond a) v x = 0) (i : Fin d) {r : ℕ} (hr : 0 < r)
    {S S' I : Finset (Site d)} (hS : CoversEdges Q.vertices S)
    (hS' : ∀ x ∈ S, x ∈ S' ∧ ∀ j : Fin d, x + unit j ∈ S')
    (hI : ∀ x ∈ I, x ∈ S ∧ ∀ j : Fin d, cubeCutoff Q r (x + unit j) = 1) :
    ∑ x ∈ I, ∑ j : Fin d,
        ((v (x + unit j + unit i) - v (x + unit j)) - (v (x + unit i) - v x)) ^ 2 ≤
      10 * d * Λ / (lam * (r : ℝ) ^ 2) * ∑ x ∈ S', (v (x + unit i) - v x) ^ 2 := by
  classical
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have ha0 : ∀ j, 0 ≤ a j := fun j => hlam.le.trans (ha j).1
  have hΛ : 0 ≤ Λ := (ha0 ⟨0, by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · exact absurd i.isLt (by omega)
    · exact hd⟩).trans (ha _).2
  have hmain := sum_cubeCutoff_second_difference_le a ha0 Q hQU hv i (r := r) hS
  set D : Site d → Fin d → ℝ := fun x j =>
    ((v (x + unit j + unit i) - v (x + unit j)) - (v (x + unit i) - v x)) ^ 2
  set G : Site d → ℝ := fun x => (v (x + unit i) - v x) ^ 2
  have hG : ∀ x, 0 ≤ G x := fun x => sq_nonneg _
  -- lower bound of the left side
  have hlow : lam * ∑ x ∈ I, ∑ j : Fin d, D x j ≤
      ∑ x ∈ S, ∑ j : Fin d, cubeCutoff Q r (x + unit j) ^ 2 * a j * D x j := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun x hx => ?_) (Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => (hI x hx).1) fun x _ _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (ha0 j)) (sq_nonneg _))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [(hI x hx).2 j, one_pow, one_mul]
    exact mul_le_mul_of_nonneg_right (ha j).1 (sq_nonneg _)
  -- upper bound of the right side
  have hshiftj : ∀ j : Fin d, ∑ x ∈ S, G (x + unit j) ≤ ∑ x ∈ S', G x := by
    intro j
    calc ∑ x ∈ S, G (x + unit j) = ∑ y ∈ S.map (addRightEmbedding (unit j)), G y := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ x ∈ S', G x := Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
          exact (hS' x hx).2 j) fun _ _ _ => hG _
  have hSS' : ∑ x ∈ S, G x ≤ ∑ x ∈ S', G x :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (hS' x hx).1) fun _ _ _ => hG _
  have hpt : ∀ x ∈ S, ∑ j : Fin d, a j * (G (x + unit j) + G x) ≤
      Λ * ∑ j : Fin d, G (x + unit j) + Λ * d * G x := by
    intro x _
    calc ∑ j : Fin d, a j * (G (x + unit j) + G x)
        ≤ ∑ j : Fin d, Λ * (G (x + unit j) + G x) := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (ha j).2 (add_nonneg (hG _) (hG _))
      _ = Λ * ∑ j : Fin d, G (x + unit j) + Λ * d * G x := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  have hup : ∑ x ∈ S, ∑ j : Fin d, a j * (G (x + unit j) + G x) ≤
      2 * d * Λ * ∑ x ∈ S', G x := by
    calc ∑ x ∈ S, ∑ j : Fin d, a j * (G (x + unit j) + G x)
        ≤ ∑ x ∈ S, (Λ * ∑ j : Fin d, G (x + unit j) + Λ * d * G x) := Finset.sum_le_sum hpt
      _ = Λ * ∑ j : Fin d, ∑ x ∈ S, G (x + unit j) + Λ * d * ∑ x ∈ S, G x := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      _ ≤ Λ * ∑ _j : Fin d, ∑ x ∈ S', G x + Λ * d * ∑ x ∈ S', G x :=
          add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hshiftj j) hΛ)
            (mul_le_mul_of_nonneg_left hSS' (mul_nonneg hΛ (Nat.cast_nonneg d)))
      _ = 2 * d * Λ * ∑ x ∈ S', G x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hfin : lam * ∑ x ∈ I, ∑ j : Fin d, D x j ≤
      10 * d * Λ / (r : ℝ) ^ 2 * ∑ x ∈ S', G x := by
    calc lam * ∑ x ∈ I, ∑ j : Fin d, D x j
        ≤ 5 * (1 / (r : ℝ)) ^ 2 * ∑ x ∈ S, ∑ j : Fin d, a j * (G (x + unit j) + G x) :=
          hlow.trans hmain
      _ ≤ 5 * (1 / (r : ℝ)) ^ 2 * (2 * d * Λ * ∑ x ∈ S', G x) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = 10 * d * Λ / (r : ℝ) ^ 2 * ∑ x ∈ S', G x := by
          field_simp
          ring
  calc ∑ x ∈ I, ∑ j : Fin d, D x j = (lam * ∑ x ∈ I, ∑ j : Fin d, D x j) / lam := by
        field_simp
    _ ≤ (10 * d * Λ / (r : ℝ) ^ 2 * ∑ x ∈ S', G x) / lam :=
        div_le_div_of_nonneg_right hfin hlam.le
    _ = 10 * d * Λ / (lam * (r : ℝ) ^ 2) * ∑ x ∈ S', G x := by
        field_simp

end Rigidity.Dirichlet

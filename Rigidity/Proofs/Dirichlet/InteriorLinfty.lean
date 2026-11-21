import Rigidity.Proofs.Dirichlet.DiscreteSobolev
import Rigidity.Proofs.Dirichlet.CubeCutoff

/-!
# Interior estimates for constant-coefficient harmonic functions

For constant conductances `λ ≤ a_k ≤ Λ` and `h` harmonic on the points of a cube `Q` off its
outer slices, the Caccioppoli inequality with the cube cutoff gives
`Σ_{shrink(Q, r+2)} Σ_j (∇_j h)² ≤ 10 d Λ/(λ r²) Σ_Q h²`. Since mixed differences of harmonic
functions are harmonic, iterating along nested cubes bounds `Σ (∂^S h)²` on the cube shrunk
`|S|` times by `(10 d Λ/(λ r²))^{|S|} Σ_Q h²`.

These are the interior estimates of all orders used, with the discrete Sobolev inequality, for
the large-scale regularity of the discrete homogenized solutions.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The cube `Q` shrunk by `t` on every side. -/
def shrinkCube (Q : IntegerCube d) (t : ℕ) : IntegerCube d :=
  ⟨Q.corner + fun _ => (t : ℤ), Q.size - 2 * t⟩

theorem mem_shrinkCube_iff (Q : IntegerCube d) (t : ℕ) (x : Vertex d) :
    x ∈ (shrinkCube Q t).vertices ↔
      ∀ k, Q.corner k + t ≤ x k ∧ x k < Q.corner k + t + ((Q.size - 2 * t : ℕ) : ℤ) := by
  rw [IntegerCube.mem_vertices]
  simp [shrinkCube]

/-- **Caccioppoli inequality on a cube**: for `λ ≤ a_k ≤ Λ`, `λ > 0`, `r ≥ 1` and `h` harmonic
on `shrink(Q, 1)`, `Σ_{shrink(Q, r+2)} Σ_j (∇_j h)² ≤ 10 d Λ/(λ r²) Σ_Q h²`. -/
theorem sum_sq_grad_shrinkCube_le (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ} (hlam : 0 < lam)
    (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (Q : IntegerCube d) {h : Vertex d → ℝ}
    (hh : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) h x = 0) {r : ℕ}
    (hr : 0 < r) :
    ∑ x ∈ (shrinkCube Q (r + 2)).vertices, ∑ j : Fin d, (h (x + unit j) - h x) ^ 2 ≤
      10 * d * Λ / (lam * (r : ℝ) ^ 2) * ∑ x ∈ Q.vertices, h x ^ 2 := by
  classical
  have ha0 : ∀ j, 0 ≤ a j := fun j => hlam.le.trans (ha j).1
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set Q₁ := shrinkCube Q 1
  set η := cubeCutoff Q₁ r
  have hS : CoversEdges Q₁.vertices Q.vertices := by
    intro x j hx
    rw [IntegerCube.mem_vertices]
    intro k
    rcases hx with hx | hx
    · have := (mem_shrinkCube_iff Q 1 x).mp hx k
      push_cast at this
      constructor <;> omega
    · have := (mem_shrinkCube_iff Q 1 _).mp hx k
      rw [add_unit_apply] at this
      push_cast at this
      split_ifs at this <;> constructor <;> omega
  have hη : ∀ x, x ∉ Q₁.vertices → η x = 0 := fun x hx => by
    by_contra hne
    exact hx (mem_vertices_of_cubeCutoff_ne_zero Q₁ r hne).1
  have hcacc := sum_cutoff_energy_le (constCond a) (fun e => ha0 e.2) hS h η 0 hh hη
  simp only [constCond, sub_zero] at hcacc
  -- lower bound of the left side
  have hlow : lam * ∑ x ∈ (shrinkCube Q (r + 2)).vertices, ∑ j : Fin d, (h (x + unit j) - h x) ^ 2
      ≤ ∑ x ∈ Q.vertices, ∑ j : Fin d, η (x + unit j) ^ 2 * a j * (h (x + unit j) - h x) ^ 2 := by
    have hsub : (shrinkCube Q (r + 2)).vertices ⊆ Q.vertices := by
      intro x hx
      rw [IntegerCube.mem_vertices]
      intro k
      have := (mem_shrinkCube_iff Q (r + 2) x).mp hx k
      push_cast at this
      constructor <;> omega
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun x hx => ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun x _ _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (ha0 j)) (sq_nonneg _))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hone : η (x + unit j) = 1 := by
      refine cubeCutoff_eq_one Q₁ hr fun k => ?_
      have := (mem_shrinkCube_iff Q (r + 2) x).mp hx k
      rw [add_unit_apply]
      simp only [Q₁, shrinkCube, Pi.add_apply]
      push_cast at this ⊢
      split_ifs <;> constructor <;> omega
    rw [hone, one_pow, one_mul]
    exact mul_le_mul_of_nonneg_right (ha j).1 (sq_nonneg _)
  -- upper bound of the right side
  have hup : ∑ x ∈ Q.vertices, ∑ j : Fin d, a j * (η (x + unit j) - η x) ^ 2 *
      (h (x + unit j) ^ 2 + h x ^ 2) ≤
        (1 / (r : ℝ)) ^ 2 * Λ * (2 * d * ∑ x ∈ Q.vertices, h x ^ 2) := by
    have hpt : ∀ x ∈ Q.vertices, ∀ j : Fin d, a j * (η (x + unit j) - η x) ^ 2 *
        (h (x + unit j) ^ 2 + h x ^ 2) ≤ (1 / (r : ℝ)) ^ 2 * Λ *
          ((if x + unit j ∈ Q.vertices then h (x + unit j) ^ 2 else 0) + h x ^ 2) := by
      intro x _ j
      have hK : (η (x + unit j) - η x) ^ 2 ≤ (1 / (r : ℝ)) ^ 2 := by
        have := abs_cubeCutoff_add_unit_sub_le Q₁ r x j
        nlinarith [abs_nonneg (η (x + unit j) - η x), sq_abs (η (x + unit j) - η x)]
      by_cases hxj : x + unit j ∈ Q.vertices
      · rw [if_pos hxj]
        have h1 : a j * (η (x + unit j) - η x) ^ 2 ≤ Λ * (1 / (r : ℝ)) ^ 2 :=
          mul_le_mul (ha j).2 hK (sq_nonneg _) ((ha0 j).trans (ha j).2)
        nlinarith [mul_le_mul_of_nonneg_right h1 (add_nonneg (sq_nonneg (h (x + unit j)))
          (sq_nonneg (h x)))]
      · -- the cutoff vanishes at both endpoints
        have hη1 : η (x + unit j) = 0 := by
          by_contra hne
          have := (mem_vertices_of_cubeCutoff_ne_zero Q₁ r hne).1
          apply hxj
          rw [IntegerCube.mem_vertices]
          intro k
          have h2 := (mem_shrinkCube_iff Q 1 _).mp this k
          push_cast at h2
          constructor <;> omega
        have hη0 : η x = 0 := by
          by_contra hne
          obtain ⟨_, hnb⟩ := mem_vertices_of_cubeCutoff_ne_zero Q₁ r hne
          apply hxj
          rw [IntegerCube.mem_vertices]
          intro k
          have h2 := (mem_shrinkCube_iff Q 1 _).mp (hnb j).1 k
          push_cast at h2
          constructor <;> omega
        rw [hη1, hη0, if_neg hxj]
        simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          zero_mul, zero_add]
        exact mul_nonneg (mul_nonneg (by positivity) ((ha0 j).trans (ha j).2)) (sq_nonneg _)
    have hΛ : 0 ≤ (1 / (r : ℝ)) ^ 2 * Λ :=
      mul_nonneg (by positivity) ((ha0 ⟨0, hd⟩).trans (ha ⟨0, hd⟩).2)
    have hshift : ∀ j : Fin d, ∑ x ∈ Q.vertices,
        (if x + unit j ∈ Q.vertices then h (x + unit j) ^ 2 else 0) ≤
          ∑ x ∈ Q.vertices, h x ^ 2 := by
      intro j
      rw [← Finset.sum_filter]
      calc ∑ x ∈ Q.vertices.filter (fun x => x + unit j ∈ Q.vertices), h (x + unit j) ^ 2
          = ∑ y ∈ (Q.vertices.filter (fun x => x + unit j ∈ Q.vertices)).map
              (addRightEmbedding (unit j)), h y ^ 2 := by
            rw [Finset.sum_map]
            rfl
        _ ≤ ∑ x ∈ Q.vertices, h x ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => by
              obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
              exact (Finset.mem_filter.mp hx).2) fun _ _ _ => sq_nonneg _
    refine (Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j _ => hpt x hx j).trans ?_
    rw [Finset.sum_comm]
    calc ∑ j : Fin d, ∑ x ∈ Q.vertices, (1 / (r : ℝ)) ^ 2 * Λ *
          ((if x + unit j ∈ Q.vertices then h (x + unit j) ^ 2 else 0) + h x ^ 2)
        ≤ ∑ _j : Fin d, (1 / (r : ℝ)) ^ 2 * Λ * (2 * ∑ x ∈ Q.vertices, h x ^ 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          exact mul_le_mul_of_nonneg_left (by linarith [hshift j]) hΛ
      _ = (1 / (r : ℝ)) ^ 2 * Λ * (2 * d * ∑ x ∈ Q.vertices, h x ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc ∑ x ∈ (shrinkCube Q (r + 2)).vertices, ∑ j : Fin d, (h (x + unit j) - h x) ^ 2
      = (lam * ∑ x ∈ (shrinkCube Q (r + 2)).vertices, ∑ j : Fin d,
          (h (x + unit j) - h x) ^ 2) / lam := by
        field_simp
    _ ≤ (5 * ((1 / (r : ℝ)) ^ 2 * Λ * (2 * d * ∑ x ∈ Q.vertices, h x ^ 2))) / lam :=
        div_le_div_of_nonneg_right ((hlow.trans hcacc).trans
          (mul_le_mul_of_nonneg_left hup (by norm_num))) hlam.le
    _ = 10 * d * Λ / (lam * (r : ℝ) ^ 2) * ∑ x ∈ Q.vertices, h x ^ 2 := by
        field_simp
        ring

end Rigidity.Dirichlet

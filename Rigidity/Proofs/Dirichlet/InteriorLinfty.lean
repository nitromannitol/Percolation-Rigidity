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

theorem shrinkCube_zero_vertices (Q : IntegerCube d) : (shrinkCube Q 0).vertices = Q.vertices := by
  ext x
  rw [mem_shrinkCube_iff, IntegerCube.mem_vertices]
  simp

theorem shrinkCube_shrinkCube_vertices (Q : IntegerCube d) (s t : ℕ) :
    (shrinkCube (shrinkCube Q s) t).vertices = (shrinkCube Q (s + t)).vertices := by
  ext x
  rw [mem_shrinkCube_iff, mem_shrinkCube_iff]
  simp only [shrinkCube, Pi.add_apply]
  refine forall_congr' fun k => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> push_cast at * <;> omega

theorem sum_unit_apply (R : Finset (Fin d)) (k : Fin d) :
    (∑ j ∈ R, unit j) k = if k ∈ R then 1 else 0 := by
  simp [unit, Finset.sum_apply, Pi.single_apply]

/-- **Interior estimates of all orders**: for `h` harmonic on `shrink(Q, 1)` and every set `S` of
coordinates, `Σ_{shrink(Q, |S|(r+2))} (∂^S h)² ≤ (10 d Λ/(λ r²))^{|S|} Σ_Q h²`. -/
theorem sum_sq_mixedDiff_shrinkCube_le (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (Q : IntegerCube d) {h : Vertex d → ℝ}
    (hh : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) h x = 0) {r : ℕ}
    (hr : 0 < r) (S : Finset (Fin d)) :
    ∑ x ∈ (shrinkCube Q (S.card * (r + 2))).vertices, mixedDiff S h x ^ 2 ≤
      (10 * d * Λ / (lam * (r : ℝ) ^ 2)) ^ S.card * ∑ x ∈ Q.vertices, h x ^ 2 := by
  classical
  have hC : 0 ≤ 10 * d * Λ / (lam * (r : ℝ) ^ 2) := by
    have := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
    positivity
  induction S using Finset.induction_on with
  | empty => simp [shrinkCube_zero_vertices, mixedDiff_empty]
  | insert k S hk ih =>
    set Q' := shrinkCube Q (S.card * (r + 2))
    set g := mixedDiff S h
    have hg : ∀ x ∈ (shrinkCube Q' 1).vertices, condLaplacian (constCond a) g x = 0 := by
      intro y hy
      refine condLaplacian_constCond_mixedDiff_eq_zero a S (U := ↑(shrinkCube Q 1).vertices)
        (fun x hx => hh x hx) fun R hR => ?_
      rw [Finset.mem_coe, mem_shrinkCube_iff]
      rw [shrinkCube_shrinkCube_vertices, mem_shrinkCube_iff] at hy
      intro m
      have hym := hy m
      rw [Pi.add_apply, sum_unit_apply]
      obtain ⟨t, ht⟩ : ∃ t, t = S.card * (r + 2) := ⟨_, rfl⟩
      rw [← ht] at hym
      rcases Nat.eq_zero_or_pos S.card with h0 | h0
      · have hRe : R = ∅ := by
          have := Finset.card_eq_zero.mp h0
          subst this
          exact Finset.subset_empty.mp hR
        subst hRe
        have ht0 : t = 0 := by rw [ht, h0, zero_mul]
        subst ht0
        simp only [Finset.notMem_empty, if_false, add_zero]
        push_cast at hym ⊢
        omega
      · have h1 : 1 ≤ t := by
          rw [ht]
          exact Nat.one_le_iff_ne_zero.mpr (by positivity)
        push_cast at hym ⊢
        split_ifs <;> constructor <;> omega
    have hcc := sum_sq_grad_shrinkCube_le hd a hlam ha Q' hg hr
    rw [shrinkCube_shrinkCube_vertices] at hcc
    rw [Finset.card_insert_of_notMem hk, pow_succ]
    have hshape : (S.card + 1) * (r + 2) = S.card * (r + 2) + (r + 2) := by ring
    rw [hshape]
    calc ∑ x ∈ (shrinkCube Q (S.card * (r + 2) + (r + 2))).vertices,
          mixedDiff (insert k S) h x ^ 2
        ≤ ∑ x ∈ (shrinkCube Q (S.card * (r + 2) + (r + 2))).vertices,
            ∑ j : Fin d, (g (x + unit j) - g x) ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [mixedDiff_insert hk]
          exact Finset.single_le_sum (f := fun j => (g (x + unit j) - g x) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ k)
      _ ≤ 10 * d * Λ / (lam * (r : ℝ) ^ 2) * ∑ x ∈ Q'.vertices, g x ^ 2 := hcc
      _ ≤ 10 * d * Λ / (lam * (r : ℝ) ^ 2) *
            ((10 * d * Λ / (lam * (r : ℝ) ^ 2)) ^ S.card * ∑ x ∈ Q.vertices, h x ^ 2) :=
          mul_le_mul_of_nonneg_left ih hC
      _ = _ := by ring

theorem shrinkCube_vertices_subset (Q : IntegerCube d) {s t : ℕ} (hst : s ≤ t) :
    (shrinkCube Q t).vertices ⊆ (shrinkCube Q s).vertices := by
  intro x hx
  rw [mem_shrinkCube_iff] at hx ⊢
  intro k
  have := hx k
  constructor <;> omega

/-- `Σ_T |f| ≤ √#T √(Σ_T f²)`. -/
theorem sum_abs_le_sqrt_card_mul_sqrt {ι : Type*} (T : Finset ι) (f : ι → ℝ) :
    ∑ x ∈ T, |f x| ≤ √(#T : ℝ) * √(∑ x ∈ T, f x ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  have h := sq_sum_le_card_mul_sum_sq (s := T) (f := fun x => |f x|)
  simpa only [sq_abs] using h

/-- **Interior `L^∞` bound for constant-coefficient harmonic functions**: for `h` harmonic on
`shrink(Q, 1)`, `r ≥ 1`, `M ≥ 1` and a cube `x + {0, …, M − 1}^d` inside `shrink(Q, d(r + 2))`,
`|h(x)| ≤ Σ_{S} M^{|S| − d} M^{d/2} ((10 d Λ/(λ r²))^{|S|} Σ_Q h²)^{1/2}`. -/
theorem abs_le_of_condLaplacian_constCond_eq_zero (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (Q : IntegerCube d) {h : Vertex d → ℝ}
    (hh : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) h x = 0) {r : ℕ}
    (hr : 0 < r) {x : Vertex d} {M : ℕ} (hM : 0 < M)
    (hxM : (cornerCube x M).vertices ⊆ (shrinkCube Q (d * (r + 2))).vertices) :
    |h x| ≤ ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, (1 / (M : ℝ)) ^ (d - S.card) *
      (√((M : ℝ) ^ d) * √((10 * d * Λ / (lam * (r : ℝ) ^ 2)) ^ S.card *
        ∑ y ∈ Q.vertices, h y ^ 2)) := by
  refine (abs_le_sum_mixedDiff_cube h x hM).trans (Finset.sum_le_sum fun S _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcard : (#(cornerCube x M).vertices : ℝ) = (M : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  refine (sum_abs_le_sqrt_card_mul_sqrt _ _).trans ?_
  rw [hcard]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  have hS : S.card ≤ d := by
    have := Finset.card_le_univ S
    simpa using this
  have hsub : (cornerCube x M).vertices ⊆ (shrinkCube Q (S.card * (r + 2))).vertices :=
    hxM.trans (shrinkCube_vertices_subset Q (Nat.mul_le_mul_right _ hS))
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _) ?_
  exact sum_sq_mixedDiff_shrinkCube_le hd a hlam ha Q hh hr S

end Rigidity.Dirichlet

import Rigidity.Proofs.Dirichlet.BoundaryLayer

/-!
# Gradients of cube averages

For an integer cube `Q` of side `N` and a direction `i`, the sum over `Q` of the differences
`∇_i g(x) = g(x + e_i) − g(x)` splits into the sum over the edges of `Q` (both endpoints in `Q`) and
the sum over the upper face of `Q` in the direction `i`, whose `N^{d-1}` points give, by
Cauchy–Schwarz, `(N^{-d} Σ_{face} h)² ≤ N^{-1} N^{-d} Σ_Q h²`. The discrete gradient of the cube
average `ξ(y) = N^{-d} Σ_{y + □} g` is the cube average of the discrete gradient.

Together these are the discrete form of Step 2 of the proof of Armstrong–Dario, Lemma 6.2
(display (6.21) there): the average over a mesoscopic cube `y + □_n` of the gradient of the
interpolation differs from the average of the gradient of the coarsened function over the edges
of `y + □_n` by at most `C 3^{-n}` times its normalized `L²` norm, in square.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

theorem add_unit_apply (x : Vertex d) (i k : Fin d) :
    (x + unit i) k = x k + if k = i then 1 else 0 := by
  simp [unit, Pi.single_apply]

/-- A point of `Q` moved by `e_i` stays in `Q` exactly when it is not on the upper face in the
direction `i`. -/
theorem add_unit_mem_vertices_iff (Q : IntegerCube d) {x : Vertex d} (hx : x ∈ Q.vertices)
    (i : Fin d) : x + unit i ∈ Q.vertices ↔ x ∉ Q.upperFace i := by
  rw [IntegerCube.mem_vertices] at hx
  rw [IntegerCube.mem_vertices, IntegerCube.mem_upperFace, IntegerCube.mem_vertices]
  constructor
  · intro h ⟨_, hi⟩
    have := (h i).2
    rw [add_unit_apply, if_pos rfl] at this
    omega
  · intro h k
    rw [add_unit_apply]
    by_cases hk : k = i
    · subst hk
      rw [if_pos rfl]
      have := (hx k).2
      have hne : x k + 1 ≠ Q.corner k + (Q.size : ℤ) := fun he => h ⟨hx, he⟩
      exact ⟨by linarith [(hx k).1], by omega⟩
    · rw [if_neg hk, add_zero]
      exact hx k

/-- The upper face of a cube of side `N` has at most `N^{d-1}` points. -/
theorem card_upperFace_le (Q : IntegerCube d) (i : Fin d) :
    #(Q.upperFace i) ≤ Q.size ^ (d - 1) := by
  classical
  have hsub : Q.upperFace i ⊆ Fintype.piFinset (Function.update
      (fun k => Finset.Ico (Q.corner k) (Q.corner k + (Q.size : ℤ))) i
      (Finset.Ico (Q.corner i + Q.size - 1) (Q.corner i + Q.size))) := by
    intro x hx
    rw [IntegerCube.mem_upperFace, IntegerCube.mem_vertices] at hx
    refine Fintype.mem_piFinset.mpr fun k => ?_
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self, Finset.mem_Ico]
      omega
    · rw [Function.update_of_ne hk]
      exact Finset.mem_Ico.mpr (hx.1 k)
  refine (Finset.card_le_card hsub).trans ?_
  rw [card_piFinset_update, Int.card_Ico]
  simp

/-- **Edges and the upper face**: `Σ_{x∈Q} ∇_i g(x)` is the sum over the edges of `Q` in the
direction `i` plus the sum over the upper face of `Q`. -/
theorem sum_grad_eq_sum_inner_add_sum_upperFace (Q : IntegerCube d) (i : Fin d)
    (g : Vertex d → ℝ) :
    ∑ x ∈ Q.vertices, (g (x + unit i) - g x) =
      ∑ x ∈ Q.vertices.filter (fun x => x + unit i ∈ Q.vertices), (g (x + unit i) - g x) +
        ∑ x ∈ Q.upperFace i, (g (x + unit i) - g x) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q.vertices (fun x => x + unit i ∈ Q.vertices)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hnot⟩
    by_contra h
    exact hnot ((add_unit_mem_vertices_iff Q hx i).mpr h)
  · intro hx
    have hxQ := (IntegerCube.mem_upperFace Q i x).mp hx
    exact ⟨hxQ.1, fun h => (add_unit_mem_vertices_iff Q hxQ.1 i).mp h hx⟩

/-- **Cauchy–Schwarz on the upper face**: `(N^{-d} Σ_{face} h)² ≤ N^{-1} N^{-d} Σ_Q h²`. -/
theorem sq_sum_upperFace_div_le (Q : IntegerCube d) (hN : 0 < Q.size) (i : Fin d)
    (h : Vertex d → ℝ) :
    ((∑ x ∈ Q.upperFace i, h x) / (Q.size : ℝ) ^ d) ^ 2 ≤
      1 / Q.size * ((∑ x ∈ Q.vertices, h x ^ 2) / (Q.size : ℝ) ^ d) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ i).elim0
  have hN' : (0 : ℝ) < Q.size := by exact_mod_cast hN
  have hface : Q.upperFace i ⊆ Q.vertices := Finset.filter_subset _ _
  have hcs := sq_sum_le_card_mul_sum_sq (s := Q.upperFace i) (f := h)
  have hcard : (#(Q.upperFace i) : ℝ) ≤ (Q.size : ℝ) ^ (d - 1) := by
    exact_mod_cast card_upperFace_le Q i
  have hsq : ∑ x ∈ Q.upperFace i, h x ^ 2 ≤ ∑ x ∈ Q.vertices, h x ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hface fun _ _ _ => sq_nonneg _
  have hpow : (Q.size : ℝ) ^ d = (Q.size : ℝ) ^ (d - 1) * Q.size := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have hS : 0 ≤ ∑ x ∈ Q.vertices, h x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc (∑ x ∈ Q.upperFace i, h x) ^ 2
      ≤ #(Q.upperFace i) * ∑ x ∈ Q.upperFace i, h x ^ 2 := hcs
    _ ≤ (Q.size : ℝ) ^ (d - 1) * ∑ x ∈ Q.vertices, h x ^ 2 :=
        mul_le_mul hcard hsq (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = 1 / Q.size * ((∑ x ∈ Q.vertices, h x ^ 2) / (Q.size : ℝ) ^ d) *
          ((Q.size : ℝ) ^ d) ^ 2 := by
        rw [hpow]
        field_simp

/-- **Mesoscopic gradient comparison** (discrete form of Armstrong–Dario (6.21)): the averages
over `Q` of `∇_i g` over all points and over the edges of `Q` differ, in square, by at most
`N^{-1} N^{-d} Σ_Q (∇_i g)²`. -/
theorem sq_avg_grad_sub_avg_inner_le (Q : IntegerCube d) (hN : 0 < Q.size) (i : Fin d)
    (g : Vertex d → ℝ) :
    ((∑ x ∈ Q.vertices, (g (x + unit i) - g x) -
        ∑ x ∈ Q.vertices.filter (fun x => x + unit i ∈ Q.vertices), (g (x + unit i) - g x)) /
          (Q.size : ℝ) ^ d) ^ 2 ≤
      1 / Q.size * ((∑ x ∈ Q.vertices, (g (x + unit i) - g x) ^ 2) / (Q.size : ℝ) ^ d) := by
  rw [sum_grad_eq_sum_inner_add_sum_upperFace Q i g, add_sub_cancel_left]
  exact sq_sum_upperFace_div_le Q hN i fun x => g (x + unit i) - g x

/-- The cube with corner `y` and side `N`. -/
def cornerCube (y : Vertex d) (N : ℕ) : IntegerCube d := ⟨y, N⟩

/-- Sums over a translated cube are sums of the translated function. -/
theorem sum_cornerCube_add (y z : Vertex d) (N : ℕ) (g : Vertex d → ℝ) :
    ∑ x ∈ (cornerCube (y + z) N).vertices, g x = ∑ x ∈ (cornerCube y N).vertices, g (x + z) := by
  refine Finset.sum_nbij' (fun x => x - z) (fun x => x + z) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [IntegerCube.mem_vertices] at hx ⊢
    intro k
    simp only [cornerCube, Pi.add_apply, Pi.sub_apply] at hx ⊢
    constructor <;> linarith [(hx k).1, (hx k).2]
  · intro x hx
    rw [IntegerCube.mem_vertices] at hx ⊢
    intro k
    simp only [cornerCube, Pi.add_apply] at hx ⊢
    constructor <;> linarith [(hx k).1, (hx k).2]
  · intro x _
    simp
  · intro x _
    simp
  · intro x _
    simp

/-- The average `ξ(y) = N^{-d} Σ_{x ∈ y + □} g(x)` of `g` over the cube with corner `y` and
side `N`. -/
noncomputable def cubeAverage (N : ℕ) (g : Vertex d → ℝ) (y : Vertex d) : ℝ :=
  (∑ x ∈ (cornerCube y N).vertices, g x) / (N : ℝ) ^ d

/-- **The discrete gradient of a cube average is the cube average of the discrete gradient.** -/
theorem cubeAverage_add_unit_sub (N : ℕ) (g : Vertex d → ℝ) (y : Vertex d) (i : Fin d) :
    cubeAverage N g (y + unit i) - cubeAverage N g y =
      (∑ x ∈ (cornerCube y N).vertices, (g (x + unit i) - g x)) / (N : ℝ) ^ d := by
  rw [cubeAverage, cubeAverage, sum_cornerCube_add, ← sub_div, Finset.sum_sub_distrib]

end Rigidity.Dirichlet

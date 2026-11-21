import Rigidity.Proofs.Dirichlet.MesoscopicAffine

/-!
# The coarse-gradient defect summed over the tiles

On each tile `y + □` of side `N`, the mesoscopic slope `p_k(y) = N^{-d} Σ_{y+□} ∇_k w` differs from
the edge average `G_k(y) = N^{-d} Σ_{edges of y+□} ∇_k w` by the upper face terms. Summing over the
tiles with Cauchy–Schwarz, for `0 ≤ a_k ≤ Λ`,
`Σ_i N^d Σ_k |a_k p_k(y_i)| |G_k(y_i) − p_k(y_i)| ≤ Λ N^{-1/2} Σ_{x} Σ_k (∇_k w(x))²`.

This is Step 2 of the proof of Armstrong–Dario, Lemma 6.2 ((6.19)–(6.20)): the term
`Σ_y |q(y)| |⟨∇[u]_𝒫⟩_{y+□_n}/|□_n| − p(y)|` is at most `C 3^{−n/2}` times the energy; on the
lattice `w` is the boundary interpolation `w̃`, equal to `[u]_𝒫` inside.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The edge average `G_k(y)` of `∇_k w` over the edges of the cube `y + □` of side `N`. -/
noncomputable def cubeEdgeSlope (N : ℕ) (w : Vertex d → ℝ) (y : Vertex d) (k : Fin d) : ℝ :=
  (∑ x ∈ (cornerCube y N).vertices.filter (fun x => x + unit k ∈ (cornerCube y N).vertices),
    (w (x + unit k) - w x)) / (N : ℝ) ^ d

/-- The defect on one tile: `(G_k(y) − p_k(y))² ≤ N⁻¹ N^{-d} Σ_{y+□} (∇_k w)²`. -/
theorem sq_cubeEdgeSlope_sub_cubeSlope_le {N : ℕ} (hN : 0 < N) (w : Vertex d → ℝ) (y : Vertex d)
    (k : Fin d) :
    (cubeEdgeSlope N w y k - cubeSlope N w y k) ^ 2 ≤
      1 / N * ((∑ x ∈ (cornerCube y N).vertices, (w (x + unit k) - w x) ^ 2) / (N : ℝ) ^ d) := by
  have h := sq_avg_grad_sub_avg_inner_le (cornerCube y N) hN k w
  simp only [cornerCube] at h
  have e : cubeEdgeSlope N w y k - cubeSlope N w y k =
      -((∑ x ∈ (cornerCube y N).vertices, (w (x + unit k) - w x) -
        ∑ x ∈ (cornerCube y N).vertices.filter (fun x => x + unit k ∈ (cornerCube y N).vertices),
          (w (x + unit k) - w x)) / (N : ℝ) ^ d) := by
    simp only [cubeEdgeSlope, cubeSlope, cubeAverage]
    ring
  rw [e, neg_sq]
  exact h

/-- **The coarse-gradient defect summed over the tiles.** -/
theorem sum_tiles_slope_mul_defect_le (a : Fin d → ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (haΛ : ∀ k, |a k| ≤ Λ) {N : ℕ} (hN : 0 < N) (w : Vertex d → ℝ) (z : Vertex d) (M : ℕ) :
    ∑ i ∈ (cornerCube 0 M).vertices, (N : ℝ) ^ d * ∑ k,
        |a k * cubeSlope N w (z + (N : ℤ) • i) k| *
          |cubeEdgeSlope N w (z + (N : ℤ) • i) k - cubeSlope N w (z + (N : ℤ) • i) k| ≤
      Λ / √(N : ℝ) * ∑ x ∈ (cornerCube z (M * N)).vertices, ∑ k, (w (x + unit k) - w x) ^ 2 := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set I := (cornerCube (0 : Vertex d) M).vertices
  set E := ∑ x ∈ (cornerCube z (M * N)).vertices, ∑ k, (w (x + unit k) - w x) ^ 2
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set A : Vertex d × Fin d → ℝ := fun q => |a q.2 * cubeSlope N w (z + (N : ℤ) • q.1) q.2|
  set B : Vertex d × Fin d → ℝ := fun q =>
    |cubeEdgeSlope N w (z + (N : ℤ) • q.1) q.2 - cubeSlope N w (z + (N : ℤ) • q.1) q.2|
  set T := I ×ˢ (Finset.univ : Finset (Fin d))
  have hLHS : ∑ i ∈ I, (N : ℝ) ^ d * ∑ k,
      |a k * cubeSlope N w (z + (N : ℤ) • i) k| *
        |cubeEdgeSlope N w (z + (N : ℤ) • i) k - cubeSlope N w (z + (N : ℤ) • i) k| =
      (N : ℝ) ^ d * ∑ q ∈ T, A q * B q := by
    rw [← Finset.mul_sum, Finset.sum_product]
  -- the slopes
  have hjensen := sum_tiles_cubeSlope_sq_le (fun _ => (1 : ℝ)) (fun _ => zero_le_one) z M hN w
  simp only [one_mul] at hjensen
  have hA : ∑ q ∈ T, A q ^ 2 ≤ Λ ^ 2 * (E / (N : ℝ) ^ d) := by
    rw [Finset.sum_product]
    have h1 : ∑ i ∈ I, ∑ k, A (i, k) ^ 2 ≤ ∑ i ∈ I, ∑ k, Λ ^ 2 *
        cubeSlope N w (z + (N : ℤ) • i) k ^ 2 := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
      simp only [A, sq_abs, mul_pow]
      exact mul_le_mul_of_nonneg_right (by
        have := haΛ k
        nlinarith [abs_nonneg (a k), sq_abs (a k)]) (sq_nonneg _)
    refine h1.trans ?_
    simp only [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [le_div_iff₀ (by positivity), Finset.sum_mul]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => by ring)) hjensen
  -- the defects
  have hB : ∑ q ∈ T, B q ^ 2 ≤ E / ((N : ℝ) * (N : ℝ) ^ d) := by
    rw [Finset.sum_product]
    have h1 : ∑ i ∈ I, ∑ k, B (i, k) ^ 2 ≤ ∑ i ∈ I, ∑ k, 1 / N *
        ((∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, (w (x + unit k) - w x) ^ 2) /
          (N : ℝ) ^ d) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
        simp only [B, sq_abs]
        exact sq_cubeEdgeSlope_sub_cubeSlope_le hN w _ k
    refine h1.trans (le_of_eq ?_)
    have hE : E = ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        ∑ k, (w (x + unit k) - w x) ^ 2 := sum_cornerCube_mul hN z M _
    rw [hE, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := (cornerCube (z + (N : ℤ) • i) N).vertices), Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  -- Cauchy–Schwarz and the square root
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T A B
  have hAB0 : 0 ≤ ∑ q ∈ T, A q * B q := Finset.sum_nonneg fun q _ =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [hLHS]
  have hlhs0 : 0 ≤ (N : ℝ) ^ d * ∑ q ∈ T, A q * B q := by positivity
  have hrhs0 : 0 ≤ Λ / √(N : ℝ) * E := by positivity
  rw [← pow_le_pow_iff_left₀ hlhs0 hrhs0 two_ne_zero]
  have hsq : (Λ / √(N : ℝ) * E) ^ 2 = Λ ^ 2 * E ^ 2 / N := by
    rw [mul_pow, div_pow, Real.sq_sqrt hN'.le]
    ring
  rw [hsq, mul_pow]
  have hA0 : 0 ≤ ∑ q ∈ T, A q ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ((N : ℝ) ^ d) ^ 2 * (∑ q ∈ T, A q * B q) ^ 2
      ≤ ((N : ℝ) ^ d) ^ 2 * ((∑ q ∈ T, A q ^ 2) * ∑ q ∈ T, B q ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ ((N : ℝ) ^ d) ^ 2 * ((Λ ^ 2 * (E / (N : ℝ) ^ d)) * (E / ((N : ℝ) * (N : ℝ) ^ d))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hA hB (Finset.sum_nonneg fun _ _ =>
          sq_nonneg _) (by positivity)) (by positivity)
    _ = Λ ^ 2 * E ^ 2 / N := by
        field_simp

end Rigidity.Dirichlet

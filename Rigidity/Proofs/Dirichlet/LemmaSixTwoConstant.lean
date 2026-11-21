import Rigidity.Proofs.Dirichlet.LemmaSixTwoHomogenized

/-!
# The `μ` test for constant conductances

For constant conductances `ā` (no percolation) the quantity `μ(x + □, ā p)` is `−p · ā p / 2`, and
the `μ` test of `edgeEnergy_dirichletSolution_div_le_of_mu_test_density` holds with `δ = 0` and
the energy density `e = Σ_k a_k (∇_k w)²` of the datum: by Cauchy–Schwarz the edge average `G_k`
of `∇_k w` satisfies `G_k² ≤ N^{-d} Σ_{x+□} (∇_k w)²`, and `2 p G − p² ≤ G²`
(`mu_test_constCond`). So the hypotheses of the lattice form of Lemma 6.2 are satisfied in this
case (`edgeEnergy_dirichletSolution_div_le_constCond`, and
`edgeEnergy_dirichletSolution_div_le_constCond_trim` for the cutoff on the trimmed cube).
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Cauchy–Schwarz for the edge average**: `G_k(x)² ≤ N^{-d} Σ_{x+□} (∇_k w)²`. -/
theorem sq_cubeEdgeSlope_le (N : ℕ) (w : Vertex d → ℝ) (x : Vertex d) (k : Fin d) :
    cubeEdgeSlope N w x k ^ 2 ≤
      (∑ y ∈ (cornerCube x N).vertices, (w (y + unit k) - w y) ^ 2) / (N : ℝ) ^ d := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [cubeEdgeSlope]
      exact k.elim0
    · simp [cubeEdgeSlope, zero_pow hd.ne']
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  set T := (cornerCube x N).vertices
  set F := T.filter fun y => y + unit k ∈ T
  have hcard : (#T : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  have hF : (#F : ℝ) ≤ (N : ℝ) ^ d := by
    rw [← hcard]
    exact_mod_cast Finset.card_filter_le _ _
  have hcs := sq_sum_le_card_mul_sum_sq (s := F) (f := fun y => w (y + unit k) - w y)
  have hsub : ∑ y ∈ F, (w (y + unit k) - w y) ^ 2 ≤ ∑ y ∈ T, (w (y + unit k) - w y) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ y ∈ F, (w (y + unit k) - w y) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [cubeEdgeSlope, div_pow, div_le_div_iff₀ (by positivity) hNd]
  calc (∑ y ∈ F, (w (y + unit k) - w y)) ^ 2 * (N : ℝ) ^ d
      ≤ (#F * ∑ y ∈ F, (w (y + unit k) - w y) ^ 2) * (N : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hcs hNd.le
    _ ≤ ((N : ℝ) ^ d * ∑ y ∈ T, (w (y + unit k) - w y) ^ 2) * (N : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right (mul_le_mul hF hsub hS0 hNd.le) hNd.le
    _ = (∑ y ∈ T, (w (y + unit k) - w y) ^ 2) * ((N : ℝ) ^ d) ^ 2 := by ring

/-- **The `μ` test for constant conductances.** -/
theorem mu_test_constCond (a : Fin d → ℝ) (ha : ∀ k, 0 ≤ a k) (N : ℕ) (w : Vertex d → ℝ)
    (x : Vertex d) :
    -(∑ k, a k * cubeSlope N w x k ^ 2) / 2 ≤
      (∑ y ∈ (cornerCube x N).vertices, ∑ k, a k * (w (y + unit k) - w y) ^ 2) /
          (N : ℝ) ^ d / 2 -
        ∑ k, a k * cubeSlope N w x k * cubeEdgeSlope N w x k := by
  have hG : ∑ k, a k * cubeEdgeSlope N w x k ^ 2 ≤
      (∑ y ∈ (cornerCube x N).vertices, ∑ k, a k * (w (y + unit k) - w y) ^ 2) /
        (N : ℝ) ^ d := by
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (sq_cubeEdgeSlope_le N w x k) (ha k)
  have hpt : ∑ k, (2 * (a k * cubeSlope N w x k * cubeEdgeSlope N w x k) -
      a k * cubeSlope N w x k ^ 2) ≤ ∑ k, a k * cubeEdgeSlope N w x k ^ 2 :=
    Finset.sum_le_sum fun k _ => by
      nlinarith [mul_nonneg (ha k) (sq_nonneg (cubeSlope N w x k - cubeEdgeSlope N w x k))]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hpt
  linarith

/-- **Lemma 6.2 on the lattice for constant conductances**: the hypotheses of the density form
hold with `μ = −p · ā p / 2`, `δ = 0` and the energy density of the datum. -/
theorem edgeEnergy_dirichletSolution_div_le_constCond (hd : 1 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ k, 0 < a k) {Λ : ℝ} (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 2 ≤ s)
    (B : Finset (Vertex d)) (hB : ∀ x ∈ Q.vertices, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B) :
    edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d ≤
      (∑ y ∈ B, ∑ k, a k * (w (y + unit k) - w y) ^ 2 +
          2 * (Λ / √(N : ℝ) * ∑ y ∈ B, ∑ k, (w (y + unit k) - w y) ^ 2)) / (Q.size : ℝ) ^ d +
        Λ * ((2 * d * ((r + 1 : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s) *
              ∑ y ∈ B, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) / (Q.size : ℝ) ^ d) ^ (2 / s)) := by
  have h := edgeEnergy_dirichletSolution_div_le_of_mu_test_density hd a ha haΛ Q hL hN hr w hs B
    hB (fun x => -(∑ k, a k * cubeSlope N w x k ^ 2) / 2) (fun _ => 0)
    (fun y => ∑ k, a k * (w (y + unit k) - w y) ^ 2)
    (fun y => Finset.sum_nonneg fun k _ => mul_nonneg (ha k).le (sq_nonneg _))
    (fun x _ => mu_test_constCond a (fun k => (ha k).le) N w x)
    (fun x _ => by
      have hq : ∑ k, (a k * cubeSlope N w x k) ^ 2 / a k = ∑ k, a k * cubeSlope N w x k ^ 2 :=
        Finset.sum_congr rfl fun k _ => by
          have := (ha k).ne'
          field_simp
      rw [hq, neg_div, add_neg_cancel, abs_zero])
  simpa only [Finset.sum_const_zero, mul_zero, add_zero] using h

/-- **Lemma 6.2 on the lattice for constant conductances, with all cubes inside `Q`.** -/
theorem edgeEnergy_dirichletSolution_div_le_constCond_trim (hd : 1 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ k, 0 < a k) {Λ : ℝ} (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 2 ≤ s) :
    edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d ≤
      (∑ y ∈ Q.vertices, ∑ k, a k * (w (y + unit k) - w y) ^ 2 +
          2 * (Λ / √(N : ℝ) * ∑ y ∈ Q.vertices, ∑ k, (w (y + unit k) - w y) ^ 2)) /
            (Q.size : ℝ) ^ d +
        Λ * ((2 * d * ((r + 1 + N : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s)) *
              ∑ y ∈ Q.vertices, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) /
                (Q.size : ℝ) ^ d) ^ (2 / s)) := by
  have h := edgeEnergy_dirichletSolution_div_le_of_mu_test_trim hd a ha haΛ Q hL hN hr w hs
    (fun x => -(∑ k, a k * cubeSlope N w x k ^ 2) / 2) (fun _ => 0)
    (fun y => ∑ k, a k * (w (y + unit k) - w y) ^ 2)
    (fun y => Finset.sum_nonneg fun k _ => mul_nonneg (ha k).le (sq_nonneg _))
    (fun x _ => mu_test_constCond a (fun k => (ha k).le) N w x)
    (fun x _ => by
      have hq : ∑ k, (a k * cubeSlope N w x k) ^ 2 / a k = ∑ k, a k * cubeSlope N w x k ^ 2 :=
        Finset.sum_congr rfl fun k _ => by
          have := (ha k).ne'
          field_simp
      rw [hq, neg_div, add_neg_cancel, abs_zero])
  simpa only [Finset.sum_const_zero, mul_zero, add_zero] using h

end Rigidity.Dirichlet

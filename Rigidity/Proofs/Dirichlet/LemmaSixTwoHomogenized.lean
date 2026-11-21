import Rigidity.Proofs.Dirichlet.TrialEnergyInner
import Rigidity.Proofs.Dirichlet.MuTest
import Rigidity.Proofs.Dirichlet.CoarseGradientDefect

/-!
# The homogenized side of Lemma 6.2 of Armstrong–Dario

For constant conductances `0 < a_k ≤ Λ` on a cube `Q` of side `L`, the homogenized solution
`u_hom` with datum `w`, a mesoscopic side `N` and a layer depth `r`, suppose that at every point
`x` of `Q` off the boundary layer the `μ` test holds with local energy `E(x)`, convergence error
`δ(x)` and coarse gradient `G(x)` (the edge average of `∇w` on `x + □_N`):
`μ(x) ≤ E(x)/2 − Σ_k a_k p_k(x) G_k(x)` and `|p(x)·ā p(x)/2 + μ(x)| ≤ δ(x)`, with `p(x)` the
mesoscopic slope. Then
`L^{-d} E_hom(u_hom) ≤ L^{-d} Σ_{x} (E(x) + 2δ(x)) + 2Λ N^{-1/2} L^{-d} Σ_B |∇w|²`
`+ Λ · (layer term)`.

This assembles, on the lattice and with all translates of the mesoscopic cube in place of a
mesh, Steps 1, 2 and 5 of the proof of Armstrong–Dario, Lemma 6.2; the cluster inputs (the `μ`
test for `u`, the convergence (6.10) and the local energies, whose sum over the translates is at
most `N^d` times the energy of `u` by `sum_translates_le`, Step 3) enter as the hypotheses.
When the local energies are the normalized sums `N^{-d} Σ_{x+□} e` of an energy density `e ≥ 0`
of `u`, their sum is at most `Σ_B e` (`edgeEnergy_dirichletSolution_div_le_of_mu_test_density`),
which is the comparison `E_hom(u_hom) ≤ E(u) + errors` of Lemma 6.2. With the cutoff on the
trimmed cube (`edgeEnergy_dirichletSolution_div_le_trim`) all mesoscopic cubes lie in `Q`, the
`μ` test is needed only for the cubes `x + □_N ⊆ Q` with `x` in the trimmed cube off its layer, and
all sums are over `Q` (`edgeEnergy_dirichletSolution_div_le_of_mu_test_trim`).
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Lemma 6.2, homogenized side, on the lattice.** -/
theorem edgeEnergy_dirichletSolution_div_le_of_mu_test (hd : 1 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ k, 0 < a k) {Λ : ℝ} (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 2 ≤ s)
    (B : Finset (Vertex d)) (hB : ∀ x ∈ Q.vertices, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B)
    (μ E δ : Vertex d → ℝ)
    (htest : ∀ x ∈ Q.vertices \ cubeLayer Q (r + 1),
      μ x ≤ E x / 2 - ∑ k, a k * cubeSlope N w x k * cubeEdgeSlope N w x k)
    (hconv : ∀ x ∈ Q.vertices \ cubeLayer Q (r + 1),
      |(∑ k, (a k * cubeSlope N w x k) ^ 2 / a k) / 2 + μ x| ≤ δ x) :
    edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d ≤
      (∑ x ∈ Q.vertices \ cubeLayer Q (r + 1), (E x + 2 * δ x) +
          2 * (Λ / √(N : ℝ) * ∑ y ∈ B, ∑ k, (w (y + unit k) - w y) ^ 2)) / (Q.size : ℝ) ^ d +
        Λ * ((2 * d * ((r + 1 : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s) *
              ∑ y ∈ B, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) / (Q.size : ℝ) ^ d) ^ (2 / s)) := by
  have hΛ : 0 ≤ Λ := (ha ⟨0, hd⟩).le.trans (haΛ _)
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  set A := Q.vertices \ cubeLayer Q (r + 1)
  have hhom := edgeEnergy_dirichletSolution_div_le hd a ha haΛ Q hL hN hr w hs B hB
  have hpt : ∀ x ∈ A, ∑ k, a k * cubeSlope N w x k ^ 2 ≤ E x + 2 * δ x +
      2 * ∑ k, |a k * cubeSlope N w x k| * |cubeEdgeSlope N w x k - cubeSlope N w x k| :=
    fun x hx => quadratic_le_of_mu_test' a (cubeSlope N w x) (cubeEdgeSlope N w x) ha
      (htest x hx) (hconv x hx)
  have hdef := sum_translates_slope_mul_defect_le a hΛ (fun k => by
    rw [abs_of_pos (ha k)]; exact haΛ k) hN w A B (fun x hx => hB x (Finset.sdiff_subset hx))
  have hsum : ∑ x ∈ A, ∑ k, a k * cubeSlope N w x k ^ 2 ≤
      ∑ x ∈ A, (E x + 2 * δ x) +
        2 * (Λ / √(N : ℝ) * ∑ y ∈ B, ∑ k, (w (y + unit k) - w y) ^ 2) := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hdef (by norm_num))
  refine hhom.trans (add_le_add (div_le_div_of_nonneg_right hsum hV.le) le_rfl)

/-- **Lemma 6.2, homogenized side, with an energy density.** -/
theorem edgeEnergy_dirichletSolution_div_le_of_mu_test_density (hd : 1 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ k, 0 < a k) {Λ : ℝ} (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 2 ≤ s)
    (B : Finset (Vertex d)) (hB : ∀ x ∈ Q.vertices, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B)
    (μ δ e : Vertex d → ℝ) (he : ∀ y, 0 ≤ e y)
    (htest : ∀ x ∈ Q.vertices \ cubeLayer Q (r + 1),
      μ x ≤ (∑ y ∈ (cornerCube x N).vertices, e y) / (N : ℝ) ^ d / 2 -
        ∑ k, a k * cubeSlope N w x k * cubeEdgeSlope N w x k)
    (hconv : ∀ x ∈ Q.vertices \ cubeLayer Q (r + 1),
      |(∑ k, (a k * cubeSlope N w x k) ^ 2 / a k) / 2 + μ x| ≤ δ x) :
    edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d ≤
      (∑ y ∈ B, e y + 2 * ∑ x ∈ Q.vertices \ cubeLayer Q (r + 1), δ x +
          2 * (Λ / √(N : ℝ) * ∑ y ∈ B, ∑ k, (w (y + unit k) - w y) ^ 2)) / (Q.size : ℝ) ^ d +
        Λ * ((2 * d * ((r + 1 : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s) *
              ∑ y ∈ B, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) / (Q.size : ℝ) ^ d) ^ (2 / s)) := by
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  set A := Q.vertices \ cubeLayer Q (r + 1)
  refine (edgeEnergy_dirichletSolution_div_le_of_mu_test hd a ha haΛ Q hL hN hr w hs B hB μ
    (fun x => (∑ y ∈ (cornerCube x N).vertices, e y) / (N : ℝ) ^ d) δ htest hconv).trans ?_
  refine add_le_add (div_le_div_of_nonneg_right ?_ hV.le) le_rfl
  have htr := sum_translates_le A B N e he fun x hx => hB x (Finset.sdiff_subset hx)
  have hE : ∑ x ∈ A, (∑ y ∈ (cornerCube x N).vertices, e y) / (N : ℝ) ^ d ≤ ∑ y ∈ B, e y := by
    rw [← Finset.sum_div, div_le_iff₀ hNd, mul_comm]
    exact htr
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

/-- **Lemma 6.2, homogenized side, with all mesoscopic cubes inside `Q`.** -/
theorem edgeEnergy_dirichletSolution_div_le_of_mu_test_trim (hd : 1 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ k, 0 < a k) {Λ : ℝ} (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 2 ≤ s)
    (μ δ e : Vertex d → ℝ) (he : ∀ y, 0 ≤ e y)
    (htest : ∀ x ∈ (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1),
      μ x ≤ (∑ y ∈ (cornerCube x N).vertices, e y) / (N : ℝ) ^ d / 2 -
        ∑ k, a k * cubeSlope N w x k * cubeEdgeSlope N w x k)
    (hconv : ∀ x ∈ (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1),
      |(∑ k, (a k * cubeSlope N w x k) ^ 2 / a k) / 2 + μ x| ≤ δ x) :
    edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d ≤
      (∑ y ∈ Q.vertices, e y +
          2 * ∑ x ∈ (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1), δ x +
          2 * (Λ / √(N : ℝ) * ∑ y ∈ Q.vertices, ∑ k, (w (y + unit k) - w y) ^ 2)) /
            (Q.size : ℝ) ^ d +
        Λ * ((2 * d * ((r + 1 + N : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s)) *
              ∑ y ∈ Q.vertices, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) /
                (Q.size : ℝ) ^ d) ^ (2 / s)) := by
  have hΛ : 0 ≤ Λ := (ha ⟨0, hd⟩).le.trans (haΛ _)
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  set A := (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1)
  have hB : ∀ x ∈ A, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ Q.vertices :=
    fun x hx o ho => add_mem_of_mem_trimCube Q N (Finset.sdiff_subset hx) ho
  have hhom := edgeEnergy_dirichletSolution_div_le_trim hd a ha haΛ Q hL hN hr w hs
  have hpt : ∀ x ∈ A, ∑ k, a k * cubeSlope N w x k ^ 2 ≤
      (∑ y ∈ (cornerCube x N).vertices, e y) / (N : ℝ) ^ d + 2 * δ x +
        2 * ∑ k, |a k * cubeSlope N w x k| * |cubeEdgeSlope N w x k - cubeSlope N w x k| :=
    fun x hx => quadratic_le_of_mu_test' a (cubeSlope N w x) (cubeEdgeSlope N w x) ha
      (htest x hx) (hconv x hx)
  have hdef := sum_translates_slope_mul_defect_le a hΛ (fun k => by
    rw [abs_of_pos (ha k)]; exact haΛ k) hN w A Q.vertices hB
  have htr := sum_translates_le A Q.vertices N e he hB
  have hE : ∑ x ∈ A, (∑ y ∈ (cornerCube x N).vertices, e y) / (N : ℝ) ^ d ≤
      ∑ y ∈ Q.vertices, e y := by
    rw [← Finset.sum_div, div_le_iff₀ hNd, mul_comm]
    exact htr
  have hsum : ∑ x ∈ A, ∑ k, a k * cubeSlope N w x k ^ 2 ≤
      ∑ y ∈ Q.vertices, e y + 2 * ∑ x ∈ A, δ x +
        2 * (Λ / √(N : ℝ) * ∑ y ∈ Q.vertices, ∑ k, (w (y + unit k) - w y) ^ 2) := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hdef (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  exact hhom.trans (add_le_add (div_le_div_of_nonneg_right hsum hV.le) le_rfl)

end Rigidity.Dirichlet

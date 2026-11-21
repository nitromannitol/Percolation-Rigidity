import Rigidity.Proofs.Dirichlet.LemmaSixThreeLattice
import Rigidity.Proofs.Dirichlet.LayerEnergyBound

/-!
# Lemma 6.3 (ii) of Armstrong–Dario for the homogenized Dirichlet solution, normalized

For the homogenized solution `u_hom = dirichletSolution (constCond ā) (cubeInterior Q) f` with
datum `f`, the boundary-layer energies in `edgeEnergy_patch_cubeCutoff_le` are bounded by the
Hardy-weighted layer estimate `sum_energy_cubeLayer_div_le`. Normalized by the volume `L^d` of
`Q`, the energy of the patched function `ũ` satisfies
`L^{-d} E_c(ũ) ≤ L^{-d} E_ā(u_hom) + L^{-d} (6 N^d Σ δ + 3 F + 6 Λ d ρ^{-2} (X + Y))`
`+ (2 + 3Λ/λ) (2 L^{-d} Σ_{layer} ā|∇f|² + C ((D + ρ + N + 1)/L)^γ (L^{-d} Σ |∇f|^p)^{2/p})`,
which is the energy estimate (ii) of Lemma 6.3 with the boundary strip estimates (2step31) and
(2step32) on the lattice.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

theorem shrinkCube_one_vertices_subset_cubeInterior (Q : IntegerCube d) :
    (shrinkCube Q 1).vertices ⊆ cubeInterior Q := by
  intro x hx
  rw [mem_shrinkCube_iff] at hx
  refine Finset.mem_filter.mpr ⟨shrinkCube_vertices_subset_self Q 1
    ((mem_shrinkCube_iff Q 1 x).mpr hx), fun k => ?_⟩
  have h := hx k
  push_cast at h
  have : ((Q.size - 2 * 1 : ℕ) : ℤ) ≤ (Q.size : ℤ) - 2 ∨ Q.size < 2 := by omega
  omega

theorem cubeLayer_mono (Q : IntegerCube d) {r s : ℕ} (hrs : r ≤ s) :
    cubeLayer Q r ⊆ cubeLayer Q s := by
  intro x hx
  obtain ⟨hxQ, k, hk⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxQ, k, ?_⟩
  have : (r : ℤ) ≤ s := by exact_mod_cast hrs
  rcases hk with hk | hk
  · left
    linarith
  · right
    linarith

/-- **Lemma 6.3 (ii) for the homogenized Dirichlet solution, normalized.** -/
theorem edgeEnergy_patch_dirichletSolution_div_le (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (hcΛ : ∀ e, c e ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size) (f : Vertex d → ℝ)
    {r : ℕ} (hr : 0 < r) (z : Vertex d) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices)
    {D : ℕ} (hT1 : ∀ k, z k ≤ Q.corner k + D)
    (hT2 : ∀ k, Q.corner k + Q.size ≤ z k + (M * N : ℕ) + D) {ρ : ℕ} (hρ : 0 < ρ)
    (v : Vertex d → ℝ) (δ : Vertex d → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hinner : ∀ i ∈ (cornerCube 0 M).vertices,
      innerEdgeEnergy c (cornerCube (z + (N : ℤ) • i) N) v / (N : ℝ) ^ d ≤
        ∑ k, a k * cubeSlope N (dirichletSolution (constCond a) (cubeInterior Q) f)
          (z + (N : ℤ) • i) k ^ 2 + 2 * δ i)
    (hface : ∀ i ∈ (cornerCube 0 M).vertices, ∀ j : Fin d,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j, c (x, j) ≠ 0 →
        v x = cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) f)
            (z + (N : ℤ) • i) x ∧
          v (x + unit j) = cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) f)
            (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j))
    {γ p : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (hp : 2 < p) (hγp : γ * (p / (p - 2)) < 1) :
    let u := dirichletSolution (constCond a) (cubeInterior Q) f
    edgeEnergy c Q.vertices (patch (cubeCutoff (cornerCube z (M * N)) ρ) v u) /
        (Q.size : ℝ) ^ d ≤
      edgeEnergy (constCond a) Q.vertices u / (Q.size : ℝ) ^ d +
        (6 * (N : ℝ) ^ d * ∑ i ∈ (cornerCube 0 M).vertices, δ i +
          3 * (Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 *
            (10 * d * Λ / (lam * (r : ℝ) ^ 2)) + 1 / N) *
              ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2))) +
          6 * Λ * (d * (1 / (ρ : ℝ)) ^ 2) *
            (∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
                (v x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 +
              ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
                (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2)) / (Q.size : ℝ) ^ d +
        (2 + 3 * Λ / lam) *
          (2 * ((∑ x ∈ cubeLayer Q (D + ρ + N + 1), ∑ k : Fin d,
              a k * (f (x + unit k) - f x) ^ 2) / (Q.size : ℝ) ^ d) +
            88 * Λ * Real.exp (γ + 4 * γ ^ 2) *
              ((2 * (d : ℝ)) ^ (p / (p - 2)) / (1 - γ * (p / (p - 2)))) ^ (1 - 2 / p) *
              ((((D + ρ + N : ℕ) : ℝ) + 1) / Q.size) ^ γ *
              ((∑ x ∈ Q.vertices, √(∑ k : Fin d, (f (x + unit k) - f x) ^ 2) ^ p) /
                (Q.size : ℝ) ^ d) ^ (2 / p)) := by
  intro u
  have hapos : ∀ k, 0 < a k := fun k => hlam.trans_le (ha k).1
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  have hharm : ∀ x ∈ cubeInterior Q, condLaplacian (constCond a) u x = 0 :=
    condLaplacian_dirichletSolution hd (constCond a) (fun e => hapos e.2) _ f
  have hu : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) u x = 0 :=
    fun x hx => hharm x (shrinkCube_one_vertices_subset_cubeInterior Q hx)
  have hmain := edgeEnergy_patch_cubeCutoff_le hd a hlam ha c hc0 hcΛ Q hu hr z M hN hsub hT1
    hT2 hρ v δ hδ hinner hface
  -- the layer energies of `u`
  set Lay := ∑ x ∈ cubeLayer Q (D + ρ + N + 1), ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2
  have hsmall : ∑ x ∈ cubeLayer Q (D + ρ + 2), ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 ≤
      Lay / lam := by
    rw [le_div_iff₀ hlam, Finset.sum_mul]
    calc ∑ x ∈ cubeLayer Q (D + ρ + 2), (∑ j : Fin d, (u (x + unit j) - u x) ^ 2) * lam
        ≤ ∑ x ∈ cubeLayer Q (D + ρ + N + 1), (∑ j : Fin d, (u (x + unit j) - u x) ^ 2) * lam :=
          Finset.sum_le_sum_of_subset_of_nonneg (cubeLayer_mono Q (by omega)) fun x _ _ =>
            mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hlam.le
      _ ≤ Lay := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun k _ => by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (ha k).1 (sq_nonneg _)
  have hhardy := sum_energy_cubeLayer_div_le hγ0 hγ hp hγp hd a hapos (fun k => (ha k).2) Q hL u f
    hharm (fun x hx => dirichletSolution_eq_of_not_mem _ _ f hx) (D + ρ + N)
  -- combine
  set H := 2 * ((∑ x ∈ cubeLayer Q (D + ρ + N + 1), ∑ k : Fin d,
      a k * (f (x + unit k) - f x) ^ 2) / (Q.size : ℝ) ^ d) +
    88 * Λ * Real.exp (γ + 4 * γ ^ 2) *
      ((2 * (d : ℝ)) ^ (p / (p - 2)) / (1 - γ * (p / (p - 2)))) ^ (1 - 2 / p) *
      ((((D + ρ + N : ℕ) : ℝ) + 1) / Q.size) ^ γ *
      ((∑ x ∈ Q.vertices, √(∑ k : Fin d, (f (x + unit k) - f x) ^ 2) ^ p) /
        (Q.size : ℝ) ^ d) ^ (2 / p)
  have hLay : Lay / (Q.size : ℝ) ^ d ≤ H := hhardy
  have hLay0 : 0 ≤ Lay := Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hapos k).le (sq_nonneg _)
  have hlayers : 2 * Lay + 3 * Λ * ∑ x ∈ cubeLayer Q (D + ρ + 2), ∑ j : Fin d,
      (u (x + unit j) - u x) ^ 2 ≤ (2 + 3 * Λ / lam) * Lay := by
    have := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 3 * Λ by positivity)
    have e : (2 + 3 * Λ / lam) * Lay = 2 * Lay + 3 * Λ * (Lay / lam) := by
      field_simp
    rw [e]
    linarith
  have hfin : (2 + 3 * Λ / lam) * Lay / (Q.size : ℝ) ^ d ≤ (2 + 3 * Λ / lam) * H := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hLay (by positivity)
  rw [div_le_iff₀ hV]
  rw [div_le_iff₀ hV] at hfin
  have e2 : (edgeEnergy (constCond a) Q.vertices u / (Q.size : ℝ) ^ d) * (Q.size : ℝ) ^ d =
      edgeEnergy (constCond a) Q.vertices u := by field_simp
  rw [add_mul, add_mul, e2, div_mul_cancel₀ _ hV.ne']
  linarith

end Rigidity.Dirichlet

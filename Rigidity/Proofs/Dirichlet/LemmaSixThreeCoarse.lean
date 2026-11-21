import Rigidity.Proofs.Dirichlet.LemmaSixThreeInner
import Rigidity.Proofs.Dirichlet.LemmaSixTwoCoarse

/-!
# Lemma 6.3 on the lattice with the boundary interpolation of the coarsened function

With the datum `w̃ = boundaryInterpolation 𝒫 B u` and `Q ⊆ cl_𝒫`, the two boundary-layer terms of
`innerEdgeEnergy_patch_dirichletSolution_div_le` are bounded through Lemma 6.4 (iii) with exponent
`t ∈ (2, p)`: the layer energy of `w̃` by Hölder's inequality on the layer of width
`D + ρ + N + 1`, and the Hardy term by the power mean `|∇w̃|^t ≤ d^{t/2−1} Σ_k |∇_k w̃|^t`. With
`𝔅_t = interpolationGradBound … t p L^d u`, the energy estimate (ii) of Lemma 6.3 reads
`L^{-d} E_c(ũ) ≤ L^{-d} E_hom(u_hom) + L^{-d} (6 N^d Σ δ + 3 F + 6 Λ d ρ^{-2} (X + Y))
  + (2 + 3Λ/λ) (2 Λ (2d(D + ρ + N + 1)/L)^{1 − 2/t} + C_γ ((D + ρ + N + 1)/L)^γ)
  (d^{t/2−1} 𝔅_t)^{2/t}`
(`innerEdgeEnergy_patch_div_le_of_coarse`). The `L²` estimate (iii) reads
`L^{-d} Σ_U (ũ − u_hom)² ≤ 2 L^{-d} Σ_i Σ (ṽ − ℓ_{y_i})² + 2 C N⁴ r^{-2} (Λ/λ) 𝔅₂`
(`exists_sum_sq_patch_sub_div_le_of_coarse`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Dirichlet

open Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The magnitude of the gradient of `g` on the edges inside `Q`. -/
noncomputable def innerGradNorm (Q : IntegerCube d) (g : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  √(∑ k : Fin d, (if x + unit k ∈ Q.vertices then (g (x + unit k) - g x) ^ 2 else 0))

theorem innerGradNorm_rpow_le (Q : IntegerCube d) (g : Vertex d → ℝ) (x : Vertex d) {t : ℝ}
    (ht : 2 ≤ t) :
    innerGradNorm Q g x ^ t ≤ (d : ℝ) ^ (t / 2 - 1) *
      ∑ k : Fin d, (if x + unit k ∈ Q.vertices then |g (x + unit k) - g x| ^ t else 0) := by
  have h := abs_sqrt_sum_sq_rpow_le
    (fun k => if x + unit k ∈ Q.vertices then g (x + unit k) - g x else 0) ht
  have e1 : ∑ k : Fin d, (if x + unit k ∈ Q.vertices then g (x + unit k) - g x else 0) ^ 2 =
      ∑ k : Fin d, (if x + unit k ∈ Q.vertices then (g (x + unit k) - g x) ^ 2 else 0) :=
    Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  have e2 : ∑ k : Fin d, |if x + unit k ∈ Q.vertices then g (x + unit k) - g x else 0| ^ t =
      ∑ k : Fin d, (if x + unit k ∈ Q.vertices then |g (x + unit k) - g x| ^ t else 0) :=
    Finset.sum_congr rfl fun k _ => by
      split_ifs
      · rfl
      · rw [abs_zero, Real.zero_rpow (by positivity)]
  rw [e1, e2, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  exact h

/-- **Armstrong–Dario, Lemma 6.3 (ii), on the lattice with the boundary interpolation.** -/
theorem innerEdgeEnergy_patch_div_le_of_coarse (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (hcΛ : ∀ e, c e ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size) (P : CoarseData d ω)
    {B : Finset (Vertex d)} (hB : B ⊆ P.cluster) (u : Vertex d → ℝ) {K N₃ m K' N' m' : ℕ}
    (h3 : P.PairOverlap K N₃ m) (hK : 1 ≤ K) (hN₃ : 1 ≤ N₃) (h2 : P.RegionOverlap K' N' m')
    (hK' : 1 ≤ K') (hN' : 1 ≤ N') (hQ : Q.vertices ⊆ P.domain)
    {r : ℕ} (hr : 0 < r) (z : Vertex d) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices)
    {D : ℕ} (hT1 : ∀ k, z k ≤ Q.corner k + D)
    (hT2 : ∀ k, Q.corner k + Q.size ≤ z k + (M * N : ℕ) + D) {ρ : ℕ} (hρ : 0 < ρ)
    (v : Vertex d → ℝ) (δ : Vertex d → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hinner : ∀ i ∈ (cornerCube 0 M).vertices,
      innerEdgeEnergy c (cornerCube (z + (N : ℤ) • i) N) v / (N : ℝ) ^ d ≤
        ∑ k, a k * cubeSlope N
          (dirichletSolution (constCond a) (cubeInterior Q) (boundaryInterpolation P B u))
          (z + (N : ℤ) • i) k ^ 2 + 2 * δ i)
    (hface : ∀ i ∈ (cornerCube 0 M).vertices, ∀ j : Fin d,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j, c (x, j) ≠ 0 →
        v x = cubeAffine N
            (dirichletSolution (constCond a) (cubeInterior Q) (boundaryInterpolation P B u))
            (z + (N : ℤ) • i) x ∧
          v (x + unit j) = cubeAffine N
            (dirichletSolution (constCond a) (cubeInterior Q) (boundaryInterpolation P B u))
            (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j))
    {γ t p : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (ht : 2 < t) (hγt : γ * (t / (t - 2)) < 1)
    (htp : t < p) :
    let uh := dirichletSolution (constCond a) (cubeInterior Q) (boundaryInterpolation P B u)
    innerEdgeEnergy c Q (patch (cubeCutoff (cornerCube z (M * N)) ρ) v uh) / (Q.size : ℝ) ^ d ≤
      innerEdgeEnergy (constCond a) Q uh / (Q.size : ℝ) ^ d +
        (6 * (N : ℝ) ^ d * ∑ i ∈ (cornerCube 0 M).vertices, δ i +
          3 * (Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 *
            (10 * d * Λ / (lam * (r : ℝ) ^ 2)) + 1 / N) *
              ∑ x ∈ Q.vertices, ∑ k : Fin d, (if x + unit k ∈ Q.vertices then
                (uh (x + unit k) - uh x) ^ 2 else 0)))) +
          6 * Λ * (d * (1 / (ρ : ℝ)) ^ 2) *
            (∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
                (v x - cubeAffine N uh (z + (N : ℤ) • i) x) ^ 2 +
              ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
                (uh x - cubeAffine N uh (z + (N : ℤ) • i) x) ^ 2)) / (Q.size : ℝ) ^ d +
        (2 + 3 * Λ / lam) *
          ((2 * Λ * (2 * d * ((D + ρ + N + 1 : ℕ) : ℝ) / Q.size) ^ (1 - 2 / t) +
            88 * Λ * Real.exp (γ + 4 * γ ^ 2) *
              ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
              ((((D + ρ + N : ℕ) : ℝ) + 1) / Q.size) ^ γ) *
            ((d : ℝ) ^ (t / 2 - 1) *
              interpolationGradBound P K N₃ m K' N' m' t p ((Q.size : ℝ) ^ d) u) ^ (2 / t)) := by
  intro uh
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  set w := boundaryInterpolation P B u
  have main := innerEdgeEnergy_patch_dirichletSolution_div_le hd a hlam ha c hc0 hcΛ Q hL w hr z M
    hN hsub hT1 hT2 hρ v δ hδ hinner hface (p := t) hγ0 hγ ht hγt
  -- the `L^t` bound of the gradient of `w̃` on `Q`
  set G : Vertex d → ℝ := innerGradNorm Q w
  have hG0 : ∀ x, 0 ≤ G x := fun x => Real.sqrt_nonneg _
  have hbt := sum_abs_grad_boundaryInterpolation_inner_div_le P hB u h3 hK hN₃ h2 hK' hN'
    (Nat.one_le_iff_ne_zero.mpr hd.ne') (s := t) (p := p) (by linarith) htp hV Q hQ
  set 𝔅 := interpolationGradBound P K N₃ m K' N' m' t p ((Q.size : ℝ) ^ d) u
  have hGt : (∑ x ∈ Q.vertices, |G x| ^ t) / (Q.size : ℝ) ^ d ≤ (d : ℝ) ^ (t / 2 - 1) * 𝔅 := by
    have h1 : ∑ x ∈ Q.vertices, |G x| ^ t ≤ (d : ℝ) ^ (t / 2 - 1) *
        ∑ y ∈ Q.vertices, ∑ k : Fin d, (if y + unit k ∈ Q.vertices then
          |w (y + unit k) - w y| ^ t else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => by
        rw [abs_of_nonneg (hG0 x)]
        exact innerGradNorm_rpow_le Q w x ht.le
    calc (∑ x ∈ Q.vertices, |G x| ^ t) / (Q.size : ℝ) ^ d
        ≤ (d : ℝ) ^ (t / 2 - 1) * ((∑ y ∈ Q.vertices, ∑ k : Fin d,
            (if y + unit k ∈ Q.vertices then |w (y + unit k) - w y| ^ t else 0)) /
              (Q.size : ℝ) ^ d) := by
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right h1 hV.le
      _ ≤ (d : ℝ) ^ (t / 2 - 1) * 𝔅 := mul_le_mul_of_nonneg_left hbt (by positivity)
  have hGt' : (∑ x ∈ Q.vertices, G x ^ t) / (Q.size : ℝ) ^ d ≤ (d : ℝ) ^ (t / 2 - 1) * 𝔅 := by
    have : ∑ x ∈ Q.vertices, G x ^ t = ∑ x ∈ Q.vertices, |G x| ^ t :=
      Finset.sum_congr rfl fun x _ => by rw [abs_of_nonneg (hG0 x)]
    rw [this]
    exact hGt
  have h0t : (0 : ℝ) ≤ 2 / t := by positivity
  have hpow := Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg fun x _ =>
    Real.rpow_nonneg (hG0 x) t) hV.le) hGt' h0t
  -- the layer energy of `w̃`, by Hölder on the layer
  set ℓ := D + ρ + N + 1
  have hlay1 : ∑ x ∈ cubeLayer Q ℓ, ∑ k : Fin d,
      (if x + unit k ∈ Q.vertices then a k * (w (x + unit k) - w x) ^ 2 else 0) ≤
      Λ * ∑ x ∈ cubeLayer Q ℓ, G x ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hG2 : G x ^ 2 = ∑ k : Fin d,
        (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0) :=
      Real.sq_sqrt (Finset.sum_nonneg fun k _ => by split_ifs <;> positivity)
    rw [hG2, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_right (ha k).2 (sq_nonneg _)
    · rw [mul_zero]
  have hhol := sum_sq_div_le_card_div_rpow_mul (cubeLayer_subset Q ℓ) G ht.le hV
  have he : 0 ≤ 1 - 2 / t := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact ht.le
  have hcard := Real.rpow_le_rpow (by positivity) (card_cubeLayer_div_le Q hL ℓ) he
  have hlay : (∑ x ∈ cubeLayer Q ℓ, ∑ k : Fin d,
      (if x + unit k ∈ Q.vertices then a k * (w (x + unit k) - w x) ^ 2 else 0)) /
        (Q.size : ℝ) ^ d ≤
      Λ * ((2 * d * (ℓ : ℝ) / Q.size) ^ (1 - 2 / t) *
        ((d : ℝ) ^ (t / 2 - 1) * 𝔅) ^ (2 / t)) := by
    calc _ ≤ Λ * ((∑ x ∈ cubeLayer Q ℓ, G x ^ 2) / (Q.size : ℝ) ^ d) := by
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right hlay1 hV.le
      _ ≤ Λ * (((#(cubeLayer Q ℓ) : ℝ) / (Q.size : ℝ) ^ d) ^ (1 - 2 / t) *
            ((∑ x ∈ Q.vertices, |G x| ^ t) / (Q.size : ℝ) ^ d) ^ (2 / t)) :=
          mul_le_mul_of_nonneg_left hhol hΛ
      _ ≤ Λ * ((2 * d * (ℓ : ℝ) / Q.size) ^ (1 - 2 / t) *
            ((d : ℝ) ^ (t / 2 - 1) * 𝔅) ^ (2 / t)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hcard
            (Real.rpow_le_rpow (by positivity) hGt h0t) (by positivity) (by positivity)) hΛ
  -- assemble
  refine main.trans ?_
  have hHardy : ((∑ x ∈ Q.vertices, √(∑ k : Fin d,
      (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0)) ^ t) /
        (Q.size : ℝ) ^ d) ^ (2 / t) ≤ ((d : ℝ) ^ (t / 2 - 1) * 𝔅) ^ (2 / t) := hpow
  have hcoef : 0 ≤ 2 + 3 * Λ / lam := by positivity
  have hC88 : 0 ≤ 88 * Λ * Real.exp (γ + 4 * γ ^ 2) *
      ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
      ((((D + ρ + N : ℕ) : ℝ) + 1) / Q.size) ^ γ := by
    have : 0 < 1 - γ * (t / (t - 2)) := by linarith
    positivity
  have hfin := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hlay
    (show (0 : ℝ) ≤ 2 by norm_num)) (mul_le_mul_of_nonneg_left hHardy hC88)) hcoef
  have e : (2 * Λ * (2 * d * ((D + ρ + N + 1 : ℕ) : ℝ) / Q.size) ^ (1 - 2 / t) +
      88 * Λ * Real.exp (γ + 4 * γ ^ 2) *
        ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
        ((((D + ρ + N : ℕ) : ℝ) + 1) / Q.size) ^ γ) * ((d : ℝ) ^ (t / 2 - 1) * 𝔅) ^ (2 / t) =
      2 * (Λ * ((2 * d * (ℓ : ℝ) / Q.size) ^ (1 - 2 / t) *
        ((d : ℝ) ^ (t / 2 - 1) * 𝔅) ^ (2 / t))) +
      88 * Λ * Real.exp (γ + 4 * γ ^ 2) *
        ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
        ((((D + ρ + N : ℕ) : ℝ) + 1) / Q.size) ^ γ * ((d : ℝ) ^ (t / 2 - 1) * 𝔅) ^ (2 / t) := by
    ring
  rw [e]
  linarith

theorem cornerCube_mul_subset_succ (z : Vertex d) (M N : ℕ) :
    (cornerCube z (M * N)).vertices ⊆ (cornerCube z ((M + 1) * N)).vertices := by
  intro x hx
  rw [IntegerCube.mem_vertices] at hx ⊢
  intro k
  have h := hx k
  simp only [cornerCube] at h ⊢
  have : ((M * N : ℕ) : ℤ) ≤ ((M + 1) * N : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_right N (Nat.le_succ M)
  exact ⟨h.1, h.2.trans_le (by linarith)⟩

/-- **Lemma 6.3 (iii) on the edges inside `Q`.** -/
theorem exists_sum_sq_patch_sub_le_inner (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : IntegerCube d) (w : Vertex d → ℝ) (r : ℕ), 0 < r →
      ∀ (z : Vertex d) (M N : ℕ), 0 < N →
      (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices →
      ∀ (ρ : ℕ) (U : Finset (Vertex d)), U ⊆ Q.vertices → ∀ v : Vertex d → ℝ,
      ∑ x ∈ U, (patch (cubeCutoff (cornerCube z (M * N)) ρ) v
          (dirichletSolution (constCond a) (cubeInterior Q) w) x -
            dirichletSolution (constCond a) (cubeInterior Q) w x) ^ 2 ≤
        2 * ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
            (v x - cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
              (z + (N : ℤ) • i) x) ^ 2 +
          2 * (C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 * (Λ / lam * ∑ x ∈ Q.vertices, ∑ k : Fin d,
            (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0))) := by
  obtain ⟨C, hC, hbound⟩ := exists_sum_sq_patch_cubeCutoff_sub_le hd a hlam ha
  refine ⟨C, hC, fun Q w r hr z M N hN hsub ρ U hU v => ?_⟩
  have hd1 : 1 ≤ d := hd
  have hapos : ∀ k, 0 < a k := fun k => hlam.trans_le (ha k).1
  set w' : Vertex d → ℝ := fun y => w (cubeProj Q y)
  set u' := dirichletSolution (constCond a) (cubeInterior Q) w'
  set u := dirichletSolution (constCond a) (cubeInterior Q) w
  have hagree : ∀ x ∈ Q.vertices, u' x = u x := fun x hx => dirichletSolution_comp_cubeProj _ Q w hx
  have hu' : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) u' x = 0 :=
    fun x hx => condLaplacian_dirichletSolution hd1 (constCond a) (fun e => hapos e.2) _ w' x
      (shrinkCube_one_vertices_subset_cubeInterior Q hx)
  have htile : ∀ i ∈ (cornerCube 0 (M + 1)).vertices,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, ∀ k : Fin d,
        x ∈ Q.vertices ∧ x + unit k ∈ Q.vertices := fun i hi x hx k =>
    add_unit_mem_of_mem_shrinkCube Q (by omega) (hsub (tile_subset z (M + 1) hi hx)) k
  have haff : ∀ i ∈ (cornerCube 0 (M + 1)).vertices, ∀ x,
      cubeAffine N u' (z + (N : ℤ) • i) x = cubeAffine N u (z + (N : ℤ) • i) x :=
    fun i hi => cubeAffine_congr (fun x hx => hagree x (htile i hi x hx ⟨0, hd⟩).1)
      (fun x hx k => hagree _ (htile i hi x hx k).2)
  have h := hbound Q u' hu' r hr z M N hN
    ((cornerCube_mul_subset_succ z M N).trans hsub) ρ U v
  have hL : ∑ x ∈ U, (patch (cubeCutoff (cornerCube z (M * N)) ρ) v u' x - u' x) ^ 2 =
      ∑ x ∈ U, (patch (cubeCutoff (cornerCube z (M * N)) ρ) v u x - u x) ^ 2 :=
    Finset.sum_congr rfl fun x hx => by simp only [patch]; rw [hagree x (hU hx)]
  have hX : ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
      (v x - cubeAffine N u' (z + (N : ℤ) • i) x) ^ 2 =
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (v x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun x _ => by
      rw [haff i (mem_cornerCube_succ hi)]
  have hE : ∑ x ∈ Q.vertices, ∑ j : Fin d, (u' (x + unit j) - u' x) ^ 2 ≤
      Λ / lam * ∑ x ∈ Q.vertices, ∑ k : Fin d,
        (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0) := by
    rw [sum_sq_grad_dirichletSolution_comp_cubeProj]
    exact sum_sq_inner_grad_dirichletSolution_le hd1 a hlam ha Q w
  rw [hL, hX] at h
  have hc : 0 ≤ C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hE hc
  linarith

/-- **Lemma 6.3 (iii) with the boundary interpolation**, normalized. -/
theorem exists_sum_sq_patch_sub_div_le_of_coarse (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : IntegerCube d), 0 < Q.size → ∀ (P : CoarseData d ω)
      {B : Finset (Vertex d)}, B ⊆ P.cluster → ∀ (u : Vertex d → ℝ) {K N₃ m K' N' m' : ℕ},
      P.PairOverlap K N₃ m → 1 ≤ K → 1 ≤ N₃ → P.RegionOverlap K' N' m' → 1 ≤ K' → 1 ≤ N' →
      Q.vertices ⊆ P.domain → ∀ {p : ℝ}, 2 < p → ∀ (r : ℕ), 0 < r →
      ∀ (z : Vertex d) (M N : ℕ), 0 < N →
      (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices →
      ∀ (ρ : ℕ) (U : Finset (Vertex d)), U ⊆ Q.vertices → ∀ v : Vertex d → ℝ,
      (∑ x ∈ U, (patch (cubeCutoff (cornerCube z (M * N)) ρ) v
          (dirichletSolution (constCond a) (cubeInterior Q) (boundaryInterpolation P B u)) x -
            dirichletSolution (constCond a) (cubeInterior Q) (boundaryInterpolation P B u) x) ^ 2) /
          (Q.size : ℝ) ^ d ≤
        2 * ((∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
            (v x - cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q)
              (boundaryInterpolation P B u)) (z + (N : ℤ) • i) x) ^ 2) / (Q.size : ℝ) ^ d) +
          2 * (C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 * (Λ / lam *
            interpolationGradBound P K N₃ m K' N' m' 2 p ((Q.size : ℝ) ^ d) u)) := by
  obtain ⟨C, hC, hbound⟩ := exists_sum_sq_patch_sub_le_inner hd a hlam ha
  refine ⟨C, hC, fun Q hL P B hB u K N₃ m K' N' m' h3 hK hN₃ h2 hK' hN' hQ p hp r hr z M N hN
    hsub ρ U hU v => ?_⟩
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  set w := boundaryInterpolation P B u
  have h := hbound Q w r hr z M N hN hsub ρ U hU v
  have hb2 := sum_abs_grad_boundaryInterpolation_inner_div_le P hB u h3 hK hN₃ h2 hK' hN'
    (Nat.one_le_iff_ne_zero.mpr hd.ne') (s := 2) (p := p) (by norm_num) hp hV Q hQ
  have hsq : ∑ y ∈ Q.vertices, ∑ k : Fin d,
      (if y + unit k ∈ Q.vertices then (w (y + unit k) - w y) ^ 2 else 0) =
      ∑ y ∈ Q.vertices, ∑ k : Fin d,
        (if y + unit k ∈ Q.vertices then |w (y + unit k) - w y| ^ (2 : ℝ) else 0) :=
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => by
      split_ifs
      · rw [Real.rpow_two, sq_abs]
      · rfl
  rw [← hsq] at hb2
  have h2' := div_le_div_of_nonneg_right h hV.le
  have hc : 0 ≤ C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 * (Λ / lam) := by positivity
  have h3' := mul_le_mul_of_nonneg_left hb2 hc
  have e : (2 * ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (v x - cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
          (z + (N : ℤ) • i) x) ^ 2 +
      2 * (C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 * (Λ / lam * ∑ x ∈ Q.vertices, ∑ k : Fin d,
        (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0)))) /
        (Q.size : ℝ) ^ d =
      2 * ((∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (v x - cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
          (z + (N : ℤ) • i) x) ^ 2) / (Q.size : ℝ) ^ d) +
      2 * (C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 * (Λ / lam) * ((∑ x ∈ Q.vertices, ∑ k : Fin d,
        (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0)) /
          (Q.size : ℝ) ^ d)) := by
    field_simp
  rw [e] at h2'
  have e2 : C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 * (Λ / lam *
      interpolationGradBound P K N₃ m K' N' m' 2 p ((Q.size : ℝ) ^ d) u) =
      C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 * (Λ / lam) *
        interpolationGradBound P K N₃ m K' N' m' 2 p ((Q.size : ℝ) ^ d) u := by ring
  rw [e2]
  linarith

end Rigidity.Dirichlet

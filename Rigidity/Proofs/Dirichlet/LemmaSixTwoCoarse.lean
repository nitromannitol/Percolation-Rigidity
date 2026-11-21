import Rigidity.Proofs.Dirichlet.LemmaSixTwoInner
import Rigidity.Proofs.Dirichlet.Interpolation

/-!
# Lemma 6.2 on the lattice with the boundary interpolation of the coarsened function

With the datum `w̃ = boundaryInterpolation 𝒫 B u` of Lemma 6.4 and `Q ⊆ cl_𝒫` (the domain of the
coarse-graining data), the sums of the gradient of `w̃` over the edges inside `Q` in
`innerEdgeEnergy_dirichletSolution_div_le_of_mu_test` are bounded by Lemma 6.4 (iii)
(`sum_abs_grad_boundaryInterpolation_rpow_div_le`), so that
`L^{-d} E_hom(u_hom) ≤ L^{-d} (Σ_Q e + 2 Σ δ) + 2 Λ N^{-1/2} 𝔅₂ + Λ (2d(r + 1 + N)/L)^{1 − 2/s}
  (d^{s/2−1} (1 + 3^{s−1} (1 + 2^s + d^s (N/r)^s)) 𝔅_s)^{2/s}`,
where `𝔅_s = interpolationGradBound … s p L^d u` is the right side of Lemma 6.4 (iii): the
moments of the partition sizes times `(L^{-d} Σ_{C_*} |∇u 1_{a≠0}|^p)^{s/p}` (`M^s` in the
source). This is Armstrong–Dario, Lemma 6.2, on the lattice, with the `μ` test as hypothesis
(`innerEdgeEnergy_dirichletSolution_div_le_of_coarse`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Dirichlet

open Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The right side of Lemma 6.4 (iii): the moments of the partition sizes times the normalized
`L^p` norm of the gradient of `u` on the cluster to the power `s/p`. -/
noncomputable def interpolationGradBound (P : CoarseData d ω) (K N m K' N' m' : ℕ) (s p V : ℝ)
    (u : Vertex d → ℝ) : ℝ :=
  (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) *
      (2 * (d : ℝ) * N * K * 3 ^ (m * d) * (2 * √(d : ℝ))) ^ s *
      ((∑ z ∈ P.cluster, (((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1)) ^ (p / (p - s))) /
        V) ^ (1 - s / p) +
    2 * d * ((N' : ℝ) * K' * 3 ^ (m' * d) * (2 * √(d : ℝ))) ^ s *
      ((∑ z ∈ P.cluster, (((3 : ℝ) ^ (P.part z).scale) ^ (s * d)) ^ (p / (p - s))) /
        V) ^ (1 - s / p)) *
    ((∑ z ∈ P.cluster, gradNormIn (openGraph ω) P.cluster u z ^ p) / V) ^ (s / p)

/-- The sums of the gradient of `w̃` over the edges inside `Q ⊆ cl_𝒫` are bounded by
Lemma 6.4 (iii). -/
theorem sum_abs_grad_boundaryInterpolation_inner_div_le (P : CoarseData d ω)
    {B : Finset (Vertex d)} (hB : B ⊆ P.cluster) (u : Vertex d → ℝ) {K N m K' N' m' : ℕ}
    (h3 : P.PairOverlap K N m) (hK : 1 ≤ K) (hN : 1 ≤ N) (h2 : P.RegionOverlap K' N' m')
    (hK' : 1 ≤ K') (hN' : 1 ≤ N') (hd : 1 ≤ d) {s p : ℝ} (hs : 1 ≤ s) (hsp : s < p) {V : ℝ}
    (hV : 0 < V) (Q : IntegerCube d) (hQ : Q.vertices ⊆ P.domain) :
    (∑ y ∈ Q.vertices, ∑ k : Fin d, (if y + unit k ∈ Q.vertices then
        |boundaryInterpolation P B u (y + unit k) - boundaryInterpolation P B u y| ^ s
        else 0)) / V ≤ interpolationGradBound P K N m K' N' m' s p V u := by
  refine le_trans (div_le_div_of_nonneg_right ?_ hV.le)
    (sum_abs_grad_boundaryInterpolation_rpow_div_le P hB u h3 hK hN h2 hK' hN' hd hs hsp hV)
  calc ∑ y ∈ Q.vertices, ∑ k : Fin d, (if y + unit k ∈ Q.vertices then
        |boundaryInterpolation P B u (y + unit k) - boundaryInterpolation P B u y| ^ s else 0)
      ≤ ∑ y ∈ Q.vertices, ∑ k : Fin d, (if y + unit k ∈ P.domain then
        |boundaryInterpolation P B u (y + unit k) - boundaryInterpolation P B u y| ^ s else 0) :=
        Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun k _ => by
          by_cases h1 : y + unit k ∈ Q.vertices
          · rw [if_pos h1, if_pos (hQ h1)]
          · rw [if_neg h1]
            split_ifs <;> positivity
    _ ≤ ∑ y ∈ P.domain, ∑ k : Fin d, (if y + unit k ∈ P.domain then
        |boundaryInterpolation P B u (y + unit k) - boundaryInterpolation P B u y| ^ s else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hQ fun x _ _ => Finset.sum_nonneg fun j _ => by
          split_ifs <;> positivity

/-- **Armstrong–Dario, Lemma 6.2, on the lattice with the boundary interpolation.** -/
theorem innerEdgeEnergy_dirichletSolution_div_le_of_coarse (hd : 1 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ k, 0 < a k) {Λ : ℝ} (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size)
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (P : CoarseData d ω) {B : Finset (Vertex d)}
    (hB : B ⊆ P.cluster) (u : Vertex d → ℝ) {K N m K' N' m' : ℕ}
    (h3 : P.PairOverlap K N m) (hK : 1 ≤ K) (hN : 1 ≤ N) (h2 : P.RegionOverlap K' N' m')
    (hK' : 1 ≤ K') (hN' : 1 ≤ N') (hQ : Q.vertices ⊆ P.domain) {s p : ℝ} (hs : 2 ≤ s)
    (hsp : s < p) (μ δ e : Vertex d → ℝ) (he : ∀ y, 0 ≤ e y)
    (htest : ∀ x ∈ (trimCube Q n).vertices \ cubeLayer (trimCube Q n) (r + 1),
      μ x ≤ (∑ y ∈ (cornerCube x n).vertices, e y) / (n : ℝ) ^ d / 2 -
        ∑ k, a k * cubeSlope n (boundaryInterpolation P B u) x k *
          cubeEdgeSlope n (boundaryInterpolation P B u) x k)
    (hconv : ∀ x ∈ (trimCube Q n).vertices \ cubeLayer (trimCube Q n) (r + 1),
      |(∑ k, (a k * cubeSlope n (boundaryInterpolation P B u) x k) ^ 2 / a k) / 2 + μ x| ≤
        δ x) :
    innerEdgeEnergy (constCond a) Q
        (dirichletSolution (constCond a) (cubeInterior Q) (boundaryInterpolation P B u)) /
        (Q.size : ℝ) ^ d ≤
      (∑ y ∈ Q.vertices, e y +
          2 * ∑ x ∈ (trimCube Q n).vertices \ cubeLayer (trimCube Q n) (r + 1), δ x) /
            (Q.size : ℝ) ^ d +
        2 * (Λ / √(n : ℝ) * interpolationGradBound P K N m K' N' m' 2 p ((Q.size : ℝ) ^ d) u) +
        Λ * ((2 * d * ((r + 1 + n : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((n : ℝ) / r) ^ s)) *
              interpolationGradBound P K N m K' N' m' s p ((Q.size : ℝ) ^ d) u)) ^ (2 / s)) := by
  have hΛ : 0 ≤ Λ := (ha ⟨0, hd⟩).le.trans (haΛ _)
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  set w := boundaryInterpolation P B u
  have key := innerEdgeEnergy_dirichletSolution_div_le_of_mu_test hd a ha haΛ Q hL hn hr w hs μ δ
    e he htest hconv
  -- the quadratic sum of the datum, by Lemma 6.4 (iii) with `s = 2`
  have hb2 := sum_abs_grad_boundaryInterpolation_inner_div_le P hB u h3 hK hN h2 hK' hN' hd
    (s := 2) (p := p) (by norm_num) (by linarith) hV Q hQ
  have hsq : ∑ y ∈ Q.vertices, ∑ k : Fin d,
      (if y + unit k ∈ Q.vertices then (w (y + unit k) - w y) ^ 2 else 0) =
      ∑ y ∈ Q.vertices, ∑ k : Fin d,
        (if y + unit k ∈ Q.vertices then |w (y + unit k) - w y| ^ (2 : ℝ) else 0) :=
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => by
      split_ifs
      · rw [Real.rpow_two, sq_abs]
      · rfl
  -- the `s`-th power sum, by Lemma 6.4 (iii)
  have hbs := sum_abs_grad_boundaryInterpolation_inner_div_le P hB u h3 hK hN h2 hK' hN' hd
    (s := s) (p := p) (by linarith) hsp hV Q hQ
  set S2 := ∑ y ∈ Q.vertices, ∑ k : Fin d,
    (if y + unit k ∈ Q.vertices then (w (y + unit k) - w y) ^ 2 else 0)
  set Ss := ∑ y ∈ Q.vertices, ∑ k : Fin d,
    (if y + unit k ∈ Q.vertices then |w (y + unit k) - w y| ^ s else 0)
  have hSs0 : 0 ≤ Ss := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs <;> positivity
  have hb2' : S2 / (Q.size : ℝ) ^ d ≤
      interpolationGradBound P K N m K' N' m' 2 p ((Q.size : ℝ) ^ d) u := by
    rw [hsq]
    exact hb2
  refine key.trans ?_
  have e1 : (∑ y ∈ Q.vertices, e y +
      2 * ∑ x ∈ (trimCube Q n).vertices \ cubeLayer (trimCube Q n) (r + 1), δ x +
        2 * (Λ / √(n : ℝ) * S2)) / (Q.size : ℝ) ^ d =
      (∑ y ∈ Q.vertices, e y +
        2 * ∑ x ∈ (trimCube Q n).vertices \ cubeLayer (trimCube Q n) (r + 1), δ x) /
          (Q.size : ℝ) ^ d + 2 * (Λ / √(n : ℝ) * (S2 / (Q.size : ℝ) ^ d)) := by
    field_simp
  rw [e1]
  have hC : 0 ≤ (d : ℝ) ^ (s / 2 - 1) *
      (1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((n : ℝ) / r) ^ s)) := by positivity
  have h4 : (d : ℝ) ^ (s / 2 - 1) *
      ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((n : ℝ) / r) ^ s)) * Ss) /
        (Q.size : ℝ) ^ d ≤
      (d : ℝ) ^ (s / 2 - 1) *
        ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((n : ℝ) / r) ^ s)) *
          interpolationGradBound P K N m K' N' m' s p ((Q.size : ℝ) ^ d) u) := by
    rw [← mul_assoc, ← mul_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hbs hC
  have h5 := Real.rpow_le_rpow (by positivity) h4 (show (0 : ℝ) ≤ 2 / s by positivity)
  have h6 := mul_le_mul_of_nonneg_left h5
    (show (0 : ℝ) ≤ (2 * d * ((r + 1 + n : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) by positivity)
  have h7 := mul_le_mul_of_nonneg_left h6 hΛ
  have h8 := mul_le_mul_of_nonneg_left hb2'
    (show (0 : ℝ) ≤ 2 * (Λ / √(n : ℝ)) by positivity)
  linarith

end Rigidity.Dirichlet

import Rigidity.Proofs.Dirichlet.MesoscopicInterpolation
import Rigidity.Proofs.Dirichlet.LayerEnergy
import Rigidity.Proofs.Dirichlet.CubeCutoff
import Rigidity.Proofs.Dirichlet.AffineApproximation

/-!
# The trial function of Lemma 6.2

With the cutoff `η = η_Q` of the cube `Q` at depth `r ≥ 1`, the interpolation
`ũ = w + η (ξ_N(w) − w)` between the boundary datum `w` and its mesoscopic average equals `w` off
the interior of `Q`, so it is an admissible competitor for the homogenized Dirichlet problem with
datum `w`, and off the boundary layer of width `r + 1` its gradient is the mesoscopic slope
`p(x) = ⟨∇w⟩_{x + □_N}`. Hence its homogenized energy is at most `Σ_{Q ∖ layer} p·ā p` plus `Λ`
times its energy in the layer.

This is the construction `ũ = η ξ + (1 − η) w` and Step 5 of the proof of Armstrong–Dario,
Lemma 6.2 ((6.27)–(6.28)), on the lattice; the energy in the layer is then small by the
boundary-layer estimate and the `L^{p'}` bound of `∇ũ`.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The trial function equals the datum off the interior of `Q`. -/
theorem mesoInterpolation_cubeCutoff_of_not_mem (Q : IntegerCube d) (N r : ℕ)
    (w : Vertex d → ℝ) {x : Vertex d} (hx : x ∉ cubeInterior Q) :
    mesoInterpolation N (cubeCutoff Q r) w x = w x := by
  apply mesoInterpolation_eq_of_eq_zero
  by_contra h
  obtain ⟨hxQ, hnb⟩ := mem_vertices_of_cubeCutoff_ne_zero Q r h
  apply hx
  refine Finset.mem_filter.mpr ⟨hxQ, fun k => ?_⟩
  have h1 := (IntegerCube.mem_vertices Q _).mp (hnb k).1 k
  have h2 := (IntegerCube.mem_vertices Q _).mp (hnb k).2 k
  rw [add_unit_apply, if_pos rfl] at h1
  rw [sub_unit_apply, if_pos rfl] at h2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Off the boundary layer of width `r + 1`, the gradient of the trial function is the mesoscopic
slope of the datum. -/
theorem mesoInterpolation_cubeCutoff_grad (Q : IntegerCube d) (N : ℕ) {r : ℕ} (hr : 0 < r)
    (w : Vertex d → ℝ) {x : Vertex d} (hxQ : x ∈ Q.vertices) (hx : x ∉ cubeLayer Q (r + 1))
    (k : Fin d) :
    mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
        mesoInterpolation N (cubeCutoff Q r) w x = cubeSlope N w x k := by
  have hc : ∀ j, Q.corner j + (r + 1) ≤ x j ∧ x j + (r + 1) < Q.corner j + Q.size := by
    intro j
    by_contra h
    apply hx
    refine Finset.mem_filter.mpr ⟨hxQ, j, ?_⟩
    push_cast
    omega
  have h1 : cubeCutoff Q r x = 1 :=
    cubeCutoff_eq_one Q hr fun j => ⟨by linarith [(hc j).1], by linarith [(hc j).2]⟩
  have h2 : cubeCutoff Q r (x + unit k) = 1 := by
    refine cubeCutoff_eq_one Q hr fun j => ?_
    rw [add_unit_apply]
    split_ifs <;> constructor <;> linarith [(hc j).1, (hc j).2]
  rw [mesoInterpolation_eq_of_eq_one N w h2, mesoInterpolation_eq_of_eq_one N w h1,
    cubeAverage_add_unit_sub]
  rfl

/-- **The energy of the trial function**: for `a_k ≤ Λ` and `r ≥ 1`,
`Σ_{x∈Q} Σ_k a_k (∇_k ũ)² ≤ Σ_{x ∈ Q ∖ layer} Σ_k a_k p_k(x)² + Λ Σ_{x ∈ layer} Σ_k (∇_k ũ)²`. -/
theorem sum_energy_mesoInterpolation_le (a : Fin d → ℝ) {Λ : ℝ}
    (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (N : ℕ) {r : ℕ} (hr : 0 < r)
    (w : Vertex d → ℝ) :
    ∑ x ∈ Q.vertices, ∑ k : Fin d, a k * (mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
        mesoInterpolation N (cubeCutoff Q r) w x) ^ 2 ≤
      ∑ x ∈ Q.vertices \ cubeLayer Q (r + 1), ∑ k : Fin d, a k * cubeSlope N w x k ^ 2 +
        Λ * ∑ x ∈ cubeLayer Q (r + 1), ∑ k : Fin d,
          (mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
            mesoInterpolation N (cubeCutoff Q r) w x) ^ 2 := by
  rw [← Finset.sum_sdiff (cubeLayer_subset Q (r + 1))]
  refine add_le_add (le_of_eq (Finset.sum_congr rfl fun x hx => ?_)) ?_
  · obtain ⟨hxQ, hxL⟩ := Finset.mem_sdiff.mp hx
    exact Finset.sum_congr rfl fun k _ => by
      rw [mesoInterpolation_cubeCutoff_grad Q N hr w hxQ hxL k]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (haΛ k) (sq_nonneg _)

/-- **Power mean on the coordinates**: for `s ≥ 2`, `|(Σ_k f_k²)^{1/2}|^s ≤ d^{s/2−1} Σ_k |f_k|^s`. -/
theorem abs_sqrt_sum_sq_rpow_le (f : Fin d → ℝ) {s : ℝ} (hs : 2 ≤ s) :
    |√(∑ k, f k ^ 2)| ^ s ≤ (d : ℝ) ^ (s / 2 - 1) * ∑ k, |f k| ^ s := by
  have hs1 : 1 ≤ s / 2 := by linarith
  have hY : 0 ≤ ∑ k, f k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h1 : |√(∑ k, f k ^ 2)| ^ s = (∑ k, f k ^ 2) ^ (s / 2) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hY]
    congr 1
    ring
  have h2 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.univ : Finset (Fin d)) hs1
    (f := fun k => f k ^ 2) fun k _ => sq_nonneg _
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : ∀ k : Fin d, (f k ^ 2) ^ (s / 2) = |f k| ^ s := fun k => by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  simp only [h3] at h2
  rw [h1]
  exact h2

/-- **The energy of the trial function in the boundary layer**: for `s ≥ 2`, `N, r ≥ 1`, a cube of
side `L ≥ 1` and `B ⊇ Q + {0, …, N − 1}^d`,
`L^{-d} Σ_{layer} Σ_k (∇_k ũ)² ≤ (2d(r + 1)/L)^{1 − 2/s}
  (d^{s/2 − 1} 3^{s−1} (1 + 2^s + d^s (N/r)^s) L^{-d} Σ_B Σ_k |∇_k w|^s)^{2/s}`. -/
theorem sum_layer_energy_mesoInterpolation_div_le (Q : IntegerCube d) (hL : 0 < Q.size)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 2 ≤ s)
    (B : Finset (Vertex d)) (hB : ∀ x ∈ Q.vertices, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B) :
    (∑ x ∈ cubeLayer Q (r + 1), ∑ k : Fin d,
        (mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
          mesoInterpolation N (cubeCutoff Q r) w x) ^ 2) / (Q.size : ℝ) ^ d ≤
      (2 * d * ((r + 1 : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
        ((d : ℝ) ^ (s / 2 - 1) *
          ((3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s) *
          ∑ y ∈ B, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) / (Q.size : ℝ) ^ d) ^ (2 / s) := by
  set u := mesoInterpolation N (cubeCutoff Q r) w
  set g : Vertex d → ℝ := fun x => √(∑ k : Fin d, (u (x + unit k) - u x) ^ 2) with hg
  have hs0 : 0 < s := by linarith
  have hg2 : ∀ x, g x ^ 2 = ∑ k : Fin d, (u (x + unit k) - u x) ^ 2 := fun x => by
    rw [hg, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  have hlayer := sum_sq_cubeLayer_div_le Q hL (r + 1) g hs
  simp only [hg2] at hlayer
  refine hlayer.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right ?_ (by positivity))
    (by positivity)
  have hgs : ∀ x, |g x| ^ s ≤ (d : ℝ) ^ (s / 2 - 1) * ∑ k : Fin d, |u (x + unit k) - u x| ^ s :=
    fun x => abs_sqrt_sum_sq_rpow_le (fun k => u (x + unit k) - u x) hs
  have hmeso := sum_abs_grad_mesoInterpolation_rpow_le Q.vertices B hN hr (cubeCutoff Q r) w
    (cubeCutoff_nonneg Q r) (cubeCutoff_le_one Q r)
    (fun x _ j => abs_cubeCutoff_add_unit_sub_le Q r x j) (s := s) (by linarith) hB
  calc ∑ x ∈ Q.vertices, |g x| ^ s
      ≤ ∑ x ∈ Q.vertices, (d : ℝ) ^ (s / 2 - 1) * ∑ k : Fin d, |u (x + unit k) - u x| ^ s :=
        Finset.sum_le_sum fun x _ => hgs x
    _ = (d : ℝ) ^ (s / 2 - 1) * ∑ x ∈ Q.vertices, ∑ k : Fin d, |u (x + unit k) - u x| ^ s := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmeso (by positivity)

theorem coversEdges_cubeInterior (Q : IntegerCube d) :
    CoversEdges (cubeInterior Q) Q.vertices := by
  intro x j hx
  rcases hx with hx | hx
  · exact (Finset.mem_filter.mp hx).1
  · obtain ⟨hxQ, hxi⟩ := Finset.mem_filter.mp hx
    rw [IntegerCube.mem_vertices] at hxQ ⊢
    intro k
    have h1 := hxQ k
    have h2 := hxi k
    rw [add_unit_apply] at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The homogenized half of Armstrong–Dario, Lemma 6.2, on the lattice**: for constant
conductances `0 < a_k ≤ Λ`, the homogenized solution `u_hom` with datum `w` on the cube `Q`
(of side `L`) satisfies, for `N, r ≥ 1`, `s ≥ 2` and `B ⊇ Q + {0, …, N − 1}^d`,
`L^{-d} E_hom(u_hom) ≤ L^{-d} Σ_{Q ∖ layer} Σ_k a_k p_k² + Λ (2d(r + 1)/L)^{1 − 2/s}
  (d^{s/2−1} 3^{s−1} (1 + 2^s + d^s (N/r)^s) L^{-d} Σ_B Σ_k |∇_k w|^s)^{2/s}`,
with `p_k(x) = ⟨∇_k w⟩_{x + □_N}` the mesoscopic slopes and the layer of width `r + 1`. -/
theorem edgeEnergy_dirichletSolution_div_le (hd : 1 ≤ d) (a : Fin d → ℝ) (ha : ∀ k, 0 < a k)
    {Λ : ℝ} (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size) {N r : ℕ} (hN : 0 < N)
    (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 2 ≤ s) (B : Finset (Vertex d))
    (hB : ∀ x ∈ Q.vertices, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B) :
    edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d ≤
      (∑ x ∈ Q.vertices \ cubeLayer Q (r + 1), ∑ k : Fin d, a k * cubeSlope N w x k ^ 2) /
          (Q.size : ℝ) ^ d +
        Λ * ((2 * d * ((r + 1 : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s) *
              ∑ y ∈ B, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) / (Q.size : ℝ) ^ d) ^ (2 / s)) := by
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  have hΛ : 0 ≤ Λ := (ha ⟨0, hd⟩).le.trans (haΛ _)
  have hmin := edgeEnergy_dirichletSolution_le hd (constCond a) (fun e => ha e.2)
    (coversEdges_cubeInterior Q) w (mesoInterpolation N (cubeCutoff Q r) w)
    (fun x hx => mesoInterpolation_cubeCutoff_of_not_mem Q N r w hx)
  have htrial := sum_energy_mesoInterpolation_le a haΛ Q N hr w
  have hlayer := sum_layer_energy_mesoInterpolation_div_le Q hL hN hr w hs B hB
  have hE : edgeEnergy (constCond a) Q.vertices (mesoInterpolation N (cubeCutoff Q r) w) =
      ∑ x ∈ Q.vertices, ∑ k : Fin d, a k *
        (mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
          mesoInterpolation N (cubeCutoff Q r) w x) ^ 2 := rfl
  rw [hE] at hmin
  calc edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d
      ≤ (∑ x ∈ Q.vertices \ cubeLayer Q (r + 1), ∑ k : Fin d, a k * cubeSlope N w x k ^ 2 +
          Λ * ∑ x ∈ cubeLayer Q (r + 1), ∑ k : Fin d,
            (mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
              mesoInterpolation N (cubeCutoff Q r) w x) ^ 2) / (Q.size : ℝ) ^ d :=
        div_le_div_of_nonneg_right (hmin.trans htrial) hV.le
    _ = (∑ x ∈ Q.vertices \ cubeLayer Q (r + 1), ∑ k : Fin d, a k * cubeSlope N w x k ^ 2) /
          (Q.size : ℝ) ^ d +
        Λ * ((∑ x ∈ cubeLayer Q (r + 1), ∑ k : Fin d,
            (mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
              mesoInterpolation N (cubeCutoff Q r) w x) ^ 2) / (Q.size : ℝ) ^ d) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlayer hΛ)

end Rigidity.Dirichlet

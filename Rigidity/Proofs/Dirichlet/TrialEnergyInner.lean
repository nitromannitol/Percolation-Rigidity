import Rigidity.Proofs.Dirichlet.TrialEnergy

/-!
# The trial function of Lemma 6.2 with the mesoscopic cubes inside the cube

The trial function of `TrialEnergy` uses the averages of the datum `w` over the cubes `x + □_N`
for `x` in the support of the cutoff, which leave `Q` near its upper faces. Here the cutoff is
taken on the trimmed cube `Q' = Q.corner + {0, …, L − N − 1}^d`, so that all these cubes lie in
`Q`: the trial function `w + η_{Q'} (ξ_N(w) − w)` equals `w` off the interior of `Q`, has
gradient the mesoscopic slope on `Q' ∖ layer_{Q'}(r + 1)`, and the rest of `Q` lies in the layer
of `Q` of width `r + 1 + N`. Hence
`L^{-d} E_hom(u_hom) ≤ L^{-d} Σ_{Q' ∖ layer} Σ_k a_k p_k² + Λ (2d(r + 1 + N)/L)^{1 − 2/s}
  (d^{s/2−1} (1 + 3^{s−1} (1 + 2^s + d^s (N/r)^s)) L^{-d} Σ_Q Σ_k |∇_k w|^s)^{2/s}`,
with all sums over `Q`, as in Step 5 of the proof of Armstrong–Dario, Lemma 6.2, where the
cutoff lives in `□°_int` (`edgeEnergy_dirichletSolution_div_le_trim`).
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The cube `Q.corner + {0, …, L − N − 1}^d`. -/
def trimCube (Q : IntegerCube d) (N : ℕ) : IntegerCube d := ⟨Q.corner, Q.size - N⟩

theorem trimCube_vertices_subset (Q : IntegerCube d) (N : ℕ) :
    (trimCube Q N).vertices ⊆ Q.vertices := by
  intro x hx
  rw [IntegerCube.mem_vertices] at hx ⊢
  intro k
  have h := hx k
  simp only [trimCube] at h
  refine ⟨h.1, h.2.trans_le ?_⟩
  have : ((Q.size - N : ℕ) : ℤ) ≤ Q.size := by exact_mod_cast Nat.sub_le _ _
  linarith

/-- The cubes `x + □_N` with `x` in the trimmed cube lie in `Q`. -/
theorem add_mem_of_mem_trimCube (Q : IntegerCube d) (N : ℕ) {x o : Vertex d}
    (hx : x ∈ (trimCube Q N).vertices) (ho : o ∈ (cornerCube 0 N).vertices) :
    x + o ∈ Q.vertices := by
  rw [IntegerCube.mem_vertices] at hx ho ⊢
  intro k
  have h1 := hx k
  have h2 := ho k
  simp only [trimCube, cornerCube, Pi.zero_apply, zero_add] at h1 h2
  simp only [Pi.add_apply]
  have : ((Q.size - N : ℕ) : ℤ) ≥ (Q.size : ℤ) - N := by omega
  constructor <;> omega

theorem not_mem_cubeInterior_trimCube (Q : IntegerCube d) (N : ℕ) {x : Vertex d}
    (hx : x ∉ cubeInterior Q) : x ∉ cubeInterior (trimCube Q N) := by
  intro h
  obtain ⟨hxQ', hint⟩ := Finset.mem_filter.mp h
  refine hx (Finset.mem_filter.mpr ⟨trimCube_vertices_subset Q N hxQ', fun k => ?_⟩)
  have h1 := hint k
  simp only [trimCube] at h1
  have : ((Q.size - N : ℕ) : ℤ) ≤ Q.size := by exact_mod_cast Nat.sub_le _ _
  constructor <;> linarith [h1.1, h1.2]

/-- Off the trimmed cube, the step `e_j` stays off the trimmed cube. -/
theorem add_unit_not_mem_trimCube (Q : IntegerCube d) (N : ℕ) {x : Vertex d}
    (hxQ : x ∈ Q.vertices) (hx : x ∉ (trimCube Q N).vertices) (j : Fin d) :
    x + unit j ∉ (trimCube Q N).vertices := by
  intro h
  apply hx
  rw [IntegerCube.mem_vertices] at hxQ h ⊢
  intro k
  have h1 := hxQ k
  have h2 := h k
  simp only [trimCube] at h2 ⊢
  rw [add_unit_apply] at h2
  have h01 : (0 : ℤ) ≤ (if k = j then 1 else 0) := by split_ifs <;> norm_num
  constructor <;> linarith [h1.1, h2.1, h2.2]

/-- The points of `Q` off `Q' ∖ layer_{Q'}(r + 1)` lie in the layer of `Q` of width `r + 1 + N`. -/
theorem sdiff_trimCube_subset_cubeLayer (Q : IntegerCube d) (N r : ℕ) :
    Q.vertices \ ((trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1)) ⊆
      cubeLayer Q (r + 1 + N) := by
  intro x hx
  obtain ⟨hxQ, hxA⟩ := Finset.mem_sdiff.mp hx
  refine Finset.mem_filter.mpr ⟨hxQ, ?_⟩
  have hc : ((Q.size - N : ℕ) : ℤ) ≥ (Q.size : ℤ) - N := by omega
  by_cases hT : x ∈ (trimCube Q N).vertices
  · have hL : x ∈ cubeLayer (trimCube Q N) (r + 1) := by
      by_contra h
      exact hxA (Finset.mem_sdiff.mpr ⟨hT, h⟩)
    obtain ⟨_, k, hk⟩ := Finset.mem_filter.mp hL
    refine ⟨k, ?_⟩
    simp only [trimCube] at hk
    push_cast at hk ⊢
    rcases hk with hk | hk
    · left
      linarith
    · right
      linarith
  · rw [IntegerCube.mem_vertices] at hT hxQ
    push Not at hT
    obtain ⟨k, hk⟩ := hT
    refine ⟨k, Or.inr ?_⟩
    simp only [trimCube] at hk
    have h1 := hxQ k
    push_cast
    have := hk h1.1
    linarith

/-- Off the trimmed cube the trial function has the gradient of the datum. -/
theorem mesoInterpolation_trimCube_grad_of_not_mem (Q : IntegerCube d) (N r : ℕ)
    (w : Vertex d → ℝ) {x : Vertex d} (hxQ : x ∈ Q.vertices)
    (hx : x ∉ (trimCube Q N).vertices) (j : Fin d) :
    mesoInterpolation N (cubeCutoff (trimCube Q N) r) w (x + unit j) -
        mesoInterpolation N (cubeCutoff (trimCube Q N) r) w x = w (x + unit j) - w x := by
  have h0 : ∀ y, y ∉ (trimCube Q N).vertices → cubeCutoff (trimCube Q N) r y = 0 := by
    intro y hy
    by_contra h
    exact hy (mem_vertices_of_cubeCutoff_ne_zero _ r h).1
  rw [mesoInterpolation_eq_of_eq_zero N w (h0 _ (add_unit_not_mem_trimCube Q N hxQ hx j)),
    mesoInterpolation_eq_of_eq_zero N w (h0 _ hx)]

/-- **The gradient of the trial function in `L^s` on `Q`.** -/
theorem sum_abs_grad_mesoInterpolation_trimCube_rpow_le (Q : IntegerCube d) {N r : ℕ}
    (hN : 0 < N) (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ Q.vertices, ∑ j : Fin d,
        |mesoInterpolation N (cubeCutoff (trimCube Q N) r) w (x + unit j) -
          mesoInterpolation N (cubeCutoff (trimCube Q N) r) w x| ^ s ≤
      (1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s)) *
        ∑ y ∈ Q.vertices, ∑ j : Fin d, |w (y + unit j) - w y| ^ s := by
  set Q' := trimCube Q N
  set u := mesoInterpolation N (cubeCutoff Q' r) w
  set W := ∑ y ∈ Q.vertices, ∑ j : Fin d, |w (y + unit j) - w y| ^ s
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rw [← Finset.sum_sdiff (trimCube_vertices_subset Q N)]
  have h1 : ∑ x ∈ Q.vertices \ Q'.vertices, ∑ j : Fin d, |u (x + unit j) - u x| ^ s ≤ W := by
    calc ∑ x ∈ Q.vertices \ Q'.vertices, ∑ j : Fin d, |u (x + unit j) - u x| ^ s
        = ∑ x ∈ Q.vertices \ Q'.vertices, ∑ j : Fin d, |w (x + unit j) - w x| ^ s :=
          Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun j _ => by
            obtain ⟨hxQ, hxQ'⟩ := Finset.mem_sdiff.mp hx
            rw [mesoInterpolation_trimCube_grad_of_not_mem Q N r w hxQ hxQ' j]
      _ ≤ W := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => by positivity
  have h2 := sum_abs_grad_mesoInterpolation_rpow_le Q'.vertices Q.vertices hN hr
    (cubeCutoff Q' r) w (cubeCutoff_nonneg Q' r) (cubeCutoff_le_one Q' r)
    (fun x _ j => abs_cubeCutoff_add_unit_sub_le Q' r x j) hs
    (fun x hx o ho => add_mem_of_mem_trimCube Q N hx ho)
  have : (1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s)) * W =
      W + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s) * W := by ring
  rw [this]
  exact add_le_add h1 h2

/-- **The homogenized half of Lemma 6.2 with the mesoscopic cubes inside `Q`.** -/
theorem edgeEnergy_dirichletSolution_div_le_trim (hd : 1 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ k, 0 < a k) {Λ : ℝ} (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (w : Vertex d → ℝ) {s : ℝ} (hs : 2 ≤ s) :
    edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d ≤
      (∑ x ∈ (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1),
          ∑ k : Fin d, a k * cubeSlope N w x k ^ 2) / (Q.size : ℝ) ^ d +
        Λ * ((2 * d * ((r + 1 + N : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s)) *
              ∑ y ∈ Q.vertices, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) /
                (Q.size : ℝ) ^ d) ^ (2 / s)) := by
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  have hΛ : 0 ≤ Λ := (ha ⟨0, hd⟩).le.trans (haΛ _)
  set Q' := trimCube Q N
  set u := mesoInterpolation N (cubeCutoff Q' r) w
  set A' := Q'.vertices \ cubeLayer Q' (r + 1)
  have hA'Q : A' ⊆ Q.vertices := Finset.sdiff_subset.trans (trimCube_vertices_subset Q N)
  -- the Dirichlet principle
  have hmin := edgeEnergy_dirichletSolution_le hd (constCond a) (fun e => ha e.2)
    (coversEdges_cubeInterior Q) w u
    (fun x hx => mesoInterpolation_cubeCutoff_of_not_mem Q' N r w
      (not_mem_cubeInterior_trimCube Q N hx))
  -- the energy of the trial function
  have hsplit : edgeEnergy (constCond a) Q.vertices u ≤
      ∑ x ∈ A', ∑ k : Fin d, a k * cubeSlope N w x k ^ 2 +
        Λ * ∑ x ∈ Q.vertices \ A', ∑ k : Fin d, (u (x + unit k) - u x) ^ 2 := by
    rw [edgeEnergy, ← Finset.sum_sdiff hA'Q, add_comm]
    refine add_le_add (le_of_eq (Finset.sum_congr rfl fun x hx => ?_)) ?_
    · obtain ⟨hxQ', hxL⟩ := Finset.mem_sdiff.mp hx
      exact Finset.sum_congr rfl fun k _ => by
        rw [mesoInterpolation_cubeCutoff_grad Q' N hr w hxQ' hxL k]
        rfl
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (haΛ k) (sq_nonneg _)
  -- the layer
  set g : Vertex d → ℝ := fun x => √(∑ k : Fin d, (u (x + unit k) - u x) ^ 2) with hg
  have hs1 : 1 ≤ s / 2 := by linarith
  have hg2 : ∀ x, g x ^ 2 = ∑ k : Fin d, (u (x + unit k) - u x) ^ 2 := fun x => by
    rw [hg, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  have hhol := sum_sq_div_le_card_div_rpow_mul (Finset.sdiff_subset (s := Q.vertices) (t := A'))
    g hs hV
  simp only [hg2] at hhol
  have he : 0 ≤ 1 - 2 / s := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hs
  have hcard0 : (#(Q.vertices \ A') : ℝ) ≤ #(cubeLayer Q (r + 1 + N)) := by
    exact_mod_cast Finset.card_le_card (sdiff_trimCube_subset_cubeLayer Q N r)
  have hcard : (#(Q.vertices \ A') : ℝ) / (Q.size : ℝ) ^ d ≤
      2 * d * ((r + 1 + N : ℕ) : ℝ) / Q.size :=
    (div_le_div_of_nonneg_right hcard0 hV.le).trans (card_cubeLayer_div_le Q hL _)
  have hgs : ∀ x, |g x| ^ s ≤ (d : ℝ) ^ (s / 2 - 1) * ∑ k : Fin d, |u (x + unit k) - u x| ^ s := by
    intro x
    have hY : 0 ≤ ∑ k : Fin d, (u (x + unit k) - u x) ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have h1 : |g x| ^ s = (∑ k : Fin d, (u (x + unit k) - u x) ^ 2) ^ (s / 2) := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hY]
      congr 1
      ring
    have h2 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.univ : Finset (Fin d)) hs1
      (f := fun k => (u (x + unit k) - u x) ^ 2) fun k _ => sq_nonneg _
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : ∀ k : Fin d, ((u (x + unit k) - u x) ^ 2) ^ (s / 2) = |u (x + unit k) - u x| ^ s :=
      fun k => by
        rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        push_cast
        ring
    simp only [h3] at h2
    rw [h1]
    exact h2
  have hmeso := sum_abs_grad_mesoInterpolation_trimCube_rpow_le Q hN hr w (s := s) (by linarith)
  have hsum : ∑ x ∈ Q.vertices, |g x| ^ s ≤ (d : ℝ) ^ (s / 2 - 1) *
      ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s)) *
        ∑ y ∈ Q.vertices, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) := by
    calc ∑ x ∈ Q.vertices, |g x| ^ s
        ≤ ∑ x ∈ Q.vertices, (d : ℝ) ^ (s / 2 - 1) * ∑ k : Fin d, |u (x + unit k) - u x| ^ s :=
          Finset.sum_le_sum fun x _ => hgs x
      _ = (d : ℝ) ^ (s / 2 - 1) * ∑ x ∈ Q.vertices, ∑ k : Fin d, |u (x + unit k) - u x| ^ s := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmeso (by positivity)
  have hlayer : (∑ x ∈ Q.vertices \ A', ∑ k : Fin d, (u (x + unit k) - u x) ^ 2) /
      (Q.size : ℝ) ^ d ≤
      (2 * d * ((r + 1 + N : ℕ) : ℝ) / Q.size) ^ (1 - 2 / s) *
        ((d : ℝ) ^ (s / 2 - 1) *
          ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s)) *
            ∑ y ∈ Q.vertices, ∑ k : Fin d, |w (y + unit k) - w y| ^ s) /
              (Q.size : ℝ) ^ d) ^ (2 / s) := by
    refine hhol.trans (mul_le_mul (Real.rpow_le_rpow (by positivity) hcard he)
      (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hsum hV.le)
        (by positivity)) (by positivity) (by positivity))
  calc edgeEnergy (constCond a) Q.vertices (dirichletSolution (constCond a) (cubeInterior Q) w) /
        (Q.size : ℝ) ^ d
      ≤ (∑ x ∈ A', ∑ k : Fin d, a k * cubeSlope N w x k ^ 2 +
          Λ * ∑ x ∈ Q.vertices \ A', ∑ k : Fin d, (u (x + unit k) - u x) ^ 2) /
            (Q.size : ℝ) ^ d :=
        div_le_div_of_nonneg_right (hmin.trans hsplit) hV.le
    _ = (∑ x ∈ A', ∑ k : Fin d, a k * cubeSlope N w x k ^ 2) / (Q.size : ℝ) ^ d +
        Λ * ((∑ x ∈ Q.vertices \ A', ∑ k : Fin d, (u (x + unit k) - u x) ^ 2) /
          (Q.size : ℝ) ^ d) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlayer hΛ)

end Rigidity.Dirichlet

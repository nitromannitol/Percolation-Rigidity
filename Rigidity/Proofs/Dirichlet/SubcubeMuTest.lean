import Rigidity.Proofs.Dirichlet.CubeTiling
import Rigidity.Proofs.Dirichlet.CoarseGradientDefect
import Rigidity.Proofs.Dirichlet.BoundaryLayer

/-!
# The `μ` test on a cube from the tests on subcubes

Lemma 6.2 on the lattice (`innerEdgeEnergy_dirichletSolution_div_le_of_mu_test`) uses, at every
translate `x + □` of a mesoscopic cube of side `N`, a number `μ(x)` with the test inequality
`μ(x) ≤ E(x)/(2 N^d) − Σ_k a_k p_k G_k` and the convergence `|q · ā⁻¹ q/2 + μ(x)| ≤ δ(x)`, where
`q = ā p`, `p` is the mesoscopic slope and `G` the edge slope of the datum on `x + □`. On the
cluster, `μ` is defined on triadic cubes; the translates `x + □` are not triadic. This file obtains
such a number from the tests on a block of `M^d` disjoint subcubes of side `K` inside `x + □`:
`μ(x) = N^{-d} Σ_T K^d μ_T − |Σ_k a_k p_k (G_k − N^{-d} Σ_T K^d G_{T,k})|` satisfies the test, and
`|q · ā⁻¹ q/2 + μ(x)|` is at most the average of the errors on the subcubes, the fraction of
`x + □` outside the block times `q · ā⁻¹ q/2`, and the defect of the edge slopes
(`exists_mu_test_of_subcubes`). The defect is at most
`(N^{-1/2} + (1 − (MK)^d/N^d)^{1/2} + K^{-1/2}) (N^{-d} Σ_{x+□} (∇_k w)²)^{1/2}`
(`abs_cubeEdgeSlope_sub_sum_tiles_le`).

This replaces the translates `z + □_n`, `z ∈ 3^k ℤ^d`, of Armstrong and Dario (Definition 5.12 and
the proof of Lemma 6.2, Step 1) by the triadic cubes of scale `k`.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **The `μ` test on a cube from the tests on subcubes.** If `μ_T ≤ E_T/W/2 − Σ_k a_k p_k G_{T,k}`
on the subcubes `T ∈ S` of volume `W` and `Σ_T E_T ≤ E`, then for a cube of volume `V` there is
`μ ≤ E/V/2 − Σ_k a_k p_k G_k` with
`|Σ_k (a_k p_k)²/a_k/2 + μ| ≤ V⁻¹ Σ_T W |Σ_k (a_k p_k)²/a_k/2 + μ_T| + |1 − |S| W/V| |Σ_k (a_k p_k)²/a_k/2|
  + |Σ_k a_k p_k (G_k − V⁻¹ Σ_T W G_{T,k})|`. -/
theorem exists_mu_test_of_subcubes {ι : Type*} (a p G : Fin d → ℝ) {V W E : ℝ} (hV : 0 < V)
    (hW : 0 < W) (S : Finset ι) (μT ET : ι → ℝ) (GT : ι → Fin d → ℝ)
    (htest : ∀ T ∈ S, μT T ≤ ET T / W / 2 - ∑ k, a k * p k * GT T k)
    (hE : ∑ T ∈ S, ET T ≤ E) :
    ∃ μ : ℝ, μ ≤ E / V / 2 - ∑ k, a k * p k * G k ∧
      |(∑ k, (a k * p k) ^ 2 / a k) / 2 + μ| ≤
        (∑ T ∈ S, W * |(∑ k, (a k * p k) ^ 2 / a k) / 2 + μT T|) / V +
          |1 - S.card * W / V| * |(∑ k, (a k * p k) ^ 2 / a k) / 2| +
          |∑ k, a k * p k * (G k - (∑ T ∈ S, W * GT T k) / V)| := by
  set Qf := (∑ k, (a k * p k) ^ 2 / a k) / 2 with hQf
  set X := ∑ k, a k * p k * ∑ T ∈ S, W * GT T k with hX
  set Y := ∑ k, a k * p k * G k with hY
  set D := ∑ k, a k * p k * (G k - (∑ T ∈ S, W * GT T k) / V) with hD
  have hDeq : D = Y - X / V := by
    rw [hD, hY, hX, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hswap : ∑ T ∈ S, W * ∑ k, a k * p k * GT T k = X := by
    rw [hX]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun T _ => by ring
  have hsum : ∑ T ∈ S, W * μT T ≤ E / 2 - X := by
    calc ∑ T ∈ S, W * μT T ≤ ∑ T ∈ S, (ET T / 2 - W * ∑ k, a k * p k * GT T k) := by
          refine Finset.sum_le_sum fun T hT => ?_
          have h := mul_le_mul_of_nonneg_left (htest T hT) hW.le
          have e : W * (ET T / W / 2 - ∑ k, a k * p k * GT T k) =
              ET T / 2 - W * ∑ k, a k * p k * GT T k := by
            field_simp
          linarith
      _ = (∑ T ∈ S, ET T) / 2 - X := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div, hswap]
      _ ≤ E / 2 - X := by linarith
  refine ⟨(∑ T ∈ S, W * μT T) / V - |D|, ?_, ?_⟩
  · have h1 : (∑ T ∈ S, W * μT T) / V ≤ (E / 2 - X) / V :=
      div_le_div_of_nonneg_right hsum hV.le
    have h2 : -|D| ≤ -D := neg_le_neg (le_abs_self D)
    have e : (E / 2 - X) / V - D = E / V / 2 - Y := by
      rw [hDeq]
      field_simp
      ring
    linarith
  · have hsplit : ∑ T ∈ S, W * (Qf + μT T) = S.card * W * Qf + ∑ T ∈ S, W * μT T := by
      rw [Finset.sum_congr rfl (fun T _ => mul_add W Qf (μT T)), Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
      ring
    have e : Qf + ((∑ T ∈ S, W * μT T) / V - |D|) =
        (∑ T ∈ S, W * (Qf + μT T)) / V + (1 - S.card * W / V) * Qf - |D| := by
      rw [hsplit]
      field_simp
      ring
    rw [e]
    have h1 : |(∑ T ∈ S, W * (Qf + μT T)) / V| ≤ (∑ T ∈ S, W * |Qf + μT T|) / V := by
      rw [abs_div, abs_of_pos hV]
      refine div_le_div_of_nonneg_right ?_ hV.le
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun T _ => ?_)
      rw [abs_mul, abs_of_pos hW]
    have h2 : |(1 - S.card * W / V) * Qf| = |1 - S.card * W / V| * |Qf| := abs_mul _ _
    have h3 := abs_sub ((∑ T ∈ S, W * (Qf + μT T)) / V + (1 - S.card * W / V) * Qf) |D|
    rw [abs_abs] at h3
    have h4 := abs_add_le ((∑ T ∈ S, W * (Qf + μT T)) / V) ((1 - S.card * W / V) * Qf)
    rw [h2] at h4
    linarith

/-- The absolute value of a sum is at most the square root of the number of terms times the sum of
the squares. -/
theorem abs_sum_le_sqrt_card_mul_sum_sq {ι : Type*} (A : Finset ι) (g : ι → ℝ) :
    |∑ y ∈ A, g y| ≤ √(A.card * ∑ y ∈ A, g y ^ 2) :=
  Real.abs_le_sqrt (sq_sum_le_card_mul_sum_sq (s := A) (f := g))

/-- **The defect of the edge slopes of the subcubes.** Let `x + □` have side `N`, and let the
subcubes `z + K i + □_K`, `i ∈ {0, …, M − 1}^d`, with `x ≤ z < x + K` and `(M + 1) K ≤ N`, tile a
block inside it. Then the edge slope of `w` on `x + □` and the average of the edge slopes on the
subcubes differ by at most
`(N^{-1/2} + (1 − (MK)^d/N^d)^{1/2} + K^{-1/2}) (N^{-d} Σ_{x+□} (∇_k w)²)^{1/2}`. -/
theorem abs_cubeEdgeSlope_sub_sum_tiles_le {N K M : ℕ} (hK : 0 < K) (hMK : (M + 1) * K ≤ N)
    (w : Vertex d → ℝ) {x z : Vertex d} (hz : ∀ t, x t ≤ z t ∧ z t < x t + K) (k : Fin d) :
    |cubeEdgeSlope N w x k - (∑ i ∈ (cornerCube 0 M).vertices,
        (K : ℝ) ^ d * cubeEdgeSlope K w (z + (K : ℤ) • i) k) / (N : ℝ) ^ d| ≤
      (√(1 / (N : ℝ)) + √(1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d) + √(1 / (K : ℝ))) *
        √((∑ y ∈ (cornerCube x N).vertices, (w (y + unit k) - w y) ^ 2) / (N : ℝ) ^ d) := by
  classical
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hMK
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hVN : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have hVK : (0 : ℝ) < (K : ℝ) ^ d := by positivity
  set g : Vertex d → ℝ := fun y => w (y + unit k) - w y with hg
  set F := (∑ y ∈ (cornerCube x N).vertices, g y ^ 2) / (N : ℝ) ^ d with hF
  have hF0 : 0 ≤ F := div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hVN.le
  set B := (cornerCube z (M * K)).vertices with hB
  set C := (cornerCube x N).vertices with hC
  -- the block lies in the cube
  have hBC : B ⊆ C := by
    intro y hy
    rw [hB, IntegerCube.mem_vertices] at hy
    rw [hC, IntegerCube.mem_vertices]
    intro t
    have h1 := hy t
    have h2 := hz t
    simp only [cornerCube] at h1 ⊢
    have h3 : ((M * K : ℕ) : ℤ) + K ≤ (N : ℤ) := by
      have : ((M + 1) * K : ℕ) ≤ N := hMK
      have : (((M + 1) * K : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast this
      push_cast at this ⊢
      linarith
    constructor <;> omega
  -- the three slopes
  set p := cubeSlope N w x k with hp
  have hpC : p = (∑ y ∈ C, g y) / (N : ℝ) ^ d := rfl
  have htile : ∑ y ∈ B, g y = ∑ i ∈ (cornerCube 0 M).vertices,
      (K : ℝ) ^ d * cubeSlope K w (z + (K : ℤ) • i) k := by
    rw [hB, sum_cornerCube_mul hK z M g]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cubeSlope, cubeAverage]
    rw [mul_div_cancel₀ _ hVK.ne']
  have hdecomp : cubeEdgeSlope N w x k - (∑ i ∈ (cornerCube 0 M).vertices,
      (K : ℝ) ^ d * cubeEdgeSlope K w (z + (K : ℤ) • i) k) / (N : ℝ) ^ d =
      (cubeEdgeSlope N w x k - p) + (∑ y ∈ C \ B, g y) / (N : ℝ) ^ d +
        (∑ i ∈ (cornerCube 0 M).vertices, (K : ℝ) ^ d *
          (cubeSlope K w (z + (K : ℤ) • i) k - cubeEdgeSlope K w (z + (K : ℤ) • i) k)) /
            (N : ℝ) ^ d := by
    have hCB : ∑ y ∈ C \ B, g y = ∑ y ∈ C, g y - ∑ y ∈ B, g y := by
      rw [Finset.sum_sdiff_eq_sub hBC]
    rw [hCB, hpC, htile]
    simp only [mul_sub, Finset.sum_sub_distrib]
    field_simp
    ring
  rw [hdecomp]
  -- term 1: edge slope against slope on the cube
  have t1 : |cubeEdgeSlope N w x k - p| ≤ √(1 / (N : ℝ)) * √F := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.abs_le_sqrt (sq_cubeEdgeSlope_sub_cubeSlope_le hN w x k)
  -- term 2: the part of the cube outside the block
  have hcardC : (C.card : ℝ) = (N : ℝ) ^ d := by
    rw [hC, card_vertices]
    simp [cornerCube]
  have hcardB : (B.card : ℝ) = ((M * K : ℕ) : ℝ) ^ d := by
    rw [hB, card_vertices]
    simp [cornerCube]
  have hMKN : ((M * K : ℕ) : ℝ) ^ d ≤ (N : ℝ) ^ d := by
    rw [← hcardB, ← hcardC]
    exact_mod_cast Finset.card_le_card hBC
  have t2 : |(∑ y ∈ C \ B, g y) / (N : ℝ) ^ d| ≤
      √(1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d) * √F := by
    have h1b : 0 ≤ 1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d := by
      rw [sub_nonneg, div_le_one hVN]
      exact hMKN
    have hcard : ((C \ B).card : ℝ) = (N : ℝ) ^ d - ((M * K : ℕ) : ℝ) ^ d := by
      rw [Finset.card_sdiff_of_subset hBC, Nat.cast_sub (Finset.card_le_card hBC), hcardC, hcardB]
    have hsq : ∑ y ∈ C \ B, g y ^ 2 ≤ ∑ y ∈ C, g y ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => sq_nonneg _
    have hsq2 : ((∑ y ∈ C \ B, g y) / (N : ℝ) ^ d) ^ 2 ≤
        (1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d) * F := by
      rw [div_pow, hF, div_le_iff₀ (by positivity)]
      calc (∑ y ∈ C \ B, g y) ^ 2 ≤ ((C \ B).card : ℝ) * ∑ y ∈ C \ B, g y ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ ≤ ((N : ℝ) ^ d - ((M * K : ℕ) : ℝ) ^ d) * ∑ y ∈ C, g y ^ 2 := by
            rw [hcard]
            exact mul_le_mul_of_nonneg_left hsq (by linarith)
        _ = (1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d) * ((∑ y ∈ C, g y ^ 2) / (N : ℝ) ^ d) *
              ((N : ℝ) ^ d) ^ 2 := by
            field_simp
    rw [← Real.sqrt_mul h1b]
    exact Real.abs_le_sqrt hsq2
  -- term 3: slopes against edge slopes on the subcubes
  have t3 : |(∑ i ∈ (cornerCube 0 M).vertices, (K : ℝ) ^ d *
      (cubeSlope K w (z + (K : ℤ) • i) k - cubeEdgeSlope K w (z + (K : ℤ) • i) k)) /
        (N : ℝ) ^ d| ≤ √(1 / (K : ℝ)) * √F := by
    rw [abs_div, abs_of_pos hVN, ← Real.sqrt_mul (by positivity)]
    set I := (cornerCube (0 : Vertex d) M).vertices with hI
    set b : Vertex d → ℝ := fun i =>
      cubeSlope K w (z + (K : ℤ) • i) k - cubeEdgeSlope K w (z + (K : ℤ) • i) k with hb
    set Fi : Vertex d → ℝ := fun i =>
      (∑ y ∈ (cornerCube (z + (K : ℤ) • i) K).vertices, g y ^ 2) / (K : ℝ) ^ d with hFi
    have hbi : ∀ i, b i ^ 2 ≤ 1 / K * Fi i := fun i => by
      have h := sq_cubeEdgeSlope_sub_cubeSlope_le hK w (z + (K : ℤ) • i) k
      rw [hb]
      calc (cubeSlope K w (z + (K : ℤ) • i) k - cubeEdgeSlope K w (z + (K : ℤ) • i) k) ^ 2
          = (cubeEdgeSlope K w (z + (K : ℤ) • i) k - cubeSlope K w (z + (K : ℤ) • i) k) ^ 2 := by
            ring
        _ ≤ _ := h
    have hcs : (∑ i ∈ I, (K : ℝ) ^ d * b i) ^ 2 ≤
        (∑ i ∈ I, (K : ℝ) ^ d) * ∑ i ∈ I, (K : ℝ) ^ d * (1 / K * Fi i) := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul I (fun _ _ => hVK.le)
        (fun i _ => mul_nonneg hVK.le (mul_nonneg (by positivity)
          (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hVK.le))) fun i _ => ?_
      calc ((K : ℝ) ^ d * b i) ^ 2 = (K : ℝ) ^ d * ((K : ℝ) ^ d * b i ^ 2) := by ring
        _ ≤ (K : ℝ) ^ d * ((K : ℝ) ^ d * (1 / K * Fi i)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbi i) hVK.le) hVK.le
    have hcardI : ∑ i ∈ I, (K : ℝ) ^ d = (((M * K : ℕ) : ℝ)) ^ d := by
      rw [Finset.sum_const, nsmul_eq_mul, hI, card_vertices]
      simp [cornerCube]
      ring
    have hsumF : ∑ i ∈ I, (K : ℝ) ^ d * (1 / K * Fi i) = 1 / K * ∑ y ∈ B, g y ^ 2 := by
      rw [hB, sum_cornerCube_mul hK z M (fun y => g y ^ 2), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hFi]
      field_simp
    have hBsq : ∑ y ∈ B, g y ^ 2 ≤ ∑ y ∈ C, g y ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hBC fun _ _ _ => sq_nonneg _
    have hfin : (∑ i ∈ I, (K : ℝ) ^ d * b i) ^ 2 ≤ (1 / K * F) * ((N : ℝ) ^ d) ^ 2 := by
      refine hcs.trans ?_
      rw [hcardI, hsumF, hF]
      have e : 1 / (K : ℝ) * ((∑ y ∈ C, g y ^ 2) / (N : ℝ) ^ d) * ((N : ℝ) ^ d) ^ 2 =
          (N : ℝ) ^ d * (1 / K * ∑ y ∈ C, g y ^ 2) := by
        field_simp
      rw [e]
      exact mul_le_mul hMKN (mul_le_mul_of_nonneg_left hBsq (by positivity))
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hVN.le
    rw [div_le_iff₀ hVN]
    have h := Real.abs_le_sqrt hfin
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hVN.le] at h
    exact h
  calc |(cubeEdgeSlope N w x k - p) + (∑ y ∈ C \ B, g y) / (N : ℝ) ^ d +
        (∑ i ∈ (cornerCube 0 M).vertices, (K : ℝ) ^ d *
          (cubeSlope K w (z + (K : ℤ) • i) k - cubeEdgeSlope K w (z + (K : ℤ) • i) k)) /
            (N : ℝ) ^ d|
      ≤ |cubeEdgeSlope N w x k - p| + |(∑ y ∈ C \ B, g y) / (N : ℝ) ^ d| +
          |(∑ i ∈ (cornerCube 0 M).vertices, (K : ℝ) ^ d *
            (cubeSlope K w (z + (K : ℤ) • i) k - cubeEdgeSlope K w (z + (K : ℤ) • i) k)) /
              (N : ℝ) ^ d| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ √(1 / (N : ℝ)) * √F + √(1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d) * √F +
          √(1 / (K : ℝ)) * √F := add_le_add (add_le_add t1 t2) t3
    _ = _ := by ring

theorem add_mem_cornerCube_of_mem_zero {N : ℕ} (x : Vertex d) {o : Vertex d}
    (ho : o ∈ (cornerCube 0 N).vertices) : x + o ∈ (cornerCube x N).vertices := by
  rw [IntegerCube.mem_vertices] at ho ⊢
  intro t
  have h := ho t
  simp only [cornerCube, Pi.zero_apply, zero_add, Pi.add_apply] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The square of the slope on a cube is at most the average of the squares of the increments. -/
theorem sq_cubeSlope_le (N : ℕ) (w : Vertex d → ℝ) (x : Vertex d) (k : Fin d) :
    cubeSlope N w x k ^ 2 ≤
      (∑ y ∈ (cornerCube x N).vertices, (w (y + unit k) - w y) ^ 2) / (N : ℝ) ^ d := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [cubeSlope, cubeAverage, pow_zero, div_one]
      have hcard : (cornerCube x 0).vertices.card = 1 := by
        rw [card_vertices]; simp [cornerCube]
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
      rw [hy, Finset.sum_singleton, Finset.sum_singleton]
    · simp only [cubeSlope, cubeAverage, Nat.cast_zero, zero_pow hd.ne', div_zero]
      norm_num
  have hVN : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have hcard : ((cornerCube x N).vertices.card : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]; simp [cornerCube]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (cornerCube x N).vertices)
    (f := fun y => w (y + unit k) - w y)
  rw [hcard] at hcs
  simp only [cubeSlope, cubeAverage, div_pow]
  rw [div_le_div_iff₀ (by positivity) hVN]
  calc (∑ y ∈ (cornerCube x N).vertices, (w (y + unit k) - w y)) ^ 2 * (N : ℝ) ^ d
      ≤ ((N : ℝ) ^ d * ∑ y ∈ (cornerCube x N).vertices, (w (y + unit k) - w y) ^ 2) *
          (N : ℝ) ^ d := mul_le_mul_of_nonneg_right hcs hVN.le
    _ = _ := by ring

/-- **The errors of the subcube tests summed over the translates.** If
`|Σ_k (a_k p_k)²/a_k/2 + μ_{x,i}| ≤ ε Σ_k (a_k p_k)²` on the subcubes, with `p` the slope of `w`
on `x + □`, then the sum over `x ∈ A` of the error bound of `exists_mu_test_of_subcubes`, with the
defect bounded by `abs_cubeEdgeSlope_sub_sum_tiles_le`, is at most
`(ε Λ² + Λ β/2 + Λ γ) Σ_{y ∈ D} Σ_k 1{y + e_k ∈ D} (∇_k w(y))²`, where
`β = 1 − (MK)^d/N^d` and `γ = N^{-1/2} + β^{1/2} + K^{-1/2}`. -/
theorem sum_subcube_errors_le (a : Fin d → ℝ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (ha : ∀ k, 0 < a k)
    (haΛ : ∀ k, a k ≤ Λ) {N K M : ℕ} (hK : 0 < K) (hMK : (M + 1) * K ≤ N) (w : Vertex d → ℝ)
    (A D : Finset (Vertex d))
    (hAD : ∀ x ∈ A, ∀ y ∈ (cornerCube x N).vertices, y ∈ D ∧ ∀ k : Fin d, y + unit k ∈ D)
    (z : Vertex d → Vertex d) (hz : ∀ x ∈ A, ∀ t, x t ≤ z x t ∧ z x t < x t + K)
    (μT : Vertex d → Vertex d → ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ x ∈ A, ∀ i ∈ (cornerCube 0 M).vertices,
      |(∑ k, (a k * cubeSlope N w x k) ^ 2 / a k) / 2 + μT x i| ≤
        ε * ∑ k, (a k * cubeSlope N w x k) ^ 2) :
    ∑ x ∈ A, ((∑ i ∈ (cornerCube 0 M).vertices, (K : ℝ) ^ d *
          |(∑ k, (a k * cubeSlope N w x k) ^ 2 / a k) / 2 + μT x i|) / (N : ℝ) ^ d +
        |1 - ((cornerCube (0 : Vertex d) M).vertices.card : ℝ) * (K : ℝ) ^ d / (N : ℝ) ^ d| *
          |(∑ k, (a k * cubeSlope N w x k) ^ 2 / a k) / 2| +
        |∑ k, a k * cubeSlope N w x k * (cubeEdgeSlope N w x k -
          (∑ i ∈ (cornerCube 0 M).vertices,
            (K : ℝ) ^ d * cubeEdgeSlope K w (z x + (K : ℤ) • i) k) / (N : ℝ) ^ d)|) ≤
      (ε * Λ ^ 2 + Λ * (1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d) / 2 +
          Λ * (√(1 / (N : ℝ)) + √(1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d) + √(1 / (K : ℝ)))) *
        ∑ y ∈ D, ∑ k : Fin d, (if y + unit k ∈ D then (w (y + unit k) - w y) ^ 2 else 0) := by
  classical
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hMK
  have hVN : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have hVK : (0 : ℝ) < (K : ℝ) ^ d := by positivity
  set β := 1 - ((M * K : ℕ) : ℝ) ^ d / (N : ℝ) ^ d with hβ
  set γ := √(1 / (N : ℝ)) + √β + √(1 / (K : ℝ)) with hγ
  have hcardM : ((cornerCube (0 : Vertex d) M).vertices.card : ℝ) * (K : ℝ) ^ d =
      ((M * K : ℕ) : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
    ring
  have hMKN : ((M * K : ℕ) : ℝ) ^ d ≤ (N : ℝ) ^ d := by
    have : M * K ≤ N := le_trans (Nat.mul_le_mul_right K (Nat.le_succ M)) hMK
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast this) d
  have hβ0 : 0 ≤ β := by
    rw [hβ, sub_nonneg, div_le_one hVN]
    exact hMKN
  have hγ0 : 0 ≤ γ := by positivity
  set F : Vertex d → Fin d → ℝ := fun x k =>
    (∑ y ∈ (cornerCube x N).vertices, (w (y + unit k) - w y) ^ 2) / (N : ℝ) ^ d with hF
  have hF0 : ∀ x k, 0 ≤ F x k := fun x k =>
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hVN.le
  set c := ε * Λ ^ 2 + Λ * β / 2 + Λ * γ with hc
  -- the bound at one translate
  have hone : ∀ x ∈ A, ((∑ i ∈ (cornerCube 0 M).vertices, (K : ℝ) ^ d *
          |(∑ k, (a k * cubeSlope N w x k) ^ 2 / a k) / 2 + μT x i|) / (N : ℝ) ^ d +
        |1 - ((cornerCube (0 : Vertex d) M).vertices.card : ℝ) * (K : ℝ) ^ d / (N : ℝ) ^ d| *
          |(∑ k, (a k * cubeSlope N w x k) ^ 2 / a k) / 2| +
        |∑ k, a k * cubeSlope N w x k * (cubeEdgeSlope N w x k -
          (∑ i ∈ (cornerCube 0 M).vertices,
            (K : ℝ) ^ d * cubeEdgeSlope K w (z x + (K : ℤ) • i) k) / (N : ℝ) ^ d)|) ≤
        c * ∑ k, F x k := by
    intro x hx
    set p : Fin d → ℝ := fun k => cubeSlope N w x k with hp
    have hp2 : ∀ k, p k ^ 2 ≤ F x k := fun k => sq_cubeSlope_le N w x k
    have hpabs : ∀ k, |p k| ≤ √(F x k) := fun k => Real.abs_le_sqrt (hp2 k)
    have hap2 : ∀ k, (a k * p k) ^ 2 ≤ Λ ^ 2 * F x k := fun k => by
      have h1 : a k ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (ha k).le (haΛ k) 2
      calc (a k * p k) ^ 2 = a k ^ 2 * p k ^ 2 := by ring
        _ ≤ Λ ^ 2 * F x k := mul_le_mul h1 (hp2 k) (sq_nonneg _) (sq_nonneg _)
    have hQ : ∑ k, (a k * p k) ^ 2 / a k = ∑ k, a k * p k ^ 2 :=
      Finset.sum_congr rfl fun k _ => by
        have := (ha k).ne'
        field_simp
    have hQ0 : 0 ≤ ∑ k, a k * p k ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (ha k).le (sq_nonneg _)
    have hQle : ∑ k, a k * p k ^ 2 ≤ Λ * ∑ k, F x k := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => mul_le_mul (haΛ k) (hp2 k) (sq_nonneg _) hΛ0
    -- the errors on the subcubes
    have t1 : (∑ i ∈ (cornerCube 0 M).vertices, (K : ℝ) ^ d *
          |(∑ k, (a k * p k) ^ 2 / a k) / 2 + μT x i|) / (N : ℝ) ^ d ≤
        ε * Λ ^ 2 * ∑ k, F x k := by
      have h1 : ∑ i ∈ (cornerCube 0 M).vertices, (K : ℝ) ^ d *
          |(∑ k, (a k * p k) ^ 2 / a k) / 2 + μT x i| ≤
          ∑ _i ∈ (cornerCube (0 : Vertex d) M).vertices, (K : ℝ) ^ d *
            (ε * ∑ k, (a k * p k) ^ 2) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hε x hx i hi) hVK.le
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hcardM] at h1
      have h2 : ε * ∑ k, (a k * p k) ^ 2 ≤ ε * (Λ ^ 2 * ∑ k, F x k) := by
        refine mul_le_mul_of_nonneg_left ?_ hε0
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => hap2 k
      have h3 : 0 ≤ ε * ∑ k, (a k * p k) ^ 2 :=
        mul_nonneg hε0 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      rw [div_le_iff₀ hVN]
      calc _ ≤ ((M * K : ℕ) : ℝ) ^ d * (ε * ∑ k, (a k * p k) ^ 2) := h1
        _ ≤ (N : ℝ) ^ d * (ε * ∑ k, (a k * p k) ^ 2) := mul_le_mul_of_nonneg_right hMKN h3
        _ ≤ (N : ℝ) ^ d * (ε * (Λ ^ 2 * ∑ k, F x k)) := mul_le_mul_of_nonneg_left h2 hVN.le
        _ = ε * Λ ^ 2 * (∑ k, F x k) * (N : ℝ) ^ d := by ring
    -- the part outside the block
    have t2 : |1 - ((cornerCube (0 : Vertex d) M).vertices.card : ℝ) * (K : ℝ) ^ d /
          (N : ℝ) ^ d| * |(∑ k, (a k * p k) ^ 2 / a k) / 2| ≤ Λ * β / 2 * ∑ k, F x k := by
      rw [hcardM, ← hβ, abs_of_nonneg hβ0, hQ, abs_of_nonneg (div_nonneg hQ0 (by norm_num))]
      calc β * ((∑ k, a k * p k ^ 2) / 2) ≤ β * ((Λ * ∑ k, F x k) / 2) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hQle (by norm_num)) hβ0
        _ = Λ * β / 2 * ∑ k, F x k := by ring
    -- the defect of the edge slopes
    have t3 : |∑ k, a k * p k * (cubeEdgeSlope N w x k -
          (∑ i ∈ (cornerCube 0 M).vertices,
            (K : ℝ) ^ d * cubeEdgeSlope K w (z x + (K : ℤ) • i) k) / (N : ℝ) ^ d)| ≤
        Λ * γ * ∑ k, F x k := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have hD := abs_cubeEdgeSlope_sub_sum_tiles_le hK hMK w (hz x hx) k
      rw [abs_mul, abs_mul, abs_of_pos (ha k)]
      have hsF : √(F x k) * √(F x k) = F x k := Real.mul_self_sqrt (hF0 x k)
      calc a k * |p k| * |cubeEdgeSlope N w x k -
            (∑ i ∈ (cornerCube 0 M).vertices,
              (K : ℝ) ^ d * cubeEdgeSlope K w (z x + (K : ℤ) • i) k) / (N : ℝ) ^ d|
          ≤ Λ * √(F x k) * (γ * √(F x k)) :=
            mul_le_mul (mul_le_mul (haΛ k) (hpabs k) (abs_nonneg _) hΛ0) hD (abs_nonneg _)
              (by positivity)
        _ = Λ * γ * (√(F x k) * √(F x k)) := by ring
        _ = Λ * γ * F x k := by rw [hsF]
    have e : c * ∑ k, F x k = ε * Λ ^ 2 * ∑ k, F x k + Λ * β / 2 * ∑ k, F x k +
        Λ * γ * ∑ k, F x k := by
      rw [hc]; ring
    rw [e]
    exact add_le_add (add_le_add t1 t2) t3
  -- summing over the translates
  set Fd : Vertex d → ℝ := fun y =>
    ∑ k : Fin d, (if y + unit k ∈ D then (w (y + unit k) - w y) ^ 2 else 0) with hFd
  have hFd0 : ∀ y, 0 ≤ Fd y := fun y => Finset.sum_nonneg fun _ _ => by
    split_ifs <;> positivity
  have hFx : ∀ x ∈ A, ∑ k, F x k = (∑ y ∈ (cornerCube x N).vertices, Fd y) / (N : ℝ) ^ d := by
    intro x hx
    rw [hF, hFd]
    show ∑ k, (∑ y ∈ (cornerCube x N).vertices, (w (y + unit k) - w y) ^ 2) / (N : ℝ) ^ d =
      (∑ y ∈ (cornerCube x N).vertices,
        ∑ k : Fin d, (if y + unit k ∈ D then (w (y + unit k) - w y) ^ 2 else 0)) / (N : ℝ) ^ d
    rw [← Finset.sum_div, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos ((hAD x hx y hy).2 k)]
  have htr := sum_translates_le A D N Fd hFd0 fun x hx o ho =>
    (hAD x hx (x + o) (add_mem_cornerCube_of_mem_zero x ho)).1
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact add_nonneg (add_nonneg (mul_nonneg hε0 (sq_nonneg _))
      (div_nonneg (mul_nonneg hΛ0 hβ0) (by norm_num))) (mul_nonneg hΛ0 hγ0)
  calc _ ≤ ∑ x ∈ A, c * ∑ k, F x k := Finset.sum_le_sum hone
    _ = c * ((∑ x ∈ A, ∑ y ∈ (cornerCube x N).vertices, Fd y) / (N : ℝ) ^ d) := by
        rw [← Finset.mul_sum, Finset.sum_div]
        congr 1
        exact Finset.sum_congr rfl fun x hx => hFx x hx
    _ ≤ c * ((N : ℝ) ^ d * (∑ y ∈ D, Fd y) / (N : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htr hVN.le) hc0
    _ = c * ∑ y ∈ D, Fd y := by rw [mul_div_cancel_left₀ _ hVN.ne']

end Rigidity.Dirichlet

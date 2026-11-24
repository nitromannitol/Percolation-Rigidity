import Rigidity.Steps.S2.GreenGradientHomogenization
import PercolationClusterHomogenization.Proofs.Density.AffineMajorization

/-!
# Proposition 2.6, step:2.6-expansion: affine majorization

`AffineMajorizationStep` (paper L617-620, proof step `step:2.6-expansion`): under the density
estimate (H4) at the scale `X`, for
`r ≥ X ∨ R₀`, the `L̲²(𝒞 ∩ B_r(x))` norm of an affine function `b + η · (· - x)` majorizes
`c₁ r |η|₁`.

Proof. Replacing `(b, η)` by `(-b, -η)` we may assume `b ≥ 0`. Let `p = x + (r / 2|η|) η` and
let `z` be the lattice point obtained by rounding `p`, so that `|z - p| ≤ d + 1`. For `r ≥ R₀`,
the ball `B_{r/100}(z)` lies in `B_r(x)`, the affine function is at least `|η| r / 4` on it, and by
(H4) it carries at least `c r^d` vertices of the cluster; the ball `B_r(x)` carries at most
`5^d r^d` lattice points (`card_componentEuclideanBall_le`), and `|η|₁² ≤ (d + 1) |η|²`.

The file also records the elementary properties of the normalized `L̲²` norm `componentBallL2`
used in the slope estimate: the triangle inequality (`componentBallL2_add_le`) and the bound by
the supremum (`componentBallL2_le_of_abs_le`).
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2

variable {d : ℕ} {ω : Configuration d}

/-! ### The normalized `L̲²` norm on a component ball -/

/-! ### Affine majorization -/

/-- The Euclidean inner product with a coordinate vector. -/
theorem inner_toLp_eq_sum (η : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (WithLp.toLp 2 η) u = ∑ i, η i * u i := by
  simp [PiLp.inner_apply, mul_comm]

/-- `|η|₁² ≤ (d + 1) |η|²`. -/
theorem sq_sum_abs_le (η : Fin d → ℝ) :
    (∑ i, |η i|) ^ 2 ≤ ((d : ℝ) + 1) * ‖(WithLp.toLp 2 η : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |η i|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
  have hn : ‖(WithLp.toLp 2 η : EuclideanSpace ℝ (Fin d))‖ ^ 2 = ∑ i, η i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_sum]
    simp [sq]
  rw [hn]
  have : 0 ≤ ∑ i, η i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

/-- Rounding a vector of `ℝ^d` to the lattice moves it by at most `d + 1`. -/
theorem norm_embedding_round_sub_le (p : EuclideanSpace ℝ (Fin d)) :
    ‖latticeEuclideanEmbedding (fun i => round (p i)) - p‖ ≤ (d : ℝ) + 1 := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ d + 1)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(latticeEuclideanEmbedding (fun i => round (p i)) - p) i‖ ^ 2
      ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [PiLp.sub_apply]
        change ‖((round (p i) : ℤ) : ℝ) - p i‖ ^ 2 ≤ 1
        have h := abs_sub_round (p i)
        rw [Real.norm_eq_abs, abs_sub_comm]
        nlinarith [abs_nonneg (p i - round (p i))]
    _ = d := by simp
    _ ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith

/-- The affine majorization for a nonnegative constant term `b`, with the explicit constants
`c₁ = (c / (16 · 5^d (d + 1)))^{1/2}` and `R₀ = 8 (d + 1)`. -/
theorem affineMajorization_of_nonneg {c X r : ℝ} (hc : 0 < c) {C : OpenComponent ω}
    {x : Vertex d} (hD : DenseAt C x c X) (hXr : X ≤ r) (hr : 8 * ((d : ℝ) + 1) ≤ r) {b : ℝ}
    (hb : 0 ≤ b) (η : Fin d → ℝ) :
    Real.sqrt (c / (16 * 5 ^ d * ((d : ℝ) + 1))) * r * ∑ i, |η i| ≤
      componentBallL2 C x r (fun z => b + ∑ i, η i * ((z.val i : ℝ) - (x i : ℝ))) := by
  set v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 η with hv
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 < r := by linarith
  have hcs := sq_sum_abs_le η
  rw [← hv] at hcs
  have hS0 : 0 ≤ ∑ i, |η i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  by_cases hv0 : ‖v‖ = 0
  · have : ∑ i, |η i| = 0 := by
      rw [hv0] at hcs
      nlinarith [sq_nonneg (∑ i, |η i|)]
    rw [this, mul_zero]
    exact componentBallL2_nonneg _ _ _ _
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
  set p : EuclideanSpace ℝ (Fin d) := latticeEuclideanEmbedding x + (r / (2 * ‖v‖)) • v with hp
  set z : Vertex d := fun i => round (p i) with hz
  have hzp : ‖latticeEuclideanEmbedding z - p‖ ≤ (d : ℝ) + 1 := norm_embedding_round_sub_le p
  have hpx : ‖p - latticeEuclideanEmbedding x‖ = r / 2 := by
    rw [hp, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hzx : dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding x) ≤
      r / 2 + ((d : ℝ) + 1) := by
    rw [dist_eq_norm]
    calc ‖latticeEuclideanEmbedding z - latticeEuclideanEmbedding x‖
        = ‖(latticeEuclideanEmbedding z - p) + (p - latticeEuclideanEmbedding x)‖ := by
          congr 1; abel
      _ ≤ ‖latticeEuclideanEmbedding z - p‖ + ‖p - latticeEuclideanEmbedding x‖ :=
          norm_add_le _ _
      _ ≤ _ := by rw [hpx]; linarith
  set S := componentEuclideanBall C z (r / 100) with hSdef
  have hSsub : S ⊆ componentEuclideanBall C x r := by
    intro w hw
    rw [hSdef, mem_componentEuclideanBall] at hw
    rw [mem_componentEuclideanBall]
    calc dist (latticeEuclideanEmbedding w.val) (latticeEuclideanEmbedding x)
        ≤ dist (latticeEuclideanEmbedding w.val) (latticeEuclideanEmbedding z) +
          dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding x) := dist_triangle _ _ _
      _ < r := by linarith
  have hcardS : c * r ^ d ≤ (S.card : ℝ) := hD r hXr z (by linarith)
  have hlow : ∀ w ∈ S, ‖v‖ * r / 4 ≤ b + ∑ i, η i * ((w.val i : ℝ) - (x i : ℝ)) := by
    intro w hw
    rw [hSdef, mem_componentEuclideanBall, dist_eq_norm] at hw
    have hsum : ∑ i, η i * ((w.val i : ℝ) - (x i : ℝ)) =
        inner ℝ v (latticeEuclideanEmbedding w.val - latticeEuclideanEmbedding x) := by
      rw [hv, inner_toLp_eq_sum]; rfl
    have hsplit : latticeEuclideanEmbedding w.val - latticeEuclideanEmbedding x =
        (r / (2 * ‖v‖)) • v + (latticeEuclideanEmbedding z - p) +
          (latticeEuclideanEmbedding w.val - latticeEuclideanEmbedding z) := by
      rw [hp]; abel
    rw [hsum, hsplit, inner_add_right, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    have h1 := neg_abs_le (inner ℝ v (latticeEuclideanEmbedding z - p))
    have h2 := abs_real_inner_le_norm v (latticeEuclideanEmbedding z - p)
    have h3 := neg_abs_le (inner ℝ v (latticeEuclideanEmbedding w.val - latticeEuclideanEmbedding z))
    have h4 := abs_real_inner_le_norm v
      (latticeEuclideanEmbedding w.val - latticeEuclideanEmbedding z)
    have e : r / (2 * ‖v‖) * ‖v‖ ^ 2 = ‖v‖ * r / 2 := by field_simp
    rw [e]
    have h5 : ‖v‖ * ‖latticeEuclideanEmbedding z - p‖ ≤ ‖v‖ * ((d : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hzp hvpos.le
    have h6 : ‖v‖ * ‖latticeEuclideanEmbedding w.val - latticeEuclideanEmbedding z‖ ≤
        ‖v‖ * (r / 100) := mul_le_mul_of_nonneg_left hw.le hvpos.le
    have h7 : ‖v‖ * ((d : ℝ) + 1) ≤ ‖v‖ * (r / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hvpos.le
    nlinarith
  have hsumS : (S.card : ℝ) * (‖v‖ * r / 4) ^ 2 ≤ ∑ w ∈ componentEuclideanBall C x r,
      (b + ∑ i, η i * ((w.val i : ℝ) - (x i : ℝ))) ^ 2 := by
    calc (S.card : ℝ) * (‖v‖ * r / 4) ^ 2 = ∑ _w ∈ S, (‖v‖ * r / 4) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ S, (b + ∑ i, η i * ((w.val i : ℝ) - (x i : ℝ))) ^ 2 :=
          Finset.sum_le_sum fun w hw => pow_le_pow_left₀ (by positivity) (hlow w hw) 2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSsub fun _ _ _ => sq_nonneg _
  have hN := card_componentEuclideanBall_le C x (r := r) (by linarith)
  have hNpos : 0 < ((componentEuclideanBall C x r).card : ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < c * r ^ d)
      (hcardS.trans (by exact_mod_cast Finset.card_le_card hSsub))
  unfold componentBallL2
  rw [Real.le_sqrt (by positivity) (by positivity), le_div_iff₀ hNpos]
  have hc1 : Real.sqrt (c / (16 * 5 ^ d * ((d : ℝ) + 1))) ^ 2 =
      c / (16 * 5 ^ d * ((d : ℝ) + 1)) := Real.sq_sqrt (by positivity)
  calc (Real.sqrt (c / (16 * 5 ^ d * ((d : ℝ) + 1))) * r * ∑ i, |η i|) ^ 2 *
        ((componentEuclideanBall C x r).card : ℝ)
      = c / (16 * 5 ^ d * ((d : ℝ) + 1)) * r ^ 2 * (∑ i, |η i|) ^ 2 *
          ((componentEuclideanBall C x r).card : ℝ) := by rw [mul_pow, mul_pow, hc1]
    _ ≤ c / (16 * 5 ^ d * ((d : ℝ) + 1)) * r ^ 2 * (((d : ℝ) + 1) * ‖v‖ ^ 2) *
          (5 ^ d * r ^ d) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcs (by positivity)) hN (by positivity)
          (by positivity)
    _ = c * r ^ d * (‖v‖ * r / 4) ^ 2 := by field_simp; ring
    _ ≤ (S.card : ℝ) * (‖v‖ * r / 4) ^ 2 := by gcongr
    _ ≤ _ := hsumS

/-- step:2.6-expansion, affine majorization: `AffineMajorizationStep`. -/
theorem affineMajorizationStep : AffineMajorizationStep d := by
  intro c hc
  refine ⟨Real.sqrt (c / (16 * 5 ^ d * ((d : ℝ) + 1))), 8 * ((d : ℝ) + 1),
    Real.sqrt_pos.mpr (by positivity), by positivity, ?_⟩
  intro ω C x X r hD hXr hr b η
  rcases le_or_gt 0 b with hb | hb
  · exact affineMajorization_of_nonneg hc hD hXr hr hb η
  · have h := affineMajorization_of_nonneg hc hD hXr hr (b := -b) (by linarith)
      (fun i => -η i)
    simp only [abs_neg] at h
    refine h.trans (le_of_eq ?_)
    rw [← componentBallL2_neg C x r]
    congr 1
    funext z
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

end Rigidity.Proofs.S2

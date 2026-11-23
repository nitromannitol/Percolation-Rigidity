import Rigidity.Proofs.Green.PlanarHeatKernelInputs
import Rigidity.Proofs.Regularity.LatticeHarmonic

/-!
# The energy identity of Step 2 of the proof of Proposition 4.3 of Dario–Gu

Step 2 of the proof of Proposition 4.3 of Dario–Gu (lines 2276-2331 of the source) tests the
equation of `w` against `ψ² w` and integrates by parts on the cluster. This file proves:

* `tsum_openLaplacian_mul`: the discrete integration by parts (1.35)-(1.37) on `ℤ²` for square
  summable functions, `Σ_x (Δ u)(x) φ(x) = -Σ_x Σ_i a_i(x) D_i u(x) D_i φ(x)`, where
  `a_i(x) = 1` if the edge `{x, x + e_i}` is open and `0` otherwise (`openCond`);
* `edge_energy_ge`: on one edge, `(q² b - p² a)(b - a) ≥ (q b - p a)² - (q - p)² (a² + b²)/2`, the
  discrete product rule which replaces (4.27) in the lower bound of the left side of (4.28):
  `Σ ∇(ψ² w) · ∇w ≥ Σ |∇(ψ w)|² - Σ_x w(x)² Σ_{z ∼ x} (ψ(z) - ψ(x))²`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The conductance `a_i(x)` of the edge `{x, x + e_i}`: `1` if it is open, `0` otherwise. -/
noncomputable def openCond (ω : Configuration 2) (i : Fin 2) (x : Vertex 2) : ℝ :=
  if (openGraph ω).Adj x (x + unit i) then 1 else 0

theorem abs_openCond_le (ω : Configuration 2) (i : Fin 2) (x : Vertex 2) :
    |openCond ω i x| ≤ 1 := by
  unfold openCond
  split_ifs <;> norm_num

/-- The Laplacian of the open graph, direction by direction. -/
theorem openLaplacian_eq_sum (ω : Configuration 2) (u : Vertex 2 → ℝ) (x : Vertex 2) :
    openLaplacian ω u x = ∑ i : Fin 2, (openCond ω i x * (u (x + unit i) - u x) +
      openCond ω i (x - unit i) * (u (x - unit i) - u x)) := by
  rw [openLaplacian, sum_neighborFinset_openGraph ω x (fun z => u z - u x),
    Rigidity.Proofs.Regularity.sum_nbrFinset]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc2 : openCond ω i (x - unit i) = if (openGraph ω).Adj x (x - unit i) then 1 else 0 := by
    unfold openCond
    rw [sub_add_cancel]
    by_cases h : (openGraph ω).Adj x (x - unit i)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  rw [hc2]
  unfold openCond
  split_ifs <;> ring

/-- The product of two square summable functions is summable. -/
theorem summable_mul_of_sq {f g : Vertex 2 → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) : Summable fun x => f x * g x := by
  refine Summable.of_norm_bounded ((hf.add hg).div_const 2) fun x => ?_
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

theorem summable_sq_sub {f g : Vertex 2 → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) : Summable fun x => (f x - g x) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
    ((hf.add hg).mul_left 2)
  nlinarith [sq_nonneg (f x + g x)]

theorem summable_sq_add_shift {f : Vertex 2 → ℝ} (hf : Summable fun x => f x ^ 2) (a : Vertex 2) :
    Summable fun x => f (x + a) ^ 2 :=
  (Equiv.addRight a).summable_iff.2 hf

theorem summable_sq_sub_shift {f : Vertex 2 → ℝ} (hf : Summable fun x => f x ^ 2) (a : Vertex 2) :
    Summable fun x => f (x - a) ^ 2 :=
  (Equiv.subRight a).summable_iff.2 hf

theorem summable_mul_mul_of_abs_le {c A B : Vertex 2 → ℝ} (hc : ∀ x, |c x| ≤ 1)
    (h : Summable fun x => A x * B x) : Summable fun x => c x * A x * B x := by
  refine Summable.of_norm_bounded h.abs fun x => ?_
  rw [Real.norm_eq_abs, mul_assoc, abs_mul]
  calc |c x| * |A x * B x| ≤ 1 * |A x * B x| := mul_le_mul_of_nonneg_right (hc x) (abs_nonneg _)
    _ = |A x * B x| := one_mul _

/-- **Discrete integration by parts on `ℤ²`** for the Laplacian of the open graph and square
summable functions: `Σ_x (Δ u)(x) φ(x) = -Σ_x Σ_i a_i(x) (u(x + e_i) - u(x)) (φ(x + e_i) - φ(x))`. -/
theorem tsum_openLaplacian_mul (ω : Configuration 2) {u φ : Vertex 2 → ℝ}
    (hu : Summable fun x => u x ^ 2) (hφ : Summable fun x => φ x ^ 2) :
    ∑' x, openLaplacian ω u x * φ x =
      -∑' x, ∑ i : Fin 2, openCond ω i x * (u (x + unit i) - u x) * (φ (x + unit i) - φ x) := by
  have hP : ∀ i : Fin 2, Summable fun x => openCond ω i x * (u (x + unit i) - u x) * φ x :=
    fun i => summable_mul_mul_of_abs_le (abs_openCond_le ω i)
      (summable_mul_of_sq (summable_sq_sub (summable_sq_add_shift hu _) hu) hφ)
  have hM : ∀ i : Fin 2,
      Summable fun x => openCond ω i (x - unit i) * (u (x - unit i) - u x) * φ x :=
    fun i => summable_mul_mul_of_abs_le (fun x => abs_openCond_le ω i _)
      (summable_mul_of_sq (summable_sq_sub (summable_sq_sub_shift hu _) hu) hφ)
  have hP' : ∀ i : Fin 2,
      Summable fun x => openCond ω i x * (u (x + unit i) - u x) * φ (x + unit i) :=
    fun i => summable_mul_mul_of_abs_le (abs_openCond_le ω i)
      (summable_mul_of_sq (summable_sq_sub (summable_sq_add_shift hu _) hu)
        (summable_sq_add_shift hφ _))
  have hshift : ∀ i : Fin 2,
      ∑' x, openCond ω i (x - unit i) * (u (x - unit i) - u x) * φ x =
        ∑' x, -(openCond ω i x * (u (x + unit i) - u x) * φ (x + unit i)) := by
    intro i
    rw [← (Equiv.addRight (unit i)).tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  have hterm : ∀ i : Fin 2,
      ∑' x, openCond ω i x * (u (x + unit i) - u x) * φ x +
        ∑' x, openCond ω i (x - unit i) * (u (x - unit i) - u x) * φ x =
      -∑' x, openCond ω i x * (u (x + unit i) - u x) * (φ (x + unit i) - φ x) := by
    intro i
    rw [hshift i, ← (hP i).tsum_add (hP' i).neg, ← tsum_neg]
    refine tsum_congr fun x => ?_
    ring
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      Summable fun x => openCond ω i x * (u (x + unit i) - u x) * (φ (x + unit i) - φ x) :=
    fun i _ => summable_mul_mul_of_abs_le (abs_openCond_le ω i)
      (summable_mul_of_sq (summable_sq_sub (summable_sq_add_shift hu _) hu)
        (summable_sq_sub (summable_sq_add_shift hφ _) hφ))
  calc ∑' x, openLaplacian ω u x * φ x
      = ∑' x, ∑ i : Fin 2, (openCond ω i x * (u (x + unit i) - u x) * φ x +
          openCond ω i (x - unit i) * (u (x - unit i) - u x) * φ x) := by
        refine tsum_congr fun x => ?_
        rw [openLaplacian_eq_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ i : Fin 2, (∑' x, openCond ω i x * (u (x + unit i) - u x) * φ x +
          ∑' x, openCond ω i (x - unit i) * (u (x - unit i) - u x) * φ x) := by
        rw [Summable.tsum_finsetSum fun i _ => (hP i).add (hM i)]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (hP i).tsum_add (hM i)
    _ = ∑ i : Fin 2, -∑' x, openCond ω i x * (u (x + unit i) - u x) * (φ (x + unit i) - φ x) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = -∑' x, ∑ i : Fin 2,
          openCond ω i x * (u (x + unit i) - u x) * (φ (x + unit i) - φ x) := by
        rw [Finset.sum_neg_distrib, Summable.tsum_finsetSum hsum]

/-- **The discrete product rule on one edge**:
`(q² b - p² a)(b - a) ≥ (q b - p a)² - (q - p)² (a² + b²)/2`. -/
theorem edge_energy_ge (a b p q : ℝ) :
    (q * b - p * a) ^ 2 - (q - p) ^ 2 * (a ^ 2 + b ^ 2) / 2 ≤ (q ^ 2 * b - p ^ 2 * a) * (b - a) := by
  nlinarith [mul_nonneg (sq_nonneg (q - p)) (sq_nonneg (a - b))]

end Rigidity.Green

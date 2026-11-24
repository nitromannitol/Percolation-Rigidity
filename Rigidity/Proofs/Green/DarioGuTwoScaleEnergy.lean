import Rigidity.Proofs.Green.PlanarHeatKernelInputs
import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonic

/-!
# The energy identity of Step 2 of the proof of Proposition 4.3 of Dario–Gu

Step 2 of the proof of Proposition 4.3 of Dario–Gu (lines 2276-2331 of the source) tests the
equation of `w` against `ψ² w` and integrates by parts on the cluster. This file proves:

* `tsum_openLaplacian_mul`: the discrete integration by parts (1.35) on `ℤ²` for square
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

/-- **The lower bound of the left side of (4.28)** without (4.27): for `w` square summable and
`ψ` bounded, `-Σ_x (Δw)(x) ψ(x)² w(x)` is at least
`Σ_x Σ_i a_i(x) ((ψw)(x + e_i) - (ψw)(x))² - Σ_x Σ_i a_i(x) (ψ(x + e_i) - ψ(x))² (w(x)² + w(x + e_i)²)/2`. -/
theorem tsum_edge_energy_le (ω : Configuration 2) {w ψ : Vertex 2 → ℝ} {B : ℝ}
    (hw : Summable fun x => w x ^ 2) (hψ : ∀ x, |ψ x| ≤ B) :
    ∑' x, ∑ i : Fin 2, openCond ω i x *
        ((ψ (x + unit i) * w (x + unit i) - ψ x * w x) ^ 2 -
          (ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2) ≤
      -∑' x, openLaplacian ω w x * (ψ x ^ 2 * w x) := by
  have hB : ∀ x, ψ x ^ 2 ≤ B ^ 2 := fun x => by
    have := hψ x
    nlinarith [abs_nonneg (ψ x), sq_abs (ψ x)]
  have hψw : Summable fun x => (ψ x * w x) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) (hw.mul_left (B ^ 2))
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hB x) (sq_nonneg _)
  have hφ : Summable fun x => (ψ x ^ 2 * w x) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
      (hw.mul_left (B ^ 2 * B ^ 2))
    rw [mul_pow, ← pow_mul]
    have h4 : ψ x ^ (2 * 2) ≤ B ^ 2 * B ^ 2 := by
      rw [pow_mul]
      have := hB x
      have h0 : 0 ≤ ψ x ^ 2 := sq_nonneg _
      nlinarith
    exact mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  rw [tsum_openLaplacian_mul ω hw hφ, neg_neg]
  have hL : ∀ i : Fin 2, Summable fun x => openCond ω i x *
      ((ψ (x + unit i) * w (x + unit i) - ψ x * w x) ^ 2 -
        (ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2) := by
    intro i
    have h1 : Summable fun x => (ψ (x + unit i) * w (x + unit i) - ψ x * w x) ^ 2 :=
      summable_sq_sub (summable_sq_add_shift hψw (unit i)) hψw
    have h2 : Summable fun x => (ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2 := by
      refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
        ((hw.add (summable_sq_add_shift hw (unit i))).mul_left (2 * B ^ 2))
      have hd : (ψ (x + unit i) - ψ x) ^ 2 ≤ 4 * B ^ 2 := by
        nlinarith [hB x, hB (x + unit i), sq_nonneg (ψ (x + unit i) + ψ x)]
      have hw0 : 0 ≤ w x ^ 2 + w (x + unit i) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hd hw0]
    have h12 := h1.sub h2
    refine Summable.of_norm_bounded h12.abs fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right (abs_openCond_le ω i x) (abs_nonneg _)).trans (one_mul _).le
  have hR : ∀ i : Fin 2, Summable fun x => openCond ω i x * (w (x + unit i) - w x) *
      (ψ (x + unit i) ^ 2 * w (x + unit i) - ψ x ^ 2 * w x) :=
    fun i => summable_mul_mul_of_abs_le (abs_openCond_le ω i)
      (summable_mul_of_sq (summable_sq_sub (summable_sq_add_shift hw _) hw)
        (summable_sq_sub (summable_sq_add_shift hφ _) hφ))
  refine Summable.tsum_le_tsum (fun x => ?_) (summable_sum fun i _ => hL i)
    (summable_sum fun i _ => hR i)
  refine Finset.sum_le_sum fun i _ => ?_
  have hc : 0 ≤ openCond ω i x := by unfold openCond; split_ifs <;> norm_num
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have := edge_energy_ge (w x) (w (x + unit i)) (ψ x) (ψ (x + unit i))
  linarith

/-- The error term of `tsum_edge_energy_le` as a weighted sum of `w²`:
`Σ_x Σ_i a_i(x) (D_iψ)² (w(x)² + w(x + e_i)²)/2 = Σ_x w(x)² κ(x)` with
`κ(x) = Σ_i (a_i(x) (ψ(x + e_i) - ψ(x))² + a_i(x - e_i) (ψ(x) - ψ(x - e_i))²)/2`, the half sum of the
squared differences of `ψ` along the open edges at `x`. -/
theorem tsum_edge_weight_eq (ω : Configuration 2) {w ψ : Vertex 2 → ℝ} {B : ℝ}
    (hw : Summable fun x => w x ^ 2) (hψ : ∀ x, |ψ x| ≤ B) :
    ∑' x, ∑ i : Fin 2, openCond ω i x *
        ((ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2) =
      ∑' x, w x ^ 2 * ∑ i : Fin 2, (openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 +
        openCond ω i (x - unit i) * (ψ x - ψ (x - unit i)) ^ 2) / 2 := by
  have hB : ∀ x z, (ψ z - ψ x) ^ 2 ≤ 4 * B ^ 2 := fun x z => by
    have h1 := hψ x
    have h2 := hψ z
    nlinarith [abs_nonneg (ψ x), sq_abs (ψ x), sq_abs (ψ z), abs_nonneg (ψ z),
      sq_nonneg (ψ z + ψ x)]
  have hcb : ∀ i x z, |openCond ω i x * (ψ z - ψ x) ^ 2| ≤ 4 * B ^ 2 := fun i x z => by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (ψ z - ψ x))]
    calc |openCond ω i x| * (ψ z - ψ x) ^ 2 ≤ 1 * (4 * B ^ 2) :=
          mul_le_mul (abs_openCond_le ω i x) (hB x z) (sq_nonneg _) zero_le_one
      _ = 4 * B ^ 2 := one_mul _
  have hS : ∀ (g : Vertex 2 → ℝ) (c : Vertex 2 → ℝ), (∀ x, |c x| ≤ 4 * B ^ 2) →
      Summable (fun x => g x ^ 2) → Summable fun x => c x * g x ^ 2 := by
    intro g c hc hg
    refine Summable.of_norm_bounded (hg.mul_left (4 * B ^ 2)) fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (g x))]
    exact mul_le_mul_of_nonneg_right (hc x) (sq_nonneg _)
  have hA : ∀ i : Fin 2, Summable fun x => openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w x ^ 2 :=
    fun i => hS w _ (fun x => hcb i x _) hw
  have hA' : ∀ i : Fin 2, Summable fun x =>
      openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w (x + unit i) ^ 2 :=
    fun i => hS (fun x => w (x + unit i)) _ (fun x => hcb i x _) (summable_sq_add_shift hw _)
  have hC : ∀ i : Fin 2, Summable fun x =>
      openCond ω i (x - unit i) * (ψ x - ψ (x - unit i)) ^ 2 * w x ^ 2 :=
    fun i => hS w _ (fun x => hcb i (x - unit i) x) hw
  have hshift : ∀ i : Fin 2,
      ∑' x, openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w (x + unit i) ^ 2 =
        ∑' x, openCond ω i (x - unit i) * (ψ x - ψ (x - unit i)) ^ 2 * w x ^ 2 := by
    intro i
    rw [← (Equiv.addRight (unit i)).tsum_eq
      (fun x => openCond ω i (x - unit i) * (ψ x - ψ (x - unit i)) ^ 2 * w x ^ 2)]
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  calc ∑' x, ∑ i : Fin 2, openCond ω i x *
        ((ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2)
      = ∑' x, ∑ i : Fin 2, ((openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w x ^ 2 +
          openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w (x + unit i) ^ 2) / 2) :=
        tsum_congr fun x => Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i : Fin 2, ((∑' x, openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w x ^ 2 +
          ∑' x, openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w (x + unit i) ^ 2) / 2) := by
        rw [Summable.tsum_finsetSum fun i _ => ((hA i).add (hA' i)).div_const 2]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [tsum_div_const, (hA i).tsum_add (hA' i)]
    _ = ∑ i : Fin 2, ((∑' x, openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w x ^ 2 +
          ∑' x, openCond ω i (x - unit i) * (ψ x - ψ (x - unit i)) ^ 2 * w x ^ 2) / 2) :=
        Finset.sum_congr rfl fun i _ => by rw [hshift i]
    _ = ∑' x, ∑ i : Fin 2, ((openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 * w x ^ 2 +
          openCond ω i (x - unit i) * (ψ x - ψ (x - unit i)) ^ 2 * w x ^ 2) / 2) := by
        rw [Summable.tsum_finsetSum fun i _ => ((hA i).add (hC i)).div_const 2]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [tsum_div_const, (hA i).tsum_add (hC i)]
    _ = ∑' x, w x ^ 2 * ∑ i : Fin 2, (openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 +
          openCond ω i (x - unit i) * (ψ x - ψ (x - unit i)) ^ 2) / 2 := by
        refine tsum_congr fun x => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

end Rigidity.Green

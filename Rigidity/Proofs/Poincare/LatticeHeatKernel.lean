import Rigidity.Proofs.Corrector.PeriodicHeatDecay
import Rigidity.Proofs.Green.OpenHeatSemigroup
import LatticeProb.Walk.ContinuousHeatGauss
import LatticeProb.Walk.LineKernelLocalLimit

/-!
# The heat kernel of `ℤ²` as a product of one-dimensional kernels

The heat kernel `Φ_t(x, y) = openHeat (allOpen 2) t x y` of `ℤ²` (Dario, Definition 2.18; the
variable speed random walk with every bond open, generator `Δ u(x) = Σ_{z ∼ x} (u(z) - u(x))`) is
the Poisson average, with parameter `4t`, of the simple random walk kernel. By the
Poissonisation of Lattice-Probability (`LatticeProb.ContinuousTime.hasSum_ctHeat`) it is the
continuous-time kernel at time `4t`, the product of the one-dimensional kernels
`q_s(k) = (2π)⁻¹ ∫_{-π}^{π} e^{-s(1 - cos θ)} cos(kθ) dθ` at time `s = 2t`:

* `openHeat_allOpen_eq_lineKernel`: `Φ_t(x, y) = q_{2t}(y₀ - x₀) q_{2t}(y₁ - x₁)`;
* `openHeat_allOpen_add`: translation invariance `Φ_t(x + a, y + a) = Φ_t(x, y)`;
* `lineKernel_nonneg`, `lineKernel_le_exp_abs` (the Chernoff bound
  `q_s(k) ≤ e^{-b|k| + s(cosh b - 1)}`, from `abs_lineKernel_le_exp`);
* `openHeat_allOpen_le_exp_mul`: `Φ_s ≤ e^{8T} Φ_{2T}` for `0 ≤ s ≤ T`, term by term in the
  Poisson series.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green LatticeProb.ContinuousTime

namespace Rigidity.Poincare

/-- The neighbours of `x` in `ℤ²`, direction by direction (real-valued sums). -/
theorem sum_neighborFinset_allOpen_real (x : Vertex 2) (u : Vertex 2 → ℝ) :
    ∑ z ∈ (openGraph (allOpen 2)).neighborFinset x, u z =
      ∑ i : Fin 2, (u (x + unit i) + u (x - unit i)) := by
  have h := Rigidity.Corrector.sum_neighborFinset_allOpen x (fun z => (u z : ℂ))
  exact_mod_cast h

/-- The powers of the lazy kernel of `ℤ²` (degree four, so not lazy) are the simple random walk
kernels of Lattice-Probability. -/
theorem lazyPow_allOpen_eq_srwHeat (n : ℕ) (x y : Vertex 2) :
    lazyPow (openGraph (allOpen 2)) 4 n x y = srwHeat 2 n (y - x) := by
  induction n generalizing x with
  | zero =>
      rw [lazyPow_zero, srwHeat_zero]
      by_cases h : x = y
      · subst h
        simp
      · rw [if_neg h, if_neg (sub_ne_zero.2 (Ne.symm h))]
  | succ n ih =>
      rw [lazyPow_succ, Rigidity.Corrector.degree_allOpen, sum_neighborFinset_allOpen_real,
        srwHeat_succ, walkOp, nbrSum]
      simp only [ih]
      have e : ∀ i : Fin 2, srwHeat 2 n (y - (x + unit i)) + srwHeat 2 n (y - (x - unit i)) =
          srwHeat 2 n (y - x + unit i) + srwHeat 2 n (y - x - unit i) := by
        intro i
        rw [add_comm (srwHeat 2 n (y - x + unit i))]
        congr 2 <;> abel
      simp only [e]
      push_cast
      ring

/-- **Poissonisation**: `Φ_t(x, y)` is the continuous-time simple random walk kernel of
Lattice-Probability at time `4t`. -/
theorem openHeat_allOpen_eq_ctHeat (t : ℝ) (x y : Vertex 2) :
    openHeat (allOpen 2) t x y = ctHeat 2 (4 * t) (y - x) := by
  have h := hasSum_ctHeat (d := 2) (by norm_num) (4 * t) (y - x)
  have e : (fun n : ℕ => poissonWeight 4 t n * lazyPow (openGraph (allOpen 2)) 4 n x y) =
      fun n : ℕ => Real.exp (-(4 * t)) * (4 * t) ^ n / n.factorial * srwHeat 2 n (y - x) := by
    funext n
    rw [lazyPow_allOpen_eq_srwHeat, poissonWeight]
    push_cast
    ring_nf
  rw [openHeat, vsrwHeat, e]
  exact h.tsum_eq

/-- **The product form**: `Φ_t(x, y) = q_{2t}(y₀ - x₀) q_{2t}(y₁ - x₁)`. -/
theorem openHeat_allOpen_eq_lineKernel (t : ℝ) (x y : Vertex 2) :
    openHeat (allOpen 2) t x y =
      lineKernel (2 * t) ((y - x) 0) * lineKernel (2 * t) ((y - x) 1) := by
  rw [openHeat_allOpen_eq_ctHeat, ctHeat, Fin.prod_univ_two]
  have : 4 * t / ((2 : ℕ) : ℝ) = 2 * t := by push_cast; ring
  rw [this]

/-- **Translation invariance** of the heat kernel of `ℤ²`. -/
theorem openHeat_allOpen_add (t : ℝ) (x y a : Vertex 2) :
    openHeat (allOpen 2) t (x + a) (y + a) = openHeat (allOpen 2) t x y := by
  rw [openHeat_allOpen_eq_ctHeat, openHeat_allOpen_eq_ctHeat, add_sub_add_right_eq_sub]

theorem openHeat_allOpen_sub (t : ℝ) (x y a : Vertex 2) :
    openHeat (allOpen 2) t (x - a) (y - a) = openHeat (allOpen 2) t x y := by
  rw [openHeat_allOpen_eq_ctHeat, openHeat_allOpen_eq_ctHeat, sub_sub_sub_cancel_right]

/-- The one-dimensional kernel is even. -/
theorem lineKernel_neg (s : ℝ) (k : ℤ) : lineKernel s (-k) = lineKernel s k := by
  unfold lineKernel
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Int.cast_neg, neg_mul, Real.cos_neg]

/-- The one-dimensional kernel is nonnegative at nonnegative times: it is the Poisson average of
the simple random walk kernels on `ℤ`. -/
theorem lineKernel_nonneg {s : ℝ} (hs : 0 ≤ s) (k : ℤ) : 0 ≤ lineKernel s k := by
  have h := hasSum_ctHeat (d := 1) le_rfl s (fun _ => k)
  have hc : ctHeat 1 s (fun _ => k) = lineKernel s k := by
    rw [ctHeat, Fin.prod_univ_one]
    norm_num
  rw [← hc]
  refine h.nonneg fun n => mul_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le
    (pow_nonneg hs n)) (Nat.cast_nonneg _)) (srwHeat_nonneg n _)

/-- **The Chernoff bound** `q_s(k) ≤ e^{-b|k| + s(cosh b - 1)}`. -/
theorem lineKernel_le_exp_abs {s : ℝ} (hs : 0 ≤ s) (k : ℤ) (b : ℝ) :
    lineKernel s k ≤ Real.exp (-(b * |(k : ℝ)|) + s * (Real.cosh b - 1)) := by
  rcases le_total 0 (k : ℝ) with hk | hk
  · have h := abs_lineKernel_le_exp hs k b
    rw [abs_of_nonneg hk]
    exact (le_abs_self _).trans h
  · have h := abs_lineKernel_le_exp hs k (-b)
    rw [Real.cosh_neg] at h
    rw [abs_of_nonpos hk]
    have e : -(-b * (k : ℝ)) = -(b * -(k : ℝ)) := by ring
    rw [e] at h
    exact (le_abs_self _).trans h

/-- The Poisson weights at time `s ≤ T` are at most `e^{8T}` times those at time `2T`. -/
theorem poissonWeight_le_exp_mul {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (n : ℕ) :
    poissonWeight 4 s n ≤ Real.exp (8 * T) * poissonWeight 4 (2 * T) n := by
  unfold poissonWeight
  push_cast
  have hT : 0 ≤ T := hs.trans hsT
  have h1 : Real.exp (-4 * s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : (4 * s) ^ n ≤ (4 * (2 * T)) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
  have h3 : Real.exp (8 * T) * Real.exp (-4 * (2 * T)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [mul_div_assoc', ← mul_assoc, h3, one_mul]
  refine div_le_div_of_nonneg_right ?_ hf.le
  calc Real.exp (-4 * s) * (4 * s) ^ n ≤ 1 * (4 * (2 * T)) ^ n :=
        mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = (4 * (2 * T)) ^ n := one_mul _

/-- **Domination in time**: `Φ_s ≤ e^{8T} Φ_{2T}` for `0 ≤ s ≤ T`. -/
theorem openHeat_allOpen_le_exp_mul {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (x y : Vertex 2) :
    openHeat (allOpen 2) s x y ≤ Real.exp (8 * T) * openHeat (allOpen 2) (2 * T) x y := by
  have hdeg := openGraph_degree_le_four (allOpen 2)
  rw [openHeat, openHeat, vsrwHeat, vsrwHeat, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_vsrwHeat (by norm_num) hdeg s x y)
    ((summable_vsrwHeat (by norm_num) hdeg (2 * T) x y).mul_left _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (poissonWeight_le_exp_mul hs hsT n)
    (lazyPow_mem_Icc (by norm_num) hdeg n x y).1

end Rigidity.Poincare

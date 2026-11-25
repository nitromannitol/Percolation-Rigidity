import Rigidity.Proofs.Poincare.LatticeHeatKernel

/-!
# The heat kernel of `ℤ^d` as a product of one-dimensional kernels

The heat kernel `Φ_t(x, y)` of `ℤ^d` (Dario, Definition 2.18) is the heat kernel of the variable
speed random walk on `ℤ^d` with every bond open, generator `Δ u(x) = Σ_{z ∼ x} (u(z) - u(x))`
(`zdHeat`, the lazy kernel of degree `2d`). This file extends `LatticeHeatKernel.lean` from
`ℤ²` to `ℤ^d`, `d ≥ 1`. By the Poissonisation of Lattice-Probability
(`LatticeProb.ContinuousTime.hasSum_ctHeat`) it is the continuous-time kernel at time `2dt`, the
product of the one-dimensional kernels at time `2t`:

* `zdHeat_eq_ctHeat`: `Φ_t(x, y) = ctHeat d (2dt) (y - x)`;
* `zdHeat_eq_prod_lineKernel`: `Φ_t(x, y) = ∏_i q_{2t}(y_i - x_i)`;
* `zdHeat_add`: translation invariance `Φ_t(x + a, y + a) = Φ_t(x, y)`;
* `zdHeat_nonneg`, `zdHeat_le_one`, `tsum_ofReal_zdHeat` (mass one) and the heat equation
  `hasDerivAt_zdHeat`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green LatticeProb.ContinuousTime Finset

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- The neighbours of `x` in the lattice `ℤ^d` with every bond open. -/
theorem neighborFinset_allOpen (x : Vertex d) :
    (openGraph (allOpen d)).neighborFinset x = nbrFinset x := by
  ext y
  rw [SimpleGraph.mem_neighborFinset, ← Graph.Zd.neighborFinset_eq, SimpleGraph.mem_neighborFinset,
    openGraph_allOpen]

theorem degree_allOpen (x : Vertex d) : (openGraph (allOpen d)).degree x = 2 * d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_allOpen, Graph.Zd.card_nbrFinset]

/-- The neighbours of `x` in `ℤ^d`, direction by direction. -/
theorem sum_neighborFinset_allOpen (x : Vertex d) (u : Vertex d → ℝ) :
    ∑ z ∈ (openGraph (allOpen d)).neighborFinset x, u z =
      ∑ i : Fin d, (u (x + unit i) + u (x - unit i)) := by
  rw [neighborFinset_allOpen, nbrFinset, sum_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [sum_pair]
    intro h
    have := congrFun h i
    simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
    omega
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- The heat kernel of `ℤ^d` (Dario, Definition 2.18): the heat kernel of the variable speed random
walk on `ℤ^d` with every bond open. -/
noncomputable def zdHeat (d : ℕ) (t : ℝ) (x y : Vertex d) : ℝ :=
  vsrwHeat (openGraph (allOpen d)) (2 * d) t x y

theorem two_mul_ne_zero_of_neZero [NeZero d] : ((2 * d : ℕ) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by have := NeZero.ne d; omega)

/-- The powers of the lazy kernel of `ℤ^d` (degree `2d`, so not lazy) are the simple random walk
kernels of Lattice-Probability. -/
theorem lazyPow_allOpen_eq_srwHeat [NeZero d] (n : ℕ) (x y : Vertex d) :
    lazyPow (openGraph (allOpen d)) (2 * d) n x y = srwHeat d n (y - x) := by
  induction n generalizing x with
  | zero =>
      rw [lazyPow_zero, srwHeat_zero]
      by_cases h : x = y
      · subst h
        simp
      · rw [if_neg h, if_neg (sub_ne_zero.2 (Ne.symm h))]
  | succ n ih =>
      rw [lazyPow_succ, degree_allOpen, div_self two_mul_ne_zero_of_neZero, sub_self, zero_mul,
        zero_add, sum_neighborFinset_allOpen, srwHeat_succ, walkOp, nbrSum]
      simp only [ih]
      have e : ∀ i : Fin d, srwHeat d n (y - (x + unit i)) + srwHeat d n (y - (x - unit i)) =
          srwHeat d n (y - x + unit i) + srwHeat d n (y - x - unit i) := by
        intro i
        rw [add_comm (srwHeat d n (y - x + unit i))]
        congr 2 <;> abel
      simp only [e]
      push_cast
      ring

/-- **Poissonisation**: `Φ_t(x, y)` is the continuous-time simple random walk kernel of
Lattice-Probability at time `2dt`. -/
theorem zdHeat_eq_ctHeat [NeZero d] (t : ℝ) (x y : Vertex d) :
    zdHeat d t x y = ctHeat d (2 * d * t) (y - x) := by
  have h := hasSum_ctHeat (d := d) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) (2 * d * t) (y - x)
  have e : (fun n : ℕ => poissonWeight (2 * d) t n *
      lazyPow (openGraph (allOpen d)) (2 * d) n x y) =
      fun n : ℕ => Real.exp (-(2 * d * t)) * (2 * d * t) ^ n / n.factorial * srwHeat d n (y - x) := by
    funext n
    rw [lazyPow_allOpen_eq_srwHeat, poissonWeight]
    push_cast
    ring_nf
  rw [zdHeat, vsrwHeat, e]
  exact h.tsum_eq

/-- **The product form**: `Φ_t(x, y) = ∏_i q_{2t}(y_i - x_i)`. -/
theorem zdHeat_eq_prod_lineKernel [NeZero d] (t : ℝ) (x y : Vertex d) :
    zdHeat d t x y = ∏ i, lineKernel (2 * t) ((y - x) i) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [zdHeat_eq_ctHeat, ctHeat]
  refine prod_congr rfl fun i _ => ?_
  rw [show 2 * (d : ℝ) * t / d = 2 * t by field_simp]

/-- **Translation invariance** of the heat kernel of `ℤ^d`. -/
theorem zdHeat_add [NeZero d] (t : ℝ) (x y a : Vertex d) :
    zdHeat d t (x + a) (y + a) = zdHeat d t x y := by
  rw [zdHeat_eq_ctHeat, zdHeat_eq_ctHeat, add_sub_add_right_eq_sub]

theorem zdHeat_sub [NeZero d] (t : ℝ) (x y a : Vertex d) :
    zdHeat d t (x - a) (y - a) = zdHeat d t x y := by
  rw [zdHeat_eq_ctHeat, zdHeat_eq_ctHeat, sub_sub_sub_cancel_right]

theorem two_mul_pos_of_neZero [NeZero d] : 0 < 2 * d := by
  have := NeZero.ne d
  omega

theorem zdHeat_zero (x y : Vertex d) : zdHeat d 0 x y = if x = y then 1 else 0 := by
  rw [zdHeat, vsrwHeat_zero]
  split_ifs <;> rfl

theorem zdHeat_nonneg [NeZero d] {t : ℝ} (ht : 0 ≤ t) (x y : Vertex d) : 0 ≤ zdHeat d t x y :=
  vsrwHeat_nonneg two_mul_pos_of_neZero (openGraph_degree_le (allOpen d)) ht x y

theorem zdHeat_le_one [NeZero d] {t : ℝ} (ht : 0 ≤ t) (x y : Vertex d) : zdHeat d t x y ≤ 1 :=
  vsrwHeat_le_one two_mul_pos_of_neZero (openGraph_degree_le (allOpen d)) ht x y

/-- The heat kernel of `ℤ^d` has mass one. -/
theorem tsum_ofReal_zdHeat [NeZero d] {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    ∑' y, ENNReal.ofReal (zdHeat d t x y) = 1 :=
  tsum_ofReal_vsrwHeat two_mul_pos_of_neZero (openGraph_degree_le (allOpen d)) ht x

/-- The heat equation for `zdHeat` in the first variable. -/
theorem hasDerivAt_zdHeat [NeZero d] (t : ℝ) (x y : Vertex d) :
    HasDerivAt (fun t => zdHeat d t x y)
      (openLaplacian (allOpen d) (fun z => zdHeat d t z y) x) t :=
  hasDerivAt_vsrwHeat two_mul_pos_of_neZero (openGraph_degree_le (allOpen d)) t x y

end Rigidity.Poincare.GeneralDim

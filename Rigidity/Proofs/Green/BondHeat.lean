import Rigidity.Proofs.Green.OpenHeatSemigroup
import Rigidity.Proofs.Green.PlanarHeatKernelInputs

/-!
# The heat kernel of the variable speed random walk on the open graph of `ℤ^d`

For a bond configuration `ω` on `ℤ^d`, `bondHeat ω t x y` is the heat kernel of the variable speed
random walk with unit conductances on the open graph of `ω` (`vsrwHeat` with degree bound `2d`):
`∂_t p_t(x, y) = Σ_{z ∼ x} (p_t(z, y) - p_t(x, y))`, `p_0 = δ` (Dario–Gu, (1.2)). It is the Poisson
average `p_t(x, y) = Σ_n e^{-2dt} (2dt)^n / n! · Qⁿ(x, y)` of the lazy walk
`Q(x, z) = 1/(2d)` for `z ∼ x`, `Q(x, x) = 1 - deg x/(2d)`.

This file records its properties in every dimension: `p_0 = δ`, `0 ≤ p_t ≤ 1`, the heat equation,
continuity in `t`, joint measurability in the configuration and the time, the symmetry
`p_t(x, y) = p_t(y, x)`, the mass `Σ_y p_t(x, y) = 1`, the semigroup property
`Σ_y p_s(x, y) p_t(y, z) = p_{s+t}(x, z)` and `p_t(x, y) = 0` off the open cluster of `x`. In
dimension two it is the planar kernel `openHeat` (`bondHeat_two`).
-/

open scoped Classical
open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- The heat kernel of the variable speed random walk on the open graph of a configuration of
`ℤ^d`. -/
noncomputable def bondHeat (ω : Configuration d) (t : ℝ) (x y : Vertex d) : ℝ :=
  vsrwHeat (openGraph ω) (2 * d) t x y

/-- In dimension two, `bondHeat` is the planar heat kernel `openHeat`. -/
theorem bondHeat_two (ω : Configuration 2) (t : ℝ) (x y : Vertex 2) :
    bondHeat ω t x y = openHeat ω t x y := rfl

theorem openGraph_degree_le_two_mul (ω : Configuration d) (x : Vertex d) :
    (openGraph ω).degree x ≤ 2 * d :=
  openGraph_degree_le ω x

theorem bondHeat_zero (ω : Configuration d) (x y : Vertex d) :
    bondHeat ω 0 x y = if x = y then 1 else 0 := by
  rw [bondHeat, vsrwHeat_zero]
  split_ifs <;> rfl

variable [NeZero d]

theorem two_mul_dim_pos : 0 < 2 * d := by
  have := NeZero.pos d
  omega

theorem bondHeat_nonneg (ω : Configuration d) {t : ℝ} (ht : 0 ≤ t) (x y : Vertex d) :
    0 ≤ bondHeat ω t x y :=
  vsrwHeat_nonneg two_mul_dim_pos (openGraph_degree_le_two_mul ω) ht x y

theorem bondHeat_le_one (ω : Configuration d) {t : ℝ} (ht : 0 ≤ t) (x y : Vertex d) :
    bondHeat ω t x y ≤ 1 :=
  vsrwHeat_le_one two_mul_dim_pos (openGraph_degree_le_two_mul ω) ht x y

theorem summable_bondHeat (ω : Configuration d) (t : ℝ) (x y : Vertex d) :
    Summable fun n => poissonWeight (2 * d) t n * lazyPow (openGraph ω) (2 * d) n x y :=
  summable_vsrwHeat two_mul_dim_pos (openGraph_degree_le_two_mul ω) t x y

/-- The heat equation for `bondHeat` in the first variable. -/
theorem hasDerivAt_bondHeat (ω : Configuration d) (t : ℝ) (x y : Vertex d) :
    HasDerivAt (fun t => bondHeat ω t x y)
      (openLaplacian ω (fun z => bondHeat ω t z y) x) t :=
  hasDerivAt_vsrwHeat two_mul_dim_pos (openGraph_degree_le_two_mul ω) t x y

theorem continuous_bondHeat (ω : Configuration d) (x y : Vertex d) :
    Continuous fun t => bondHeat ω t x y :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_bondHeat ω t x y).continuousAt

theorem bondHeat_symm (ω : Configuration d) (t : ℝ) (x y : Vertex d) :
    bondHeat ω t x y = bondHeat ω t y x :=
  vsrwHeat_symm two_mul_dim_pos (openGraph_degree_le_two_mul ω) t x y

/-- The mass of the heat kernel is one. -/
theorem hasSum_bondHeat (ω : Configuration d) {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    HasSum (fun y => bondHeat ω t x y) 1 :=
  hasSum_vsrwHeat two_mul_dim_pos (openGraph_degree_le_two_mul ω) ht x

/-- The semigroup property `Σ_y p_s(x, y) p_t(y, z) = p_{s+t}(x, z)`. -/
theorem hasSum_bondHeat_mul (ω : Configuration d) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x z : Vertex d) :
    HasSum (fun y => bondHeat ω s x y * bondHeat ω t y z) (bondHeat ω (s + t) x z) :=
  hasSum_vsrwHeat_mul two_mul_dim_pos (openGraph_degree_le_two_mul ω) hs ht x z

omit [NeZero d] in
theorem bondHeat_eq_zero_of_not_reachable (ω : Configuration d) {x y : Vertex d}
    (h : ¬ (openGraph ω).Reachable x y) (t : ℝ) : bondHeat ω t x y = 0 :=
  vsrwHeat_eq_zero_of_not_reachable h t

omit [NeZero d] in
/-- Sums over open neighbours are sums over lattice neighbours of indicator-weighted terms. -/
theorem sum_neighborFinset_openGraph_eq (ω : Configuration d) (x : Vertex d) (f : Vertex d → ℝ) :
    ∑ z ∈ (openGraph ω).neighborFinset x, f z =
      ∑ z ∈ LatticeProb.nbrFinset x, if (openGraph ω).Adj x z then f z else 0 := by
  rw [openGraph_neighborFinset_eq_filter, Finset.sum_filter]

omit [NeZero d] in
theorem degree_openGraph_eq_sum_ite (ω : Configuration d) (x : Vertex d) :
    ((openGraph ω).degree x : ℝ) =
      ∑ z ∈ LatticeProb.nbrFinset x, if (openGraph ω).Adj x z then (1 : ℝ) else 0 := by
  rw [← sum_neighborFinset_openGraph_eq, Finset.sum_const,
    (openGraph ω).card_neighborFinset_eq_degree, nsmul_one]

omit [NeZero d] in
theorem measurable_lazyPow_bond (n : ℕ) :
    ∀ x y : Vertex d, Measurable fun ω : Configuration d => lazyPow (openGraph ω) (2 * d) n x y := by
  induction n with
  | zero => intro x y; exact measurable_const
  | succ n ih =>
    intro x y
    simp only [lazyPow_succ, degree_openGraph_eq_sum_ite, sum_neighborFinset_openGraph_eq]
    have hadj : ∀ z, MeasurableSet {ω : Configuration d | (openGraph ω).Adj x z} :=
      fun z => measurableSet_openGraph_adj x z
    refine ((measurable_const.sub ((Finset.measurable_sum _ fun z _ =>
      Measurable.ite (hadj z) measurable_const measurable_const).div_const _)).mul (ih x y)).add
      (measurable_const.mul (Finset.measurable_sum _ fun z _ =>
        Measurable.ite (hadj z) (ih z y) measurable_const))

omit [NeZero d] in
theorem measurable_poissonWeight_two_mul (n : ℕ) :
    Measurable fun t : ℝ => poissonWeight (2 * d) t n := by
  unfold poissonWeight
  fun_prop

/-- `bondHeat` is jointly measurable in the configuration and the time. -/
theorem measurable_bondHeat (x y : Vertex d) :
    Measurable fun q : Configuration d × ℝ => bondHeat q.1 q.2 x y := by
  refine measurable_of_tendsto_metrizable (f := fun N (q : Configuration d × ℝ) =>
    ∑ n ∈ Finset.range N, poissonWeight (2 * d) q.2 n * lazyPow (openGraph q.1) (2 * d) n x y) ?_ ?_
  · intro N
    exact Finset.measurable_sum _ fun n _ =>
      ((measurable_poissonWeight_two_mul n).comp measurable_snd).mul
        ((measurable_lazyPow_bond n x y).comp measurable_fst)
  · rw [tendsto_pi_nhds]
    intro q
    exact (summable_bondHeat q.1 q.2 x y).hasSum.tendsto_sum_nat

end Rigidity.Green

import Rigidity.Proofs.Green.LazyHeatKernel
import PercolationClusterHomogenization.External.PlanarInputs
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable
import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent

/-!
# The planar percolation heat kernel and two estimates of Dario–Gu

`openHeat ω t x y` is the heat kernel of the variable speed random walk on the open graph of a
planar bond configuration (`vsrwHeat` with degree bound `4`): it solves
`∂_t p_t(x, y) = Σ_{z ∼ x} (p_t(z, y) - p_t(x, y))`, `p_0 = δ` (Dario–Gu, (1.2)); the walk started
at `y` stays in the open cluster of `y`, so for `x, y ∈ 𝒞_∞` it is the heat kernel of `𝒞_∞` of the
source. It is jointly measurable in the configuration and the time.

Two results of Dario–Gu (arXiv:1909.10439v4) on this kernel are stated as propositions, which
later reductions take as hypotheses; both are proved (`darioGuHeatKernelTwo_holds` in
`Rigidity.Assembly.ProvedFluxWeakNorm`, `carneVaropoulosTwo_holds`).

* `DarioGuHeatKernelTwo`: **Theorem 1** in dimension two (quantitative local limit theorem):
  there is `σ̄ > 0` such that, for every `δ > 0`, there are `C, s` and random times
  `T_par,δ(y)` with `P[T_par,δ(y) ≥ T] ≤ C exp(-T^s / C)` such that, on `{y ∈ 𝒞_∞}`, for every
  `x ∈ 𝒞_∞` and every `t ≥ max(T_par,δ(y), |x - y|)`,
  `|p(t, x, y) - θ(p)^{-1} p̄(t, x - y)| ≤ C t^{-1 - (1/2 - δ)} exp(-|x - y|² / (C t))`,
  with `p̄(t, z) = (2π σ̄ t)^{-1} exp(-|z|²/(2 σ̄ t))`. The hypothesis also requires `t ≥ 1`.
* `CarneVaropoulosTwo`: **Proposition 2.15** (Carne–Varopoulos bound; Davies 1993, Corollaries 11
  and 12) for unit conductances on an infinite component.
-/

open scoped Classical
open MeasureTheory Filter LatticeProb.Percolation

namespace Rigidity.Green

/-- The heat kernel of the variable speed random walk on the open graph of a planar configuration. -/
noncomputable def openHeat (ω : Configuration 2) (t : ℝ) (x y : Vertex 2) : ℝ :=
  vsrwHeat (openGraph ω) 4 t x y

/-- The planar Gaussian kernel `p̄(t, z) = (2πσt)^{-1} exp(-|z|²/(2σt))` (Dario–Gu, (1.5)). -/
noncomputable def gaussianHeat (σ t : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (2 * Real.pi * σ * t)⁻¹ * Real.exp (-(‖z‖ ^ 2 / (2 * σ * t)))

/-- **Dario–Gu, Theorem 1** in dimension two, for the heat kernel `openHeat` of the infinite
cluster, with the additional restriction `t ≥ 1`. -/
def DarioGuHeatKernelTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∀ δ : ℝ, 0 < δ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
      ∃ T : Configuration 2 → ℝ, Measurable T ∧ (∀ ω, 0 ≤ T ω) ∧
        (∀ R : ℝ, 0 ≤ R →
          latticeBondLaw 2 p {ω | R ≤ T ω} ≤ ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          y ∈ (uniqueInfiniteComponent h).supp → ∀ x ∈ (uniqueInfiniteComponent h).supp,
          ∀ t : ℝ, 1 ≤ t → T ω ≤ t →
            ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ≤ t →
            |openHeat ω t x y - (theta 2 p)⁻¹ *
                gaussianHeat σ t (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y)| ≤
              C * t ^ (-1 - (1 / 2 - δ)) *
                Real.exp (-(‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ 2 /
                  (C * t)))

/-- **Dario–Gu, Proposition 2.15** (Carne–Varopoulos bound, Davies 1993, Corollaries 11 and 12)
for unit conductances on an infinite open component of `ℤ²`. -/
def CarneVaropoulosTwo : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration 2) (K : OpenComponent ω), K.supp.Infinite →
    ∀ x ∈ K.supp, ∀ y ∈ K.supp, ∀ t : ℝ, 0 < t →
      (‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ≤ t →
        openHeat ω t x y ≤
          C * Real.exp (-(‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ 2 /
            (C * t)))) ∧
      (t ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ →
        openHeat ω t x y ≤
          C * Real.exp (-(‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ / C *
            (1 + Real.log (‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ / t)))))

/-! ### Properties of `openHeat` -/

theorem openGraph_degree_le_four (ω : Configuration 2) (x : Vertex 2) :
    (openGraph ω).degree x ≤ 4 :=
  openGraph_degree_le ω x

theorem openHeat_zero (ω : Configuration 2) (x y : Vertex 2) :
    openHeat ω 0 x y = if x = y then 1 else 0 := by
  rw [openHeat, vsrwHeat_zero]
  split_ifs <;> rfl

theorem openHeat_nonneg (ω : Configuration 2) {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) :
    0 ≤ openHeat ω t x y :=
  vsrwHeat_nonneg (by norm_num) (openGraph_degree_le_four ω) ht x y

theorem openHeat_le_one (ω : Configuration 2) {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) :
    openHeat ω t x y ≤ 1 :=
  vsrwHeat_le_one (by norm_num) (openGraph_degree_le_four ω) ht x y

/-- The heat equation for `openHeat` in the first variable. -/
theorem hasDerivAt_openHeat (ω : Configuration 2) (t : ℝ) (x y : Vertex 2) :
    HasDerivAt (fun t => openHeat ω t x y)
      (openLaplacian ω (fun z => openHeat ω t z y) x) t :=
  hasDerivAt_vsrwHeat (by norm_num) (openGraph_degree_le_four ω) t x y

theorem continuous_openHeat (ω : Configuration 2) (x y : Vertex 2) :
    Continuous fun t => openHeat ω t x y :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_openHeat ω t x y).continuousAt

/-- Sums over open neighbours are sums over lattice neighbours of indicator-weighted terms. -/
theorem sum_neighborFinset_openGraph (ω : Configuration 2) (x : Vertex 2) (f : Vertex 2 → ℝ) :
    ∑ z ∈ (openGraph ω).neighborFinset x, f z =
      ∑ z ∈ LatticeProb.nbrFinset x, if (openGraph ω).Adj x z then f z else 0 := by
  rw [openGraph_neighborFinset_eq_filter, Finset.sum_filter]

theorem degree_openGraph_eq_sum (ω : Configuration 2) (x : Vertex 2) :
    ((openGraph ω).degree x : ℝ) =
      ∑ z ∈ LatticeProb.nbrFinset x, if (openGraph ω).Adj x z then (1 : ℝ) else 0 := by
  rw [← sum_neighborFinset_openGraph, Finset.sum_const, (openGraph ω).card_neighborFinset_eq_degree,
    nsmul_one]

theorem measurable_lazyPow_openGraph (n : ℕ) :
    ∀ x y : Vertex 2, Measurable fun ω : Configuration 2 => lazyPow (openGraph ω) 4 n x y := by
  induction n with
  | zero => intro x y; exact measurable_const
  | succ n ih =>
    intro x y
    simp only [lazyPow_succ, degree_openGraph_eq_sum, sum_neighborFinset_openGraph]
    have hadj : ∀ z, MeasurableSet {ω : Configuration 2 | (openGraph ω).Adj x z} :=
      fun z => measurableSet_openGraph_adj x z
    refine ((measurable_const.sub ((Finset.measurable_sum _ fun z _ =>
      Measurable.ite (hadj z) measurable_const measurable_const).div_const _)).mul (ih x y)).add
      (measurable_const.mul (Finset.measurable_sum _ fun z _ =>
        Measurable.ite (hadj z) (ih z y) measurable_const))

theorem measurable_poissonWeight (n : ℕ) : Measurable fun t : ℝ => poissonWeight 4 t n := by
  unfold poissonWeight
  fun_prop

/-- `openHeat` is jointly measurable in the configuration and the time. -/
theorem measurable_openHeat (x y : Vertex 2) :
    Measurable fun q : Configuration 2 × ℝ => openHeat q.1 q.2 x y := by
  refine measurable_of_tendsto_metrizable (f := fun N (q : Configuration 2 × ℝ) =>
    ∑ n ∈ Finset.range N, poissonWeight 4 q.2 n * lazyPow (openGraph q.1) 4 n x y) ?_ ?_
  · intro N
    exact Finset.measurable_sum _ fun n _ =>
      ((measurable_poissonWeight n).comp measurable_snd).mul
        ((measurable_lazyPow_openGraph n x y).comp measurable_fst)
  · rw [tendsto_pi_nhds]
    intro q
    exact (summable_vsrwHeat (by norm_num) (openGraph_degree_le_four q.1) q.2 x y).hasSum.tendsto_sum_nat

theorem gaussianHeat_nonneg {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (z : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ gaussianHeat σ t z := by
  unfold gaussianHeat
  have := Real.pi_pos
  positivity

end Rigidity.Green

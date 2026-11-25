import Rigidity.Proofs.Green.DarioGuApproxInputs
import Rigidity.Proofs.Corrector.PlanarShiftedAnchor
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# The parabolic objects of §3.2 of Dario–Gu in dimension two

Dario–Gu prove Theorem 3 (the gradient bound on the heat kernel, `DarioGuGradientBoundTwo`) in
§3.2 from Proposition 3.9 (a large-scale `C^{0,1}` estimate for caloric functions on `𝒞_∞`), and
Proposition 3.9 from Theorem 5 (homogenization of the parabolic Cauchy–Dirichlet problem). This
file fixes the objects of §3.2 and states these two results.

* `IsClusterCaloric ω V a b u`: `∂_t u = Δ u` (unit conductances) at the vertices of `V` all of
  whose open neighbours lie in `V` (the interior `int_a V` of §1.6.3), for times in `(a, b)`, with
  `u(·, x)` continuous on `[a, b]` for `x ∈ V` (a weak solution in `H_par`; the equation is an ODE).
* `coarsenPar ω K u`: the coarsened function `[u]_𝒫` of (2.5)-(2.6) on `ℝ × ℝ²`, piecewise constant
  on the cells `x + [-1/2, 1/2)²`, equal to `u(t, x)` if `x ∈ K` and to `u(t, z(x))` otherwise,
  `z(x)` the anchor of the partition cube of `x` (the point of its crossing cluster closest to the
  centre, as in the source).
* `parabolicCylinderAt y r = (-r², 0] × B_r(y)` in `ℝ × ℝ²`.
* `latticeHull y r = cv(ℤ² ∩ B_r(y))` (3.7); `IsMollifier η`; `mollifiedCoarsening` the boundary
  condition `f̃ = [f]_𝒫 ⋆ η` (3.10) (convolution in space).
* `IsHeatDirichletSolution σ D r g ū`: `ū` solves `∂_t ū = (σ/2) Δ ū` in `(-r², 0) × int D`, is
  continuous on `[-r², 0] × D̄`, equals `g` on the parabolic boundary and has `∇ū ∈ L²`; for the
  boundary conditions used here this is the weak solution in `H_par` of (3.9).
* `parAvgL2 K y r g` and `parGradLp ω K y r q u`: the norms `‖g‖_{L̲²(I_r × (𝒞_∞ ∩ B_r(y)))}` and
  `‖∇u‖_{L̲^q(I_r × (𝒞_∞ ∩ B_r(y)))}` of §1.6.4, the gradient over the open edges inside the ball.

Named statements:

* `DarioGuLipschitzTwo`: Proposition 3.9, for `r ∈ [M, R/2]` (see the docstring).
* `DarioGuThmFiveTwo`: Theorem 5 with `f = u` caloric, the form used in the proof of
  Proposition 3.9, together with the interior gradient bound (3.16) of Lemma 3.7.
* `DarioGuHomogenizedSolutionExists`: existence of the solution `ū` of (3.9), which the source
  takes for granted.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open scoped ENNReal

namespace Rigidity.Green

/-! ### Caloric functions on the cluster -/

/-- `u` solves `∂_t u = Δ u` at the vertices of `V` all of whose open neighbours lie in `V`, for
times in `(a, b)`, and `u(·, x)` is continuous on `[a, b]` for every `x ∈ V`. -/
def IsClusterCaloric (ω : Configuration 2) (V : Finset (Vertex 2)) (a b : ℝ)
    (u : ℝ → Vertex 2 → ℝ) : Prop :=
  (∀ x ∈ V, ContinuousOn (fun s => u s x) (Set.Icc a b)) ∧
    ∀ x ∈ V, (∀ z, (openGraph ω).Adj x z → z ∈ V) → ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun s => u s x) (openLaplacian ω (u s) x) s

/-- Every `u(·, x)` is continuously differentiable on `[a, b]`. -/
def IsTimeCOne (a b : ℝ) (u : ℝ → Vertex 2 → ℝ) : Prop :=
  ∀ x : Vertex 2, ∃ u' : ℝ → ℝ, ContinuousOn u' (Set.Icc a b) ∧
    ∀ s ∈ Set.Icc a b, HasDerivWithinAt (fun s => u s x) (u' s) (Set.Icc a b) s

/-! ### The coarsened function -/

/-- The lattice point `x` with `ξ ∈ x + [-1/2, 1/2)²`. -/
noncomputable def latticeRound (ξ : EuclideanSpace ℝ (Fin 2)) : Vertex 2 :=
  fun i => ⌊ξ i + 1 / 2⌋

open scoped Classical in
/-- The vertex whose value the coarsened function takes at `x`: `x` itself on `K`, the anchor of
the partition cube of `x` otherwise. -/
noncomputable def coarseVertex (ω : Configuration 2) (K : OpenComponent ω) (x : Vertex 2) :
    Vertex 2 :=
  if x ∈ K.supp then x else planarCoarseAnchor ω x

/-- **Dario–Gu, (2.5)-(2.6)**: the coarsened function `[u]_𝒫` on `ℝ × ℝ²`. -/
noncomputable def coarsenPar (ω : Configuration 2) (K : OpenComponent ω)
    (u : ℝ → Vertex 2 → ℝ) : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun z => u z.1 (coarseVertex ω K (latticeRound z.2))

/-- The parabolic cylinder `I_r × B_r(y) = (-r², 0] × B_r(y)` of `ℝ × ℝ²`. -/
def parabolicCylinderAt (y : Vertex 2) (r : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
  Set.Ioc (-r ^ 2) 0 ×ˢ Metric.ball (latticeEuclideanEmbedding y) r

/-! ### The homogenized problem -/

/-- **Dario–Gu, (3.7)**: the convex hull `cv(ℤ² ∩ B_r(y))`. -/
def latticeHull (y : Vertex 2) (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ (latticeEuclideanEmbedding '' {x | latticeDist x y < r})

/-- A smooth nonnegative function supported in `B_{1/2}` with integral `1` (§3.2.1). -/
structure IsMollifier (η : EuclideanSpace ℝ (Fin 2) → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) η
  nonneg : ∀ ξ, 0 ≤ η ξ
  support_subset : Function.support η ⊆ Metric.ball 0 (1 / 2)
  integral_eq : ∫ ξ, η ξ = 1

/-- **Dario–Gu, (3.10)**: the boundary condition `f̃ = [f]_𝒫 ⋆ η`, convolution in space. -/
noncomputable def mollifiedCoarsening (ω : Configuration 2) (K : OpenComponent ω)
    (η : EuclideanSpace ℝ (Fin 2) → ℝ) (u : ℝ → Vertex 2 → ℝ) :
    ℝ × EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun z => ∫ ζ, coarsenPar ω K u (z.1, z.2 - ζ) * η ζ

/-- `ū` solves `∂_t ū = (σ/2) Δ ū` in `(-r², 0) × int D`, is continuous on `[-r², 0] × D̄`, is `C²`
inside, equals `g` on the parabolic boundary `({-r²} × D̄) ∪ ([-r², 0] × ∂D)` and has spatial
gradient in `L²`: the weak solution in `H_par` of (3.9) with boundary condition `g`. -/
def IsHeatDirichletSolution (σ : ℝ) (D : Set (EuclideanSpace ℝ (Fin 2))) (r : ℝ)
    (g ū : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ) : Prop :=
  ContinuousOn ū (Set.Icc (-r ^ 2) 0 ×ˢ closure D) ∧
    ContDiffOn ℝ 2 ū (Set.Ioo (-r ^ 2) 0 ×ˢ interior D) ∧
    (∀ z ∈ Set.Ioo (-r ^ 2) 0 ×ˢ interior D,
      deriv (fun s => ū (s, z.2)) z.1 = σ / 2 * Laplacian.laplacian (fun ξ => ū (z.1, ξ)) z.2) ∧
    (∀ ξ ∈ closure D, ū (-r ^ 2, ξ) = g (-r ^ 2, ξ)) ∧
    (∀ t ∈ Set.Icc (-r ^ 2) 0, ∀ ξ ∈ frontier D, ū (t, ξ) = g (t, ξ)) ∧
    MemLp (fun z => fderiv ℝ (fun ξ => ū (z.1, ξ)) z.2) 2
      (volume.restrict (Set.Ioo (-r ^ 2) 0 ×ˢ interior D))

/-! ### Parabolic norms on the cluster -/

/-- `|∇v|_U(x) = Σ_{z ∈ U, z ∼ x} |v(z) - v(x)|`, over the open edges inside `U`. -/
noncomputable def clusterGradAt (ω : Configuration 2) (U : Finset (Vertex 2))
    (v : Vertex 2 → ℝ) (x : Vertex 2) : ℝ := by
  classical
  exact ∑ z ∈ U.filter (fun z => (openGraph ω).Adj x z), |v z - v x|

/-- `‖g‖_{L̲²(I_r × (𝒞_∞ ∩ B_r(y)))} = (r^{-2} ∫_{-r²}^0 ‖g(t, ·)‖²_{L̲²(𝒞_∞ ∩ B_r(y))} dt)^{1/2}`. -/
noncomputable def parAvgL2 {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2) (r : ℝ)
    (g : ℝ → Vertex 2 → ℝ) : ℝ :=
  Real.sqrt ((r ^ 2)⁻¹ * ∫ t in Set.Ioc (-r ^ 2) 0,
    (∑ x ∈ clusterBall K y r, g t x ^ 2) / (clusterBall K y r).card)

/-- `‖∇u‖_{L̲^q(I_r × (𝒞_∞ ∩ B_r(y)))}`, the gradient over the open edges inside the ball. -/
noncomputable def parGradLp (ω : Configuration 2) (K : OpenComponent ω) (y : Vertex 2) (r q : ℝ)
    (u : ℝ → Vertex 2 → ℝ) : ℝ :=
  ((r ^ 2)⁻¹ * ∫ t in Set.Ioc (-r ^ 2) 0,
    (∑ x ∈ clusterBall K y r, clusterGradAt ω (clusterBall K y r) (u t) x ^ q) /
      (clusterBall K y r).card) ^ (1 / q)

/-! ### The named statements -/

/-- **Dario–Gu, Proposition 3.9** (large-scale `C^{0,1}` estimate for caloric functions on `𝒞_∞`),
in dimension two, for `r ∈ [M, R/2]`.

Printed statement (lines 1690-1709 of the source): *There exist a constant `C < ∞`, an exponent
`s > 0` such that for each point `y ∈ ℤ^d`, there exists a non-negative random variable
`M_{C^{0,1}-reg}(y) ≤ O_s(C)` such that, for every `r ≥ M_{C^{0,1}-reg}(y)`, and every weak
solution `u ∈ H_par(I_R × (𝒞_∞ ∩ B_R(y)))` of `∂_t u - ∇·a∇u = 0`, one has, for every radius
`r ∈ [M_{C^{0,1}-reg}(y), R]`,
`sup_{t ∈ I_r} ‖∇u(t, ·)‖_{L̲²(𝒞_∞ ∩ B_r(y))} ≤ (C/R) ‖[u]_𝒫 - ([u]_𝒫)_{I_R × B_R(y)}‖_{L̲²(I_R × B_R(y))}`.*

For `r` close to `R` the printed inequality fails (a time-independent `u`, harmonic at the interior
vertices of `𝒞_∞ ∩ B_R(y)` with boundary values `±1`, has `‖∇u‖²_{L̲²(𝒞_∞ ∩ B_R)}` of order `R^{-1}`
and right side of order `R^{-1}`); the proof (Step 4, lines 1851-1859: "with the radius `r/2`
instead of `r`; this is a minor difference which can be fixed by standard arguments") gives
`r ≤ θ R` for a fixed `θ < 1`. The statement here takes `2r ≤ R`. The gradient is over the open
edges inside `𝒞_∞ ∩ B_r(y)`; `u` is a function on `ℝ × ℤ²` which is caloric on `𝒞_∞ ∩ B_R(y)`
(the coarsening `[u]_𝒫` on `B_R(y)` reads `u` at anchors which may lie outside the ball). -/
def DarioGuLipschitzTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ y : Vertex 2,
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ r R : ℝ,
          M ω ≤ r → 2 * r ≤ R → ∀ u : ℝ → Vertex 2 → ℝ,
            IsClusterCaloric ω (clusterBall (uniqueInfiniteComponent h) y R) (-R ^ 2) 0 u →
            ∀ τ ∈ Set.Ioc (-r ^ 2) 0,
              Real.sqrt (gradEnergy ω (clusterBall (uniqueInfiniteComponent h) y r) (u τ) /
                  (clusterBall (uniqueInfiniteComponent h) y r).card) ≤
                C / R * avgL2 (subMean (coarsenPar ω (uniqueInfiniteComponent h) u)
                  (parabolicCylinderAt y R)) (parabolicCylinderAt y R)

/-- **Dario–Gu, Theorem 5** (homogenization of the parabolic Cauchy–Dirichlet problem) for the
boundary condition `f = u` caloric on `𝒞_∞ ∩ B_r(y)`, with the interior gradient bound (3.16) of
Lemma 3.7 (`k = l = 0`, boundary layer `r' = r/8`), in dimension two.

Printed statement (lines 1280-1306 of the source): *Fix an exponent `δ > 0`, then there exist
`C(δ) < ∞`, `s(δ) > 0`, `α(δ) > 0` such that for any `y ∈ ℤ^d` there is `M_hom,δ(y) ≤ O_s(C)` such
that, for every `r > M_hom(y)` and every boundary condition `f ∈ W_par(I_r × (𝒞_∞ ∩ B_r(y)))`,
with `u` the weak solution of (3.8) (`∂_t u - ∇·a∇u = 0` in `I_r × (𝒞_∞ ∩ B_r(y))`, `u = f` on
the parabolic boundary) and `ū` the weak solution of (3.9) (`∂_t ū - (σ̄²/2) Δ ū = 0` in
`I_r × cv(ℤ^d ∩ B_r(y))`, `ū = f̃` on the parabolic boundary, `f̃ = [f]_𝒫 ⋆ η`),
`r^{-1} ‖u - ū‖_{L̲²(I_r × (𝒞_∞ ∩ B_r(y)))} ≤ C r^{-α} ‖∇f‖_{L̲^{2+δ}(I_r × (𝒞_∞ ∩ B_r(y)))}`.*
Lemma 3.7 (lines 1357-1361): `‖∂_t^l ∇^k (Υ ∇ū)‖_{L^∞} ≤ C (r')^{-(k+2l)} (r/r')^{(2+d)/2} ‖∇f‖_{L̲^{2+δ}}`.

The proof of Proposition 3.9 (line 1789) applies Theorem 5 with `f = u`; this is the form stated
here, with `u(·, x)` continuously differentiable in time at every vertex (`f ∈ W_par`). For a
general `f` the printed estimate cannot hold: for `f(t, x) = t` the right side vanishes while
`u - ū` does not. -/
def DarioGuThmFiveTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∀ δ : ℝ, 0 < δ → ∀ η : EuclideanSpace ℝ (Fin 2) → ℝ, IsMollifier η →
      ∃ s C α : ℝ, 0 < s ∧ 0 < C ∧ 0 < α ∧ ∀ y : Vertex 2,
        ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
          ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ r : ℝ, M ω ≤ r →
            ∀ u : ℝ → Vertex 2 → ℝ,
              IsClusterCaloric ω (clusterBall (uniqueInfiniteComponent h) y r) (-r ^ 2) 0 u →
              IsTimeCOne (-r ^ 2) 0 u →
              ∀ ū : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ,
                IsHeatDirichletSolution σ (latticeHull y r) r
                  (mollifiedCoarsening ω (uniqueInfiniteComponent h) η u) ū →
                r⁻¹ * parAvgL2 (uniqueInfiniteComponent h) y r
                    (fun t x => u t x - ū (t, latticeEuclideanEmbedding x)) ≤
                  C * r ^ (-α) * parGradLp ω (uniqueInfiniteComponent h) y r (2 + δ) u ∧
                ∀ z ∈ Set.Ioo (-r ^ 2 / 2) 0 ×ˢ
                    Metric.ball (latticeEuclideanEmbedding y) (3 * r / 4),
                  ‖fderiv ℝ (fun ξ => ū (z.1, ξ)) z.2‖ ≤
                    C * parGradLp ω (uniqueInfiniteComponent h) y r (2 + δ) u

/-- Existence of the solution `ū` of (3.9) (Dario–Gu, line 1294: "`ū` be the weak solution of the
homogenized, continuous in space, parabolic equation"), for the boundary conditions `f̃` of the
caloric functions with `C¹` time dependence. The source does not prove or cite it. -/
def DarioGuHomogenizedSolutionExists : Prop :=
  ∀ σ : ℝ, 0 < σ → ∀ η : EuclideanSpace ℝ (Fin 2) → ℝ, IsMollifier η →
    ∀ (ω : Configuration 2) (K : OpenComponent ω) (y : Vertex 2) (r : ℝ), 1 ≤ r →
      ∀ u : ℝ → Vertex 2 → ℝ, IsTimeCOne (-r ^ 2) 0 u →
        ∃ ū : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ,
          IsHeatDirichletSolution σ (latticeHull y r) r (mollifiedCoarsening ω K η u) ū

end Rigidity.Green

import Rigidity.Proofs.Green.DarioGuApproxInputs
import Rigidity.Proofs.Corrector.PlanarShiftedAnchor

/-!
# The parabolic objects of §3.2 of Dario–Gu in dimension two

Dario–Gu prove Theorem 3 (the gradient bound on the heat kernel, `DarioGuGradientBoundTwo`) in
§3.2 from Proposition 3.9, a large-scale `C^{0,1}` estimate for caloric functions on `𝒞_∞`. This
file fixes the objects of Proposition 3.9 and states it.

* `IsClusterCaloric ω V a b u`: `∂_t u = Δ u` (unit conductances) at the vertices of `V` all of
  whose open neighbours lie in `V` (the interior `int_a V` of §1.6.3), for times in `(a, b)`, with
  `u(·, x)` continuous on `[a, b]` for `x ∈ V` (a weak solution in `H_par`; the equation is an ODE).
* `coarsenPar ω K u`: the coarsened function `[u]_𝒫` of (2.5)-(2.6) on `ℝ × ℝ²`, piecewise constant
  on the cells `x + [-1/2, 1/2)²`, equal to `u(t, x)` if `x ∈ K` and to `u(t, z(x))` otherwise,
  `z(x)` the anchor of the partition cube of `x` (the point of its crossing cluster closest to the
  centre, as in the source).
* `parabolicCylinderAt y r = (-r², 0] × B_r(y)` in `ℝ × ℝ²`.
* `DarioGuLipschitzTwo`: Proposition 3.9, for `r ∈ [M, R/2]` (see the docstring).
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

/-! ### The named statements -/

/-- **Dario–Gu, Proposition 3.9** (large-scale `C^{0,1}` estimate for caloric functions on `𝒞_∞`),
in dimension two, for `r ∈ [M, R/2]`.

Printed statement (lines 1690-1709 of the source): *There exist a constant `C < ∞`, an exponent
`s > 0` such that for each point `y ∈ ℤ^d`, there exists a non-negative random variable
`M_{C^{0,1}-reg}(y) ≤ O_s(C)` such that, for every `r ≥ M_{C^{0,1}-reg}(y)`, and every weak
solution `u ∈ H_par(I_R × (𝒞_∞ ∩ B_R(y)))` of `∂_t u - ∇·a∇u = 0`, one has, for every radius
`r ∈ [M_{C^{0,1}-reg}(y), R]`,
`sup_{t ∈ I_r} ‖∇u(t, ·)‖_{L̲²(𝒞_∞ ∩ B_r(y))} ≤ (C/R) ‖[u]_𝒫 - ([u]_𝒫)_{I_R × B_R(y)}‖_{L̲²(I_R × B_R(y))}`.*

At `r = R` the printed inequality fails: a time-independent `u`, harmonic at the interior vertices
of `𝒞_∞ ∩ B_R(y)`, with values `±1` at the boundary vertices of opposite signs along about `cR` open
edges between them, has `‖∇u‖²_{L̲²(𝒞_∞ ∩ B_R(y))}` of order `R^{-1}`, while the square of the right
side is at most of order `R^{-2}`. The proof (Step 4, lines 1851-1859: "completes the proof of
Proposition 3.9 with the radius `r/2` instead of `r`") gives the estimate at the radius `r/2` for
`r ∈ [M, R]`, that is for `2r ≤ R`, the form stated here. The gradient is over the open edges inside
`𝒞_∞ ∩ B_r(y)`; `u` is a function on `ℝ × ℤ²` which is caloric on `𝒞_∞ ∩ B_R(y)` (the coarsening
`[u]_𝒫` on `B_R(y)` reads `u` at anchors which may lie outside the ball). -/
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

end Rigidity.Green

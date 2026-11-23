import Rigidity.Proofs.Green.PlanarHeatKernelInputs
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.Average

/-!
# The inputs of the proof of Theorem 1 of Dario–Gu in dimension two

Dario–Gu, *Quantitative homogenization of the parabolic and elliptic Green's functions on
percolation clusters* (arXiv:1909.10439v4), prove Theorem 1 (`DarioGuHeatKernelTwo`) in §4.3 from
the results of §4.1–§4.2 (Lemma 4.2, Lemma 4.3, Proposition 4.4), the Gaussian upper bound of
Barlow (Theorem 3.1, cited), the Carne–Varopoulos bound (Proposition 2.11, cited; rigr57's
`CarneVaropoulosTwo`) and the concentration of the Gaussian mass of the cluster (Proposition A.3).
This file fixes the planar objects of §3–§4 and states these results as named hypotheses.

* `dgPhi C t r` is `Φ_C(t, x)` of (3.1) at `|x| = r` in dimension two, and `dgExponent C t r` its
  exponent: `Φ_C = C t^{-1} exp(-dgExponent)`.
* `dgQ`, `dgTwoScale`, `dgV`, `dgW` are the functions `q` (4.3), `h` (4.1), `v` (4.6) and
  `w = h - v - q` of §4. The parabolic problems (4.3) and (4.6) are solved by the semigroup of the
  cluster: `q(t, x) = Σ_z p(t - τ, x, z) q(τ, z)`; for `x ∈ 𝒞_∞` the kernel vanishes off `𝒞_∞`.
* `WeightedL2Le K C t y f B` is `‖f exp(|· - y|² / (C t))‖_{L²(K)} ≤ B` (in the regime `|x| ≤ t`;
  in general with the weight `exp(dgExponent C t |· - y|)`), expressed through finite sums.

Cited results with no proof on hand (named hypotheses with their printed statements):

* `BarlowGaussianUpperBoundTwo`: Theorem 3.1 of Dario–Gu (Barlow 2004, Theorem 1 and Lemma 1.1).
* `AKMLemmaEightNineTwo`: Lemma 3.6 of Dario–Gu (Armstrong–Kuusi–Mourrat, Lemma 8.9).

Results of Dario–Gu whose proofs (§3, §4.1–§4.2, App. A) are not formalized here:

* `DarioGuApproxLemmaTwo` (Lemma 4.2, in the form used in the iteration step of §4.3),
  `DarioGuCorrectorLemmaTwo` (Lemma 4.3), `DarioGuTwoScaleErrorTwo` (Proposition 4.4),
  `DarioGuTwoScaleInitialTwo` (the estimate of `h - θ^{-1} p̄` in §4.3, whose details the source
  leaves to the reader), `DarioGuDensityGaussianTwo` (Proposition A.3).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- The Euclidean distance between two lattice points. -/
noncomputable def latticeDist (x y : Vertex 2) : ℝ :=
  ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖

/-- The exponent of `Φ_C(t, x)` (Dario–Gu, (3.1)) at `|x| = r`: `r² / (C t)` if `r ≤ t` and
`r / C (1 + ln(r / t))` if `r > t`. -/
noncomputable def dgExponent (C t r : ℝ) : ℝ :=
  if r ≤ t then r ^ 2 / (C * t) else r / C * (1 + Real.log (r / t))

/-- **Dario–Gu, (3.1)** in dimension two: `Φ_C(t, x) = C t^{-1} exp(-|x|²/(C t))` if `|x| ≤ t`
and `C t^{-1} exp(-|x|/C (1 + ln(|x|/t)))` if `|x| ≥ t`, at `|x| = r`. -/
noncomputable def dgPhi (C t r : ℝ) : ℝ :=
  C * t⁻¹ * Real.exp (-dgExponent C t r)

/-! ### Cited results -/

/-- **Dario–Gu, Theorem 3.1** (Gaussian upper bound; Barlow, *Random walks on supercritical
percolation clusters*, Ann. Probab. 2004, Theorem 1 and Lemma 1.1), in dimension two.

Printed statement (lines 1220-1228 of the source): *There exist an exponent `s > 0`, a positive
constant `C < ∞` such that for each `y`, there exists a random time `T_NA(y)` satisfying
`T_NA(y) ≤ O_s(C)`, such that, on the event `{y ∈ 𝒞_∞}`, for every time `t ∈ (0, ∞)` satisfying
`t ≥ T_NA(y)`, and every point `x ∈ 𝒞_∞`, `p(t, x, y) ≤ Φ_C(t, x - y)`.*

Citing lines: "we record the result of Barlow [Ba], who established Gaussian bounds on the
transition kernel" (1185); "The stochastic integrability estimate (3.4) is not stated in
Theorem 1.1 of [Ba] but is mentioned in its remark equation (0.5) following the theorem"
(1231-1232); "the result of Barlow is proved for the heat kernel associated to the constant speed
random walk and on the percolation cluster only ... The adaptation to the variable speed random
walk ... only requires a typographical change of the proof" (1251-1254). `openHeat` is the
variable speed walk with unit conductances. -/
def BarlowGaussianUpperBoundTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ y : Vertex 2,
      ∃ T : Configuration 2 → ℝ, Measurable T ∧ (∀ ω, 0 ≤ T ω) ∧ IsOsBond 2 p T s C ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          y ∈ (uniqueInfiniteComponent h).supp → ∀ t : ℝ, 0 < t → T ω ≤ t →
            ∀ x ∈ (uniqueInfiniteComponent h).supp, openHeat ω t x y ≤ dgPhi C t (latticeDist x y)

/-- The parabolic cylinder `I_r × B_r = (-r², 0] × B_r` of `ℝ × ℝ²` (Dario–Gu, §1.6). -/
def parabolicCylinder (r : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
  Set.Ioc (-r ^ 2) 0 ×ˢ Metric.ball 0 r

/-- The average `L²` norm `‖f‖_{L̲²(U)} = (⨍_U f²)^{1/2}`. -/
noncomputable def avgL2 (f : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ)
    (U : Set (ℝ × EuclideanSpace ℝ (Fin 2))) : ℝ :=
  Real.sqrt (⨍ z in U, f z ^ 2)

/-- `f - (f)_U`, the function minus its mean on `U`. -/
noncomputable def subMean (f : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ)
    (U : Set (ℝ × EuclideanSpace ℝ (Fin 2))) : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun z => f z - ⨍ z' in U, f z'

/-- `w` is a classical solution of `∂_t w - (σ/2) Δ w = 0` in `U`, of class `C²` on an open
neighbourhood of the closure of `U`. On a bounded cylinder such a `w` is a weak solution in
`H_par`. -/
def IsCaloricOn (σ : ℝ) (w : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ)
    (U : Set (ℝ × EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ V : Set (ℝ × EuclideanSpace ℝ (Fin 2)), IsOpen V ∧ closure U ⊆ V ∧ ContDiffOn ℝ 2 w V ∧
    ∀ z ∈ U, deriv (fun s => w (s, z.2)) z.1 =
      σ / 2 * Laplacian.laplacian (fun x => w (z.1, x)) z.2

/-- **Dario–Gu, Lemma 3.6** (Armstrong–Kuusi–Mourrat, *Quantitative stochastic homogenization
and large-scale regularity*, Lemma 8.9), in dimension two, for the operator `∂_t - (σ/2) Δ`
(`σ = σ̄²`).

Printed statement (lines 1721-1744 of the source): *Fix an exponent `β ∈ (0, 1]`, `K ≥ 1` and
`X ≥ 1`. Let `R ≥ 4X` and `v ∈ L²(I_R × B_R)` have the property that, for every `r ∈ [X, R/4]`,
there exists a function `w ∈ H_par(I_r × B_r)` which is a weak solution of
`∂_t w - (σ̄²/2) Δ w = 0` in `I_r × B_r`, satisfying
`‖v - w‖_{L̲²(I_{r/2} × B_{r/2})} ≤ K r^{-β} ‖v - (v)_{I_{4r} × B_{4r}}‖_{L̲²(I_{4r} × B_{4r})}`.
Then there exists a constant `C(β, K, d, λ) < ∞` such that for every `r ∈ [X, R]`,
`r^{-1} ‖v - (v)_{I_r × B_r}‖_{L̲²(I_r × B_r)} ≤ C R^{-1} ‖v - (v)_{I_R × B_R}‖_{L̲²(I_R × B_R)}`.*

Citing lines: "Lemma 3.6 [Lemma 8.9 of [AKM]]" (1720); "To prove Proposition 3.5, we apply the
previous lemma and combine it with Theorem 3.2" (1745). The comparison functions `w` are taken
classical (`IsCaloricOn`), which are weak solutions; the printed statement implies this one. The
QSH formalization of the book has no declaration for Lemma 8.9 at its current head. -/
def AKMLemmaEightNineTwo : Prop :=
  ∀ σ β K : ℝ, 0 < σ → 0 < β → β ≤ 1 → 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ X R : ℝ, 1 ≤ X → 4 * X ≤ R → ∀ v : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ,
      MemLp v 2 (volume.restrict (parabolicCylinder R)) →
      (∀ r : ℝ, X ≤ r → r ≤ R / 4 → ∃ w : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ,
        IsCaloricOn σ w (parabolicCylinder r) ∧
          avgL2 (v - w) (parabolicCylinder (r / 2)) ≤
            K * r ^ (-β) * avgL2 (subMean v (parabolicCylinder (4 * r)))
              (parabolicCylinder (4 * r))) →
      ∀ r : ℝ, X ≤ r → r ≤ R →
        r⁻¹ * avgL2 (subMean v (parabolicCylinder r)) (parabolicCylinder r) ≤
          C * R⁻¹ * avgL2 (subMean v (parabolicCylinder R)) (parabolicCylinder R)

/-! ### The functions of §4 -/

/-- `p̄(t, x - y)` at lattice points. -/
noncomputable def latticeGaussian (σ t : ℝ) (x y : Vertex 2) : ℝ :=
  gaussianHeat σ t (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y)

/-- **Dario–Gu, (4.3)**: `q(t, x, τ, y)`, the solution on the cluster from time `τ` of the heat
equation with initial value `θ^{-1} p̄(τ, · - y)`. -/
noncomputable def dgQ (ω : Configuration 2) (σ θ t τ : ℝ) (x y : Vertex 2) : ℝ :=
  ∑' z : Vertex 2, openHeat ω (t - τ) x z * (θ⁻¹ * latticeGaussian σ τ z y)

/-- **Dario–Gu, (4.1)**: the two-scale expansion
`h(t, x, y) = θ^{-1} (p̄(t, x - y) + Σ_k D_{e_k} p̄(t, · - y)(x) χ_{e_k}(x))`, with
`D_{e_k} u(x) = u(x + e_k) - u(x)` (§1.6). -/
noncomputable def dgTwoScale (σ θ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ) (t : ℝ) (x y : Vertex 2) : ℝ :=
  θ⁻¹ * (latticeGaussian σ t x y +
    ∑ k : Fin 2, (latticeGaussian σ t (x + Pi.single k 1) y - latticeGaussian σ t x y) * χ k x)

/-- **Dario–Gu, (4.6)**: `v(t, x, τ, y)`, the solution on the cluster from time `τ` of the heat
equation with initial value `h(τ, ·, y) - θ^{-1} p̄(τ, · - y)`. -/
noncomputable def dgV (ω : Configuration 2) (σ θ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ) (t τ : ℝ)
    (x y : Vertex 2) : ℝ :=
  ∑' z : Vertex 2, openHeat ω (t - τ) x z *
    (dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y)

/-- **Dario–Gu, §4**: `w := h - v - q`. -/
noncomputable def dgW (ω : Configuration 2) (σ θ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ) (t τ : ℝ)
    (x y : Vertex 2) : ℝ :=
  dgTwoScale σ θ χ t x y - dgV ω σ θ χ t τ x y - dgQ ω σ θ t τ x y

/-- The correctors `χ_{e_k}` of the cluster `K` normalized around `y ∈ K` (Dario–Gu, §2.2.1):
`x ↦ x_k + χ_{e_k}(x)` is a corrected plane of slope `e_k` and `χ_{e_k}(y) = 0` (the point of
`𝒞_∞` closest to `y ∈ 𝒞_∞` is `y`). -/
def IsDGCorrector {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2)
    (χ : Fin 2 → Vertex 2 → ℝ) : Prop :=
  ∀ k : Fin 2, IsCorrectedPlane K (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) ∧
    χ k y = 0

/-- `‖f exp(dgExponent C t |· - y|)‖_{L²(K)} ≤ B`, through finite sums. In the regime `|x| ≤ t`
the weight is `exp(|x - y|² / (C t))`. -/
def WeightedL2Le (K : Set (Vertex 2)) (C t : ℝ) (y : Vertex 2) (f : Vertex 2 → ℝ) (B : ℝ) :
    Prop :=
  ∀ S : Finset (Vertex 2), (∀ x ∈ S, x ∈ K) →
    ∑ x ∈ S, (f x * Real.exp (dgExponent C t (latticeDist x y))) ^ 2 ≤ B ^ 2

/-! ### Results of Dario–Gu §4.1–§4.2 and Appendix A -/

/-- **Dario–Gu, Lemma 4.2**, in the form used in the iteration step of §4.3: if
`|θ^{-1} p̄(τ, z - y) - p(τ, z, y)| ≤ ε Φ_{C₀}(τ, z - y)` on `𝒞_∞`, then for `t ≥ 3τ`,
`τ ≥ T_approx,α(y)` and `x ∈ 𝒞_∞`,
`|q(t, x, τ, y) - p(t, x, y)| ≤ C (ε (τ/t)^{1/2} + τ^{-1/2 + α}) Φ_C(t, x - y)`.

Printed Lemma 4.2 (lines 1977-1990) is the case where the hypothesis is Barlow's bound (3.4)
(`ε = 1`); lines 2618-2622: "We go back to the proof of Lemma 4.2 and in the inequality (4.5),
instead of using the Nash-Aronson estimate stated in Theorem 3.1, we use the homogenization
estimate (4.27). We then proceed with the proof and do not make any other modification. This
implies the following improved version of Lemma 4.2". In the proof (lines 2005-2023) the
hypothesis enters only through the first term of (4.5), linearly. -/
def DarioGuApproxLemmaTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ C₀ : ℝ, 0 < C₀ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
    ∃ T : Configuration 2 → ℝ, Measurable T ∧ (∀ ω, 0 ≤ T ω) ∧ IsOsBond 2 p T s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ t τ ε : ℝ, T ω ≤ τ → 3 * τ ≤ t → 0 ≤ ε →
          (∀ z ∈ (uniqueInfiniteComponent h).supp,
            |(theta 2 p)⁻¹ * latticeGaussian σ τ z y - openHeat ω τ z y| ≤
              ε * dgPhi C₀ τ (latticeDist z y)) →
          ∀ x ∈ (uniqueInfiniteComponent h).supp,
            |dgQ ω σ (theta 2 p) t τ x y - openHeat ω t x y| ≤
              C * (ε * (τ / t) ^ (1 / 2 : ℝ) + τ ^ (-(1 / 2 : ℝ) + α)) *
                dgPhi C t (latticeDist x y)

/-- **Dario–Gu, Lemma 4.3** (lines 2159-2163): for `t ≥ 3τ`, `t - τ ≥ T'_NA(y)` and
`√τ ≥ M_corr,α(y)`, `|v(t, x, τ, y)| ≤ C τ^{-1/2 + α/2} Φ_C(t, x - y)`. The two minimal times are
merged into one `M ≤ O_s(C)` with `τ ≥ M`. -/
def DarioGuCorrectorLemmaTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin 2 → Vertex 2 → ℝ,
          IsDGCorrector (uniqueInfiniteComponent h) y χ → ∀ t τ : ℝ, M ω ≤ τ → 3 * τ ≤ t →
          ∀ x ∈ (uniqueInfiniteComponent h).supp,
            |dgV ω σ (theta 2 p) χ t τ x y| ≤
              C * τ ^ (-(1 / 2 : ℝ) + α / 2) * dgPhi C t (latticeDist x y)

/-- **Dario–Gu, Proposition 4.4** (lines 2234-2239), in dimension two:
`‖w(t, ·, τ, y) exp(Ψ_C(t, |· - y|))‖_{L²(𝒞_∞)} ≤ C (t/τ)^{1/2} τ^{-d/4 - 1/2 + α/2}` for
`√t ≥ max(M_corr,α(y), M_flux,α(y))`. Here `τ ≥ M` and `t ≥ 3τ` (the regime of §4.3), and the
weight is the Gaussian factor of `exp Ψ_C` (see `WeightedL2Le`). -/
def DarioGuTwoScaleErrorTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin 2 → Vertex 2 → ℝ,
          IsDGCorrector (uniqueInfiniteComponent h) y χ → ∀ t τ : ℝ, M ω ≤ τ → 3 * τ ≤ t →
            WeightedL2Le (uniqueInfiniteComponent h).supp C t y
              (fun x => dgW ω σ (theta 2 p) χ t τ x y)
              (C * (t / τ) ^ (1 / 2 : ℝ) * τ ^ (-(1 : ℝ) + α / 2))

/-- **Dario–Gu, §4.3, fourth item of the base case** (lines 2556-2562): the term
`h(t, ·, y) - θ^{-1} p̄(t, · - y) = θ^{-1} Σ_k D_{e_k} p̄(t, · - y) χ_{e_k}` "can then be estimated
by using the sublinearity of the corrector stated in Proposition 2.9 and the assumption
`√t ≥ M_corr,α(z)` ... the details are left to the reader. It accounts for an error of order
`t^{-d/4 - 1/2 + δ}`." -/
def DarioGuTwoScaleInitialTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin 2 → Vertex 2 → ℝ,
          IsDGCorrector (uniqueInfiniteComponent h) y χ → ∀ t : ℝ, M ω ≤ t →
            WeightedL2Le (uniqueInfiniteComponent h).supp C t y
              (fun x => dgTwoScale σ (theta 2 p) χ t x y -
                (theta 2 p)⁻¹ * latticeGaussian σ t x y)
              (C * t ^ (-(1 : ℝ) + α))

/-- **Dario–Gu, Proposition A.3** (lines 2911-2920), second part, in dimension two: for every
`α > 0` there is `T_dense,α(y) ≤ O_s(C)` such that for `t > T_dense,α(y)`,
`|∫_{𝒞_∞} p̄(t, x - y) dx - θ(p)| ≤ C t^{-(1/2 - α)}`. -/
def DarioGuDensityGaussianTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
    ∃ T : Configuration 2 → ℝ, Measurable T ∧ (∀ ω, 0 ≤ T ω) ∧ IsOsBond 2 p T s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ t : ℝ, T ω < t →
        |∑' x : (uniqueInfiniteComponent h).supp, latticeGaussian σ t x.val y - theta 2 p| ≤
          C * t ^ (-(1 / 2 - α))

/-- The results of Dario–Gu §4.1–§4.2 and Proposition A.3 for the diffusivity `σ = σ̄²`. -/
def DarioGuSectionFourTwo (p : unitInterval) (σ : ℝ) : Prop :=
  DarioGuApproxLemmaTwo p σ ∧ DarioGuCorrectorLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
    DarioGuTwoScaleInitialTwo p σ ∧ DarioGuDensityGaussianTwo p σ

end Rigidity.Green

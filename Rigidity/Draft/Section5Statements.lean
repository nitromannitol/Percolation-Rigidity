import Rigidity.Draft.Section2Statements
import LatticeProb.Prob.Percolation.LatticeClusterBall

/-! Statements of Theorem 1.3 and of the numbered results of Sections 5.1 and 5.2 (d = 2). The
statements follow the corrected draft `paper/percolation-harmonic-corrected.tex` (each correction
is marked `% CORRECTION [Cn]` there).
Fix a deterministic finitely supported `f : ℤ² → ℤ`; `G` is the Green function of `𝒞_∞` of eq.
`green-function-2D` (`Δ G(·, y) = -δ_y`, sublinear, `G(y, y) = 0`; `IsGreenColumn`).

* Convention: the statements (`…Stmt`) omit the regime `p_c(2) < p < 1`; the composed theorems
  (`Rigidity/Proofs/Assembly`) carry it as hypotheses `criticalProbability 2 < p` and `p < 1`.

* [C13, C14] The corrected draft defines `u_f` with the normalized Green function
  `H(x, y) = G(x, y) - κ(y)`. When `Σ f = 0`, `Σ_y f(y) H(x, y) = Σ_y f(y) G(x, y) - L` with `L`
  the limit at infinity of the `G`-potential; the statements below write it that way (`potential`
  is the `G`-potential) and assert that the limit exists. Proposition 5.5 is unaffected (a constant
  shift) and Lemma 5.6 is an identity valid for any kernel.
* [C12] Theorem 5.1, eq. `linear-decay`: `limsup |x| |u(x)| > 0`.
* [C17, C19, C30] Propositions 5.7 and 5.11 fix a slope `p ≠ 0`; they are stated for every
  `p ≠ 0`.
* [C29] Proposition 5.11 bounds the density from below for all large `k` (lower limit), which is
  what Step 3 of the proof of Proposition 5.7 needs.
* [C18] Proposition 5.8: leading term `-Σᵢ Mᵢ ∂ᵢḠ(x)`. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Section5

open Rigidity.Section2

/-- The `ℓ¹` norm `|x|`. -/
def l1 (x : Vertex 2) : ℝ := ∑ i, |(x i : ℝ)|

/-- The Euclidean norm `|x|₂`. -/
noncomputable def eucl (x : Vertex 2) : ℝ := ‖latticeEuclideanEmbedding x‖

variable {ω : Configuration 2}

/-- `G(x, y)` is the Green function of the component: each column `G(·, y)` is the paper's. -/
def IsGreenFamily (C : OpenComponent ω) (G : C → C → ℝ) : Prop :=
  ∀ y, IsGreenColumn 2 le_rfl C y (fun x => G x y)

/-- The potential `u_f(x) = Σ_{y ∈ 𝒞_∞} f(y) G(x, y)`. -/
noncomputable def potential (C : OpenComponent ω) (G : C → C → ℝ) (f : Vertex 2 → ℤ) (x : C) :
    ℝ :=
  ∑ᶠ y : C, (f y.val : ℝ) * G x y

/-- The mass `Σ_{x ∈ 𝒞_∞} f(x)`. -/
noncomputable def mass (C : OpenComponent ω) (f : Vertex 2 → ℤ) : ℤ := ∑ᶠ y : C, f y.val

/-- `Σ_{y ∈ 𝒞_∞} f(y) ℓ(y)`. -/
noncomputable def pairing (C : OpenComponent ω) (f : Vertex 2 → ℤ) (ℓ : C → ℝ) : ℝ :=
  ∑ᶠ y : C, (f y.val : ℝ) * ℓ y

/-- Eq. `linear-decay` (as intended): `limsup_{|x| → ∞} |x| |u(x)| > 0`. -/
def LinearDecay (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∃ x : C, R ≤ l1 x.val ∧ c ≤ l1 x.val * |u x|

/-- Eq. `compactly-supported`: `u ≡ 0` on `𝒞_∞ \ B_R` for some `R`. -/
def EventuallyZero (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val → u x = 0

/-- Theorem 1.3 (d = 2): almost surely, for every finitely supported `f : ℤ² → ℤ` and every
`u : 𝒞_∞ → ℝ` with `-Δu = f` and `lim sup_R R sup_{B_R \ B_{R/2}} |u| = 0`, `u` has finite
support. -/
def FastDecayStmt (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ f : Vertex 2 → ℤ, (Function.support f).Finite →
    ∀ u : uniqueInfiniteComponent h → ℝ,
      (∀ x, -componentLaplacian (uniqueInfiniteComponent h) u x = f x.val) →
      (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ x : uniqueInfiniteComponent h,
        R / 2 ≤ eucl x.val → eucl x.val < R → R * |u x| ≤ ε) →
      (Function.support u).Finite

/-- Theorem 5.1: almost surely, every `u : 𝒞_∞ → ℝ` with `u(x) → 0` and `Δu ∈ ℤ` either decays at
most like `|x|^{-1}` or vanishes outside a ball. -/
def FastDecayDichotomyStmt (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u : uniqueInfiniteComponent h → ℝ, Tendsto u cofinite (𝓝 0) →
      (∀ x, ∃ z : ℤ, componentLaplacian (uniqueInfiniteComponent h) u x = z) →
      LinearDecay _ u ∨ EventuallyZero _ u

/-- Proposition 5.3: almost surely, either `Σ f ≠ 0`, or `u_f` converges at infinity and
`u_f - lim u_f` satisfies eq. `linear-decay` or eq. `compactly-supported`. -/
def FastDecayPotentialStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
      mass (uniqueInfiniteComponent h) f ≠ 0 ∨ ∃ L : ℝ, Tendsto (potential _ G f) cofinite (𝓝 L) ∧
        (LinearDecay _ (fun x => potential _ G f x - L) ∨
          EventuallyZero _ (fun x => potential _ G f x - L))

/-- Proposition 5.5: almost surely, if `Σ f ≠ 0` then `u_f = Θ(log |x|)`. -/
def LogGrowthStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G → mass (uniqueInfiniteComponent h) f ≠ 0 →
      ∃ c C R₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : uniqueInfiniteComponent h, R₀ ≤ l1 x.val →
        c * Real.log (l1 x.val) ≤ |potential _ G f x| ∧
          |potential _ G f x| ≤ C * Real.log (l1 x.val)

/-- Lemma 5.6: on the event `Σ f = 0` there is a finitely supported vector field `F` on the
oriented edges of `𝒞_∞` with `u_f(x) = Σ_e F(e) ∇_y G(x, e)`, where `∇_y G(x, (a, b)) =
G(x, a) - G(x, b)` and each unoriented edge is counted once; the size of its support and its
`L²` norm are bounded by a random variable `X ≤ O_s(C_f)`. (Sums over oriented edges count each
edge twice; the factor is absorbed in `C_f`.) -/
def MeanZeroRepresentationStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∃ Cf s : ℝ, 0 < Cf ∧ 0 < s ∧ ∃ X : Configuration 2 → ℝ, Measurable X ∧ IsOs 2 p X s Cf ∧
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
      mass (uniqueInfiniteComponent h) f = 0 →
      ∃ F : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ,
        (∀ a b, F a b = -F b a) ∧
        (∀ a b, F a b ≠ 0 → (componentGraph (uniqueInfiniteComponent h)).Adj a b) ∧
        ∃ S : Finset (uniqueInfiniteComponent h × uniqueInfiniteComponent h),
          (∀ a b, F a b ≠ 0 → (a, b) ∈ S) ∧ (S.card : ℝ) ≤ X ω ∧
          Real.sqrt (∑ e ∈ S, F e.1 e.2 ^ 2) ≤ X ω ∧
          ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G → ∀ x,
            potential _ G f x = (1 / 2) * ∑ e ∈ S, F e.1 e.2 * (G x e.1 - G x e.2)

/-- Proposition 5.7: for a fixed slope `p ≠ 0`, almost surely on `Σ f = 0`, either
`Σ f ℓ_p ≠ 0`, or `u_f` converges at infinity and `u_f - lim u_f` has finite support. -/
def GradientTrichotomyStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ q : Fin 2 → ℝ, q ≠ 0 →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
      mass (uniqueInfiniteComponent h) f = 0 →
      ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        pairing _ f ℓ ≠ 0 ∨ ∃ L : ℝ, Tendsto (potential _ G f) cofinite (𝓝 L) ∧
          (Function.support (fun x => potential _ G f x - L)).Finite

/-- Proposition 5.8: there are `C, s` and a minimal scale `M_f ≤ O_s(C)` such that on `Σ f = 0`,
`u_f` has a limit `L` at infinity and, for `|x| ≥ M_f`,
`|u_f(x) - L + Σᵢ (Σ_y f(y) ℓ_{eᵢ}(y)) ∂ᵢḠ(x)| ≤ C |x|^{-5/4}`, with `Ḡ` a multiple of the
Green function of `ℝ²` [C18]. -/
def TwoScaleExpansionStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∃ κ : {a : ℝ // 0 < a},
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ IsOs 2 p M s C ∧
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
      mass (uniqueInfiniteComponent h) f = 0 →
      ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
      ∀ ℓ : Fin 2 → uniqueInfiniteComponent h → ℝ,
        (∀ i, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) (ℓ i)) →
      ∃ L : ℝ, ∀ x : uniqueInfiniteComponent h, M ω ≤ l1 x.val →
        |potential _ G f x - L + ∑ i, pairing _ f (ℓ i) *
            fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val) (EuclideanSpace.single i 1)|
          ≤ C * Real.rpow (l1 x.val) (-5 / 4)

/-- The oriented edges of `𝒞_∞` inside the Euclidean ball `B_r` on which both `∇u` and `∇ℓ` are
nonzero. -/
def activeEdges (C : OpenComponent ω) (u ℓ : C → ℝ) (r : ℝ) : Set (C × C) :=
  {e | (componentGraph C).Adj e.1 e.2 ∧ eucl e.1.val < r ∧ eucl e.2.val < r ∧
    u e.1 ≠ u e.2 ∧ ℓ e.1 ≠ ℓ e.2}

/-- Proposition 5.11 ([C29], [C30]): for a fixed slope `p ≠ 0`, almost surely on `Σ f = 0` with
`u_f - lim u_f` of infinite support,
`liminf_k |B_{2^k}|⁻¹ |{e ∈ E(B_{2^k}) : ∇u_f(e) ≠ 0, ∇ℓ_p(e) ≠ 0}| > 0`: some `c > 0` bounds the
density from below for all large `k`. (Oriented edges are counted, twice the number of edges.) -/
def LevelSetDensityStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ q : Fin 2 → ℝ, q ≠ 0 →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
      mass (uniqueInfiniteComponent h) f = 0 →
      ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
      ∀ L : ℝ, Tendsto (potential _ G f) cofinite (𝓝 L) →
        (Function.support (fun x => potential _ G f x - L)).Infinite →
        ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
          c ≤ ((activeEdges _ (potential _ G f) ℓ (2 ^ k)).ncard : ℝ) / (Real.pi * 4 ^ k)

end Rigidity.Section5

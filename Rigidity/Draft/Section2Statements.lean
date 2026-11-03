import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.ContinuumGreen
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Statements of the numbered results of Section 2 that the paper proves. They follow the
corrected draft `paper/percolation-harmonic-corrected.tex` (each correction is marked
`% CORRECTION [Cn]` there).

* [C4] Proposition 2.6 is stated with forward differences `u(x + e_i) - u(x)`, zero on closed
  edges: the left side is `|D⁺G - Σᵢ D⁺ℓ_{eᵢ} ∂ᵢḠ|` on open edges and `0` on closed ones, the
  absolute value of the corrected display `|∇ₓG(x, y) - Σᵢ ∇ℓ_{eᵢ}(x) ∂ᵢḠ(x - y)|`.
* [C7] Lemma 2.16 with a Jordan curve `α` avoiding `N` and simple arcs `γᵢ` meeting `α` only at
  `xᵢ` and each other only at `N`.
* Convention: like every `...Stmt` of the draft, Proposition 2.6 omits the paper's standing
  assumption `p_c(d) < p < 1` (corrected draft L66, L231); the composed theorem
  `Rigidity.Assembly.greenGradientHomogenization` carries it as hypotheses `hpc`, `hp1`. Read
  alone, outside that regime, it may be false. Lemma 2.16 is deterministic. -/

open MeasureTheory LatticeProb.Percolation Classical

namespace Rigidity.Section2

variable {d : ℕ}

/-- `X ≤ O_s(θ)`: `E[exp((X/θ ∨ 0)^s)] ≤ 2`. -/
def IsOs (d : ℕ) (p : unitInterval) (X : Configuration d → ℝ) (s θ : ℝ) : Prop :=
  Integrable (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) (latticeBondLaw d p) ∧
  (∫ ω, Real.exp (Real.rpow (max (X ω / θ) 0) s) ∂latticeBondLaw d p) ≤ 2

/-- The forward difference of `u` along the open edge `(x, x + e_i)` of the component, and zero
when that edge is not an open edge. -/
noncomputable def forwardDiff {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ) (x : C)
    (i : Fin d) : ℝ :=
  if hx : (openGraph ω).Adj x.val (x.val + LatticeProb.unit i) then
    u ⟨x.val + LatticeProb.unit i, C.mem_supp_of_adj_mem_supp x.property hx⟩ - u x
  else 0

/-- The homogenized Green function `Ḡ` with conductivity `κ`, extended by zero at the pole. -/
noncomputable def greenBar (d : ℕ) (hd : 2 ≤ d) (κ : {a : ℝ // 0 < a}) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun v => if hv : v ≠ 0 then continuumGreen d hd κ ⟨v, hv⟩ else 0

/-- The lattice point `x` as a vector of `ℝ^d`. -/
def toReal (x : Vertex d) : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 _).symm (fun i => (x i : ℝ))

/-- Proposition 2.6 (homogenization of the gradient of the Green function): for some
conductivity `κ > 0` and every `δ > 0` there are `s, C` and, for each pole `y`, a minimal scale
`M(y) ≤ O_s(C)` such that for all `x, y` in the infinite cluster with `|x - y| ≥ M(y)`,
`|∇ₓG(x, y) - ∇Ḡ(x - y) - Σᵢ ∇χ_{eᵢ}(x) ∂ᵢḠ(x - y)| ≤ C |x - y|^{-1/2 + δ} |x - y|^{1 - d}`,
where `|·|` is the `ℓ¹` norm and `χ_{eᵢ}` is read off the corrected plane `ℓ_{eᵢ} = xᵢ + χ_{eᵢ}`. -/
def GreenGradientHomogenizationStmt (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval) :
    Prop :=
  ∃ κ : {a : ℝ // 0 < a}, ∀ δ : ℝ, 0 < δ → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
    ∀ y : Vertex d, ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      IsOs d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ g : uniqueInfiniteComponent h → ℝ,
          IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
        ∀ ℓ : Fin d → uniqueInfiniteComponent h → ℝ,
          (∀ i, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) (ℓ i)) →
        ∀ x : uniqueInfiniteComponent h, M ω ≤ ∑ i, |((x.val i - y i : ℤ) : ℝ)| →
          (∑ j, |forwardDiff (uniqueInfiniteComponent h) g x j
              - fderiv ℝ (greenBar d hd κ) (toReal x.val - toReal y) (EuclideanSpace.single j 1)
              - ∑ i, (forwardDiff (uniqueInfiniteComponent h) (ℓ i) x j - if i = j then 1 else 0)
                  * fderiv ℝ (greenBar d hd κ) (toReal x.val - toReal y)
                      (EuclideanSpace.single i 1)|)
            ≤ C * Real.rpow (∑ i, |((x.val i - y i : ℤ) : ℝ)|) (-1 / 2 + δ)
                * Real.rpow (∑ i, |((x.val i - y i : ℤ) : ℝ)|) (1 - (d : ℝ))

/-- The unit sphere `S²` of `ℝ³` and its north pole. -/
abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The north pole `(0, 0, 1)`. -/
noncomputable def northPole : S2 :=
  ⟨EuclideanSpace.single 2 1, by simp⟩

/-- Lemma 2.16 (with the hypotheses its proof uses): for `K ≥ 2` distinct points `x₁, …, x_K` of
`S²`, a Jordan curve `α` through them avoiding the north pole `N`, and simple arcs `γᵢ` from `xᵢ`
to `N` with `α ∩ γᵢ = {xᵢ}` and `γᵢ ∩ γⱼ = {N}` for `i ≠ j`, the set `S² \ (α ∪ ⋃ γᵢ)` has at
least `K` connected components whose closure contains `N`. -/
def JordanCurvesStmt : Prop :=
  ∀ (K : ℕ), 2 ≤ K → ∀ (x : Fin K → S2), Function.Injective x →
    ∀ (γ : ∀ i, Path (x i) northPole) (q : S2) (α : Path q q),
      Set.InjOn α (Set.Ico 0 1) → northPole ∉ Set.range α →
      (∀ i, Function.Injective (γ i)) →
      (∀ i, Set.range α ∩ Set.range (γ i) = {x i}) →
      (∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {northPole}) →
      ∃ z : Fin K → S2,
        (∀ k, z k ∉ Set.range α ∪ ⋃ i, Set.range (γ i)) ∧
        (∀ k l, k ≠ l →
          connectedComponentIn (Set.range α ∪ ⋃ i, Set.range (γ i))ᶜ (z k) ≠
            connectedComponentIn (Set.range α ∪ ⋃ i, Set.range (γ i))ᶜ (z l)) ∧
        ∀ k, northPole ∈ closure
          (connectedComponentIn (Set.range α ∪ ⋃ i, Set.range (γ i))ᶜ (z k))

end Rigidity.Section2

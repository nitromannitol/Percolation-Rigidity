import Rigidity.Draft.Section2Statements
import Rigidity.External.JordanCurve
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Lemma 2.16: the steps of the Jordan curves lemma on `S²`

Lemma 2.16 (paper L755-785 of the corrected draft; corrections [C7] and [C8]) is carved into
three steps:

* `ParametrizeStep` (`step:2.16-parametrize`): the points `x_i` of the Jordan curve `α` are
  `α(t_i)` for parameters `0 ≤ t_1 < ⋯ < t_K < 1`, after relabelling the points;
* `LoopsStep` (`step:2.16-loops`): for each `k`, the loop `β_k = α_k ∪ γ_{k+1} ∪ γ_k` made of the
  arc `α_k` of `α` from `x_k` to `x_{k+1}` (indices modulo `K`) and of the two simple paths
  `γ_k`, `γ_{k+1}` is a Jordan curve;
* `ComponentsStep` (`step:2.16-components`): by the Jordan curve theorem on `S²` (Lemma 2.14), one
  of the two components of `S² \ β_k` avoids `Γ = α ∪ ⋃ γ_i`; it is a component of `S² \ Γ` whose
  frontier `β_k` contains the north pole, and these `K` components are distinct.

The loop `α : Path q q` is read as a map of `ℝ / ℤ` through its periodic lift `loopLift α`, so
that the arc `α_K` from `x_K` back to `x_1` is the image of `[t_K, t_1 + 1]`, like the others.
-/

namespace Rigidity.Steps.S2

open Set Rigidity.Section2

section LoopLift

variable {X : Type*} [TopologicalSpace X] {q : X}

/-- The periodic lift `u ↦ α (fract u)` of a loop `α`, i.e. the loop read on `ℝ / ℤ`. -/
noncomputable def loopLift (α : Path q q) (u : ℝ) : X :=
  α.extend (Int.fract u)

/-- The end parameter `t_{k+1}` of the arc `α_k` of the Jordan curve from `x_k` to `x_{k+1}`
(indices modulo `n + 2`): the last arc ends at `t_1 + 1`. -/
noncomputable def arcEnd {n : ℕ} (s : Fin (n + 2) → ℝ) (k : Fin (n + 2)) : ℝ :=
  if k = Fin.last (n + 1) then s 0 + 1 else s (k + 1)

end LoopLift

/-- The hypotheses of Lemma 2.16 (corrected statement): the points `x_i` are distinct, `α` is a
Jordan curve avoiding the north pole `N`, the `γ_i` are simple paths from `x_i` to `N` with
`α ∩ γ_i = {x_i}` and `γ_i ∩ γ_j = {N}` for `i ≠ j`. -/
structure IsJordanCurvesData {K : ℕ} {q : S2} (x : Fin K → S2) (γ : ∀ i, Path (x i) northPole)
    (α : Path q q) : Prop where
  injective_points : Function.Injective x
  injOn_curve : Set.InjOn α (Set.Ico 0 1)
  northPole_not_mem_curve : northPole ∉ Set.range α
  injective_path : ∀ i, Function.Injective (γ i)
  curve_inter_path : ∀ i, Set.range α ∩ Set.range (γ i) = {x i}
  path_inter_path : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {northPole}

/-- The parameters `s` list the points `x` in cyclic order along the loop `α`, within one turn. -/
structure IsCyclicParametrization {n : ℕ} {q : S2} (α : Path q q) (x : Fin (n + 2) → S2)
    (s : Fin (n + 2) → ℝ) : Prop where
  strictMono : StrictMono s
  last_lt : s (Fin.last (n + 1)) < s 0 + 1
  loopLift_eq : ∀ k, loopLift α (s k) = x k

/-- Step `step:2.16-parametrize` (paper L761): the distinct points `x_i` of the Jordan curve `α`
are, after relabelling by a permutation `σ`, the points `α(t_k)` with `0 ≤ t_1 < ⋯ < t_K < 1`. -/
def ParametrizeStep : Prop :=
  ∀ (K : ℕ) (q : S2) (α : Path q q) (x : Fin K → S2), Set.InjOn α (Set.Ico 0 1) →
    Function.Injective x → (∀ i, x i ∈ Set.range α) →
    ∃ (σ : Equiv.Perm (Fin K)) (s : Fin K → ℝ), StrictMono s ∧ (∀ k, s k ∈ Set.Ico (0 : ℝ) 1) ∧
      ∀ k, loopLift α (s k) = x (σ k)

/-- Step `step:2.16-loops` (paper L761-765): the loop `β_k = α_k ∪ γ_{k+1} ∪ γ_k` is a Jordan
curve, where `α_k` is the arc of `α` from `x_k` to `x_{k+1}`. -/
def LoopsStep : Prop :=
  ∀ (n : ℕ) (q : S2) (α : Path q q) (x : Fin (n + 2) → S2) (γ : ∀ i, Path (x i) northPole)
    (s : Fin (n + 2) → ℝ), IsJordanCurvesData x γ α → IsCyclicParametrization α x s →
    ∀ k, ∃ β : Path (x k) (x k), Set.InjOn β (Set.Ico 0 1) ∧
      Set.range β = loopLift α '' Set.Icc (s k) (arcEnd s k) ∪ Set.range (γ k) ∪
        Set.range (γ (k + 1))

/-- Step `step:2.16-components` (paper L766-784): given the Jordan curve theorem on `S²` and the
Jordan curves `β_k`, the set `S² \ Γ` has `n + 2` distinct components whose closure contains the
north pole. -/
def ComponentsStep : Prop :=
  External.JordanCurveTheoremSphere →
  ∀ (n : ℕ) (q : S2) (α : Path q q) (x : Fin (n + 2) → S2) (γ : ∀ i, Path (x i) northPole)
    (s : Fin (n + 2) → ℝ), IsJordanCurvesData x γ α → IsCyclicParametrization α x s →
    (∀ k, ∃ β : Path (x k) (x k), Set.InjOn β (Set.Ico 0 1) ∧
      Set.range β = loopLift α '' Set.Icc (s k) (arcEnd s k) ∪ Set.range (γ k) ∪
        Set.range (γ (k + 1))) →
    ∃ z : Fin (n + 2) → S2,
      (∀ k, z k ∉ Set.range α ∪ ⋃ i, Set.range (γ i)) ∧
      (∀ k l, k ≠ l →
        connectedComponentIn (Set.range α ∪ ⋃ i, Set.range (γ i))ᶜ (z k) ≠
          connectedComponentIn (Set.range α ∪ ⋃ i, Set.range (γ i))ᶜ (z l)) ∧
      ∀ k, northPole ∈ closure
        (connectedComponentIn (Set.range α ∪ ⋃ i, Set.range (γ i))ᶜ (z k))

/-- Lemma 2.16 follows from its three steps and the Jordan curve theorem on `S²`: relabel the
points in cyclic order along `α`, which leaves `Γ = α ∪ ⋃ γ_i` unchanged. -/
theorem jordanCurves_of_steps (hJ : External.JordanCurveTheoremSphere) (hP : ParametrizeStep)
    (hL : LoopsStep) (hC : ComponentsStep) : Section2.JordanCurvesStmt := by
  intro K hK x hx γ q α hα hN hγ hαγ hγγ
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 2 := ⟨K - 2, by omega⟩
  obtain ⟨σ, s, hs, hs01, hsx⟩ :=
    hP (n + 2) q α x hα hx fun i => ((hαγ i).ge (mem_singleton (x i))).1
  have hD : IsJordanCurvesData (fun k => x (σ k)) (fun k => γ (σ k)) α :=
    ⟨hx.comp σ.injective, hα, hN, fun k => hγ (σ k), fun k => hαγ (σ k),
      fun k l hkl => hγγ (σ k) (σ l) (σ.injective.ne hkl)⟩
  have hS : IsCyclicParametrization α (fun k => x (σ k)) s :=
    ⟨hs, by linarith [(hs01 (Fin.last (n + 1))).2, (hs01 0).1], hsx⟩
  have hΓ : (⋃ k, Set.range (γ (σ k))) = ⋃ i, Set.range (γ i) :=
    σ.surjective.iUnion_comp fun i => Set.range (γ i)
  obtain ⟨z, h1, h2, h3⟩ := hC hJ n q α (fun k => x (σ k)) (fun k => γ (σ k)) s hD hS
    (hL n q α (fun k => x (σ k)) (fun k => γ (σ k)) s hD hS)
  simp only [hΓ] at h1 h2 h3
  exact ⟨z, h1, h2, h3⟩

end Rigidity.Steps.S2

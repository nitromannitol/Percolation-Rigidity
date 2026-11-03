import Rigidity.Steps.Section5.Common

/-!
# Lemma 5.16: the steps of the strong maximum principle in two dimensions

Lemma 5.16 (paper L1964-1978 of the corrected draft) is carved into the finite maximum principle
(`Steps.Section5.FiniteMaxPrinciple`) and a recurrence barrier, and the comparison of the two.

The printed proof compares `g - M` with `t v`, `v = -G(·, a) ≥ 0` (correction C20), which tends
to `+∞` at infinity because the cluster is recurrent. The carve uses the same recurrence through
an exhaustion: for a vertex `a` of the cluster, a point `x` and `ε > 0`, there are a finite set
`B` and a nonnegative function `φ`, harmonic on `B \ {a}`, at least one off `B` and at most `ε`
at `x`. On a subgraph of `ℤ²` such a barrier is `1 - P_·(hit a before leaving B)`, and
`φ(x) → 0` as `B ↑` because the effective resistance from `a` to the complement of `B` diverges
(Nash-Williams). For `a ∉ Ω` and `K = (sup g - M)₊`, the function `g - M - K φ` is harmonic on
the finite set `Ω ∩ B` and nonpositive on its outer boundary, so `g(x) - M ≤ K ε`.

Neither the lower bound on `g` nor the hypothesis that `Ω` is infinite is used.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- Step `step:5.16-barrier` (recurrence of subgraphs of `ℤ²`): on an infinite open component
of a planar configuration, for every vertex `a`, point `x` and `ε > 0` there are a finite set `B`
and a nonnegative function `φ`, harmonic on `B \ {a}`, at least one off `B`, with `φ x ≤ ε`. -/
def RecurrenceBarrierStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω), (Set.univ : Set C).Infinite →
    ∀ (a x : C) (ε : ℝ), 0 < ε → ∃ B : Set C, B.Finite ∧ ∃ φ : C → ℝ, (∀ y, 0 ≤ φ y) ∧
      (∀ y, y ∉ B → 1 ≤ φ y) ∧ (∀ y ∈ B, y ≠ a → componentLaplacian C φ y = 0) ∧ φ x ≤ ε

/-- The component Laplacian of `g - M - K φ`. -/
theorem componentLaplacian_sub_const_sub_mul {ω : Configuration 2} (C : OpenComponent ω)
    (g φ : C → ℝ) (M K : ℝ) (y : C) :
    componentLaplacian C (fun z => g z - M - K * φ z) y =
      componentLaplacian C g y - K * componentLaplacian C φ y := by
  simp only [componentLaplacian, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Step `step:5.16-comparison`: on an infinite open component, the finite maximum principle and
the recurrence barrier bound a function bounded above and harmonic on a proper subset `Ω` by any
upper bound on the outer boundary of `Ω`. -/
theorem le_of_recurrenceBarrier (hF : FiniteMaxPrinciple) (hR : RecurrenceBarrierStep)
    {ω : Configuration 2} (C : OpenComponent ω) (hC : (Set.univ : Set C).Infinite)
    (Ω : Set C) (hΩ : Ω ≠ Set.univ) (g : C → ℝ) (B₀ : ℝ) (hB₀ : ∀ x, g x ≤ B₀)
    (hg : ∀ x ∈ Ω, componentLaplacian C g x = 0) (M : ℝ)
    (hM : ∀ x ∈ outerBoundary C Ω, g x ≤ M) : ∀ x ∈ Ω, g x ≤ M := by
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem Ω).mp hΩ
  intro x hx
  by_contra hlt
  rw [not_le] at hlt
  set K := max (B₀ - M) 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hgap : 0 < g x - M := sub_pos.mpr hlt
  have hden : 0 < 2 * (K + 1) := by linarith
  obtain ⟨B, hBfin, φ, hφ0, hφ1, hφharm, hφx⟩ :=
    hR ω C hC a x ((g x - M) / (2 * (K + 1))) (div_pos hgap hden)
  have key := hF ω C hC (Ω ∩ B) (hBfin.inter_of_right Ω) (fun z => g z - M - K * φ z)
    (fun y hy => by
      rw [componentLaplacian_sub_const_sub_mul, hg y hy.1,
        hφharm y hy.2 (fun hya => ha (hya ▸ hy.1)), mul_zero, sub_zero])
    0 (fun y ⟨hyΩB, z, hz, hyz⟩ => by
      by_cases hyΩ : y ∈ Ω
      · have hyB : y ∉ B := fun hyB => hyΩB ⟨hyΩ, hyB⟩
        have h1 := hφ1 y hyB
        have h2 := hB₀ y
        have h3 : B₀ - M ≤ K := le_max_left _ _
        nlinarith
      · have h1 := hM y ⟨hyΩ, z, hz.1, hyz⟩
        have h2 := mul_nonneg hK0 (hφ0 y)
        linarith)
    x ⟨hx, by_contra fun hxB => by
      have h1 := hφ1 x hxB
      have h2 : (g x - M) / (2 * (K + 1)) < 1 := by
        rw [div_lt_one hden]
        have h3 : B₀ - M ≤ K := le_max_left _ _
        linarith [hB₀ x]
      linarith⟩
  have hdiv : (g x - M) / (2 * (K + 1)) * (2 * (K + 1)) = g x - M := div_mul_cancel₀ _ hden.ne'
  have hKφ : K * φ x ≤ K * ((g x - M) / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hφx hK0
  nlinarith

/-- Lemma 5.16 follows from the uniqueness of the infinite cluster, the finite maximum principle
and the recurrence barrier. -/
theorem strongMaxPrinciple_of_steps {p : unitInterval} (hU : UniqueClusterAe p)
    (hF : FiniteMaxPrinciple) (hR : RecurrenceBarrierStep) : StrongMaxPrincipleStmt p := by
  filter_upwards [hU] with ω h
  refine ⟨h, fun Ω _ hΩ g ⟨B₀, hB₀⟩ hg M hM => ?_⟩
  exact le_of_recurrenceBarrier hF hR _
    (Set.infinite_univ_iff.mpr (Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)))
    Ω hΩ g B₀ (fun x => (le_abs_self _).trans (hB₀ x)) hg M hM

end Rigidity.Steps.Section5

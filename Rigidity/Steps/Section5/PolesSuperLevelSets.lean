import Rigidity.Steps.Section5.Common

/-! # Lemma 5.17: poles of the superlevel sets

Carving of Lemma 5.17 (`PolesSuperLevelSetsStmt`, corrected draft L1981-1986). Let `T` be a
connected component of `{u > a}` containing no pole. Then `u` is harmonic on `T`, and `u ≤ a` on the
outer boundary `∂T`, since a neighbor of `T` in `{u > a}` lies in `T`.

* If `T` is finite, the finite maximum principle (`FiniteMaxPrinciple`) gives `u ≤ a` on `T`.
* If `T` is infinite and `T ≠ 𝒞_∞`, Lemma 5.16 with `Ω = T` gives `u ≤ a` on `T`; `u` is bounded
  since it decays to zero at infinity.
* If `T = 𝒞_∞`, then `u` is harmonic on `𝒞_∞`. For every vertex `b`, Lemma 5.16 with
  `Ω = 𝒞_∞ \ {b}` and `M = u(b)` shows that `u` attains its maximum at `b`; so `u` is constant,
  hence zero since it decays to zero, against the infinite support of `u`.

In each of the first two cases `u ≤ a` contradicts `u > a` on the nonempty set `T`. The
uniqueness of the infinite cluster is not used: Lemma 5.16 provides it. -/

open MeasureTheory LatticeProb.Percolation Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section5

variable {ω : Configuration 2}

/-- A real function decaying to zero along the cofinite filter is bounded. -/
theorem exists_abs_le_of_tendsto_cofinite {α : Type*} {u : α → ℝ}
    (hu : Tendsto u cofinite (𝓝 0)) : ∃ B, ∀ x, |u x| ≤ B := by
  obtain ⟨B, hB⟩ := hu.abs.bddAbove_range_of_cofinite
  exact ⟨B, fun x => hB ⟨x, rfl⟩⟩

/-- On the outer boundary of a connected component of `{u > a}`, `u ≤ a`. -/
theorem le_of_mem_outerBoundary_component {C : OpenComponent ω} {u : C → ℝ} {a : ℝ} {x₀ z : C}
    (hz : z ∈ outerBoundary C {y | JoinedIn C {x | a < u x} x₀ y}) : u z ≤ a := by
  obtain ⟨hzT, y, ⟨hx₀, hy, hr⟩, hzy⟩ := hz
  by_contra hlt
  have hz' : a < u z := lt_of_not_ge hlt
  exact hzT ⟨hx₀, hz', hr.trans
    (SimpleGraph.Adj.reachable (G := (componentGraph C).induce {x | a < u x})
      (u := ⟨y, hy⟩) (v := ⟨z, hz'⟩) hzy.symm)⟩

/-- A function on an infinite component `C`, harmonic on `C`, which satisfies the conclusion of
Lemma 5.16 and decays to zero at infinity, vanishes identically. -/
theorem eq_zero_of_harmonic_of_strongMaxPrinciple {C : OpenComponent ω}
    (hC : (Set.univ : Set C).Infinite)
    (hS : ∀ Ω : Set C, Ω.Infinite → Ω ≠ Set.univ →
      ∀ g : C → ℝ, (∃ B, ∀ x, |g x| ≤ B) → (∀ x ∈ Ω, componentLaplacian C g x = 0) →
      ∀ M : ℝ, (∀ x ∈ outerBoundary C Ω, g x ≤ M) → ∀ x ∈ Ω, g x ≤ M)
    {u : C → ℝ} (hu : Tendsto u cofinite (𝓝 0)) (harm : ∀ x, componentLaplacian C u x = 0) :
    ∀ x, u x = 0 := by
  have hmax : ∀ b y, u y ≤ u b := by
    intro b y
    by_cases hyb : y = b
    · rw [hyb]
    refine hS {b}ᶜ ?_ ?_ u (exists_abs_le_of_tendsto_cofinite hu) (fun x _ => harm x) (u b)
      ?_ y hyb
    · rw [Set.compl_eq_univ_sdiff]
      exact hC.sdiff (Set.finite_singleton b)
    · intro h
      have hb : b ∈ ({b}ᶜ : Set C) := h ▸ Set.mem_univ b
      exact hb rfl
    · intro z hz
      have hzb : z = b := not_not.mp hz.1
      rw [hzb]
  haveI : Infinite C := Set.infinite_univ_iff.mp hC
  intro x
  have hconst : u = fun _ => u x := funext fun y => le_antisymm (hmax x y) (hmax y x)
  rw [hconst] at hu
  exact tendsto_nhds_unique tendsto_const_nhds hu

/-- Lemma 5.17 on a fixed infinite component: from the finite maximum principle and the
conclusion of Lemma 5.16 on `C`, every connected component of `{u > a}` meets a pole. -/
theorem exists_pole_of_isComponentOf (hF : FiniteMaxPrinciple) {C : OpenComponent ω}
    (hC : (Set.univ : Set C).Infinite)
    (hS : ∀ Ω : Set C, Ω.Infinite → Ω ≠ Set.univ →
      ∀ g : C → ℝ, (∃ B, ∀ x, |g x| ≤ B) → (∀ x ∈ Ω, componentLaplacian C g x = 0) →
      ∀ M : ℝ, (∀ x ∈ outerBoundary C Ω, g x ≤ M) → ∀ x ∈ Ω, g x ≤ M)
    {f : Vertex 2 → ℤ} {u : C → ℝ} (hu : IsDecayingPotential C f u)
    (hsupp : (Function.support u).Infinite) (a : ℝ) (T : Set C)
    (hT : IsComponentOf C {x | a < u x} T) : ∃ y ∈ T, f y.val ≠ 0 := by
  obtain ⟨x₀, hx₀, rfl⟩ := hT
  by_contra hno
  push Not at hno
  have harm : ∀ y ∈ {y | JoinedIn C {x | a < u x} x₀ y}, componentLaplacian C u y = 0 := by
    intro y hy
    have h := hu.1 y
    rw [hno y hy, Int.cast_zero] at h
    exact neg_eq_zero.mp h
  have hx₀T : x₀ ∈ {y | JoinedIn C {x | a < u x} x₀ y} := ⟨hx₀, hx₀, SimpleGraph.Reachable.refl _⟩
  have hbd : ∀ z ∈ outerBoundary C {y | JoinedIn C {x | a < u x} x₀ y}, u z ≤ a :=
    fun _ hz => le_of_mem_outerBoundary_component hz
  rcases Set.finite_or_infinite {y | JoinedIn C {x | a < u x} x₀ y} with hfin | hinf
  · exact absurd (hF ω C hC _ hfin u harm a hbd x₀ hx₀T) (not_le.mpr hx₀)
  by_cases huniv : {y | JoinedIn C {x | a < u x} x₀ y} = Set.univ
  · have hzero := eq_zero_of_harmonic_of_strongMaxPrinciple hC hS hu.2
      (fun y => harm y (huniv ▸ Set.mem_univ y))
    exact hsupp (by simp [Function.support, hzero])
  · exact absurd (hS _ hinf huniv u (exists_abs_le_of_tendsto_cofinite hu.2) harm a hbd x₀ hx₀T)
      (not_le.mpr hx₀)

/-- Lemma 5.17 follows from the finite maximum principle and Lemma 5.16. -/
theorem polesSuperLevelSets_of_steps {p : unitInterval} (hF : FiniteMaxPrinciple)
    (h516 : StrongMaxPrincipleStmt p) (f : Vertex 2 → ℤ) : PolesSuperLevelSetsStmt p f := by
  intro _
  filter_upwards [h516] with ω ⟨h, hS⟩
  exact ⟨h, fun u hu hsupp a T hT => exists_pole_of_isComponentOf hF
    (Set.infinite_univ_iff.mpr (Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)))
    hS hu hsupp a T hT⟩

end Rigidity.Steps.Section5

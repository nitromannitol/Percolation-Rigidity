import Rigidity.Percolation.TargetConnectionHarris

/-!
# Infinite components and two-point connections

Positive association and almost-sure uniqueness of an infinite component give
a lower bound for two-point connection probabilities in an arbitrary region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The root has an infinite open component inside the specified vertex region. -/
def infiniteOpenInEvent {d : ℕ} (B : Set (Vertex d)) (x : Vertex d) : Set (Configuration d) :=
  {ω | {y | y ∈ B ∧ (openIn ω B).Reachable x y}.Infinite}

/-- An infinite component escapes every finite vertex set. -/
theorem mem_infiniteOpenInEvent_iff {d : ℕ} (B : Set (Vertex d)) (x : Vertex d)
    (ω : Configuration d) : ω ∈ infiniteOpenInEvent B x ↔
      ∀ s : Finset (Vertex d), ∃ y ∈ B, y ∉ s ∧ (openIn ω B).Reachable x y := by
  classical
  constructor
  · intro h s
    obtain ⟨y, hy, hys⟩ := h.exists_notMem_finset s
    exact ⟨y, hy.1, hys, hy.2⟩
  · intro h hf
    obtain ⟨y, hyB, hy, hr⟩ := h hf.toFinset
    exact hy (hf.mem_toFinset.mpr ⟨hyB, hr⟩)

/-- Existence of an infinite open component in a fixed region is measurable. -/
theorem measurableSet_infiniteOpenInEvent {d : ℕ} (B : Set (Vertex d)) (x : Vertex d) :
    MeasurableSet (infiniteOpenInEvent B x) := by
  have heq : infiniteOpenInEvent B x = ⋂ s : Finset (Vertex d),
      ⋃ y : Vertex d, {ω | y ∈ B ∧ y ∉ s ∧ (openIn ω B).Reachable x y} := by
    ext ω
    simp only [mem_infiniteOpenInEvent_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [heq]
  exact MeasurableSet.iInter fun s => MeasurableSet.iUnion fun y =>
    (MeasurableSet.const (y ∈ B)).inter
      ((MeasurableSet.const (y ∉ s)).inter (measurableSet_openIn_reachable B x y))

/-- Opening bonds preserves infinitude of a component in the region. -/
theorem isUpperSet_infiniteOpenInEvent {d : ℕ} (B : Set (Vertex d)) (x : Vertex d) :
    IsUpperSet (infiniteOpenInEvent B x) := by
  intro ω η hωη hω
  rw [mem_infiniteOpenInEvent_iff] at hω ⊢
  intro s
  obtain ⟨y, hyB, hys, hxy⟩ := hω s
  exact ⟨y, hyB, hys, hxy.mono (openIn_mono_configuration hωη B)⟩

/-- If all infinite open components in a region coincide almost surely, the
probability of a connection between two roots is at least the product of their
infinite-component probabilities. -/
theorem mul_measureReal_infiniteOpenIn_le_reachable {d : ℕ} (p : unitInterval)
    (B : Set (Vertex d)) (x y : Vertex d)
    (hunique : ∀ᵐ ω ∂(latticeBondLaw d p),
      ω ∈ infiniteOpenInEvent B x → ω ∈ infiniteOpenInEvent B y →
        (openIn ω B).Reachable x y) :
    (latticeBondLaw d p).real (infiniteOpenInEvent B x) *
      (latticeBondLaw d p).real (infiniteOpenInEvent B y) ≤
      (latticeBondLaw d p).real {ω | (openIn ω B).Reachable x y} := by
  calc
    _ ≤ (latticeBondLaw d p).real (infiniteOpenInEvent B x ∩ infiniteOpenInEvent B y) :=
      LatticeProb.infinitePi_harris_bool (fun _ : Bond d => bernoulliMeasure true false p)
        (isUpperSet_infiniteOpenInEvent B x) (isUpperSet_infiniteOpenInEvent B y)
        (measurableSet_infiniteOpenInEvent B x) (measurableSet_infiniteOpenInEvent B y)
    _ ≤ _ := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [hunique] with ω hω hmem
      exact hω hmem.1 hmem.2

/-- A uniform positive lower bound for infinite-component probabilities and
almost-sure uniqueness imply a uniform two-point lower bound. -/
theorem sq_le_measureReal_reachable_of_infiniteOpenIn {d : ℕ} (p : unitInterval)
    (B : Set (Vertex d)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hθ : ∀ x ∈ B, ρ ≤ (latticeBondLaw d p).real (infiniteOpenInEvent B x))
    (hunique : ∀ᵐ ω ∂(latticeBondLaw d p), ∀ x ∈ B, ∀ y ∈ B,
      ω ∈ infiniteOpenInEvent B x → ω ∈ infiniteOpenInEvent B y →
        (openIn ω B).Reachable x y) :
    ∀ x ∈ B, ∀ y ∈ B, ρ ^ 2 ≤
      (latticeBondLaw d p).real {ω | (openIn ω B).Reachable x y} := by
  intro x hx y hy
  calc
    ρ ^ 2 ≤ (latticeBondLaw d p).real (infiniteOpenInEvent B x) *
        (latticeBondLaw d p).real (infiniteOpenInEvent B y) := by
      rw [pow_two]
      exact mul_le_mul (hθ x hx) (hθ y hy) hρ measureReal_nonneg
    _ ≤ _ := mul_measureReal_infiniteOpenIn_le_reachable p B x y
      (hunique.mono fun ω hω => hω x hx y hy)

end Rigidity.Percolation

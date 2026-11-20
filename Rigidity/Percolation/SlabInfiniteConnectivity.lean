import Rigidity.Percolation.TargetConnectionHarris

/-!
# Infinite components and two-point connections

Positive association and almost-sure uniqueness of an infinite component give
a lower bound for two-point connection probabilities in an arbitrary region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

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

/-- A finite path in an increasing union of vertex regions is contained in
one of the regions. -/
theorem reachable_openIn_iUnion_iff {d : ℕ} (B : ℕ → Set (Vertex d))
    (hB : Monotone B) (ω : Configuration d) (x y : Vertex d) :
    (openIn ω (⋃ n, B n)).Reachable x y ↔ ∃ n, (openIn ω (B n)).Reachable x y := by
  constructor
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact ⟨0, SimpleGraph.Reachable.refl _⟩
    | @cons u v w huv walk ih =>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp huv.2.1
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp huv.2.2
      obtain ⟨k, hk⟩ := ih
      let m := max (max i j) k
      have hu : u ∈ B m := hB (le_trans (le_max_left i j) (le_max_left _ _)) hi
      have hv : v ∈ B m := hB (le_trans (le_max_right i j) (le_max_left _ _)) hj
      have hstep : (openIn ω (B m)).Adj u v := ⟨huv.1, hu, hv⟩
      have htail : (openIn ω (B m)).Reachable v w := by
        apply hk.mono
        intro a b hab
        exact ⟨hab.1, hB (le_max_right _ _) hab.2.1, hB (le_max_right _ _) hab.2.2⟩
      exact ⟨m, hstep.reachable.trans htail⟩
  · rintro ⟨n, hn⟩
    apply hn.mono
    intro a b hab
    exact ⟨hab.1, Set.mem_iUnion.mpr ⟨n, hab.2.1⟩,
      Set.mem_iUnion.mpr ⟨n, hab.2.2⟩⟩

/-- Two-point probabilities in increasing regions converge to the corresponding
probability in their union. -/
theorem tendsto_measureReal_reachable_openIn_iUnion {d : ℕ} (p : unitInterval)
    (B : ℕ → Set (Vertex d)) (hB : Monotone B) (x y : Vertex d) :
    Tendsto (fun n => (latticeBondLaw d p).real {ω | (openIn ω (B n)).Reachable x y})
      atTop (𝓝 ((latticeBondLaw d p).real {ω | (openIn ω (⋃ n, B n)).Reachable x y})) := by
  let E : ℕ → Set (Configuration d) := fun n => {ω | (openIn ω (B n)).Reachable x y}
  have hE : Monotone E := by
    intro n m hnm ω hω
    apply hω.mono
    intro a b hab
    exact ⟨hab.1, hB hnm hab.2.1, hB hnm hab.2.2⟩
  have heq : (⋃ n, E n) = {ω | (openIn ω (⋃ n, B n)).Reachable x y} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, E, reachable_openIn_iUnion_iff B hB]
  have hlim := tendsto_measure_iUnion_atTop (μ := latticeBondLaw d p) hE
  rw [heq] at hlim
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim

/-- For a fixed finite set of roots, a uniform infinite-region bound transfers
to all sufficiently large regions in an increasing exhaustion. -/
theorem eventually_uniform_finite_reachable_of_infiniteOpenIn {d : ℕ} (p : unitInterval)
    (B : ℕ → Set (Vertex d)) (hB : Monotone B) (A : Finset (Vertex d))
    (hA : (↑A : Set (Vertex d)) ⊆ ⋃ n, B n) (ρ δ : ℝ) (hρ : 0 ≤ ρ) (hδ : δ < ρ ^ 2)
    (hθ : ∀ x ∈ ⋃ n, B n, ρ ≤
      (latticeBondLaw d p).real (infiniteOpenInEvent (⋃ n, B n) x))
    (hunique : ∀ᵐ ω ∂(latticeBondLaw d p), ∀ x ∈ ⋃ n, B n, ∀ y ∈ ⋃ n, B n,
      ω ∈ infiniteOpenInEvent (⋃ n, B n) x → ω ∈ infiniteOpenInEvent (⋃ n, B n) y →
        (openIn ω (⋃ n, B n)).Reachable x y) :
    ∀ᶠ n in atTop, ∀ x ∈ A, ∀ y ∈ A, δ ≤
      (latticeBondLaw d p).real {ω | (openIn ω (B n)).Reachable x y} := by
  apply (eventually_all_finset A).mpr
  intro x hx
  apply (eventually_all_finset A).mpr
  intro y hy
  have hlimit := tendsto_measureReal_reachable_openIn_iUnion p B hB x y
  have hlower := sq_le_measureReal_reachable_of_infiniteOpenIn p (⋃ n, B n)
    ρ hρ hθ hunique x (hA hx) y (hA hy)
  exact (hlimit.eventually (eventually_gt_nhds (lt_of_lt_of_le hδ hlower))).mono
    (fun _ h => le_of_lt h)

end Rigidity.Percolation

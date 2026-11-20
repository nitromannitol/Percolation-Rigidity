import Rigidity.Percolation.BondFaceContactSelection

/-!
# Random face contacts and seed trials

A base-measurable finite set of sufficiently many face contacts supplies
independent added-layer trials with a geometric success bound.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped MeasureTheory

/-- A sufficiently large base-measurable contact set gives a conditional lower
bound on the probability of at least one open outward face-seed trial. -/
theorem condExp_indicator_lower_of_random_face_contacts {d k m : ℕ} (hk : 0 < k)
    (q r : unitInterval) (j : Fin d) (n : ℤ)
    (S : (Bond d → Bool × Bool) → Finset (Vertex d))
    (hS : @Measurable _ _ (baseBondSigma d) _ S)
    {G C : Set (Bond d → Bool × Bool)} (hG : MeasurableSet G)
    (hC : MeasurableSet C)
    (hface : ∀ ω ∈ G, ∀ x ∈ S ω, x j = n)
    (hcard : ∀ ω ∈ G, m * k ^ d ≤ (S ω).card)
    (hsubset : ∀ ω, ∀ x ∈ S ω,
      addedBondConfiguration ω ∈ fullyOpenRegion (faceSeedTrial k j n x) → ω ∈ C) :
    ∀ᵐ ω ∂(bondPairLaw d q r).restrict G,
      1 - (1 - (r : ℝ) ^ ((k ^ d + 1) ^ 2)) ^ m ≤
        (bondPairLaw d q r)[C.indicator (fun _ => (1 : ℝ)) | baseBondSigma d] ω := by
  classical
  let ι := {s : Finset (Vertex d) // (∀ x ∈ s, x j = n) ∧ m * k ^ d ≤ s.card}
  have hchoose (a : ι) : ∃ x : Fin m → Vertex d, (∀ t, x t ∈ a.val) ∧
      Function.Injective (fun t => seedGridIndex k (x t)) :=
    exists_contacts_distinct_seedGridIndex hk a.val a.property.2
  let x : ι → Fin m → Vertex d := fun a => Classical.choose (hchoose a)
  have hx (a : ι) : (∀ t, x a t ∈ a.val) ∧
      Function.Injective (fun t => seedGridIndex k (x a t)) := Classical.choose_spec (hchoose a)
  let A : ι → Set (Bond d → Bool × Bool) := fun a => S ⁻¹' {a.val}
  apply condExp_indicator_lower_of_base_faceSeedTrials hk q r m j n x
    (fun a t => a.property.1 _ ((hx a).1 t)) (fun a => (hx a).2) A
    (fun a => hS (measurableSet_singleton a.val)) hG hC
  · intro ω hω
    let a : ι := ⟨S ω, hface ω hω, hcard ω hω⟩
    exact Set.mem_iUnion.mpr ⟨a, rfl⟩
  · intro a ω hω
    rcases hω with ⟨hA, htrial⟩
    rcases Set.mem_iUnion.mp htrial with ⟨t, ht⟩
    have hmem : x a t ∈ S ω := by
      change S ω = a.val at hA
      rw [hA]
      exact (hx a).1 t
    exact hsubset ω _ hmem ht

end Rigidity.Percolation

import Rigidity.Percolation.BondReachableFaceContacts

/-!
# Face contacts reached from a finite seed

The set of vertices reached from a finite starting set is measurable and can
be used to select outward bond-seed trials.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped MeasureTheory

/-- Face vertices connected to at least one vertex of a finite starting set. -/
noncomputable def seedReachableContacts {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (ω : Configuration d) : Finset (Vertex d) := by
  classical
  exact face.filter (fun x => ∃ y ∈ roots, (openIn ω B).Reachable y x)

/-- Membership in the contact set means connection to one of the roots. -/
theorem mem_seedReachableContacts {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (ω : Configuration d) (x : Vertex d) :
    x ∈ seedReachableContacts B roots face ω ↔
      x ∈ face ∧ ∃ y ∈ roots, (openIn ω B).Reachable y x := by
  classical
  simp [seedReachableContacts]

/-- The finite contact set is measurable. -/
theorem measurable_seedReachableContacts {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) : Measurable (seedReachableContacts B roots face) := by
  classical
  apply measurable_finset_iff.mpr
  intro x
  have hy : MeasurableSet {ω : Configuration d | ∃ y ∈ roots,
      (openIn ω B).Reachable y x} := by
    have heq : {ω : Configuration d | ∃ y ∈ roots, (openIn ω B).Reachable y x} =
        ⋃ y ∈ roots, {ω | (openIn ω B).Reachable y x} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ =>
      measurableSet_openIn_reachable B y x
  simpa only [mem_seedReachableContacts] using
    (measurable_const.and (measurableSet_setOf.mp hy))

/-- The contacts are measurable with respect to the base field. -/
theorem measurable_base_seedReachableContacts {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) :
    @Measurable _ _ (baseBondSigma d) _
      (fun ω => seedReachableContacts B roots face (baseBondConfiguration ω)) :=
  (measurable_seedReachableContacts B roots face).comp (comap_measurable _)

/-- A contact reached from the starting set has an open outward trial. -/
def seedReachableFaceSuccess {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (k : ℕ) (j : Fin d) (n : ℤ) :
    Set (Bond d → Bool × Bool) :=
  ⋃ y ∈ roots, reachableFaceSeedSuccess B y face k j n

/-- The seed-to-face trial success event is measurable. -/
theorem measurableSet_seedReachableFaceSuccess {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (k : ℕ) (j : Fin d) (n : ℤ) :
    MeasurableSet (seedReachableFaceSuccess B roots face k j n) :=
  MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ =>
    measurableSet_reachableFaceSeedSuccess B y face k j n

/-- A sufficiently large set of face contacts reached from a finite seed gives
an explicit conditional success bound for an outward seed trial. -/
theorem condExp_indicator_lower_of_seed_face_contacts {d k m : ℕ} (hk : 0 < k)
    (q r : unitInterval) (B : Set (Vertex d)) (roots face : Finset (Vertex d))
    (j : Fin d) (n : ℤ) (hface : ∀ x ∈ face, x j = n)
    {G : Set (Bond d → Bool × Bool)} (hG : MeasurableSet G)
    (hcard : ∀ ω ∈ G, m * k ^ d ≤
      (seedReachableContacts B roots face (baseBondConfiguration ω)).card) :
    ∀ᵐ ω ∂(bondPairLaw d q r).restrict G,
      1 - (1 - (r : ℝ) ^ ((k ^ d + 1) ^ 2)) ^ m ≤
        (bondPairLaw d q r)[(seedReachableFaceSuccess B roots face k j n).indicator
          (fun _ => (1 : ℝ)) | baseBondSigma d] ω := by
  apply condExp_indicator_lower_of_random_face_contacts hk q r j n
    (fun ω => seedReachableContacts B roots face (baseBondConfiguration ω))
    (measurable_base_seedReachableContacts B roots face) hG
    (measurableSet_seedReachableFaceSuccess B roots face k j n)
    (fun ω _ x hx => hface x ((mem_seedReachableContacts B roots face _ x).mp hx).1) hcard
  intro ω x hx hopen
  obtain ⟨hxf, y, hyr, hreach⟩ := (mem_seedReachableContacts B roots face _ x).mp hx
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyr, x, hxf, hreach, hopen⟩⟩

end Rigidity.Percolation

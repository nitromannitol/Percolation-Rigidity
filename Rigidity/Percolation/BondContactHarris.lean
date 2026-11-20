import Rigidity.Percolation.InfiniteSeedBoundaryDecay

/-!
# Positive association of small contact sets

A finite collection of boundary pieces with few reached vertices is
positively associated under Bernoulli bond percolation. If the pieces cover
the boundary, their simultaneous occurrence bounds the total contact count.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The event that fewer than `m` vertices of a face are reached from a seed. -/
def fewSeedContacts {d : ℕ} (B : Set (Vertex d)) (roots face : Finset (Vertex d))
    (m : ℕ) : Set (Configuration d) :=
  {ω | (seedReachableContacts B roots face ω).card < m}

/-- A small-contact event is measurable. -/
theorem measurableSet_fewSeedContacts {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (m : ℕ) :
    MeasurableSet (fewSeedContacts B roots face m) := by
  have hcount : Measurable (fun ω => (seedReachableContacts B roots face ω).card) :=
    (measurable_of_countable Finset.card).comp (measurable_seedReachableContacts B roots face)
  exact hcount (Set.to_countable {k : ℕ | k < m}).measurableSet

/-- Closing bonds cannot increase the number of reached contacts. -/
theorem isLowerSet_fewSeedContacts {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (m : ℕ) : IsLowerSet (fewSeedContacts B roots face m) := by
  intro η ω hωη hη
  change (seedReachableContacts B roots face ω).card < m
  apply lt_of_le_of_lt (Finset.card_le_card ?_) hη
  intro x hx
  obtain ⟨hface, y, hy, hreach⟩ := (mem_seedReachableContacts B roots face ω x).mp hx
  exact (mem_seedReachableContacts B roots face η x).mpr
    ⟨hface, y, hy, hreach.mono (openIn_mono_configuration hωη B)⟩

/-- The product of the probabilities of finitely many small-contact events is
at most the probability of their intersection. -/
theorem prod_measureReal_fewSeedContacts_le {d : ℕ} {ι : Type*} (p : unitInterval)
    (B : Set (Vertex d)) (roots : Finset (Vertex d)) (face : ι → Finset (Vertex d))
    (m : ℕ) (s : Finset ι) :
    (∏ i ∈ s, (latticeBondLaw d p).real (fewSeedContacts B roots (face i) m)) ≤
      (latticeBondLaw d p).real (⋂ i ∈ s, fewSeedContacts B roots (face i) m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.set_biInter_insert]
    calc
      _ ≤ (latticeBondLaw d p).real (fewSeedContacts B roots (face i) m) *
          (latticeBondLaw d p).real (⋂ j ∈ s, fewSeedContacts B roots (face j) m) :=
        mul_le_mul_of_nonneg_left ih measureReal_nonneg
      _ ≤ _ :=
        LatticeProb.infinitePi_harris_bool_lower
          (fun _ : Bond d => bernoulliMeasure true false p)
          (isLowerSet_fewSeedContacts B roots (face i) m)
          (isLowerSet_iInter₂ fun j _ => isLowerSet_fewSeedContacts B roots (face j) m)
          (measurableSet_fewSeedContacts B roots (face i) m)
          (s.measurableSet_biInter fun j _ => measurableSet_fewSeedContacts B roots (face j) m)

/-- If nonempty finitely many pieces cover a face and each has fewer than `m`
contacts, the whole face has fewer than the number of pieces times `m`. -/
theorem iInter_fewSeedContacts_subset {d : ℕ} {ι : Type*} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (pieces : ι → Finset (Vertex d))
    (m : ℕ) (s : Finset ι) (hs : s.Nonempty)
    (hcover : face ⊆ s.biUnion pieces) :
    (⋂ i ∈ s, fewSeedContacts B roots (pieces i) m) ⊆
      fewSeedContacts B roots face (s.card * m) := by
  classical
  intro ω hω
  simp only [Set.mem_iInter] at hω
  change (seedReachableContacts B roots face ω).card < s.card * m
  have hsub : seedReachableContacts B roots face ω ⊆
      s.biUnion (fun i => seedReachableContacts B roots (pieces i) ω) := by
    intro x hx
    obtain ⟨hface, y, hy, hreach⟩ := (mem_seedReachableContacts B roots face ω x).mp hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hcover hface)
    exact Finset.mem_biUnion.mpr ⟨i, hi,
      (mem_seedReachableContacts B roots (pieces i) ω x).mpr ⟨hxi, y, hy, hreach⟩⟩
  have hm : 0 < m := by
    obtain ⟨i, hi⟩ := hs
    exact lt_of_le_of_lt (Nat.zero_le _) (hω i hi)
  have hbound : (seedReachableContacts B roots face ω).card ≤ s.card * (m - 1) := by
    calc
      _ ≤ (s.biUnion (fun i => seedReachableContacts B roots (pieces i) ω)).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ i ∈ s, (seedReachableContacts B roots (pieces i) ω).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ s, (m - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := hω i hi
        change (seedReachableContacts B roots (pieces i) ω).card < m at h
        omega
      _ = s.card * (m - 1) := by simp
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  have heq : s.card * m = s.card * (m - 1) + s.card := by
    have : m - 1 + 1 = m := by omega
    conv_lhs => rw [← this, Nat.mul_add]
    simp only [Nat.mul_one]
  omega

/-- Equal small-contact probabilities on a finite cover satisfy the
boundary-to-piece inequality. -/
theorem pow_measureReal_fewSeedContacts_le {d : ℕ} {ι : Type*} (p : unitInterval)
    (B : Set (Vertex d)) (roots face : Finset (Vertex d))
    (pieces : ι → Finset (Vertex d)) (m : ℕ) (s : Finset ι) (hs : s.Nonempty)
    (hcover : face ⊆ s.biUnion pieces) (i₀ : ι)
    (heq : ∀ i ∈ s, (latticeBondLaw d p).real (fewSeedContacts B roots (pieces i) m) =
      (latticeBondLaw d p).real (fewSeedContacts B roots (pieces i₀) m)) :
    (latticeBondLaw d p).real (fewSeedContacts B roots (pieces i₀) m) ^ s.card ≤
      (latticeBondLaw d p).real (fewSeedContacts B roots face (s.card * m)) := by
  classical
  calc
    _ = ∏ i ∈ s, (latticeBondLaw d p).real (fewSeedContacts B roots (pieces i) m) := by
      rw [← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro i hi
      exact (heq i hi).symm
    _ ≤ (latticeBondLaw d p).real (⋂ i ∈ s, fewSeedContacts B roots (pieces i) m) :=
      prod_measureReal_fewSeedContacts_le p B roots pieces m s
    _ ≤ _ := measureReal_mono (iInter_fewSeedContacts_subset B roots face pieces m s hs hcover)
      (measure_ne_top _ _)

end Rigidity.Percolation

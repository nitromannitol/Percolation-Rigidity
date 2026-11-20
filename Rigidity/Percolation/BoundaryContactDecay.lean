import Rigidity.Percolation.ExtinctionProbability

/-!
# Decay of small nonempty boundary contact sets

For nested survival events, finite energy and disjoint successive extinctions
show that a fixed finite number of nonempty reached boundary contacts becomes
unlikely.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology ENNReal

/-- Nonempty reached contacts in a sequence of finite regions. -/
def seedBoundarySurvival {d : ℕ} (P : ℕ → Set (Vertex d))
    (roots : Finset (Vertex d)) (face : ℕ → Finset (Vertex d)) (n : ℕ) :
    Set (Configuration d) :=
  {ω | seedReachableContacts (P n) roots (face n) ω ≠ ∅}

/-- Reached-contact survival is measurable. -/
theorem measurableSet_seedBoundarySurvival {d : ℕ} (P : ℕ → Set (Vertex d))
    (roots : Finset (Vertex d)) (face : ℕ → Finset (Vertex d)) (n : ℕ) :
    MeasurableSet (seedBoundarySurvival P roots face n) := by
  have h := (measurable_seedReachableContacts (P n) roots (face n))
    (measurableSet_singleton (∅ : Finset (Vertex d)))
  exact h.compl

/-- If each next face lies outside the current region, every path to it
first reaches the current boundary. -/
theorem antitone_seedBoundarySurvival {d : ℕ} (P : ℕ → Set (Vertex d))
    (roots : Finset (Vertex d)) (face : ℕ → Finset (Vertex d))
    (hroots : ∀ n z, z ∈ roots → z ∈ P n)
    (hface : ∀ n x, x ∈ P n → ∀ y, y ∉ P n →
      (nearestNeighborGraph d).Adj x y → x ∈ face n)
    (houter : ∀ n w, w ∈ face (n + 1) → w ∉ P n) :
    Antitone (seedBoundarySurvival P roots face) := by
  classical
  apply antitone_nat_of_succ_le
  intro n ω hω
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hω
  obtain ⟨hwface, z, hz, hzw⟩ := (mem_seedReachableContacts _ _ _ _ _).mp hw
  have hdisj : Disjoint (P n) (P n)ᶜ := by
    rw [Set.disjoint_left]
    intro x hx hxnot
    exact hxnot hx
  have hcover : P (n + 1) ⊆ P n ∪ (P n)ᶜ := by simp only [Set.union_compl_self, Set.subset_univ]
  obtain ⟨x, hx, y, hy, hxy, hzx, _⟩ :=
    exists_slab_attachment_of_reachable hdisj hcover (hroots n z hz) (houter n w hwface) hzw
  apply Finset.nonempty_iff_ne_empty.mp
  exact ⟨x, (mem_seedReachableContacts _ _ _ _ _).mpr ⟨hface n x hx y hy hxy, z, hz, hzx⟩⟩

/-- The probability of any locally measurable event with at most `m`
nonempty reached contacts tends to zero when the survival events decrease
and the next boundary lies outside the present region. -/
theorem tendsto_measure_small_seed_boundary {d : ℕ} (p : unitInterval) (hp : (p : ℝ) < 1)
    (P : ℕ → Set (Vertex d)) (roots : Finset (Vertex d))
    (face : ℕ → Finset (Vertex d)) (A : ℕ → Set (Configuration d)) (m : ℕ)
    (hP : ∀ n, (P n).Finite) (hroots : ∀ n z, z ∈ roots → z ∈ P n)
    (hfaceP : ∀ n x, x ∈ face n → x ∈ P n)
    (hface : ∀ n x, x ∈ P n → ∀ y, y ∉ P n →
      (nearestNeighborGraph d).Adj x y → x ∈ face n)
    (houter : ∀ n w, w ∈ face (n + 1) → w ∉ P n)
    (hanti : Antitone (seedBoundarySurvival P roots face))
    (hA : ∀ n, MeasurableSet[bondSigma (localBonds (P n))] (A n))
    (hAne : ∀ n, A n ⊆ seedBoundarySurvival P roots face n)
    (hcard : ∀ n ω, ω ∈ A n → (seedReachableContacts (P n) roots (face n) ω).card ≤ m) :
    Tendsto (fun n => latticeBondLaw d p (A n)) atTop (𝓝 0) := by
  let c := ENNReal.ofReal ((1 - (p : ℝ)) ^ (m * (2 * d)))
  have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (sub_pos.mpr hp) _)
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  apply tendsto_measure_of_extinction_cost (latticeBondLaw d p)
    (seedBoundarySurvival P roots face) A
    (measurableSet_seedBoundarySurvival P roots face) hanti c hc0 hct
  intro n
  have hcost := finiteEnergy_seed_extinction_lattice (D := P (n + 1)) p roots
    (face n) (face (n + 1))
    (hP n) (hroots n) (hfaceP n) (hface n) (houter n) m (hA n) (hcard n)
  refine hcost.trans (measure_mono ?_)
  intro ω hω
  exact ⟨hAne n hω.1, fun hsurv => hsurv hω.2⟩

/-- A fixed positive number of reached boundary contacts becomes unlikely
for finite regions whose next boundary lies outside the present region. -/
theorem tendsto_measure_bounded_seed_contacts {d : ℕ} (p : unitInterval) (hp : (p : ℝ) < 1)
    (P : ℕ → Set (Vertex d)) (roots : Finset (Vertex d))
    (face : ℕ → Finset (Vertex d)) (m : ℕ)
    (hP : ∀ n, (P n).Finite) (hroots : ∀ n z, z ∈ roots → z ∈ P n)
    (hfaceP : ∀ n x, x ∈ face n → x ∈ P n)
    (hface : ∀ n x, x ∈ P n → ∀ y, y ∉ P n →
      (nearestNeighborGraph d).Adj x y → x ∈ face n)
    (houter : ∀ n w, w ∈ face (n + 1) → w ∉ P n) :
    Tendsto (fun n => latticeBondLaw d p {ω |
      0 < (seedReachableContacts (P n) roots (face n) ω).card ∧
        (seedReachableContacts (P n) roots (face n) ω).card ≤ m}) atTop (𝓝 0) := by
  classical
  let A : ℕ → Set (Configuration d) := fun n => {ω |
    0 < (seedReachableContacts (P n) roots (face n) ω).card ∧
      (seedReachableContacts (P n) roots (face n) ω).card ≤ m}
  apply tendsto_measure_small_seed_boundary p hp P roots face A m hP hroots hfaceP hface houter
    (antitone_seedBoundarySurvival P roots face hroots hface houter)
  · intro n
    letI : MeasurableSpace (Configuration d) := bondSigma (localBonds (P n))
    have hm := measurable_seedReachableContacts_local (P n) roots (face n) (hP n)
      (hroots n) (hfaceP n)
    have hcount : Measurable (fun ω => (seedReachableContacts (P n) roots (face n) ω).card) :=
      (measurable_of_countable Finset.card).comp hm
    exact hcount (Set.to_countable {k : ℕ | 0 < k ∧ k ≤ m}).measurableSet
  · intro n ω hω
    exact Finset.card_pos.mp hω.1 |>.ne_empty
  · intro n ω hω
    exact hω.2

end Rigidity.Percolation

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

end Rigidity.Percolation

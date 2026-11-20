import Rigidity.Percolation.TriadicInfluenceProbability
import Rigidity.Percolation.TriadicStoppingNeighbors
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost-sure coverage by stable cubes

A summable tail bound for bad cubes gives stable cubes at all sufficiently large
scales around every lattice point, and hence a partition into stopping cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- Summability of the per-scale bad-cube tails gives eventual stable coverage at
all scales and all lattice points simultaneously. -/
theorem TriadicCube.ae_eventually_stable_coverage {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (p : ℕ → ℝ≥0∞) (hprob : ∀ R : TriadicCube d, μ {ω | R ∉ G ω} ≤ p R.scale)
    (hsum : (∑' n : ℕ, ∑' m : ℕ, (19 ^ d : ℝ≥0∞) * p (n + m)) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ x : Vertex d, ∃ N : ℕ, ∀ n ≥ N,
      ∃ Q : TriadicCube d, Q.scale = n ∧ x ∈ Q.vertices ∧ Q ∈ stableGood (G ω) := by
  classical
  let cube : Vertex d → ℕ → TriadicCube d := fun x n =>
    Classical.choose (existsUnique_mem d n x).exists
  have hcube (x : Vertex d) (n : ℕ) : (cube x n).scale = n ∧ x ∈ (cube x n).vertices :=
    Classical.choose_spec (existsUnique_mem d n x).exists
  apply ae_all_iff.mpr
  intro x
  have hfinite : (∑' n : ℕ, μ {ω | cube x n ∉ stableGood (G ω)}) ≠ ∞ := by
    apply ne_top_of_le_ne_top hsum
    apply ENNReal.tsum_le_tsum
    intro n
    simpa only [(hcube x n).1] using measure_not_mem_stableGood_le μ G p hprob (cube x n)
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hω
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨cube x n, (hcube x n).1, (hcube x n).2, Classical.not_not.mp (hN n hn)⟩

/-- Under the summable-tail hypothesis, maximal stopping cubes partition the
lattice almost surely. -/
theorem TriadicCube.ae_existsUnique_maximal_stopping {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (p : ℕ → ℝ≥0∞) (hprob : ∀ R : TriadicCube d, μ {ω | R ∉ G ω} ≤ p R.scale)
    (hsum : (∑' n : ℕ, ∑' m : ℕ, (19 ^ d : ℝ≥0∞) * p (n + m)) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω) := by
  filter_upwards [ae_eventually_stable_coverage μ G p hprob hsum] with ω hω
  intro x
  obtain ⟨N, hN⟩ := hω x
  obtain ⟨Q, _, hx, hQ⟩ := hN N le_rfl
  exact existsUnique_isMaximalStopping_of_mem_stableGood hQ hx

end Rigidity.Percolation

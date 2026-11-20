import Rigidity.Percolation.SlabTwoAttachments

/-!
# Decay for two-component slab exploration

A nested exploration survives each step only if two explored components
remain disconnected. Fresh boundary bonds and a uniform slab two-point bound
then give geometric decay of the survival probability.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped MeasureTheory

/-- Two-component exploration decays geometrically when each past event
reaches a pair of distinct fresh boundary bonds and connecting the components
precludes survival at the next step. -/
theorem measureReal_le_pow_of_two_component_slab_exploration {d : ℕ} {ι : Type*}
    [Countable ι] (p : unitInterval) (P S D : ℕ → Set (Vertex d))
    (hP : ∀ n, (P n).Finite) (hS : ∀ n, (S n).Finite)
    (hPS : ∀ n, Disjoint (P n) (S n))
    (hPD : ∀ n, P n ⊆ D n) (hSD : ∀ n, S n ⊆ D n)
    (z z' : Vertex d) (hz : ∀ n, z ∈ P n) (hz' : ∀ n, z' ∈ P n)
    (x y x' y' : ℕ → ι → Vertex d)
    (hx : ∀ n i, x n i ∈ P n) (hy : ∀ n i, y n i ∈ S n)
    (hx' : ∀ n i, x' n i ∈ P n) (hy' : ∀ n i, y' n i ∈ S n)
    (hxy : ∀ n i, (nearestNeighborGraph d).Adj (x n i) (y n i))
    (hx'y' : ∀ n i, (nearestNeighborGraph d).Adj (x' n i) (y' n i))
    (hne : ∀ n i, bondOfAdjacent (hxy n i) ≠ bondOfAdjacent (hx'y' n i))
    (δ : ℝ) (hδ₁ : δ ≤ 1)
    (hprob : ∀ n i, δ ≤ (latticeBondLaw d p).real
      {ω | (openIn ω (S n)).Reachable (y n i) (y' n i)})
    (G : ℕ → Set (Configuration d))
    (hG : ∀ n, MeasurableSet[bondSigma (localBonds (P n))] (G n))
    (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hcover : ∀ n, G n ⊆ ⋃ i,
      ({ω | (openIn ω (P n)).Reachable z (x n i)} ∩
        {ω | (openIn ω (P n)).Reachable z' (x' n i)}))
    (hdisj : ∀ n, Disjoint (G (n + 1)) {ω | (openIn ω (D n)).Reachable z z'}) :
    ∀ n, (latticeBondLaw d p).real (G n) ≤
      (1 - (p : ℝ) * ((p : ℝ) * δ)) ^ n := by
  have hfirst : (p : ℝ) * δ ≤ 1 := by
    calc
      (p : ℝ) * δ ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hδ₁ p.property.1
      _ ≤ 1 := by simpa using p.property.2
  have hsecond : (p : ℝ) * ((p : ℝ) * δ) ≤ 1 := by
    calc
      (p : ℝ) * ((p : ℝ) * δ) ≤ (p : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hfirst p.property.1
      _ ≤ 1 := by simpa using p.property.2
  apply measureReal_le_pow_one_sub_of_condExp_success (latticeBondLaw d p)
    (fun n => bondSigma (localBonds (P n))) (fun n => bondSigma_le _)
    G (fun n => {ω | (openIn ω (D n)).Reachable z z'}) hG
    (fun n => measurableSet_openIn_reachable (D n) z z') hdecr hdisj
    ((p : ℝ) * ((p : ℝ) * δ)) hsecond
  intro n
  apply ae_restrict_of_ae_restrict_of_subset (hcover n)
  exact condExp_reachable_lower_of_two_slab_attachments p (P n) (S n) (D n)
    (hP n) (hS n) (hPS n) (hPD n) (hSD n) z z' (hz n) (hz' n)
    (x n) (y n) (x' n) (y' n) (hx n) (hy n) (hx' n) (hy' n)
    (hxy n) (hx'y' n) (hne n) δ (hprob n)

end Rigidity.Percolation

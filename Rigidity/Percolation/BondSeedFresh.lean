import PercolationClusterHomogenization.Percolation.BondSeedExploration

/-!
# Fresh bond seeds

A seed region selected using previously revealed bonds retains its uniform
opening probability when its internal bonds are fresh. Repeated such tests
produce a geometric survival bound.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped MeasureTheory

/-- A past-measurable choice of a uniformly bounded fresh seed has the
corresponding lower bound on its conditional probability of opening. -/
theorem condExp_indicator_lower_of_fresh_seed_selection {d : ℕ} {ι : Type*}
    [Countable ι] (p : unitInterval) (F : Set (Bond d)) (U : ι → Set (Vertex d))
    (hU : ∀ i, (U i).Finite) (N : ℕ)
    (hN : ∀ i, (finite_localBonds (hU i)).toFinset.card ≤ N)
    (hfresh : ∀ i, Disjoint (localBonds (U i)) F)
    (A : ι → Set (Configuration d)) {G C : Set (Configuration d)}
    (hA : ∀ i, MeasurableSet[bondSigma F] (A i))
    (hG : MeasurableSet G) (hC : MeasurableSet C) (hcover : G ⊆ ⋃ i, A i)
    (hsubset : ∀ i, A i ∩ fullyOpenRegion (U i) ⊆ C) :
    ∀ᵐ ω ∂(latticeBondLaw d p).restrict G,
      (p : ℝ) ^ N ≤ (latticeBondLaw d p)[C.indicator (fun _ => (1 : ℝ)) | bondSigma F] ω := by
  apply condExp_indicator_lower_of_fresh_bond_selection p F (fun i => localBonds (U i))
    hfresh A (fun i => fullyOpenRegion (U i)) hA
    (fun i => measurableSet_fullyOpenRegion_localBond (U i)) hC hG hcover hsubset
  exact fun i => latticeBondLaw_real_fullyOpenRegion_lower p (U i) (hU i) N (hN i)

/-- If each survival step selects a fresh bounded seed whose opening ends
survival, the probability of survival decays geometrically. -/
theorem measureReal_survival_le_of_fresh_seed_selection {d : ℕ} {ι : Type*}
    [Countable ι] (p : unitInterval) (N : ℕ)
    (F : ℕ → Set (Bond d)) (U : ℕ → ι → Set (Vertex d))
    (hU : ∀ n i, (U n i).Finite)
    (hN : ∀ n i, (finite_localBonds (hU n i)).toFinset.card ≤ N)
    (hfresh : ∀ n i, Disjoint (localBonds (U n i)) (F n))
    (A : ℕ → ι → Set (Configuration d)) (G C : ℕ → Set (Configuration d))
    (hA : ∀ n i, MeasurableSet[bondSigma (F n)] (A n i))
    (hG : ∀ n, MeasurableSet[bondSigma (F n)] (G n))
    (hC : ∀ n, MeasurableSet (C n))
    (hcover : ∀ n, G n ⊆ ⋃ i, A n i)
    (hsubset : ∀ n i, A n i ∩ fullyOpenRegion (U n i) ⊆ C n)
    (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hdisj : ∀ n, Disjoint (G (n + 1)) (C n)) :
    ∀ n, (latticeBondLaw d p).real (G n) ≤ (1 - (p : ℝ) ^ N) ^ n := by
  apply measureReal_le_pow_one_sub_of_condExp_success (latticeBondLaw d p)
    (fun n => bondSigma (F n)) (fun n => bondSigma_le (F n)) G C hG hC hdecr hdisj
    ((p : ℝ) ^ N) (pow_le_one₀ p.property.1 p.property.2)
  intro n
  exact condExp_indicator_lower_of_fresh_seed_selection p (F n) (U n) (hU n) N (hN n)
    (hfresh n) (A n) (hA n) (bondSigma_le (F n) _ (hG n)) (hC n)
    (hcover n) (hsubset n)

end Rigidity.Percolation

import Rigidity.Percolation.SlabIndependence

/-!
# Bounds for crossings of disjoint regions

A connection between two marked subsets of a finite region depends only on
its internal bonds. Disjoint regions with a uniform crossing probability
therefore provide a geometric bound for failure of a larger crossing event.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- A region contains an open connection from one marked subset to another. -/
def ConnectsRegions {d : ℕ} (ω : Configuration d) (B L R : Set (Vertex d)) : Prop :=
  ∃ x ∈ B, x ∈ L ∧ ∃ y ∈ B, y ∈ R ∧ (openIn ω B).Reachable x y

/-- Connection inside a finite region is measurable in its internal bonds. -/
theorem measurableSet_connectsRegions_localBond {d : ℕ} (B L R : Set (Vertex d))
    (hB : B.Finite) :
    MeasurableSet[localBondSigma B] {ω | ConnectsRegions ω B L R} := by
  apply localEdgeSigma_le_localBondSigma B
  apply localGraphSigma_le_localEdgeSigma B hB
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨{G | ∃ ω, ConnectsRegions ω B L R ∧ (openGraph ω).induce B = G}, trivial, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ω', hω', heq⟩
    have hgraph : openIn ω' B = openIn ω B := by
      apply openIn_eq_of_agree_on (Set.Subset.refl B)
      intro x hx y hy
      exact Iff.of_eq (congrArg (fun G : SimpleGraph {x : Vertex d // x ∈ B} =>
        G.Adj ⟨x, hx⟩ ⟨y, hy⟩) heq)
    simpa only [ConnectsRegions, hgraph] using hω'
  · intro hω
    exact ⟨ω, hω, rfl⟩

/-- If a global event occurs whenever any of several disjoint finite regions
has a marked connection, its failure probability decays geometrically in the
number of regions. -/
theorem measureReal_failure_le_of_disjoint_region_connections {d : ℕ} {ι : Type*}
    (p : unitInterval) (B L R : ι → Set (Vertex d)) (E : Set (Configuration d))
    (hfinite : ∀ i, (B i).Finite) (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hE : ∀ i ω, ConnectsRegions ω (B i) (L i) (R i) → ω ∈ E)
    (δ : ℝ) (hprob : ∀ i, δ ≤ (latticeBondLaw d p).real
      {ω | ConnectsRegions ω (B i) (L i) (R i)}) (s : Finset ι) :
    (latticeBondLaw d p).real Eᶜ ≤ (1 - δ) ^ s.card := by
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (measureReal_no_local_success_le p B (fun i => {ω | ConnectsRegions ω (B i) (L i) (R i)})
      hdisj (fun i => measurableSet_connectsRegions_localBond (B i) (L i) (R i) (hfinite i))
      δ hprob s)
  intro ω hω
  simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
  intro i hi hcross
  exact hω (hE i ω hcross)

end Rigidity.Percolation

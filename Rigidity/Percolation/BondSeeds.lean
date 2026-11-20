import Rigidity.Percolation.BondSprinkling

/-!
# Finite open bond seeds

A finite vertex region has finitely many internal bonds. Requiring all of them
to be open defines a positive-probability seed at every positive bond density.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- A finite vertex region has finitely many internal bonds. -/
theorem finite_localBonds {d : ℕ} {U : Set (Vertex d)} (hU : U.Finite) :
    (localBonds U).Finite := by
  let E : Set (Sym2 (Vertex d)) := (fun xy : Vertex d × Vertex d => s(xy.1, xy.2)) '' (U ×ˢ U)
  have hE : E.Finite := (hU.prod hU).image _
  have hpre : (Subtype.val ⁻¹' E : Set (Bond d)).Finite :=
    hE.preimage (Set.injOn_of_injective Subtype.val_injective)
  apply hpre.subset
  intro e he
  obtain ⟨x, y, hxy, _⟩ := e.property
  refine ⟨(x, y), ⟨?_, ?_⟩, hxy.symm⟩
  · exact he x (hxy ▸ Sym2.mem_mk_left x y)
  · exact he y (hxy ▸ Sym2.mem_mk_right x y)

/-- Every internal bond of the region is open. -/
def fullyOpenRegion {d : ℕ} (U : Set (Vertex d)) : Set (Configuration d) :=
  {ω | ∀ e ∈ localBonds U, ω e = true}

/-- A finite region is fully open with probability `p` raised to its number
of internal bonds. -/
theorem latticeBondLaw_fullyOpenRegion {d : ℕ} (p : unitInterval)
    (U : Set (Vertex d)) (hU : U.Finite) :
    latticeBondLaw d p (fullyOpenRegion U) =
      ENNReal.ofReal (p : ℝ) ^ (finite_localBonds hU).toFinset.card := by
  have heq : fullyOpenRegion U = allBondsOpen (finite_localBonds hU).toFinset := by
    ext ω
    simp only [fullyOpenRegion, allBondsOpen, Set.mem_setOf_eq, Set.Finite.mem_toFinset]
  rw [heq, latticeBondLaw_allBondsOpen]

/-- A finite bond seed occurs with positive probability at positive density. -/
theorem latticeBondLaw_fullyOpenRegion_pos {d : ℕ} (p : unitInterval)
    (hp : 0 < (p : ℝ)) (U : Set (Vertex d)) (hU : U.Finite) :
    0 < latticeBondLaw d p (fullyOpenRegion U) := by
  rw [latticeBondLaw_fullyOpenRegion p U hU]
  exact ENNReal.pow_pos (ENNReal.ofReal_pos.mpr hp) _

/-- Opening every internal bond preserves all paths of the fully open graph
inside the region. -/
theorem reachable_openIn_of_fullyOpenRegion {d : ℕ} {ω : Configuration d}
    {U : Set (Vertex d)} (hseed : ω ∈ fullyOpenRegion U) {x y : Vertex d}
    (hpath : (openIn (allOpen d) U).Reachable x y) : (openIn ω U).Reachable x y := by
  apply hpath.mono
  intro a b hab
  have hnn : (nearestNeighborGraph d).Adj a b := by
    simpa only [openGraph_allOpen] using hab.1
  have he : bondOfAdjacent hnn ∈ localBonds U := by
    intro z hz
    change z ∈ s(a, b) at hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hab.2.1
    · exact hab.2.2
  exact ⟨(openGraph_adj_iff ω a b).mpr ⟨hnn, hseed _ he⟩, hab.2.1, hab.2.2⟩

/-- A fully open region depends only on its internal bonds. -/
theorem measurableSet_fullyOpenRegion_localBond {d : ℕ} (U : Set (Vertex d)) :
    MeasurableSet[localBondSigma U] (fullyOpenRegion U) := by
  have heq : fullyOpenRegion U = ⋂ e ∈ localBonds U, {ω : Configuration d | ω e = true} := by
    ext ω
    simp only [fullyOpenRegion, Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun he =>
    bondSigma_mono (Set.singleton_subset_iff.mpr he) _ (measurableSet_bond_open e)

/-- Fully open seeds in disjoint vertex regions have the product law. -/
theorem latticeBondLaw_disjoint_fullyOpenRegions {d : ℕ} {ι : Type*}
    (p : unitInterval) (U : ι → Set (Vertex d)) (hU : ∀ i, (U i).Finite)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j)) (s : Finset ι) :
    latticeBondLaw d p (⋂ i ∈ s, fullyOpenRegion (U i)) =
      ∏ i ∈ s, ENNReal.ofReal (p : ℝ) ^ (finite_localBonds (hU i)).toFinset.card := by
  rw [measure_biInter_localBond p U (fun i => fullyOpenRegion (U i)) hdisj
    (fun i => measurableSet_fullyOpenRegion_localBond (U i)) s]
  exact Finset.prod_congr rfl (fun i _ => latticeBondLaw_fullyOpenRegion p (U i) (hU i))

/-- If each of several disjoint finite regions has probability at least `δ`
of being a seed, their joint failure probability decays geometrically. -/
theorem measureReal_no_fullyOpenRegion_le {d : ℕ} {ι : Type*}
    (p : unitInterval) (U : ι → Set (Vertex d))
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j)) (δ : ℝ)
    (hprob : ∀ i, δ ≤ (latticeBondLaw d p).real (fullyOpenRegion (U i))) (s : Finset ι) :
    (latticeBondLaw d p).real (⋂ i ∈ s, (fullyOpenRegion (U i))ᶜ) ≤ (1 - δ) ^ s.card :=
  measureReal_no_local_success_le p U (fun i => fullyOpenRegion (U i)) hdisj
    (fun i => measurableSet_fullyOpenRegion_localBond (U i)) δ hprob s

end Rigidity.Percolation

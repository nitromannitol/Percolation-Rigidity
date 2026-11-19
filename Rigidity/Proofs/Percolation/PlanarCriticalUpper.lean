import Rigidity.Proofs.Section5.Peierls
import Rigidity.Proofs.Section5.InfiniteClusterMeasurable
import LatticeProb.Prob.Percolation.LatticeIncidentBonds
import LatticeProb.Prob.Percolation.LSSThinKDependent
import LatticeProb.Prob.CountableMeasurable

/-!
# A planar high-density bound

A planar site is declared open when both bonds pointing in the positive coordinate directions
are open. The site field has independent coordinates and its open paths are bond-open paths.
A Peierls estimate then gives percolation at a bond parameter strictly below one.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation
open scoped ENNReal

noncomputable section

namespace Rigidity.Percolation

open Rigidity.Steps.Section5 Rigidity.Proofs.Section5 LatticeProb.Percolation.LatticeIncident

/-- The bond from a site in a positive coordinate direction. -/
def outgoingBond (z : PlanarCarrier) (i : Fin 2) : Bond 2 :=
  bondOfAdjacent (show (nearestNeighborGraph 2).Adj (toSite2 z) (toSite2 z + LatticeProb.unit i)
    from ⟨i, Or.inl rfl⟩)

/-- A site is good when its two outgoing bonds are open. -/
def outgoingField (ω : Configuration 2) (z : PlanarCarrier) : Bool :=
  decide (∀ i : Fin 2, ω (outgoingBond z i) = true)

/-- Good-site events are measurable. -/
theorem measurable_outgoingField : Measurable outgoingField := by
  apply measurable_pi_lambda
  intro z
  unfold outgoingField
  apply LatticeProb.measurable_decide
  have he : {ω : Configuration 2 | ∀ i : Fin 2, ω (outgoingBond z i) = true} =
      ⋂ i : Fin 2, {ω : Configuration 2 | ω (outgoingBond z i) = true} := by
    ext ω
    simp
  rw [he]
  refine MeasurableSet.iInter fun i => ?_
  have hm := (measurable_pi_apply (outgoingBond z i) :
    Measurable fun ω : Configuration 2 => ω (outgoingBond z i))
      (measurableSet_singleton (true : Bool))
  simpa only [Set.preimage, Set.mem_singleton_iff] using hm

/-- Distinct pairs of a site and a positive direction determine distinct bonds. -/
theorem outgoingBond_injective {z w : PlanarCarrier} {i j : Fin 2}
    (h : outgoingBond z i = outgoingBond w j) : z = w ∧ i = j := by
  have he : positiveBond i (toSite2 z) = positiveBond j (toSite2 w) :=
    congrArg Subtype.val h
  obtain ⟨hij, hzw⟩ := positiveBond_injective he
  exact ⟨planarSiteEquiv.injective hzw, hij⟩

/-- The finite collection of bonds used by a finite family of sites. -/
def outgoingBonds (I : Finset PlanarCarrier) : Finset (Bond 2) :=
  I.biUnion fun z => Finset.univ.image (outgoingBond z)

/-- Each outgoing bond of a listed site belongs to the bond collection. -/
theorem mem_outgoingBonds {I : Finset PlanarCarrier} {z : PlanarCarrier} (hz : z ∈ I)
    (i : Fin 2) : outgoingBond z i ∈ outgoingBonds I := by
  simp only [outgoingBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨z, hz, i, rfl⟩

/-- Disjoint sets of sites use disjoint sets of outgoing bonds. -/
theorem disjoint_outgoingBonds {I J : Finset PlanarCarrier} (hIJ : Disjoint I J) :
    Disjoint (outgoingBonds I) (outgoingBonds J) := by
  rw [Finset.disjoint_left] at hIJ ⊢
  intro e heI heJ
  simp only [outgoingBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and] at heI heJ
  obtain ⟨z, hz, i, rfl⟩ := heI
  obtain ⟨w, hw, j, he⟩ := heJ
  obtain ⟨hzw, _⟩ := outgoingBond_injective he.symm
  subst w
  exact hIJ hz hw

/-- The field on `I` as a function of the bonds attached to `I`. -/
def outgoingLocal (I : Finset PlanarCarrier) (ξ : outgoingBonds I → Bool) : I → Bool :=
  fun z => decide (∀ i : Fin 2, ξ ⟨outgoingBond z i, mem_outgoingBonds z.2 i⟩ = true)

/-- Restricting the field to `I` uses only its outgoing bonds. -/
theorem outgoingField_restrict_eq (I : Finset PlanarCarrier) :
    (fun ω : Configuration 2 => fun z : I => outgoingField ω z) =
      outgoingLocal I ∘ fun ω e => ω e := by
  funext ω z
  rfl

/-- The outgoing field is one-dependent, in fact independent on disjoint site sets. -/
theorem outgoingField_oneDependent (p : unitInterval) :
    KDependentPlanar 1 ((latticeBondLaw 2 p).map outgoingField) := by
  intro I J hIJ
  rw [indepFun_map_iff_of_measurable measurable_outgoingField
    (measurable_finsetRestrict_planar I) (measurable_finsetRestrict_planar J)]
  have hd : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro z hzI hzJ
    have h := hIJ z hzI z hzJ
    simp at h
  have hind := ((latticeBondLaw_iIndepFun (d := 2) p).indepFun_finset
    (outgoingBonds I) (outgoingBonds J) (disjoint_outgoingBonds hd)
    fun e => measurable_pi_apply e).comp
      (measurable_of_finite (outgoingLocal I)) (measurable_of_finite (outgoingLocal J))
  convert hind using 1
  · exact outgoingField_restrict_eq I
  · exact outgoingField_restrict_eq J

end Rigidity.Percolation

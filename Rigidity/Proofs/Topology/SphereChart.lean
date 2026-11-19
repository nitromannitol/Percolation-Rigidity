import Rigidity.Proofs.Topology.SphereLoopPole
import Rigidity.Proofs.Topology.PlanarJordan.Summary

/-!
# Stereographic images of plane sets

A bounded plane set has a compact stereographic closure away from the projection pole; an
unbounded set accumulates at that pole.
-/

open Set Metric Bornology

namespace Rigidity.Topology

open Rigidity.External MatedCRTHarmonic.Planar.Jordan

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- The inverse stereographic projection is an open embedding. -/
theorem stereographic_symm_openEmbedding (p : S2) :
    Topology.IsOpenEmbedding (stereographic' 2 p).symm := by
  apply (stereographic' 2 p).symm.to_isOpenEmbedding
  simp

/-- The closure of the stereographic image of a bounded set is the image of its closure. -/
theorem closure_stereographic_symm_image (p : S2) {U : Set Plane} (hU : IsBounded U) :
    closure ((stereographic' 2 p).symm '' U) = (stereographic' 2 p).symm '' closure U := by
  have hc : Continuous (stereographic' 2 p).symm := (stereographic_symm_openEmbedding p).continuous
  have hclosed : IsClosed ((stereographic' 2 p).symm '' closure U) :=
    (hU.isCompact_closure.image hc).isClosed
  exact (closure_minimal (image_mono subset_closure) hclosed).antisymm
    (image_closure_subset_closure_image hc)

/-- The projection pole avoids the closure of the stereographic image of a bounded set. -/
theorem pole_not_mem_closure_image_of_bounded (p : S2) {U : Set Plane} (hU : IsBounded U) :
    p ∉ closure ((stereographic' 2 p).symm '' U) := by
  rw [closure_stereographic_symm_image p hU]
  rintro ⟨u, _, hu⟩
  have hs := (stereographic' 2 p).map_target (show u ∈ (stereographic' 2 p).target by simp)
  simp only [stereographic'_source, mem_compl_iff, mem_singleton_iff] at hs
  exact hs hu

/-- The frontier of a bounded open plane set is transported by stereographic projection. -/
theorem frontier_stereographic_symm_image (p : S2) {U : Set Plane} (hU : IsOpen U)
    (hb : IsBounded U) :
    frontier ((stereographic' 2 p).symm '' U) = (stereographic' 2 p).symm '' frontier U := by
  have he := stereographic_symm_openEmbedding p
  have ho : IsOpen ((stereographic' 2 p).symm '' U) := he.isOpenMap U hU
  change closure ((stereographic' 2 p).symm '' U) \ interior ((stereographic' 2 p).symm '' U) =
    (stereographic' 2 p).symm '' (closure U \ interior U)
  rw [ho.interior_eq, closure_stereographic_symm_image p hb, hU.interior_eq,
    image_sdiff he.injective]

/-- The projection pole belongs to the closure of the image of every unbounded set. -/
theorem pole_mem_closure_image_of_unbounded (p : S2) {U : Set Plane} (hU : ¬ IsBounded U) :
    p ∈ closure ((stereographic' 2 p).symm '' U) := by
  by_contra hp
  let e := stereographic' 2 p
  have hsource : closure (e.symm '' U) ⊆ e.source := by
    intro z hz
    rw [stereographic'_source]
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    have hp' : p ∉ closure (e.symm '' U) := hp
    subst z
    exact hp' hz
  have hcompact : IsCompact (closure (e.symm '' U)) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have hbounded : IsBounded (e '' closure (e.symm '' U)) :=
    (hcompact.image_of_continuousOn (e.continuousOn.mono hsource)).isBounded
  apply hU (hbounded.subset ?_)
  intro z hz
  refine ⟨e.symm z, subset_closure ⟨z, hz, rfl⟩, ?_⟩
  exact e.right_inv (by simp [e])

end Rigidity.Topology

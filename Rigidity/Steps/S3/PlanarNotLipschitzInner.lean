import Rigidity.Proofs.S3.PlanarCorrectorValid
import Rigidity.Steps.S3.NotLipschitzInner

/-!
# Planar inner-measure non-Lipschitz conclusion

The measurable event construction needs only the planar qualitative corrector input.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation LatticeProb.External Rigidity.Section3
open Classical

namespace Rigidity.Steps.S3

/-- A positive outer probability contains a positive measurable event under planar inputs. -/
theorem exists_measurable_subset_originGradientEvent_two (hclassical : SupercriticalBondUniqueness)
    (hcorrector : Rigidity.External.SupercriticalBondCorrectorInputTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {L : ℝ}
    (h : latticeBondLaw 2 p (originGradientEvent 2 L) ≠ 0) :
    ∃ A ⊆ originGradientEvent 2 L, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A := by
  obtain ⟨G, hGm, hG1, hvalid⟩ :=
    Rigidity.Proofs.S3.exists_measurable_corrector_valid_set_two hclassical hcorrector p hpc hp1
  obtain ⟨F, hFm, hF⟩ := exists_measurable_rooted_plane_on_valid_set G hGm hvalid 0
  have hB : MeasurableSet (G ∩ infiniteComponentEvent 0) :=
    hGm.inter (measurableSet_infiniteComponentEvent 0)
  have hΦ : ∀ a, Measurable fun z : ↥(G ∩ infiniteComponentEvent 0) => F (z, slopeE1 2) a :=
    fun a => (measurable_pi_apply a).comp (hFm.comp (measurable_id.prodMk measurable_const))
  set g : ↥(G ∩ infiniteComponentEvent 0) → ℝ := fun z => ∑ i : Fin 2,
    if (openGraph z.val).Adj 0 (unit i) then
      |F (z, slopeE1 2) 0 - F (z, slopeE1 2) (unit i)| else 0 with hg_def
  have hg : Measurable g := Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurable_subtype_coe (measurableSet_openGraph_adj 0 (unit i)))
      ((hΦ 0).sub (hΦ (unit i))).abs measurable_const
  have key : ∀ (z : ↥(G ∩ infiniteComponentEvent 0)) (h : HasUniqueInfiniteOpenComponent z.val)
      (ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp) (u : uniqueInfiniteComponent h → ℝ),
      IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 2) u →
      g z = originGradientNorm (uniqueInfiniteComponent h) ho u := by
    intro z h ho u hu
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (openGraph z.val).Adj 0 (unit i)
    · rw [if_pos hi, dif_pos hi, rootedPlane_eq_sub hF z h ho hu ho,
        rootedPlane_eq_sub hF z h ho hu
          ((uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hi)]
      congr 1
      ring
    · rw [if_neg hi, dif_neg hi]
  have hGc : latticeBondLaw 2 p Gᶜ = 0 := (prob_compl_eq_zero_iff hGm).2 hG1
  refine ⟨Subtype.val '' {z | L < g z}, ?_, hB.subtype_image (measurableSet_lt measurable_const hg),
    ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have h := (hvalid z.2.1).1
    have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
      (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
    obtain ⟨u, ⟨hu, -⟩, -⟩ := ((hvalid z.2.1).2 h).1 (slopeE1 2) ⟨0, ho⟩
    exact ⟨h, ho, u, hu, (key z h ho u hu) ▸ hz⟩
  · refine pos_iff_ne_zero.mpr fun hA => h (measure_mono_null ?_ (measure_union_null hA hGc))
    rintro ω ⟨h, ho, u, hu, hlt⟩
    by_cases hωG : ω ∈ G
    · refine Or.inl ⟨⟨ω, hωG, (mem_uniqueInfiniteComponent_iff h 0).mp ho⟩, ?_, rfl⟩
      show L < g _
      rw [key _ h ho u hu]
      exact hlt
    · exact Or.inr hωG

/-- The inner-measure non-Lipschitz statement from planar corrector data. -/
theorem notLipschitzStmt_of_originGradient_two (hclassical : SupercriticalBondUniqueness)
    (hcorrector : Rigidity.External.SupercriticalBondCorrectorInputTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : ∀ L : ℝ, 1 ≤ L → latticeBondLaw 2 p (originGradientEvent 2 L) ≠ 0) :
    NotLipschitzStmt 2 p := by
  intro L hL
  have hd1 : (1 : ℝ) ≤ 2 := by exact_mod_cast (show 1 ≤ 2 by omega)
  obtain ⟨A, hA, hAm, hApos⟩ :=
    exists_measurable_subset_originGradientEvent_two hclassical hcorrector hpc hp1 (h L hL)
  obtain ⟨A', hA', hA'm, hA'pos⟩ := exists_measurable_subset_originGradientEvent_two hclassical
    hcorrector hpc hp1 (h (2 * L) (one_le_mul_of_one_le_of_one_le hd1 hL))
  refine ⟨⟨A, hA, hAm, hApos⟩, ⟨A', fun ω hω => ?_, hA'm, hA'pos⟩⟩
  obtain ⟨h, ho, u, hu, hlt⟩ := hA' hω
  exact ⟨h, u, hu, not_isLipschitzWith_of_lt_originGradientNorm ho (by linarith) hlt⟩

end Rigidity.Steps.S3

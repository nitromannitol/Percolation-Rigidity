import Rigidity.Proofs.Section5.SecondGoodEvent
import Rigidity.Proofs.Section5.ThirdGoodEventDirectionFree
import Rigidity.Proofs.S3.PlanarNonLipschitz
import Rigidity.Proofs.Section5.PlanarLiteratureAdapters

/-!
# Planar good-event estimates

The second and third good-event estimates use the planar corrector hypotheses.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5 Rigidity.External

theorem secondGoodEvent_bound_two (hQ : CorrectorQuantitativeInputTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hUae : UniqueClusterAe p) :
    ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ (x : Vertex 2) (K : ℝ), 1 ≤ K →
      latticeBondLaw 2 p (eventG2 x K)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * K ^ s))) := by
  obtain ⟨s, C, hs, hC, hQx⟩ := hQ p hpc hp1 (1 / 2) (by norm_num)
  set c := (5 / C) ^ s with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) s
  set K₁ := 2 * C ^ 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨2 * Real.exp (c * K₁ ^ s), c, s, by positivity, hc, hs, fun x K hK => ?_⟩
  obtain ⟨M, -, -, hMos, hMae⟩ := hQx x
  set μ := latticeBondLaw 2 p
  have hexp1 : 1 ≤ Real.exp (c * K₁ ^ s) :=
    Real.one_le_exp (mul_nonneg hc.le (Real.rpow_nonneg hK₁0 s))
  rcases lt_or_ge K K₁ with hKK | hKK
  · refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal]
    have hKs : K ^ s ≤ K₁ ^ s := Real.rpow_le_rpow (by linarith) hKK.le hs.le
    have h1 : 1 ≤ Real.exp (c * K₁ ^ s - c * K ^ s) :=
      Real.one_le_exp (by nlinarith)
    calc (1 : ℝ) ≤ 2 * Real.exp (c * K₁ ^ s - c * K ^ s) := by linarith
      _ = 2 * Real.exp (c * K₁ ^ s) * Real.exp (-(c * K ^ s)) := by
        rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
  · have hbad := ae_iff.mp (hMae.and hUae)
    have hsub : (eventG2 x K)ᶜ ⊆ {ω | ¬ ((∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin 2 → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ r : ℝ, M ω ≤ r →
        ∀ a b a' b' : uniqueInfiniteComponent h,
          ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
          (componentGraph (uniqueInfiniteComponent h)).Adj a' b' →
          |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
              |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
            ≤ C * (∑ i, |q i|) * r ^ (1 / 2 : ℝ)) ∧ HasUniqueInfiniteOpenComponent ω)} ∪
        {ω | 5 * K < M ω} := by
      intro ω hω
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, not_lt] at hn
      exact hω (mem_eventG2_of_minimalScale_le hC hKK hK hn.1.1 hn.1.2 hn.2)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hbad, zero_add]
    refine (measure_lt_minimalScale_le hs hC (by linarith) hMos).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hpow : (5 * K / C) ^ s = c * K ^ s := by
      rw [hc_def, ← Real.mul_rpow (by positivity) (by linarith)]
      ring_nf
    rw [hpow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (Real.exp_pos _).le hexp1) (by norm_num)


theorem exists_measurable_subset_eventG3_two
    (hU : Rigidity.External.SupercriticalBondCorrectorInputTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h32 : Rigidity.Section3.NotLipschitzStmt 2 p) (Cχ : ℝ) (hCχ : 1 ≤ Cχ) :
    ∃ A ⊆ eventG3 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A := by
  set μ := latticeBondLaw 2 p
  set q : Fin 2 → ℝ := Pi.single 0 1
  have hbad := ae_iff.mp (hU p hpc hp1)
  set N := toMeasurable μ {ω | ¬ ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin 2 → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin 2 → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)} with hN
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hbad
  set G := Nᶜ ∩ uniqueInfiniteComponentEvent 2
  have hGm : MeasurableSet G :=
    (measurableSet_toMeasurable _ _).compl.inter (measurableSet_uniqueInfiniteComponentEvent 2)
  have hvalid : G ⊆ correctorValidEvent 2 := by
    intro ω hω
    by_contra hn
    exact hω.1 (subset_toMeasurable _ _ fun hP => hn ⟨hω.2, by simpa using hP⟩)
  obtain ⟨F, hFm, hF⟩ := exists_measurable_rooted_plane_on_valid_set G hGm hvalid 0
  have hB : MeasurableSet (G ∩ infiniteComponentEvent 0) :=
    hGm.inter (measurableSet_infiniteComponentEvent 0)
  set T : Set ↥(G ∩ infiniteComponentEvent 0) :=
    ⋃ v : Vertex 2, {z | (openGraph z.val).Adj 0 v ∧ Cχ ≤ F (z, q) v}
  have hT : MeasurableSet T := by
    refine MeasurableSet.iUnion fun v => ?_
    refine (measurable_subtype_coe (measurableSet_openGraph_adj 0 v)).inter ?_
    exact measurableSet_le measurable_const
      ((measurable_pi_apply v).comp (hFm.comp (measurable_id.prodMk measurable_const)))
  refine ⟨Subtype.val '' T, ?_, hB.subtype_image hT, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨v, hadj, hval⟩ := Set.mem_iUnion.mp hz
    have h := (hvalid z.2.1).1
    have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
      (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
    have hv : v ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    refine ⟨h, ho, ⟨v, hv⟩, ((uniqueInfiniteComponent h).toSimpleGraph_adj ho hv).2 hadj,
      fun ℓ hℓ => ?_⟩
    rw [Steps.S3.rootedPlane_eq_sub hF z h ho hℓ hv] at hval
    exact hval
  · have hS := neighborRise_of_notLipschitz h32 Cχ hCχ
    refine pos_iff_ne_zero.mpr fun hA => hS (measure_mono_null ?_ (measure_union_null hA hN0))
    rintro ω ⟨h, ho, y, hadj, u, hu, hlt⟩
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · refine Or.inl ⟨⟨ω, ⟨hωN, h⟩, (mem_uniqueInfiniteComponent_iff h 0).mp ho⟩,
        Set.mem_iUnion.mpr ⟨y.val,
          ((uniqueInfiniteComponent h).toSimpleGraph_adj ho y.2).1 hadj, ?_⟩, rfl⟩
      rw [Steps.S3.rootedPlane_eq_sub hF _ h ho hu y.2]
      exact hlt.le


theorem goodEventLowerBound_of_planar_inputs {p : unitInterval} (hQ : CorrectorQuantitativeInputTwo)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hU : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h32 : Rigidity.Section3.NotLipschitzStmt 2 p) :
    GoodEventLowerBoundStmt p := by
  intro Cχ hCχ
  set μ := latticeBondLaw 2 p
  obtain ⟨A₃, hA₃, hA₃m, hA₃pos⟩ := exists_measurable_subset_eventG3_two hU hpc hp1 h32 Cχ hCχ
  have hA₃top : μ A₃ ≠ ⊤ := measure_ne_top μ A₃
  set c := (μ A₃).toReal / 2 with hc_def
  have hc : 0 < c := half_pos (ENNReal.toReal_pos hA₃pos.ne' hA₃top)
  refine ⟨c, hc, fun Cf R c₁ hL => ?_⟩
  obtain ⟨C₁, a₁, hC₁, ha₁, hbad⟩ := hL
  obtain ⟨C₂, a₂, s, hC₂, ha₂, hs, hG2⟩ := secondGoodEvent_bound_two hQ hpc hp1 (uniqueClusterAe hUq hpc hp1)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    (((tendsto_exp_add_exp_rpow (C := C₁) (C' := C₂) ha₁ ha₂ hs).eventually
      (ge_mem_nhds hc)).and (eventually_ge_atTop 1))
  refine ⟨K₀, fun K hK x => ?_⟩
  obtain ⟨hsmall, hK1⟩ := hK₀ K hK
  obtain ⟨A₀, hA₀, hA₀m, hA₀μ⟩ :=
    exists_measurable_subset_eventG_zero (p := p) (Cf := Cf) (R := R) (c₁ := c₁) (K := K) firstGoodEventStep hA₃
      hA₃m
  have hD : μ (badPathEvent Cf R c₁ K) + μ (eventG2 0 K)ᶜ ≤ ENNReal.ofReal c := by
    refine (add_le_add (hbad K hK1) (hG2 0 K hK1)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hsmall
  have hτ := measurePreserving_configurationTranslation p (-x)
  refine ⟨configurationTranslation (-x) ⁻¹' A₀, fun ω hω => (goodEventTranslationStep Cf R c₁ Cχ K x ω).mpr (hA₀ hω),
    hτ.measurable hA₀m, ?_⟩
  rw [hτ.measure_preimage hA₀m.nullMeasurableSet]
  refine le_trans ?_ (le_trans (tsub_le_tsub_left hD _) hA₀μ)
  rw [← ENNReal.ofReal_toReal hA₃top, ← ENNReal.ofReal_sub _ hc.le]
  exact ENNReal.ofReal_le_ofReal (by rw [hc_def]; linarith)


end Rigidity.Proofs.Section5

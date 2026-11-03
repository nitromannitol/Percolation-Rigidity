import LatticeProb.Prob.Percolation.TranslationFlipStableEvent
import LatticeProb.Prob.Percolation.DeterministicIntegerSlope
import LatticeProb.Prob.Percolation.DeletedBridgeRigidity
import LatticeProb.Prob.Percolation.CorrectedPlaneEnergyRepair
import LatticeProb.Prob.Percolation.FiniteGradientBondDeletion
import LatticeProb.Network.EdgeDeletionRigidity
import LatticeProb.Prob.Percolation.LatticeLinearGrowth



open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Support

theorem integer_gradient_corrected_planes_constant
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin d → ℝ) (u : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q u →
          (∀ x y : uniqueInfiniteComponent h,
            (componentGraph (uniqueInfiniteComponent h)).Adj x y →
            ∃ n : ℤ, u y - u x = (n : ℝ)) →
          ∀ x y : uniqueInfiniteComponent h, u x = u y := by
  classical
  obtain ⟨G, hG, hmass, hvalid, hinv, hstable⟩ :=
    exists_translation_flip_stable_corrector_event hclassical hcorrector d hd p hpc hp1
  obtain ⟨data⟩ := exists_deterministicIntegerSlopeData p
    ((criticalProbability_nonneg d).trans_lt hpc) hp1 G hG hmass hvalid hinv
  filter_upwards [(mem_ae_iff_prob_eq_one data.measurable_flipEvent).mpr
    data.mass_flipEvent] with ω hω
  let h := (hvalid (data.event_subset (data.flipEvent_subset hω))).1
  let C := uniqueInfiniteComponent h
  have hC : C.supp.Infinite := uniqueInfiniteComponent_infinite h
  refine ⟨h, ?_⟩
  intro q u hu hint
  have hq : q ∈ data.subgroup := (data.source_iff ω (data.flipEvent_subset hω) q).2
    ⟨u, hu, hint⟩
  have hedge : ∀ a b : C, (componentGraph C).Adj a b → u a = u b := by
    intro a b hab
    let F : Finset (Bond d) := {componentEdgeBond C hab}
    have hη : componentEdgeFlip C hab ∈ G := data.flip_mem ω hω F
    let hNew := (hvalid hη).1
    have hqNew := (data.flip_source_iff ω hω F q).1 hq
    obtain ⟨v, hv, hvint⟩ := hqNew
    by_cases hreach : ((openGraph (componentEdgeFlip C hab)).induce C.supp).Reachable a b
    · let E := nonBridgeComponentEquiv C h hC hab hNew hreach
      let e := nonBridgeComponentIso C h hC hab hNew hreach
      obtain ⟨B, K, hB, hK⟩ :=
        correctedPlane_comparison_bounded_finite_energy_of_nonbridge C h hC hab hNew hreach
          (hvalid hη) hu hv
      let w : uniqueInfiniteComponent hNew → ℝ := fun y => v y - u (E.symm y)
      have hwint : ∀ x y, (componentGraph (uniqueInfiniteComponent hNew)).Adj x y →
          ∃ z : ℤ, w x - w y = (z : ℝ) := by
        intro x y hxy
        have hd : ((componentGraph C).deleteEdges
            (({s(a, b)} : Finset (Sym2 C)) : Set (Sym2 C))).Adj (E.symm x) (E.symm y) := by
          apply e.map_rel_iff.mp
          change (componentGraph (uniqueInfiniteComponent hNew)).Adj
            (E (E.symm x)) (E (E.symm y))
          simpa only [Equiv.apply_symm_apply] using hxy
        obtain ⟨m, hm⟩ := hvint y x hxy.symm
        obtain ⟨n, hn⟩ := hint (E.symm y) (E.symm x) (SimpleGraph.deleteEdges_adj.mp hd).1.symm
        refine ⟨m - n, ?_⟩
        simp only [Int.cast_sub]
        dsimp only [w]
        linarith
      obtain ⟨S, c, hc⟩ := exists_finset_exception_constant_on_flip_stable_valid_set
        G hvalid (fun F η hη => hstable η hη F) hη (uniqueInfiniteComponent hNew)
        (uniqueInfiniteComponent_infinite hNew) w hwint ⟨K, hK⟩
      let V : C → ℝ := fun x => v (E x)
      have hcof : ∃ (T : Finset C) (c : ℝ), ∀ x, x ∉ T → V x - u x = c := by
        refine ⟨S.image E.symm, c, ?_⟩
        intro x hx
        have hxS : E x ∉ S := by
          intro hxS
          apply hx
          exact Finset.mem_image.mpr ⟨E x, hxS, E.symm_apply_apply x⟩
        simpa only [w, V, E.symm_apply_apply] using hc (E x) hxS
      have huNet : ∀ x, LatticeProb.Network.netLaplacian (componentGraph C)
          (LatticeProb.Network.unitCond (componentGraph C)) u x = 0 := by
        intro x
        rw [← componentLaplacian_eq_netLaplacian]
        exact hu.1.1 x
      have hVNet : ∀ x, LatticeProb.Network.netLaplacian
          ((componentGraph C).deleteEdges (({s(a, b)} : Finset (Sym2 C)) : Set (Sym2 C)))
          (LatticeProb.Network.unitCond ((componentGraph C).deleteEdges
            (({s(a, b)} : Finset (Sym2 C)) : Set (Sym2 C)))) V x = 0 := by
        intro x
        rw [LatticeProb.Network.netLaplacian_unitCond]
        rw [← nonBridgeComponent_laplacian C h hC hab hNew hreach V x]
        change componentLaplacian (uniqueInfiniteComponent hNew)
          (fun y => v (E (E.symm y))) (E x) = 0
        have heq : (fun y => v (E (E.symm y))) = v := by
          funext y
          rw [E.apply_symm_apply]
        rw [heq]
        exact hv.1.1 (E x)
      exact LatticeProb.Network.edge_drop_eq_zero_of_harmonic_cofinite_difference
        (componentGraph C) hab u V huNet hVNet hcof
    · exact correctedPlane_eq_of_singleton_flip_separates C h hC hab hNew hreach hu
  intro x y
  obtain ⟨walk⟩ := (uniqueInfiniteComponent_connected h) x y
  induction walk with
  | nil => rfl
  | @cons a b c hab walk ih => exact (hedge a b hab).trans ih

theorem integer_valued_linear_growth (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x : uniqueInfiniteComponent h,
            componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          (∀ x : uniqueInfiniteComponent h, ∃ z : ℤ, u x = (z : ℝ)) →
          componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u →
          ∃ a : ℤ, ∀ x : uniqueInfiniteComponent h, u x = (a : ℝ) := by
  classical
  obtain ⟨G, hG, hmass, hvalid, _, _⟩ :=
    exists_translation_flip_stable_corrector_event hclassical hcorrector d hd p hpc hp1
  filter_upwards [integer_gradient_corrected_planes_constant d hd p hpc hp1 hclassical hcorrector,
    (mem_ae_iff_prob_eq_one hG).mpr hmass] with ω hconstant hω
  obtain ⟨h, hconst⟩ := hconstant
  refine ⟨h, ?_⟩
  intro u hu hint hg
  obtain ⟨q, hq, _⟩ := (hvalid hω).2 h |>.2 u
    (mem_harmonicGrowthSpace_one_of_pointwise_linear_growth _ u hu hg)
  have hgrad : ∀ x y : uniqueInfiniteComponent h,
      (componentGraph (uniqueInfiniteComponent h)).Adj x y →
        ∃ n : ℤ, u y - u x = (n : ℝ) := by
    intro x y _
    obtain ⟨m, hm⟩ := hint y
    obtain ⟨n, hn⟩ := hint x
    exact ⟨m - n, by rw [hm, hn, Int.cast_sub]⟩
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  obtain ⟨a, ha⟩ := hint ⟨o, ho⟩
  exact ⟨a, fun x => (hconst q u hq hgrad x ⟨o, ho⟩).trans ha⟩

end Rigidity.Support

import Rigidity.Proofs.Section5.SiteRectangleCrossings

/-!
# Translation of planar site fields

Translations preserve finite-range dependence and one-site probability bounds.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Percolation.Literature

namespace Rigidity.Proofs.Section5

/-- A planar site field observed from the site `a`. -/
def translatePlanarField (a : PlanarCarrier) (η : PlanarCarrier → Bool) : PlanarCarrier → Bool :=
  fun z => η (a + z)

theorem measurable_translatePlanarField (a : PlanarCarrier) :
    Measurable (translatePlanarField a) :=
  measurable_pi_lambda _ fun z => measurable_pi_apply (a + z)

/-- Translating a finite-range dependent planar field preserves its dependence range. -/
theorem kDependentPlanar_map_translate {ν : Measure (PlanarCarrier → Bool)} [IsFiniteMeasure ν]
    {k : ℕ} (hν : KDependentPlanar k ν) (a : PlanarCarrier) :
    KDependentPlanar k (ν.map (translatePlanarField a)) := by
  classical
  intro I J hfar
  let f : PlanarCarrier → PlanarCarrier := fun z => a + z
  have hfar' : ∀ x ∈ I.image f, ∀ y ∈ J.image f,
      (k : ℤ) < max |x.1 - y.1| |x.2 - y.2| := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
    simpa [f, Prod.fst_add, Prod.snd_add] using hfar x' hx' y' hy'
  have h := hν (I.image f) (J.image f) hfar'
  refine (indepFun_map_iff_of_measurable (T := translatePlanarField a)
    (measurable_translatePlanarField a) (measurable_finsetRestrict_planar I)
    (measurable_finsetRestrict_planar J) ν).mpr ?_
  have hI : Measurable (fun g : (I.image f → Bool) => fun x : I =>
      g ⟨f x, Finset.mem_image.2 ⟨x, x.2, rfl⟩⟩) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply _
  have hJ : Measurable (fun g : (J.image f → Bool) => fun x : J =>
      g ⟨f x, Finset.mem_image.2 ⟨x, x.2, rfl⟩⟩) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply _
  exact h.comp hI hJ

/-- Translation carries a one-site event to the event at its translated site. -/
theorem translatePlanarField_closed_marginal (ν : Measure (PlanarCarrier → Bool))
    (a z : PlanarCarrier) :
    (ν.map (translatePlanarField a)) {η | η z = false} = ν {η | η (a + z) = false} := by
  rw [Measure.map_apply (measurable_translatePlanarField a)
    (measurableSet_eq_fun (measurable_pi_apply z) measurable_const)]
  rfl

/-- A translated rectangle has the same uniform bound for failure of disjoint crossings. -/
theorem measure_no_disjoint_open_crossings_translate_le {ν : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure ν] (hν : KDependentPlanar 1 ν)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18))
    (a : PlanarCarrier) (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 2 * k ≤ n) :
    ν (translatePlanarField a ⁻¹' {η | ¬∃ L : Finset (List (LatticeModels.Site 2)),
      Menger.IsLinkage
        (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
        (↑(leftSide m n)) (↑(rightSide m n)) L ∧ L.card = k}) ≤
      ENNReal.ofReal (4 * (m + 1 : ℝ) * (1 / 8 : ℝ) ^ n) := by
  let ν' := ν.map (translatePlanarField a)
  haveI : IsProbabilityMeasure ν' :=
    Measure.isProbabilityMeasure_map (measurable_translatePlanarField a).aemeasurable
  have hν' : KDependentPlanar 1 ν' := kDependentPlanar_map_translate hν a
  have hcl' : ∀ z, ν' {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18) := by
    intro z
    rw [translatePlanarField_closed_marginal]
    exact hcl (a + z)
  exact (Measure.le_map_apply (measurable_translatePlanarField a).aemeasurable _).trans
    (measure_no_disjoint_open_crossings_le hν' hcl' m n k hm hn hk)

/-- The probability that any of finitely many translated rectangles lacks `k` disjoint
horizontal crossings is bounded by the sum of their individual bounds. -/
theorem measure_exists_no_disjoint_crossings_translate_le
    {ν : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν] (hν : KDependentPlanar 1 ν)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18))
    (T : Finset PlanarCarrier) (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 2 * k ≤ n) :
    ν (⋃ a ∈ T, translatePlanarField a ⁻¹'
      {η | ¬∃ L : Finset (List (LatticeModels.Site 2)), Menger.IsLinkage
        (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
        (↑(leftSide m n)) (↑(rightSide m n)) L ∧ L.card = k}) ≤
      ENNReal.ofReal (4 * (T.card : ℝ) * (m + 1 : ℝ) * (1 / 8 : ℝ) ^ n) := by
  calc
    _ ≤ ∑ a ∈ T, ν (translatePlanarField a ⁻¹'
        {η | ¬∃ L : Finset (List (LatticeModels.Site 2)), Menger.IsLinkage
          (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
          (↑(leftSide m n)) (↑(rightSide m n)) L ∧ L.card = k}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ T, ENNReal.ofReal (4 * (m + 1 : ℝ) * (1 / 8 : ℝ) ^ n) :=
      Finset.sum_le_sum fun a _ =>
        measure_no_disjoint_open_crossings_translate_le hν hcl a m n k hm hn hk
    _ = ENNReal.ofReal (4 * (T.card : ℝ) * (m + 1 : ℝ) * (1 / 8 : ℝ) ^ n) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Rigidity.Proofs.Section5

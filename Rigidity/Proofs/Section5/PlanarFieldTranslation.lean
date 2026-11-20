import Rigidity.Proofs.Section5.SiteRectangleCrossings

/-!
# Translation of planar site fields

Translations preserve finite-range dependence and one-site probability bounds.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation

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

end Rigidity.Proofs.Section5

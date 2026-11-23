import Rigidity.Proofs.Section5.PlanarGreenUniqueness
import Rigidity.Proofs.Section5.PlanarGreenExistence
import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth

/-!
# Planar Green columns from the uniqueness of corrected planes

The first clause of the planar qualitative corrector input `SupercriticalBondCorrectorInputTwo`
(Armstrong–Dario, Theorem 2(i); Dario–Gu, §2.2.1) asserts that, for every slope `q` and every
vertex `o` of the infinite cluster, there is exactly one corrected plane of slope `q` vanishing at
`o`. At the slope `q = 0` this is the Liouville theorem at order zero: a harmonic function on the
cluster with `|v(x)| ≤ ε |x|` far from the origin, for every `ε > 0`, is a corrected plane of slope
zero, as is the constant `v(o)`, so the two agree.

Together with the existence of planar Green columns (`planar_greenColumn_exists`), this gives the
planar existence and uniqueness of Green columns (Dario–Gu, p. 4): two Green columns with the same
pole differ by a harmonic function of sublinear growth vanishing at the pole.
-/

namespace Rigidity.Green

open MeasureTheory LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

variable {ω : Configuration 2}

/-- The uniqueness of the zero-slope corrected plane normalized at each vertex gives the Liouville
theorem at order zero on the component. -/
theorem hasSublinearLiouville_of_existsUnique_correctedPlane {C : OpenComponent ω}
    (hC : ∀ o : C, ∃! u : C → ℝ, IsCorrectedPlane C 0 u ∧ u o = 0) :
    HasSublinearLiouville C := by
  intro v hv hsub
  rcases isEmpty_or_nonempty C with hE | ⟨⟨o⟩⟩
  · exact ⟨0, fun x => (IsEmpty.false x).elim⟩
  have hs : componentSlopeAsymptotics C 0 v :=
    Rigidity.Proofs.Section5.componentSlopeAsymptotics_zero_of_sublinear C v hsub
  have hv1 : IsCorrectedPlane C 0 v :=
    ⟨(mem_harmonicGrowthSpace_iff C 1 v).2
      ⟨hv, componentL2Subpolynomial_one_of_slope_asymptotics C 0 v hs⟩, hs⟩
  have hw : IsCorrectedPlane C 0 (v - fun _ => v o) := by
    simpa only [sub_zero] using isCorrectedPlane_sub C hv1 (isCorrectedPlane_const C (v o))
  have h0 : IsCorrectedPlane C 0 (fun _ => (0 : ℝ)) := isCorrectedPlane_const C 0
  have heq : (v - fun _ => v o) = fun _ => (0 : ℝ) :=
    (hC o).unique ⟨hw, by simp⟩ ⟨h0, rfl⟩
  refine ⟨v o, fun x => ?_⟩
  have hx := congrFun heq x
  simp only [Pi.sub_apply] at hx
  linarith

/-- The planar qualitative corrector input gives the order-zero Liouville theorem on the planar
infinite cluster. -/
theorem sublinearLiouville_two_of_correctorInput
    (hC : Rigidity.External.SupercriticalBondCorrectorInputTwo) (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : SublinearLiouville p := by
  filter_upwards [hC p hpc hp1] with ω hω h
  exact hasSublinearLiouville_of_existsUnique_correctedPlane fun o => (hω h).1 0 o

/-- **Existence and uniqueness of planar Green columns from the corrector input** (Dario–Gu, p. 4,
in dimension two): the existence of planar Green columns and the uniqueness of the zero-slope
corrected plane give the planar Green-column input. -/
theorem supercriticalBondGreenColumnExistenceTwo_of_correctorInput
    (hC : Rigidity.External.SupercriticalBondCorrectorInputTwo) :
    Rigidity.External.SupercriticalBondGreenColumnExistenceTwo := by
  intro p hpc hp1 y
  filter_upwards [Rigidity.Proofs.Section5.planar_greenColumn_exists p hpc hp1 y,
    sublinearLiouville_two_of_correctorInput hC p hpc hp1] with ω hEω hLω
  intro h hy
  obtain ⟨g, hg⟩ := hEω h hy
  exact ⟨g, hg, fun g' hg' => Rigidity.Proofs.Section5.eq_of_isGreenColumn (hLω h) hg' hg⟩

end Rigidity.Green

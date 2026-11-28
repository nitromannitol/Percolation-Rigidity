import Rigidity.Proofs.Green.GeneralFluxSpatialAverage
import Rigidity.Proofs.Green.DarioGuFluxSpatialAverage

/-!
# The variance bound of Gu in dimension two

The statement `FluxVarianceBoundD d p` used in Proposition 2.13 on `ℤ^d` (the variance bound
(3.4) of Gu's proof of his Proposition 1.1) holds in dimension two (`fluxVarianceBoundD_two`): at
`d = 2` the flux `fluxValD`, its heat average `fluxObsD` and the resampling variance of
`Rigidity.Corrector.GeneralDim.resampleVar` are the planar objects `fluxVal`, `fluxObs` and
`Rigidity.Corrector.resampleVar` (`fluxObsD_two_eq`, `resampleVar_two_eq`), the variance is at most
the sum of the squared flip differences (`ae_resampleVar_le_tsum_bondFlipDiff`), and that sum is
`O_s(C/r²)` (`fluxFlipSum_isOsBond`, through the Step 2 sum of Dario's Lemma 3.3 in dimension two).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green.GeneralFlux

section Two

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

theorem zdHeat_two_eq_latticeHeat (t : ℝ) (x y : Vertex 2) :
    Rigidity.Poincare.GeneralDim.zdHeat 2 t x y = Rigidity.Corrector.latticeHeat t x y := rfl

theorem fluxValD_two_eq (k : Fin 2) (ω : Configuration 2) (z : Vertex 2) (i : Fin 2) :
    fluxValD hG hGv k ω z i = Rigidity.Green.fluxVal hG hGv k ω (z, i) := rfl

theorem fluxObsD_two_eq (k i : Fin 2) (r : ℝ) (x : Vertex 2) :
    fluxObsD hG hGv k i r x = Rigidity.Green.fluxObs hG hGv k i r x := rfl

theorem resampleVar_two_eq (p : unitInterval) (X : Configuration 2 → ℝ) :
    Rigidity.Corrector.GeneralDim.resampleVar p X = Rigidity.Corrector.resampleVar p X := rfl

end Two

/-- **The variance bound (3.4) of Gu in dimension two**: `FluxVarianceBoundD 2 p` holds for every
supercritical `p < 1`. -/
theorem fluxVarianceBoundD_two {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : FluxVarianceBoundD 2 p := by
  intro G hG hGv hGae
  obtain ⟨s, C, hs, hC, hV⟩ := Rigidity.Green.fluxFlipSum_isOsBond hG hGv hpc hp1 hGae
  obtain ⟨abar, -, habar⟩ := exists_fluxMeanD (p := p) le_rfl hpc hp1
  refine ⟨s, C, hs, hC, fun k i r hr x => ?_⟩
  obtain ⟨hfin, hOs⟩ := hV k i r hr x
  have hr0 : 0 < r := by linarith
  have hXm : Measurable (Rigidity.Green.fluxObs hG hGv k i r x) :=
    Rigidity.Green.measurable_fluxObs hG hGv k i r x
  have hXi : Integrable (Rigidity.Green.fluxObs hG hGv k i r x) (latticeBondLaw 2 p) := by
    rw [← fluxObsD_two_eq hG hGv]
    exact (integral_fluxObsD hG hGv hGae habar k i r x).1
  have hres := Rigidity.Corrector.ae_resampleVar_le_tsum_bondFlipDiff p hXm hXi
  rw [fluxObsD_two_eq hG hGv, resampleVar_two_eq, Real.rpow_natCast]
  refine ⟨?_, ?_⟩
  · filter_upwards [hres, hfin] with ω h1 h2
    exact h1.trans_lt h2
  · refine Rigidity.Corrector.isOsBond_of_ae_le hs (by positivity)
      (Rigidity.Corrector.measurable_resampleVar p hXm).ennreal_toReal ?_ hOs
    filter_upwards [hres, hfin] with ω h1 h2
    exact ENNReal.toReal_mono h2.ne h1

end Rigidity.Green.GeneralFlux

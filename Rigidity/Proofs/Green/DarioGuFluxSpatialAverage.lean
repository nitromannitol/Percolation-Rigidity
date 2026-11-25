import Rigidity.Proofs.Green.DarioGuFluxFlipMoments
import Rigidity.Proofs.Green.DarioGuFluxMean
import Rigidity.Proofs.Corrector.ConcentrationTwoHolds

/-!
# The spatial average of the flux on the infinite cluster in dimension two

**Gu, Proposition 1.1** (*An efficient algorithm for solving elliptic problems on percolation
clusters*, arXiv:1907.13571, (1.7)), in dimension two with the heat kernel `Φ_{r²}` of `ℤ²` as the
kernel `K_R`, `R = r`: the spatial average of the centered flux
`g_{e_k} = a(Dχ_{e_k} + e_k) - ā e_k` satisfies `|Φ_{r²} ⋆ [g_{e_k}]_i(x)| ≤ O_s(C/r)`
(`exists_fluxSpatialAverage_two`). Here `ā` is the mean of the flux (`exists_fluxMean_two`), the
flux vanishes off the infinite cluster, and the kernel is the discrete heat kernel on the lattice
points instead of a continuous kernel against the piecewise constant extension; `R^{-d/2} = 1/r`.

The proof is Gu's (Step 1): the exponential Efron–Stein inequality (Proposition 2.17 of Dario,
`concentrationTwo_holds`) with the mean `E[X] = ā δ_{ik}` (`integral_fluxObs`, by the stationarity
of the corrector, `fluxVal_translation`) and the variance `𝕍[X] ≤ Σ_e (D_e X)² ≤ O_s(C/r²)`
(`ae_resampleVar_le_tsum_bondFlipDiff`, `fluxFlipSum_isOsBond`), as in the proof of Dario's
Proposition 3.1 (`darioPropThreeOneTwo_of_lemmas`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.Corrector Rigidity.External Rigidity.Section3 Rigidity.Steps.S3
open scoped Classical ENNReal

section Average

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

theorem edgeHead_add (z t : Vertex 2) (i : Fin 2) :
    edgeHead ((z + t, i) : LatticeEdge) = edgeHead (z, i) + t := by
  simp only [edgeHead]
  abel

/-- **Stationarity of the flux**: the flux of the translated configuration at the translated edge. -/
theorem fluxVal_translation {k : Fin 2} {ω : Configuration 2} (t : Vertex 2) (hω : ω ∈ G)
    (hω' : configurationTranslation t ω ∈ G) (z : Vertex 2) (i : Fin 2) :
    fluxVal hG hGv k (configurationTranslation t ω) (z + t, i) = fluxVal hG hGv k ω (z, i) := by
  unfold fluxVal
  have hopen : EdgeOpen (configurationTranslation t ω) (z + t, i) ↔ EdgeOpen ω (z, i) := by
    unfold EdgeOpen
    rw [edgeHead_add]
    exact openGraph_adj_translation_iff t ω z (edgeHead (z, i))
  have hinf : configurationTranslation t ω ∈ infiniteComponentEvent ((z + t, i) : LatticeEdge).1 ↔
      ω ∈ infiniteComponentEvent z := by
    rw [Rigidity.Proofs.S3.HomogenizedCoefficient.infiniteComponentEvent_translation_iff]
    simp
  by_cases hc : EdgeOpen ω (z, i) ∧ ω ∈ infiniteComponentEvent z
  · rw [if_pos ⟨hopen.2 hc.1, hinf.2 hc.2⟩, if_pos hc]
    set K := (openGraph ω).connectedComponentMk z
    have hzK : z ∈ K.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    have hyK : edgeHead (z, i) ∈ K.supp := K.mem_supp_of_adj_mem_supp hzK hc.1
    have hKinf : K.supp.Infinite := hc.2
    have h := correctorDiff_translation hG hGv (q := Pi.single k 1) t hω hω' hKinf
      ⟨edgeHead (z, i), hyK⟩ ⟨z, hzK⟩
    simp only at h
    rw [edgeHead_add, h]
  · rw [if_neg (fun h => hc ⟨hopen.1 h.1, hinf.1 h.2⟩), if_neg hc]

theorem planeFlux_zero_eq_edgeDifference {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ)
    (i : Fin 2) : planeFlux C u ((0 : Vertex 2), i) = edgeDifference C u (unit i) 0 := by
  unfold planeFlux edgeDifference
  have hh : edgeHead (((0 : Vertex 2), i) : LatticeEdge) = unit i := by
    simp [edgeHead, LatticeProb.unit]
  rw [hh]
  have hiff : (EdgeOpen ω ((0 : Vertex 2), i) ∧ ((0 : Vertex 2), i).1 ∈ C.supp) ↔
      (unit i ∈ C.supp ∧ (openGraph ω).Adj (unit i) 0) := by
    unfold EdgeOpen
    rw [hh]
    constructor
    · rintro ⟨ha, h0⟩
      exact ⟨C.mem_supp_of_adj_mem_supp h0 ha, ha.symm⟩
    · rintro ⟨h1, ha⟩
      exact ⟨ha.symm, C.mem_supp_of_adj_mem_supp h1 ha⟩
  by_cases hc : unit i ∈ C.supp ∧ (openGraph ω).Adj (unit i) 0
  · rw [if_pos (hiff.2 hc), if_pos hc]
    rfl
  · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]

/-- The flux at the origin is a flux field. -/
theorem isFluxField_fluxVal {p : unitInterval} (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G)
    (k i : Fin 2) :
    IsFluxField p (Pi.single k 1) (unit i) 0 fun ω => fluxVal hG hGv k ω ((0 : Vertex 2), i) := by
  filter_upwards [hGae] with ω hω h u hu
  rw [fluxVal_eq_planeFlux hG hGv hω h hu, planeFlux_zero_eq_edgeDifference]

theorem fluxVal_ae_eq_comp {p : unitInterval} (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G)
    (k i : Fin 2) (z : Vertex 2) :
    (fun ω => fluxVal hG hGv k ω (z, i)) =ᵐ[latticeBondLaw 2 p]
      fun ω => fluxVal hG hGv k (configurationTranslation (-z) ω) ((0 : Vertex 2), i) := by
  have h2 := (measurePreserving_configurationTranslation p (-z)).quasiMeasurePreserving.ae hGae
  filter_upwards [hGae, h2] with ω hω hω'
  have h := fluxVal_translation hG hGv (k := k) (-z) hω hω' z i
  rw [add_neg_cancel] at h
  exact h.symm

theorem lintegral_enorm_fluxVal_eq {p : unitInterval} (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G)
    (k i : Fin 2) (z : Vertex 2) :
    ∫⁻ ω, ‖fluxVal hG hGv k ω (z, i)‖ₑ ∂latticeBondLaw 2 p =
      ∫⁻ ω, ‖fluxVal hG hGv k ω ((0 : Vertex 2), i)‖ₑ ∂latticeBondLaw 2 p := by
  have hae : (fun ω => ‖fluxVal hG hGv k ω (z, i)‖ₑ) =ᵐ[latticeBondLaw 2 p]
      fun ω => ‖fluxVal hG hGv k (configurationTranslation (-z) ω) ((0 : Vertex 2), i)‖ₑ := by
    filter_upwards [fluxVal_ae_eq_comp hG hGv hGae k i z] with ω h
    rw [h]
  rw [lintegral_congr_ae hae]
  exact (measurePreserving_configurationTranslation p (-z)).lintegral_comp
    ((measurable_fluxVal hG hGv k ((0 : Vertex 2), i)).enorm)

/-- **The heat average of the flux is integrable with mean `ā δ_{ik}`.** -/
theorem integral_fluxObs {p : unitInterval} (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {abar : ℝ}
    (habar : ∀ (k i : Fin 2) (X : Configuration 2 → ℝ),
      IsFluxField p (Pi.single k 1) (unit i) 0 X →
        Integrable X (latticeBondLaw 2 p) ∧
          ∫ ω, X ω ∂latticeBondLaw 2 p = if i = k then abar else 0)
    (k i : Fin 2) (r : ℝ) (x : Vertex 2) :
    Integrable (fluxObs hG hGv k i r x) (latticeBondLaw 2 p) ∧
      ∫ ω, fluxObs hG hGv k i r x ω ∂latticeBondLaw 2 p = if i = k then abar else 0 := by
  set μ := latticeBondLaw 2 p
  obtain ⟨hi0, hm0⟩ := habar k i _ (isFluxField_fluxVal hG hGv hGae k i)
  set c := ∫⁻ ω, ‖fluxVal hG hGv k ω ((0 : Vertex 2), i)‖ₑ ∂μ
  have hc : c ≠ ∞ := (hi0.2).ne
  have hFm : ∀ z, Measurable fun ω => latticeHeat (r ^ 2) x z * fluxVal hG hGv k ω (z, i) :=
    fun z => (measurable_fluxVal hG hGv k (z, i)).const_mul _
  have hsum : ∑' z, ∫⁻ ω, ‖latticeHeat (r ^ 2) x z * fluxVal hG hGv k ω (z, i)‖ₑ ∂μ = c := by
    have e : ∀ z, ∫⁻ ω, ‖latticeHeat (r ^ 2) x z * fluxVal hG hGv k ω (z, i)‖ₑ ∂μ =
        ENNReal.ofReal (latticeHeat (r ^ 2) x z) * c := by
      intro z
      simp only [enorm_mul]
      rw [lintegral_const_mul _ (measurable_fluxVal hG hGv k (z, i)).enorm,
        lintegral_enorm_fluxVal_eq hG hGv hGae k i z,
        Real.enorm_of_nonneg (latticeHeat_nonneg (sq_nonneg r) x z)]
    rw [tsum_congr e, ENNReal.tsum_mul_right, tsum_ofReal_latticeHeat (sq_nonneg r) x, one_mul]
  have hint : Integrable (fluxObs hG hGv k i r x) μ := by
    refine ⟨(measurable_fluxObs hG hGv k i r x).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral fluxObs
    calc ∫⁻ ω, ‖∑' z, latticeHeat (r ^ 2) x z * fluxVal hG hGv k ω (z, i)‖ₑ ∂μ
        ≤ ∫⁻ ω, ∑' z, ‖latticeHeat (r ^ 2) x z * fluxVal hG hGv k ω (z, i)‖ₑ ∂μ :=
          lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
      _ = ∑' z, ∫⁻ ω, ‖latticeHeat (r ^ 2) x z * fluxVal hG hGv k ω (z, i)‖ₑ ∂μ :=
          lintegral_tsum fun z => (hFm z).enorm.aemeasurable
      _ = c := hsum
      _ < ∞ := lt_top_iff_ne_top.2 hc
  refine ⟨hint, ?_⟩
  unfold fluxObs
  rw [integral_tsum (fun z => (hFm z).aestronglyMeasurable) (by rw [hsum]; exact hc)]
  have e : ∀ z, ∫ ω, latticeHeat (r ^ 2) x z * fluxVal hG hGv k ω (z, i) ∂μ =
      latticeHeat (r ^ 2) x z * (if i = k then abar else 0) := by
    intro z
    rw [integral_const_mul, integral_congr_ae (fluxVal_ae_eq_comp hG hGv hGae k i z),
      Rigidity.Proofs.S3.FluxEvent.integral_comp_mp (measurePreserving_configurationTranslation p (-z))
        (measurable_fluxVal hG hGv k ((0 : Vertex 2), i)).aestronglyMeasurable, hm0]
  rw [tsum_congr e, tsum_mul_right, tsum_latticeHeat (sq_nonneg r) x, one_mul]

/-- **Gu, Proposition 1.1, in dimension two**: the heat averages of the centered flux are
`O_s(C/r)`. -/
theorem exists_fluxSpatialAverage_two {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ abar s C : ℝ, 0 < abar ∧ 0 < s ∧ 0 < C ∧ ∀ (k i : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
      IsOsBond 2 p (fun ω => |fluxObs hG hGv k i r x ω - if i = k then abar else 0|) s (C / r) := by
  obtain ⟨abar, habar0, habar⟩ := exists_fluxMean_two hpc hp1
  obtain ⟨s₁, C₁, hs₁, hC₁, hV⟩ := fluxFlipSum_isOsBond hG hGv hpc hp1 hGae
  obtain ⟨A, hA, hmomX⟩ := lintegral_abs_sub_integral_rpow_le p concentrationTwo_holds hs₁
  set κ : ℝ := (1 + s₁) / (2 * s₁) with hκ
  have hκ0 : 0 < κ := by positivity
  set B : ℝ := A * Real.sqrt C₁ with hB
  have hB0 : 0 < B := by positivity
  have hs' : 0 < 1 / (2 * κ) := by positivity
  have hsk : 1 / (2 * κ) * κ < 1 := by
    rw [one_div_mul_eq_div, div_lt_one (by positivity)]
    linarith
  obtain ⟨C, hC, hmom⟩ := isOsBond_of_moment_le (d := 2) (p := p) hB0 hs' hsk
  refine ⟨abar, 1 / (2 * κ), C, habar0, hs', hC, fun k i r hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  set X := fluxObs hG hGv k i r x
  have hXm : Measurable X := measurable_fluxObs hG hGv k i r x
  obtain ⟨hXi, hXmean⟩ := integral_fluxObs hG hGv hGae habar k i r x
  -- the variance
  have hres := ae_resampleVar_le_tsum_bondFlipDiff p hXm hXi
  obtain ⟨hfin, hOs⟩ := hV k i r hr x
  have hresfin : ∀ᵐ ω ∂latticeBondLaw 2 p, resampleVar p X ω < ∞ := by
    filter_upwards [hres, hfin] with ω h1 h2
    exact h1.trans_lt h2
  have hresOs : IsOsBond 2 p (fun ω => (resampleVar p X ω).toReal) s₁ (C₁ / r ^ 2) := by
    refine isOsBond_of_ae_le hs₁ (by positivity) (measurable_resampleVar p hXm).ennreal_toReal ?_
      hOs
    filter_upwards [hres, hfin] with ω h1 h2
    exact ENNReal.toReal_mono h2.ne h1
  have hθ : 0 < C₁ / r ^ 2 := by positivity
  have hm := hmomX X (C₁ / r ^ 2) hθ hXi hresfin hresOs
  rw [hXmean] at hm
  -- `r |X - E X|` has moments of polynomial growth
  refine isOsBond_div_of_mul (isOsBond_of_ae_ofReal_le hB0.le hmom
    (measurable_const.mul ((hXm.sub measurable_const).abs))
    (fun ω => mul_nonneg hr0.le (abs_nonneg _)) (T := fun ω => ENNReal.ofReal
      (r * |X ω - if i = k then abar else 0|)) (Eventually.of_forall fun ω => le_rfl)
    fun q hq => ?_)
  have hq0 : 0 < q := by linarith
  calc ∫⁻ ω, ENNReal.ofReal (r * |X ω - if i = k then abar else 0|) ^ q ∂latticeBondLaw 2 p
      = ∫⁻ ω, ENNReal.ofReal (r ^ q) * ENNReal.ofReal (|X ω - if i = k then abar else 0| ^ q)
          ∂latticeBondLaw 2 p := by
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le,
          Real.mul_rpow hr0.le (abs_nonneg _), ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (r ^ q) * ∫⁻ ω, ENNReal.ofReal (|X ω - if i = k then abar else 0| ^ q)
          ∂latticeBondLaw 2 p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (r ^ q) * ENNReal.ofReal
          ((A * Real.sqrt (C₁ / r ^ 2) * q ^ κ) ^ q) := mul_le_mul_right (hm q hq) _
    _ = ENNReal.ofReal ((B * q ^ κ) ^ q) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hr0.le (by positivity),
          Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr0.le, hB]
        congr 2
        field_simp

end Average

end Rigidity.Green

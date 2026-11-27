import Rigidity.Proofs.Green.GeneralFluxMean
import Rigidity.Proofs.Green.GeneralFluxWeakNormStatement
import Rigidity.Proofs.Corrector.GeneralPropThreeOne

/-!
# The flux of the correctors on `ℤ^d` and its heat average as random variables

The extension of `DarioGuFluxObservable.lean` and of the first part of
`DarioGuFluxSpatialAverage.lean` from `ℤ²` to `ℤ^d`. On a measurable conull set `G` of
configurations where the qualitative corrector input holds, the flux of the corrected plane of slope
`e_k` along the edge `(z, z + e_i)` is the measurable function `fluxValD k ω z i`, built from the
measurable corrector increments `correctorDiff`:

* `fluxValD_eq_edgeDifference`: it is `ℓ(z + e_i) - ℓ(z)` on the open edges of the infinite cluster
  and `0` elsewhere, for every corrected plane `ℓ` of slope `e_k`;
* `centeredFluxD_eq_fluxValD`: on the infinite cluster it is the `i`-th component of the flux
  `a(Dχ_{e_k} + e_k)` of Dario–Gu, so the centered flux `g̃_{e_k}` is `fluxValD - (σ/2) δ_{ik}`;
* `fluxValD_translation`: the stationarity of the flux, from (2.3) of the corrector;
* `fluxObsD k i r x = Σ_z Φ_{r²}(x, z) fluxValD(z, i)` (the random variable `X = K_R ⋆ [g_p](x)`
  of Gu's proof of Proposition 1.1, before centering), with `Φ` the heat kernel of `ℤ^d`; it is
  measurable and integrable with mean `ā δ_{ik}` (`integral_fluxObsD`, from `exists_fluxMeanD`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3
  Rigidity.Corrector Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

section Observable

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The flux of the corrected plane of slope `e_k` along the edge `(z, z + e_i)`, through the
measurable corrector increments: `χ_{e_k}(z + e_i) - χ_{e_k}(z) + δ_{ik}` on the open edges of the
infinite cluster, `0` elsewhere. -/
noncomputable def fluxValD (k : Fin d) (ω : Configuration d) (z : Vertex d) (i : Fin d) : ℝ :=
  if (openGraph ω).Adj z (z + unit i) ∧ ω ∈ infiniteComponentEvent z then
    correctorDiff hG hGv (Pi.single k 1) ω (z + unit i) z + (if i = k then 1 else 0)
  else 0

theorem measurableSet_openAdj (z y : Vertex d) :
    MeasurableSet {ω : Configuration d | (openGraph ω).Adj z y} := by
  by_cases hzy : (nearestNeighborGraph d).Adj z y
  · have e : {ω : Configuration d | (openGraph ω).Adj z y} =
        (fun ω : Configuration d => ω (bondOfAdjacent hzy)) ⁻¹' {true} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, hh⟩
        exact hh
      · intro hh
        exact ⟨hzy, hh⟩
    rw [e]
    exact (measurable_pi_apply _) (measurableSet_singleton true)
  · have e : {ω : Configuration d | (openGraph ω).Adj z y} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hzy h.1
    rw [e]
    exact MeasurableSet.empty

theorem measurable_fluxValD (k : Fin d) (z : Vertex d) (i : Fin d) :
    Measurable fun ω => fluxValD hG hGv k ω z i := by
  unfold fluxValD
  exact Measurable.ite ((measurableSet_openAdj z (z + unit i)).inter
    (measurableSet_infiniteComponentEvent z))
    ((measurable_correctorDiff hG hGv _ _ _).add_const _) measurable_const

theorem cast_add_unit_apply (z : Vertex d) (i k : Fin d) :
    (((z + unit i) k : ℤ) : ℝ) = ((z k : ℤ) : ℝ) + (if i = k then 1 else 0) := by
  by_cases hik : i = k
  · subst hik
    simp [LatticeProb.unit]
  · simp [LatticeProb.unit, Ne.symm hik, hik]

theorem sum_single_mulD (i : Fin d) (v : Vertex d) :
    ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * (v j : ℝ) = v i := by
  simp [Pi.single_apply]

theorem sum_abs_singleD (i : Fin d) : ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j| = 1 := by
  simp [Pi.single_apply, apply_ite]

theorem sum_single_mul_add_unit_sub (k i : Fin d) (z : Vertex d) :
    ∑ j, (Pi.single k (1 : ℝ) : Fin d → ℝ) j * (((z + unit i) j : ℤ) : ℝ) -
        ∑ j, (Pi.single k (1 : ℝ) : Fin d → ℝ) j * ((z j : ℤ) : ℝ) =
      if i = k then 1 else 0 := by
  rw [sum_single_mulD, sum_single_mulD, cast_add_unit_apply]
  ring

/-- **The measurable flux is the flux of the corrected plane.** -/
theorem fluxValD_eq_edgeDifference {k : Fin d} {ω : Configuration d} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single k 1) ℓ) (z : Vertex d)
    (i : Fin d) :
    fluxValD hG hGv k ω z i = edgeDifference (uniqueInfiniteComponent h) ℓ (z + unit i) z := by
  unfold fluxValD edgeDifference
  have e : ((openGraph ω).Adj z (z + unit i) ∧ ω ∈ infiniteComponentEvent z) ↔
      (z + unit i ∈ (uniqueInfiniteComponent h).supp ∧ (openGraph ω).Adj (z + unit i) z) := by
    rw [← mem_uniqueInfiniteComponent_iff h z]
    constructor
    · rintro ⟨ha, hz⟩
      exact ⟨(uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hz ha, ha.symm⟩
    · rintro ⟨hy, ha⟩
      exact ⟨ha.symm, (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hy ha⟩
  by_cases hc : z + unit i ∈ (uniqueInfiniteComponent h).supp ∧
      (openGraph ω).Adj (z + unit i) z
  · rw [if_pos (e.2 hc), if_pos hc]
    have hz : z ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hc.1 hc.2
    rw [correctorDiff_eq hG hGv hω (uniqueInfiniteComponent_infinite h) hℓ ⟨z + unit i, hc.1⟩
      ⟨z, hz⟩]
    have ea : Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ (z + unit i) =
        ℓ ⟨z + unit i, hc.1⟩ := dif_pos hc.1
    have eb : Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ z = ℓ ⟨z, hz⟩ := dif_pos hz
    rw [ea, eb]
    have hs := sum_single_mul_add_unit_sub k i z
    linarith
  · rw [if_neg (fun h' => hc (e.1 h')), if_neg hc]

/-- **Stationarity of the flux**: the flux of the translated configuration at the translated
edge. -/
theorem fluxValD_translation {k : Fin d} {ω : Configuration d} (t : Vertex d) (hω : ω ∈ G)
    (hω' : configurationTranslation t ω ∈ G) (z : Vertex d) (i : Fin d) :
    fluxValD hG hGv k (configurationTranslation t ω) (z + t) i = fluxValD hG hGv k ω z i := by
  unfold fluxValD
  have e1 : z + t + unit i = z + unit i + t := by abel
  have hopen : (openGraph (configurationTranslation t ω)).Adj (z + t) (z + t + unit i) ↔
      (openGraph ω).Adj z (z + unit i) := by
    rw [e1]
    exact openGraph_adj_translation_iff t ω z (z + unit i)
  have hinf : configurationTranslation t ω ∈ infiniteComponentEvent (z + t) ↔
      ω ∈ infiniteComponentEvent z := by
    rw [Rigidity.Proofs.S3.HomogenizedCoefficient.infiniteComponentEvent_translation_iff]
    simp
  by_cases hc : (openGraph ω).Adj z (z + unit i) ∧ ω ∈ infiniteComponentEvent z
  · rw [if_pos ⟨hopen.2 hc.1, hinf.2 hc.2⟩, if_pos hc]
    set K := (openGraph ω).connectedComponentMk z
    have hzK : z ∈ K.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    have hyK : z + unit i ∈ K.supp := K.mem_supp_of_adj_mem_supp hzK hc.1
    have hKinf : K.supp.Infinite := hc.2
    have h := correctorDiff_translation hG hGv (q := Pi.single k 1) t hω hω' hKinf
      ⟨z + unit i, hyK⟩ ⟨z, hzK⟩
    simp only at h
    rw [e1, h]
  · rw [if_neg (fun h => hc ⟨hopen.1 h.1, hinf.1 h.2⟩), if_neg hc]

/-- The flux at the origin is a flux field. -/
theorem isFluxFieldD_fluxValD {p : unitInterval} (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G)
    (k i : Fin d) :
    IsFluxFieldD p (Pi.single k 1) (unit i) 0 fun ω => fluxValD hG hGv k ω 0 i := by
  filter_upwards [hGae] with ω hω h u hu
  rw [fluxValD_eq_edgeDifference hG hGv hω h hu, zero_add]

/-- **The centered flux of Dario–Gu is the measurable flux minus `(σ/2) δ_{ik}`** on the infinite
cluster. -/
theorem centeredFluxD_eq_fluxValD {ω : Configuration d} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {y : Vertex d} {χ : Fin d → Vertex d → ℝ}
    (hχ : IsDGCorrectorD (uniqueInfiniteComponent h) y χ) (σ : ℝ) (k i : Fin d) {z : Vertex d}
    (hz : z ∈ (uniqueInfiniteComponent h).supp) :
    centeredFluxD ω σ χ k i z = fluxValD hG hGv k ω z i - σ / 2 * (if i = k then 1 else 0) := by
  rw [fluxValD_eq_edgeDifference hG hGv hω h (hχ k).1 z i]
  unfold centeredFluxD edgeDifference
  rw [show (unit i : Vertex d) = Pi.single i 1 from rfl]
  congr 1
  by_cases hadj : (openGraph ω).Adj z (z + Pi.single i 1)
  · have hy : z + Pi.single i 1 ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hz hadj
    have hc : z + Pi.single i 1 ∈ (uniqueInfiniteComponent h).supp ∧
        (openGraph ω).Adj (z + Pi.single i 1) z := ⟨hy, hadj.symm⟩
    rw [if_pos hadj, if_pos hc]
    have ea : Rigidity.Section3.extend (uniqueInfiniteComponent h)
        (fun a => (a.val k : ℝ) + χ k a.val) (z + Pi.single i 1) =
        (((z + Pi.single i 1 : Vertex d) k : ℤ) : ℝ) + χ k (z + Pi.single i 1) := dif_pos hy
    have eb : Rigidity.Section3.extend (uniqueInfiniteComponent h)
        (fun a => (a.val k : ℝ) + χ k a.val) z = ((z k : ℤ) : ℝ) + χ k z := dif_pos hz
    rw [ea, eb, show (z + Pi.single i 1 : Vertex d) = z + unit i from rfl, cast_add_unit_apply]
    ring
  · rw [if_neg hadj, if_neg (fun hc => hadj hc.2.symm)]

/-- **The heat average of the flux**, `X = Σ_z Φ_{r²}(x, z) flux_{e_k}(z, i)`. -/
noncomputable def fluxObsD (k i : Fin d) (r : ℝ) (x : Vertex d) (ω : Configuration d) : ℝ :=
  ∑' z, zdHeat d (r ^ 2) x z * fluxValD hG hGv k ω z i

theorem measurable_fluxObsD (k i : Fin d) (r : ℝ) (x : Vertex d) :
    Measurable (fluxObsD hG hGv k i r x) := by
  unfold fluxObsD
  exact Measurable.tsum fun z => (measurable_fluxValD hG hGv k z i).const_mul _

theorem fluxValD_ae_eq_comp {p : unitInterval} (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G)
    (k i : Fin d) (z : Vertex d) :
    (fun ω => fluxValD hG hGv k ω z i) =ᵐ[latticeBondLaw d p]
      fun ω => fluxValD hG hGv k (configurationTranslation (-z) ω) 0 i := by
  have h2 := (measurePreserving_configurationTranslation p (-z)).quasiMeasurePreserving.ae hGae
  filter_upwards [hGae, h2] with ω hω hω'
  have h := fluxValD_translation hG hGv (k := k) (-z) hω hω' z i
  rw [add_neg_cancel] at h
  exact h.symm

theorem lintegral_enorm_fluxValD_eq {p : unitInterval}
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (k i : Fin d) (z : Vertex d) :
    ∫⁻ ω, ‖fluxValD hG hGv k ω z i‖ₑ ∂latticeBondLaw d p =
      ∫⁻ ω, ‖fluxValD hG hGv k ω 0 i‖ₑ ∂latticeBondLaw d p := by
  have hae : (fun ω => ‖fluxValD hG hGv k ω z i‖ₑ) =ᵐ[latticeBondLaw d p]
      fun ω => ‖fluxValD hG hGv k (configurationTranslation (-z) ω) 0 i‖ₑ := by
    filter_upwards [fluxValD_ae_eq_comp hG hGv hGae k i z] with ω h
    rw [h]
  rw [lintegral_congr_ae hae]
  exact (measurePreserving_configurationTranslation p (-z)).lintegral_comp
    ((measurable_fluxValD hG hGv k 0 i).enorm)

/-- **The heat average of the flux is integrable with mean `ā δ_{ik}`.** -/
theorem integral_fluxObsD [NeZero d] {p : unitInterval}
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {abar : ℝ}
    (habar : ∀ (k i : Fin d) (X : Configuration d → ℝ),
      IsFluxFieldD p (Pi.single k 1) (unit i) 0 X →
        Integrable X (latticeBondLaw d p) ∧
          ∫ ω, X ω ∂latticeBondLaw d p = if i = k then abar else 0)
    (k i : Fin d) (r : ℝ) (x : Vertex d) :
    Integrable (fluxObsD hG hGv k i r x) (latticeBondLaw d p) ∧
      ∫ ω, fluxObsD hG hGv k i r x ω ∂latticeBondLaw d p = if i = k then abar else 0 := by
  set μ := latticeBondLaw d p
  obtain ⟨hi0, hm0⟩ := habar k i _ (isFluxFieldD_fluxValD hG hGv hGae k i)
  set c := ∫⁻ ω, ‖fluxValD hG hGv k ω 0 i‖ₑ ∂μ
  have hc : c ≠ ∞ := (hi0.2).ne
  have hFm : ∀ z, Measurable fun ω => zdHeat d (r ^ 2) x z * fluxValD hG hGv k ω z i :=
    fun z => (measurable_fluxValD hG hGv k z i).const_mul _
  have hsum : ∑' z, ∫⁻ ω, ‖zdHeat d (r ^ 2) x z * fluxValD hG hGv k ω z i‖ₑ ∂μ = c := by
    have e : ∀ z, ∫⁻ ω, ‖zdHeat d (r ^ 2) x z * fluxValD hG hGv k ω z i‖ₑ ∂μ =
        ENNReal.ofReal (zdHeat d (r ^ 2) x z) * c := by
      intro z
      simp only [enorm_mul]
      rw [lintegral_const_mul _ (measurable_fluxValD hG hGv k z i).enorm,
        lintegral_enorm_fluxValD_eq hG hGv hGae k i z,
        Real.enorm_of_nonneg (zdHeat_nonneg (sq_nonneg r) x z)]
    rw [tsum_congr e, ENNReal.tsum_mul_right, tsum_ofReal_zdHeat (sq_nonneg r) x, one_mul]
  have hint : Integrable (fluxObsD hG hGv k i r x) μ := by
    refine ⟨(measurable_fluxObsD hG hGv k i r x).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral fluxObsD
    calc ∫⁻ ω, ‖∑' z, zdHeat d (r ^ 2) x z * fluxValD hG hGv k ω z i‖ₑ ∂μ
        ≤ ∫⁻ ω, ∑' z, ‖zdHeat d (r ^ 2) x z * fluxValD hG hGv k ω z i‖ₑ ∂μ :=
          lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
      _ = ∑' z, ∫⁻ ω, ‖zdHeat d (r ^ 2) x z * fluxValD hG hGv k ω z i‖ₑ ∂μ :=
          lintegral_tsum fun z => (hFm z).enorm.aemeasurable
      _ = c := hsum
      _ < ∞ := lt_top_iff_ne_top.2 hc
  refine ⟨hint, ?_⟩
  unfold fluxObsD
  rw [integral_tsum (fun z => (hFm z).aestronglyMeasurable) (by rw [hsum]; exact hc)]
  have e : ∀ z, ∫ ω, zdHeat d (r ^ 2) x z * fluxValD hG hGv k ω z i ∂μ =
      zdHeat d (r ^ 2) x z * (if i = k then abar else 0) := by
    intro z
    rw [integral_const_mul, integral_congr_ae (fluxValD_ae_eq_comp hG hGv hGae k i z),
      Rigidity.Proofs.S3.FluxEvent.integral_comp_mp
        (measurePreserving_configurationTranslation p (-z))
        (measurable_fluxValD hG hGv k 0 i).aestronglyMeasurable, hm0]
  rw [tsum_congr e, tsum_mul_right, (hasSum_zdHeat (sq_nonneg r) x).tsum_eq, one_mul]

end Observable

end Rigidity.Green.GeneralFlux

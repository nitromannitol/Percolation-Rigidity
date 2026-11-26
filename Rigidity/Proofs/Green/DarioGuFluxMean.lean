import Rigidity.Proofs.S3.PlanarCoefficient
import Rigidity.Proofs.S3.Reflection
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds
import Rigidity.Proofs.Poincare.DarioStepTwoHolds
import PercolationClusterHomogenization.Proofs.Percolation.BondUniqueness

/-!
# The mean of the flux of the correctors in dimension two

For `𝔭_c(2) < p < 1` and the corrected planes `ℓ_k = x_k + χ_{e_k}` of the infinite cluster, the
flux along the edge `(0, e_i)` is `X_{k,i} = (ℓ_k(e_i) - ℓ_k(0)) 1{(e_i, 0) ∈ E(𝒞_∞)}`, the
`i`-th component of `a(Dχ_{e_k} + e_k)` at the origin. Its mean is `ā δ_{ik}` with `ā > 0`
(`exists_fluxMean_two`):

* `ā = E[X_{0,0}] > 0` is the planar homogenized coefficient
  (`Rigidity.Proofs.S3.homogenizedCoefficient_two`, with the corrector inputs proved);
* the transposition of the coordinates carries the corrected planes of slope `e₁` to those of
  slope `e₀` and the edge `(e₁, 0)` to `(e₀, 0)`, and preserves the law, so `E[X_{1,1}] = ā` and
  `E[X_{1,0}] = E[X_{0,1}]` (`isFluxField_comp_symm`);
* the reflection of the second coordinate fixes the slope `e₀` and carries `(-e₁, 0)` to
  `(e₁, 0)`, and the flux along `(-e₁, 0)` is minus the flux along `(e₁, 0)` of the translated
  configuration, so `E[X_{0,1}] = -E[X_{0,1}] = 0`.

This is the identity `E[a(Dχ_p + p)] = ā p` that Dario and Gu use for the centered flux
`g̃_p = a(Dχ_p + p) - (σ̄²/2) p` with `σ̄² = 2 θ(p)^{-1} ā` (*Quantitative homogenization of the
parabolic and elliptic Green's functions on percolation clusters*, (B.5), and C. Gu, *An
efficient algorithm for solving elliptic problems on percolation clusters*, the condition (3.3)
of the proof of Proposition 1.1, proved there in its Appendix C). Here `ā` is the mean of the flux,
and its positivity and isotropy are proved directly, without the identification with the
homogenized matrix of Armstrong and Dario.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3
open scoped Classical

namespace Rigidity.Green

open Rigidity.Proofs.S3 Rigidity.Proofs.S3.FluxEvent Rigidity.Proofs.S3.HomogenizedCoefficient

/-- `X` is almost surely the flux along `(a, b)` of the corrected planes of slope `q`: for every
corrected plane `u` of slope `q` on the infinite cluster, `X = (u(a) - u(b)) 1{(a, b) ∈ E(𝒞_∞)}`. -/
def IsFluxField (p : unitInterval) (q : Fin 2 → ℝ) (a b : Vertex 2)
    (X : Configuration 2 → ℝ) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ), IsCorrectedPlane (uniqueInfiniteComponent h) q u →
      X ω = edgeDifference (uniqueInfiniteComponent h) u a b

section Transport

variable (φ : nearestNeighborGraph 2 ≃g nearestNeighborGraph 2)

theorem mem_openComponentMap_supp_iff {ω : Configuration 2} (C : OpenComponent ω)
    (x : Vertex 2) : φ x ∈ (openComponentMap φ ω C).supp ↔ x ∈ C.supp := by
  constructor
  · intro h
    have h2 := ((SimpleGraph.ConnectedComponent.isoEquivSupp (openGraphMap φ ω) C).symm
      ⟨φ x, h⟩).2
    have e : (openGraphMap φ ω).symm (φ x) = x := (openGraphMap φ ω).symm_apply_apply x
    change (openGraphMap φ ω).symm (φ x) ∈ C.supp at h2
    rwa [e] at h2
  · intro h
    exact ((SimpleGraph.ConnectedComponent.isoEquivSupp (openGraphMap φ ω) C) ⟨x, h⟩).2

/-- The flux along an edge is carried along a lattice automorphism. -/
theorem edgeDifference_openComponentMap {ω : Configuration 2} (C : OpenComponent ω)
    (v : openComponentMap φ ω C → ℝ) (a b : Vertex 2) :
    edgeDifference (openComponentMap φ ω C) v (φ a) (φ b) =
      edgeDifference C (fun x => v (openComponentMapIso φ C x)) a b := by
  have hadj := openGraph_adj_configurationMap_iff φ ω a b
  unfold edgeDifference
  by_cases ha : a ∈ C.supp
  · have ha' := (mem_openComponentMap_supp_iff φ C a).2 ha
    by_cases hab : (openGraph ω).Adj a b
    · have hb : b ∈ C.supp := (C.mem_supp_congr_adj hab).1 ha
      have hb' := (mem_openComponentMap_supp_iff φ C b).2 hb
      rw [if_pos ⟨ha', hadj.2 hab⟩, if_pos ⟨ha, hab⟩]
      simp only [Section3.extend, dif_pos ha', dif_pos hb', dif_pos ha, dif_pos hb]
      rfl
    · rw [if_neg fun h => hab (hadj.1 h.2), if_neg fun h => hab h.2]
  · rw [if_neg fun h => ha ((mem_openComponentMap_supp_iff φ C a).1 h.1), if_neg fun h => ha h.1]

end Transport

/-- The flux along `(x, y)` is minus the flux along `(y, x)`. -/
theorem edgeDifference_swap {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ)
    (x y : Vertex 2) : edgeDifference C u x y = -edgeDifference C u y x := by
  unfold edgeDifference
  by_cases h : x ∈ C.supp ∧ (openGraph ω).Adj x y
  · have hy : y ∈ C.supp := (C.mem_supp_congr_adj h.2).1 h.1
    rw [if_pos h, if_pos ⟨hy, h.2.symm⟩]
    ring
  · have h' : ¬ (y ∈ C.supp ∧ (openGraph ω).Adj y x) := fun h' =>
      h ⟨(C.mem_supp_congr_adj h'.2).1 h'.1, h'.2.symm⟩
    rw [if_neg h, if_neg h', neg_zero]

section Fields

variable {p : unitInterval}

/-- **Transport of flux fields along signed permutations**: if `X` is the flux along `(a, b)` of
the corrected planes of slope `q`, then `X ∘ Φ⁻¹`, with `Φ` the action of the signed permutation
`φ` on the configurations, is the flux along `(φ a, φ b)` of the corrected planes of slope `φ_* q`. -/
theorem isFluxField_comp_symm (π : Equiv.Perm (Fin 2)) (s : Fin 2 → ℤˣ) {q : Fin 2 → ℝ}
    {a b : Vertex 2} {X : Configuration 2 → ℝ} (hX : IsFluxField p q a b X) :
    IsFluxField p (signedPermSlope π s q) (signedPermIso π s a) (signedPermIso π s b)
      (X ∘ (configurationMap (signedPermIso π s)).symm) := by
  set φ := signedPermIso π s
  set Φ := configurationMap φ
  have h1 : ∀ᵐ ω₀ ∂latticeBondLaw 2 p, ∀ (h : HasUniqueInfiniteOpenComponent (Φ ω₀))
      (u : uniqueInfiniteComponent h → ℝ),
      IsCorrectedPlane (uniqueInfiniteComponent h) (signedPermSlope π s q) u →
        X ω₀ = edgeDifference (uniqueInfiniteComponent h) u (φ a) (φ b) := by
    filter_upwards [hX] with ω₀ hω₀ h
    have h₀ : HasUniqueInfiniteOpenComponent ω₀ :=
      (hasUniqueInfiniteOpenComponent_configurationMap_iff φ ω₀).1 h
    have hD : openComponentMap φ ω₀ (uniqueInfiniteComponent h₀) = uniqueInfiniteComponent h :=
      openComponentMap_uniqueInfiniteComponent φ h₀
    rw [← hD]
    intro u hu
    rw [hω₀ h₀ _ (isCorrectedPlane_comp_signedPerm π s _ q u hu),
      edgeDifference_openComponentMap]
  have hmp := (measurePreserving_configurationMap φ p).symm Φ
  filter_upwards [hmp.quasiMeasurePreserving.ae h1] with ω hω
  rw [MeasurableEquiv.apply_symm_apply] at hω
  exact hω

/-- Two flux fields with the same slope and edge agree almost surely. -/
theorem IsFluxField.ae_eq (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {q : Fin 2 → ℝ} {a b : Vertex 2} {X Y : Configuration 2 → ℝ} (hX : IsFluxField p q a b X)
    (hY : IsFluxField p q a b Y) : X =ᵐ[latticeBondLaw 2 p] Y := by
  filter_upwards [hX, hY, Rigidity.Percolation.ae_hasUniqueInfiniteOpenComponent le_rfl hpc,
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds p hpc hp1] with
    ω hXω hYω h hC
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  obtain ⟨u, hu, -⟩ := (hC h).1 q ⟨o, ho⟩
  rw [hXω h u hu.1, hYω h u hu.1]

theorem signedPermSlope_swap_piSingle (k : Fin 2) :
    signedPermSlope (Equiv.swap 0 1) 1 (Pi.single k 1) = Pi.single (Equiv.swap 0 1 k) 1 := by
  funext i
  fin_cases k <;> fin_cases i <;> simp [signedPermSlope]

theorem signedPermIso_swap_unit (i : Fin 2) :
    signedPermIso (Equiv.swap 0 1) 1 (unit i : Vertex 2) = unit (Equiv.swap 0 1 i) := by
  funext j
  change ((1 : Fin 2 → ℤˣ) j : ℤ) * (unit i : Vertex 2) (Equiv.swap 0 1 j) = _
  fin_cases i <;> fin_cases j <;> simp [LatticeProb.unit]

theorem signedPermIso_zero_two (π : Equiv.Perm (Fin 2)) (s : Fin 2 → ℤˣ) :
    signedPermIso π s (0 : Vertex 2) = 0 :=
  signedPermIso_zero π s

theorem signedPermSlope_reflect_single_zero :
    signedPermSlope (Equiv.refl (Fin 2)) (Function.update 1 1 (-1)) (Pi.single 0 1) =
      Pi.single 0 1 := by
  funext i
  fin_cases i <;> simp [signedPermSlope]

theorem signedPermIso_reflect_neg_unit_one :
    signedPermIso (Equiv.refl (Fin 2)) (Function.update 1 1 (-1)) (-(unit 1 : Vertex 2)) =
      unit 1 := by
  funext j
  change ((Function.update (1 : Fin 2 → ℤˣ) 1 (-1) j : ℤˣ) : ℤ) *
    (-(unit 1 : Vertex 2)) (Equiv.refl (Fin 2) j) = _
  fin_cases j <;> simp [LatticeProb.unit]

/-- The swap transport of a flux field, with the slope and the edge in the form `e_{swap k}`,
`(e_{swap i}, 0)`. -/
theorem isFluxField_swap {k i : Fin 2} {X : Configuration 2 → ℝ}
    (hX : IsFluxField p (Pi.single k 1) (unit i) 0 X) :
    IsFluxField p (Pi.single (Equiv.swap 0 1 k) 1) (unit (Equiv.swap 0 1 i)) 0
      (X ∘ (configurationMap (signedPermIso (Equiv.swap 0 1) 1)).symm) := by
  have h := isFluxField_comp_symm (Equiv.swap 0 1) 1 hX
  rwa [signedPermSlope_swap_piSingle, signedPermIso_swap_unit, signedPermIso_zero_two] at h

theorem integrable_comp_symm (π : Equiv.Perm (Fin 2)) (s : Fin 2 → ℤˣ)
    {X : Configuration 2 → ℝ} (hX : Integrable X (latticeBondLaw 2 p)) :
    Integrable (X ∘ (configurationMap (signedPermIso π s)).symm) (latticeBondLaw 2 p) :=
  ((measurePreserving_configurationMap (signedPermIso π s) p).symm _).integrable_comp_of_integrable
    hX

theorem integrable_of_comp_symm (π : Equiv.Perm (Fin 2)) (s : Fin 2 → ℤˣ)
    {X : Configuration 2 → ℝ}
    (hX : Integrable (X ∘ (configurationMap (signedPermIso π s)).symm) (latticeBondLaw 2 p)) :
    Integrable X (latticeBondLaw 2 p) := by
  have := (measurePreserving_configurationMap (signedPermIso π s) p).integrable_comp_of_integrable
    hX
  simpa [Function.comp_def] using this

theorem integral_comp_symm (π : Equiv.Perm (Fin 2)) (s : Fin 2 → ℤˣ)
    {X : Configuration 2 → ℝ} (hX : Integrable X (latticeBondLaw 2 p)) :
    ∫ ω, (X ∘ (configurationMap (signedPermIso π s)).symm) ω ∂latticeBondLaw 2 p =
      ∫ ω, X ω ∂latticeBondLaw 2 p :=
  integral_comp_mp ((measurePreserving_configurationMap (signedPermIso π s) p).symm _)
    hX.aestronglyMeasurable

/-- **The off-diagonal flux of slope `e₀` has mean zero.** -/
theorem integral_fluxField_zero_one (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {X : Configuration 2 → ℝ} (hX : IsFluxField p (Pi.single 0 1) (unit 1) 0 X) :
    Integrable X (latticeBondLaw 2 p) ∧ ∫ ω, X ω ∂latticeBondLaw 2 p = 0 := by
  set μ := latticeBondLaw 2 p
  obtain ⟨G, hG, hG1, Φe, hΦm, hex, hΦ⟩ :=
    exists_edgeField_two Rigidity.Percolation.supercritical_bond_uniqueness
      Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds p hpc hp1
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := mem_ae_iff.2 ((prob_compl_eq_zero_iff hG).2 hG1)
  have hall : ∀ᵐ ω ∂μ, ∀ z, configurationTranslation z ω ∈ G :=
    ae_all_iff.2 fun z =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae hGae
  have hXi := integrable_edgeField_unit_two Rigidity.Poincare.correctorQuantitativeInputTwo_holds
    p hpc hp1 hGae hΦm hex hΦ 1
  -- `X` is the edge field `Φe (e₁) 0`
  have hXeq : X =ᵐ[μ] Φe (unit 1) 0 := by
    filter_upwards [hGae, hX] with ω hω hXω
    obtain ⟨h, hexu⟩ := hex ω hω
    obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
    rw [hXω h u hu]
    exact hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu _ _
  have hXint : Integrable X μ := hXi.congr hXeq.symm
  -- the flux along `(-e₁, 0)`
  set W : Configuration 2 → ℝ := fun ω => -Φe (unit 1) 0 (configurationTranslation (unit 1) ω)
  have hW : IsFluxField p (Pi.single 0 1) (-(unit 1 : Vertex 2)) 0 W := by
    filter_upwards [hall] with ω hω h u hu
    have hC := uniqueInfiniteComponent_infinite h
    have key := edgeDifference_add_unit hΦ hω (uniqueInfiniteComponent h) hC u hu
      (-(unit 1 : Vertex 2)) 1
    rw [neg_add_cancel, neg_neg] at key
    rw [edgeDifference_swap, key]
  have hWi : Integrable W μ :=
    ((measurePreserving_configurationTranslation p (unit 1)).integrable_comp_of_integrable hXi).neg
  have hWint : ∫ ω, W ω ∂μ = -∫ ω, X ω ∂μ := by
    rw [integral_neg, integral_comp_mp (measurePreserving_configurationTranslation p (unit 1))
      hXi.aestronglyMeasurable, integral_congr_ae hXeq]
  -- the reflection of the second coordinate
  have hR := isFluxField_comp_symm (Equiv.refl (Fin 2)) (Function.update 1 1 (-1)) hW
  rw [signedPermSlope_reflect_single_zero, signedPermIso_reflect_neg_unit_one,
    signedPermIso_zero_two] at hR
  have hXR := hX.ae_eq hpc hp1 hR
  have hRint := integral_comp_symm (p := p) (Equiv.refl (Fin 2)) (Function.update 1 1 (-1)) hWi
  rw [← integral_congr_ae hXR, hWint] at hRint
  exact ⟨hXint, by linarith⟩

/-- **The mean of the flux** in dimension two: there is `ā > 0` such that the flux `X_{k,i}`
along `(e_i, 0)` of the corrected planes of slope `e_k` is integrable with mean `ā δ_{ik}`. -/
theorem exists_fluxMean_two (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ abar : ℝ, 0 < abar ∧ ∀ (k i : Fin 2) (X : Configuration 2 → ℝ),
      IsFluxField p (Pi.single k 1) (unit i) 0 X →
        Integrable X (latticeBondLaw 2 p) ∧
          ∫ ω, X ω ∂latticeBondLaw 2 p = if i = k then abar else 0 := by
  obtain ⟨abar, habar, hmean⟩ := homogenizedCoefficient_two Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds
    Rigidity.Poincare.correctorQuantitativeInputTwo_holds p hpc hp1
  have h00 : ∀ X : Configuration 2 → ℝ, IsFluxField p (Pi.single 0 1) (unit 0) 0 X →
      Integrable X (latticeBondLaw 2 p) ∧ ∫ ω, X ω ∂latticeBondLaw 2 p = abar :=
    fun X hX => hmean X hX
  have h01 : ∀ X : Configuration 2 → ℝ, IsFluxField p (Pi.single 0 1) (unit 1) 0 X →
      Integrable X (latticeBondLaw 2 p) ∧ ∫ ω, X ω ∂latticeBondLaw 2 p = 0 :=
    fun X hX => integral_fluxField_zero_one hpc hp1 hX
  have h10 : ∀ X : Configuration 2 → ℝ, IsFluxField p (Pi.single 1 1) (unit 0) 0 X →
      Integrable X (latticeBondLaw 2 p) ∧ ∫ ω, X ω ∂latticeBondLaw 2 p = 0 := by
    intro X hX
    have hS : IsFluxField p (Pi.single 0 1) (unit 1) 0
        (X ∘ (configurationMap (signedPermIso (Equiv.swap 0 1) 1)).symm) := by
      simpa using isFluxField_swap hX
    obtain ⟨hi, hint⟩ := h01 _ hS
    have hXi := integrable_of_comp_symm (p := p) (Equiv.swap 0 1) 1 hi
    exact ⟨hXi, by rw [← integral_comp_symm (p := p) (Equiv.swap 0 1) 1 hXi, hint]⟩
  have h11 : ∀ X : Configuration 2 → ℝ, IsFluxField p (Pi.single 1 1) (unit 1) 0 X →
      Integrable X (latticeBondLaw 2 p) ∧ ∫ ω, X ω ∂latticeBondLaw 2 p = abar := by
    intro X hX
    have hS : IsFluxField p (Pi.single 0 1) (unit 0) 0
        (X ∘ (configurationMap (signedPermIso (Equiv.swap 0 1) 1)).symm) := by
      simpa using isFluxField_swap hX
    obtain ⟨hi, hint⟩ := h00 _ hS
    have hXi := integrable_of_comp_symm (p := p) (Equiv.swap 0 1) 1 hi
    exact ⟨hXi, by rw [← integral_comp_symm (p := p) (Equiv.swap 0 1) 1 hXi, hint]⟩
  refine ⟨abar, habar, fun k i X hX => ?_⟩
  fin_cases k <;> fin_cases i
  · simpa using h00 X hX
  · simpa using h01 X hX
  · simpa using h10 X hX
  · simpa using h11 X hX

end Fields

end Rigidity.Green

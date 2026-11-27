import Rigidity.Proofs.Green.GeneralFluxMoments
import Rigidity.Proofs.Green.DarioGuFluxMean
import Rigidity.Proofs.Corrector.GeneralCorrectorLipschitz
import Rigidity.Proofs.Corrector.DarioMoments
import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorInput

/-!
# The mean of the flux of the correctors on `ℤ^d`

The extension of `DarioGuFluxMean.lean` from `ℤ²` to `ℤ^d`, `d ≥ 2`. For `𝔭_c(d) < p < 1` and the
corrected planes `ℓ_k = x_k + χ_{e_k}` of the infinite cluster, the flux along the edge `(0, e_i)`
is `X_{k,i} = (ℓ_k(e_i) - ℓ_k(0)) 1{(e_i, 0) ∈ E(𝒞_∞)}`, the `i`-th component of
`a(Dχ_{e_k} + e_k)` at the origin. Its mean is `ā δ_{ik}` with `ā > 0` (`exists_fluxMeanD`):

* `ā = E[X_{0,0}] > 0` (`exists_homogenizedCoefficientD`): the argument of
  `Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed_of_boxEnergy`, with
  the integrability of the edge differences taken from the Lipschitz bound of the corrected planes
  (Dario, Proposition 2.15, `lipschitz_correctedPlane_origin`) instead of Theorem 2.5;
* the transposition of the coordinates `0` and `k` carries the corrected planes of slope `e_k` to
  those of slope `e₀` and the edge `(e_i, 0)` to `(e_{τ i}, 0)`, and preserves the law;
* for `i ≠ k`, the reflection of the coordinate `i` fixes the slope `e_k` and carries `(-e_i, 0)`
  to `(e_i, 0)`, and the flux along `(-e_i, 0)` is minus the flux along `(e_i, 0)` of the
  translated configuration, so `E[X_{k,i}] = -E[X_{k,i}] = 0`.

This is the identity `E[a(Dχ_p + p)] = ā p` used by Dario and Gu for the centered flux
`g̃_p = a(Dχ_p + p) - (σ̄²/2) p`, `σ̄² = 2 θ(p)^{-1} ā` ((B.5)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3
open scoped Classical

namespace Rigidity.Green.GeneralFlux

open Rigidity.Proofs.S3 Rigidity.Proofs.S3.FluxEvent Rigidity.Proofs.S3.HomogenizedCoefficient

variable {d : ℕ}

/-- `X` is almost surely the flux along `(a, b)` of the corrected planes of slope `q`. -/
def IsFluxFieldD (p : unitInterval) (q : Fin d → ℝ) (a b : Vertex d)
    (X : Configuration d → ℝ) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ), IsCorrectedPlane (uniqueInfiniteComponent h) q u →
      X ω = edgeDifference (uniqueInfiniteComponent h) u a b

section Transport

variable (φ : nearestNeighborGraph d ≃g nearestNeighborGraph d)

theorem mem_openComponentMap_supp_iffD {ω : Configuration d} (C : OpenComponent ω)
    (x : Vertex d) : φ x ∈ (openComponentMap φ ω C).supp ↔ x ∈ C.supp := by
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
theorem edgeDifference_openComponentMapD {ω : Configuration d} (C : OpenComponent ω)
    (v : openComponentMap φ ω C → ℝ) (a b : Vertex d) :
    edgeDifference (openComponentMap φ ω C) v (φ a) (φ b) =
      edgeDifference C (fun x => v (openComponentMapIso φ C x)) a b := by
  have hadj := openGraph_adj_configurationMap_iff φ ω a b
  unfold edgeDifference
  by_cases ha : a ∈ C.supp
  · have ha' := (mem_openComponentMap_supp_iffD φ C a).2 ha
    by_cases hab : (openGraph ω).Adj a b
    · have hb : b ∈ C.supp := (C.mem_supp_congr_adj hab).1 ha
      have hb' := (mem_openComponentMap_supp_iffD φ C b).2 hb
      rw [if_pos ⟨ha', hadj.2 hab⟩, if_pos ⟨ha, hab⟩]
      simp only [Section3.extend, dif_pos ha', dif_pos hb', dif_pos ha, dif_pos hb]
      rfl
    · rw [if_neg fun h => hab (hadj.1 h.2), if_neg fun h => hab h.2]
  · rw [if_neg fun h => ha ((mem_openComponentMap_supp_iffD φ C a).1 h.1), if_neg fun h => ha h.1]

end Transport

/-- The flux along `(x, y)` is minus the flux along `(y, x)`. -/
theorem edgeDifference_swapD {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    (x y : Vertex d) : edgeDifference C u x y = -edgeDifference C u y x := by
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

variable {p : unitInterval}

/-- **Transport of flux fields along signed permutations**: if `X` is the flux along `(a, b)` of
the corrected planes of slope `q`, then `X ∘ Φ⁻¹`, with `Φ` the action of the signed permutation
`φ` on the configurations, is the flux along `(φ a, φ b)` of the corrected planes of slope `φ_* q`. -/
theorem isFluxFieldD_comp_symm (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) {q : Fin d → ℝ}
    {a b : Vertex d} {X : Configuration d → ℝ} (hX : IsFluxFieldD p q a b X) :
    IsFluxFieldD p (signedPermSlope π s q) (signedPermIso π s a) (signedPermIso π s b)
      (X ∘ (configurationMap (signedPermIso π s)).symm) := by
  set φ := signedPermIso π s
  set Φ := configurationMap φ
  have h1 : ∀ᵐ ω₀ ∂latticeBondLaw d p, ∀ (h : HasUniqueInfiniteOpenComponent (Φ ω₀))
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
      edgeDifference_openComponentMapD]
  have hmp := (measurePreserving_configurationMap φ p).symm Φ
  filter_upwards [hmp.quasiMeasurePreserving.ae h1] with ω hω
  rw [MeasurableEquiv.apply_symm_apply] at hω
  exact hω

/-- Two flux fields with the same slope and edge agree almost surely. -/
theorem IsFluxFieldD.ae_eq [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1)
    {q : Fin d → ℝ} {a b : Vertex d} {X Y : Configuration d → ℝ} (hX : IsFluxFieldD p q a b X)
    (hY : IsFluxFieldD p q a b Y) : X =ᵐ[latticeBondLaw d p] Y := by
  filter_upwards [hX, hY, Rigidity.Percolation.ae_hasUniqueInfiniteOpenComponent hd hpc,
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds d hd p hpc hp1] with
    ω hXω hYω h hC
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  obtain ⟨u, hu, -⟩ := (hC h).1 q ⟨o, ho⟩
  rw [hXω h u hu.1, hYω h u hu.1]

theorem integrable_comp_symmD (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)
    {X : Configuration d → ℝ} (hX : Integrable X (latticeBondLaw d p)) :
    Integrable (X ∘ (configurationMap (signedPermIso π s)).symm) (latticeBondLaw d p) :=
  ((measurePreserving_configurationMap (signedPermIso π s) p).symm _).integrable_comp_of_integrable
    hX

theorem integrable_of_comp_symmD (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)
    {X : Configuration d → ℝ}
    (hX : Integrable (X ∘ (configurationMap (signedPermIso π s)).symm) (latticeBondLaw d p)) :
    Integrable X (latticeBondLaw d p) := by
  have := (measurePreserving_configurationMap (signedPermIso π s) p).integrable_comp_of_integrable
    hX
  simpa [Function.comp_def] using this

theorem integral_comp_symmD (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)
    {X : Configuration d → ℝ} (hX : Integrable X (latticeBondLaw d p)) :
    ∫ ω, (X ∘ (configurationMap (signedPermIso π s)).symm) ω ∂latticeBondLaw d p =
      ∫ ω, X ω ∂latticeBondLaw d p :=
  integral_comp_mp ((measurePreserving_configurationMap (signedPermIso π s) p).symm _)
    hX.aestronglyMeasurable

/-- A permutation of the coordinates carries the slope `e_k` to `e_{π⁻¹ k}`. -/
theorem signedPermSlope_one_piSingle (π : Equiv.Perm (Fin d)) (k : Fin d) :
    signedPermSlope π 1 (Pi.single k 1) = Pi.single (π.symm k) 1 := by
  funext j
  simp only [signedPermSlope, Pi.one_apply, Units.val_one, Int.cast_one, one_mul,
    Pi.single_apply, Equiv.eq_symm_apply]

/-- A permutation of the coordinates carries `e_i` to `e_{π⁻¹ i}`. -/
theorem signedPermIso_one_unit (π : Equiv.Perm (Fin d)) (i : Fin d) :
    signedPermIso π 1 (unit i : Vertex d) = unit (π.symm i) := by
  funext j
  change ((1 : Fin d → ℤˣ) j : ℤ) * (unit i : Vertex d) (π j) = _
  simp only [Pi.one_apply, Units.val_one, one_mul, LatticeProb.unit, Pi.single_apply,
    Equiv.eq_symm_apply]

/-- The reflection of the coordinate `i` fixes the slope `e_k` for `k ≠ i`. -/
theorem signedPermSlope_reflect_piSingle {i k : Fin d} (hik : i ≠ k) :
    signedPermSlope (Equiv.refl (Fin d)) (Function.update 1 i (-1)) (Pi.single k 1) =
      Pi.single k 1 := by
  funext j
  simp only [signedPermSlope, Equiv.refl_apply]
  by_cases hj : j = k
  · subst hj
    simp [Function.update_of_ne (Ne.symm hik)]
  · simp [hj]

/-- The reflection of the coordinate `i` carries `-e_i` to `e_i`. -/
theorem signedPermIso_reflect_neg_unit (i : Fin d) :
    signedPermIso (Equiv.refl (Fin d)) (Function.update 1 i (-1)) (-(unit i : Vertex d)) =
      unit i := by
  funext j
  change ((Function.update (1 : Fin d → ℤˣ) i (-1) j : ℤˣ) : ℤ) *
    (-(unit i : Vertex d)) (Equiv.refl (Fin d) j) = _
  by_cases hj : j = i
  · subst hj
    simp [LatticeProb.unit]
  · simp [LatticeProb.unit, hj]

/-- **Integrability of the edge differences** from the Lipschitz bound of the corrected planes
(Dario, Proposition 2.15): `|X_k| ≤ L max(𝒳, 2)^d` with `𝒳 ≤ O_s(θ)`. -/
theorem integrable_edgeField_unitD [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {G : Set (Configuration d)} (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G)
    {Φ : Vertex d → Vertex d → Configuration d → ℝ} (hΦm : ∀ x y, Measurable (Φ x y))
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 d) u)
    (hΦ : IsEdgeField G Φ) (k : Fin d) :
    Integrable (Φ (unit k) 0) (latticeBondLaw d p) := by
  obtain ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXos, hlip⟩ :=
    Rigidity.Corrector.GeneralDim.lipschitz_correctedPlane_origin hd hpc hp1
  have hXd := (Rigidity.Corrector.IsOsBond.integral_rpow_le hs hθ
    (q := (d : ℝ)) (Nat.cast_pos.mpr (NeZero.pos d)) hXm hX0 hXos).1
  refine Integrable.mono' ((hXd.add (integrable_const ((2 : ℝ) ^ d))).const_mul L)
    (hΦm (unit k) 0).aestronglyMeasurable ?_
  filter_upwards [hGae, hlip] with ω hω hb
  obtain ⟨h, hexu⟩ := hex ω hω
  obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
  rw [← hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu, Real.norm_eq_abs]
  have hM : max (X ω) 2 ^ d ≤ X ω ^ (d : ℝ) + 2 ^ d := by
    rw [Real.rpow_natCast]
    rcases le_total (X ω) 2 with h2 | h2
    · rw [max_eq_right h2]
      linarith [pow_nonneg (hX0 ω) d]
    · rw [max_eq_left h2]
      linarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) d]
  have hB : 0 ≤ L * (X ω ^ (d : ℝ) + 2 ^ d) :=
    mul_nonneg hL.le (add_nonneg (Real.rpow_nonneg (hX0 ω) (d : ℝ)) (by positivity))
  unfold edgeDifference
  split_ifs with h0
  · have h0' : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp h0.1 h0.2
    let a : uniqueInfiniteComponent h := ⟨unit k, h0.1⟩
    let b : uniqueInfiniteComponent h := ⟨0, h0'⟩
    have hab : (componentGraph (uniqueInfiniteComponent h)).Adj a b :=
      ((uniqueInfiniteComponent h).toSimpleGraph_adj a.2 b.2).2 h0.2
    have hna : ‖latticeEuclideanEmbedding a.val‖ < 2 := by
      have := norm_latticeEuclideanEmbedding_unit_sub_zero (d := d) k
      rw [Rigidity.Corrector.GeneralDim.latticeEuclideanEmbedding_zero, sub_zero] at this
      exact this.trans_lt (by norm_num)
    have hq : ∑ i, |slopeE1 d i| = 1 := by
      rw [Finset.sum_eq_single (0 : Fin d) (fun i _ hi => by simp [slopeE1, hi]) (by simp)]
      simp [slopeE1]
    have hbd := hb h (slopeE1 d) u hu a b hab hna
    rw [hq, mul_one] at hbd
    have ea : Rigidity.Section3.extend (uniqueInfiniteComponent h) u (unit k) = u a := dif_pos h0.1
    have eb : Rigidity.Section3.extend (uniqueInfiniteComponent h) u 0 = u b := dif_pos h0'
    rw [ea, eb]
    exact hbd.trans (mul_le_mul_of_nonneg_left hM hL.le)
  · rw [abs_zero]
    exact hB

/-- **Positivity of the homogenized coefficient** on `ℤ^d`: the mean `ā` of the flux of the corrected
planes of slope `e₀` along `(e₀, 0)` is positive. -/
theorem exists_homogenizedCoefficientD [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ abar > 0, ∀ X : Configuration d → ℝ,
      (∀ᵐ ω ∂latticeBondLaw d p, ∀ (h : HasUniqueInfiniteOpenComponent ω) u,
        IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u →
        X ω = edgeDifference (uniqueInfiniteComponent h) u (unit 0) 0) →
      Integrable X (latticeBondLaw d p) ∧ ∫ ω, X ω ∂latticeBondLaw d p = abar := by
  set μ := latticeBondLaw d p
  obtain ⟨G, hG, hG1, Φ, hΦm, hex, hΦ⟩ := exists_edgeField
    Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds hd p hpc hp1
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := mem_ae_iff.2 ((prob_compl_eq_zero_iff hG).2 hG1)
  have hall : ∀ᵐ ω ∂μ, ∀ z, configurationTranslation z ω ∈ G :=
    ae_all_iff.2 fun z =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae hGae
  have hXi := fun k => integrable_edgeField_unitD hd hpc hp1 hGae hΦm hex hΦ k
  have hge := integral_ge_energy (boxEnergyInequality d) p hall hΦm hex hΦ hXi zero_le_one
  have iMin : ∀ k, Integrable (fun ω => min (Φ (unit k) 0 ω ^ 2) 1) μ := fun k =>
    (integrable_const (1 : ℝ)).mono'
      ((((hΦm _ _).pow_const 2).min measurable_const).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) zero_le_one)]
        exact min_le_right _ _)
  have hnn : ∀ k, 0 ≤ ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ := fun k =>
    integral_nonneg fun ω => le_min (sq_nonneg _) zero_le_one
  have hpos : 0 < ∑ k, ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ := by
    by_contra hle
    rw [not_lt] at hle
    apply not_forall_ae_eq_zero p hGae hall hex hΦ
    intro k
    have h0 : ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ = 0 := le_antisymm
      ((Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ k)).trans hle) (hnn k)
    rw [integral_eq_zero_iff_of_nonneg (fun ω => le_min (sq_nonneg _) zero_le_one) (iMin k)]
      at h0
    filter_upwards [h0] with ω hω
    by_contra hne
    have h1 : 0 < Φ (unit k) 0 ω ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    exact (lt_min h1 one_pos).ne' hω
  refine ⟨∫ ω, Φ (unit 0) 0 ω ∂μ, hpos.trans_le hge, fun X hX => ?_⟩
  have hXeq : X =ᵐ[μ] Φ (unit 0) 0 := by
    filter_upwards [hGae, hX] with ω hω hXω
    obtain ⟨h, hexu⟩ := hex ω hω
    obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
    rw [hXω h u hu]
    exact hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu _ _
  exact ⟨(hXi 0).congr hXeq.symm, integral_congr_ae hXeq⟩

/-- **The off-diagonal flux of slope `e₀` has mean zero**: for `i ≠ 0`, the flux along `(e_i, 0)`. -/
theorem integral_fluxFieldD_zero_off [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {i : Fin d} (hi : i ≠ 0)
    {X : Configuration d → ℝ} (hX : IsFluxFieldD p (Pi.single 0 1) (unit i) 0 X) :
    Integrable X (latticeBondLaw d p) ∧ ∫ ω, X ω ∂latticeBondLaw d p = 0 := by
  set μ := latticeBondLaw d p
  obtain ⟨G, hG, hG1, Φe, hΦm, hex, hΦ⟩ := exists_edgeField
    Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds hd p hpc hp1
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := mem_ae_iff.2 ((prob_compl_eq_zero_iff hG).2 hG1)
  have hall : ∀ᵐ ω ∂μ, ∀ z, configurationTranslation z ω ∈ G :=
    ae_all_iff.2 fun z =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae hGae
  have hXi := integrable_edgeField_unitD hd hpc hp1 hGae hΦm hex hΦ i
  have hXeq : X =ᵐ[μ] Φe (unit i) 0 := by
    filter_upwards [hGae, hX] with ω hω hXω
    obtain ⟨h, hexu⟩ := hex ω hω
    obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
    rw [hXω h u hu]
    exact hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu _ _
  have hXint : Integrable X μ := hXi.congr hXeq.symm
  set W : Configuration d → ℝ := fun ω => -Φe (unit i) 0 (configurationTranslation (unit i) ω)
  have hW : IsFluxFieldD p (Pi.single 0 1) (-(unit i : Vertex d)) 0 W := by
    filter_upwards [hall] with ω hω h u hu
    have hC := uniqueInfiniteComponent_infinite h
    have key := edgeDifference_add_unit hΦ hω (uniqueInfiniteComponent h) hC u hu
      (-(unit i : Vertex d)) i
    rw [neg_add_cancel, neg_neg] at key
    rw [edgeDifference_swapD, key]
  have hWi : Integrable W μ :=
    ((measurePreserving_configurationTranslation p (unit i)).integrable_comp_of_integrable hXi).neg
  have hWint : ∫ ω, W ω ∂μ = -∫ ω, X ω ∂μ := by
    rw [integral_neg, integral_comp_mp (measurePreserving_configurationTranslation p (unit i))
      hXi.aestronglyMeasurable, integral_congr_ae hXeq]
  have hR := isFluxFieldD_comp_symm (Equiv.refl (Fin d)) (Function.update 1 i (-1)) hW
  rw [signedPermSlope_reflect_piSingle hi, signedPermIso_reflect_neg_unit,
    signedPermIso_zero] at hR
  have hXR := hX.ae_eq hd hpc hp1 hR
  have hRint := integral_comp_symmD (p := p) (Equiv.refl (Fin d)) (Function.update 1 i (-1)) hWi
  rw [← integral_congr_ae hXR, hWint] at hRint
  exact ⟨hXint, by linarith⟩

/-- **The mean of the flux** on `ℤ^d`: there is `ā > 0` such that the flux `X_{k,i}` along
`(e_i, 0)` of the corrected planes of slope `e_k` is integrable with mean `ā δ_{ik}`. -/
theorem exists_fluxMeanD [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ abar : ℝ, 0 < abar ∧ ∀ (k i : Fin d) (X : Configuration d → ℝ),
      IsFluxFieldD p (Pi.single k 1) (unit i) 0 X →
        Integrable X (latticeBondLaw d p) ∧
          ∫ ω, X ω ∂latticeBondLaw d p = if i = k then abar else 0 := by
  obtain ⟨abar, habar, hmean⟩ := exists_homogenizedCoefficientD (p := p) hd hpc hp1
  refine ⟨abar, habar, fun k i X hX => ?_⟩
  set π : Equiv.Perm (Fin d) := Equiv.swap 0 k with hπ
  have hS : IsFluxFieldD p (Pi.single 0 1) (unit (π.symm i)) 0
      (X ∘ (configurationMap (signedPermIso π 1)).symm) := by
    have h := isFluxFieldD_comp_symm π 1 hX
    rwa [signedPermSlope_one_piSingle, signedPermIso_one_unit, signedPermIso_zero,
      show π.symm k = 0 by rw [hπ, Equiv.symm_swap, Equiv.swap_apply_right]] at h
  have key : Integrable (X ∘ (configurationMap (signedPermIso π 1)).symm) (latticeBondLaw d p) ∧
      ∫ ω, (X ∘ (configurationMap (signedPermIso π 1)).symm) ω ∂latticeBondLaw d p =
        if i = k then abar else 0 := by
    by_cases hik : i = k
    · rw [if_pos hik]
      have e : π.symm i = 0 := by rw [hik, hπ, Equiv.symm_swap, Equiv.swap_apply_right]
      rw [e] at hS
      exact hmean _ hS
    · rw [if_neg hik]
      have e : π.symm i ≠ 0 := by
        rw [hπ, Equiv.symm_swap, Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        exact hik
      exact integral_fluxFieldD_zero_off hd hpc hp1 e hS
  obtain ⟨hi, hint⟩ := key
  have hXi := integrable_of_comp_symmD (p := p) π 1 hi
  exact ⟨hXi, by rw [← integral_comp_symmD (p := p) π 1 hXi, hint]⟩

end Fields

end Rigidity.Green.GeneralFlux

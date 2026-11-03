import Rigidity.External.ArmstrongDarioRegularity
import Rigidity.Proofs.S2.ScaleInputsFaithful
import LatticeProb.Prob.Percolation.LatticeOrderZeroTranslation
import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation

/-!
# Proposition 2.6, step:2.6-inputs: order-one regularity at every centre, by stationarity

`armstrongDarioOrderOneProposed_of_origin` derives `ArmstrongDarioOrderOneProposed` (the large-scale
`C^{1,1}` regularity around every vertex `x`, `ScaleInputs.lean`) from the literature statement at
the origin, `Rigidity.External.ArmstrongDarioOrderOneOrigin` (Armstrong–Dario 2018, Theorem 2(iii)
at `k = 1`; corrected draft C34), and the classification of `𝒜₁` of
`LatticeProb.External.SupercriticalBondCorrectorInput` (Theorem 2.5).

The minimal scale at `x` is `M_x := 𝒳 ∘ τ_{-x}`, where `τ_{-x} = configurationTranslation (-x)`
moves the infinite cluster by `-x` (`openComponentTranslation_uniqueInfiniteComponent`), so that
`x` goes to the origin. The law is translation invariant
(`measurePreserving_configurationTranslation`), so `M_x` is measurable with the same `O_s` bound,
and the origin statement holds almost surely at `τ_{-x} ω`. The deterministic transport
(`orderOne_approximation_translation`) moves balls and `L̲²` averages
(`componentBallL2_translation`), the Laplacian (`componentLaplacian_translation`) and corrected
planes (`isCorrectedPlane_translation_iff`); an element of `𝒜₁` of the translated cluster is a
corrected plane (classification), so its pullback is a corrected plane, hence lies in `𝒜₁`. The
two constants of the source are merged into their maximum (`IsOsBond.mono_scale`).
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation
open Rigidity.External (IsOsBond ArmstrongDarioOrderOneOrigin)

variable {d : ℕ}

/-- **Transport of the order-one approximation from the origin to the centre `z`.** If the
order-one approximation property holds at the origin for the infinite cluster of `τ_{-z} ω`, whose
`𝒜₁` consists of corrected planes, then it holds at `z` for the infinite cluster of `ω`, with the
same minimal scale `X` and the same constant `C`. -/
theorem orderOne_approximation_translation (z : Vertex d) {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) (X C : ℝ)
    (hcl : ∀ φ : uniqueInfiniteComponent
          ((hasUniqueInfiniteOpenComponent_translation_iff (-z) ω).mpr h) → ℝ,
        φ ∈ harmonicGrowthSpace _ 1 → ∃ q : Fin d → ℝ, IsCorrectedPlane _ q φ)
    (happ : ∀ (R : ℝ), 2 * X ≤ R →
      ∀ u : uniqueInfiniteComponent
          ((hasUniqueInfiniteOpenComponent_translation_iff (-z) ω).mpr h) → ℝ,
        (∀ x ∈ componentEuclideanBall _ 0 R,
          (∀ y, (componentGraph _).Adj x y → y ∈ componentEuclideanBall _ 0 R) →
            componentLaplacian _ u x = 0) →
        ∃ φ ∈ harmonicGrowthSpace _ 1, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
          componentBallL2 _ 0 r (u - φ) ≤ C * (r / R) ^ 2 * componentBallL2 _ 0 R u) :
    ∀ (R : ℝ), 2 * X ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
      (∀ x ∈ componentEuclideanBall _ z R,
        (∀ y, (componentGraph _).Adj x y → y ∈ componentEuclideanBall _ z R) →
          componentLaplacian _ u x = 0) →
      ∃ φ ∈ harmonicGrowthSpace _ 1, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
        componentBallL2 _ z r (u - φ) ≤ C * (r / R) ^ 2 * componentBallL2 _ z R u := by
  classical
  have heq := openComponentTranslation_uniqueInfiniteComponent (-z) h
  rw [← heq] at happ hcl
  intro R hR u hu
  let e := openComponentTranslationIso (-z) (uniqueInfiniteComponent h)
  let v : openComponentTranslation (-z) ω (uniqueInfiniteComponent h) → ℝ :=
    fun y => u (e.symm y)
  have hv : ∀ x ∈ componentEuclideanBall _ 0 R,
      (∀ y, (componentGraph _).Adj x y → y ∈ componentEuclideanBall _ 0 R) →
        componentLaplacian _ v x = 0 := by
    intro x hx hinside
    let x' := e.symm x
    have hx' : x' ∈ componentEuclideanBall (uniqueInfiniteComponent h) z R := by
      apply (mem_componentEuclideanBall_translation (-z) z _ R x').mp
      simpa [e, x'] using hx
    have hi : ∀ y, (componentGraph (uniqueInfiniteComponent h)).Adj x' y →
        y ∈ componentEuclideanBall (uniqueInfiniteComponent h) z R := by
      intro y hy
      apply (mem_componentEuclideanBall_translation (-z) z _ R y).mp
      have hadj : (componentGraph _).Adj x (e y) := by
        simpa [x'] using e.map_rel_iff.mpr hy
      have hy' := hinside (e y) hadj
      simpa using hy'
    have hl := componentLaplacian_translation (-z) (uniqueInfiniteComponent h) u x'
    simpa [v, e, x'] using hl.trans (hu x' hx' hi)
  obtain ⟨φ', hφ', hc⟩ := happ R hR v hv
  obtain ⟨q, hq⟩ := hcl φ' hφ'
  let φ : uniqueInfiniteComponent h → ℝ := fun x => φ' (e x)
  have hpull : (fun y => φ (e.symm y)) = φ' := by
    funext y
    simp only [φ, e.apply_symm_apply]
  have hφ : IsCorrectedPlane (uniqueInfiniteComponent h) q φ := by
    apply (isCorrectedPlane_translation_iff (-z) (uniqueInfiniteComponent h) q φ).mp
    rw [hpull]
    exact hq
  refine ⟨φ, hφ.1, ?_⟩
  intro r hr hrR
  have h1 := componentBallL2_translation (-z) z (uniqueInfiniteComponent h) r (u - φ)
  have h2 := componentBallL2_translation (-z) z (uniqueInfiniteComponent h) R u
  simp only [add_neg_cancel] at h1 h2
  rw [← h1, ← h2]
  have hvsub : (fun y => (u - φ) (e.symm y)) = v - φ' := by
    funext y
    simp only [Pi.sub_apply, v, φ, e.apply_symm_apply]
  rw [hvsub]
  exact hc r hr hrR

/-- **Order-one large-scale regularity around every vertex, from the origin statement.**
Armstrong–Dario 2018, Theorem 2(iii) at `k = 1` at the origin
(`Rigidity.External.ArmstrongDarioOrderOneOrigin`), transported to every centre `x` by
stationarity with the minimal scale `M_x := 𝒳 ∘ τ_{-x}`; the `𝒜₁` classification of
`SupercriticalBondCorrectorInput` makes `𝒜₁` translation invariant. -/
theorem armstrongDarioOrderOneProposed_of_origin (hAD : ArmstrongDarioOrderOneOrigin)
    (hcorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ArmstrongDarioOrderOneProposed := by
  intro d _ hd p hp hp1
  obtain ⟨s, C₀, hs, hC₀, X, hXm, hX0, hXO, C, hAE⟩ := hAD d hd p hp hp1
  have hcl := hcorr d hd p hp hp1
  refine ⟨s, max C₀ C, hs, lt_max_of_lt_left hC₀, fun x => ?_⟩
  have hmp := measurePreserving_configurationTranslation p (-x)
  have hYm : Measurable (fun ω => X (configurationTranslation (-x) ω)) :=
    hXm.comp (configurationTranslationMeasurableEquiv (-x)).measurable
  have hYO : IsOsBond d p (fun ω => X (configurationTranslation (-x) ω)) s C₀ := by
    refine ⟨hmp.integrable_comp_of_integrable hXO.1, ?_⟩
    have he := hmp.integral_comp (configurationTranslationMeasurableEquiv (-x)).measurableEmbedding
      (fun ω => Real.exp (Real.rpow (max (X ω / C₀) 0) s))
    exact he.trans_le hXO.2
  refine ⟨fun ω => X (configurationTranslation (-x) ω), hYm, fun ω => hX0 _,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs hC₀ (le_max_left _ _) hYm hYO, ?_⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae hAE, hmp.quasiMeasurePreserving.ae hcl]
    with ω hω hcω
  intro h R hR u hu
  have ht := (hasUniqueInfiniteOpenComponent_translation_iff (-x) ω).mpr h
  obtain ⟨φ, hφ, hest⟩ := orderOne_approximation_translation x h
    (X (configurationTranslation (-x) ω)) C
    (fun φ hφ => ((hcω ht).2 φ hφ).exists) (hω ht) R hR u hu
  refine ⟨φ, hφ, fun r hr hrR => (hest r hr hrR).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
    (componentBallL2_nonneg _ _ _ _)

end Rigidity.Proofs.S2

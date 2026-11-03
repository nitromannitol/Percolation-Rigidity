import Rigidity.Proofs.S2.GreenGradientCore
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra
import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth

/-!
# Proposition 2.6, step:2.6-inputs: the regularity and density minimal scales

The two input steps of Proposition 2.6 (paper L508-519 of the corrected draft) that come from the
literature.

* `regularityScaleStep`: `RegularityScaleStep d p`, from the proposed order-one regularity input
  (`ArmstrongDarioOrderOneProposed`) and the classification of `𝒜₁` of
  `LatticeProb.External.SupercriticalBondCorrectorInput` (Theorem 2.5): an element `φ ∈ 𝒜₁` has a
  slope `ξ`, and `φ - ∑ᵢ ξᵢ ℓ_{eᵢ}` is a corrected plane of slope zero, hence constant
  (`exists_eq_sum_correctedPlane`).
* `densityScaleStep`: `DensityScaleStep d p`, verbatim `ClusterDensityInputProposed`.
* `greenGradientHomogenization_of_inputs`: Proposition 2.6 from the literature inputs
  `SupercriticalBondGreenQuantitative`, `CorrectorQuantitativeInput`,
  `SupercriticalBondCorrectorInput` and the two proposed inputs above.

The two proposed inputs are not literature statements as printed: both are stronger than the
sentences of the corrected draft that cite them. The printed sentences are
`ArmstrongDarioOrderOneFaithful` and `ClusterDensityInputFaithful`
(`Rigidity/Proofs/S2/ScaleInputsFaithful.lean`), which derives both proposed forms from them:
`clusterDensityInputProposed_of_faithful` (union bound over the centres) and
`armstrongDarioOrderOneProposed_of_faithful` (with the printed density and
`CorrectorQuantitativeInput`).

Source of the density input (correction C35): the draft cites Penrose–Pisztora at L509, but their
Theorem 1 concerns continuum percolation and their lattice theorems are for site percolation. For
bond percolation in every `d ≥ 2` the density sentence follows from Dario–Gu, arXiv:1909.10439v4,
Proposition A.1 (`Rigidity.External.ClusterDensityConcentrationInput`) by a union bound over
triadic cubes: `clusterDensityInputFaithful_of_concentration` and
`clusterDensityInputProposed_of_concentration` (`Rigidity/Proofs/S2/ClusterDensityFromDarioGu.lean`).
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.Steps.S2
open Rigidity.External (IsOsBond)

/-- **Large-scale `C^{1,1}` regularity, proposed form**: for `R ≥ 2 M_reg(x)` and `u` harmonic in
`𝒞_∞ ∩ B_R(x)` there is one `φ ∈ 𝒜₁` with `‖u - φ‖_{L̲²(B_r(x))} ≤ C (r/R)² ‖u‖_{L̲²(B_R(x))}` for
every `r ∈ [M_reg(x), R/2]`; `M_reg(x) ≤ O_s(C)`. This is stronger than eq. (large
scale-regularity) as printed at paper L513-518 (`ArmstrongDarioOrderOneFaithful`: harmonic in
`B_{2R}`, constant depending on `r`) and is not part of Theorem 2.4 as quoted (L373-387, global
harmonic functions only). It is derived from the printed form, the printed density and the corrector
bounds by `armstrongDarioOrderOneProposed_of_faithful` (`ScaleInputsFaithful.lean`). Consumed by
the proof of `Rigidity.Steps.S2.RegularityScaleStep` (with the 𝒜₁ classification of
`LatticeProb.External.SupercriticalBondCorrectorInput`). -/
def ArmstrongDarioOrderOneProposed : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, 2 * M ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) x R,
            (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
              w ∈ componentEuclideanBall (uniqueInfiniteComponent h) x R) →
            componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
          ∃ φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1,
            ∀ r : ℝ, M ω ≤ r → r ≤ R / 2 →
              componentBallL2 (uniqueInfiniteComponent h) x r (u - φ) ≤
                C * (r / R) ^ 2 * componentBallL2 (uniqueInfiniteComponent h) x R u

/-- **Density of the infinite cluster, proposed form**: beyond `M_dense(x) ≤ O_s(C)`, every ball
of radius `r/100` centred at a vertex of `B̄_r(x)` contains at least `c r^d` vertices of `𝒞_∞`. This
is stronger than the sentence printed at paper L508-511 (balls of radius `r/100` containing `x`,
`ClusterDensityInputFaithful`), from which it follows at every centre by a union bound
(`clusterDensityInputProposed_of_faithful`, `ScaleInputsFaithful.lean`). Source (correction C35):
Dario–Gu, arXiv:1909.10439v4, Proposition A.1, with a union bound over triadic cubes
(`clusterDensityInputProposed_of_concentration`, `ClusterDensityFromDarioGu.lean`); the draft's
citation of Penrose–Pisztora does not cover bond percolation. It is verbatim the content of
`Rigidity.Steps.S2.DensityScaleStep`, which it discharges. -/
def ClusterDensityInputProposed : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C c : ℝ, 0 < s ∧ 0 < C ∧ 0 < c ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ r : ℝ, M ω ≤ r → ∀ z : Vertex d,
          dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding x) ≤ r →
            c * r ^ d ≤
              ((componentEuclideanBall (uniqueInfiniteComponent h) z (r / 100)).card : ℝ)

variable {d : ℕ}

/-- A linear combination of corrected planes is a corrected plane, with the same combination of
the slopes. -/
theorem isCorrectedPlane_sum_smul {ω : Configuration d} (C : OpenComponent ω)
    {q : Fin d → Fin d → ℝ} {ℓ : Fin d → C → ℝ} (hℓ : ∀ i, IsCorrectedPlane C (q i) (ℓ i))
    (ξ : Fin d → ℝ) : IsCorrectedPlane C (∑ i, ξ i • q i) (∑ i, ξ i • ℓ i) := by
  classical
  refine Finset.induction_on (Finset.univ : Finset (Fin d)) ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact isCorrectedPlane_const C 0
  · intro i s hi hs
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact isCorrectedPlane_add C (isCorrectedPlane_smul C (hℓ i) (ξ i)) hs

/-- Classification of `𝒜₁` in the coordinates of a family of corrected planes (Theorem 2.5): under
the two uniqueness assertions of `SupercriticalBondCorrectorInput` on a component `C`, every
`φ ∈ 𝒜₁(C)` equals `∑ᵢ ξᵢ ℓ_{eᵢ} + a` for every family `ℓ_{eᵢ}` of corrected planes of slopes
`eᵢ`. -/
theorem exists_eq_sum_correctedPlane {ω : Configuration d} {C : OpenComponent ω}
    (hU₁ : ∀ (q : Fin d → ℝ) (o : C), ∃! u : C → ℝ, IsCorrectedPlane C q u ∧ u o = 0)
    (hU₂ : ∀ u : C → ℝ, u ∈ harmonicGrowthSpace C 1 → ∃! q : Fin d → ℝ, IsCorrectedPlane C q u)
    {ℓ : Fin d → C → ℝ} (hℓ : ∀ i, IsCorrectedPlane C (Pi.single i 1) (ℓ i))
    {φ : C → ℝ} (hφ : φ ∈ harmonicGrowthSpace C 1) :
    ∃ (ξ : Fin d → ℝ) (a : ℝ), ∀ z : C, φ z = ∑ i, ξ i * ℓ i z + a := by
  rcases isEmpty_or_nonempty C with hC | ⟨⟨o⟩⟩
  · exact ⟨0, 0, fun z => isEmptyElim z⟩
  obtain ⟨ξ, hξ, -⟩ := hU₂ φ hφ
  have hL := isCorrectedPlane_sum_smul C hℓ ξ
  have hsl : (∑ i, ξ i • (Pi.single i 1 : Fin d → ℝ)) = ξ := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsl] at hL
  set L : C → ℝ := ∑ i, ξ i • ℓ i with hLdef
  have hw := isCorrectedPlane_sub C (isCorrectedPlane_sub C hξ hL)
    (isCorrectedPlane_const C ((φ - L) o))
  rw [sub_self, sub_zero] at hw
  have h0 := (hU₁ 0 o).unique ⟨hw, by simp⟩ ⟨isCorrectedPlane_const C 0, rfl⟩
  refine ⟨ξ, (φ - L) o, fun z => ?_⟩
  have hz := congrFun h0 z
  have hLz : L z = ∑ i, ξ i * ℓ i z := by
    simp only [hLdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.sub_apply] at hz
  rw [← hLz, Pi.sub_apply]
  linarith

/-- step:2.6-inputs, regularity (paper L513-519): (H2) beyond a minimal scale
`M_reg(x) ≤ O_s(C)`, for every family of corrected planes `ℓ_{eᵢ}`, from the proposed order-one regularity input
(`ArmstrongDarioOrderOneProposed`, proposed form) and the classification of `𝒜₁` (Theorem 2.5,
`SupercriticalBondCorrectorInput`). -/
theorem regularityScaleStep [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hAD : ArmstrongDarioOrderOneProposed)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput) : RegularityScaleStep d p := by
  intro hpc hp1
  obtain ⟨s, C₀, hs, hC₀, hx⟩ := hAD d hd p hpc hp1
  refine ⟨s, C₀, hs, hC₀, fun x => ?_⟩
  obtain ⟨M, hMm, hM0, hMos, hae⟩ := hx x
  refine ⟨M, hMm, hM0, hMos, ?_⟩
  filter_upwards [hae, hU d hd p hpc hp1] with ω hω hUω
  intro h ℓ hℓ R hR u hu
  obtain ⟨φ, hφ, hbd⟩ := hω h R hR u hu
  obtain ⟨ξ, a, hξ⟩ := exists_eq_sum_correctedPlane (hUω h).1 (hUω h).2 hℓ hφ
  have huφ : u - φ = fun z => u z - ∑ i, ξ i * ℓ i z - a :=
    funext fun z => by rw [Pi.sub_apply, hξ z, sub_sub]
  refine ⟨ξ, a, fun r hr hrR => ?_⟩
  rw [← huφ]
  exact hbd r hr hrR

/-- step:2.6-inputs, density (paper L508-511): (H4) beyond a minimal scale `M_dense(x) ≤ O_s(C)`;
verbatim `ClusterDensityInputProposed`. -/
theorem densityScaleStep [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hD : ClusterDensityInputProposed) : DensityScaleStep d p :=
  fun hpc hp1 => hD d hd p hpc hp1

/-- **Proposition 2.6** (homogenization of the gradient of the Green function, forward-difference
reading [C4]) from the literature inputs `SupercriticalBondGreenQuantitative`,
`CorrectorQuantitativeInput`, `SupercriticalBondCorrectorInput` (classification of `𝒜₁`) and the
two proposed inputs `ArmstrongDarioOrderOneProposed` (order-one regularity, proposed form) and
`ClusterDensityInputProposed` (density, proposed form). -/
theorem greenGradientHomogenization_of_inputs [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hAD : ArmstrongDarioOrderOneProposed) (hD : ClusterDensityInputProposed) :
    Rigidity.Section2.GreenGradientHomogenizationStmt d hd p :=
  greenGradientHomogenization_of_regularity_density hd p hpc hp1 hGQ hCQ
    (regularityScaleStep hd p hAD hU) (densityScaleStep hd p hD)

end Rigidity.Proofs.S2

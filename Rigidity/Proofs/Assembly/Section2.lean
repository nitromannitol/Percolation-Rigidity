import Rigidity.Proofs.S2.JordanCurves
import Rigidity.Proofs.S2.ScaleInputs

/-!
# Section 2: the composed results

Lemma 2.16 of the corrected draft (correction [C7] of the printed statement), obtained by
composing the reduction of its carving (`Rigidity.Steps.S2.jordanCurves_of_steps`) with its three
proved steps (`Rigidity.Proofs.S2.parametrizeStep`, `loopsStep`, `componentsStep`).
The only literature input is the Jordan curve theorem on the sphere
(`Rigidity.External.JordanCurveTheoremSphere`).

Proposition 2.6 (homogenization of the gradient of the Green function, forward-difference reading
[C4]), obtained by composing `Rigidity.Steps.S2.greenGradientHomogenization_of_steps` with its
nine proved steps: `regularityScaleStep`, `densityScaleStep`, `tailOfOsStep`, `minimalScaleStep`,
`greenGradientCoreStep` (top level), the last one proved from `greenOscillationStep`,
`slopeEstimateStep`, `continuumGreenStep` and `affineMajorizationStep`. Hypotheses: the regime
`2 ≤ d`, `p_c(d) < p < 1` and the literature inputs
* `LatticeProb.External.SupercriticalBondGreenQuantitative` (quantitative homogenization of the
  Green function of the cluster, Dario–Gu),
* `Rigidity.External.CorrectorQuantitativeInput` (Theorem 2.5, quantitative sublinearity of the
  corrector, Armstrong–Dario),
* `LatticeProb.External.SupercriticalBondCorrectorInput` (Theorem 2.5, classification of `𝒜₁`),

and the two **local proposed inputs** of `Rigidity/Proofs/S2/ScaleInputs.lean` (derived from
cited inputs in `Rigidity/Proofs/Assembly/Main.lean`):
* `Rigidity.Proofs.S2.ArmstrongDarioOrderOneProposed` (Theorem 2.4 at order one, Armstrong–Dario,
  CPAM 71 (2018), Theorem 2 with `k = 1`),
* `Rigidity.Proofs.S2.ClusterDensityInputProposed` (density of the cluster, Penrose–Pisztora).
-/

namespace Rigidity.Assembly

/-- **Lemma 2.16** (corrected statement): for `K ≥ 2` distinct points `x_i` of a Jordan curve
`α` of `S²` avoiding the north pole `N`, and simple arcs `γ_i` from `x_i` to `N` with
`α ∩ γ_i = {x_i}` and `γ_i ∩ γ_j = {N}` for `i ≠ j`, the set `S² \ (α ∪ ⋃ γ_i)` has at least `K`
connected components whose closure contains `N`. Uses the Jordan curve theorem on the sphere. -/
theorem jordanCurves (hJ : External.JordanCurveTheoremSphere) : Section2.JordanCurvesStmt :=
  Steps.S2.jordanCurves_of_steps hJ Proofs.S2.parametrizeStep Proofs.S2.loopsStep
    Proofs.S2.componentsStep

/-- **Proposition 2.6** (homogenization of the gradient of the Green function, forward-difference
reading [C4]): for `2 ≤ d` and `p_c(d) < p < 1`, beyond a minimal scale `M(y) ≤ O_s(C)`,
`|D⁺G(x, y) - ∑ᵢ D⁺ℓ_{eᵢ}(x) ∂ᵢḠ(x - y)| ≤ C |x - y|^{-1/2 + δ} |x - y|^{1 - d}`.
Inputs: `SupercriticalBondGreenQuantitative`, `CorrectorQuantitativeInput`,
`SupercriticalBondCorrectorInput`, and the local proposed inputs
`Rigidity.Proofs.S2.ArmstrongDarioOrderOneProposed` (Theorem 2.4 at order one) and
`Rigidity.Proofs.S2.ClusterDensityInputProposed` (Penrose–Pisztora). -/
theorem greenGradientHomogenization {d : ℕ} [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : LatticeProb.Percolation.criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : External.CorrectorQuantitativeInput)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hAD : Proofs.S2.ArmstrongDarioOrderOneProposed)
    (hD : Proofs.S2.ClusterDensityInputProposed) :
    Section2.GreenGradientHomogenizationStmt d hd p :=
  Steps.S2.greenGradientHomogenization_of_steps hd p hpc hp1 hGQ hCQ
    (Proofs.S2.regularityScaleStep hd p hAD hU) (Proofs.S2.densityScaleStep hd p hD)
    (Proofs.S2.tailOfOsStep d p) (Proofs.S2.minimalScaleStep d p)
    (Proofs.S2.greenGradientCoreStep hd)

end Rigidity.Assembly

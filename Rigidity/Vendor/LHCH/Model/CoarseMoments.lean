/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Model/CoarseMoments.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Coarse

/-!
# Statistics of the coarse-grained matrices on the triadic cubes

For random positive conductances `c` on `Ω`, the coarse-grained matrices `A_{□_n}` and `B_{□_n}`
of `c` on the triadic cube `□_n = {0, …, 3^n}^d` (Appendix A.1, `ss:coarse-def`), and the variance
`v_k = E ‖X_{□_k} - X̄_k‖²` of `X_□ = diag(A_□, B_□)` about `X̄_k = diag(a_k Id, b_k Id)`
(Step 2 of the proof of `p:finite-range`). The norm is the operator norm of matrices.
The operator norm of a block-diagonal matrix is the larger of the norms of its blocks, so
`‖X_□ - X̄_k‖ = max(‖A_□ - a_k Id‖, ‖B_□ - b_k Id‖)`. The variance is valued in `[0, ∞]`.
-/

namespace LatticeHC

open MeasureTheory LatticeProb
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-- The coarse-grained matrix `A_{□_n}` of `c ω` on the triadic cube `□_n = {0, …, 3^n}^d`. -/
def triadicA (c : Ω → Edge d → ℝ) (hc : ∀ ω e, 0 < c ω e) (n : ℕ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  coarseA (c ω) 0 (3 ^ n) fun e _ => hc ω e

/-- The coarse-grained matrix `B_{□_n}` of `c ω` on the triadic cube `□_n = {0, …, 3^n}^d`. -/
def triadicB (c : Ω → Edge d → ℝ) (hc : ∀ ω e, 0 < c ω e) (n : ℕ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  coarseB (c ω) 0 (3 ^ n) fun e _ => hc ω e

/-- The variance `v_k = E ‖X_{□_k} - diag(a_k Id, b_k Id)‖²` of the coarse-grained matrices at
scale `k` about the scalar matrices `a_k Id` and `b_k Id`. -/
def coarseDeviation [MeasurableSpace Ω] (μ : Measure Ω) (c : Ω → Edge d → ℝ)
    (hc : ∀ ω e, 0 < c ω e) (a b : ℕ → ℝ) (k : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (max ‖triadicA c hc k ω - a k • (1 : Matrix (Fin d) (Fin d) ℝ)‖
    ‖triadicB c hc k ω - b k • (1 : Matrix (Fin d) (Fin d) ℝ)‖) ^ 2 ∂μ

end

end LatticeHC

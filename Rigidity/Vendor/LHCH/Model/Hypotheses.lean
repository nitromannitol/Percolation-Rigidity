/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Model/Hypotheses.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Conductance
import Rigidity.Vendor.LHCH.Model.Symmetry

/-!
# The hypotheses (H1)–(H3) of the general homogenization theorem

The hypotheses of Theorem A.1 (`t:general`). They concern stationary random
conductances `c`, positive random weights `m`, and random conductances `c_R` for every integer
`R ≥ 2`, on a probability space `(Ω, P)`. The literal displays are:
* (H1): lattice symmetry of the laws, and moments of order `P = 64(d+1)`;
* (H2): a finite range of dependence of `c_R`, and the approximation of `c` by `c_R` in `L^{P_γ}`
  with `P_γ = max{64, ⌈2d/γ⌉}`;
* (H3): the normalization of `m`, and bounds on quadratic forms of the Dirichlet Green function
  `g_U` of `c` by the kernel form `𝒦(a) = Σ_{x,y} |a_x a_y| (1 + |x - y|)^{2-d}`.

Moments are lower integrals of ℝ≥0∞ powers, so `0^{-P} = ∞`. The norms are `eLpNorm`, which is `∞`
off `L^p`. The laws are pushforwards `μ.map`; the theorems that use these hypotheses assume the
fields measurable, so the pushforwards are honest.
-/

namespace LatticeHC

open MeasureTheory LatticeProb

noncomputable section

variable {d : ℕ}

/-- The moment exponent `P = 64(d+1)` of (H1). -/
def momentExp (d : ℕ) : ℝ := 64 * ((d : ℝ) + 1)

/-- The moment exponent `P = 64(d+1)` of (H1) is at least `64`. -/
theorem le_momentExp (d : ℕ) : 64 ≤ momentExp d := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold momentExp
  linarith

/-- The moment exponent `P = 64(d+1)` of (H1) is positive. -/
theorem momentExp_pos (d : ℕ) : 0 < momentExp d :=
  lt_of_lt_of_le (by norm_num) (le_momentExp d)

/-- The moment exponent `P = 64(d+1)` of (H1) is at least `1`. -/
theorem one_le_momentExp (d : ℕ) : 1 ≤ momentExp d :=
  le_trans (by norm_num) (le_momentExp d)

/-- Every `k (d+1)` with `k ≤ 64` is at most the moment exponent `P = 64(d+1)` of (H1). -/
theorem mul_add_one_le_momentExp {k : ℝ} (hk : k ≤ 64) (d : ℕ) :
    k * ((d : ℝ) + 1) ≤ momentExp d :=
  mul_le_mul_of_nonneg_right hk (by positivity)

/-- The exponent `P_γ = max{64, ⌈2d/γ⌉}` of (H2). -/
def ratioExp (d : ℕ) (γ : ℝ) : ℝ := max 64 (⌈2 * (d : ℝ) / γ⌉ : ℝ)

/-- (H1). The law of every `c_R` is invariant under the translations. The laws of `c`
and of every `c_R` are invariant under the coordinate permutations and reflections. For every
edge `e`, every `x` and every `R ≥ 2`,
`E[c_e^P + c_e^{-P} + c_R(e)^P + c_R(e)^{-P} + m_x^P] ≤ M^P`. -/
def HypH1 {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (M : ℝ) (μ : Measure Ω)
    (c : Ω → Edge d → ℝ) (m : Ω → Site d → ℝ) (cR : ℕ → Ω → Edge d → ℝ) : Prop :=
  (∀ R : ℕ, 2 ≤ R → IsEdgeShiftStationary (μ.map (cR R))) ∧ IsPointSymmetric (μ.map c) ∧
    (∀ R : ℕ, 2 ≤ R → IsPointSymmetric (μ.map (cR R))) ∧
    ∀ (e : Edge d) (x : Site d) (R : ℕ), 2 ≤ R →
      ∫⁻ ω, ENNReal.ofReal (c ω e) ^ momentExp d + ENNReal.ofReal (c ω e) ^ (-momentExp d) +
          ENNReal.ofReal (cR R ω e) ^ momentExp d +
          ENNReal.ofReal (cR R ω e) ^ (-momentExp d) + ENNReal.ofReal (m ω x) ^ momentExp d ∂μ ≤
        ENNReal.ofReal M ^ momentExp d

/-- (H2). For every `R ≥ 2`, the restrictions of `c_R` to finitely many sets of edges
whose endpoints are at pairwise `ℓ^∞` distance greater than `MR` are independent. For every edge
`e`, `‖c_e/c_R(e) - 1‖_{P_γ} + ‖c_R(e)/c_e - 1‖_{P_γ} ≤ M R^{-γ}`. -/
def HypH2 {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (γ M : ℝ) (μ : Measure Ω)
    (c : Ω → Edge d → ℝ) (cR : ℕ → Ω → Edge d → ℝ) : Prop :=
  ∀ R : ℕ, 2 ≤ R → FiniteRange (M * R) μ (cR R) ∧ ∀ e : Edge d,
    eLpNorm (fun ω => c ω e / cR R ω e - 1) (ENNReal.ofReal (ratioExp d γ)) μ +
        eLpNorm (fun ω => cR R ω e / c ω e - 1) (ENNReal.ofReal (ratioExp d γ)) μ ≤
      ENNReal.ofReal (M * (R : ℝ) ^ (-γ))

/-- (H3). For every `x`, `E m_x = 1`. For every finite `U` and every deterministic `a`
supported in `U`, `‖(ma)ᵀ g_U (ma)‖_2 ≤ M 𝒦(a)` and `‖Σ_x a_x (m_x - 1)‖_4 ≤ M 𝒦(a)^{1/2}`. -/
def HypH3 {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (M : ℝ) (μ : Measure Ω)
    (c : Ω → Edge d → ℝ) (m : Ω → Site d → ℝ) : Prop :=
  (∀ x : Site d, ∫ ω, m ω x ∂μ = 1) ∧
    ∀ (U : Finset (Site d)) (a : Site d → ℝ), (∀ x, x ∉ U → a x = 0) →
      eLpNorm (fun ω => ∑ x ∈ U, ∑ z ∈ U,
          m ω x * a x * dirichletGreen (c ω) U x z * (m ω z * a z)) 2 μ ≤
        ENNReal.ofReal (M * kernelForm U a) ∧
      eLpNorm (fun ω => ∑ x ∈ U, a x * (m ω x - 1)) 4 μ ≤
        ENNReal.ofReal (M * Real.sqrt (kernelForm U a))

/-- The hypotheses of `p:finite-range`. The law of the positive conductances `c`
is invariant under the translations, the coordinate permutations and the reflections. The
restrictions of `c` to finitely many sets of edges whose endpoints are at pairwise `ℓ^∞` distance
greater than `R` are independent. And `sup_e (E[c_e^P + c_e^{-P}])^{1/P} ≤ M`
(`(e:FR-moments)`). -/
def IsFiniteRangeLaw {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (M R : ℝ) (μ : Measure Ω)
    (c : Ω → Edge d → ℝ) : Prop :=
  IsEdgeShiftStationary (μ.map c) ∧ IsPointSymmetric (μ.map c) ∧ FiniteRange R μ c ∧
    ∀ e : Edge d, (∫⁻ ω, ENNReal.ofReal (c ω e) ^ momentExp d +
      ENNReal.ofReal (c ω e) ^ (-momentExp d) ∂μ) ^ (1 / momentExp d) ≤ ENNReal.ofReal M

end

end LatticeHC

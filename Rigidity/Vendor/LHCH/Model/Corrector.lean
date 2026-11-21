/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Model/Corrector.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Symmetry

/-!
# The effective conductivity of stationary random conductances

The construction `(e:corrector)` of the paper (Appendix A), which is the classical
construction of the corrector.
* `Ω` carries a probability measure and a measure-preserving action `(τ_x)_{x ∈ ℤ^d}` of `ℤ^d`.
  Conductances `c` are stationary when `c_{x+e} = c_e ∘ τ_x`.
* `𝓗_c` is the Hilbert space of random vectors `F` with `‖F‖²_c = E Σ_j c_{0,e_j} F_j²`, and `𝒢` is
  the closure of the gradients `∇_j φ = φ ∘ τ_{e_j} - φ` of bounded measurable `φ`.
* With `F_p = (Id - Π) p`, the effective conductivity is `p · A_* q = ⟨F_p, F_q⟩_c`.

`𝓗_c` is realized isometrically inside `L²(Ω; ℝ^d)` through `F ↦ (√c_{0,e_j} F_j)_j`. The orthogonal
projection onto the image of `𝒢` corresponds to `Π`. The construction needs only `E c_{0,e_j} < ∞`,
which the paper's `E[c_e + c_e⁻¹] < ∞` provides; that hypothesis is an argument of the definition,
so no value is invented off it.

The embedding `sqrtWeighted` uses `Real.sqrt`, which sends negative values to `0`, so it is the
intended one only for positive conductances. The definitions and membership lemmas of this file do
not assume `0 < c`; the zero-curl results in `Support` do, through `unweightedCoord_sqrtWeighted`,
recovering `F` from `sqrtWeighted c F` coordinatewise by dividing by `√c_{0,j}`, which is nonzero
when `0 < c`.

Random variables are equal when they agree almost surely, so stationarity is almost sure equality.
-/

namespace LatticeHC

open MeasureTheory LatticeProb

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- A measure-preserving action `(τ_x)_{x ∈ ℤ^d}` of `ℤ^d` on `(Ω, μ)` (Appendix A). -/
structure LatticeAction (d : ℕ) (μ : Measure Ω) where
  /-- The map `τ_x`. -/
  act : Site d → Ω → Ω
  /-- The action of `0` is the identity. -/
  act_zero : ∀ ω, act 0 ω = ω
  /-- The action is additive: `τ_{x+y} = τ_x ∘ τ_y`. -/
  act_add : ∀ x y ω, act (x + y) ω = act x (act y ω)
  /-- Each `τ_x` is measurable. -/
  measurable_act : ∀ x, Measurable (act x)
  /-- Each `τ_x` preserves `μ`. -/
  map_act : ∀ x, μ.map (act x) = μ

/-- Random conductances are stationary: `c_{x+e} = c_e ∘ τ_x` for every `x` and every edge `e`, as
random variables (Appendix A). -/
def IsStationary {μ : Measure Ω} (τ : LatticeAction d μ) (c : Ω → Edge d → ℝ) : Prop :=
  ∀ (x : Site d) (e : Edge d), (fun ω => c ω (x + e.1, e.2)) =ᵐ[μ] fun ω => c (τ.act x ω) e

/-- The embedding `F ↦ (√c_{0,e_j} F_j)_j` of a random vector into `L²(Ω; ℝ^d)`. -/
def sqrtWeighted (c : Ω → Edge d → ℝ) (F : Ω → Fin d → ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun j => Real.sqrt (c ω (0, j)) * F ω j

/-- The gradient `∇_j φ = φ ∘ τ_{e_j} - φ` of a function on `Ω`. -/
def stationaryGrad {μ : Measure Ω} (τ : LatticeAction d μ) (φ : Ω → ℝ) (ω : Ω) : Fin d → ℝ :=
  fun j => φ (τ.act (unit j) ω) - φ ω

/-- The square of a square root is bounded by the absolute value of the radicand. -/
private lemma sq_sqrt_le_abs (x : ℝ) : (Real.sqrt x) ^ 2 ≤ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [Real.sq_sqrt hx]
    exact le_abs_self x
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hx)]
    simp

/-- The weighted embedding `ω ↦ (√(c ω (0,j)) F ω j)_j` is measurable. -/
private lemma measurable_sqrtWeighted (c : Ω → Edge d → ℝ) (F : Ω → Fin d → ℝ)
    (hcm : ∀ e, Measurable fun ω => c ω e) (hF : Measurable F) :
    Measurable (sqrtWeighted c F) := by
  have hcoord : Measurable (fun ω : Ω => fun j : Fin d =>
      Real.sqrt (c ω (0, j)) * F ω j) :=
    measurable_pi_lambda _ fun j =>
      (Real.continuous_sqrt.measurable.comp (hcm (0, j))).mul
        ((measurable_pi_apply j).comp hF)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp hcoord

omit [MeasurableSpace Ω] in
/-- The squared norm of the weighted embedding is bounded coordinatewise. -/
private lemma norm_sq_sqrtWeighted_le (c : Ω → Edge d → ℝ) (F : Ω → Fin d → ℝ)
    (ω : Ω) :
    ‖sqrtWeighted c F ω‖ ^ 2 ≤ ∑ j, |c ω (0, j)| * (F ω j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [sqrtWeighted, WithLp.ofLp_toLp, mul_pow]
  exact mul_le_mul_of_nonneg_right (sq_sqrt_le_abs _) (sq_nonneg _)

/-- The coordinatewise weighted square bound is integrable. -/
private lemma integrable_abs_mul_sum {μ : Measure Ω} {c : Ω → Edge d → ℝ}
    (hc : ∀ j, Integrable (fun ω => c ω (0, j)) μ) (a : Fin d → ℝ) :
    Integrable (fun ω => ∑ j, |c ω (0, j)| * a j) μ := by
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  exact ((hc j).abs).mul_const (a j)

/-- The squared norm of the weighted gradient is bounded by the conductance bound. -/
private lemma norm_sq_sqrtWeighted_grad_le {μ : Measure Ω} (τ : LatticeAction d μ)
    {c : Ω → Edge d → ℝ} {φ : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |φ ω| ≤ C) (ω : Ω) :
    ‖sqrtWeighted c (stationaryGrad τ φ) ω‖ ^ 2 ≤
      ∑ j, |c ω (0, j)| * (2 * |C|) ^ 2 := by
  refine (norm_sq_sqrtWeighted_le c (stationaryGrad τ φ) ω).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : |φ (τ.act (unit j) ω)| ≤ C := hC _
  have h2 : |φ ω| ≤ C := hC _
  have h3 : |stationaryGrad τ φ ω j| ≤ 2 * |C| := by
    calc |stationaryGrad τ φ ω j| = |φ (τ.act (unit j) ω) - φ ω| := rfl
      _ ≤ |φ (τ.act (unit j) ω)| + |φ ω| := abs_sub _ _
      _ ≤ C + C := add_le_add h1 h2
      _ ≤ |C| + |C| := add_le_add (le_abs_self C) (le_abs_self C)
      _ = 2 * |C| := by ring
  calc (stationaryGrad τ φ ω j) ^ 2 = |stationaryGrad τ φ ω j| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * |C|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2

/-- A constant vector `p` belongs to `𝓗_c` when `E c_{0,e_j} < ∞`. -/
theorem memLp_sqrtWeighted_const {μ : Measure Ω} {c : Ω → Edge d → ℝ}
    (hcm : ∀ e, Measurable fun ω => c ω e) (hc : ∀ j, Integrable (fun ω => c ω (0, j)) μ)
    (p : Fin d → ℝ) : MemLp (sqrtWeighted c fun _ => p) 2 μ := by
  have hmeas : Measurable (sqrtWeighted c fun _ => p) :=
    measurable_sqrtWeighted c _ hcm measurable_const
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  refine Integrable.mono' (integrable_abs_mul_sum hc fun j => (p j) ^ 2)
    ((hmeas.norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_sq_sqrtWeighted_le c (fun _ => p) ω

/-- The gradient of a bounded measurable function belongs to `𝓗_c` when `E c_{0,e_j} < ∞`. -/
theorem memLp_sqrtWeighted_grad {μ : Measure Ω} (τ : LatticeAction d μ)
    {c : Ω → Edge d → ℝ}
    (hcm : ∀ e, Measurable fun ω => c ω e) (hc : ∀ j, Integrable (fun ω => c ω (0, j)) μ)
    {φ : Ω → ℝ} (hφ : Measurable φ) (hb : ∃ C, ∀ ω, |φ ω| ≤ C) :
    MemLp (sqrtWeighted c (stationaryGrad τ φ)) 2 μ := by
  obtain ⟨C, hC⟩ := hb
  have hFmeas : Measurable (stationaryGrad τ φ) := by
    apply measurable_pi_lambda
    intro j
    exact (hφ.comp (τ.measurable_act (unit j))).sub hφ
  have hmeas : Measurable (sqrtWeighted c (stationaryGrad τ φ)) :=
    measurable_sqrtWeighted c _ hcm hFmeas
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  refine Integrable.mono' (integrable_abs_mul_sum hc fun _ => (2 * |C|) ^ 2)
    ((hmeas.norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_sq_sqrtWeighted_grad_le τ hC ω

variable {μ : Measure Ω}

/-- The image of `𝒢` in `L²(Ω; ℝ^d)`: the closure of the span of the gradients of bounded measurable
functions (Appendix A). -/
def gradientSubspace (τ : LatticeAction d μ) (c : Ω → Edge d → ℝ)
    (hcm : ∀ e, Measurable fun ω => c ω e) (hc : ∀ j, Integrable (fun ω => c ω (0, j)) μ) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin d)) 2 μ) :=
  (Submodule.span ℝ {G | ∃ (φ : Ω → ℝ) (hφ : Measurable φ) (hb : ∃ C, ∀ ω, |φ ω| ≤ C),
    G = (memLp_sqrtWeighted_grad τ hcm hc hφ hb).toLp _}).topologicalClosure

instance (τ : LatticeAction d μ) (c : Ω → Edge d → ℝ) (hcm : ∀ e, Measurable fun ω => c ω e)
    (hc : ∀ j, Integrable (fun ω => c ω (0, j)) μ) :
    (gradientSubspace τ c hcm hc).HasOrthogonalProjection := by
  haveI : CompleteSpace (gradientSubspace τ c hcm hc) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The image of `F_p = (Id - Π) p` in `L²(Ω; ℝ^d)` (`(e:corrector)`). -/
def correctedField (τ : LatticeAction d μ) (c : Ω → Edge d → ℝ)
    (hcm : ∀ e, Measurable fun ω => c ω e) (hc : ∀ j, Integrable (fun ω => c ω (0, j)) μ)
    (p : Fin d → ℝ) : Lp (EuclideanSpace ℝ (Fin d)) 2 μ :=
  (memLp_sqrtWeighted_const hcm hc p).toLp _ -
    (gradientSubspace τ c hcm hc).starProjection ((memLp_sqrtWeighted_const hcm hc p).toLp _)

/-- The effective conductivity `A_*` of stationary conductances `c`, `p · A_* q = ⟨F_p, F_q⟩_c`
(`(e:corrector)`), for `E c_{0,e_j} < ∞`. -/
def effConductivity (τ : LatticeAction d μ) (c : Ω → Edge d → ℝ)
    (hcm : ∀ e, Measurable fun ω => c ω e) (hc : ∀ j, Integrable (fun ω => c ω (0, j)) μ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => inner ℝ (correctedField τ c hcm hc (Pi.single i 1))
    (correctedField τ c hcm hc (Pi.single j 1))

end

end LatticeHC

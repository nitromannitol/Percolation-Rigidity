import Rigidity.Proofs.Green.PointwiseHeatD
import Rigidity.Proofs.Green.GeometricMeanD

/-!
# The heat kernel against the Gaussian at a pair of points, with the Gaussian factor

At one configuration, for `x, y ∈ K` and `t = 2s`, `s ≥ 2`, with

* the point source at both poles: `‖p_s(·, x) - G^x_s‖, ‖p_s(·, y) - G^y_s‖ ≤ E s^{ε - d/4 - 1/2}`,
* the diagonal bound `p_{2s}(y, y) ≤ C_B s^{-d/2}`,
* Proposition A.7 at `x`, `y` (time `s`) and at `midLattice x y` (time `s/2`), with errors
  `C_A s^{η - 1/2} ≤ θ/2` (`η ≤ ε`),

`|p_t(x, y) - θ^{-1} p̄(t, x - y)| ≤ C₁ t^{-d/2 - 1/2 + ε}` (`abs_vsrwHeat_sub_le_rpow`). Together
with the Gaussian bound `C₂ t^{-d/2} e^{-|x - y|²/(C₃ t)}` of both terms (the Gaussian upper bound
of the heat kernel), the geometric mean (`le_of_two_bounds`) gives the error of Theorem 1 of
Dario–Gu at one configuration (`abs_vsrwHeat_sub_le_gaussian`).
-/

open scoped Classical
open LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ} [NeZero d] {ω : Configuration d} {K : OpenComponent ω} {σ θ : ℝ}

/-- The norm of a column of the heat kernel: `‖p_s(·, y)‖ = p_{2s}(y, y)^{1/2}`. -/
theorem l2norm_vsrwHeat_col {s : ℝ} (hs : 0 ≤ s) (y : Vertex d) :
    l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) s z y) =
      Real.sqrt (vsrwHeat (openGraph ω) (2 * d) (s + s) y y) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have h := hasSum_heatDeriv_sq hD hdeg 0 hs y
  have e : heatDeriv (openGraph ω) (2 * d) (0 + 0) (s + s) y y =
      vsrwHeat (openGraph ω) (2 * d) (s + s) y y := rfl
  rw [e] at h
  have h2 : HasSum (fun z => vsrwHeat (openGraph ω) (2 * d) s z y ^ 2)
      (vsrwHeat (openGraph ω) (2 * d) (s + s) y y) :=
    h.congr_fun fun z => by rw [heatDeriv_zero, vsrwHeat_symm hD hdeg s z y]
  unfold l2norm
  rw [h2.tsum_eq]

omit [NeZero d] in
/-- The norm of the normalized Gaussian. -/
theorem l2norm_clusterGaussNorm_le (hσ : 0 < σ) (hθ : 0 < θ) {s : ℝ} (hs : 0 < s) {x : Vertex d}
    (hM1 : θ / 2 ≤ clusterGaussMass K σ s x) (hM2 : clusterGaussMass K σ s x ≤ 2 * θ) :
    l2norm (clusterGaussNorm K σ s x) ≤ 2 / θ * psGauss d σ θ * s ^ (-((d : ℝ) / 4)) := by
  have hM0 : 0 < clusterGaussMass K σ s x := by linarith
  have e : clusterGaussNorm K σ s x =
      fun z => (clusterGaussMass K σ s x)⁻¹ * clusterInd K σ s x z := by
    funext z; unfold clusterGaussNorm; ring
  rw [e, l2norm_const_mul, abs_of_pos (inv_pos.2 hM0)]
  have hb := l2norm_clusterInd_le (K := K) (y := x) hσ hθ hs hM2
  have hMi : (clusterGaussMass K σ s x)⁻¹ ≤ 2 / θ := by
    rw [inv_le_comm₀ hM0 (by positivity)]; field_simp; linarith
  calc _ ≤ 2 / θ * (psGauss d σ θ * s ^ (-((d : ℝ) / 4))) :=
        mul_le_mul hMi hb (l2norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The constant `C₁` of the heat kernel against the Gaussian. -/
noncomputable def pwConst (d : ℕ) (σ θ E CB CA : ℝ) : ℝ :=
  E * Real.sqrt CB + 2 / θ * psGauss d σ θ * E +
    (4 * Real.pi * σ) ^ (-((d : ℝ) / 2)) *
      (4 * (CA * Real.sqrt 2 + 3 * CA + shiftConstD d σ d * Real.sqrt 2) / θ ^ 2)

omit [NeZero d] in
theorem shiftConstD_nonneg (hσ : 0 < σ) (ρ : ℝ) (hρ : 0 ≤ ρ) : 0 ≤ shiftConstD d σ ρ := by
  unfold shiftConstD
  have := one_le_gaussMassBoundD (d := d) hσ
  positivity

/-- **The heat kernel against the Gaussian at a pair of points.** -/
theorem abs_vsrwHeat_sub_le_rpow (hσ : 0 < σ) (hθ : 0 < θ) {s η ε E CB CA : ℝ} (hs : 2 ≤ s)
    (hη0 : 0 < η) (hηε : η ≤ ε) (hCB : 0 ≤ CB) (hCA : 0 ≤ CA) {x y : Vertex d}
    (hEx : l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) s z x - clusterGaussNorm K σ s x z) ≤
      E * s ^ (ε - (d : ℝ) / 4 - 1 / 2))
    (hEy : l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) s z y - clusterGaussNorm K σ s y z) ≤
      E * s ^ (ε - (d : ℝ) / 4 - 1 / 2))
    (hdiag : vsrwHeat (openGraph ω) (2 * d) (s + s) y y ≤ CB * s ^ (-((d : ℝ) / 2)))
    (hAx : |clusterGaussMass K σ s x - θ| ≤ CA * s ^ (η - 1 / 2))
    (hAy : |clusterGaussMass K σ s y - θ| ≤ CA * s ^ (η - 1 / 2))
    (hA' : |clusterGaussMass K σ (s / 2) (midLattice x y) - θ| ≤ CA * (s / 2) ^ (η - 1 / 2))
    (hsm : CA * s ^ (η - 1 / 2) ≤ θ / 2) :
    |vsrwHeat (openGraph ω) (2 * d) (2 * s) x y - θ⁻¹ * gaussianHeatD d σ (2 * s) (edzD x y)| ≤
      pwConst d σ θ E CB CA * s ^ (ε - (d : ℝ) / 2 - 1 / 2) := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hpow : ∀ a b : ℝ, a ≤ b → s ^ a ≤ s ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le hs1 hab
  have hmul : ∀ a b : ℝ, s ^ a * s ^ b = s ^ (a + b) := fun a b => (Real.rpow_add hs0 a b).symm
  -- the columns
  have hPy : l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) s z y) ≤
      Real.sqrt CB * s ^ (-((d : ℝ) / 4)) := by
    rw [l2norm_vsrwHeat_col hs0.le]
    calc _ ≤ Real.sqrt (CB * s ^ (-((d : ℝ) / 2))) := Real.sqrt_le_sqrt hdiag
      _ = _ := by
        rw [Real.sqrt_mul hCB, Real.sqrt_eq_rpow (s ^ _), ← Real.rpow_mul hs0.le]
        ring_nf
  have hx' := abs_le.1 hAx
  have hGx := l2norm_clusterGaussNorm_le (K := K) hσ hθ hs0 (x := x) (by linarith) (by linarith)
  have h := abs_vsrwHeat_sub_gaussianHeatD_le (K := K) hσ hθ hs hEx hEy hPy hGx hAx hAy hsm hsm hA'
  refine h.trans ?_
  -- the three parts
  have h1 : E * s ^ (ε - (d : ℝ) / 4 - 1 / 2) * (Real.sqrt CB * s ^ (-((d : ℝ) / 4))) =
      E * Real.sqrt CB * s ^ (ε - (d : ℝ) / 2 - 1 / 2) := by
    rw [show E * s ^ (ε - (d : ℝ) / 4 - 1 / 2) * (Real.sqrt CB * s ^ (-((d : ℝ) / 4))) =
      E * Real.sqrt CB * (s ^ (ε - (d : ℝ) / 4 - 1 / 2) * s ^ (-((d : ℝ) / 4))) by ring, hmul]
    congr 2; ring
  have h2 : 2 / θ * psGauss d σ θ * s ^ (-((d : ℝ) / 4)) * (E * s ^ (ε - (d : ℝ) / 4 - 1 / 2)) =
      2 / θ * psGauss d σ θ * E * s ^ (ε - (d : ℝ) / 2 - 1 / 2) := by
    rw [show 2 / θ * psGauss d σ θ * s ^ (-((d : ℝ) / 4)) * (E * s ^ (ε - (d : ℝ) / 4 - 1 / 2)) =
      2 / θ * psGauss d σ θ * E * (s ^ (-((d : ℝ) / 4)) * s ^ (ε - (d : ℝ) / 4 - 1 / 2)) by ring,
      hmul]
    congr 2; ring
  -- the Gaussian part
  have hb : gaussianHeatD d σ (2 * s) (edzD x y) ≤
      (4 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * s ^ (-((d : ℝ) / 2)) := by
    refine (gaussianHeatD_le_sup hσ (by linarith) _).trans_eq ?_
    rw [show 2 * Real.pi * σ * (2 * s) = 4 * Real.pi * σ * s by ring,
      Real.mul_rpow (by positivity) hs0.le]
  have hb0 : 0 ≤ gaussianHeatD d σ (2 * s) (edzD x y) :=
    gaussianHeatD_nonneg' σ (2 * s) (by positivity) _
  have hhalf : (s / 2) ^ (η - 1 / 2) ≤ Real.sqrt 2 * s ^ (η - 1 / 2) := by
    rw [Real.div_rpow hs0.le (by norm_num), div_eq_mul_inv, mul_comm, ← Real.rpow_neg (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hshift : (s / 2) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 * s ^ (η - 1 / 2) := by
    rw [Real.div_rpow hs0.le (by norm_num), div_eq_mul_inv, mul_comm, ← Real.rpow_neg (by norm_num),
      neg_neg, ← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) (by positivity)
  have hsh0 := shiftConstD_nonneg (d := d) hσ d (Nat.cast_nonneg d)
  have herr : CA * (s / 2) ^ (η - 1 / 2) + shiftConstD d σ d * (s / 2) ^ (-(1 / 2 : ℝ)) +
      CA * s ^ (η - 1 / 2) + 2 * (CA * s ^ (η - 1 / 2)) ≤
      (CA * Real.sqrt 2 + 3 * CA + shiftConstD d σ d * Real.sqrt 2) * s ^ (η - 1 / 2) := by
    have := mul_le_mul_of_nonneg_left hhalf hCA
    have := mul_le_mul_of_nonneg_left hshift hsh0
    nlinarith
  have hg : gaussianHeatD d σ (2 * s) (edzD x y) *
      (4 * (CA * (s / 2) ^ (η - 1 / 2) + shiftConstD d σ d * (s / 2) ^ (-(1 / 2 : ℝ)) +
        CA * s ^ (η - 1 / 2) + 2 * (CA * s ^ (η - 1 / 2))) / θ ^ 2) ≤
      (4 * Real.pi * σ) ^ (-((d : ℝ) / 2)) *
        (4 * (CA * Real.sqrt 2 + 3 * CA + shiftConstD d σ d * Real.sqrt 2) / θ ^ 2) *
        s ^ (ε - (d : ℝ) / 2 - 1 / 2) := by
    have hK : 0 ≤ CA * Real.sqrt 2 + 3 * CA + shiftConstD d σ d * Real.sqrt 2 := by positivity
    calc _ ≤ ((4 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * s ^ (-((d : ℝ) / 2))) *
          (4 * ((CA * Real.sqrt 2 + 3 * CA + shiftConstD d σ d * Real.sqrt 2) *
            s ^ (η - 1 / 2)) / θ ^ 2) := by
          apply mul_le_mul hb _ (by
            have : 0 ≤ CA * (s / 2) ^ (η - 1 / 2) + shiftConstD d σ d * (s / 2) ^ (-(1 / 2 : ℝ)) +
              CA * s ^ (η - 1 / 2) + 2 * (CA * s ^ (η - 1 / 2)) := by positivity
            positivity) (by positivity)
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = (4 * Real.pi * σ) ^ (-((d : ℝ) / 2)) *
          (4 * (CA * Real.sqrt 2 + 3 * CA + shiftConstD d σ d * Real.sqrt 2) / θ ^ 2) *
          (s ^ (-((d : ℝ) / 2)) * s ^ (η - 1 / 2)) := by ring
      _ ≤ _ := by
          rw [hmul]
          exact mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) (by positivity)
  unfold pwConst
  rw [h1, h2]
  linarith [hg]

end Rigidity.Green

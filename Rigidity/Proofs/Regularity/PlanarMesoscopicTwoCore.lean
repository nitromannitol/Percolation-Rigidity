import Rigidity.Proofs.Regularity.PlanarMesoscopicTwoTopBounds

/-!
# The deterministic core of Lemma 7.3 at `k = 2` in the plane

Armstrong and Dario (arXiv:1609.09431v2), Lemma 7.3, (7.18) at `k = 2`, for one planar
configuration: if the coarsening `U = [u]_𝒫` of every function harmonic on `𝒞_∞ ∩ B_{R'}`,
`R' ≥ A X`, satisfies the harmonic approximation hypothesis of Lemma 7.2 on the balls of `ℤ²` and
is close to `u` on the cluster balls (the two conclusions of Lemma 7.1 in the form of the proof of
Lemma 7.3), and if on `B_R` the partition cubes have side at most `c R^{α/2}`, their sizes have
bounded first and second moments, and the cluster is dense in the cubes, then for
`r ∈ [r₀ X, R / 2]`
`D̃_2(r) ≤ C (r / R)³ D̃_2(R) + C r^{-α/2} (r / R) R^{-1} ‖u‖_{ℓ²(𝒞_∞ ∩ B_R)}`
(`mesoscopicDegreeTwo_core`), with `D̃_2(r)` the excess of `u` over the harmonic quadratic
polynomials in the normalization `r^{-1} ‖·‖_{ℓ²(𝒞_∞ ∩ B_r)}`.

The proof follows the source: Lemma 7.2 at `k = 2` and `k = 0` for `U` on the balls of `ℤ²` up to
the top scale `T = R / (8A)` (`armstrongDario_lemma_7_2_two_latticeHarmonic`,
`armstrongDario_lemma_7_2_zero_latticeHarmonic`), the top-scale bounds of `U` by the cluster
excesses of `u` (`coarse_top_bounds`, `harmonicApproximation_error_le`), Step 1 of the proof
(`clusterExcess_two_le`, `clusterExcess_zero_le`) to return to `u`, and the Lipschitz bound
`D̃_0(s) ≤ C s R^{-1} D̃_0(R)` of `u` proved first by an induction over the scales `s, A s, A² s, …`
(the case `k = 0` of the same argument), which bounds the coarsening error `K s^{-1} D̃_0(A s)`.
The loss `R^{α/2}` of the crude bound of the coarse oscillation at the top scale is absorbed by
the factor `(4T)^{-α}` of the harmonic approximation error, leaving the exponent `δ = α / 2`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {ω : Configuration 2}

theorem HarmonicApproximation.mono_scale {F : Type*} [AddCommGroup F]
    {N : ℝ → AddGroupSeminorm F} {Abar : ℝ → Set F} {P₀ : AddSubgroup F} {A α X X' R E : ℝ}
    {u : F} (h : HarmonicApproximation N Abar P₀ A α X R E u) (hX : X ≤ X') :
    HarmonicApproximation N Abar P₀ A α X' R E u :=
  fun r hr hrR => h r (hX.trans hr) hrR

/-- The excess of a cluster function over a family, on a smaller ball. -/
theorem iInf_clusterBallVolumeL2_le_of_le {ι : Type*} [Nonempty ι] (C : OpenComponent ω)
    {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) (u : C → ℝ) (w : ι → C → ℝ) :
    (⨅ i, clusterBallVolumeL2 C s (u - w i)) ≤ 0 + R / s * ⨅ i, clusterBallVolumeL2 C R (u - w i) :=
  le_add_mul_iInf (div_nonneg (hs.le.trans hsR) hs.le) fun i => by
    rw [zero_add]
    exact (iInf_le_of_le (fun _ => clusterBallVolumeL2_nonneg _ _ _) i).trans
      (clusterBallVolumeL2_le_of_le C hs hsR _)

theorem rpow_cube_le {r R β : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R) (hβ : 0 ≤ β) :
    (r / R) ^ 3 * R ^ (1 - β) ≤ r ^ (1 - β) := by
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := by linarith
  have e1 : R ^ (1 - β) = R * R ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add hR0, Real.rpow_one]
  have e2 : r ^ (1 - β) = r * r ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_one]
  rw [e1, e2]
  have h1 : R ^ (-β) ≤ r ^ (-β) := Real.rpow_le_rpow_of_nonpos hr0 hrR (by linarith)
  have h2 : (r / R) ^ 3 * R ≤ r := by
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h4 : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr0.le hrR 2
    have h5 := mul_le_mul_of_nonneg_left h4 (mul_pos hr0 hR0).le
    nlinarith
  have h3 : 0 ≤ R ^ (-β) := Real.rpow_nonneg hR0.le _
  calc (r / R) ^ 3 * (R * R ^ (-β)) = (r / R) ^ 3 * R * R ^ (-β) := by ring
    _ ≤ r * R ^ (-β) := mul_le_mul_of_nonneg_right h2 h3
    _ ≤ r * r ^ (-β) := mul_le_mul_of_nonneg_left h1 hr0.le

/-- The scale of the cube sides: `c R^{α/2} ≤ R / 16` when `(16 c + 1)² ≤ R`. -/
theorem mul_rpow_half_le {c R α : ℝ} (hc : 0 ≤ c) (hα1 : α ≤ 1)
    (hR : (16 * c + 1) ^ 2 ≤ R) : c * R ^ (α / 2) ≤ R / 16 := by
  have hR1 : 1 ≤ R := le_trans (by nlinarith) hR
  have hR0 : 0 < R := by linarith
  have h1 : R ^ (α / 2) ≤ R ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hs : R ^ ((1 : ℝ) / 2) = Real.sqrt R := (Real.sqrt_eq_rpow R).symm
  rw [hs] at h1
  have h2 : 16 * c + 1 ≤ Real.sqrt R := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 16 * c + 1)]
    exact Real.sqrt_le_sqrt hR
  have h3 : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR0.le
  have h4 : c * Real.sqrt R ≤ R / 16 := by
    have : 16 * c * Real.sqrt R ≤ Real.sqrt R * Real.sqrt R := by
      have := Real.sqrt_nonneg R
      nlinarith
    linarith
  calc c * R ^ (α / 2) ≤ c * Real.sqrt R := mul_le_mul_of_nonneg_left h1 hc
    _ ≤ R / 16 := h4

/-- **The induction over the scales `s, A s, A² s, …`** for the Lipschitz bound of order zero:
if `f(s) ≤ (16 A)² s G` above `T / 2` and `f(s) ≤ K s^{-1} f(A s) + 3 C₄ s G` on `[s₁, T / 2]`
with `s₁ > 2 K A`, then `f(s) ≤ max ((16 A)²) (6 C₄) s G` on `[s₁, R / 2]`. -/
theorem le_of_scale_induction {f : ℝ → ℝ} {A K s₁ T R C₄ G : ℝ} (hA : 2 ≤ A) (hK : 0 ≤ K)
    (hG : 0 ≤ G) (hs₁ : 2 * K * A < s₁) (hs₁0 : 0 < s₁) (hAT : A * (T / 2) ≤ R / 2)
    (hbase : ∀ s, T / 2 < s → s ≤ R / 2 → f s ≤ (16 * A) ^ 2 * s * G)
    (hstep : ∀ s, s₁ ≤ s → s ≤ T / 2 → f s ≤ K / s * f (A * s) + 3 * C₄ * s * G) :
    ∀ s, s₁ ≤ s → s ≤ R / 2 → f s ≤ max ((16 * A) ^ 2) (6 * C₄) * s * G := by
  set C₅ := max ((16 * A) ^ 2) (6 * C₄) with hC₅
  have hA0 : 0 < A := by linarith
  have hA1 : 1 < A := by linarith
  have hC₅0 : 0 ≤ C₅ := (sq_nonneg _).trans (le_max_left _ _)
  have hclaim : ∀ n : ℕ, ∀ s, s₁ ≤ s → s ≤ R / 2 → T / 2 < A ^ n * s → f s ≤ C₅ * s * G := by
    intro n
    induction n with
    | zero =>
      intro s _ hsR hs
      rw [pow_zero, one_mul] at hs
      have := hbase s hs hsR
      have : (16 * A) ^ 2 * s * G ≤ C₅ * s * G :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by linarith)) hG
      linarith
    | succ n ih =>
      intro s hs hsR hsn
      by_cases hsT : T / 2 < s
      · have := hbase s hsT hsR
        have : (16 * A) ^ 2 * s * G ≤ C₅ * s * G :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by linarith)) hG
        linarith
      · push Not at hsT
        have hs0 : 0 < s := hs₁0.trans_le hs
        have hAs1 : s₁ ≤ A * s := hs.trans (le_mul_of_one_le_left hs0.le hA1.le)
        have hAsR : A * s ≤ R / 2 := (mul_le_mul_of_nonneg_left hsT hA0.le).trans hAT
        have hAsn : T / 2 < A ^ n * (A * s) := by rw [← mul_assoc, ← pow_succ]; exact hsn
        have hih := ih (A * s) hAs1 hAsR hAsn
        have h1 := hstep s hs hsT
        have hKs : 0 ≤ K / s := div_nonneg hK hs0.le
        have h2 : K / s * f (A * s) ≤ K / s * (C₅ * (A * s) * G) :=
          mul_le_mul_of_nonneg_left hih hKs
        have h3 : K / s * (C₅ * (A * s) * G) = K * A * C₅ * G := by field_simp
        have h4 : K * A * C₅ * G ≤ C₅ * s * G / 2 := by
          have : 2 * K * A ≤ s := by linarith
          have := mul_le_mul_of_nonneg_right this (mul_nonneg hC₅0 hG)
          nlinarith
        have h5 : 3 * C₄ * s * G ≤ C₅ * s * G / 2 := by
          have : 6 * C₄ ≤ C₅ := le_max_right _ _
          have := mul_le_mul_of_nonneg_right this (mul_nonneg hs0.le hG)
          nlinarith
        linarith
  intro s hs hsR
  have hs0 : 0 < s := hs₁0.trans_le hs
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T / 2 / s) hA1
  exact hclaim n s hs hsR (by rwa [div_lt_iff₀ hs0] at hn)

end Rigidity.Proofs.Regularity

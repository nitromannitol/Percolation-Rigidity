import Rigidity.Proofs.Green.GreenTimeIntegralThree
import Rigidity.Proofs.Green.GreenQuantitativeAllDim
import Rigidity.Proofs.Green.SupercriticalGreenColumn
import PercolationClusterHomogenization.Proofs.Percolation.SupercriticalUniqueness

/-!
# Theorem 2 of Dario and Gu for `d ≥ 3` from Theorem 1

`supercriticalBondGreenQuantitativeThree_of_heatKernel` proves the `d ≥ 3` part of the
quantitative Green estimate of Dario and Gu (`SupercriticalBondGreenQuantitativeThree`, Theorem 2,
(1.10)) from

* Theorem 1 of Dario and Gu in dimension `d` (`DarioGuHeatKernelD d`): the heat kernel `p(t, x, y)`
  of the variable speed random walk on the open graph is `θ^{-1} p̄(t, x - y)` up to
  `C t^{-d/2 - (1/2 - δ)} e^{-|x-y|²/(Ct)}` for `t ≥ max(1, T(y), |x - y|)`, and
* the small-time bound `p(t, x, y) ≤ C e^{-|x-y|/C}` for `t ≤ |x - y|` (`HeatSmallTimeD d`), a
  consequence of the Carne–Varopoulos bound (Dario–Gu, Proposition 2.15),

with the uniqueness of the Green columns for `d ≥ 3` (`greenColumnExistence_of_three_le`). The
proof is that of the source, §5: with `κ = σθ/2`, `ḡ = continuumGreen d κ` is
`θ^{-1} ∫_0^∞ p̄(t, ·) dt` (`inv_mul_integral_gaussianHeatD_eq`); every Green column with pole `y`
is `G = ∫_0^∞ p(t, ·, y) dt` (`isGreenColumn_timeGreenD`); and
`|G(x) - ḡ(x - y)| ≤ C |x - y|^{2 - 2β}` with `β = d/2 + 1/2 - δ/2`
(`abs_timeGreenD_sub_le`). The minimal scale is `max(T(y), 1)`.
-/

open MeasureTheory Set Real Filter Topology LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-! ### The constants -/

namespace HeatBoundsD

/-- The constant of `abs_timeGreenD_sub_le`. -/
noncomputable def errConst (d : ℕ) (σ θ C₁ C₂ β : ℝ) : ℝ :=
  d.factorial * C₂ ^ (d + 1) +
    θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * (4 * σ) ^ ((d : ℝ) / 2 - 1) *
      Real.Gamma ((d : ℝ) / 2 - 1) * (4 * σ) +
    C₁ ^ β * Real.Gamma (β - 1)

variable [NeZero d] {ω : Configuration d} {K : OpenComponent ω} {y : Vertex d}
  {σ θ C₁ C₂ β T₀ : ℝ}

omit [NeZero d] in
theorem errConst_pos (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) : 0 < errConst d σ θ C₁ C₂ β := by
  have hσ := hb.hσ
  have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
  have hC₁ := hb.hC₁
  have hC₂ := hb.hC₂
  have hg1 : 0 < Real.Gamma ((d : ℝ) / 2 - 1) :=
    Real.Gamma_pos_of_pos (by linarith [hb.one_lt_half_dim])
  have hg2 : 0 < Real.Gamma (β - 1) :=
    Real.Gamma_pos_of_pos (by linarith [hb.one_lt_half_dim, hb.hβ1])
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  unfold errConst
  have := Real.pi_pos
  positivity

omit [NeZero d] in
theorem rpow_one_sub_le (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) {r : ℝ} (hr : 1 ≤ r) :
    r ^ (1 - (d : ℝ)) ≤ r ^ (2 - 2 * β) :=
  Real.rpow_le_rpow_of_exponent_le hr (by linarith [hb.hβ2])

/-- **The comparison with the homogenized Green function**: for `|x - y| = r ≥ T₀`,
`|G(x) - θ^{-1} ∫_0^∞ p̄(t, x - y) dt| ≤ C r^{2 - 2β}`. -/
theorem abs_timeGreenD_sub_le (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) {x : Vertex d}
    (hx : x ∈ K.supp) (hr : T₀ ≤ ‖edzD x y‖) :
    |timeGreenD ω K y ⟨x, hx⟩ - θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t (edzD x y)| ≤
      errConst d σ θ C₁ C₂ β * ‖edzD x y‖ ^ (2 - 2 * β) := by
  have hraw := hb.abs_timeGreenD_sub_le_raw hx hr
  set r := ‖edzD x y‖ with hrdef
  have hr1 : 1 ≤ r := hb.hT₀.trans hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hσ := hb.hσ
  have hC₁ := hb.hC₁
  have hC₂ := hb.hC₂
  have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
  have hpow := hb.rpow_one_sub_le hr1
  have hP : 0 ≤ r ^ (2 - 2 * β) := Real.rpow_nonneg hr0.le _
  -- the heat kernel at small times
  have hrr : r ^ (d : ℕ) * r ^ (1 - (d : ℝ)) = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
    norm_num
  have h1 : C₂ * Real.exp (-(r / C₂)) * r ≤ d.factorial * C₂ ^ (d + 1) * r ^ (2 - 2 * β) := by
    have hq := pow_mul_exp_neg_div_le hC₂ hr0.le d
    calc C₂ * Real.exp (-(r / C₂)) * r =
          C₂ * (r ^ (d : ℕ) * Real.exp (-(r / C₂))) * r ^ (1 - (d : ℝ)) := by
          have e : C₂ * (r ^ (d : ℕ) * Real.exp (-(r / C₂))) * r ^ (1 - (d : ℝ)) =
              C₂ * Real.exp (-(r / C₂)) * (r ^ (d : ℕ) * r ^ (1 - (d : ℝ))) := by ring
          rw [e, hrr]
      _ ≤ C₂ * (d.factorial * C₂ ^ d) * r ^ (2 - 2 * β) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hq hC₂.le) hpow
            (Real.rpow_nonneg hr0.le _)
          have : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
          positivity
      _ = d.factorial * C₂ ^ (d + 1) * r ^ (2 - 2 * β) := by ring
  -- the Gaussian kernel at small times
  have h4σ : 0 < 4 * σ := by positivity
  have hsplit : (r ^ 2 / (4 * σ)) ^ (1 - (d : ℝ) / 2) =
      (4 * σ) ^ ((d : ℝ) / 2 - 1) * (r ^ (1 - (d : ℝ)) * r) := by
    rw [Real.div_rpow (sq_nonneg _) h4σ.le, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le,
      ← Real.rpow_add_one hr0.ne', div_eq_mul_inv, ← Real.rpow_neg h4σ.le]
    rw [show -(1 - (d : ℝ) / 2) = (d : ℝ) / 2 - 1 by ring,
      show ((2 : ℕ) : ℝ) * (1 - (d : ℝ) / 2) = 1 - (d : ℝ) + 1 by push_cast; ring]
    ring
  have hexp : r * Real.exp (-(r / (4 * σ))) ≤ 4 * σ := by
    have := mul_exp_neg_le_one (r / (4 * σ))
    rw [div_mul_eq_mul_div, div_le_one h4σ] at this
    linarith
  have h2 : θ⁻¹ * ((2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * Real.exp (-(r / (4 * σ))) *
        ((r ^ 2 / (4 * σ)) ^ (1 - (d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2 - 1))) ≤
      θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * (4 * σ) ^ ((d : ℝ) / 2 - 1) *
        Real.Gamma ((d : ℝ) / 2 - 1) * (4 * σ) * r ^ (2 - 2 * β) := by
    rw [hsplit]
    have hg : 0 < Real.Gamma ((d : ℝ) / 2 - 1) :=
      Real.Gamma_pos_of_pos (by linarith [hb.one_lt_half_dim])
    have hA : 0 ≤ θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * (4 * σ) ^ ((d : ℝ) / 2 - 1) *
        Real.Gamma ((d : ℝ) / 2 - 1) := by positivity
    calc θ⁻¹ * ((2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * Real.exp (-(r / (4 * σ))) *
          ((4 * σ) ^ ((d : ℝ) / 2 - 1) * (r ^ (1 - (d : ℝ)) * r) * Real.Gamma ((d : ℝ) / 2 - 1)))
        = θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * (4 * σ) ^ ((d : ℝ) / 2 - 1) *
            Real.Gamma ((d : ℝ) / 2 - 1) * (r * Real.exp (-(r / (4 * σ)))) * r ^ (1 - (d : ℝ)) := by
          ring
      _ ≤ θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * (4 * σ) ^ ((d : ℝ) / 2 - 1) *
            Real.Gamma ((d : ℝ) / 2 - 1) * (4 * σ) * r ^ (2 - 2 * β) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hA) hpow (Real.rpow_nonneg hr0.le _)
            (by positivity)
  -- large times
  have h3 : C₁ * ((r ^ 2 / C₁) ^ (1 - β) * Real.Gamma (β - 1)) =
      C₁ ^ β * Real.Gamma (β - 1) * r ^ (2 - 2 * β) := by
    rw [Real.div_rpow (sq_nonneg _) hC₁.le, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    have hC1 : C₁ / C₁ ^ (1 - β) = C₁ ^ β := by
      rw [div_eq_iff (Real.rpow_pos_of_pos hC₁ _).ne', ← Real.rpow_add hC₁,
        show β + (1 - β) = 1 by ring, Real.rpow_one]
    rw [show ((2 : ℕ) : ℝ) * (1 - β) = 2 - 2 * β by push_cast; ring]
    calc C₁ * (r ^ (2 - 2 * β) / C₁ ^ (1 - β) * Real.Gamma (β - 1))
        = C₁ / C₁ ^ (1 - β) * Real.Gamma (β - 1) * r ^ (2 - 2 * β) := by ring
      _ = C₁ ^ β * Real.Gamma (β - 1) * r ^ (2 - 2 * β) := by rw [hC1]
  have hsum := hraw.trans (add_le_add (add_le_add h1 h2) (le_of_eq h3))
  refine hsum.trans (le_of_eq ?_)
  unfold errConst
  ring

/-! ### The Green column -/

omit [NeZero d] in
theorem inv_mul_integral_gaussianHeatD_eq_rpow (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀)
    {z : EuclideanSpace ℝ (Fin d)} (hz : z ≠ 0) :
    θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t z =
      θ⁻¹ * (Real.Gamma ((d : ℝ) / 2 - 1) / (2 * Real.pi ^ ((d : ℝ) / 2) * σ)) *
        ‖z‖ ^ (2 - (d : ℝ)) := by
  rw [integral_gaussianHeatD hb.hd hb.hσ hz]
  ring

/-- `G` tends to zero at infinity. -/
theorem timeGreenD_small (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : K, R ≤ ‖latticeEuclideanEmbedding x.val‖ →
      |timeGreenD ω K y x| ≤ ε := by
  set cG := θ⁻¹ * (Real.Gamma ((d : ℝ) / 2 - 1) / (2 * Real.pi ^ ((d : ℝ) / 2) * σ)) with hcG
  have hσ := hb.hσ
  have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
  have hg : 0 < Real.Gamma ((d : ℝ) / 2 - 1) :=
    Real.Gamma_pos_of_pos (by linarith [hb.one_lt_half_dim])
  have hcG0 : 0 < cG := by have := Real.pi_pos; positivity
  have hE := hb.errConst_pos
  set A := cG + errConst d σ θ C₁ C₂ β with hA
  have hA0 : 0 < A := by positivity
  refine ⟨‖latticeEuclideanEmbedding y‖ + max T₀ (A / ε) + 1, by positivity, fun x hx => ?_⟩
  set r := ‖edzD x.val y‖ with hrdef
  have hrge : max T₀ (A / ε) + 1 ≤ r := by
    have := norm_sub_norm_le (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y)
    rw [hrdef]
    linarith
  have hT₀r : T₀ ≤ r := by linarith [le_max_left T₀ (A / ε)]
  have hAr : A / ε ≤ r := by linarith [le_max_right T₀ (A / ε)]
  have hr1 : 1 ≤ r := hb.hT₀.trans hT₀r
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hz : edzD x.val y ≠ 0 := norm_pos_iff.1 hr0
  have hmain : |timeGreenD ω K y x - θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t (edzD x.val y)| ≤
      errConst d σ θ C₁ C₂ β * ‖edzD x.val y‖ ^ (2 - 2 * β) := hb.abs_timeGreenD_sub_le x.2 hT₀r
  rw [hb.inv_mul_integral_gaussianHeatD_eq_rpow hz, ← hcG, ← hrdef] at hmain
  have hp1 : r ^ (2 - (d : ℝ)) ≤ r⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hb.hd
      linarith)
  have hp2 : r ^ (2 - 2 * β) ≤ r⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hb.hd
      linarith [hb.hβ1])
  have hG : |timeGreenD ω K y x| ≤ A * r⁻¹ := by
    have h0 : |cG * r ^ (2 - (d : ℝ))| ≤ cG * r⁻¹ := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hp1 hcG0.le
    have h1 := abs_sub_abs_le_abs_sub (timeGreenD ω K y x) (cG * r ^ (2 - (d : ℝ)))
    have h2 : errConst d σ θ C₁ C₂ β * r ^ (2 - 2 * β) ≤ errConst d σ θ C₁ C₂ β * r⁻¹ :=
      mul_le_mul_of_nonneg_left hp2 hE.le
    rw [hA]
    linarith
  calc |timeGreenD ω K y x| ≤ A * r⁻¹ := hG
    _ ≤ ε := by
        rw [← div_eq_mul_inv, div_le_iff₀ hr0]
        rw [div_le_iff₀ hε] at hAr
        linarith

/-- **`G` is a Green column** with pole `y`. -/
theorem isGreenColumn_timeGreenD (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) (hd2 : 2 ≤ d) :
    IsGreenColumn d hd2 K ⟨y, hb.hy⟩ (timeGreenD ω K y) := by
  refine ⟨fun x => (hb.laplacian_timeGreenD x).trans (by split_ifs <;> rfl),
    fun h => absurd h (by have := hb.hd; omega), fun _ ε hε => hb.timeGreenD_small hε⟩

end HeatBoundsD

/-! ### Theorem 2 for `d ≥ 3` -/

/-- **Dario–Gu, Theorem 1, in dimension `d`**, for the heat kernel of the variable speed random walk
on the open graph of `ℤ^d`, with the restriction `t ≥ 1`. -/
def DarioGuHeatKernelD (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∀ δ : ℝ, 0 < δ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex d,
      ∃ T : Configuration d → ℝ, Measurable T ∧ (∀ ω, 0 ≤ T ω) ∧
        (∀ R : ℝ, 0 ≤ R →
          latticeBondLaw d p {ω | R ≤ T ω} ≤ ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          y ∈ (uniqueInfiniteComponent h).supp → ∀ x ∈ (uniqueInfiniteComponent h).supp,
          ∀ t : ℝ, 1 ≤ t → T ω ≤ t → ‖edzD x y‖ ≤ t →
            |openHeatD ω t x y - (theta d p)⁻¹ * gaussianHeatD d σ t (edzD x y)| ≤
              C * t ^ (-((d : ℝ) / 2) - (1 / 2 - δ)) * Real.exp (-(‖edzD x y‖ ^ 2 / (C * t)))

/-- The small-time bound `p(t, x, y) ≤ C e^{-|x - y|/C}` for `0 < t ≤ |x - y|` on infinite
components of `ℤ^d` (from the Carne–Varopoulos bound, Dario–Gu, Proposition 2.15). -/
def HeatSmallTimeD (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (K : OpenComponent ω), K.supp.Infinite →
    ∀ x ∈ K.supp, ∀ y ∈ K.supp, ∀ t : ℝ, 0 < t → t ≤ ‖edzD x y‖ →
      openHeatD ω t x y ≤ C * Real.exp (-(‖edzD x y‖ / C))

/-- A tail `C e^{-R^s/C}` of `T` gives a tail of `max T 1`. -/
theorem tail_max_one {p : unitInterval} {T : Configuration d → ℝ} {C s : ℝ} (hC : 0 < C)
    (hs : 0 < s) (hT : ∀ R : ℝ, 0 ≤ R →
      latticeBondLaw d p {ω | R ≤ T ω} ≤ ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C)))
    {C' : ℝ} (hC' : max C 2 ≤ C') :
    ∀ R : ℝ, 0 ≤ R → latticeBondLaw d p {ω | R ≤ max (T ω) 1} ≤
      ENNReal.ofReal (C' * Real.exp (-Real.rpow R s / C')) := by
  intro R hR
  have hC'2 : 2 ≤ C' := (le_max_right _ _).trans hC'
  have hC'0 : 0 < C' := by linarith
  rcases le_or_gt R 1 with hR1 | hR1
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hRs : Real.rpow R s ≤ 1 := Real.rpow_le_one hR hR1 hs.le
    have he : 1 / 2 ≤ Real.exp (-Real.rpow R s / C') := by
      have h0 : Real.rpow R s / C' ≤ 1 / 2 := by
        rw [div_le_iff₀ hC'0]; linarith
      have h1 := Real.add_one_le_exp (-Real.rpow R s / C')
      have e : -Real.rpow R s / C' = -(Real.rpow R s / C') := neg_div _ _
      rw [e] at h1 ⊢
      linarith
    nlinarith
  · have hsub : {ω | R ≤ max (T ω) 1} ⊆ {ω | R ≤ T ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rcases le_total (T ω) 1 with h | h
      · rw [max_eq_right h] at hω; linarith
      · rwa [max_eq_left h] at hω
    refine (measure_mono hsub).trans ((hT R hR).trans (ENNReal.ofReal_le_ofReal ?_))
    have hRs : 0 ≤ Real.rpow R s := Real.rpow_nonneg hR s
    have hCC : C ≤ C' := (le_max_left _ _).trans hC'
    apply mul_le_mul hCC _ (Real.exp_pos _).le hC'0.le
    apply Real.exp_le_exp.2
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hRs hC hCC

/-- **Dario–Gu, Theorem 2, for `d ≥ 3`**, from Theorem 1 in dimension `d` and the small-time
bound. -/
theorem supercriticalBondGreenQuantitativeThree_of_heatKernel
    (hP : ∀ (d : ℕ) [NeZero d], 3 ≤ d → DarioGuHeatKernelD d)
    (hS : ∀ (d : ℕ) [NeZero d], 3 ≤ d → HeatSmallTimeD d) :
    SupercriticalBondGreenQuantitativeThree := by
  intro d _ hd2 hd3 p hpc hp1
  obtain ⟨σ, hσ, hT⟩ := hP d hd3 p hpc hp1
  obtain ⟨C₂, hC₂, hcv⟩ := hS d hd3
  have hθ : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  set θ := theta d p with hθdef
  have hκ : 0 < σ * θ / 2 := by positivity
  refine ⟨σ * θ / 2, hκ, fun δ hδ => ?_⟩
  set δ₁ := min δ (1 / 2) with hδ₁def
  have hδ₁ : 0 < δ₁ := lt_min hδ (by norm_num)
  have hδ₁2 : δ₁ ≤ 1 / 2 := min_le_right _ _
  have hδ₁δ : δ₁ ≤ δ := min_le_left _ _
  obtain ⟨C₁, s, hC₁, hs, hTy⟩ := hT (δ₁ / 2) (by positivity)
  set β := (d : ℝ) / 2 + (1 / 2 - δ₁ / 2) with hβdef
  have hexp : -((d : ℝ) / 2) - (1 / 2 - δ₁ / 2) = -β := by rw [hβdef]; ring
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  set E := HeatBoundsD.errConst d σ θ C₁ C₂ β with hEdef
  set Cf := max E (max C₁ 2) with hCf
  have hE0 : 0 < E := by
    have hb0 : (d : ℝ) / 2 < β := by rw [hβdef]; linarith
    have hg1 : 0 < Real.Gamma ((d : ℝ) / 2 - 1) := Real.Gamma_pos_of_pos (by linarith)
    have hg2 : 0 < Real.Gamma (β - 1) := Real.Gamma_pos_of_pos (by linarith)
    have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
    rw [hEdef]
    unfold HeatBoundsD.errConst
    have := Real.pi_pos
    have : 0 < θ⁻¹ := inv_pos.2 hθ
    positivity
  have hCf0 : 0 < Cf := lt_of_lt_of_le hE0 (le_max_left _ _)
  refine ⟨Cf, s, hCf0, hs, fun y => ?_⟩
  obtain ⟨T, hTm, hT0, hTtail, hTae⟩ := hTy y
  refine ⟨fun ω => max (T ω) 1, hTm.max measurable_const,
    fun ω => zero_le_one.trans (le_max_right _ _),
    tail_max_one hC₁ hs hTtail (le_max_right _ _), ?_⟩
  filter_upwards [hTae, greenColumnExistence_of_three_le hd3 hd2 p hpc hp1 y] with ω hω hU
  intro h hy g hg x z hz hM
  have hb : HeatBoundsD (uniqueInfiniteComponent h) y σ θ C₁ C₂ β (max (T ω) 1) :=
    { hd := hd3, hσ := hσ, hθ := hθ, hC₁ := hC₁, hC₂ := hC₂,
      hβ1 := by rw [hβdef]; linarith, hβ2 := by rw [hβdef]; linarith,
      hT₀ := le_max_right _ _, hy := hy,
      thm1 := fun x hx t ht hxt => by
        have := hω h hy x hx t ((le_max_right _ _).trans ht) ((le_max_left _ _).trans ht) hxt
        rwa [hexp] at this
      cv := fun x hx t ht htx =>
        hcv ω (uniqueInfiniteComponent h) (uniqueInfiniteComponent_infinite h) x hx y hy t ht htx }
  have hgG : g = timeGreenD ω (uniqueInfiniteComponent h) y :=
    (hU h hy).unique hg (hb.isGreenColumn_timeGreenD hd2)
  subst hgG
  have hzeq : z.val = edzD x.val y := hz
  have hr : max (T ω) 1 ≤ ‖edzD x.val y‖ := by rw [← hzeq]; exact hM
  have hmain : |timeGreenD ω (uniqueInfiniteComponent h) y x -
      θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t (edzD x.val y)| ≤
      HeatBoundsD.errConst d σ θ C₁ C₂ β * ‖edzD x.val y‖ ^ (2 - 2 * β) :=
    hb.abs_timeGreenD_sub_le x.2 hr
  have hcg : continuumGreen d hd2 ⟨σ * θ / 2, hκ⟩ z =
      θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t (edzD x.val y) := by
    rw [← inv_mul_integral_gaussianHeatD_eq hd3 hd2 hσ hθ z, hzeq]
  rw [hcg]
  set r := ‖z.val‖ with hrdef
  have hrz : ‖edzD x.val y‖ = r := by rw [hrdef, hzeq]
  rw [hrz] at hmain hr
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  -- the exponents
  have hpow : r ^ (2 - 2 * β) ≤ 1 / (Real.rpow r (1 - δ) * r ^ (d - 2)) := by
    have hnat : (r ^ (d - 2) : ℝ) = r ^ ((d : ℝ) - 2) := by
      rw [← Real.rpow_natCast]
      congr 1
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hnat, Real.rpow_eq_pow, ← Real.rpow_add hr0, one_div, ← Real.rpow_neg hr0.le]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (by rw [hβdef]; linarith)
  have hden : 0 < Real.rpow r (1 - δ) * r ^ (d - 2) := by
    have : 0 < Real.rpow r (1 - δ) := Real.rpow_pos_of_pos hr0 _
    positivity
  calc |timeGreenD ω (uniqueInfiniteComponent h) y x -
        θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t (edzD x.val y)|
      ≤ E * r ^ (2 - 2 * β) := hmain
    _ ≤ Cf * (1 / (Real.rpow r (1 - δ) * r ^ (d - 2))) :=
        mul_le_mul (le_max_left _ _) hpow (Real.rpow_nonneg hr0.le _) hCf0.le
    _ = Cf / (Real.rpow r (1 - δ) * r ^ (d - 2)) := by ring

end Rigidity.Green

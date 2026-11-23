import Rigidity.Proofs.Green.PlanarHeatKernelInputs
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Time integrals of the planar Gaussian kernel

Three computations used in the proof of Dario–Gu, Theorem 2, in dimension two (§5).

* Frullani's integral `∫_0^∞ (e^{-au} - e^{-bu}) / u du = log b - log a` for `a, b > 0`, by
  Fubini's theorem applied to `∫_a^b e^{-cu} dc = (e^{-au} - e^{-bu}) / u`.
* `∫_0^∞ (p̄(t, z) - p̄(t, e)) dt = -log |z| / (π σ)` for `z ≠ 0` and `|e| = 1`, with
  `p̄(t, z) = (2πσt)^{-1} exp(-|z|²/(2σt))`, by the substitution `u = 1/t` and Frullani's integral.
  Dario–Gu normalize the time integral of `p̄` by its mean over the unit ball and record the
  resulting constant `K_1` (Dario–Gu, (5.6), citing Dautray–Lions, Chapter 1.8); the normalization
  by `p̄(t, e)` used here gives the homogenized Green function `ḡ` itself, without a constant.
* `∫_0^∞ t^{-β} e^{-a/t} dt = a^{1-β} Γ(β - 1)` for `β > 1`, `a > 0` (substitution `u = 1/t`).
-/

open MeasureTheory Set Real

namespace Rigidity.Green

/-- `∫_0^∞ e^{-cu} du = 1/c` for `c > 0`. -/
theorem integral_exp_neg_mul_Ioi_zero {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-c * u) = 1 / c := by
  rw [integral_exp_mul_Ioi (a := -c) (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- `∫_a^b e^{-cu} dc = (e^{-au} - e^{-bu}) / u` for `u ≠ 0`. -/
theorem integral_exp_neg_mul_left {u : ℝ} (hu : u ≠ 0) (a b : ℝ) :
    ∫ c in a..b, Real.exp (-c * u) = (Real.exp (-a * u) - Real.exp (-b * u)) / u := by
  have hd : ∀ c : ℝ, HasDerivAt (fun c : ℝ => -Real.exp (-c * u) / u) (Real.exp (-c * u)) c := by
    intro c
    have h0 : HasDerivAt (fun x : ℝ => -u * x) (-u * 1) c := (hasDerivAt_id' c).const_mul (-u)
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-u * x)) (Real.exp (-u * c) * (-u * 1)) c :=
      HasDerivAt.exp h0
    have h2 : HasDerivAt (fun x : ℝ => -Real.exp (-u * x) / u)
        (-(Real.exp (-u * c) * (-u * 1)) / u) c := HasDerivAt.div_const (HasDerivAt.neg h1) u
    have heq : (fun x : ℝ => -Real.exp (-u * x) / u) = fun c : ℝ => -Real.exp (-c * u) / u := by
      funext x
      ring_nf
    rw [heq] at h2
    refine h2.congr_deriv ?_
    rw [show -u * c = -c * u by ring]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun c _ => hd c)
    (Continuous.intervalIntegrable (by fun_prop) a b)]
  ring

/-- Frullani's integral for `a ≤ b`. -/
theorem frullani_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u => (Real.exp (-a * u) - Real.exp (-b * u)) / u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (Real.exp (-a * u) - Real.exp (-b * u)) / u =
        Real.log b - Real.log a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set μ := volume.restrict (Ioi (0 : ℝ))
  set ν := volume.restrict (Ioc a b)
  have hprod : μ.prod ν = (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioc a b) :=
    Measure.prod_restrict _ _
  have hdom : Integrable (fun z : ℝ × ℝ => Real.exp (-a * z.1) * 1) (μ.prod ν) :=
    Integrable.mul_prod (exp_neg_integrableOn_Ioi 0 ha) (integrable_const (1 : ℝ))
  have hcont : Continuous (Function.uncurry fun u c : ℝ => Real.exp (-c * u)) := by
    rw [Function.uncurry_def]
    fun_prop
  have hint : Integrable (Function.uncurry fun u c : ℝ => Real.exp (-c * u)) (μ.prod ν) := by
    refine hdom.mono' hcont.aestronglyMeasurable ?_
    rw [hprod]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    change ‖Real.exp (-z.2 * z.1)‖ ≤ Real.exp (-a * z.1) * 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one]
    apply Real.exp_le_exp.mpr
    have h1 : (0 : ℝ) < z.1 := hz1
    have h2 : a ≤ z.2 := (Set.mem_Ioc.1 hz2).1.le
    nlinarith
  have hleft : ∀ u ∈ Ioi (0 : ℝ), ∫ c in Ioc a b, Real.exp (-c * u) =
      (Real.exp (-a * u) - Real.exp (-b * u)) / u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [← intervalIntegral.integral_of_le hab, integral_exp_neg_mul_left hu0.ne']
  have hright : ∀ c ∈ Ioc a b, ∫ u in Ioi (0 : ℝ), Real.exp (-c * u) = 1 / c :=
    fun c hc => integral_exp_neg_mul_Ioi_zero (lt_of_lt_of_le ha (Set.mem_Ioc.1 hc).1.le)
  constructor
  · refine (Integrable.integral_prod_left hint).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hleft u hu
  · have hswap := integral_integral_swap hint
    calc ∫ u in Ioi (0 : ℝ), (Real.exp (-a * u) - Real.exp (-b * u)) / u
        = ∫ u in Ioi (0 : ℝ), ∫ c in Ioc a b, Real.exp (-c * u) :=
          (setIntegral_congr_fun measurableSet_Ioi hleft).symm
      _ = ∫ c in Ioc a b, ∫ u in Ioi (0 : ℝ), Real.exp (-c * u) := hswap
      _ = ∫ c in Ioc a b, 1 / c := setIntegral_congr_fun measurableSet_Ioc hright
      _ = Real.log b - Real.log a := by
          rw [← intervalIntegral.integral_of_le hab, integral_one_div_of_pos ha hb,
            Real.log_div hb.ne' ha.ne']

/-- **Frullani's integral** `∫_0^∞ (e^{-au} - e^{-bu}) / u du = log b - log a` for `a, b > 0`. -/
theorem frullani {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun u => (Real.exp (-a * u) - Real.exp (-b * u)) / u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (Real.exp (-a * u) - Real.exp (-b * u)) / u =
        Real.log b - Real.log a := by
  rcases le_total a b with hab | hba
  · exact frullani_of_le ha hab
  · obtain ⟨hi, he⟩ := frullani_of_le hb hba
    have heq : (fun u => (Real.exp (-a * u) - Real.exp (-b * u)) / u) =
        fun u => -((Real.exp (-b * u) - Real.exp (-a * u)) / u) := by
      funext u
      ring
    rw [heq]
    refine ⟨hi.neg, ?_⟩
    rw [integral_neg, he]
    ring

/-- The substitution `u = 1/t` on `(0, ∞)`: `∫ t^{-2} g(1/t) dt = ∫ g`, and integrability. -/
theorem integral_comp_inv_Ioi (g : ℝ → ℝ) :
    (IntegrableOn (fun t => t ^ (-2 : ℝ) * g t⁻¹) (Ioi 0) ↔ IntegrableOn g (Ioi 0)) ∧
      ∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * g t⁻¹ = ∫ u in Ioi (0 : ℝ), g u := by
  have hp : (-1 : ℝ) ≠ 0 := by norm_num
  have heq : EqOn (fun t : ℝ => (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • g (t ^ (-1 : ℝ)))
      (fun t => t ^ (-2 : ℝ) * g t⁻¹) (Ioi 0) := by
    intro t _
    simp only [smul_eq_mul, Real.rpow_neg_one]
    norm_num
  constructor
  · rw [← integrableOn_Ioi_comp_rpow_iff g hp]
    exact ⟨fun h => h.congr_fun heq.symm measurableSet_Ioi,
      fun h => h.congr_fun heq measurableSet_Ioi⟩
  · rw [← integral_comp_rpow_Ioi g hp]
    exact (setIntegral_congr_fun measurableSet_Ioi heq).symm

/-- **The time integral of the planar Gaussian kernel**: for `z ≠ 0` and `|e| = 1`,
`∫_0^∞ (p̄(t, z) - p̄(t, e)) dt = -log |z| / (π σ)`. -/
theorem integral_gaussianHeat_sub {σ : ℝ} (hσ : 0 < σ) {z e : EuclideanSpace ℝ (Fin 2)}
    (hz : z ≠ 0) (he : ‖e‖ = 1) :
    IntegrableOn (fun t => gaussianHeat σ t z - gaussianHeat σ t e) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), (gaussianHeat σ t z - gaussianHeat σ t e) =
        -Real.log ‖z‖ / (Real.pi * σ) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set A := ‖z‖ ^ 2 / (2 * σ) with hA
  set B := 1 / (2 * σ) with hB
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by positivity
  obtain ⟨hint, hval⟩ := frullani hA0 hB0
  set g : ℝ → ℝ := fun u => (2 * Real.pi * σ)⁻¹ * ((Real.exp (-A * u) - Real.exp (-B * u)) / u)
    with hgdef
  have hpt : EqOn (fun t => t ^ (-2 : ℝ) * g t⁻¹)
      (fun t => gaussianHeat σ t z - gaussianHeat σ t e) (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [g, gaussianHeat, he, one_pow]
    rw [Real.rpow_neg ht0.le, Real.rpow_two]
    have h1 : -A * t⁻¹ = -(‖z‖ ^ 2 / (2 * σ * t)) := by rw [hA]; field_simp
    have h2 : -B * t⁻¹ = -(1 / (2 * σ * t)) := by rw [hB]; field_simp
    rw [h1, h2]
    have := Real.pi_pos
    field_simp
  obtain ⟨hiff, hsub⟩ := integral_comp_inv_Ioi g
  have hg : IntegrableOn g (Ioi 0) := hint.const_mul _
  constructor
  · exact (hiff.2 hg).congr_fun hpt measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi hpt, hsub]
    show ∫ u in Ioi (0 : ℝ), (2 * Real.pi * σ)⁻¹ * ((Real.exp (-A * u) - Real.exp (-B * u)) / u) = _
    rw [integral_const_mul, hval, hA, hB]
    have := Real.pi_pos
    have h2σ : (2 : ℝ) * σ ≠ 0 := by positivity
    have hz2 : ‖z‖ ^ 2 ≠ 0 := by positivity
    rw [Real.log_div one_ne_zero h2σ, Real.log_div hz2 h2σ, Real.log_one, Real.log_pow]
    field_simp
    ring

/-- `∫_0^∞ t^{-β} e^{-a/t} dt = a^{1-β} Γ(β - 1)` for `β > 1` and `a > 0`, with integrability. -/
theorem integral_rpow_neg_mul_exp_neg_div {β a : ℝ} (hβ : 1 < β) (ha : 0 < a) :
    IntegrableOn (fun t => t ^ (-β) * Real.exp (-(a / t))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ (-β) * Real.exp (-(a / t)) = a ^ (1 - β) * Real.Gamma (β - 1) := by
  set g : ℝ → ℝ := fun u => u ^ (β - 2) * Real.exp (-a * u ^ (1 : ℝ))
  have hpt : EqOn (fun t => t ^ (-2 : ℝ) * g t⁻¹) (fun t => t ^ (-β) * Real.exp (-(a / t)))
      (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [g, Real.rpow_one]
    rw [Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, ← mul_assoc, ← Real.rpow_add ht0]
    congr 1
    · ring_nf
    · congr 1
      ring
  obtain ⟨hiff, hsub⟩ := integral_comp_inv_Ioi g
  have hg : IntegrableOn g (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl ha
  constructor
  · exact (hiff.2 hg).congr_fun hpt measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi hpt, hsub]
    show ∫ u in Ioi (0 : ℝ), u ^ (β - 2) * Real.exp (-a * u ^ (1 : ℝ)) = _
    rw [integral_rpow_mul_exp_neg_mul_rpow one_pos (show (-1 : ℝ) < β - 2 by linarith) ha]
    rw [show (β - 2 + 1) / 1 = β - 1 by ring, show -(β - 2 + 1) / 1 = 1 - β by ring]
    ring

end Rigidity.Green

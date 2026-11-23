import Rigidity.Proofs.Green.DarioGuGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# The mass and the oscillation of the Gaussian kernel on the planar lattice

Estimates on `p̄(t, x - y) = (2πσt)^{-1} exp(-|x - y|²/(2σt))` used in the proof of Proposition A.7
of Dario–Gu (the concentration of the Gaussian mass of the infinite cluster).

* `abs_gaussianHeat_sub_le_of_near`: if `|u - z|, |v - z| ≤ L ≤ 2√t`, then
  `|p̄(t, u) - p̄(t, v)| ≤ K_σ L t^{-3/2} exp(-|z|²/(8σt))`.
* `tsum_latticeGaussian_eq`: by the Poisson summation formula for the Gaussian,
  `Σ_{x ∈ ℤ²} p̄(t, x - y) = (Σ_{n ∈ ℤ} exp(-2π²σt n²))²`; hence
  `|Σ_{x ∈ ℤ²} p̄(t, x - y) - 1| ≤ C t^{-1/2}` for `t ≥ 1` (`abs_tsum_latticeGaussian_sub_one_le`).
* `sum_latticeGaussian_far_le`: the mass of `p̄(t, · - y)` at distance at least `t` from `y` is at
  most `C t^{-1/2}`.
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

/-! ### Oscillation -/

/-- The constant `K_σ = e^{2/σ} (2√σ + 2) / (π σ²)` of the oscillation bound. -/
noncomputable def gaussOscConst (σ : ℝ) : ℝ :=
  Real.exp (2 / σ) * (2 * Real.sqrt σ + 2) / (Real.pi * σ ^ 2)

theorem gaussOscConst_pos {σ : ℝ} (hσ : 0 < σ) : 0 < gaussOscConst σ := by
  unfold gaussOscConst
  positivity

/-- If `|u - z| ≤ L` and `|v - z| ≤ L` with `L ≤ 2√t`, then
`|p̄(t, u) - p̄(t, v)| ≤ K_σ L t^{-3/2} exp(-|z|²/(8σt))`. -/
theorem abs_gaussianHeat_sub_le_of_near {σ : ℝ} (hσ : 0 < σ) {t L : ℝ} (ht : 0 < t)
    (hL : 0 ≤ L) (hLt : L ≤ 2 * Real.sqrt t) {z u v : EuclideanSpace ℝ (Fin 2)}
    (hu : ‖u - z‖ ≤ L) (hv : ‖v - z‖ ≤ L) :
    |gaussianHeat σ t u - gaussianHeat σ t v| ≤
      gaussOscConst σ * L / (t * Real.sqrt t) * Real.exp (-(1 / (8 * σ) * ‖z‖ ^ 2 / t)) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  rw [Real.sqrt_sq hs.le] at hLt ⊢
  set nz := ‖z‖ with hnz
  have hz0 : 0 ≤ nz := norm_nonneg _
  have hu0 := norm_nonneg u
  have hv0 := norm_nonneg v
  set a := ‖u‖ ^ 2 / (2 * σ * s ^ 2) with ha
  set b := ‖v‖ ^ 2 / (2 * σ * s ^ 2) with hb
  have huv : ‖u - v‖ ≤ 2 * L := by
    have h := norm_sub_le_norm_sub_add_norm_sub u z v
    rw [norm_sub_rev z v] at h
    linarith
  have huz : ‖u‖ ≤ nz + L := by
    have h := norm_sub_norm_le u z
    linarith
  have hvz : ‖v‖ ≤ nz + L := by
    have h := norm_sub_norm_le v z
    linarith
  have hzu : nz ≤ ‖u‖ + L := by
    have h := norm_sub_norm_le z u
    rw [norm_sub_rev] at h
    linarith
  have hzv : nz ≤ ‖v‖ + L := by
    have h := norm_sub_norm_le z v
    rw [norm_sub_rev] at h
    linarith
  have hab : |a - b| ≤ 2 * L * (nz + L) / (σ * s ^ 2) := by
    have e : a - b = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) / (2 * σ * s ^ 2) := by
      simp only [ha, hb]
      ring
    rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * σ * s ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u‖ + ‖v‖),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |‖u‖ - ‖v‖| ≤ 2 * L := (abs_norm_sub_norm_le u v).trans huv
    have h2 : ‖u‖ + ‖v‖ ≤ 2 * (nz + L) := by linarith
    have h3 : |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) ≤ (2 * L) * (2 * (nz + L)) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : 0 < σ * s ^ 2 := by positivity
    nlinarith
  have hmin : (nz ^ 2 / 2 - L ^ 2) / (2 * σ * s ^ 2) ≤ min a b := by
    have hu2 : nz ^ 2 / 2 - L ^ 2 ≤ ‖u‖ ^ 2 := by
      nlinarith [mul_self_le_mul_self hz0 hzu, sq_nonneg (‖u‖ - L)]
    have hv2 : nz ^ 2 / 2 - L ^ 2 ≤ ‖v‖ ^ 2 := by
      nlinarith [mul_self_le_mul_self hz0 hzv, sq_nonneg (‖v‖ - L)]
    exact le_min (div_le_div_of_nonneg_right hu2 (by positivity))
      (div_le_div_of_nonneg_right hv2 (by positivity))
  have hL2 : L ^ 2 ≤ 4 * s ^ 2 := by nlinarith
  have hexp : Real.exp (-min a b) ≤
      Real.exp (2 / σ) * Real.exp (-(nz ^ 2 / (4 * σ * s ^ 2))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e1 : (nz ^ 2 / 2 - L ^ 2) / (2 * σ * s ^ 2) =
        nz ^ 2 / (4 * σ * s ^ 2) - L ^ 2 / (2 * σ * s ^ 2) := by
      field_simp
      ring
    have e2 : L ^ 2 / (2 * σ * s ^ 2) ≤ 2 / σ := by
      rw [div_le_div_iff₀ (by positivity) hσ]
      nlinarith
    linarith
  have hpoly : (nz + L) * Real.exp (-(nz ^ 2 / (4 * σ * s ^ 2))) ≤
      (2 * Real.sqrt σ + 2) * s * Real.exp (-(1 / (8 * σ) * nz ^ 2 / s ^ 2)) := by
    have h1 := mul_exp_neg_sq_le (c := 4 * σ * s ^ 2) (by positivity) hz0
    have h8 : nz ^ 2 / (2 * (4 * σ * s ^ 2)) = 1 / (8 * σ) * nz ^ 2 / s ^ 2 := by
      field_simp
      ring
    have hsq : Real.sqrt (4 * σ * s ^ 2) = 2 * Real.sqrt σ * s := by
      rw [show 4 * σ * s ^ 2 = (2 * s) ^ 2 * σ by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
      ring
    rw [h8, hsq] at h1
    have h2 : Real.exp (-(nz ^ 2 / (4 * σ * s ^ 2))) ≤
        Real.exp (-(1 / (8 * σ) * nz ^ 2 / s ^ 2)) := by
      apply Real.exp_le_exp.2
      rw [neg_le_neg_iff, show 1 / (8 * σ) * nz ^ 2 / s ^ 2 = nz ^ 2 / (8 * σ * s ^ 2) by
        field_simp]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    have hE := (Real.exp_pos (-(nz ^ 2 / (4 * σ * s ^ 2)))).le
    have hE' := (Real.exp_pos (-(1 / (8 * σ) * nz ^ 2 / s ^ 2))).le
    have hss := Real.sqrt_nonneg σ
    calc (nz + L) * Real.exp (-(nz ^ 2 / (4 * σ * s ^ 2)))
        = nz * Real.exp (-(nz ^ 2 / (4 * σ * s ^ 2))) +
            L * Real.exp (-(nz ^ 2 / (4 * σ * s ^ 2))) := by ring
      _ ≤ 2 * Real.sqrt σ * s * Real.exp (-(1 / (8 * σ) * nz ^ 2 / s ^ 2)) +
            2 * s * Real.exp (-(1 / (8 * σ) * nz ^ 2 / s ^ 2)) := by
          exact add_le_add h1 (mul_le_mul hLt h2 hE (by positivity))
      _ = _ := by ring
  have hdiff : gaussianHeat σ (s ^ 2) u - gaussianHeat σ (s ^ 2) v =
      (2 * Real.pi * σ * s ^ 2)⁻¹ * (Real.exp (-a) - Real.exp (-b)) := by
    simp only [gaussianHeat, ha, hb]
    ring
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi * σ * s ^ 2)⁻¹)]
  have hmain := abs_exp_neg_sub_exp_neg_le a b
  calc (2 * Real.pi * σ * s ^ 2)⁻¹ * |Real.exp (-a) - Real.exp (-b)|
      ≤ (2 * Real.pi * σ * s ^ 2)⁻¹ * (2 * L * (nz + L) / (σ * s ^ 2) *
          (Real.exp (2 / σ) * Real.exp (-(nz ^ 2 / (4 * σ * s ^ 2))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hmain.trans (mul_le_mul hab hexp (Real.exp_pos _).le (by positivity))
    _ = (2 * Real.pi * σ * s ^ 2)⁻¹ * (2 * L / (σ * s ^ 2)) * Real.exp (2 / σ) *
          ((nz + L) * Real.exp (-(nz ^ 2 / (4 * σ * s ^ 2)))) := by ring
    _ ≤ (2 * Real.pi * σ * s ^ 2)⁻¹ * (2 * L / (σ * s ^ 2)) * Real.exp (2 / σ) *
          ((2 * Real.sqrt σ + 2) * s * Real.exp (-(1 / (8 * σ) * nz ^ 2 / s ^ 2))) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = gaussOscConst σ * L / (s ^ 2 * s) * Real.exp (-(1 / (8 * σ) * nz ^ 2 / s ^ 2)) := by
        rw [gaussOscConst]
        field_simp

/-! ### Mass -/

/-- The bound `Σ_{x ∈ S} p̄(t, x - y) ≤ L₀ / (2πσ)` for `t ≥ 1`. -/
noncomputable def gaussMassBound (σ : ℝ) : ℝ :=
  (2 * Real.pi * σ)⁻¹ * (4 * Real.exp (1 / (2 * σ) / 2) * (1 + 1 / (1 / (2 * σ))) ^ 2)

theorem sum_latticeGaussian_le {σ t : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) (y : Vertex 2)
    (S : Finset (Vertex 2)) : ∑ x ∈ S, latticeGaussian σ t x y ≤ gaussMassBound σ := by
  have ht0 : 0 < t := by linarith
  have hsum := sum_exp_neg_sq_div_le (c := 1 / (2 * σ)) (by positivity) ht y S
  calc ∑ x ∈ S, latticeGaussian σ t x y
      = (2 * Real.pi * σ * t)⁻¹ *
          ∑ x ∈ S, Real.exp (-(1 / (2 * σ) * latticeDist x y ^ 2 / t)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have e : latticeDist x y ^ 2 / (2 * σ * t) = 1 / (2 * σ) * latticeDist x y ^ 2 / t := by
          field_simp
        rw [latticeGaussian_eq, e]
    _ ≤ (2 * Real.pi * σ * t)⁻¹ *
          (4 * Real.exp (1 / (2 * σ) / 2) * (1 + 1 / (1 / (2 * σ))) ^ 2 * t) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = gaussMassBound σ := by
        rw [gaussMassBound]
        field_simp

theorem summable_latticeGaussian {σ t : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) (y : Vertex 2) :
    Summable fun x => latticeGaussian σ t x y :=
  summable_of_sum_le (fun x => (latticeGaussian_pos hσ (by linarith) x y).le)
    (sum_latticeGaussian_le hσ ht y)

theorem tsum_latticeGaussian_le {σ t : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) (y : Vertex 2) :
    ∑' x, latticeGaussian σ t x y ≤ gaussMassBound σ :=
  (summable_latticeGaussian hσ ht y).tsum_le_of_sum_le (sum_latticeGaussian_le hσ ht y)

/-- `n ↦ exp(-b n²)` is summable over `ℤ` for `b > 0`. -/
theorem summable_exp_neg_mul_int_sq {b : ℝ} (hb : 0 < b) :
    Summable fun n : ℤ => Real.exp (-b * (n : ℝ) ^ 2) := by
  set q := Real.exp (-b) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hgeo : Summable fun n : ℤ => q ^ n.natAbs := by
    refine summable_of_sum_le (fun n => pow_nonneg hq0 _) (c := 2 / (1 - q)) fun T => ?_
    simpa using sum_pow_natAbs_sub_le hq0 hq1 0 T
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeo
  rw [hq, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have h1 : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
    have h := Nat.le_self_pow (two_ne_zero) n.natAbs
    have h' : ((n.natAbs : ℕ) : ℝ) ≤ ((n.natAbs : ℕ) : ℝ) ^ 2 := by exact_mod_cast h
    rwa [Nat.cast_natAbs, Int.cast_abs, sq_abs] at h'
  rw [Nat.cast_natAbs, Int.cast_abs]
  nlinarith

theorem latticeGaussian_add_left_eq {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (z y : Vertex 2) :
    latticeGaussian σ t (z + y) y = (2 * Real.pi * σ * t)⁻¹ *
      (Real.exp (-Real.pi * (2 * Real.pi * σ * t)⁻¹ * ((z 0 : ℤ) : ℝ) ^ 2) *
        Real.exp (-Real.pi * (2 * Real.pi * σ * t)⁻¹ * ((z 1 : ℤ) : ℝ) ^ 2)) := by
  rw [latticeGaussian_eq, latticeDist_sq, ← Real.exp_add]
  congr 2
  simp only [Pi.add_apply, Int.cast_add, add_sub_cancel_right]
  field_simp
  ring

/-- **Poisson summation**: `Σ_{x ∈ ℤ²} p̄(t, x - y) = (Σ_{n ∈ ℤ} exp(-2π²σt n²))²`. -/
theorem tsum_latticeGaussian_eq {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (y : Vertex 2) :
    ∑' x, latticeGaussian σ t x y =
      (∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * σ * t) * (n : ℝ) ^ 2)) ^ 2 := by
  set a : ℝ := (2 * Real.pi * σ * t)⁻¹ with ha
  have ha0 : 0 < a := by positivity
  set g : ℤ → ℝ := fun n => Real.exp (-Real.pi * a * (n : ℝ) ^ 2) with hg
  have hgs : Summable g :=
    (summable_exp_neg_mul_int_sq (b := Real.pi * a) (by positivity)).congr fun n => by
      simp only [hg]
      ring_nf
  have hnorm : Summable fun n => ‖g n‖ :=
    hgs.congr fun n => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hP : ∑' n, g n = 1 / a ^ (1 / 2 : ℝ) *
      ∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * σ * t) * (n : ℝ) ^ 2) := by
    have hpa : -Real.pi / a = -(2 * Real.pi ^ 2 * σ * t) := by
      rw [ha]
      field_simp
    have h := Real.tsum_exp_neg_mul_int_sq ha0
    rw [hpa] at h
    exact h
  set Θ := ∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * σ * t) * (n : ℝ) ^ 2)
  set r := a ^ (1 / 2 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos ha0 _
  have hr2 : r * r = a := by
    rw [hr, ← Real.rpow_add ha0]
    norm_num
  have hpt : ∀ z : Vertex 2, latticeGaussian σ t (z + y) y = a * (g (z 0) * g (z 1)) :=
    fun z => latticeGaussian_add_left_eq hσ ht z y
  calc ∑' x, latticeGaussian σ t x y = ∑' z, latticeGaussian σ t (z + y) y :=
        ((Equiv.addRight y).tsum_eq (fun x => latticeGaussian σ t x y)).symm
    _ = ∑' z : Vertex 2, a * (g (z 0) * g (z 1)) := tsum_congr hpt
    _ = a * ∑' p : ℤ × ℤ, g p.1 * g p.2 := by
        rw [tsum_mul_left]
        congr 1
        exact (finTwoArrowEquiv ℤ).tsum_eq (fun p => g p.1 * g p.2)
    _ = a * ((∑' n, g n) * ∑' n, g n) := by
        rw [tsum_mul_tsum_of_summable_norm hnorm hnorm]
    _ = a / (r * r) * Θ ^ 2 := by
        rw [hP]
        ring
    _ = Θ ^ 2 := by
        rw [hr2, div_self ha0.ne', one_mul]

/-- For `b ≥ b₀ > 0`: `1 ≤ Σ_n exp(-b n²) ≤ 1 + exp(-(b - b₀)) Σ_n exp(-b₀ n²)`. -/
theorem one_le_tsum_exp_neg_mul_int_sq {b : ℝ} (hb : 0 < b) :
    1 ≤ ∑' n : ℤ, Real.exp (-b * (n : ℝ) ^ 2) := by
  have h := (summable_exp_neg_mul_int_sq hb).le_tsum 0 (fun n _ => (Real.exp_pos _).le)
  simpa using h

theorem tsum_exp_neg_mul_int_sq_le {b b₀ : ℝ} (hb₀ : 0 < b₀) (hbb : b₀ ≤ b) :
    ∑' n : ℤ, Real.exp (-b * (n : ℝ) ^ 2) ≤
      1 + Real.exp (-(b - b₀)) * ∑' n : ℤ, Real.exp (-b₀ * (n : ℝ) ^ 2) := by
  have hb : 0 < b := by linarith
  have hs := summable_exp_neg_mul_int_sq hb
  have hs₀ := summable_exp_neg_mul_int_sq hb₀
  rw [hs.tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero]
  gcongr
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) ?_ (hs₀.mul_left _)
  · split_ifs with hn
    · positivity
    · rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h := Int.one_le_abs hn
        have h' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h
        nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ)]
      nlinarith
  · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
    · split_ifs <;> positivity
    · split_ifs <;> simp [(Real.exp_pos _).le]

/-- **The mass of `p̄(t, · - y)` on `ℤ²`**: `|Σ_{x ∈ ℤ²} p̄(t, x - y) - 1| ≤ C t^{-1/2}` for
`t ≥ 1`. -/
theorem abs_tsum_latticeGaussian_sub_one_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ y : Vertex 2,
      |∑' x, latticeGaussian σ t x y - 1| ≤ C / Real.sqrt t := by
  set b₀ := 2 * Real.pi ^ 2 * σ with hb₀
  have hb₀0 : 0 < b₀ := by positivity
  set Θ₀ := ∑' n : ℤ, Real.exp (-b₀ * (n : ℝ) ^ 2) with hΘ₀
  have hΘ₀1 : 1 ≤ Θ₀ := one_le_tsum_exp_neg_mul_int_sq hb₀0
  set lam := min 1 b₀ with hlam
  have hlam0 : 0 < lam := lt_min one_pos hb₀0
  refine ⟨Θ₀ * (2 + Θ₀) / lam, by positivity, fun t ht y => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hsqt : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left ht0.le]
    nlinarith
  rw [tsum_latticeGaussian_eq hσ ht0 y]
  set b := 2 * Real.pi ^ 2 * σ * t with hb
  have hbb : b₀ ≤ b := by
    rw [hb, hb₀]
    have : 0 < 2 * Real.pi ^ 2 * σ := by positivity
    nlinarith
  set Θ := ∑' n : ℤ, Real.exp (-b * (n : ℝ) ^ 2) with hΘ
  set ε := Real.exp (-(b - b₀)) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hΘ1 : 1 ≤ Θ := one_le_tsum_exp_neg_mul_int_sq (by linarith)
  have hΘu : Θ ≤ 1 + ε * Θ₀ := tsum_exp_neg_mul_int_sq_le hb₀0 hbb
  have hεt : ε ≤ 1 / (lam * Real.sqrt t) := by
    have h1 : 1 + (b - b₀) ≤ Real.exp (b - b₀) := by
      have := Real.add_one_le_exp (b - b₀)
      linarith
    have h2 : lam * t ≤ 1 + (b - b₀) := by
      have hbt : b - b₀ = b₀ * (t - 1) := by rw [hb, hb₀]; ring
      rw [hbt]
      have hl1 : lam ≤ 1 := min_le_left _ _
      have hl2 : lam ≤ b₀ := min_le_right _ _
      nlinarith
    rw [hε, Real.exp_neg]
    calc (Real.exp (b - b₀))⁻¹ ≤ (lam * t)⁻¹ :=
          inv_anti₀ (by positivity) (h2.trans h1)
      _ ≤ (lam * Real.sqrt t)⁻¹ :=
          inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hsqt hlam0.le)
      _ = 1 / (lam * Real.sqrt t) := (one_div _).symm
  have hsq : Θ ^ 2 - 1 = (Θ - 1) * (Θ + 1) := by ring
  rw [abs_of_nonneg (by nlinarith), hsq]
  calc (Θ - 1) * (Θ + 1) ≤ (ε * Θ₀) * (2 + Θ₀) := by
        apply mul_le_mul (by linarith) (by nlinarith) (by linarith) (by positivity)
    _ ≤ (1 / (lam * Real.sqrt t) * Θ₀) * (2 + Θ₀) := by gcongr
    _ = Θ₀ * (2 + Θ₀) / lam / Real.sqrt t := by
        field_simp

/-- **The mass far from `y`**: for `t ≥ 1` the mass of `p̄(t, · - y)` on a set of vertices at
distance at least `t` from `y` is at most `C t^{-1/2}`. -/
theorem sum_latticeGaussian_far_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ (y : Vertex 2) (S : Finset (Vertex 2)),
      (∀ x ∈ S, t ≤ latticeDist x y) → ∑ x ∈ S, latticeGaussian σ t x y ≤ C / Real.sqrt t := by
  set L₀ := 4 * Real.exp (1 / (4 * σ) / 2) * (1 + 1 / (1 / (4 * σ))) ^ 2 with hL₀
  refine ⟨(2 * Real.pi * σ)⁻¹ * L₀ * (4 * σ), by positivity, fun t ht y S hS => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hsqt : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left ht0.le]
    nlinarith
  have hsum := sum_exp_neg_sq_div_le (c := 1 / (4 * σ)) (by positivity) ht y S
  have hpt : ∀ x ∈ S, latticeGaussian σ t x y ≤ (2 * Real.pi * σ * t)⁻¹ *
      Real.exp (-(t / (4 * σ))) * Real.exp (-(1 / (4 * σ) * latticeDist x y ^ 2 / t)) := by
    intro x hx
    have e : (2 * Real.pi * σ * t)⁻¹ * Real.exp (-(t / (4 * σ))) *
        Real.exp (-(1 / (4 * σ) * latticeDist x y ^ 2 / t)) = (2 * Real.pi * σ * t)⁻¹ *
        Real.exp (-(t / (4 * σ)) + -(1 / (4 * σ) * latticeDist x y ^ 2 / t)) := by
      rw [Real.exp_add]
      ring
    rw [e, latticeGaussian_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    have hd : t ≤ latticeDist x y := hS x hx
    have hd2 : t ^ 2 ≤ latticeDist x y ^ 2 := pow_le_pow_left₀ ht0.le hd 2
    have e1 : latticeDist x y ^ 2 / (2 * σ * t) =
        latticeDist x y ^ 2 / (4 * σ * t) + 1 / (4 * σ) * latticeDist x y ^ 2 / t := by
      field_simp
      ring
    have e2 : t / (4 * σ) ≤ latticeDist x y ^ 2 / (4 * σ * t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hexp : Real.exp (-(t / (4 * σ))) ≤ 4 * σ / t := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    have := Real.add_one_le_exp (t / (4 * σ))
    rw [inv_div]
    linarith
  calc ∑ x ∈ S, latticeGaussian σ t x y
      ≤ ∑ x ∈ S, (2 * Real.pi * σ * t)⁻¹ * Real.exp (-(t / (4 * σ))) *
          Real.exp (-(1 / (4 * σ) * latticeDist x y ^ 2 / t)) := Finset.sum_le_sum hpt
    _ = (2 * Real.pi * σ * t)⁻¹ * Real.exp (-(t / (4 * σ))) *
          ∑ x ∈ S, Real.exp (-(1 / (4 * σ) * latticeDist x y ^ 2 / t)) := by
        rw [Finset.mul_sum]
    _ ≤ (2 * Real.pi * σ * t)⁻¹ * (4 * σ / t) * (L₀ * t) := by
        gcongr
    _ = (2 * Real.pi * σ)⁻¹ * L₀ * (4 * σ) / t := by
        field_simp
    _ ≤ (2 * Real.pi * σ)⁻¹ * L₀ * (4 * σ) / Real.sqrt t :=
        div_le_div_of_nonneg_left (by positivity) hst hsqt

end Rigidity.Green

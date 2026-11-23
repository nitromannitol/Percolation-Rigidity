import Rigidity.Proofs.Green.DarioGuGaussianDiff
import Rigidity.Proofs.Green.DarioGuTwoScaleSourceSplit

/-!
# The planar Gaussian on the lattice as a product, and the first term of `f`

The planar heat kernel at lattice points is a product of one-dimensional Gaussians,
`p̄(r, x - y) = (2πσr)^{-1} g(x₀ - y₀) g(x₁ - y₁)` with `g = gauss1 (2σr)`
(`latticeGaussian_eq_prod`), and solves the heat equation `∂_r p̄ = (σ/2) Δ p̄`
(`latticeGaussianTimeDeriv_eq`). The first term of `f` in (4.26) of Dario–Gu, the difference
`∂_r p̄ - (σ/2) Σ_k D_k D_k p̄` of the continuous and the discrete Laplacians, is
`(σ/2)(2πσr)^{-1} Σ_k (g'' - D²g)(u_k) g(u_{k'})` (`timeDeriv_sub_secondDiff_eq`), and is bounded by
`C r^{-5/2} exp(-|x - y|²/(32σr))` (`abs_timeDeriv_sub_secondDiff_le`), the estimate of Step 4 of
the source (lines 2416-2419).
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- **The product structure of the planar Gaussian.** -/
theorem latticeGaussian_eq_prod (σ r : ℝ) (x y : Vertex 2) :
    latticeGaussian σ r x y = (2 * Real.pi * σ * r)⁻¹ *
      (gauss1 (2 * σ * r) ((x 0 : ℝ) - y 0) * gauss1 (2 * σ * r) ((x 1 : ℝ) - y 1)) := by
  unfold latticeGaussian gaussianHeat gauss1
  change (2 * Real.pi * σ * r)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (2 * σ * r))) = _
  rw [latticeDist_sq, ← Real.exp_add]
  congr 2
  ring

/-- **The heat equation** `∂_r p̄ = (σ/2)(∂₀² + ∂₁²) p̄` at lattice points. -/
theorem latticeGaussianTimeDeriv_eq {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (x y : Vertex 2) :
    latticeGaussianTimeDeriv σ r x y = σ / 2 * (2 * Real.pi * σ * r)⁻¹ *
      (gauss1'' (2 * σ * r) ((x 0 : ℝ) - y 0) * gauss1 (2 * σ * r) ((x 1 : ℝ) - y 1) +
        gauss1 (2 * σ * r) ((x 0 : ℝ) - y 0) * gauss1'' (2 * σ * r) ((x 1 : ℝ) - y 1)) := by
  unfold latticeGaussianTimeDeriv gaussianHeatTimeDeriv
  change latticeGaussian σ r x y * (latticeDist x y ^ 2 / (2 * σ * r ^ 2) - 1 / r) = _
  rw [latticeGaussian_eq_prod, latticeDist_sq]
  unfold gauss1''
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hr0 : r ≠ 0 := hr.ne'
  field_simp
  ring

/-- The second difference `D²g(u) = g(u + 2) - 2 g(u + 1) + g(u)`. -/
noncomputable def secondDiff (c u : ℝ) : ℝ :=
  gauss1 c (u + 2) - 2 * gauss1 c (u + 1) + gauss1 c u

theorem cast_add_unit_sub (x y : Vertex 2) (i k : Fin 2) :
    (((x + unit i) k : ℤ) : ℝ) - (y k : ℝ) = ((x k : ℝ) - y k) + (if i = k then 1 else 0) := by
  rw [cast_add_unit_apply]
  ring

/-- **The first term of `f`** as the difference of the continuous and discrete second
derivatives of the one-dimensional Gaussians. -/
theorem timeDeriv_sub_secondDiff_eq {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (x y : Vertex 2) :
    latticeGaussianTimeDeriv σ r x y -
        σ / 2 * ∑ k : Fin 2, fwdDiff k (fwdDiff k fun z => latticeGaussian σ r z y) x =
      σ / 2 * (2 * Real.pi * σ * r)⁻¹ *
        ((gauss1'' (2 * σ * r) ((x 0 : ℝ) - y 0) - secondDiff (2 * σ * r) ((x 0 : ℝ) - y 0)) *
            gauss1 (2 * σ * r) ((x 1 : ℝ) - y 1) +
          gauss1 (2 * σ * r) ((x 0 : ℝ) - y 0) *
            (gauss1'' (2 * σ * r) ((x 1 : ℝ) - y 1) -
              secondDiff (2 * σ * r) ((x 1 : ℝ) - y 1))) := by
  rw [latticeGaussianTimeDeriv_eq hσ hr]
  simp only [fwdDiff, Fin.sum_univ_two, latticeGaussian_eq_prod, cast_add_unit_sub, secondDiff]
  simp only [Fin.isValue, if_true, show ((0 : Fin 2) = 1) = False from by decide,
    show ((1 : Fin 2) = 0) = False from by decide, if_false, add_zero]
  rw [add_assoc (((x 0 : ℤ) : ℝ) - ((y 0 : ℤ) : ℝ)) 1 1,
    add_assoc (((x 1 : ℤ) : ℝ) - ((y 1 : ℤ) : ℝ)) 1 1, one_add_one_eq_two]
  ring

/-- The shift of the Gaussian decay: `g_{8c}(ζ) ≤ e^{1/(2c)} g_{16c}(n)` for `|ζ - n| ≤ 2`. -/
theorem gauss1_shift_le {c : ℝ} (hc : 0 < c) {n ζ : ℝ} (h : |ζ - n| ≤ 2) :
    gauss1 (8 * c) ζ ≤ Real.exp (1 / (2 * c)) * gauss1 (16 * c) n := by
  unfold gauss1
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : (ζ - n) ^ 2 ≤ 4 := by
    have := abs_le.1 h
    nlinarith
  have h2 : n ^ 2 ≤ 2 * ζ ^ 2 + 8 := by nlinarith [sq_nonneg (ζ + (ζ - n))]
  have h3 : n ^ 2 / (16 * c) ≤ (2 * ζ ^ 2 + 8) / (16 * c) :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have e : (2 * ζ ^ 2 + 8) / (16 * c) = ζ ^ 2 / (8 * c) + 1 / (2 * c) := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  linarith

/-- **The bound of the first term of `f`** (Step 4 of the source):
`|∂_r p̄ - (σ/2) Σ_k D_k D_k p̄| ≤ K r^{-5/2} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_timeDeriv_sub_secondDiff_le {σ : ℝ} (hσ : 0 < σ) : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ) (x y : Vertex 2), 1 ≤ r →
      |latticeGaussianTimeDeriv σ r x y -
          σ / 2 * ∑ k : Fin 2, fwdDiff k (fwdDiff k fun z => latticeGaussian σ r z y) x| ≤
        K / (r ^ 2 * Real.sqrt r) * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) := by
  refine ⟨σ / 2 * (2 * Real.pi * σ)⁻¹ * (160 / (2 * σ * Real.sqrt (2 * σ))) *
    Real.exp (1 / (4 * σ)), by positivity, fun r x y hr => ?_⟩
  have hr0 : 0 < r := by linarith
  set c := 2 * σ * r with hcdef
  have hc : 0 < c := by positivity
  set u₀ : ℝ := (x 0 : ℝ) - y 0 with hu₀
  set u₁ : ℝ := (x 1 : ℝ) - y 1 with hu₁
  rw [timeDeriv_sub_secondDiff_eq hσ hr0]
  -- the one-dimensional estimate
  have hD : ∀ n : ℝ, |gauss1'' c n - secondDiff c n| ≤
      80 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n) := by
    intro n
    obtain ⟨ξ, ζ, hξ0, hξ2, hζ, he⟩ := exists_secondDiff_sub_eq hc.ne' n
    have e : gauss1'' c n - secondDiff c n = -((ξ - n) * gauss1''' c ζ) := by
      rw [← he, secondDiff]
      ring
    rw [e, abs_neg, abs_mul, abs_of_pos hξ0]
    have h3 := abs_gauss1'''_le hc ζ
    have hs := gauss1_shift_le hc (show |ζ - n| ≤ 2 by
      rw [abs_le]; constructor <;> linarith [hζ.1, hζ.2])
    calc (ξ - n) * |gauss1''' c ζ| ≤ 2 * (40 / (c * Real.sqrt c) * gauss1 (8 * c) ζ) :=
          mul_le_mul hξ2.le h3 (abs_nonneg _) (by norm_num)
      _ ≤ 2 * (40 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n)) := by
          gcongr
      _ = 80 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n) := by ring
  have hg : ∀ n : ℝ, gauss1 c n ≤ gauss1 (16 * c) n := fun n => gauss1_mono hc (by linarith) n
  have hprod : gauss1 (16 * c) u₀ * gauss1 (16 * c) u₁ =
      Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) := by
    unfold gauss1
    rw [← Real.exp_add, latticeDist_sq]
    congr 1
    rw [hcdef]
    field_simp
    ring
  -- assembly
  have hexp : Real.exp (1 / (2 * c)) ≤ Real.exp (1 / (4 * σ)) := by
    rw [Real.exp_le_exp]
    rw [div_le_div_iff₀ (by positivity) (by positivity), hcdef]
    nlinarith
  have hcs : 160 / (c * Real.sqrt c) = 160 / (2 * σ * Real.sqrt (2 * σ)) / (r * Real.sqrt r) := by
    rw [hcdef, Real.sqrt_mul (by positivity), div_div]
    ring
  set Φ := Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) with hΦ
  have hN : 0 ≤ σ / 2 * (2 * Real.pi * σ * r)⁻¹ := by positivity
  have hA : |(gauss1'' c u₀ - secondDiff c u₀) * gauss1 c u₁ +
      gauss1 c u₀ * (gauss1'' c u₁ - secondDiff c u₁)| ≤
      160 / (c * Real.sqrt c) * Real.exp (1 / (2 * c)) * Φ := by
    rw [← hprod]
    have a1 := hD u₀
    have a2 := hD u₁
    have b1 := hg u₀
    have b2 := hg u₁
    have p0 := gauss1_pos c u₀
    have p1 := gauss1_pos c u₁
    have q0 := gauss1_pos (16 * c) u₀
    have q1 := gauss1_pos (16 * c) u₁
    have hk : 0 ≤ 80 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) u₀) := by
      positivity
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos p1, abs_of_pos p0]
    calc |gauss1'' c u₀ - secondDiff c u₀| * gauss1 c u₁ +
          gauss1 c u₀ * |gauss1'' c u₁ - secondDiff c u₁|
        ≤ 80 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) u₀) *
            gauss1 (16 * c) u₁ +
          gauss1 (16 * c) u₀ *
            (80 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) u₁)) :=
          add_le_add (mul_le_mul a1 b2 p1.le hk) (mul_le_mul b1 a2 (abs_nonneg _) q0.le)
      _ = 160 / (c * Real.sqrt c) * Real.exp (1 / (2 * c)) *
            (gauss1 (16 * c) u₀ * gauss1 (16 * c) u₁) := by ring
  calc |σ / 2 * (2 * Real.pi * σ * r)⁻¹ * ((gauss1'' c u₀ - secondDiff c u₀) * gauss1 c u₁ +
        gauss1 c u₀ * (gauss1'' c u₁ - secondDiff c u₁))|
      = σ / 2 * (2 * Real.pi * σ * r)⁻¹ * |(gauss1'' c u₀ - secondDiff c u₀) * gauss1 c u₁ +
        gauss1 c u₀ * (gauss1'' c u₁ - secondDiff c u₁)| := by rw [abs_mul, abs_of_nonneg hN]
    _ ≤ σ / 2 * (2 * Real.pi * σ * r)⁻¹ *
          (160 / (c * Real.sqrt c) * Real.exp (1 / (2 * c)) * Φ) :=
        mul_le_mul_of_nonneg_left hA hN
    _ ≤ σ / 2 * (2 * Real.pi * σ * r)⁻¹ *
          (160 / (2 * σ * Real.sqrt (2 * σ)) / (r * Real.sqrt r) * Real.exp (1 / (4 * σ)) * Φ) := by
        rw [hcs]
        gcongr
    _ = σ / 2 * (2 * Real.pi * σ)⁻¹ * (160 / (2 * σ * Real.sqrt (2 * σ))) *
          Real.exp (1 / (4 * σ)) / (r ^ 2 * Real.sqrt r) * Φ := by
        field_simp

end Rigidity.Green

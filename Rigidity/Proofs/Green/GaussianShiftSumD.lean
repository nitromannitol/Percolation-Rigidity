import Rigidity.Proofs.Green.GaussianShiftD
import Rigidity.Proofs.Green.LatticeGaussianD

/-!
# Moving the centre of a Gaussian kernel summed over the lattice

For `s ≥ 1`, a lattice point `y'` and `m ∈ ℝ^d` with `|m - y'| ≤ ρ`,

  `Σ_{z ∈ ℤ^d} |p̄(s, z - m) - p̄(s, z - y')| ≤ K_ρ s^{-1/2}`,
  `K_ρ = e^{ρ²/(2σ)} (ρ √8 σ^{-1/2} 4^{d/2} M_σ + ρ²/(2σ) 2^{d/2} M_σ)`

(`tsum_abs_gaussianHeatD_shift_le`), from `abs_gaussianHeatD_sub_le`, `x e^{-x²/c} ≤ √c` and the
mass bound `M_σ` of the Gaussian kernels at the times `2s` and `4s`.
-/

open LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- `(2πσs)^{-d/2} e^{-|u|²/(2σks)} = k^{d/2} p̄(ks, u)`. -/
theorem rpow_mul_exp_eq_gaussianHeatD {σ s k : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hk : 0 < k)
    (u : EuclideanSpace ℝ (Fin d)) :
    (2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖u‖ ^ 2 / (2 * σ * (k * s)))) =
      k ^ ((d : ℝ) / 2) * gaussianHeatD d σ (k * s) u := by
  unfold gaussianHeatD
  rw [show 2 * Real.pi * σ * (k * s) = k * (2 * Real.pi * σ * s) by ring,
    Real.mul_rpow (x := k) (y := 2 * Real.pi * σ * s) hk.le (by positivity)]
  have hk' : k ^ ((d : ℝ) / 2) * k ^ (-((d : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hk]; simp
  calc _ = (k ^ ((d : ℝ) / 2) * k ^ (-((d : ℝ) / 2))) * ((2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)) *
        Real.exp (-(‖u‖ ^ 2 / (2 * σ * (k * s))))) := by rw [hk', one_mul]
    _ = _ := by ring

/-- The constant `K_ρ`. -/
noncomputable def shiftConstD (d : ℕ) (σ ρ : ℝ) : ℝ :=
  Real.exp (ρ ^ 2 / (2 * σ)) * (ρ * Real.sqrt 8 / Real.sqrt σ * (4 ^ ((d : ℝ) / 2) *
    gaussMassBoundD d σ) + ρ ^ 2 / (2 * σ) * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ))

/-- **Moving the centre of a Gaussian kernel, summed over the lattice.** -/
theorem tsum_abs_gaussianHeatD_shift_le {σ s ρ : ℝ} (hσ : 0 < σ) (hs : 1 ≤ s) (hρ : 0 ≤ ρ)
    (y' : Vertex d) (m : EuclideanSpace ℝ (Fin d))
    (hm : ‖m - latticeEuclideanEmbedding y'‖ ≤ ρ) :
    Summable (fun z => |gaussianHeatD d σ s (latticeEuclideanEmbedding z - m) -
        gaussianHeatD d σ s (edzD z y')|) ∧
      ∑' z, |gaussianHeatD d σ s (latticeEuclideanEmbedding z - m) -
        gaussianHeatD d σ s (edzD z y')| ≤ shiftConstD d σ ρ * s ^ (-(1 / 2 : ℝ)) := by
  have hs0 : 0 < s := by linarith
  have hc : 0 < 2 * σ * s := by positivity
  set E := Real.exp (ρ ^ 2 / (2 * σ * s)) with hE
  set a1 := ρ / (σ * s) * Real.sqrt (8 * σ * s) * 4 ^ ((d : ℝ) / 2) with ha1
  set a2 := ρ ^ 2 / (2 * σ * s) * 2 ^ ((d : ℝ) / 2) with ha2
  have hpt : ∀ z, |gaussianHeatD d σ s (latticeEuclideanEmbedding z - m) -
      gaussianHeatD d σ s (edzD z y')| ≤
      E * (a1 * gaussianHeatD d σ (4 * s) (edzD z y') +
        a2 * gaussianHeatD d σ (2 * s) (edzD z y')) := by
    intro z
    set u := edzD z y' with hu
    have huv : ‖u - (latticeEuclideanEmbedding z - m)‖ ≤ ρ := by
      have : u - (latticeEuclideanEmbedding z - m) = m - latticeEuclideanEmbedding y' := by
        rw [hu, edzD]; abel
      rw [this]; exact hm
    rw [abs_sub_comm]
    have h := abs_gaussianHeatD_sub_le (d := d) hσ hs0 hρ huv
    refine h.trans ?_
    set P := (2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)) with hP
    have hP0 : 0 ≤ P := by positivity
    have h2 : P * Real.exp (-(‖u‖ ^ 2 / (4 * σ * s))) =
        2 ^ ((d : ℝ) / 2) * gaussianHeatD d σ (2 * s) u := by
      rw [← rpow_mul_exp_eq_gaussianHeatD hσ hs0 (by norm_num : (0 : ℝ) < 2),
        show 2 * σ * (2 * s) = 4 * σ * s by ring]
    have h4 : P * Real.exp (-(‖u‖ ^ 2 / (8 * σ * s))) =
        4 ^ ((d : ℝ) / 2) * gaussianHeatD d σ (4 * s) u := by
      rw [← rpow_mul_exp_eq_gaussianHeatD hσ hs0 (by norm_num : (0 : ℝ) < 4),
        show 2 * σ * (4 * s) = 8 * σ * s by ring]
    have hsplit : Real.exp (-(‖u‖ ^ 2 / (4 * σ * s))) =
        Real.exp (-(‖u‖ ^ 2 / (8 * σ * s))) * Real.exp (-(‖u‖ ^ 2 / (8 * σ * s))) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have hx := mul_exp_neg_sq_div_le (norm_nonneg u) (by positivity : 0 < 8 * σ * s)
    have hnorm : ‖u‖ * (P * Real.exp (-(‖u‖ ^ 2 / (4 * σ * s)))) ≤
        Real.sqrt (8 * σ * s) * (4 ^ ((d : ℝ) / 2) * gaussianHeatD d σ (4 * s) u) := by
      rw [hsplit, ← h4]
      have : ‖u‖ * (P * (Real.exp (-(‖u‖ ^ 2 / (8 * σ * s))) *
          Real.exp (-(‖u‖ ^ 2 / (8 * σ * s))))) = (‖u‖ * Real.exp (-(‖u‖ ^ 2 / (8 * σ * s)))) *
          (P * Real.exp (-(‖u‖ ^ 2 / (8 * σ * s)))) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hx (by positivity)
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    calc ρ * (2 * ‖u‖ + ρ) / (2 * σ * s) * E * (P * Real.exp (-(‖u‖ ^ 2 / (4 * σ * s))))
        = E * (ρ / (σ * s) * (‖u‖ * (P * Real.exp (-(‖u‖ ^ 2 / (4 * σ * s))))) +
          ρ ^ 2 / (2 * σ * s) * (P * Real.exp (-(‖u‖ ^ 2 / (4 * σ * s))))) := by
          field_simp; try ring
      _ ≤ E * (ρ / (σ * s) * (Real.sqrt (8 * σ * s) * (4 ^ ((d : ℝ) / 2) *
            gaussianHeatD d σ (4 * s) u)) +
          ρ ^ 2 / (2 * σ * s) * (2 ^ ((d : ℝ) / 2) * gaussianHeatD d σ (2 * s) u)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hnorm
            (by positivity)) (le_of_eq (by rw [h2]))) hE0
      _ = _ := by rw [ha1, ha2]; ring
  have hs4 := summable_gaussianHeatD (d := d) hσ (by linarith : (0 : ℝ) < 4 * s) y'
  have hs2 := summable_gaussianHeatD (d := d) hσ (by linarith : (0 : ℝ) < 2 * s) y'
  have hR : Summable fun z => E * (a1 * gaussianHeatD d σ (4 * s) (edzD z y') +
      a2 * gaussianHeatD d σ (2 * s) (edzD z y')) :=
    ((hs4.mul_left a1).add (hs2.mul_left a2)).mul_left E
  have hS : Summable (fun z => |gaussianHeatD d σ s (latticeEuclideanEmbedding z - m) -
      gaussianHeatD d σ s (edzD z y')|) :=
    hR.of_nonneg_of_le (fun z => abs_nonneg _) hpt
  refine ⟨hS, ?_⟩
  have hM := one_le_gaussMassBoundD (d := d) hσ
  have hM4 := tsum_gaussianHeatD_le (d := d) hσ (by linarith : 1 ≤ 4 * s) y'
  have hM2 := tsum_gaussianHeatD_le (d := d) hσ (by linarith : 1 ≤ 2 * s) y'
  have ha10 : 0 ≤ a1 := by positivity
  have ha20 : 0 ≤ a2 := by positivity
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hsum : ∑' z, E * (a1 * gaussianHeatD d σ (4 * s) (edzD z y') +
      a2 * gaussianHeatD d σ (2 * s) (edzD z y')) ≤ E * (a1 * gaussMassBoundD d σ +
        a2 * gaussMassBoundD d σ) := by
    rw [tsum_mul_left, (hs4.mul_left a1).tsum_add (hs2.mul_left a2), tsum_mul_left, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hM4 ha10)
      (mul_le_mul_of_nonneg_left hM2 ha20)) hE0
  -- the constants for `s ≥ 1`
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hrs : s ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt s := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hs0.le, inv_eq_one_div]
  have hEle : E ≤ Real.exp (ρ ^ 2 / (2 * σ)) := by
    apply Real.exp_le_exp.2
    exact div_le_div_of_nonneg_left (sq_nonneg ρ) (by positivity) (by nlinarith)
  have ha1e : a1 = ρ * Real.sqrt 8 / Real.sqrt σ * 4 ^ ((d : ℝ) / 2) * (1 / Real.sqrt s) := by
    rw [ha1, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    have hσs : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
    have e1 : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ.le
    have e2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
    calc ρ / (σ * s) * (Real.sqrt 8 * Real.sqrt σ * Real.sqrt s) * 4 ^ ((d : ℝ) / 2)
        = ρ / ((Real.sqrt σ * Real.sqrt σ) * (Real.sqrt s * Real.sqrt s)) *
          (Real.sqrt 8 * Real.sqrt σ * Real.sqrt s) * 4 ^ ((d : ℝ) / 2) := by rw [e1, e2]
      _ = _ := by field_simp
  have ha2e : a2 ≤ ρ ^ 2 / (2 * σ) * 2 ^ ((d : ℝ) / 2) * (1 / Real.sqrt s) := by
    rw [ha2]
    have h1 : 1 / s ≤ 1 / Real.sqrt s := by
      apply one_div_le_one_div_of_le hsq
      calc Real.sqrt s ≤ Real.sqrt s * Real.sqrt s :=
            le_mul_of_one_le_right hsq.le (Real.one_le_sqrt.2 hs)
        _ = s := Real.mul_self_sqrt hs0.le
    have e : ρ ^ 2 / (2 * σ * s) * 2 ^ ((d : ℝ) / 2) =
        ρ ^ 2 / (2 * σ) * 2 ^ ((d : ℝ) / 2) * (1 / s) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  calc _ ≤ ∑' z, E * (a1 * gaussianHeatD d σ (4 * s) (edzD z y') +
        a2 * gaussianHeatD d σ (2 * s) (edzD z y')) := hS.tsum_le_tsum hpt hR
    _ ≤ E * (a1 * gaussMassBoundD d σ + a2 * gaussMassBoundD d σ) := hsum
    _ ≤ Real.exp (ρ ^ 2 / (2 * σ)) *
        (ρ * Real.sqrt 8 / Real.sqrt σ * 4 ^ ((d : ℝ) / 2) * (1 / Real.sqrt s) *
          gaussMassBoundD d σ +
        ρ ^ 2 / (2 * σ) * 2 ^ ((d : ℝ) / 2) * (1 / Real.sqrt s) * gaussMassBoundD d σ) := by
        rw [← ha1e]
        gcongr
    _ = _ := by rw [hrs, shiftConstD]; ring

end Rigidity.Green

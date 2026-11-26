import Rigidity.Proofs.Green.GeneralTwoScaleSourceBound

/-!
# The whole-cluster estimate (4.40) of Dario–Gu on `ℤ^d`

Step 5 of the proof of Proposition 4.3 of Dario–Gu (lines 2448-2490 of the source), first pass
(weight one), on `ℤ^d`, `d ≥ 2`, with initial time `τ` and final time `3τ`: for
`u(s) = 1_𝒞 (h(s, ·, y) - P_{s - τ} 1_𝒞 h(τ, ·, y))` (`clusterWD`),

`Σ_x u(3τ, x)² ≤ C τ^{α - d/2 - 1}`

(`tsum_sq_clusterWD_le`), when on the cluster the corrector grows like
`B (√r + |x - y| + 2)^α` and the weak norms of the centered flux on the dyadic balls of radius
`2^{m+2}√r` are at most `C_f (2^{m+2}√r)^α`, at every scale `r ≥ τ` (Propositions 2.12 and 2.13 above
their minimal scales). This is (4.40) with `t = 3τ`: the energy inequality
`∂_s Σ_x u² ≤ s^{-1} Σ_x u² + 2Q s^{α - d/2 - 2}` (Steps 2-4, `tsum_clusterSourceD_le`) integrated
from `u(τ) = 0` (`energy_first_passD`).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

/-- **(4.40) on `ℤ^d`** for one configuration: `Σ_x u(3τ, x)² ≤ C τ^{α - d/2 - 1}`. -/
theorem tsum_sq_clusterWD_le [NeZero d] (hd : 2 ≤ d) {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    {B Cf α : ℝ} (hB : 0 ≤ B) (hCf : 0 ≤ Cf) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ω : Configuration d) (K : OpenComponent ω) (y : Vertex d)
      (χ : Fin d → Vertex d → ℝ) (τ : ℝ), IsDGCorrectorD K y χ → 1 ≤ τ →
      (∀ r, τ ≤ r → ∀ z ∈ K.supp, ∀ k, |χ k z| ≤ B * (Real.sqrt r + ‖edzD z y‖ + 2) ^ α) →
      (∀ r, τ ≤ r → ∀ k i : Fin d, ∀ m : ℕ,
        WeakNormLeD ω (dgClusterBallD K y (2 ^ (m + 2) * Real.sqrt r))
          (centeredFluxD ω σ χ k i) (Cf * (2 ^ (m + 2) * Real.sqrt r) ^ α)) →
      ∑' x, clusterWD K σ θ χ τ y (3 * τ) x ^ 2 ≤ C * τ ^ (α - (d : ℝ) / 2 - 1) := by
  obtain ⟨Q, hQ0, hQ⟩ := tsum_clusterSourceD_le hd hσ hθ hB hCf hα0 hα1
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h3 : 0 < 3 - (α - (d : ℝ) / 2 + 1) := by linarith
  refine ⟨2 * Q / (3 - (α - (d : ℝ) / 2 + 1)) * 3,
    mul_nonneg (div_nonneg (by positivity) h3.le) (by norm_num),
    fun ω K y χ τ hχK hτ hgr hW => ?_⟩
  have hτ0 : 0 < τ := by linarith
  have hτt : τ ≤ 3 * τ := by linarith
  -- the linear growth of the corrector, for the domination
  set A := B * (Real.sqrt τ + 2) with hAdef
  have hA : 0 ≤ A := by positivity
  have hlin : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + ‖edzD x y‖) := by
    intro x hx k
    have h := hgr τ le_rfl x hx k
    have hv := norm_nonneg (edzD x y)
    have hs := Real.sqrt_nonneg τ
    refine h.trans ?_
    have h1 : (Real.sqrt τ + ‖edzD x y‖ + 2) ^ α ≤ Real.sqrt τ + ‖edzD x y‖ + 2 := by
      calc (Real.sqrt τ + ‖edzD x y‖ + 2) ^ α ≤ (Real.sqrt τ + ‖edzD x y‖ + 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hα1
        _ = Real.sqrt τ + ‖edzD x y‖ + 2 := Real.rpow_one _
    have h2 : Real.sqrt τ + ‖edzD x y‖ + 2 ≤ (Real.sqrt τ + 2) * (1 + ‖edzD x y‖) := by
      nlinarith
    calc B * (Real.sqrt τ + ‖edzD x y‖ + 2) ^ α ≤ B * (Real.sqrt τ + ‖edzD x y‖ + 2) :=
          mul_le_mul_of_nonneg_left h1 hB
      _ ≤ B * ((Real.sqrt τ + 2) * (1 + ‖edzD x y‖)) := mul_le_mul_of_nonneg_left h2 hB
      _ = A * (1 + ‖edzD x y‖) := by rw [hAdef]; ring
  obtain ⟨D, hD, hDu⟩ := exists_clusterWD_dom (θ := θ) hσ hτ hτt hA hlin
  obtain ⟨D', hD', hDu'⟩ := exists_clusterWD_deriv_dom (θ := θ) hχK hσ hτ hτt hA hlin
  have hf := summable_sq_clusterInitD (θ := θ) hσ hτ hlin
  -- the estimate of the source term at every time
  have hsrc : ∀ s ∈ Set.Ioo τ (3 * τ), ∑' x, clusterWD K σ θ χ τ y s x *
      clusterSourceD K σ θ χ y s x ≤ openEnergyD ω (clusterWD K σ θ χ τ y s) +
        1 / (2 * s) * ∑' x, clusterWD K σ θ χ τ y s x ^ 2 +
          Q * s ^ ((α - (d : ℝ) / 2 + 1) - 3) := by
    intro s hs
    have hs1 : 1 ≤ s := hτ.trans hs.1.le
    have hvs : Summable fun x => clusterWD K σ θ χ τ y s x ^ 2 :=
      Summable.of_nonneg_of_le (fun x => sq_nonneg _)
        (fun x => sq_le_sq_of_abs_leD (hDu s ⟨hs.1.le, hs.2.le⟩ x)) hD
    have hvK : ∀ x, x ∉ K.supp → clusterWD K σ θ χ τ y s x = 0 := fun x hx => by
      simp only [clusterWD, if_neg hx]
    have h := hQ ω K y χ s (clusterWD K σ θ χ τ y s) hs1 (hgr s hs.1.le) (hW s hs.1.le) hvs hvK
    rw [show (α - (d : ℝ) / 2 + 1) - 3 = α - (d : ℝ) / 2 - 2 by ring]
    exact h
  have h := energy_first_passD ω (u := clusterWD K σ θ χ τ y) (G := clusterSourceD K σ θ χ y)
    (Q := Q) (α := α - (d : ℝ) / 2 + 1) hτ0 hτt hQ0 (by linarith) hD hD'
    (fun s hs x => hDu s ⟨hs.1.le, hs.2.le⟩ x)
    (fun s hs x => hDu' s ⟨hs.1, hs.2.le⟩ x)
    (fun s hs x => hasDerivAt_clusterWD hχK hσ hf (T := 3 * τ - τ + 1)
      ⟨by linarith [hs.1], by linarith [hs.2]⟩ (hτ0.trans hs.1) x)
    (continuousOn_tsum_sq_clusterWD hσ hτ hτt hA hlin)
    (fun x => clusterWD_self K σ θ χ τ y x) hsrc
  refine h.trans (le_of_eq ?_)
  rw [show (α - (d : ℝ) / 2 + 1) - 2 = α - (d : ℝ) / 2 - 1 by ring,
    show 3 * τ / τ = 3 by field_simp]

end Rigidity.Green.GeneralDim

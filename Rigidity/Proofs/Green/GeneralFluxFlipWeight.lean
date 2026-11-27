import Rigidity.Proofs.Green.GeneralFluxP2Input

/-!
# Each flip difference of the heat average of the flux on `ℤ^d` bounded by the Step 2 factor

The extension of the first half of `DarioGuFluxFlipSum.lean` from `ℤ²` to `ℤ^d`: with the bounds
for the bonds open in `ω` (`FluxOpenBoundD`) and closed in `ω` (`ae_fluxFlipD_sq_le_closed`), every
squared flip difference of `X = Σ_z Φ_{r²}(x, z) flux_{e_k}(z, i)` across the bond of `a = (x₀, i')`
is at most

`K₀ R^{7d} (Σ_{B(x₀, R)} G)² (Σ_{B(x₀, R)} E_v + Σ_{B(x₀, R)} Φ_{r²}(x, ·)²)`

for every radius `R ≥ 6 max(s_ω(x₀), s_ω(y₀), s_{ω^{e,0}}(x₀))` (`ae_fluxFlipD_sq_le_radius`, from
the deterministic `sq_le_radius_of_bounds`), with `K₀ = fluxFlipConst d`, `G = planeGrad` and `v`
the potential of the Green projection of the heat field of the edges. With the radius
`stepTwoRadius 6 ω a = 6 max(s_ω(x₀), s_ω(y₀), s_{ω^{e,0}}(x₀))` this is the boundary statement
`FluxFlipWeightBoundD` of part 2 of the port (`fluxFlipWeightBoundD_of_open`), the form of the bound
(4) of the Step 2 sum of the proof of Lemma 3.3 of Dario (*Optimal corrector estimates on
percolation clusters*) used for the corrector (`ae_flipTermTwo_sq_le_weight`).

The planar statement has the box parameter `C₀ + 5C + 6` and the constant `2 · 1297⁴ · 46656`
from Lemma 3.5 with constants `C₀, C`; here the scale of the corrected Lemma 3.5 enters through
the radius, and the box parameter is `6`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Corrector.GeneralDim
open Rigidity.Poincare.GeneralDim (zdHeat zdHeat_nonneg)
open scoped Classical ENNReal InnerProductSpace

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

/-- The arithmetic of the bound for a bond open in the configuration. -/
theorem open_flux_weight_arithD {c S R g SG e SE φ SΦ : ℝ} {n m : ℕ} (hc : 0 ≤ c) (hS : 1 ≤ S)
    (hSR : S ≤ R) (hnm : 4 * n ≤ m) (hg : 0 ≤ g) (hgS : g ≤ SG) (he : 0 ≤ e) (heS : e ≤ SE)
    (hφ : 0 ≤ φ) (hφS : φ ≤ SΦ) :
    2 * (1 + (c * S ^ n) ^ 2) ^ 2 * g ^ 2 * (e + φ) ≤
      2 * (1 + c ^ 2) ^ 2 * (R ^ m * SG ^ 2) * (SE + SΦ) := by
  have hS0 : 0 ≤ S := by linarith
  have hR0 : 0 ≤ R := hS0.trans hSR
  have h2n : 1 ≤ S ^ (2 * n) := one_le_pow₀ hS
  have h1 : 1 + (c * S ^ n) ^ 2 ≤ (1 + c ^ 2) * S ^ (2 * n) := by
    have e1 : (c * S ^ n) ^ 2 = c ^ 2 * S ^ (2 * n) := by ring
    rw [e1]
    have hc2 : 0 ≤ c ^ 2 := pow_nonneg hc 2
    nlinarith [hc2]
  have h2 : (1 + (c * S ^ n) ^ 2) ^ 2 ≤ (1 + c ^ 2) ^ 2 * R ^ m := by
    have h3 : S ^ (4 * n) ≤ R ^ m :=
      (pow_le_pow_left₀ hS0 hSR _).trans (pow_le_pow_right₀ (by linarith) hnm)
    calc (1 + (c * S ^ n) ^ 2) ^ 2 ≤ ((1 + c ^ 2) * S ^ (2 * n)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = (1 + c ^ 2) ^ 2 * S ^ (4 * n) := by ring
      _ ≤ (1 + c ^ 2) ^ 2 * R ^ m := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hg2 : g ^ 2 ≤ SG ^ 2 := pow_le_pow_left₀ hg hgS 2
  have hS' : e + φ ≤ SE + SΦ := add_le_add heS hφS
  calc 2 * (1 + (c * S ^ n) ^ 2) ^ 2 * g ^ 2 * (e + φ)
      ≤ 2 * ((1 + c ^ 2) ^ 2 * R ^ m) * SG ^ 2 * (SE + SΦ) := by
        have := hR0
        gcongr
    _ = 2 * (1 + c ^ 2) ^ 2 * (R ^ m * SG ^ 2) * (SE + SΦ) := by ring

/-- The arithmetic of the bound for a bond closed in the configuration. -/
theorem closed_flux_weight_arithD {D R g SG b e SE φ SΦ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hR : 1 ≤ R)
    (hnm : n ≤ m) (hg : 0 ≤ g) (hgS : g ≤ SG) (hb : 0 ≤ b) (hbR : b ≤ 3 ^ n * R ^ n) (he : 0 ≤ e)
    (heS : e ≤ SE) (hφ : 0 ≤ φ) (hφS : φ ≤ SΦ) :
    D * g ^ 2 * b * (e + φ) ≤ D * 3 ^ n * (R ^ m * SG ^ 2) * (SE + SΦ) := by
  have hRn : R ^ n ≤ R ^ m := pow_le_pow_right₀ hR hnm
  have hb' : b ≤ 3 ^ n * R ^ m := hbR.trans (mul_le_mul_of_nonneg_left hRn (by positivity))
  have hg2 : g ^ 2 ≤ SG ^ 2 := pow_le_pow_left₀ hg hgS 2
  have hS' : e + φ ≤ SE + SΦ := add_le_add heS hφS
  calc D * g ^ 2 * b * (e + φ) ≤ D * SG ^ 2 * (3 ^ n * R ^ m) * (SE + SΦ) := by gcongr
    _ = D * 3 ^ n * (R ^ m * SG ^ 2) * (SE + SΦ) := by ring

/-- The constant `K₀ = 2 (1 + c²)² + 4096 d³ 3^d` of the bound of each flip difference, for the
constant `c` of the bound for the open bonds. -/
noncomputable def flipWeightConst (d : ℕ) (c : ℝ) : ℝ :=
  2 * (1 + c ^ 2) ^ 2 + 4096 * (d : ℝ) ^ 3 * 3 ^ d

theorem flipWeightConst_pos (d : ℕ) (c : ℝ) : 0 < flipWeightConst d c := by
  unfold flipWeightConst
  positivity

/-- The constant of `FluxOpenBoundD`, `c = 8d 7^d 243^d`. -/
noncomputable def fluxOpenConst (d : ℕ) : ℝ := 8 * d * 7 ^ d * 243 ^ d

/-- **One flip at a radius above the scale, deterministically**: if `X` obeys the bound of
`ae_fluxFlipD_sq_le_closed` when the bond is closed and the bound of `FluxOpenBoundD` (with a
constant `c`) when it is open, then for every `R ≥ 6 max(s₀, s₁, s₂)`,
`X ≤ K₀ R^{7d} (Σ_{B(x₀, R)} g)² (Σ_{B(x₀, R)} e + Σ_{B(x₀, R)} φ²)`. -/
theorem sq_le_radius_of_bounds {X c : ℝ} {P : Prop} {x₀ : Vertex d} {g e φ : Vertex d → ℝ}
    {s₀ s₁ s₂ R : ℕ} (hc : 0 ≤ c) (hg : ∀ z, 0 ≤ g z) (he : ∀ u, 0 ≤ e u) (hs₀ : 1 ≤ s₀)
    (hR : 6 * max (max s₀ s₁) s₂ ≤ R)
    (hcl : ¬ P → X ≤ 4096 * (d : ℝ) ^ 3 *
      (∑ z ∈ LatticeProb.boxFinset x₀ (1 + 5 * max s₀ s₁), g z) ^ 2 *
        (LatticeProb.boxFinset x₀ (1 + 5 * max s₀ s₁)).card *
      (∑ u ∈ LatticeProb.boxFinset x₀ (1 + 5 * max s₀ s₁), e u + φ x₀ ^ 2))
    (hop : P → X ≤ 2 * (1 + (c * (((max s₀ s₂ : ℕ) : ℝ)) ^ d) ^ 2) ^ 2 * g x₀ ^ 2 *
      (e x₀ + φ x₀ ^ 2)) :
    X ≤ flipWeightConst d c * ((R : ℝ) ^ (7 * d) * (∑ z ∈ LatticeProb.boxFinset x₀ R, g z) ^ 2) *
      (∑ u ∈ LatticeProb.boxFinset x₀ R, e u + ∑ y ∈ LatticeProb.boxFinset x₀ R, φ y ^ 2) := by
  have hR1 : 1 ≤ R := by
    have : s₀ ≤ max (max s₀ s₁) s₂ := (le_max_left _ _).trans (le_max_left _ _)
    omega
  have hRr1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  set SG := ∑ z ∈ LatticeProb.boxFinset x₀ R, g z with hSG
  set SE := ∑ u ∈ LatticeProb.boxFinset x₀ R, e u with hSE
  set SΦ := ∑ y ∈ LatticeProb.boxFinset x₀ R, φ y ^ 2 with hSΦ
  have hSG0 : 0 ≤ SG := Finset.sum_nonneg fun z _ => hg z
  have hSE0 : 0 ≤ SE := Finset.sum_nonneg fun u _ => he u
  have hSΦ0 : 0 ≤ SΦ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF0 : 0 ≤ ((R : ℝ) ^ (7 * d) * SG ^ 2) * (SE + SΦ) := by positivity
  have hxB : x₀ ∈ LatticeProb.boxFinset x₀ R :=
    Rigidity.Poincare.GeneralDim.self_mem_supBox x₀ _
  have hΦx : φ x₀ ^ 2 ≤ SΦ :=
    Finset.single_le_sum (f := fun y => φ y ^ 2) (fun _ _ => sq_nonneg _) hxB
  by_cases hP : P
  · -- the bond is open
    have h := hop hP
    have hS1 : (1 : ℝ) ≤ ((max s₀ s₂ : ℕ) : ℝ) := by
      have : 1 ≤ max s₀ s₂ := le_trans hs₀ (le_max_left _ _)
      exact_mod_cast this
    have hSR : ((max s₀ s₂ : ℕ) : ℝ) ≤ (R : ℝ) := by
      have : max s₀ s₂ ≤ R := by
        have h1 : max s₀ s₂ ≤ max (max s₀ s₁) s₂ :=
          max_le ((le_max_left _ _).trans (le_max_left _ _)) (le_max_right _ _)
        omega
      exact_mod_cast this
    have key := open_flux_weight_arithD (n := d) (m := 7 * d) hc hS1 hSR (by omega) (hg x₀)
      (Finset.single_le_sum (f := g) (fun z _ => hg z) hxB) (he x₀)
      (Finset.single_le_sum (f := e) (fun u _ => he u) hxB) (sq_nonneg _) hΦx
    have hK : 2 * (1 + c ^ 2) ^ 2 ≤ flipWeightConst d c := by
      unfold flipWeightConst
      have : (0 : ℝ) ≤ 4096 * (d : ℝ) ^ 3 * 3 ^ d := by positivity
      linarith
    calc X ≤ _ := h
      _ ≤ 2 * (1 + c ^ 2) ^ 2 * ((R : ℝ) ^ (7 * d) * SG ^ 2) * (SE + SΦ) := key
      _ ≤ flipWeightConst d c * ((R : ℝ) ^ (7 * d) * SG ^ 2) * (SE + SΦ) := by
          rw [mul_assoc, mul_assoc (flipWeightConst d c)]
          exact mul_le_mul_of_nonneg_right hK hF0
  · -- the bond is closed
    have h := hcl hP
    have hr0 : 1 + 5 * max s₀ s₁ ≤ R := by
      have h1 : 1 ≤ max s₀ s₁ := le_trans hs₀ (le_max_left _ _)
      have h2 : max s₀ s₁ ≤ max (max s₀ s₁) s₂ := le_max_left _ _
      omega
    have hsub : LatticeProb.boxFinset x₀ (1 + 5 * max s₀ s₁) ⊆ LatticeProb.boxFinset x₀ R :=
      LatticeProb.boxFinset_mono hr0
    have key := closed_flux_weight_arithD (D := 4096 * (d : ℝ) ^ 3) (n := d) (m := 7 * d)
      (b := ((LatticeProb.boxFinset x₀ (1 + 5 * max s₀ s₁)).card : ℝ))
      (by positivity) hRr1 (by omega) (Finset.sum_nonneg fun z _ => hg z)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hg z)
      (Nat.cast_nonneg _) (card_boxFinset_le_pow (x := x₀) hr0 hR1)
      (Finset.sum_nonneg fun u _ => he u)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => he u) (sq_nonneg _) hΦx
    have hK : 4096 * (d : ℝ) ^ 3 * 3 ^ d ≤ flipWeightConst d c := by
      unfold flipWeightConst
      have : (0 : ℝ) ≤ 2 * (1 + c ^ 2) ^ 2 := by positivity
      linarith
    calc X ≤ _ := h
      _ ≤ 4096 * (d : ℝ) ^ 3 * 3 ^ d * ((R : ℝ) ^ (7 * d) * SG ^ 2) * (SE + SΦ) := key
      _ ≤ flipWeightConst d c * ((R : ℝ) ^ (7 * d) * SG ^ 2) * (SE + SΦ) := by
          rw [mul_assoc, mul_assoc (flipWeightConst d c)]
          exact mul_le_mul_of_nonneg_right hK hF0

end Rigidity.Green.GeneralFlux

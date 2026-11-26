import Rigidity.Proofs.Green.DarioGuFluxClosedBound
import Rigidity.Proofs.Corrector.DarioStepTwoSum

/-!
# The sum over the bonds of the squared flip differences of the heat average of the flux

With the bounds for the bonds open and closed in `ω` (`ae_fluxFlip_sq_le_open`,
`ae_fluxFlip_sq_le_closed`), every flip difference of `X = Σ_z Φ_{r²}(x, z) flux_{e_k}(z, i)` is at
most `K₀ F_a (Σ_{B_a} E_v + Σ_{B_a} Φ_{r²}(x, ·)²)` with the factor `F_a` and the box `B_a` of the
Step 2 sum of the proof of Lemma 3.3 of Dario (`stepTwoFactor`, `stepTwoBox`) and `v` the potential
of the Green projection of the heat field of the edges (`ae_fluxFlip_sq_le_weight`). Summing over the
bonds (`ae_fluxFlipSum_le`):

`Σ_e (D_e X)² ≤ K₀ (Σ_u W(u) E_v(u) + Σ_y W(y) Φ_{r²}(x, y)²)`

with the weight `W = stepTwoWeight` of the slope `e_k`. This is the bound of Gu's Steps 3 and 4 in the
form of the bound (4) of the Step 2 sum of Dario's Lemma 3.3 in this repository.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Corrector
  Rigidity.External Rigidity.Poincare
open scoped Classical ENNReal

/-- The arithmetic of the bound for a bond closed in the configuration, with the heat term. -/
theorem closed_flux_weight_arith {R g SG b e SE φ SΦ : ℝ} (hR : 1 ≤ R) (hg : 0 ≤ g)
    (hgS : g ≤ SG) (hb : 0 ≤ b) (hbR : b ≤ 9 * R ^ 2) (he : 0 ≤ e) (heS : e ≤ SE) (hφ : 0 ≤ φ)
    (hφS : φ ≤ SΦ) :
    2 ^ 15 * g ^ 2 * b * (e + φ) ≤ (2 * 1297 ^ 4 * 46656) * (R ^ 14 * SG ^ 2) * (SE + SΦ) := by
  have hg2 : g ^ 2 ≤ SG ^ 2 := pow_le_pow_left₀ hg hgS 2
  have hk : 2 ^ 15 * (9 * R ^ 2) ≤ (2 * 1297 ^ 4 * 46656) * R ^ 14 := by
    have h12 : (1 : ℝ) ≤ R ^ 12 := one_le_pow₀ hR
    have e : R ^ 14 = R ^ 12 * R ^ 2 := by ring
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg _
    rw [e]
    calc (2 : ℝ) ^ 15 * (9 * R ^ 2) = 294912 * R ^ 2 := by ring
      _ ≤ (2 * 1297 ^ 4 * 46656) * (1 * R ^ 2) := by nlinarith
      _ ≤ (2 * 1297 ^ 4 * 46656) * (R ^ 12 * R ^ 2) := by gcongr
  have hS : e + φ ≤ SE + SΦ := add_le_add heS hφS
  have hS0 : 0 ≤ e + φ := add_nonneg he hφ
  calc 2 ^ 15 * g ^ 2 * b * (e + φ) ≤ 2 ^ 15 * SG ^ 2 * (9 * R ^ 2) * (SE + SΦ) := by gcongr
    _ = (2 ^ 15 * (9 * R ^ 2)) * (SG ^ 2 * (SE + SΦ)) := by ring
    _ ≤ ((2 * 1297 ^ 4 * 46656) * R ^ 14) * (SG ^ 2 * (SE + SΦ)) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg (sq_nonneg _) (hS0.trans hS))
    _ = _ := by ring

section Weight

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **One flip, with the weight**: `(D_e X)² ≤ K₀ F_a (Σ_{B_a} E_v + Σ_{B_a} Φ²)`. -/
theorem ae_fluxFlip_sq_le_weight {C₀ C : ℕ} (hC₀ : 2 ≤ C₀)
    (hres : ResamplePartitionBound C₀ C) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (k i : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (a : LatticeEdge), PlanarPartitionEvent ω →
      bondFlipDiff (fluxObs hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
        (2 * 1297 ^ 4 * 46656) * stepTwoFactor hG hGv (C₀ + 5 * C + 6) k ω a *
          (∑ u ∈ stepTwoBox (C₀ + 5 * C + 6) ω a,
              openEnergy ω (clusterPot ω (heatEdge ω r x i)) u +
            ∑ y ∈ stepTwoBox (C₀ + 5 * C + 6) ω a, latticeHeat (r ^ 2) x y ^ 2) := by
  filter_upwards [ae_fluxFlip_sq_le_closed hG hGv hpc hp1 hGae,
    ae_fluxFlip_sq_le_open hG hGv hC₀ hres hpc hp1 hGae] with ω hcl hop k i r hr x a hP
  obtain ⟨m, hm⟩ : ∃ m, m = max (planarSide ω a.1) (planarSide ω (edgeHead a)) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    have : 1 ≤ planarSide ω a.1 := by
      rw [planarSide_eq hP]; exact Nat.one_le_pow _ _ (by norm_num)
    omega
  have hRad : stepTwoRadius (C₀ + 5 * C + 6) ω a = (C₀ + 5 * C + 6) * m := by
    rw [hm]; rfl
  have hR1 : 1 ≤ (C₀ + 5 * C + 6) * m := by nlinarith
  have hRr1 : (1 : ℝ) ≤ (((C₀ + 5 * C + 6) * m : ℕ) : ℝ) := by exact_mod_cast hR1
  have hB : stepTwoBox (C₀ + 5 * C + 6) ω a = supBox a.1 ((C₀ + 5 * C + 6) * m) := by
    unfold stepTwoBox; rw [hRad]
  have hF : stepTwoFactor hG hGv (C₀ + 5 * C + 6) k ω a =
      (((C₀ + 5 * C + 6) * m : ℕ) : ℝ) ^ 14 *
        (∑ z ∈ supBox a.1 ((C₀ + 5 * C + 6) * m), planeGrad hG hGv k ω z) ^ 2 := by
    unfold stepTwoFactor; rw [hRad, hB]
  rw [hF, hB]
  have hsub : ∀ {r' : ℕ}, r' ≤ (C₀ + 5 * C + 6) * m →
      supBox a.1 r' ⊆ supBox a.1 ((C₀ + 5 * C + 6) * m) := fun h => supBox_mono h
  have hGs : ∀ {r' : ℕ}, r' ≤ (C₀ + 5 * C + 6) * m →
      ∑ z ∈ supBox a.1 r', planeGrad hG hGv k ω z ≤
        ∑ z ∈ supBox a.1 ((C₀ + 5 * C + 6) * m), planeGrad hG hGv k ω z :=
    fun h => Finset.sum_le_sum_of_subset_of_nonneg (hsub h)
      fun z _ _ => planeGrad_nonneg hG hGv k ω z
  have hEs : ∀ {r' : ℕ}, r' ≤ (C₀ + 5 * C + 6) * m →
      ∑ u ∈ supBox a.1 r', openEnergy ω (clusterPot ω (heatEdge ω r x i)) u ≤
        ∑ u ∈ supBox a.1 ((C₀ + 5 * C + 6) * m),
          openEnergy ω (clusterPot ω (heatEdge ω r x i)) u :=
    fun h => Finset.sum_le_sum_of_subset_of_nonneg (hsub h) fun u _ _ => openEnergy_nonneg _ _ u
  have hxB : a.1 ∈ supBox a.1 ((C₀ + 5 * C + 6) * m) := by
    rw [mem_supBox]
    intro k
    rw [sub_self, abs_zero]
    positivity
  have hΦx : latticeHeat (r ^ 2) x a.1 ^ 2 ≤
      ∑ y ∈ supBox a.1 ((C₀ + 5 * C + 6) * m), latticeHeat (r ^ 2) x y ^ 2 :=
    Finset.single_le_sum (f := fun y => latticeHeat (r ^ 2) x y ^ 2) (fun _ _ => sq_nonneg _) hxB
  by_cases haopen : EdgeOpen ω a
  · -- the bond is open
    have h := hop k i r hr x a haopen hP
    have hsm : planarSide ω a.1 ≤ m := by rw [hm]; exact le_max_left _ _
    have hcs : C * planarSide ω a.1 ≤ (C₀ + 5 * C + 6) * m :=
      Nat.mul_le_mul (by omega) hsm
    have hcs' : (C : ℝ) * (planarSide ω a.1 : ℝ) ≤ (((C₀ + 5 * C + 6) * m : ℕ) : ℝ) := by
      exact_mod_cast hcs
    have hR9 : (1 : ℝ) ≤ 9 * ((((C₀ + 5 * C + 6) * m : ℕ) : ℝ)) ^ 2 := by nlinarith
    have key := open_weight_arith hRr1 (Nat.cast_nonneg C) (Nat.cast_nonneg (planarSide ω a.1))
      hcs' (planeGrad_nonneg hG hGv k ω a.1)
      (Finset.single_le_sum (f := fun z => planeGrad hG hGv k ω z)
        (fun z _ => planeGrad_nonneg hG hGv k ω z) hxB)
      (openEnergy_nonneg _ _ _)
      (Finset.single_le_sum
        (f := fun u => openEnergy ω (clusterPot ω (heatEdge ω r x i)) u)
        (fun u _ => openEnergy_nonneg _ _ u) hxB)
      zero_le_one hR9 (by norm_num : (0 : ℝ) ≤ 1 / 8) (by linarith) (sq_nonneg _) hΦx
    refine h.trans (le_of_eq_of_le ?_ key)
    ring
  · -- the bond is closed
    have h := hcl k i r hr x a haopen hP
    rw [← hm] at h
    have hr0 : 1 + 5 * m ≤ (C₀ + 5 * C + 6) * m := by
      have h3 : (C₀ + 5 * C + 6) * m = C₀ * m + 5 * (C * m) + 6 * m := by ring
      omega
    have hΦx' : latticeHeat (r ^ 2) x a.1 ^ 2 ≤
        ∑ y ∈ supBox a.1 ((C₀ + 5 * C + 6) * m), latticeHeat (r ^ 2) x y ^ 2 := hΦx
    refine h.trans ?_
    exact closed_flux_weight_arith hRr1
      (Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv k ω z) (hGs hr0)
      (Nat.cast_nonneg _) (card_supBox_le hr0 hR1)
      (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u) (hEs hr0) (sq_nonneg _) hΦx'

/-- `Σ_e (D_e X)²` for the heat average of the flux. -/
noncomputable def fluxFlipSum (k i : Fin 2) (r : ℝ) (x : Vertex 2) (ω : Configuration 2) :
    ℝ≥0∞ :=
  ∑' e : Bond 2, ENNReal.ofReal (bondFlipDiff (fluxObs hG hGv k i r x) e ω ^ 2)

/-- **The sum of the squared flip differences bounded by a weighted energy.** -/
theorem ae_fluxFlipSum_le {C₀ C : ℕ} (hC₀ : 2 ≤ C₀) (hres : ResamplePartitionBound C₀ C)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (k i : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2),
      PlanarPartitionEvent ω →
      fluxFlipSum hG hGv k i r x ω ≤ ENNReal.ofReal (2 * 1297 ^ 4 * 46656) *
        (∑' u, stepTwoWeight hG hGv (C₀ + 5 * C + 6) k ω u *
            ENNReal.ofReal (openEnergy ω (clusterPot ω (heatEdge ω r x i)) u) +
          ∑' y, stepTwoWeight hG hGv (C₀ + 5 * C + 6) k ω y *
            ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by
  filter_upwards [ae_fluxFlip_sq_le_weight hG hGv hC₀ hres hpc hp1 hGae] with ω hw k i r hr x hP
  set κ := C₀ + 5 * C + 6
  set K₀ : ℝ := 2 * 1297 ^ 4 * 46656 with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hbond : ∀ a : LatticeEdge,
      ENNReal.ofReal (bondFlipDiff (fluxObs hG hGv k i r x) (edgeBond a) ω ^ 2) ≤
      ENNReal.ofReal K₀ *
        ((∑' u, (if u ∈ stepTwoBox κ ω a then
            ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) else 0) *
              ENNReal.ofReal (openEnergy ω (clusterPot ω (heatEdge ω r x i)) u)) +
          ∑' y, (if y ∈ stepTwoBox κ ω a then
            ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) else 0) *
              ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by
    intro a
    refine (ENNReal.ofReal_le_ofReal (hw k i r hr x a hP)).trans (le_of_eq ?_)
    have hF0 := stepTwoFactor_nonneg hG hGv κ k ω a
    have hE0 : ∀ u ∈ stepTwoBox κ ω a,
        0 ≤ openEnergy ω (clusterPot ω (heatEdge ω r x i)) u :=
      fun u _ => openEnergy_nonneg _ _ u
    have hΦ0 : ∀ y ∈ stepTwoBox κ ω a, 0 ≤ latticeHeat (r ^ 2) x y ^ 2 := fun y _ => sq_nonneg _
    have hite : ∀ (g : Vertex 2 → ℝ≥0∞),
        ∑' u, (if u ∈ stepTwoBox κ ω a then
          ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) else 0) * g u =
        ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) * ∑ u ∈ stepTwoBox κ ω a, g u := by
      intro g
      rw [Finset.mul_sum, ← tsum_ite_mem]
      refine tsum_congr fun u => ?_
      split_ifs <;> simp
    rw [hite, hite, ← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hK₀0,
      ← ENNReal.ofReal_sum_of_nonneg hE0, ← ENNReal.ofReal_sum_of_nonneg hΦ0,
      ← ENNReal.ofReal_add (Finset.sum_nonneg hE0) (Finset.sum_nonneg hΦ0),
      ← ENNReal.ofReal_mul (mul_nonneg hK₀0 hF0)]
  unfold fluxFlipSum
  rw [tsum_bond_eq_tsum_edge]
  refine (ENNReal.tsum_le_tsum hbond).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_comm,
    ENNReal.tsum_comm (f := fun a y => (if y ∈ stepTwoBox κ ω a then
      ENNReal.ofReal (stepTwoFactor hG hGv κ k ω a) else 0) *
        ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2))]
  unfold stepTwoWeight
  simp only [ENNReal.tsum_mul_right]

end Weight

end Rigidity.Green

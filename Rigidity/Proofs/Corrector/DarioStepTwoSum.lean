import Rigidity.Proofs.Corrector.DarioStepTwoOpenBound

/-!
# The Step 2 sum bounded by a weighted energy

For an oriented edge `a = (x, i')` with endpoints `x, y`, let `m_a = max(s(x), s(y))` be the larger
side of the partition cubes of `ω` at its endpoints, `R_a = κ m_a`, `B_a = B(x, R_a)` and

`F_a = R_a¹⁴ (Σ_{z ∈ B_a} G(z))²`,   `W(u) = Σ_a 1{u ∈ B_a} F_a`

(`stepTwoRadius`, `stepTwoBox`, `stepTwoFactor`, `stepTwoWeight`), with `G` the gradient bound of
the corrected plane (`planeGrad`) and `κ = C₀ + 5 C + 6` for Lemma 3.5 in the form
`ResamplePartitionBound C₀ C`. The bounds for the bonds closed and open in `ω`
(`ae_flipTermTwo_sq_le_closed`, `ae_flipTermTwo_sq_le_open`) give
`T₂(e)² ≤ K₀ F_a (Σ_{u ∈ B_a} E_v(u) + Σ_{y ∈ B_a} Φ_{r²}(x, y)²)`
(`ae_flipTermTwo_sq_le_weight`), and summing over the bonds (`ae_flipSumTwo_le`):

`Σ_e T₂(e)² ≤ K₀ (Σ_u W(u) E_v(u) + Σ_y W(y) Φ_{r²}(x, y)²)`,

with `v` the potential of `P_ω γ_ω` on the infinite cluster, `γ_ω` the field of the anchor paths of
the partition of `ω` weighted by the heat kernel. This is (4) of the route through estimate (2),
with the weight written through the corrector of the actual configuration only (by
`ae_dipoleCoeff_eq`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare
open scoped Classical ENNReal InnerProductSpace

/-- The radius `κ max(s(x), s(y))` attached to the oriented edge `a`. -/
noncomputable def stepTwoRadius (κ : ℕ) (ω : Configuration 2) (a : LatticeEdge) : ℕ :=
  κ * max (planarSide ω a.1) (planarSide ω (edgeHead a))

/-- The box `B(x, κ max(s(x), s(y)))` attached to the oriented edge `a`. -/
noncomputable def stepTwoBox (κ : ℕ) (ω : Configuration 2) (a : LatticeEdge) : Finset (Vertex 2) :=
  supBox a.1 (stepTwoRadius κ ω a)

theorem card_supBox_le {x : Vertex 2} {r R : ℕ} (hr : r ≤ R) (hR : 1 ≤ R) :
    ((supBox x r).card : ℝ) ≤ 9 * (R : ℝ) ^ 2 := by
  rw [card_supBox]
  have h1 : (r : ℝ) ≤ R := by exact_mod_cast hr
  have h2 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  push_cast
  have h3 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith

theorem tsum_ite_mem (S : Finset (Vertex 2)) (g : Vertex 2 → ℝ≥0∞) :
    ∑' u, (if u ∈ S then g u else 0) = ∑ u ∈ S, g u := by
  rw [tsum_eq_sum (s := S) fun u hu => if_neg hu]
  exact Finset.sum_congr rfl fun u hu => if_pos hu

/-- The sum over the bonds as a sum over the oriented edges. -/
theorem tsum_bond_eq_tsum_edge (f : Bond 2 → ℝ≥0∞) :
    ∑' e, f e = ∑' a : LatticeEdge, f (edgeBond a) :=
  ((Equiv.ofBijective edgeBond ⟨edgeBond_injective, exists_edgeBond_eq⟩).tsum_eq f).symm

section Weight

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The factor `F_a = R_a¹⁴ (Σ_{z ∈ B_a} G(z))²`. -/
noncomputable def stepTwoFactor (κ : ℕ) (i : Fin 2) (ω : Configuration 2) (a : LatticeEdge) : ℝ :=
  (stepTwoRadius κ ω a : ℝ) ^ 14 * (∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z) ^ 2

/-- The weight `W(u) = Σ_a 1{u ∈ B_a} F_a`. -/
noncomputable def stepTwoWeight (κ : ℕ) (i : Fin 2) (ω : Configuration 2) (u : Vertex 2) : ℝ≥0∞ :=
  ∑' a : LatticeEdge, if u ∈ stepTwoBox κ ω a then
    ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) else 0

theorem stepTwoFactor_nonneg (κ : ℕ) (i : Fin 2) (ω : Configuration 2) (a : LatticeEdge) :
    0 ≤ stepTwoFactor hG hGv κ i ω a := by
  unfold stepTwoFactor
  positivity

/-- The arithmetic of the bound for a bond open in the configuration. -/
theorem open_weight_arith {R c s g SG e SE b₁ b₂ φ SΦ : ℝ} (hR : 1 ≤ R) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hcs : c * s ≤ R) (hg : 0 ≤ g) (hgS : g ≤ SG) (he : 0 ≤ e) (heS : e ≤ SE) (hb₁ : 0 ≤ b₁)
    (hb₁R : b₁ ≤ 9 * R ^ 2) (hb₂ : 0 ≤ b₂) (hb₂R : b₂ ≤ 9 * R ^ 2) (hφ : 0 ≤ φ)
    (hφS : φ ≤ SΦ) :
    2 * (1 + (1296 * c ^ 2 * s ^ 2) ^ 2) ^ 2 * g ^ 2 * (e + b₁ * φ * (8 * b₂) ^ 2) ≤
      (2 * 1297 ^ 4 * 46656) * (R ^ 14 * SG ^ 2) * (SE + SΦ) := by
  have hcs0 : 0 ≤ c * s := mul_nonneg hc hs
  have hSΦ : 0 ≤ SΦ := hφ.trans hφS
  have hSE : 0 ≤ SE := he.trans heS
  have hK : (1 + (1296 * c ^ 2 * s ^ 2) ^ 2) ^ 2 ≤ 1297 ^ 4 * R ^ 8 := by
    have e1 : 1296 * c ^ 2 * s ^ 2 = 1296 * (c * s) ^ 2 := by ring
    have h1 : (c * s) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hcs0 hcs 2
    have h2 : (1 : ℝ) ≤ R ^ 4 := one_le_pow₀ hR
    have h4 : (1296 * (c * s) ^ 2) ^ 2 ≤ (1296 * R ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : 1 + (1296 * c ^ 2 * s ^ 2) ^ 2 ≤ 1297 ^ 2 * R ^ 4 := by
      rw [e1]
      have : (1296 * R ^ 2) ^ 2 = 1296 ^ 2 * R ^ 4 := by ring
      linarith
    calc _ ≤ (1297 ^ 2 * R ^ 4) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      _ = 1297 ^ 4 * R ^ 8 := by ring
  have hg2 : g ^ 2 ≤ SG ^ 2 := pow_le_pow_left₀ hg hgS 2
  have hX : e + b₁ * φ * (8 * b₂) ^ 2 ≤ 46656 * R ^ 6 * (SE + SΦ) := by
    have h1 : b₁ * φ ≤ 9 * R ^ 2 * SΦ := mul_le_mul hb₁R hφS hφ (by positivity)
    have h2 : (8 * b₂) ^ 2 ≤ (72 * R ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : b₁ * φ * (8 * b₂) ^ 2 ≤ 9 * R ^ 2 * SΦ * (72 * R ^ 2) ^ 2 :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    have h6 : (1 : ℝ) ≤ R ^ 6 := one_le_pow₀ hR
    have e2 : 9 * R ^ 2 * SΦ * (72 * R ^ 2) ^ 2 = 46656 * R ^ 6 * SΦ := by ring
    have h7 : SE ≤ 46656 * R ^ 6 * SE := by nlinarith
    nlinarith
  have hX0 : 0 ≤ e + b₁ * φ * (8 * b₂) ^ 2 := by positivity
  calc 2 * (1 + (1296 * c ^ 2 * s ^ 2) ^ 2) ^ 2 * g ^ 2 * (e + b₁ * φ * (8 * b₂) ^ 2)
      ≤ 2 * (1297 ^ 4 * R ^ 8) * SG ^ 2 * (46656 * R ^ 6 * (SE + SΦ)) := by gcongr
    _ = (2 * 1297 ^ 4 * 46656) * (R ^ 14 * SG ^ 2) * (SE + SΦ) := by ring

/-- The arithmetic of the bound for a bond closed in the configuration. -/
theorem closed_weight_arith {R g SG b e SE SΦ : ℝ} (hR : 1 ≤ R) (hg : 0 ≤ g) (hgS : g ≤ SG)
    (hb : 0 ≤ b) (hbR : b ≤ 9 * R ^ 2) (he : 0 ≤ e) (heS : e ≤ SE) (hΦ : 0 ≤ SΦ) :
    2 ^ 14 * g ^ 2 * b * e ≤ (2 * 1297 ^ 4 * 46656) * (R ^ 14 * SG ^ 2) * (SE + SΦ) := by
  have hSE : 0 ≤ SE := he.trans heS
  have hg2 : g ^ 2 ≤ SG ^ 2 := pow_le_pow_left₀ hg hgS 2
  have hk : 2 ^ 14 * (9 * R ^ 2) ≤ (2 * 1297 ^ 4 * 46656) * R ^ 14 := by
    have h12 : (1 : ℝ) ≤ R ^ 12 := one_le_pow₀ hR
    have e : R ^ 14 = R ^ 12 * R ^ 2 := by ring
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg _
    rw [e]
    calc (2 : ℝ) ^ 14 * (9 * R ^ 2) = 147456 * R ^ 2 := by ring
      _ ≤ (2 * 1297 ^ 4 * 46656) * (1 * R ^ 2) := by nlinarith
      _ ≤ (2 * 1297 ^ 4 * 46656) * (R ^ 12 * R ^ 2) := by gcongr
  calc 2 ^ 14 * g ^ 2 * b * e ≤ 2 ^ 14 * SG ^ 2 * (9 * R ^ 2) * SE := by gcongr
    _ = (2 ^ 14 * (9 * R ^ 2)) * (SG ^ 2 * SE) := by ring
    _ ≤ ((2 * 1297 ^ 4 * 46656) * R ^ 14) * (SG ^ 2 * SE) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg (sq_nonneg _) hSE)
    _ ≤ ((2 * 1297 ^ 4 * 46656) * R ^ 14) * (SG ^ 2 * (SE + SΦ)) := by gcongr; linarith
    _ = _ := by ring

/-- **Step 2 for one bond, with the weight**: `T₂(e)² ≤ K₀ F_a (Σ_{B_a} E_v + Σ_{B_a} Φ²)`. -/
theorem ae_flipTermTwo_sq_le_weight {C₀ C : ℕ} (hC₀ : 2 ≤ C₀)
    (hres : ResamplePartitionBound C₀ C) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i j : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (a : LatticeEdge) (hP : PlanarPartitionEvent ω),
      flipTermTwo hG hGv i j r x (edgeBond a) ω ^ 2 ≤
        (2 * 1297 ^ 4 * 46656) * stepTwoFactor hG hGv (C₀ + 5 * C + 6) i ω a *
          (∑ u ∈ stepTwoBox (C₀ + 5 * C + 6) ω a,
              openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u +
            ∑ y ∈ stepTwoBox (C₀ + 5 * C + 6) ω a, latticeHeat (r ^ 2) x y ^ 2) := by
  filter_upwards [ae_flipTermTwo_sq_le_closed hG hGv hpc hp1 hGae,
    ae_flipTermTwo_sq_le_open hG hGv hC₀ hres hpc hp1 hGae] with ω hcl hop i j r hr x a hP
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
  have hF : stepTwoFactor hG hGv (C₀ + 5 * C + 6) i ω a =
      (((C₀ + 5 * C + 6) * m : ℕ) : ℝ) ^ 14 *
        (∑ z ∈ supBox a.1 ((C₀ + 5 * C + 6) * m), planeGrad hG hGv i ω z) ^ 2 := by
    unfold stepTwoFactor; rw [hRad, hB]
  rw [hF, hB]
  have hsub : ∀ {r' : ℕ}, r' ≤ (C₀ + 5 * C + 6) * m →
      supBox a.1 r' ⊆ supBox a.1 ((C₀ + 5 * C + 6) * m) := fun h => supBox_mono h
  have hGs : ∀ {r' : ℕ}, r' ≤ (C₀ + 5 * C + 6) * m →
      ∑ z ∈ supBox a.1 r', planeGrad hG hGv i ω z ≤
        ∑ z ∈ supBox a.1 ((C₀ + 5 * C + 6) * m), planeGrad hG hGv i ω z :=
    fun h => Finset.sum_le_sum_of_subset_of_nonneg (hsub h)
      fun z _ _ => planeGrad_nonneg hG hGv i ω z
  have hEs : ∀ {r' : ℕ}, r' ≤ (C₀ + 5 * C + 6) * m →
      ∑ u ∈ supBox a.1 r', openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u ≤
        ∑ u ∈ supBox a.1 ((C₀ + 5 * C + 6) * m),
          openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
    fun h => Finset.sum_le_sum_of_subset_of_nonneg (hsub h) fun u _ _ => openEnergy_nonneg _ _ u
  have hΦs : ∀ {r' : ℕ}, r' ≤ (C₀ + 5 * C + 6) * m →
      ∑ y ∈ supBox a.1 r', latticeHeat (r ^ 2) x y ^ 2 ≤
        ∑ y ∈ supBox a.1 ((C₀ + 5 * C + 6) * m), latticeHeat (r ^ 2) x y ^ 2 :=
    fun h => Finset.sum_le_sum_of_subset_of_nonneg (hsub h) fun y _ _ => sq_nonneg _
  have hΦ0 : 0 ≤ ∑ y ∈ supBox a.1 ((C₀ + 5 * C + 6) * m), latticeHeat (r ^ 2) x y ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hxB : a.1 ∈ supBox a.1 ((C₀ + 5 * C + 6) * m) := by
    rw [mem_supBox]
    intro k
    rw [sub_self, abs_zero]
    positivity
  by_cases haopen : EdgeOpen ω a
  · -- the bond is open
    have h := hop i j r hr x a haopen hP
    have hsm : planarSide ω a.1 ≤ m := by rw [hm]; exact le_max_left _ _
    have hr1 : C₀ * planarSide ω a.1 ≤ (C₀ + 5 * C + 6) * m := Nat.mul_le_mul (by omega) hsm
    have hr2 : (C₀ * planarSide ω a.1 + 1) + 5 * (C * planarSide ω a.1) ≤
        (C₀ + 5 * C + 6) * m := by
      have h1 : C₀ * planarSide ω a.1 ≤ C₀ * m := Nat.mul_le_mul_left _ hsm
      have h2 : C * planarSide ω a.1 ≤ C * m := Nat.mul_le_mul_left _ hsm
      have h3 : (C₀ + 5 * C + 6) * m = C₀ * m + 5 * (C * m) + 6 * m := by ring
      omega
    have hcs : C * planarSide ω a.1 ≤ (C₀ + 5 * C + 6) * m :=
      Nat.mul_le_mul (by omega) hsm
    have hcs' : (C : ℝ) * (planarSide ω a.1 : ℝ) ≤ (((C₀ + 5 * C + 6) * m : ℕ) : ℝ) := by
      exact_mod_cast hcs
    refine h.trans ?_
    exact open_weight_arith hRr1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcs'
      (planeGrad_nonneg hG hGv i ω a.1)
      (Finset.single_le_sum (f := fun z => planeGrad hG hGv i ω z)
        (fun z _ => planeGrad_nonneg hG hGv i ω z) hxB)
      (openEnergy_nonneg _ _ _)
      (Finset.single_le_sum
        (f := fun u => openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u)
        (fun u _ => openEnergy_nonneg _ _ u) hxB)
      (Nat.cast_nonneg _) (card_supBox_le hr1 hR1) (Nat.cast_nonneg _) (card_supBox_le hr2 hR1)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hΦs hr1)
  · -- the bond is closed
    have h := hcl i j r hr x a haopen hP
    rw [← hm] at h
    have hr0 : 1 + 5 * m ≤ (C₀ + 5 * C + 6) * m := by
      have h3 : (C₀ + 5 * C + 6) * m = C₀ * m + 5 * (C * m) + 6 * m := by ring
      omega
    refine h.trans ?_
    exact closed_weight_arith hRr1
      (Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv i ω z) (hGs hr0)
      (Nat.cast_nonneg _) (card_supBox_le hr0 hR1)
      (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u) (hEs hr0) hΦ0

/-- **The Step 2 sum bounded by a weighted energy** (the bound (4)). -/
theorem ae_flipSumTwo_le {C₀ C : ℕ} (hC₀ : 2 ≤ C₀) (hres : ResamplePartitionBound C₀ C)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i j : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (hP : PlanarPartitionEvent ω),
      flipSumTwo hG hGv i j r x ω ≤ ENNReal.ofReal (2 * 1297 ^ 4 * 46656) *
        (∑' u, stepTwoWeight hG hGv (C₀ + 5 * C + 6) i ω u *
            ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) +
          ∑' y, stepTwoWeight hG hGv (C₀ + 5 * C + 6) i ω y *
            ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by
  filter_upwards [ae_flipTermTwo_sq_le_weight hG hGv hC₀ hres hpc hp1 hGae] with
    ω hw i j r hr x hP
  set κ := C₀ + 5 * C + 6
  set K₀ : ℝ := 2 * 1297 ^ 4 * 46656 with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hbond : ∀ a : LatticeEdge, ENNReal.ofReal (flipTermTwo hG hGv i j r x (edgeBond a) ω ^ 2) ≤
      ENNReal.ofReal K₀ *
        ((∑' u, (if u ∈ stepTwoBox κ ω a then
            ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) else 0) *
              ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u)) +
          ∑' y, (if y ∈ stepTwoBox κ ω a then
            ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) else 0) *
              ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by
    intro a
    refine (ENNReal.ofReal_le_ofReal (hw i j r hr x a hP)).trans (le_of_eq ?_)
    have hF0 := stepTwoFactor_nonneg hG hGv κ i ω a
    have hE0 : ∀ u ∈ stepTwoBox κ ω a,
        0 ≤ openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
      fun u _ => openEnergy_nonneg _ _ u
    have hΦ0 : ∀ y ∈ stepTwoBox κ ω a, 0 ≤ latticeHeat (r ^ 2) x y ^ 2 := fun y _ => sq_nonneg _
    have hite : ∀ (g : Vertex 2 → ℝ≥0∞),
        ∑' u, (if u ∈ stepTwoBox κ ω a then
          ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) else 0) * g u =
        ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) * ∑ u ∈ stepTwoBox κ ω a, g u := by
      intro g
      rw [Finset.mul_sum, ← tsum_ite_mem]
      refine tsum_congr fun u => ?_
      split_ifs <;> simp
    rw [hite, hite, ← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hK₀0,
      ← ENNReal.ofReal_sum_of_nonneg hE0, ← ENNReal.ofReal_sum_of_nonneg hΦ0,
      ← ENNReal.ofReal_add (Finset.sum_nonneg hE0) (Finset.sum_nonneg hΦ0),
      ← ENNReal.ofReal_mul (mul_nonneg hK₀0 hF0)]
  unfold flipSumTwo
  rw [tsum_bond_eq_tsum_edge]
  refine (ENNReal.tsum_le_tsum hbond).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_comm,
    ENNReal.tsum_comm (f := fun a y => (if y ∈ stepTwoBox κ ω a then
      ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) else 0) *
        ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2))]
  unfold stepTwoWeight
  simp only [ENNReal.tsum_mul_right]

end Weight

end Rigidity.Corrector

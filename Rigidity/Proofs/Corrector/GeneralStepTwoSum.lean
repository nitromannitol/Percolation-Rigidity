import Rigidity.Proofs.Corrector.GeneralStepTwoClosedBound

/-!
# The Step 2 sum of Lemma 3.3 of Dario on `ℤᵈ` bounded by a weighted energy

For an oriented edge `a = (x, i')` with endpoints `x, y`, let `m_a = max(s(x), s(y))` be the larger
side of the partition cubes of `ω` at its endpoints, `R_a = κ m_a`, `B_a = B(x, R_a)` and

`F_a = R_a^{7d} (Σ_{z ∈ B_a} G(z))²`,   `W(u) = Σ_a 1{u ∈ B_a} F_a`

(`stepTwoRadius`, `stepTwoBox`, `stepTwoFactor`, `stepTwoWeight`), with `G` the gradient bound of
the corrected plane (`planeGrad`) and `κ = C₀ + 3 C + 6` for Lemma 3.5 in the form
`ResamplePartitionBound C₀ C`. The bounds for the bonds closed and open in `ω`
(`ae_flipTermTwo_sq_le_closed`, `ae_flipTermTwo_sq_le_open`) give
`T₂(e)² ≤ K₀ F_a (Σ_{u ∈ B_a} E_v(u) + Σ_{y ∈ B_a} Φ_{r²}(x, y)²)` with `K₀ = stepTwoConst d`
(`ae_flipTermTwo_sq_le_weight`), and summing over the bonds (`ae_flipSumTwo_le`):

`Σ_e T₂(e)² ≤ K₀ (Σ_u W(u) E_v(u) + Σ_y W(y) Φ_{r²}(x, y)²)`,

with `v` the potential of `P_ω γ_ω` on the infinite cluster, `γ_ω` the field of the anchor paths of
the partition of `ω` weighted by the heat kernel. This is the bound (4) of the planar file
`DarioStepTwoSum` on `ℤᵈ`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal InnerProductSpace

variable {d : ℕ}

/-- The constant `32 d² 27^d (1 + (8 d 7^d)²)²` of the bound of the Step 2 sum. -/
noncomputable def stepTwoConst (d : ℕ) : ℝ :=
  32 * (d : ℝ) ^ 2 * 27 ^ d * (1 + (8 * d * 7 ^ d) ^ 2) ^ 2

theorem stepTwoConst_nonneg (d : ℕ) : 0 ≤ stepTwoConst d := by
  unfold stepTwoConst
  positivity

theorem tsum_ite_mem (S : Finset (Vertex d)) (g : Vertex d → ℝ≥0∞) :
    ∑' u, (if u ∈ S then g u else 0) = ∑ u ∈ S, g u := by
  rw [tsum_eq_sum (s := S) fun u hu => if_neg hu]
  exact Finset.sum_congr rfl fun u hu => if_pos hu

/-- The sum over the bonds as a sum over the oriented edges. -/
theorem tsum_bond_eq_tsum_edge (f : Bond d → ℝ≥0∞) :
    ∑' e, f e = ∑' a : LatticeEdge d, f (edgeBond a) :=
  ((Equiv.ofBijective edgeBond ⟨edgeBond_injective, exists_edgeBond_eq⟩).tsum_eq f).symm

/-- The arithmetic of the bound for a bond open in the configuration. -/
theorem open_weight_arith (hd : 1 ≤ d) {R c s g SG e SE b₁ b₂ φ SΦ : ℝ} (hR : 1 ≤ R)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c * s ≤ R) (hg : 0 ≤ g) (hgS : g ≤ SG) (he : 0 ≤ e)
    (heS : e ≤ SE) (hb₁ : 0 ≤ b₁) (hb₁R : b₁ ≤ 3 ^ d * R ^ d) (hb₂ : 0 ≤ b₂)
    (hb₂R : b₂ ≤ 3 ^ d * R ^ d) (hφ : 0 ≤ φ) (hφS : φ ≤ SΦ) :
    2 * (1 + (8 * d * 7 ^ d * c ^ d * s ^ d) ^ 2) ^ 2 * g ^ 2 *
        (e + b₁ * φ * (4 * d * b₂) ^ 2) ≤
      stepTwoConst d * (R ^ (7 * d) * SG ^ 2) * (SE + SΦ) := by
  set A : ℝ := 8 * d * 7 ^ d with hA
  set Q : ℝ := R ^ d with hQ
  have hA0 : 0 ≤ A := by positivity
  have hQ1 : 1 ≤ Q := one_le_pow₀ hR
  have hQ0 : 0 ≤ Q := by linarith
  have hSΦ : 0 ≤ SΦ := hφ.trans hφS
  have hSE : 0 ≤ SE := he.trans heS
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcs0 : 0 ≤ c * s := mul_nonneg hc hs
  have e1 : 8 * d * 7 ^ d * c ^ d * s ^ d = A * (c * s) ^ d := by rw [hA, mul_pow]; ring
  have hcsQ : (c * s) ^ d ≤ Q := pow_le_pow_left₀ hcs0 hcs d
  -- `(1 + (A (cs)^d)²)² ≤ (1 + A²)² Q⁴`
  have hK : (1 + (8 * d * 7 ^ d * c ^ d * s ^ d) ^ 2) ^ 2 ≤ (1 + A ^ 2) ^ 2 * Q ^ 4 := by
    rw [e1]
    have h1 : (A * (c * s) ^ d) ^ 2 ≤ A ^ 2 * Q ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcsQ 2) (sq_nonneg A)
    have hQ2 : (1 : ℝ) ≤ Q ^ 2 := one_le_pow₀ hQ1
    have h2 : 1 + (A * (c * s) ^ d) ^ 2 ≤ (1 + A ^ 2) * Q ^ 2 := by nlinarith [sq_nonneg A]
    calc (1 + (A * (c * s) ^ d) ^ 2) ^ 2 ≤ ((1 + A ^ 2) * Q ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h2 2
      _ = (1 + A ^ 2) ^ 2 * Q ^ 4 := by ring
  -- `e + b₁ φ (4d b₂)² ≤ M Q³ (SE + SΦ)` with `M = 16 d² 27^d`
  set M : ℝ := 16 * (d : ℝ) ^ 2 * 27 ^ d with hM
  have hM1 : 1 ≤ M := by
    have h27 : (1 : ℝ) ≤ 27 ^ d := one_le_pow₀ (by norm_num)
    have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd1
    rw [hM]
    nlinarith
  have hX : e + b₁ * φ * (4 * d * b₂) ^ 2 ≤ M * Q ^ 3 * (SE + SΦ) := by
    have h1 : b₁ * φ ≤ 3 ^ d * Q * SΦ := mul_le_mul hb₁R hφS hφ (by positivity)
    have h2 : (4 * d * b₂) ^ 2 ≤ (4 * d * (3 ^ d * Q)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hb₂R (by positivity)) 2
    have h3 : b₁ * φ * (4 * d * b₂) ^ 2 ≤ 3 ^ d * Q * SΦ * (4 * d * (3 ^ d * Q)) ^ 2 :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    have e2 : 3 ^ d * Q * SΦ * (4 * d * (3 ^ d * Q)) ^ 2 = M * Q ^ 3 * SΦ := by
      have h27 : (27 : ℝ) ^ d = 3 ^ d * (3 ^ d) ^ 2 := by
        rw [← pow_mul, ← pow_add, show (27 : ℝ) = 3 ^ 3 by norm_num, ← pow_mul]
        congr 1
        ring
      rw [hM, h27]
      ring
    have hMQ : 1 ≤ M * Q ^ 3 := by
      have : (1 : ℝ) ≤ Q ^ 3 := one_le_pow₀ hQ1
      nlinarith
    have h7 : SE ≤ M * Q ^ 3 * SE := le_mul_of_one_le_left hSE hMQ
    nlinarith
  have hg2 : g ^ 2 ≤ SG ^ 2 := pow_le_pow_left₀ hg hgS 2
  have hX0 : 0 ≤ e + b₁ * φ * (4 * d * b₂) ^ 2 := by positivity
  have hR7 : R ^ (7 * d) = Q ^ 7 := by rw [hQ, mul_comm, pow_mul]
  have hstep : 2 * (1 + (8 * d * 7 ^ d * c ^ d * s ^ d) ^ 2) ^ 2 * g ^ 2 *
        (e + b₁ * φ * (4 * d * b₂) ^ 2) ≤
      2 * ((1 + A ^ 2) ^ 2 * Q ^ 4) * SG ^ 2 * (M * Q ^ 3 * (SE + SΦ)) := by
    have h1 := mul_le_mul_of_nonneg_left hK (by norm_num : (0 : ℝ) ≤ 2)
    have h2 := mul_le_mul h1 hg2 (sq_nonneg g) (by positivity)
    exact mul_le_mul h2 hX hX0 (by positivity)
  calc _ ≤ 2 * ((1 + A ^ 2) ^ 2 * Q ^ 4) * SG ^ 2 * (M * Q ^ 3 * (SE + SΦ)) := hstep
    _ = stepTwoConst d * (R ^ (7 * d) * SG ^ 2) * (SE + SΦ) := by
        rw [hR7, stepTwoConst, hM, hA]
        ring

/-- The arithmetic of the bound for a bond closed in the configuration. -/
theorem closed_weight_arith (hd : 1 ≤ d) {R g SG b e SE SΦ : ℝ} (hR : 1 ≤ R) (hg : 0 ≤ g)
    (hgS : g ≤ SG) (hb : 0 ≤ b) (hbR : b ≤ 3 ^ d * R ^ d) (he : 0 ≤ e) (heS : e ≤ SE)
    (hΦ : 0 ≤ SΦ) :
    2048 * (d : ℝ) ^ 3 * g ^ 2 * b * e ≤ stepTwoConst d * (R ^ (7 * d) * SG ^ 2) * (SE + SΦ) := by
  set Q : ℝ := R ^ d with hQ
  have hQ1 : 1 ≤ Q := one_le_pow₀ hR
  have hSE : 0 ≤ SE := he.trans heS
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hg2 : g ^ 2 ≤ SG ^ 2 := pow_le_pow_left₀ hg hgS 2
  have hR7 : R ^ (7 * d) = Q ^ 7 := by rw [hQ, mul_comm, pow_mul]
  -- `2048 d³ 3^d ≤ stepTwoConst d`
  have hconst : 2048 * (d : ℝ) ^ 3 * 3 ^ d ≤ stepTwoConst d := by
    unfold stepTwoConst
    set A : ℝ := 8 * d * 7 ^ d with hA
    have h7 : (1 : ℝ) ≤ 7 ^ d := one_le_pow₀ (by norm_num)
    have hA8 : 8 * (d : ℝ) ≤ A := by
      rw [hA]
      nlinarith
    have hA2 : 64 * (d : ℝ) ^ 2 ≤ (1 + A ^ 2) ^ 2 := by
      have h1 : (8 * (d : ℝ)) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hA8 2
      have h2 : A ^ 2 ≤ (1 + A ^ 2) ^ 2 := by nlinarith [sq_nonneg A]
      nlinarith
    have h27 : (3 : ℝ) ^ d ≤ 27 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    have h3 : (0 : ℝ) ≤ 3 ^ d := by positivity
    have hdd : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 4 := pow_le_pow_right₀ hd1 (by norm_num)
    calc 2048 * (d : ℝ) ^ 3 * 3 ^ d ≤ 2048 * (d : ℝ) ^ 4 * 27 ^ d := by
          have := mul_le_mul hdd h27 h3 (by positivity)
          nlinarith
      _ = 32 * (d : ℝ) ^ 2 * 27 ^ d * (64 * (d : ℝ) ^ 2) := by ring
      _ ≤ 32 * (d : ℝ) ^ 2 * 27 ^ d * (1 + A ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hA2 (by positivity)
  have hQ7 : Q ≤ Q ^ 7 := le_self_pow₀ hQ1 (by norm_num)
  have hQ0 : 0 ≤ Q := by linarith
  have hSG2 : 0 ≤ SG ^ 2 := sq_nonneg _
  have hP0 : 0 ≤ SG ^ 2 * SE := mul_nonneg hSG2 hSE
  have hc0 := stepTwoConst_nonneg d
  have h3d : (0 : ℝ) ≤ 3 ^ d * Q := mul_nonneg (by positivity) hQ0
  calc 2048 * (d : ℝ) ^ 3 * g ^ 2 * b * e
      ≤ 2048 * (d : ℝ) ^ 3 * (SG ^ 2 * (3 ^ d * Q) * SE) := by
        have h1 : g ^ 2 * b ≤ SG ^ 2 * (3 ^ d * Q) := mul_le_mul hg2 hbR hb hSG2
        have h2 : g ^ 2 * b * e ≤ SG ^ 2 * (3 ^ d * Q) * SE :=
          mul_le_mul h1 heS he (mul_nonneg hSG2 h3d)
        have h3 : (0 : ℝ) ≤ 2048 * (d : ℝ) ^ 3 := by positivity
        calc 2048 * (d : ℝ) ^ 3 * g ^ 2 * b * e = 2048 * (d : ℝ) ^ 3 * (g ^ 2 * b * e) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3
    _ = (2048 * (d : ℝ) ^ 3 * 3 ^ d) * Q * (SG ^ 2 * SE) := by ring
    _ ≤ stepTwoConst d * Q ^ 7 * (SG ^ 2 * SE) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hconst hQ7 hQ0 hc0) hP0
    _ ≤ stepTwoConst d * Q ^ 7 * (SG ^ 2 * (SE + SΦ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hSG2)
          (mul_nonneg hc0 (pow_nonneg hQ0 7))
    _ = stepTwoConst d * (R ^ (7 * d) * SG ^ 2) * (SE + SΦ) := by rw [hR7]; ring

section Weight

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **Step 2 for one bond, with the weight**: `T₂(e)² ≤ K₀ F_a (Σ_{B_a} E_v + Σ_{B_a} Φ²)`. -/
theorem ae_flipTermTwo_sq_le_weight [NeZero d] (hd : 2 ≤ d) {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound (d := d) C₀ C) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (a : LatticeEdge d) (hP : PartitionEvent ω),
      flipTermTwo hG hGv i j r x (edgeBond a) ω ^ 2 ≤
        stepTwoConst d * stepTwoFactor hG hGv (C₀ + 3 * C + 6) i ω a *
          (∑ u ∈ stepTwoBox (C₀ + 3 * C + 6) ω a,
              openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u +
            ∑ y ∈ stepTwoBox (C₀ + 3 * C + 6) ω a, zdHeat d (r ^ 2) x y ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  filter_upwards [ae_flipTermTwo_sq_le_closed hG hGv hd hpc hp1 hGae,
    ae_flipTermTwo_sq_le_open hG hGv hd hC₀ hres hpc hp1 hGae] with ω hcl hop i j r hr x a hP
  obtain ⟨m, hm⟩ : ∃ m, m = max (partSide ω a.1) (partSide ω (edgeHead a)) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    have : 1 ≤ partSide ω a.1 := by
      rw [partSide_eq hP]; exact Nat.one_le_pow _ _ (by norm_num)
    omega
  set κ := C₀ + 3 * C + 6 with hκ
  have hRad : stepTwoRadius κ ω a = κ * m := by
    rw [hm]; rfl
  have hR1 : 1 ≤ κ * m := by nlinarith
  have hRr1 : (1 : ℝ) ≤ ((κ * m : ℕ) : ℝ) := by exact_mod_cast hR1
  have hB : stepTwoBox κ ω a = supBox a.1 (κ * m) := by
    unfold stepTwoBox; rw [hRad]; rfl
  have hF : stepTwoFactor hG hGv κ i ω a =
      ((κ * m : ℕ) : ℝ) ^ (7 * d) * (∑ z ∈ supBox a.1 (κ * m), planeGrad hG hGv i ω z) ^ 2 := by
    unfold stepTwoFactor; rw [hRad, hB]
  rw [hF, hB]
  have hcardle : ∀ {r' : ℕ}, r' ≤ κ * m → ((supBox a.1 r').card : ℝ) ≤ 3 ^ d * ((κ * m : ℕ) : ℝ) ^ d :=
    fun h => card_boxFinset_le_pow h hR1
  have hsub : ∀ {r' : ℕ}, r' ≤ κ * m → supBox a.1 r' ⊆ supBox a.1 (κ * m) :=
    fun h => supBox_subset_of_le a.1 h
  have hGs : ∀ {r' : ℕ}, r' ≤ κ * m →
      ∑ z ∈ supBox a.1 r', planeGrad hG hGv i ω z ≤
        ∑ z ∈ supBox a.1 (κ * m), planeGrad hG hGv i ω z :=
    fun h => Finset.sum_le_sum_of_subset_of_nonneg (hsub h)
      fun z _ _ => planeGrad_nonneg hG hGv i ω z
  have hEs : ∀ {r' : ℕ}, r' ≤ κ * m →
      ∑ u ∈ supBox a.1 r', openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u ≤
        ∑ u ∈ supBox a.1 (κ * m), openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
    fun h => Finset.sum_le_sum_of_subset_of_nonneg (hsub h) fun u _ _ => openEnergy_nonneg _ _ u
  have hΦs : ∀ {r' : ℕ}, r' ≤ κ * m →
      ∑ y ∈ supBox a.1 r', zdHeat d (r ^ 2) x y ^ 2 ≤
        ∑ y ∈ supBox a.1 (κ * m), zdHeat d (r ^ 2) x y ^ 2 :=
    fun h => Finset.sum_le_sum_of_subset_of_nonneg (hsub h) fun y _ _ => sq_nonneg _
  have hΦ0 : 0 ≤ ∑ y ∈ supBox a.1 (κ * m), zdHeat d (r ^ 2) x y ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hxB : a.1 ∈ supBox a.1 (κ * m) := self_mem_supBox a.1 _
  by_cases haopen : EdgeOpen ω a
  · -- the bond is open
    have h := hop i j r hr x a haopen hP
    have hsm : partSide ω a.1 ≤ m := by rw [hm]; exact le_max_left _ _
    have hr1 : C₀ * partSide ω a.1 ≤ κ * m := Nat.mul_le_mul (by omega) hsm
    have hr2 : (C₀ * partSide ω a.1 + 1) + 3 * (C * partSide ω a.1) ≤ κ * m := by
      have h1 : C₀ * partSide ω a.1 ≤ C₀ * m := Nat.mul_le_mul_left _ hsm
      have h2 : C * partSide ω a.1 ≤ C * m := Nat.mul_le_mul_left _ hsm
      have h3 : κ * m = C₀ * m + 3 * (C * m) + 6 * m := by rw [hκ]; ring
      omega
    have hcs : C * partSide ω a.1 ≤ κ * m := Nat.mul_le_mul (by omega) hsm
    have hcs' : (C : ℝ) * (partSide ω a.1 : ℝ) ≤ ((κ * m : ℕ) : ℝ) := by exact_mod_cast hcs
    refine h.trans ?_
    exact open_weight_arith hd1 hRr1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcs'
      (planeGrad_nonneg hG hGv i ω a.1)
      (Finset.single_le_sum (f := fun z => planeGrad hG hGv i ω z)
        (fun z _ => planeGrad_nonneg hG hGv i ω z) hxB)
      (openEnergy_nonneg _ _ _)
      (Finset.single_le_sum
        (f := fun u => openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u)
        (fun u _ => openEnergy_nonneg _ _ u) hxB)
      (Nat.cast_nonneg _) (hcardle hr1) (Nat.cast_nonneg _) (hcardle hr2)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hΦs hr1)
  · -- the bond is closed
    have h := hcl i j r hr x a haopen hP
    rw [← hm] at h
    have hr0 : 1 + 5 * m ≤ κ * m := by
      have h3 : κ * m = C₀ * m + 3 * (C * m) + 6 * m := by rw [hκ]; ring
      omega
    rw [← supBox_eq_boxFinset] at h
    refine h.trans ?_
    exact closed_weight_arith hd1 hRr1
      (Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv i ω z) (hGs hr0)
      (Nat.cast_nonneg _) (hcardle hr0)
      (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u) (hEs hr0) hΦ0

/-- **The Step 2 sum bounded by a weighted energy** (the bound (4)). -/
theorem ae_flipSumTwo_le [NeZero d] (hd : 2 ≤ d) {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound (d := d) C₀ C)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (hP : PartitionEvent ω),
      flipSumTwo hG hGv i j r x ω ≤ ENNReal.ofReal (stepTwoConst d) *
        (∑' u, stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω u *
            ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) +
          ∑' y, stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω y *
            ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2)) := by
  filter_upwards [ae_flipTermTwo_sq_le_weight hG hGv hd hC₀ hres hpc hp1 hGae] with
    ω hw i j r hr x hP
  set κ := C₀ + 3 * C + 6
  set K₀ : ℝ := stepTwoConst d with hK₀
  have hK₀0 : 0 ≤ K₀ := stepTwoConst_nonneg d
  have hbond : ∀ a : LatticeEdge d,
      ENNReal.ofReal (flipTermTwo hG hGv i j r x (edgeBond a) ω ^ 2) ≤
      ENNReal.ofReal K₀ *
        ((∑' u, (if u ∈ stepTwoBox κ ω a then
            ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) else 0) *
              ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u)) +
          ∑' y, (if y ∈ stepTwoBox κ ω a then
            ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) else 0) *
              ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2)) := by
    intro a
    refine (ENNReal.ofReal_le_ofReal (hw i j r hr x a hP)).trans (le_of_eq ?_)
    have hF0 := stepTwoFactor_nonneg hG hGv κ i ω a
    have hE0 : ∀ u ∈ stepTwoBox κ ω a,
        0 ≤ openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
      fun u _ => openEnergy_nonneg _ _ u
    have hΦ0 : ∀ y ∈ stepTwoBox κ ω a, 0 ≤ zdHeat d (r ^ 2) x y ^ 2 := fun y _ => sq_nonneg _
    have hite : ∀ (g : Vertex d → ℝ≥0∞),
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
        ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2))]
  unfold stepTwoWeight
  simp only [ENNReal.tsum_mul_right]

end Weight

end Rigidity.Corrector.GeneralDim

import Rigidity.Proofs.Corrector.DarioFiniteEnergyGrowth
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationHolds

/-!
# Sublinear growth of functions of finite energy on the planar infinite cluster

The almost sure form of `abs_sub_coarseAnchor_zero_le`: by the minimal scales of the planar
partition (`planarMinimalScalesTwo_holds`, with exponent `α = 1/16`), almost surely the partition
cubes of the points of the square `|y|_∞ ≤ R` have side at most `(9R)^{1/16}` for all large `R`, so
every function `W` of finite energy `E` satisfies `|W(z) - W([0]_𝒫)| ≤ C R^{3/4} E^{1/2} = o(R)` on
the infinite cluster. This is the step of Dario's proof of Lemma 3.3 (Case 3 of Step 2) where the
potential `∇G(e, ·)`, of finite energy by (2.14), is asserted to grow sublinearly
(`ae_abs_sub_coarseAnchor_le_of_finiteEnergy`).
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation

theorem mem_cube_zero_of_abs_le {m R : ℕ} (hR : 2 * R + 1 ≤ 3 ^ m) {y : Vertex 2}
    (hy : ∀ i, |y i| ≤ R) : y ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2) := by
  rw [Rigidity.Proofs.Cluster.cube, Rigidity.Proofs.Cluster.mem_box]
  intro i
  have h3 := Rigidity.Proofs.Cluster.two_mul_halfSide_add_one m
  have h0 := Rigidity.Proofs.Cluster.halfSide_nonneg m
  have hc : Rigidity.Proofs.Cluster.center m (0 : Vertex 2) i = 0 := by
    simp only [Rigidity.Proofs.Cluster.center, Rigidity.Proofs.Cluster.idx, Pi.zero_apply,
      zero_add]
    rw [Int.ediv_eq_zero_of_lt h0 (by omega), mul_zero]
  rw [hc, sub_zero]
  have h2 := hy i
  have hR' : (2 * R + 1 : ℤ) ≤ 3 ^ m := by exact_mod_cast hR
  generalize |y i| = a at h2 ⊢
  generalize (3 : ℤ) ^ m = b at hR' h3
  omega

/-- The numerical step: if `S ≥ 1`, `S^16 ≤ 9R` and `R > 9 C^4 / ε^8` with `C = 320000 E`, then
`400 S^{3/2} (R + 1)^{1/2} E^{1/2} ≤ ε R`. -/
theorem growth_bound_le {S R E ε : ℝ} (hS : 1 ≤ S) (hR : 1 ≤ R) (hE : 0 ≤ E) (hε : 0 < ε)
    (hS16 : S ^ 16 ≤ 9 * R) (hRC : 9 * (320000 * E) ^ 4 / ε ^ 8 < R) :
    400 * S * Real.sqrt S * Real.sqrt (R + 1) * Real.sqrt E ≤ ε * R := by
  set C : ℝ := 320000 * E with hC
  have hC0 : 0 ≤ C := by positivity
  have hR0 : 0 < R := by linarith
  have hclaim : C * S ^ 4 ≤ ε ^ 2 * R := by
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have h1 : (ε ^ 2 * R) ^ 4 < (C * S ^ 4) ^ 4 :=
      pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    have h2 : (C * S ^ 4) ^ 4 ≤ C ^ 4 * (9 * R) := by
      rw [mul_pow, ← pow_mul]
      exact mul_le_mul_of_nonneg_left hS16 (by positivity)
    have h4 : 9 * C ^ 4 < R * ε ^ 8 := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 8)).1 hRC
      linarith
    have h5 : R * R ≤ R ^ 4 := by
      have := pow_le_pow_right₀ hR (by norm_num : 2 ≤ 4)
      nlinarith
    have h6 : 9 * C ^ 4 * R < ε ^ 8 * R ^ 4 := by
      have := mul_lt_mul_of_pos_right h4 hR0
      have h7 : R * ε ^ 8 * R ≤ ε ^ 8 * R ^ 4 := by
        have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ ε ^ 8)
        linarith
      linarith
    have h3 : (ε ^ 2 * R) ^ 4 = ε ^ 8 * R ^ 4 := by ring
    linarith
  set L := 400 * S * Real.sqrt S * Real.sqrt (R + 1) * Real.sqrt E with hL
  have hL0 : 0 ≤ L := by positivity
  have hS3 : S ^ 3 ≤ S ^ 4 := pow_le_pow_right₀ hS (by norm_num)
  have hLsq : L ^ 2 = 160000 * S ^ 3 * (R + 1) * E := by
    rw [hL]
    have e1 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ S)
    have e2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ R + 1)
    have e3 := Real.sq_sqrt hE
    calc (400 * S * Real.sqrt S * Real.sqrt (R + 1) * Real.sqrt E) ^ 2
        = 160000 * S ^ 2 * Real.sqrt S ^ 2 * Real.sqrt (R + 1) ^ 2 * Real.sqrt E ^ 2 := by ring
      _ = 160000 * S ^ 3 * (R + 1) * E := by rw [e1, e2, e3]; ring
  have hsq : L ^ 2 ≤ (ε * R) ^ 2 := by
    rw [hLsq]
    have h1 : 160000 * S ^ 3 * (R + 1) * E ≤ C * S ^ 4 * R := by
      rw [hC]
      have : S ^ 3 * (R + 1) ≤ S ^ 4 * (2 * R) :=
        mul_le_mul hS3 (by linarith) (by linarith) (by positivity)
      nlinarith
    have h2 : C * S ^ 4 * R ≤ ε ^ 2 * R * R := mul_le_mul_of_nonneg_right hclaim hR0.le
    nlinarith
  have hεR : 0 ≤ ε * R := by positivity
  nlinarith

/-- **Sublinear growth of functions of finite energy on the planar infinite cluster**: almost
surely, for every `W` whose energy on every finite set is at most `E` and every `ε > 0`, there is
`R₀` such that `|W(z) - W([0]_𝒫)| ≤ ε R` for every `R ≥ R₀` and every vertex `z` with `|z|_∞ ≤ R`
in an infinite open cluster. -/
theorem ae_abs_sub_coarseAnchor_le_of_finiteEnergy {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (W : Vertex 2 → ℝ) (E : ℝ),
      (∀ F : Finset (Vertex 2), localEnergy ω F W ≤ E) →
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ z : Vertex 2, (∀ i, |z i| ≤ R) →
        ((openGraph ω).connectedComponentMk z).supp.Infinite →
          |W z - W (planarCoarseAnchor ω 0)| ≤ ε * R := by
  obtain ⟨_, _, _, hall⟩ := Rigidity.Proofs.Regularity.planarMinimalScalesTwo_holds hpc
  obtain ⟨K, r, θ, -, -, -, M, -, -, -, hae⟩ := hall 1 one_pos (1 / 16) (by norm_num)
  filter_upwards [hae, ae_planarPartitionEvent hpc] with ω hω hP
  intro W E hE ε hε
  have hE0 : 0 ≤ E := (localEnergy_nonneg ω ∅ W).trans (hE ∅)
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (M ω) (by norm_num : (1 : ℝ) < 3)
  obtain ⟨R₁, hR₁⟩ := exists_nat_gt (9 * (320000 * E) ^ 4 / ε ^ 8)
  refine ⟨max (max (3 ^ m₀) 1) R₁, fun R hR z hz hinf => ?_⟩
  have hR3 : 3 ^ m₀ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR1 : 1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRR₁ : R₁ ≤ R := le_trans (le_max_right _ _) hR
  set m := Nat.clog 3 (2 * R + 1) with hmdef
  have hm1 : 2 * R + 1 ≤ 3 ^ m := Nat.le_pow_clog (by norm_num) _
  have hmpos : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, pow_zero] at hm1
    omega
  have hm2 : 3 ^ m ≤ 9 * R := by
    have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 3) (by omega : 1 < 2 * R + 1)
    rw [← hmdef] at h
    have h' : 3 ^ (m - 1) < 2 * R + 1 := by simpa [Nat.pred_eq_sub_one] using h
    have e : 3 ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hm₀m : 3 ^ m₀ ≤ 3 ^ m := by omega
  have hMm : M ω ≤ 3 ^ m := hm₀.le.trans (by exact_mod_cast hm₀m)
  obtain ⟨-, -, -, hsize, -⟩ := hω m hMm
  have hs : ∀ y : Vertex 2, (∀ i, |y i| ≤ R) →
      3 ^ (planarPartCube ω y).scale ≤ 3 ^ (m / 16) := by
    intro y hy
    have hb := hsize y (mem_cube_zero_of_abs_le hm1 hy)
    have hpow := pow_le_pow_left₀ (by positivity) hb 16
    rw [← Real.rpow_natCast (((3 : ℝ) ^ m) ^ (1 / 16 : ℝ)) 16,
      ← Real.rpow_mul (by positivity)] at hpow
    norm_num at hpow
    rw [← pow_mul] at hpow
    have h16 : (planarPartCube ω y).scale * 16 ≤ m :=
      (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hpow
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbound := abs_sub_coarseAnchor_zero_le hP hE hs hz hinf
  refine hbound.trans ?_
  have hS1 : (1 : ℝ) ≤ ((3 ^ (m / 16) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hS16 : ((3 ^ (m / 16) : ℕ) : ℝ) ^ 16 ≤ 9 * (R : ℝ) := by
    have h1 : (3 ^ (m / 16)) ^ 16 ≤ 3 ^ m := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self m 16)
    have h2 : (3 ^ (m / 16)) ^ 16 ≤ 9 * R := h1.trans hm2
    exact_mod_cast h2
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hRC : 9 * (320000 * E) ^ 4 / ε ^ 8 < (R : ℝ) :=
    lt_of_lt_of_le hR₁ (by exact_mod_cast hRR₁)
  exact growth_bound_le hS1 hRreal hE0 hε hS16 hRC

end Rigidity.Corrector

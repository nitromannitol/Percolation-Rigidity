import Rigidity.Proofs.Dirichlet.HardyWeight
import Rigidity.Proofs.Dirichlet.WeightedEnergy

/-!
# The Hardy weight of a lattice cube

For an integer cube `Q` with corner `z` and side `N`, the weight
`W_Q(x) = Σ_k (w(x_k − z_k) + w(z_k + N − 1 − x_k))`, built from the power-type weight `w` of
`HardyWeight` (`w(t) ≃ (t + 1)^{-γ}`), is large near the boundary of `Q`. In each direction its
gradient ratios are bounded by `4γ` times its second difference at the points of `Q` off the two
extreme slices in that direction, which is the hypothesis of the directional Hardy inequality and
of the weighted energy estimate `sum_weighted_energy_le`.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The two-sided weight of `Q` in the direction `k`. -/
noncomputable def cubeHardyWeightDir (γ : ℝ) (Q : IntegerCube d) (k : Fin d) (x : Vertex d) :
    ℝ :=
  hardyWeight γ (x k - Q.corner k).toNat +
    hardyWeight γ (Q.corner k + Q.size - 1 - x k).toNat

/-- The Hardy weight `W_Q = Σ_k` (two-sided weight in the direction `k`). -/
noncomputable def cubeHardyWeight (γ : ℝ) (Q : IntegerCube d) (x : Vertex d) : ℝ :=
  ∑ k, cubeHardyWeightDir γ Q k x

theorem cubeHardyWeightDir_pos {γ : ℝ} (hγ : γ < 1) (Q : IntegerCube d) (k : Fin d)
    (x : Vertex d) : 0 < cubeHardyWeightDir γ Q k x :=
  add_pos (hardyWeight_pos hγ _) (hardyWeight_pos hγ _)

theorem cubeHardyWeight_pos {γ : ℝ} (hγ : γ < 1) (hd : 0 < d) (Q : IntegerCube d)
    (x : Vertex d) : 0 < cubeHardyWeight γ Q x :=
  Finset.sum_pos (fun k _ => cubeHardyWeightDir_pos hγ Q k x) ⟨⟨0, hd⟩, Finset.mem_univ _⟩

theorem sub_unit_apply (x : Vertex d) (i k : Fin d) :
    (x - unit i) k = x k - if k = i then 1 else 0 := by
  simp [unit, Pi.single_apply]

/-- The weight in the direction `j` does not change along the direction `k ≠ j`. -/
theorem cubeHardyWeightDir_add_smul_of_ne (γ : ℝ) (Q : IntegerCube d) {j k : Fin d}
    (hjk : j ≠ k) (x : Vertex d) (c : ℤ) :
    cubeHardyWeightDir γ Q j (x + c • unit k) = cubeHardyWeightDir γ Q j x := by
  have : (x + c • unit k) j = x j := by simp [unit, hjk]
  simp only [cubeHardyWeightDir, this]

/-- Differences of `W_Q` in the direction `k` are differences of its `k`-th summand. -/
theorem cubeHardyWeight_add_smul_sub (γ : ℝ) (Q : IntegerCube d) (k : Fin d) (x : Vertex d)
    (c : ℤ) : cubeHardyWeight γ Q (x + c • unit k) - cubeHardyWeight γ Q x =
      cubeHardyWeightDir γ Q k (x + c • unit k) - cubeHardyWeightDir γ Q k x := by
  classical
  rw [cubeHardyWeight, cubeHardyWeight, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k (fun j _ hjk => by
    rw [cubeHardyWeightDir_add_smul_of_ne γ Q hjk x c, sub_self]) (by simp)]

/-- The edge average of `W_Q` dominates that of its `k`-th summand. -/
theorem cubeHardyWeightDir_add_le {γ : ℝ} (hγ : γ < 1) (Q : IntegerCube d) (k : Fin d)
    (x y : Vertex d) :
    cubeHardyWeightDir γ Q k x + cubeHardyWeightDir γ Q k y ≤
      cubeHardyWeight γ Q x + cubeHardyWeight γ Q y := by
  rw [cubeHardyWeight, cubeHardyWeight, ← Finset.sum_add_distrib]
  exact Finset.single_le_sum (f := fun j => cubeHardyWeightDir γ Q j x +
    cubeHardyWeightDir γ Q j y) (fun j _ => (add_pos (cubeHardyWeightDir_pos hγ Q j x)
      (cubeHardyWeightDir_pos hγ Q j y)).le) (Finset.mem_univ k)

/-- **The Hardy condition for the cube weight**: at a point of `Q` off the two extreme slices in
the direction `k`, the gradient ratios of `W_Q` on the two edges in the direction `k` are at most
`4γ` times its second difference, for `0 < γ ≤ 1/16`. -/
theorem cubeHardyWeight_ratio_add_le {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16)
    (Q : IntegerCube d) (k : Fin d) {x : Vertex d} (hx1 : Q.corner k + 1 ≤ x k)
    (hx2 : x k + 2 ≤ Q.corner k + Q.size) :
    (cubeHardyWeight γ Q (x + unit k) - cubeHardyWeight γ Q x) ^ 2 /
        ((cubeHardyWeight γ Q x + cubeHardyWeight γ Q (x + unit k)) / 2) +
      (cubeHardyWeight γ Q x - cubeHardyWeight γ Q (x - unit k)) ^ 2 /
        ((cubeHardyWeight γ Q (x - unit k) + cubeHardyWeight γ Q x) / 2) ≤
      4 * γ * (cubeHardyWeight γ Q (x + unit k) + cubeHardyWeight γ Q (x - unit k) -
        2 * cubeHardyWeight γ Q x) := by
  have hγ1 : γ < 1 := by linarith
  set Ω := cubeHardyWeightDir γ Q k
  set W := cubeHardyWeight γ Q
  have hxp : x + unit k = x + (1 : ℤ) • unit k := by rw [one_smul]
  have hxm : x - unit k = x + (-1 : ℤ) • unit k := by rw [neg_smul, one_smul, sub_eq_add_neg]
  have hdp : W (x + unit k) - W x = Ω (x + unit k) - Ω x := by
    rw [hxp]
    exact cubeHardyWeight_add_smul_sub γ Q k x 1
  have hdm : W x - W (x - unit k) = Ω x - Ω (x - unit k) := by
    have := cubeHardyWeight_add_smul_sub γ Q k x (-1)
    rw [← hxm] at this
    linarith
  have hΔ : W (x + unit k) + W (x - unit k) - 2 * W x =
      Ω (x + unit k) + Ω (x - unit k) - 2 * Ω x := by linarith
  have hΩ : ∀ y, 0 < Ω y := cubeHardyWeightDir_pos hγ1 Q k
  have hp1 : 0 < (Ω x + Ω (x + unit k)) / 2 := by have := hΩ x; have := hΩ (x + unit k); positivity
  have hp2 : 0 < (Ω (x - unit k) + Ω x) / 2 := by
    have := hΩ x; have := hΩ (x - unit k); positivity
  have hle1 : (W (x + unit k) - W x) ^ 2 / ((W x + W (x + unit k)) / 2) ≤
      (Ω (x + unit k) - Ω x) ^ 2 / ((Ω x + Ω (x + unit k)) / 2) := by
    rw [hdp]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hp1
      (by linarith [cubeHardyWeightDir_add_le hγ1 Q k x (x + unit k)])
  have hle2 : (W x - W (x - unit k)) ^ 2 / ((W (x - unit k) + W x) / 2) ≤
      (Ω x - Ω (x - unit k)) ^ 2 / ((Ω (x - unit k) + Ω x) / 2) := by
    rw [hdm]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hp2
      (by linarith [cubeHardyWeightDir_add_le hγ1 Q k (x - unit k) x])
  -- the values of the `k`-th summand
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = (x k - Q.corner k - 1).toNat := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = (Q.corner k + Q.size - 2 - x k).toNat := ⟨_, rfl⟩
  have hc : Ω x = hardyWeight γ (s + 1) + hardyWeight γ (r + 1) := by
    simp only [Ω, cubeHardyWeightDir]
    congr 2 <;> omega
  have hcp : Ω (x + unit k) = hardyWeight γ (s + 2) + hardyWeight γ r := by
    have hk : (x + unit k) k = x k + 1 := by rw [add_unit_apply, if_pos rfl]
    simp only [Ω, cubeHardyWeightDir, hk]
    congr 2 <;> omega
  have hcm : Ω (x - unit k) = hardyWeight γ s + hardyWeight γ (r + 2) := by
    have hk : (x - unit k) k = x k - 1 := by rw [sub_unit_apply, if_pos rfl]
    simp only [Ω, cubeHardyWeightDir, hk]
    congr 2 <;> omega
  have h := twoSided_ratio_add_le hγ0 hγ s r
  rw [← hc, ← hcp, ← hcm] at h
  rw [hΔ]
  linarith

end Rigidity.Dirichlet

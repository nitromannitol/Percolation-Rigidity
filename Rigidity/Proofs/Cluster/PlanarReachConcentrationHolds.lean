import Rigidity.Proofs.Cluster.PlanarGehringInputs
import Rigidity.Proofs.Percolation.PlanarReachDomination

/-!
# The averages of the powers of the reach concentrate

The hypothesis `PlanarReachConcentration` (the analogue of Proposition 2.4 of Armstrong and Dario
for the planar partition and its reach) holds. The reach is at most the stopping size of the
partition into coarsely good cubes (`planarReach_le_stoppingSize`), whose failure events are local
to the threefold enlargements and exponentially unlikely; for such partitions the sum of the
powers of the stopping sizes over a triadic cube is at most `C |□|` outside an event of
stretched-exponentially small probability (`exists_measure_sum_stoppingSize_gt_le`, the general
form of Proposition 2.4). A stretched exponential is smaller than every power of `3^{-k}`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped ENNReal

/-- A stretched exponential in `3^k` is at most a constant times any power of `3^{-k}`. -/
theorem exists_exp_neg_rpow_le_inv_pow {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (B : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ,
      Real.exp (-c * ((3 : ℝ) ^ k) ^ s) ≤ K * ((3 : ℝ) ^ k)⁻¹ ^ B := by
  set N : ℕ := ⌈(B : ℝ) / s⌉₊ with hN
  refine ⟨(N.factorial : ℝ) / (c / 2) ^ N, by positivity, fun k => ?_⟩
  set X : ℝ := ((3 : ℝ) ^ k) ^ s with hX
  have h3 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hX1 : 1 ≤ X := Real.one_le_rpow h3 hs.le
  have hX0 : 0 < X := by linarith
  have hpow := Rigidity.Percolation.pow_mul_exp_neg_le N hc hX0.le
  have hexp1 : Real.exp (-(c / 2) * X) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hXN : ((3 : ℝ) ^ k) ^ B ≤ X ^ N := by
    rw [hX, ← Real.rpow_natCast (((3 : ℝ) ^ k) ^ s), ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast ((3 : ℝ) ^ k) B]
    refine Real.rpow_le_rpow_of_exponent_le h3 ?_
    have h1 : (B : ℝ) / s ≤ N := Nat.le_ceil _
    rw [div_le_iff₀ hs] at h1
    linarith
  have hB0 : (0 : ℝ) < ((3 : ℝ) ^ k) ^ B := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hB0]
  calc Real.exp (-c * X) * ((3 : ℝ) ^ k) ^ B ≤ Real.exp (-c * X) * X ^ N :=
        mul_le_mul_of_nonneg_left hXN (Real.exp_pos _).le
    _ = X ^ N * Real.exp (-c * X) := by ring
    _ ≤ (N.factorial : ℝ) / (c / 2) ^ N * Real.exp (-(c / 2) * X) := hpow
    _ ≤ (N.factorial : ℝ) / (c / 2) ^ N * 1 :=
        mul_le_mul_of_nonneg_left hexp1 (by positivity)
    _ = (N.factorial : ℝ) / (c / 2) ^ N := mul_one _

/-- **The averages of the powers of the reach concentrate** (the analogue of Armstrong and Dario,
Proposition 2.4, for the reach of the planar partition). -/
theorem planarReachConcentration_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) : PlanarReachConcentration p := by
  intro τ
  obtain ⟨C₀, hC₀, c₀, hc₀, hq⟩ := exists_measure_not_mem_planarCoarseGood_le hpc
  obtain ⟨Cfin, Ctot, hCtot, c', hc', hsum⟩ := exists_measure_sum_stoppingSize_gt_le (d := 2)
    (by norm_num) p planarCoarseGood measurableSet_mem_planarCoarseGood
    measurableSet_not_mem_planarCoarseGood_localEdge hC₀ hc₀ one_pos le_rfl hq τ
  have hH : ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω) :=
    TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched (latticeBondLaw 2 p)
      planarCoarseGood (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top 1 c₀ one_pos hc₀ fun R => by
        rw [← ENNReal.ofReal_mul hC₀]
        exact hq R
  set s' : ℝ := 1 / ((2 * (2 + τ + 1) : ℕ) : ℝ) with hs'
  have hs'0 : 0 < s' := by positivity
  refine ⟨max Cfin 0, le_max_right _ _, fun B => ?_⟩
  obtain ⟨K, hK, hKB⟩ := exists_exp_neg_rpow_le_inv_pow hc' hs'0 B
  refine ⟨Ctot.toReal * K, mul_nonneg ENNReal.toReal_nonneg hK, fun k y => ?_⟩
  set R' : TriadicCube 2 := ⟨k, idx k y⟩ with hR'
  have hverts : R'.toIntegerCube.vertices = cube k y := Finset.ext fun x => by
    rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
  set E := {ω : Configuration 2 | ENNReal.ofReal (max Cfin 0 * (cube k y).card) <
    ∑ x ∈ cube k y, planarReach ω x ^ τ} with hE
  set N₀ := {ω : Configuration 2 | ¬ ∀ x : Vertex 2,
    ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω)} with hN₀
  have hN₀0 : latticeBondLaw 2 p N₀ = 0 := ae_iff.1 hH
  have hsub : E ⊆ N₀ ∪ {ω | Cfin * 3 ^ (2 * R'.scale) <
      ∑ x ∈ R'.toIntegerCube.vertices, TriadicCube.stoppingSize (planarCoarseGood ω) x ^ τ} := by
    intro ω hω
    by_cases hg : ∀ x : Vertex 2,
        ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω)
    · right
      have h1 : ∑ x ∈ cube k y, planarReach ω x ^ τ ≤
          ENNReal.ofReal (∑ x ∈ cube k y, TriadicCube.stoppingSize (planarCoarseGood ω) x ^ τ) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun x _ =>
          pow_nonneg (TriadicCube.stoppingSize_nonneg _ x) τ]
        refine Finset.sum_le_sum fun x _ => ?_
        rw [ENNReal.ofReal_pow (TriadicCube.stoppingSize_nonneg _ x)]
        exact pow_le_pow_left₀ zero_le (planarReach_le_stoppingSize hg x) τ
      have h2 := lt_of_lt_of_le hω h1
      rw [ENNReal.ofReal_lt_ofReal_iff'] at h2
      have hcard : ((cube k y).card : ℝ) = (3 : ℝ) ^ (2 * k) := by
        rw [card_cube, ← pow_mul, mul_comm]
      change Cfin * 3 ^ (2 * k) < _
      rw [hverts]
      have h3 : Cfin * (3 : ℝ) ^ (2 * k) ≤ max Cfin 0 * ((cube k y).card : ℝ) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith [h2.1]
    · left
      exact hg
  calc latticeBondLaw 2 p E
      ≤ latticeBondLaw 2 p (N₀ ∪ {ω | Cfin * 3 ^ (2 * R'.scale) <
          ∑ x ∈ R'.toIntegerCube.vertices,
            TriadicCube.stoppingSize (planarCoarseGood ω) x ^ τ}) := measure_mono hsub
    _ ≤ latticeBondLaw 2 p N₀ + latticeBondLaw 2 p {ω | Cfin * 3 ^ (2 * R'.scale) <
          ∑ x ∈ R'.toIntegerCube.vertices,
            TriadicCube.stoppingSize (planarCoarseGood ω) x ^ τ} := measure_union_le _ _
    _ ≤ 0 + Ctot * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ R'.scale) ^
          ((1 : ℝ) / ((2 * (2 + τ + 1) : ℕ) : ℝ)))) := by
        rw [hN₀0]
        exact add_le_add le_rfl (hsum R')
    _ ≤ ENNReal.ofReal (Ctot.toReal * K * ((3 : ℝ) ^ k)⁻¹ ^ B) := by
        rw [zero_add]
        conv_lhs => rw [← ENNReal.ofReal_toReal hCtot]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_assoc]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
        exact hKB k

end Rigidity.Proofs.Cluster

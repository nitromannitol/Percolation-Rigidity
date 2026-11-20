import Rigidity.Proofs.Percolation.PlanarMuUpperBound
import Rigidity.Proofs.Percolation.PlanarReachMoments

/-!
# Expected size of `-μ` on the planar cluster

The coarse weight at a vertex is at most four times the number of partition cubes of `U` whose
square of side `9s` contains it, hence at most `484` times the square of the reach. With the
moment bound for the reach, the upper bound for `-μ` gives
`E[-μ(U, q); partition event, U resolved] ≤ C (|q₁| + |q₂|) ^ 2` uniformly in `U`
(Armstrong and Dario, (4.15)).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The squared coarse weight is controlled by the fourth power of the reach. -/
theorem ofReal_coarseWeight_sq_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (a : Vertex 2) :
    ENNReal.ofReal (coarseWeight ω U a ^ 2) ≤ 234256 * planarReach ω a ^ 4 := by
  have hW := coarseWeight_le hP hU a
  have hN := ofReal_sum_ninefold_le hP U.toIntegerCube.vertices a 0
  simp only [zero_mul, pow_zero, zero_add] at hN
  set N := ∑ z ∈ U.toIntegerCube.vertices,
    (if a ∈ (planarPartCube ω z).ninefold.vertices then (1 : ℝ) else 0) with hNdef
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hW0 := coarseWeight_nonneg (ω := ω) U a
  calc ENNReal.ofReal (coarseWeight ω U a ^ 2)
      ≤ ENNReal.ofReal ((4 * N) ^ 2) := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hW0 hW 2)
    _ = 16 * ENNReal.ofReal N ^ 2 := by
        rw [mul_pow, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hN0]
        norm_num
    _ ≤ 16 * (121 * planarReach ω a ^ 2) ^ 2 := by gcongr
    _ = 234256 * planarReach ω a ^ 4 := by ring

/-- `-μ` is controlled by the fourth powers of the reach over `U`. -/
theorem ofReal_neg_planarMu_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) :
    ENNReal.ofReal (-planarMu ω U q) ≤
      ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / U.volume) *
        ∑ a ∈ U.toIntegerCube.vertices, 234256 * planarReach ω a ^ 4 := by
  have h := neg_planarMu_le hP hU q
  have hc : 0 ≤ 9 * (|q 0| + |q 1|) ^ 2 / U.volume := by
    have := U.volume_pos
    positivity
  have hre : 9 * (|q 0| + |q 1|) ^ 2 *
      (∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2) / U.volume =
      9 * (|q 0| + |q 1|) ^ 2 / U.volume *
        ∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2 := by ring
  rw [hre] at h
  calc ENNReal.ofReal (-planarMu ω U q)
      ≤ ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / U.volume *
          ∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / U.volume) *
          ∑ x : ↥(clusterVertices ω U), ENNReal.ofReal (coarseWeight ω U x.1 ^ 2) := by
        rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
    _ ≤ ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / U.volume) *
          ∑ x : ↥(clusterVertices ω U), 234256 * planarReach ω x.1 ^ 4 := by
        gcongr with x
        exact ofReal_coarseWeight_sq_le hP hU x.1
    _ = ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / U.volume) *
          ∑ a ∈ clusterVertices ω U, 234256 * planarReach ω a ^ 4 := by
        rw [Finset.sum_coe_sort (clusterVertices ω U) (fun a => 234256 * planarReach ω a ^ 4)]
    _ ≤ ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / U.volume) *
          ∑ a ∈ U.toIntegerCube.vertices, 234256 * planarReach ω a ^ 4 := by
        gcongr
        exact Finset.filter_subset _ _

/-- The sum over partition cubes reaching a vertex, weighted by `s ^ m`. -/
noncomputable def reachSum (ω : Configuration 2) (m : ℕ) (a : Vertex 2) : ℝ≥0∞ :=
  ∑' Q : TriadicCube 2, if Q.IsMaximalStopping (planarGoodCubes ω) ∧
    a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then (3 : ℝ≥0∞) ^ (m * Q.scale) else 0

theorem measurable_reachSum (m : ℕ) (a : Vertex 2) :
    Measurable fun ω : Configuration 2 => reachSum ω m a := by
  refine Measurable.tsum fun Q => ?_
  by_cases ha : a ∈ (↑Q.ninefold.vertices : Set (Vertex 2))
  · simp only [ha, and_true]
    exact measurable_const.ite (measurableSet_isMaximalStopping_planarGoodCubes Q)
      measurable_const
  · simp only [ha, and_false, if_false]
    exact measurable_const

theorem card_toIntegerCube_vertices (U : TriadicCube 2) :
    ((U.toIntegerCube.vertices.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal U.volume := by
  rw [IntegerCube.card_vertices]
  change (((3 ^ U.scale) ^ 2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((9 : ℝ) ^ U.scale)
  rw [ENNReal.ofReal_pow (by norm_num), ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **Expected size of `-μ`** (Armstrong and Dario, (4.15)). -/
theorem exists_lintegral_neg_planarMu_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (q : Fin 2 → ℝ),
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) := by
  obtain ⟨C₄, hC₄, hle⟩ := exists_lintegral_tsum_ninefold_le hpc 4
  refine ⟨9 * 234256 * C₄, ENNReal.mul_ne_top (by norm_num) hC₄, fun U q => ?_⟩
  set c := ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / U.volume) with hc
  have hpoint : ∀ ω : Configuration 2, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (-planarMu ω U q) else 0) ≤
      c * ∑ a ∈ U.toIntegerCube.vertices, 234256 * reachSum ω 4 a := by
    intro ω
    split_ifs with h
    · refine (ofReal_neg_planarMu_le h.1 h.2 q).trans ?_
      gcongr with a
      exact planarReach_pow_le ω a 3
    · exact zero_le
  have hvol := U.volume_pos
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p)
      ≤ ∫⁻ ω, c * ∑ a ∈ U.toIntegerCube.vertices, 234256 * reachSum ω 4 a
          ∂(latticeBondLaw 2 p) := lintegral_mono hpoint
    _ = c * ∑ a ∈ U.toIntegerCube.vertices, 234256 *
          ∫⁻ ω, reachSum ω 4 a ∂(latticeBondLaw 2 p) := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun a _ =>
          (measurable_reachSum 4 a).const_mul _)]
        rw [lintegral_finsetSum _ fun a _ => (measurable_reachSum 4 a).const_mul _]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [lintegral_const_mul _ (measurable_reachSum 4 a)]
    _ ≤ c * ∑ _a ∈ U.toIntegerCube.vertices, 234256 * C₄ := by
        gcongr with a
        exact hle a
    _ = 9 * 234256 * C₄ * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, card_toIntegerCube_vertices, hc]
        rw [← mul_assoc, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal U.volume), ← mul_assoc,
          ← ENNReal.ofReal_mul hvol.le]
        rw [show U.volume * (9 * (|q 0| + |q 1|) ^ 2 / U.volume) =
          9 * (|q 0| + |q 1|) ^ 2 by field_simp]
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

end Rigidity.Percolation

import Rigidity.Proofs.Cluster.PlanarSubcubePairing
import Rigidity.Proofs.Percolation.PlanarMuMoments
import Rigidity.Proofs.Percolation.PlanarMuEnergyDefect

/-!
# The coarsened gradient of the minimizer of `μ`

On a triadic cube `V` resolved by the planar partition, the energy of the coarsening of a function
`w` on the cluster is at most `C² (3^{m})³ B(w, w)`, where `m` is the largest pair reach scale on
the cluster; `3^m` is at most three times the largest reach of the planar partition on `V`. For the
minimizer `u` of `μ(V, q)`, `B(u, u) = -2 |V| μ(V, q)` and `-μ(V, q) ≤ 9 |q|₁² |V|⁻¹ ∑_V 234256 R⁴`
(`ofReal_neg_planarMu_le`), so that
`∑_{x ∈ V} |∇[u]_𝒫|²(x) ≤ 18 C² |q|₁² (3 max_V R)³ ∑_{a ∈ V} 234256 R(a)⁴`
with `R = planarReach` (`ofReal_sum_gradNormIn_coarse_planarMuMinimizer_le`). This is the
deterministic part of display (4.24) of Armstrong and Dario in dimension two, with the reach of the
planar partition in place of the sizes of the partition cubes; its expectation is controlled by the
moments of the reach.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- **The energy of a coarsened function, by the largest pair reach scale.** -/
theorem sum_gradNormIn_coarse_sq_le_sup (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (w : ClusterFun ω V) :
    ∑ x ∈ V.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
        (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) x ^ 2 ≤
      (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ 2 *
        (((3 : ℝ) ^ ((clusterVertices ω V).sup (planarCoarseData hP V hV).pairReachScale)) ^ 3 *
          clusterForm ω V w w) := by
  have h := planar_sum_gradNormIn_coarseAnchor_rpow_le hP hV (clusterExtend ω V w) (s := 2)
    (by norm_num)
  simp only [Real.rpow_two] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← sum_clusterGradSq_eq_clusterForm V w, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have he : ((3 : ℝ) ^ (planarCoarseData hP V hV).pairReachScale z) ^
      ((2 : ℝ) * ((2 : ℕ) : ℝ) - 1) =
      ((3 : ℝ) ^ (planarCoarseData hP V hV).pairReachScale z) ^ 3 := by
    rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [he, gradNormIn_openGraph_eq, Real.sq_sqrt (clusterGradSq_nonneg _ _ _ _)]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ 3)
    (clusterGradSq_nonneg _ _ _ _)
  exact pow_le_pow_right₀ (by norm_num)
    (Finset.le_sup (f := (planarCoarseData hP V hV).pairReachScale) hz)

/-- The largest pair reach scale on the cluster is at most three times the largest reach of the
planar partition on the cube. -/
theorem three_pow_sup_pairReachScale_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) :
    (3 : ℝ≥0∞) ^ ((clusterVertices ω V).sup (planarCoarseData hP V hV).pairReachScale) ≤
      3 * V.toIntegerCube.vertices.sup (planarReach ω) := by
  by_cases hne : (clusterVertices ω V).Nonempty
  · obtain ⟨z, hz, hzs⟩ := Finset.exists_mem_eq_sup _ hne (planarCoarseData hP V hV).pairReachScale
    rw [hzs]
    have hzV : z ∈ V.toIntegerCube.vertices := Finset.filter_subset _ _ hz
    calc (3 : ℝ≥0∞) ^ (planarCoarseData hP V hV).pairReachScale z ≤ 3 * planarReach ω z :=
          three_pow_pairReachScale_le_planarReach hP hV z
      _ ≤ 3 * V.toIntegerCube.vertices.sup (planarReach ω) := by
          gcongr
          exact Finset.le_sup (f := planarReach ω) hzV
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sup_empty]
    have hx : V.toIntegerCube.corner ∈ V.toIntegerCube.vertices := by
      rw [IntegerCube.mem_vertices]
      intro i
      have : (0 : ℤ) < ((V.toIntegerCube.size : ℕ) : ℤ) := by
        rw [V.cast_toIntegerCube_size]
        positivity
      omega
    calc (3 : ℝ≥0∞) ^ (⊥ : ℕ) = 1 := pow_zero 3
      _ ≤ planarReach ω V.toIntegerCube.corner := one_le_planarReach hP _
      _ ≤ V.toIntegerCube.vertices.sup (planarReach ω) := Finset.le_sup (f := planarReach ω) hx
      _ ≤ 3 * V.toIntegerCube.vertices.sup (planarReach ω) :=
          le_mul_of_one_le_left zero_le (by norm_num)

/-- **The energy of a coarsened function, by the largest reach**, in `ℝ≥0∞`:
`∑_{x ∈ V} |∇[w]_𝒫|²(x) ≤ C² (3 max_V R)³ B(w, w)`. -/
theorem ofReal_sum_gradNormIn_coarse_sq_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (w : ClusterFun ω V) :
    ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
          (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) x ^ 2) ≤
      ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
        (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) *
        (3 * V.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 *
          ENNReal.ofReal (clusterForm ω V w w) := by
  set m := (clusterVertices ω V).sup (planarCoarseData hP V hV).pairReachScale with hm
  set C : ℝ := 2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ)) with hC
  have h := sum_gradNormIn_coarse_sq_le_sup hP hV w
  rw [← hm] at h
  have hB := clusterForm_self_nonneg (ω := ω) (U := V) w
  have h3 : ENNReal.ofReal (((3 : ℝ) ^ m) ^ 3) ≤
      (3 * V.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    exact pow_le_pow_left₀ zero_le (three_pow_sup_pairReachScale_le hP hV) 3
  calc ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
          (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) x ^ 2)
      ≤ ENNReal.ofReal (C ^ 2 * (((3 : ℝ) ^ m) ^ 3 * clusterForm ω V w w)) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (((3 : ℝ) ^ m) ^ 3) *
          ENNReal.ofReal (clusterForm ω V w w)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C ^ 2) * ((3 * V.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 *
          ENNReal.ofReal (clusterForm ω V w w)) := by
        gcongr
    _ = _ := by ring

/-- **The coarsened gradient of the minimizer of `μ`** (Armstrong and Dario, (4.24),
deterministic part, in dimension two): on a resolved cube `V`,
`∑_{x ∈ V} |∇[u(·, V, q)]_𝒫|²(x) ≤ 18 C² |q|₁² (3 max_V R)³ ∑_{a ∈ V} 234256 R(a)⁴`. -/
theorem ofReal_sum_gradNormIn_coarse_planarMuMinimizer_le (hP : PlanarPartitionEvent ω)
    {V : TriadicCube 2} (hV : PlanarResolved ω V) (q : Fin 2 → ℝ) :
    ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
          (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x)) x ^ 2) ≤
      ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
        (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) *
        (3 * V.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 *
          (ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) *
            ∑ a ∈ V.toIntegerCube.vertices, 234256 * planarReach ω a ^ 4) := by
  obtain ⟨hu, hvar⟩ := planarMuMinimizer_spec hP hV q
  have hmu := planarMu_mul_volume_eq hP hV q hu hvar
  have hvol := V.volume_pos
  have hB : clusterForm ω V (planarMuMinimizer ω V q) (planarMuMinimizer ω V q) =
      2 * V.volume * (-planarMu ω V q) := by linarith
  refine (ofReal_sum_gradNormIn_coarse_sq_le hP hV _).trans (mul_le_mul' le_rfl ?_)
  rw [hB, ENNReal.ofReal_mul (by positivity)]
  have hneg := ofReal_neg_planarMu_le hP hV q
  calc ENNReal.ofReal (2 * V.volume) * ENNReal.ofReal (-planarMu ω V q)
      ≤ ENNReal.ofReal (2 * V.volume) *
          (ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / V.volume) *
            ∑ a ∈ V.toIntegerCube.vertices, 234256 * planarReach ω a ^ 4) := by
        gcongr
    _ = ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) *
          ∑ a ∈ V.toIntegerCube.vertices, 234256 * planarReach ω a ^ 4 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
        ring

end Rigidity.Proofs.Cluster

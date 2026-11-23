import Rigidity.Proofs.Regularity.PlanarRestrictErrorOs
import Rigidity.Proofs.Regularity.PlanarNuEnergy
import Rigidity.Proofs.Percolation.PlanarFlatnessAE
import Rigidity.Proofs.Percolation.PlanarNablaAffineMoments

/-!
# The terms of (5.33) for one configuration with a bounded reach

For one configuration on the partition event whose reach is at most `S` on a cube `U`:

* `partScale_le_of_reach`, `planarResolved_scaleCube_of_reach`: the partition cubes of the vertices
  of `U` have side at most `S`, so the subcubes of side at least `S` are resolved;
* `coarseEnergy_le_of_reach`: the energy of the coarsened maximizer of `ν(U, ξ)` is at most
  `K (3 S)³ (9/2) |ξ|₁²` (the pointwise bound behind (4.25) of Armstrong and Dario,
  arXiv:1609.09431v2);
* `sum_sq_planarNuGradAvg_le_of_reach`: display (4.26), the deviation of the spatial average of the
  coarsened gradient of `v(·, V, ξ)` from `ξ`, is at most `C |ξ|² (16 S⁸ + 1) 3^{-n}` on a resolved
  subcube of scale `n`;
* `planarNuRestrictError_le_of_reach`: the quantity of (5.12) is at most
  `Λ (2 ε + C S 3^{-⌊n/2⌋})` when it is at most `Λ D_n / |U|` (off the bad event of Lemma 5.5)
  and `ν` is within `ε` of a constant on `U` and its subcubes.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Cluster Rigidity.Proofs.Section5
open scoped Classical ENNReal

variable {ω : Configuration 2}

theorem three_pow_partScale_le_of_reach (hP : PlanarPartitionEvent ω) {z : Vertex 2} {S : ℝ}
    (hz : planarReach ω z ≤ ENNReal.ofReal S) : (3 : ℝ) ^ (planarPartCube ω z).scale ≤ S := by
  have hz9 : z ∈ (planarPartCube ω z).ninefold.vertices :=
    Finset.mem_coe.1 (mem_ninefold_of_near (planarPartCube_spec hP z).1 fun i => by simp)
  have h := (three_pow_scale_le_planarReach hP hz9).trans hz
  rw [show (3 : ℝ≥0∞) ^ (planarPartCube ω z).scale =
    ENNReal.ofReal ((3 : ℝ) ^ (planarPartCube ω z).scale) by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num] at h
  rcases le_or_gt 0 S with hS | hneg
  · exact (ENNReal.ofReal_le_ofReal_iff hS).1 h
  · rw [ENNReal.ofReal_of_nonpos hneg.le, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
    have : (0 : ℝ) < 3 ^ (planarPartCube ω z).scale := by positivity
    linarith

theorem partScale_le_of_reach (hP : PlanarPartitionEvent ω) {z : Vertex 2} {S : ℝ} {a : ℕ}
    (hz : planarReach ω z ≤ ENNReal.ofReal S) (hSa : S ≤ 3 ^ a) :
    (planarPartCube ω z).scale ≤ a :=
  (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1
    ((three_pow_partScale_le_of_reach hP hz).trans hSa)

/-- A cube of side at least `S` inside `U` is resolved. -/
theorem planarResolved_of_reach (hP : PlanarPartitionEvent ω) {U V : TriadicCube 2}
    (hVU : V.vertices ⊆ U.vertices) {S : ℝ}
    (hreach : ∀ z ∈ U.toIntegerCube.vertices, planarReach ω z ≤ ENNReal.ofReal S)
    (hS : S ≤ 3 ^ V.scale) : PlanarResolved ω V := fun z hz =>
  partScale_le_of_reach hP (hreach z ((U.mem_toIntegerCube_vertices z).2 (hVU hz))) hS

/-- **The energy of the coarsened maximizer of `ν`** with a bounded reach. -/
theorem coarseEnergy_le_of_reach (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (ξ : Fin 2 → ℝ) {S : ℝ} (hS : 0 ≤ S)
    (hreach : ∀ z ∈ U.toIntegerCube.vertices, planarReach ω z ≤ ENNReal.ofReal S) :
    coarseEnergy ω U (planarNuSolution ω U ξ) ≤
      (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
        (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 * (3 * S) ^ 3 *
        (9 / 2 * (|ξ 0| + |ξ 1|) ^ 2) := by
  set KE : ℝ := (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 with hKE
  have hsol : planarNuSolution ω U ξ = planarNuMaximizer ω U ξ := by
    rw [planarNuSolution, if_pos ⟨hP, hU⟩]
  have h1 := ofReal_sum_gradNormIn_coarse_sq_le hP hU (planarNuMaximizer ω U ξ)
  have hsup : U.toIntegerCube.vertices.sup (planarReach ω) ≤ ENNReal.ofReal S :=
    Finset.sup_le hreach
  have hB := clusterForm_planarNuSolution_le hP hU ξ
  rw [hsol] at hB
  have hKE : 0 ≤ KE := sq_nonneg _
  have h3S : 0 ≤ (3 * S) ^ 3 := pow_nonneg (by linarith) 3
  have hB0 : 0 ≤ 9 / 2 * (|ξ 0| + |ξ 1|) ^ 2 * U.volume := by
    have := U.volume_pos; positivity
  have h2 : ENNReal.ofReal KE * (3 * U.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 *
      ENNReal.ofReal (clusterForm ω U (planarNuMaximizer ω U ξ) (planarNuMaximizer ω U ξ)) ≤
      ENNReal.ofReal (KE * (3 * S) ^ 3 * (9 / 2 * (|ξ 0| + |ξ 1|) ^ 2 * U.volume)) := by
    calc ENNReal.ofReal KE * (3 * U.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 *
          ENNReal.ofReal (clusterForm ω U (planarNuMaximizer ω U ξ) (planarNuMaximizer ω U ξ))
        ≤ ENNReal.ofReal KE * (3 * ENNReal.ofReal S) ^ 3 *
          ENNReal.ofReal (9 / 2 * (|ξ 0| + |ξ 1|) ^ 2 * U.volume) := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (mul_nonneg hKE h3S), ENNReal.ofReal_mul hKE,
            ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 3 * S),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
            ENNReal.ofReal_ofNat]
  have h3 := (h1.trans h2)
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hKE h3S) hB0)] at h3
  rw [coarseEnergy_eq, hsol]
  have hv := U.volume_pos
  rw [inv_mul_le_iff₀ hv]
  calc _ ≤ KE * (3 * S) ^ 3 * (9 / 2 * (|ξ 0| + |ξ 1|) ^ 2 * U.volume) := h3
    _ = _ := by ring

/-- **Display (4.26) with a bounded reach.** -/
theorem sum_sq_planarNuGradAvg_le_of_reach (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (ξ : Fin 2 → ℝ) {S : ℝ}
    (hreach : ∀ z ∈ V.toIntegerCube.vertices, planarReach ω z ≤ ENNReal.ofReal S) :
    ∑ j : Fin 2, (planarNuGradAvg ω V ξ j - ξ j) ^ 2 ≤
      1296 * 162001 ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) * (16 * S ^ 8 + 1) / 3 ^ V.scale := by
  refine (le_nablaAffineMajorant V ξ ω).trans ?_
  unfold nablaAffineMajorant
  rw [if_pos ⟨hP, hV⟩]
  set L : ℝ := (V.toIntegerCube.size : ℝ) with hL
  have hLs : L = (3 : ℝ) ^ V.scale := by rw [hL]; exact_mod_cast V.cast_toIntegerCube_size
  have hL0 : 0 < L := by rw [hLs]; positivity
  have hside : ∀ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ 8 ≤ S ^ 8 := by
    intro k hk
    have hkV : k.2.2 ∈ V.toIntegerCube.vertices :=
      (Finset.mem_product.1 (Finset.mem_product.1 (Finset.mem_filter.1 hk).1).2).2
    rw [partSideP, if_pos hP, partSide]
    exact pow_le_pow_left₀ (by positivity) (three_pow_partScale_le_of_reach hP (hreach _ hkV)) 8
  have hsum : ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ 8 ≤ 4 * L * S ^ 8 := by
    refine (Finset.sum_le_sum hside).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_boundaryIndex_le V) (by positivity)
  have hQ : 0 ≤ ξ 0 ^ 2 + ξ 1 ^ 2 := by positivity
  rw [← hLs]
  have h1 : (∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ 8) / (L * L) ≤ 4 * S ^ 8 / L := by
    rw [div_le_div_iff₀ (mul_pos hL0 hL0) hL0]
    have := mul_le_mul_of_nonneg_right hsum hL0.le
    nlinarith
  have key : 4 * ((∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ 8) / (L * L)) + 1 / L ≤
      (16 * S ^ 8 + 1) / L := by
    calc 4 * ((∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ 8) / (L * L)) + 1 / L
        ≤ 4 * (4 * S ^ 8 / L) + 1 / L := by linarith
      _ = (16 * S ^ 8 + 1) / L := by ring
  calc 1296 * 162001 ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) *
        (4 * ((∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ 8) / (L * L)) + 1 / L)
      ≤ 1296 * 162001 ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) * ((16 * S ^ 8 + 1) / L) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

end Rigidity.Proofs.Regularity

import Rigidity.Proofs.Cluster.PlanarCoarseMeyers
import Rigidity.Proofs.Cluster.PartitionBoxSobolev
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuUpperBound

/-!
# Coarse gradients through the Meyers estimate, in every dimension

The deterministic core of Step 3 of the proof of Lemma 5.5 of Armstrong and Dario, display
(5.16) there, for the partition into good cubes in every dimension `d ≥ 1`. The coarsening
`[w]_𝒫` of a function `w` has, on a resolved integer cube `B` whose cluster lies in a set `U₀`,
the energy bound of Lemma 3.3 with `s = 2`,
`∑_{x ∈ B} |∇[w]_𝒫|²(x) ≤ K² ∑_{z ∈ 𝒞(B)} size(□_𝒫(z))^{2d-1} |∇w 1_{𝐚≠0}|²_{U₀}(z)`
(`partitionBox_sum_gradNormIn_sq_le_clusterGradSq`). In each cell `□'` of a finite family covering
`𝒞(B)`, with `3□' ⊆ V` and overlap of the triples at most `N`, Hölder's inequality with the
exponents `p` and its conjugate `q` and the Meyers estimate `avg_{□'} E^p ≤ C_M (avg_{3□'} E)^p`,
`E = |∇w 1_{𝐚≠0}|²` on `U₀`, give (`Rigidity.Proofs.Cluster.sum_mul_le_of_meyers_cells`, which is
dimension-free): if `(avg_{□'} W^{(2d-1)q})^{1/q} ≤ A` on every cell for a weight `W ≥ size(□_𝒫)`,
`∑_{x ∈ B} |∇[w]_𝒫|² ≤ K² A C_M^{1/p} N ∑_{x ∈ V} E(x)` (`partitionBox_coarse_energy_le_of_meyers`).

As in dimension two (`Rigidity.Proofs.Cluster.planarBox_coarse_energy_le_of_meyers`), Hölder's
inequality is applied inside each cell rather than to the whole sum over the cells of the Meyers
partition, which avoids the loss of a power of the number of cells in the global form of Armstrong
and Dario; the weight factor is the largest cell average of the weight.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The constant `2d · 21^d (1 + 3^d) 3^d 2√d` of Lemma 3.3 for the partition into good cubes. -/
noncomputable def partitionCoarseGradConst (d : ℕ) : ℝ :=
  2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) * (2 * √(d : ℝ))

theorem partitionCoarseGradConst_nonneg (d : ℕ) : 0 ≤ partitionCoarseGradConst d := by
  unfold partitionCoarseGradConst
  positivity

/-- **Lemma 3.3 with `s = 2` for a function on a larger cluster.** On a resolved integer cube
`B` whose cluster lies in `U₀`,
`∑_{x ∈ B} |∇[w]_𝒫|²(x) ≤ K² ∑_{z ∈ 𝒞(B)} (3^{scale □_𝒫(z)})^{2d-1} |∇w 1_{𝐚≠0}|²_{U₀}(z)`. -/
theorem partitionBox_sum_gradNormIn_sq_le_clusterGradSq (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {U₀ : Finset (Vertex d)}
    (hBU : partitionBoxCluster ω B ⊆ U₀) (w : Vertex d → ℝ) :
    ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph d) B.vertices
        (fun x => w (partitionAnchor ω x)) x ^ 2 ≤
      coarseGradConstant d ^ 2 *
        ∑ z ∈ partitionBoxCluster ω B, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d - 1) *
          clusterGradSq ω U₀ w z := by
  have h := partitionBox_sum_gradNormIn_coarseAnchor_rpow_le hd hP hB w (s := 2) (by norm_num)
  simp only [Real.rpow_two] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) (sq_nonneg _))
  have he : ((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * (d : ℝ) - 1) =
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d - 1) := by
    rw [show (2 : ℝ) * (d : ℝ) - 1 = ((2 * d - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num, Real.rpow_natCast]
  rw [he, gradNormIn_openGraph_eq, Real.sq_sqrt (clusterGradSq_nonneg _ _ _ _)]
  exact mul_le_mul_of_nonneg_left (clusterGradSq_le_of_subset ω hBU w z) (by positivity)

/-- **Coarse gradients through the Meyers estimate** (the deterministic core of Step 3 of the proof
of Lemma 5.5 of Armstrong and Dario, display (5.16), every dimension `d ≥ 1`). Let `B` be a
resolved integer cube whose cluster lies in `U₀`, `w` a function, `E = |∇w 1_{𝐚≠0}|²` on `U₀`,
`W ≥ 0` a weight with `W ≥ size(□_𝒫)` on `𝒞(B)`, `p > 1` with Hölder conjugate `q`, and let a
finite family of cells `□'` cover `𝒞(B)`, with `3□' ⊆ V`, overlap of the triples at most `N`, the
Meyers estimate `avg_{□'} E^p ≤ C_M (avg_{3□'} E)^p` and `(avg_{□'} W^{(2d-1)q})^{1/q} ≤ A`. Then
`∑_{x ∈ B} |∇[w]_𝒫|²(x) ≤ K² A C_M^{1/p} N ∑_{x ∈ V} E(x)`. -/
theorem partitionBox_coarse_energy_le_of_meyers (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {U₀ V : Finset (Vertex d)}
    (hBU : partitionBoxCluster ω B ⊆ U₀) (w : Vertex d → ℝ)
    (Wt : Vertex d → ℝ) (hWt0 : ∀ x, 0 ≤ Wt x)
    (hWt : ∀ z ∈ partitionBoxCluster ω B, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z)
    {p q CM A : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (I : Finset (ℕ × Vertex d)) {N : ℕ}
    (hcov : ∀ z ∈ partitionBoxCluster ω B, ∃ c ∈ I, z ∈ cube c.1 c.2)
    (hV : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ V)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hA : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ q) ^ (1 / q) ≤ A)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => clusterEnergy ω U₀ w x ^ p) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω U₀ w) ^ p) :
    ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph d) B.vertices
        (fun x => w (partitionAnchor ω x)) x ^ 2 ≤
      coarseGradConstant d ^ 2 *
        (A * (CM ^ (1 / p) * ((N : ℝ) * ∑ x ∈ V, clusterEnergy ω U₀ w x))) := by
  set E : Vertex d → ℝ := clusterEnergy ω U₀ w with hEdef
  have hE0 : ∀ x, 0 ≤ E x := clusterEnergy_nonneg ω U₀ w
  have hcoarse := partitionBox_sum_gradNormIn_sq_le_clusterGradSq hd hP hB hBU w
  refine hcoarse.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  set C := partitionBoxCluster ω B with hCdef
  have hGE : ∀ z ∈ C, clusterGradSq ω U₀ w z = E z := fun z hz => by
    rw [hEdef, clusterEnergy, if_pos (hBU hz)]
  have hstep1 : ∑ z ∈ C, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d - 1) *
      clusterGradSq ω U₀ w z ≤ ∑ z ∈ C, Wt z ^ (2 * d - 1) * E z := by
    refine Finset.sum_le_sum fun z hz => ?_
    rw [hGE z hz]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hWt z hz) _) (hE0 z)
  exact hstep1.trans (Rigidity.Proofs.Cluster.sum_mul_le_of_meyers_cells hE0
    (fun x => pow_nonneg (hWt0 x) _) hpq hCM hA0 I C V hcov hV hN hA hM)

end Rigidity.Percolation

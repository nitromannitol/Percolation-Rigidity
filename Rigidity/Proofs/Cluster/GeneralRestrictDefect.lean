import Rigidity.Proofs.Cluster.GeneralRestrictQuad
import Rigidity.Proofs.Cluster.GeneralMuEnergyDefect

/-!
# The coarsened gradients of the differences of the minimizers, by the energy defect

The deterministic part of Lemma 5.5 of Armstrong and Dario, summed over the subcubes, in every
dimension `d ≥ 1`. Let `U` be a triadic cube resolved by the partition, `n ≤ scale U`, and for each
resolved subcube `V` of scale `n` let `w_V = u(·, U, q)|_V - u(·, V, q)`. If every such `V`
satisfies the hypotheses of `latticeEdgePairing_innerCubeCells_sq_le` (partition scales less than
`j` on `V`, the Meyers estimate for `w_V` on the cells of scale `j` of the inner cube, the bounds
`A` on the cell averages of the weight and `W` on the weight), then

`∑_V ⟨∇[w_V]_𝒫, g⟩_V² ≤ 2 Λ D_n(U, q)`,
`Λ = 4d G² 3^{dn} K² A C_M^{1/p} 3^d + 16 d² G² 3^{(d-1)n + j} K² W^{2d-1}`,

where `D_n(U, q) = ∑_V B(w_V, w_V)/2` is the energy of the differences of Lemma 5.4
(`cubeMuDefect`), as in the two-dimensional
`Rigidity.Proofs.Cluster.sum_edgePairing_sq_le_planarMuDefect`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The constant `Λ` of the deterministic part of Lemma 5.5. -/
noncomputable def restrictQuadConst (d n j : ℕ) (G A CM p W : ℝ) : ℝ :=
  4 * d * G ^ 2 * ((3 : ℝ) ^ n) ^ d *
      (partitionCoarseGradConst d ^ 2 * (A * (CM ^ (1 / p) * ((3 ^ d : ℕ) : ℝ)))) +
    16 * d ^ 2 * G ^ 2 * ((3 : ℝ) ^ n) ^ (d - 1) * 3 ^ j *
      (partitionCoarseGradConst d ^ 2 * W ^ (2 * d - 1))

/-- **The coarsened gradients of the differences of the minimizers, by the energy defect**
(Armstrong and Dario, Lemma 5.5, deterministic part, every dimension `d ≥ 1`). -/
theorem sum_latticeEdgePairing_sq_le_cubeMuDefect (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {n j : ℕ} (hj : j < n) (q : Fin d → ℝ)
    {g : Vertex d → Fin d → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex d → ℝ)
    (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z) {W : ℝ}
    {p r CM A : ℝ} (hpr : p.HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (hV : ∀ V ∈ U.resolvedSubcubesAt ω n,
      (∀ x ∈ V.vertices, (partitionCube ω x).scale < j) ∧
      (∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W) ∧
      (∀ c ∈ innerCubeCells V j,
        avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ^ (1 / r) ≤ A) ∧
      (∀ c ∈ innerCubeCells V j, avg (cube c.1 c.2) (fun x =>
          clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V
            (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)) x ^ p) ≤
        CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V
            (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q))) ^ p)) :
    ∑ V ∈ U.resolvedSubcubesAt ω n,
        latticeEdgePairing V.toIntegerCube.vertices g (fun x => cubeExtend ω V
          (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)
            (partitionAnchor ω x)) ^ 2 ≤
      2 * (restrictQuadConst d n j G A CM p W * cubeMuDefect ω U n q) := by
  set Λ := restrictQuadConst d n j G A CM p W with hΛ
  have hterm : ∀ V ∈ U.resolvedSubcubesAt ω n,
      latticeEdgePairing V.toIntegerCube.vertices g (fun x => cubeExtend ω V
          (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)
            (partitionAnchor ω x)) ^ 2 ≤
        2 * (Λ * (cubeForm ω V
          (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)
          (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q) / 2)) := by
    intro V hVf
    have hVr : PartitionResolved ω V := (mem_resolvedSubcubesAt.1 hVf).2
    have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt (mem_resolvedSubcubesAt.1 hVf).1
    obtain ⟨hres, hW, hA, hM⟩ := hV V hVf
    have h := latticeEdgePairing_innerCubeCells_sq_le hd hP hVr (by omega : j < V.scale) hres
      (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q) hg Wt hWt hW
      hpr hCM hA0 hA hM
    rw [hVs] at h
    refine h.trans (le_of_eq ?_)
    rw [hΛ, restrictQuadConst]
    ring
  have hdef : cubeMuDefect ω U n q = ∑ V ∈ U.resolvedSubcubesAt ω n,
      cubeForm ω V (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)
        (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q) / 2 := by
    rw [cubeMuDefect, if_pos ⟨hP, hU⟩]
  calc ∑ V ∈ U.resolvedSubcubesAt ω n,
        latticeEdgePairing V.toIntegerCube.vertices g (fun x => cubeExtend ω V
          (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)
            (partitionAnchor ω x)) ^ 2
      ≤ ∑ V ∈ U.resolvedSubcubesAt ω n,
          2 * (Λ * (cubeForm ω V
            (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)
            (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q) / 2)) :=
        Finset.sum_le_sum hterm
    _ = 2 * (Λ * cubeMuDefect ω U n q) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, hdef]

end Rigidity.Percolation

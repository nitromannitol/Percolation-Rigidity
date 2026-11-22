import Rigidity.Proofs.Cluster.PlanarInnerCells
import Rigidity.Proofs.Percolation.PlanarMuEnergyDefect

/-!
# The coarsened gradients of the differences of the minimizers, by the energy defect

The deterministic part of Lemma 5.5 of Armstrong and Dario, in dimension two, summed over the
subcubes. Let `U` be a triadic cube, `n ≤ scale U`, and for each resolved subcube `V` of scale `n`
let `w_V = u(·, U, q)|_V - u(·, V, q)`. If every such `V` satisfies the hypotheses of
`edgePairing_innerCells_sq_le` (partition scales at most `j` on `V`, the Meyers estimate for `w_V`
on the cells of scale `j` of the inner square, the bounds `A` on the cell averages of the weight and
`W` on the weight), then
`∑_V ⟨∇[w_V]_𝒫, g⟩_V² ≤ 2 Λ D_n(U, q)`, `Λ = 8 G² 9^n C² A C_M^{1/p} 9 + 64 G² 3^{n+j} C² W³`,
where `D_n(U, q) = ∑_V B(w_V, w_V)/2` is the energy of the differences of Lemma 5.4
(`planarMuDefect`). Taking expectations on the event where these hypotheses hold, Lemma 5.4
(`exists_lintegral_planarMuDefect_le`) bounds the left side; off this event the second moments of
the coarse energies (`exists_lintegral_coarse_minimizer_sq_le`) and its probability are used.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- **The coarsened gradients of the differences of the minimizers, by the energy defect**
(Armstrong and Dario, Lemma 5.5, deterministic part, with the repaired Step 3, in dimension two).
-/
theorem sum_edgePairing_sq_le_planarMuDefect (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    {n j : ℕ} (hj : j < n) (q : Fin 2 → ℝ) {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ}
    (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex 2 → ℝ)
    (hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z)) {W : ℝ}
    {p r CM A : ℝ} (hpr : p.HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (hV : ∀ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
      (∀ x ∈ V.vertices, (planarPartCube ω x).scale ≤ j) ∧
      (∀ z ∈ clusterVertices ω V, 3 * planarReach ω z ≤ ENNReal.ofReal W) ∧
      (∀ c ∈ innerCells V j, avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r) ≤ A) ∧
      (∀ c ∈ innerCells V j, avg (cube c.1 c.2) (fun x =>
          clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V
            (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q)) x ^ p) ≤
        CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V
            (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q))) ^ p)) :
    ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
        edgePairing V.toIntegerCube.vertices g (fun x => clusterExtend ω V
          (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q)
            (planarCoarseAnchor ω x)) ^ 2 ≤
      2 * ((8 * G ^ 2 * 9 ^ n *
          ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
            (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 *
            (A * (CM ^ (1 / p) * ((9 : ℕ) : ℝ)))) +
        64 * G ^ 2 * 3 ^ (n + j) *
          ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
            (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 * W ^ 3)) *
        planarMuDefect ω U n q) := by
  set Λ : ℝ := 8 * G ^ 2 * 9 ^ n *
      ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
        (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 *
        (A * (CM ^ (1 / p) * ((9 : ℕ) : ℝ)))) +
    64 * G ^ 2 * 3 ^ (n + j) *
      ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
        (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 * W ^ 3) with hΛ
  have hterm : ∀ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
      edgePairing V.toIntegerCube.vertices g (fun x => clusterExtend ω V
          (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q)
            (planarCoarseAnchor ω x)) ^ 2 ≤
        2 * (Λ * (clusterForm ω V
          (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q)
          (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q) / 2)) := by
    intro V hVf
    have hVr : PlanarResolved ω V := (Finset.mem_filter.1 hVf).2
    have hVs : V.scale = n := scale_of_mem_subcubesAt (Finset.mem_filter.1 hVf).1
    obtain ⟨hres, hW, hA, hM⟩ := hV V hVf
    have h := edgePairing_innerCells_sq_le hP hVr (by omega : j < V.scale) hres
      (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q) hg Wt hWt hW
      hpr hCM hA0 hA hM
    rw [hVs] at h
    refine h.trans (le_of_eq ?_)
    rw [hΛ]
    ring
  calc ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
        edgePairing V.toIntegerCube.vertices g (fun x => clusterExtend ω V
          (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q)
            (planarCoarseAnchor ω x)) ^ 2
      ≤ ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
          2 * (Λ * (clusterForm ω V
            (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q)
            (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q) / 2)) :=
        Finset.sum_le_sum hterm
    _ = 2 * (Λ * planarMuDefect ω U n q) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, planarMuDefect]

end Rigidity.Proofs.Cluster

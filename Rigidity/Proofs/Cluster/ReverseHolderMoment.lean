import Rigidity.Proofs.Cluster.ReverseHolderPartition
import Rigidity.Proofs.Cluster.SobolevCube

/-!
# The reverse Hölder inequality on a resolved cube given the moment bound

Armstrong–Dario, Lemma 3.6, deterministic part, for the partition into good cubes, in every
dimension `d ≥ 2`. The Sobolev inequality on the crossing cluster (Proposition 3.4 with `s = 2`)
follows from the lattice Sobolev–Poincaré inequality with the exponents `2` and `2_* = 2d/(d+2)`,
which holds on every integer cube (`IntegerCube.exists_latticeSobolevOn`). Hence the only remaining
hypotheses of `reverse_holder_partition_cube` are:

* the triadic cube `□_{m+1} = ⟨m + 1, c⟩` is resolved by the partition into good cubes;
* the moment bound `∑_{z ∈ 𝒞_*(□_{m+1})} (3^{ρ(z)})^{2ds} ≤ C_G |□_{m+1}|` of the reach scales `ρ`
  of the coarse-graining data (in the source, the scale condition `3^m ≥ 𝓜_{2sd}(𝒫)`);
* `u` is harmonic on `𝒞_*(□_{m+1})`.

Under these, `reverse_holder_partition_cube_of_moment` bounds the energy of `u` on the points of
`𝒞_*(□_{m+1})` in the central subcube `□_m` by the `s' 2_*` energy on `𝒞_*(□_{m+1})`, with a constant
depending only on `d`, `C_G` and `s`; `reverse_holder_partition_of_moment` is the case of the cube
centered at the origin.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped BigOperators Classical

variable {d : ℕ}

/-- The lattice Sobolev–Poincaré inequality with the exponents `2` and `2_*` on every integer cube
of positive side, in every dimension `d ≥ 2`. -/
theorem exists_latticeSobolevOn_two (hd : 2 ≤ d) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ B : IntegerCube d, 0 < B.size →
      LatticeSobolevOn B.vertices 2 (lowerSobolevTwo d) S := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hs : (d : ℝ) / (d - 1) ≤ 2 := by
    rw [div_le_iff₀ hdm]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ht : lowerSobolevTwo d = 2 * d / (2 + d) := by
    rw [lowerSobolevTwo, add_comm (d : ℝ) 2]
  exact IntegerCube.exists_latticeSobolevOn hd hs ht

/-- **Reverse Hölder inequality on the crossing cluster of a resolved triadic cube, given the moment
bound of the reach scales** (Armstrong–Dario, Lemma 3.6, deterministic part, for the partition into
good cubes), in every dimension `d ≥ 2`: the Sobolev hypothesis of `reverse_holder_partition_cube`
is discharged. -/
theorem reverse_holder_partition_cube_of_moment (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (m : ℕ) (c : Vertex d)
      (hU : PartitionResolved ω ⟨m + 1, c⟩),
      ∀ {CG s t : ℝ}, 0 ≤ CG → s.HolderConjugate t →
      ∑ z ∈ crossingClusterVertices ω ⟨m + 1, c⟩,
          ((3 : ℝ) ^ (partitionCoarseData (by omega) hP ⟨m + 1, c⟩ hU).reachScale z) ^
            (2 * (d : ℝ) * s) ≤ CG * (3 : ℝ) ^ ((m + 1) * d) →
      ∀ u : Vertex d → ℝ, (∀ x ∈ crossingClusterVertices ω ⟨m + 1, c⟩,
          (∀ y, (openGraph ω).Adj x y → y ∈ crossingClusterVertices ω ⟨m + 1, c⟩) →
            openLaplacian ω u x = 0) →
      (1 / (3 : ℝ) ^ (m * d)) * ∑ x ∈ (crossingClusterVertices ω ⟨m + 1, c⟩).filter
          (· ∈ cube m (centralPoint m c)),
          clusterGradSq ω (crossingClusterVertices ω ⟨m + 1, c⟩) u x ≤
        8 * d * K * CG ^ (2 / (s * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
          ((1 / (3 : ℝ) ^ ((m + 1) * d)) * ∑ x ∈ crossingClusterVertices ω ⟨m + 1, c⟩,
            clusterGradSq ω (crossingClusterVertices ω ⟨m + 1, c⟩) u x ^
              (t * lowerSobolevTwo d / 2)) ^ (2 / (t * lowerSobolevTwo d)) := by
  obtain ⟨S, hS, hLS⟩ := exists_latticeSobolevOn_two hd
  obtain ⟨K, hK0, hK⟩ := reverse_holder_partition_cube hd hS
  refine ⟨K, hK0, fun ω hP m c hU => hK ω hP m c hU (hLS _ ?_)⟩
  show 0 < 3 ^ (m + 1)
  positivity

/-- **Reverse Hölder inequality on the crossing cluster of the resolved cube centered at the origin,
given the moment bound of the reach scales** (Armstrong–Dario, Lemma 3.6, deterministic part, for the
partition into good cubes), in every dimension `d ≥ 2`. -/
theorem reverse_holder_partition_of_moment (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (m : ℕ)
      (hU : PartitionResolved ω ⟨m + 1, 0⟩),
      ∀ {CG s t : ℝ}, 0 ≤ CG → s.HolderConjugate t →
      ∑ z ∈ crossingClusterVertices ω ⟨m + 1, 0⟩,
          ((3 : ℝ) ^ (partitionCoarseData (by omega) hP ⟨m + 1, 0⟩ hU).reachScale z) ^
            (2 * (d : ℝ) * s) ≤ CG * (3 : ℝ) ^ ((m + 1) * d) →
      ∀ u : Vertex d → ℝ, (∀ x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩,
          (∀ y, (openGraph ω).Adj x y → y ∈ crossingClusterVertices ω ⟨m + 1, 0⟩) →
            openLaplacian ω u x = 0) →
      (1 / (3 : ℝ) ^ (m * d)) * ∑ x ∈ (crossingClusterVertices ω ⟨m + 1, 0⟩).filter
          (· ∈ cube m (0 : Vertex d)),
          clusterGradSq ω (crossingClusterVertices ω ⟨m + 1, 0⟩) u x ≤
        8 * d * K * CG ^ (2 / (s * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
          ((1 / (3 : ℝ) ^ ((m + 1) * d)) * ∑ x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩,
            clusterGradSq ω (crossingClusterVertices ω ⟨m + 1, 0⟩) u x ^
              (t * lowerSobolevTwo d / 2)) ^ (2 / (t * lowerSobolevTwo d)) := by
  obtain ⟨S, hS, hLS⟩ := exists_latticeSobolevOn_two hd
  obtain ⟨K, hK0, hK⟩ := reverse_holder_partition hd hS
  refine ⟨K, hK0, fun ω hP m hU => hK ω hP m hU (hLS _ ?_)⟩
  show 0 < 3 ^ (m + 1)
  positivity

end Rigidity.Proofs.Cluster

import Rigidity.Proofs.Cluster.SobolevCube
import Rigidity.Proofs.Cluster.ReverseHolderSobolev

/-!
# The Sobolev hypothesis of the reverse Hölder inequality in every dimension

The hypothesis `Rigidity.Proofs.Cluster.ClusterSobolevTwo` of the reverse Hölder inequality
(Armstrong and Dario, Lemma 3.6) is Proposition 3.4 with `s = 2` for functions of mean zero on the crossing cluster. In
every dimension `d ≥ 2` it holds on the crossing cluster of every triadic cube resolved by the
partition into good cubes, with the weight `3^{ρ(z)}` of the reach scale: the lattice
Sobolev–Poincaré inequality with the exponents `2` and `2_* = 2d/(d+2)` holds on every integer
cube.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Proposition 3.4 of Armstrong and Dario with `s = 2`, in the form of the Sobolev hypothesis
of the reverse Hölder inequality**, in every dimension `d ≥ 2`. -/
theorem exists_clusterSobolevTwo (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (U : TriadicCube d)
      (hU : PartitionResolved ω U),
      Rigidity.Proofs.Cluster.ClusterSobolevTwo ω (crossingClusterVertices ω U)
        (fun z => (3 : ℝ) ^ (partitionCoarseData (by omega) hP U hU).reachScale z) K := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hs : (d : ℝ) / (d - 1) ≤ 2 := by
    rw [div_le_iff₀ hdm]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ht : Rigidity.Proofs.Cluster.lowerSobolevTwo d = 2 * d / (2 + d) := by
    rw [Rigidity.Proofs.Cluster.lowerSobolevTwo, add_comm (d : ℝ) 2]
  obtain ⟨S, hS, hLS⟩ := IntegerCube.exists_latticeSobolevOn hd hs ht
  obtain ⟨K, hK, h⟩ := Rigidity.Proofs.Cluster.clusterSobolevTwo_of_latticeSobolevOn hd hS
  refine ⟨K, hK, fun ω hP U hU => h ω hP U hU (hLS _ ?_)⟩
  show 0 < 3 ^ U.scale
  positivity

end Rigidity.Percolation

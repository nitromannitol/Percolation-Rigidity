import Rigidity.Proofs.Partition.AlmostSure
import Rigidity.Percolation.TriadicStochasticBound

/-!
# The size of the partition cubes

Armstrong and Dario, the first bound displayed after Definition 2.9: the size of the partition cube of a
vertex satisfies `size(𝒫(x)) ≤ 𝒪₁(C)` uniformly in `x`, in the tail form of the stochastic
notation: `P[size(𝒫(x)) > t θ] ≤ exp(-t)` for every `t ≥ 1`. The size is the stopping size, the
side of the partition cube on the partition event.
-/

namespace Rigidity.Percolation

open LatticeProb LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **The size of the partition cubes is `𝒪₁(θ)`** uniformly in the vertex. -/
theorem exists_osBound_stoppingSize [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d, OsBound (latticeBondLaw d p) 1 θ
      (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) := by
  obtain ⟨C1, c, hC1, hc, hq⟩ := exists_measure_not_mem_goodCubes_le hd hpc
  have hprob : ∀ R : TriadicCube d, latticeBondLaw d p {ω | R ∉ TriadicCube.goodCubes ω} ≤
      ENNReal.ofReal C1 * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ R.scale) ^ (1 : ℝ))) := by
    intro R
    rw [Real.rpow_one, ← ENNReal.ofReal_mul hC1]
    exact hq R
  obtain ⟨θ, hθ, h⟩ := TriadicCube.uniform_osBound_of_stopping_side (latticeBondLaw d p)
    TriadicCube.goodCubes (ENNReal.ofReal C1) ENNReal.ofReal_ne_top 1 c one_pos hc hprob
  exact ⟨θ, hθ, fun x => h x _ (fun ω => TriadicCube.stoppingSize_nonneg _ x)
    (fun ω => TriadicCube.exists_stopping_of_stoppingSize_pos _ x)⟩

/-- On the partition event the stopping size is the side of the partition cube. -/
theorem stoppingSize_goodCubes_eq {ω : Configuration d} (hP : PartitionEvent ω) (x : Vertex d) :
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x = (3 : ℝ) ^ (partitionCube ω x).scale :=
  TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP x) (partitionCube_spec hP x).2

end Rigidity.Percolation

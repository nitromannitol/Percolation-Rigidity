import Rigidity.Proofs.Percolation.PlanarNuStationarity
import Rigidity.Proofs.Percolation.PlanarTranslation

/-!
# Dario's stationary partitions and the estimate (3.3)

For the proof of Lemma 3.2, Dario applies the partition construction of Proposition 2.1 to the
collection `𝒢_stat^k = 𝒢 ∪ ⋃_{n ≥ k} 𝒯_n` of the good cubes and all the triadic cubes of scale at
least `k`. For the planar good cubes this is the partition capped at scale `k`,
`TriadicCube.cappedCube (planarGoodCubes ω) k`: every vertex lies in a unique maximal stopping
cube of `TriadicCube.capped (planarGoodCubes ω) k = 𝒢_stat^k`
(`TriadicCube.existsUnique_isMaximalStopping_capped`), of scale at most `k`, and the partition is
`3^k ℤ²`-stationary, Dario's (3.2)
(`cappedCube_planarGoodCubes_translation`).

* `dario_errorstatpart`: **(3.3)**, `P[∃ x ∈ □, □_𝒫(x) ≠ □_{𝒫_stat^k}(x)] ≤ C exp(-c 3^k)` for
  every triadic cube `□` of scale `k`, from the localization of the planar partition
  (`exists_measure_planarCappedDiscrepancy_le`, Armstrong and Dario, Proposition 4.9, in dimension
  two): a change of stopping cube is witnessed by a nearby cube of scale at least `k` which is
  not good.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- **Dario, (3.3)**: the planar partition and the partition capped at the scale `k` of a triadic
cube `□` agree on `□` outside an event of probability at most `C exp(-c 3^k)`. -/
theorem dario_errorstatpart {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ V : TriadicCube 2,
      latticeBondLaw 2 p {ω | ∃ x ∈ V.vertices,
        planarPartCube ω x ≠ TriadicCube.cappedCube (planarGoodCubes ω) V.scale x} ≤
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_measure_planarCappedDiscrepancy_le hpc
  refine ⟨C, hC, c, hc, fun V => (measure_mono_ae ?_).trans (h V)⟩
  filter_upwards [ae_planarPartitionEvent hpc] with ω hP
  intro hω
  obtain ⟨x, hx, hne⟩ := hω
  exact ⟨x, hx, planarPartCube ω x, (planarPartCube_spec hP x).1, (planarPartCube_spec hP x).2,
    hne⟩

end Rigidity.Percolation

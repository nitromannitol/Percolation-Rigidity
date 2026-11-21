import Rigidity.External.PlanarInputs
import Rigidity.Proofs.Section5.GreenSymmetry
import Rigidity.Proofs.Section5.LogGrowth

/-!
# Planar Green asymptotics and symmetry

The potential asymptotics, Green symmetry and logarithmic growth use only the planar Green
quantitative estimate.
-/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- Planar potential asymptotics from the planar quantitative Green estimate. -/
theorem potentialAsymptotic_two (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    PotentialAsymptotic p := by
  obtain ⟨κ, hκ, K, _, hK⟩ := hGQ p hp hp1
  obtain ⟨Cst, s, -, -, hy⟩ := hK 1 one_pos
  refine ⟨⟨κ, hκ⟩, fun f hf => ?_⟩
  have hae : ∀ y : Vertex 2, ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ g : uniqueInfiniteComponent h → ℝ,
          IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
          ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
            ∀ x : uniqueInfiniteComponent h,
              ∀ z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0},
                z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y →
                R ≤ ‖latticeEuclideanEmbedding x.val‖ →
                |g x - continuumGreen 2 le_rfl ⟨κ, hκ⟩ z - K y ω| ≤ ε := by
    intro y
    obtain ⟨M, -, -, -, hM⟩ := (hy y).2
    exact hM.mono fun ω hω h hy g hg => (hω h hy g hg).1
  filter_upwards [ae_all_iff.2 hae] with ω hω h
  refine ⟨_, fun G hG => tendsto_potential_sub_mass_mul_greenLog _ _ G
    (fun y => K y.val ω) f hf fun y => ?_⟩
  exact tendsto_column_sub_greenLog _ _ y _ _ (hω y.val h y.prop _ (hG y))

/-- Planar Green symmetry from the planar quantitative Green estimate. -/
theorem greenSymmetry_two (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GreenSymmetry p :=
  greenSymmetry_of_potentialAsymptotic (potentialAsymptotic_two hGQ hp hp1)

/-- Logarithmic potential growth from planar Green asymptotics. -/
theorem logGrowth_two (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ) :
    LogGrowthStmt p f :=
  logGrowth_of_steps (uniqueClusterAe hUq hp hp1) (potentialAsymptotic_two hGQ hp hp1)
    (asymptoticLogBounds_of_logNormComparison
      (logNormComparison_of_normComparison normComparison)) f

end Rigidity.Proofs.Section5

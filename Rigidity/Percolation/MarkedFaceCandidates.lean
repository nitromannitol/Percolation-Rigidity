import Rigidity.Percolation.FaceSeedCandidateAbundance
import Rigidity.Percolation.ConditionalBondCandidates

/-!
# Uniform-mark candidates for outward seed connections

Thresholding exterior marks produces the same seed targets and boundary
candidates as Bernoulli bond percolation. Opening one such boundary candidate
joins the explored set to an exterior path toward an outward seed.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- Boundary candidates toward outward seed targets in the thresholded field. -/
noncomputable def markedFaceSeedCandidates {d : ℕ} (p : unitInterval)
    (M n : ℕ) (i : Fin d) (R : Finset (Vertex d)) (ω : BondMarks d) : Finset (Bond d) :=
  boundaryCandidateBonds R (centeredBondCube n) (vertexCutBonds R)
    (faceSeedTargets (centeredCubeOrthantFace n i (fun _ => true)) (2 * M + 1) i n)
    (thresholdBondMarks p ω)

/-- The candidate set is determined without revealing boundary marks. -/
theorem measurable_markedFaceSeedCandidates {d : ℕ} (p : unitInterval)
    (M n : ℕ) (i : Fin d) (R : Finset (Vertex d))
    (hR : (R : Set (Vertex d)) ⊆ centeredBondCube n)
    (hface : ∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) :
    @Measurable _ _ (bondMarkSigma (↑(vertexCutBonds R) : Set (Bond d))ᶜ) _
      (markedFaceSeedCandidates p M n i R) := by
  have hK := measurable_faceSeedTargets_exterior R n (2 * M + 1) i hR
    (centeredCubeOrthantFace n i (fun _ => true)) hface
  have hU := measurable_boundaryCandidateBonds R (centeredBondCube n)
    (finite_centeredBondCube n) (vertexCutBonds R) _ hK
    (localBonds_sdiff_subset_vertexCutBonds_compl R (centeredBondCube n))
  exact hU.comp (measurable_thresholdBondMarks_bondSigma p _)

/-- Thresholding all marks preserves the probability of any measurable bond
configuration event. -/
theorem bondMarkLaw_real_threshold_preimage {d : ℕ} (p : unitInterval)
    {A : Set (Configuration d)} (hA : MeasurableSet A) :
    (bondMarkLaw d).real (thresholdBondMarks p ⁻¹' A) = (latticeBondLaw d p).real A := by
  have hm : Measurable (thresholdBondMarks (d := d) p) := by
    apply measurable_pi_lambda
    intro e
    exact (measurable_markThreshold p).comp (measurable_pi_apply e)
  rw [measureReal_def, ← Measure.map_apply hm hA, bondMarkLaw_map_thresholdBondMarks]
  rfl

/-- An explored-region exit followed by a `p`-open exterior path to an
outward seed target, with the exit bond opened at its raised threshold. -/
def markedFaceSeedExit {d : ℕ} (p : unitInterval) (M n : ℕ) (i : Fin d)
    (R : Finset (Vertex d)) (β : Bond d → unitInterval) (δ : ℝ) : Set (BondMarks d) :=
  {ω | ∃ x ∈ R, ∃ y ∈ centeredBondCube n \ (R : Set (Vertex d)),
    ∃ hxy : (nearestNeighborGraph d).Adj x y,
      (ω (bondOfAdjacent hxy) : ℝ) ≤ (β (bondOfAdjacent hxy) : ℝ) + δ ∧
      ∃ z ∈ faceSeedTargets (centeredCubeOrthantFace n i (fun _ => true))
        (2 * M + 1) i n (thresholdBondMarks p ω),
        z ∈ centeredBondCube n \ (R : Set (Vertex d)) ∧
        (openIn (thresholdBondMarks p ω) (centeredBondCube n \ (R : Set (Vertex d)))).Reachable y z}

/-- Opening a selected candidate gives the corresponding marked exit and
exterior path to an outward seed target. -/
theorem selectedBondMarkSuccess_subset_markedFaceSeedExit {d : ℕ} (p : unitInterval)
    (M n : ℕ) (i : Fin d) (R : Finset (Vertex d)) (β : Bond d → unitInterval)
    (δ : ℝ) (hδ : 0 ≤ δ) (hβ : ∀ e, (β e : ℝ) + δ ≤ 1) :
    selectedBondMarkSuccess (markedFaceSeedCandidates p M n i R) β δ hδ hβ ⊆
      markedFaceSeedExit p M n i R β δ := by
  intro ω hω
  obtain ⟨e, he, hopen⟩ := hω
  obtain ⟨_, x, hx, y, hy, hxy, heq, z, hz, hzout, hpath⟩ :=
    (mem_boundaryCandidateBonds R (centeredBondCube n) (vertexCutBonds R)
      (faceSeedTargets (centeredCubeOrthantFace n i (fun _ => true)) (2 * M + 1) i n)
      (thresholdBondMarks p ω) e).mp he
  subst e
  refine ⟨x, hx, y, hy, hxy, ?_, z, hz, hzout, hpath⟩
  have hle : ω (bondOfAdjacent hxy) ≤
      (⟨(β (bondOfAdjacent hxy) : ℝ) + δ,
        add_nonneg (β (bondOfAdjacent hxy)).property.1 hδ, hβ _⟩ : unitInterval) := by
    simpa only [raisedBondThreshold, he, ↓reduceIte] using hopen
  exact hle

end Rigidity.Percolation

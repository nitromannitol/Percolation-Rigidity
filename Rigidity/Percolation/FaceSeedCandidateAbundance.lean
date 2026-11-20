import Rigidity.Percolation.FaceSeedTargets

/-!
# Abundant candidate exits toward seed targets

A high-probability connection to an outward seed implies that every finite
explored region containing the central seed has many boundary bonds leading
to those targets, provided its boundary is hidden from the target field.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

/-- Uniformly over explored sets containing the central seed and avoiding the
face, there are more than `t` exterior-reaching boundary candidates with
arbitrarily high probability. -/
theorem exists_faceSeed_many_boundaryCandidates {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (t : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      ∀ R : Finset (Vertex d), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        (latticeBondLaw d p).real {ω | (boundaryCandidateBonds R (centeredBondCube n)
          (vertexCutBonds R) (faceSeedTargets (centeredCubeOrthantFace n i (fun _ => true))
            (2 * M + 1) i n) ω).card ≤ t} < ε := by
  let c : ℝ := (1 - (p : ℝ)) ^ t
  have hc : 0 < c := pow_pos (sub_pos.mpr hp1) _
  obtain ⟨M, hMpos, hM⟩ :=
    exists_seed_eventually_singleFieldFaceSuccess_of_supercritical p hp i (ε * c) (mul_pos hε hc)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hM
  let a := max N (M + 1)
  let n := M + a
  have ha : N ≤ a := le_max_left _ _
  have hn : 2 * M < n := by dsimp [n, a]; omega
  refine ⟨M, n, hMpos, hn, ?_⟩
  intro R hseed hR hface
  let face := centeredCubeOrthantFace n i (fun _ => true)
  let K := faceSeedTargets face (2 * M + 1) i n
  let C := singleFieldSeedFaceSuccess (centeredBondCube n) (centeredBondCubeFinset M)
    face (2 * M + 1) i n
  let T : Set (Configuration d) := {ω | ∃ x ∈ R, ∃ z ∈ K ω,
    z ∈ centeredBondCube n \ (R : Set (Vertex d)) ∧
      (openIn ω (centeredBondCube n)).Reachable x z}
  have hK := measurable_faceSeedTargets_exterior R n (2 * M + 1) i hR face hface
  have hbound := measureReal_few_candidates_le_not_reachable p hp1 R (centeredBondCube n)
    (finite_centeredBondCube n) hR K t hK
  change (latticeBondLaw d p).real {ω | (boundaryCandidateBonds R (centeredBondCube n)
    (vertexCutBonds R) K ω).card ≤ t} ≤ (latticeBondLaw d p).real Tᶜ / c at hbound
  have hCT : C ⊆ T := singleFieldSeedFaceSuccess_subset_reachable_targets M n i R hseed hface
  have hfail : (latticeBondLaw d p).real Tᶜ ≤ 1 - (latticeBondLaw d p).real C := by
    calc
      _ ≤ (latticeBondLaw d p).real Cᶜ :=
        measureReal_mono (Set.compl_subset_compl.mpr hCT) (measure_ne_top _ _)
      _ = _ := by rw [measureReal_compl (measurableSet_singleFieldSeedFaceSuccess _ _ _ _ _ _),
        probReal_univ]
  have hsuccess : 1 - ε * c < (latticeBondLaw d p).real C := hN a ha
  apply hbound.trans_lt
  apply (div_lt_iff₀ hc).mpr
  linarith

end Rigidity.Percolation

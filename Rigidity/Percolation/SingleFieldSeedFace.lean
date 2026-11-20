import Rigidity.Percolation.SeedFaceHighProbability

/-!
# Outward seeds in a single bond configuration

The union of a supercritical base field and an independent sprinkling has the
Bernoulli bond law. A base-connected, added-open trial is also an open trial in
the union configuration.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

/-- A seed is connected inside the region to a face contact whose outward
trial is fully open in the same configuration. -/
def singleFieldSeedFaceSuccess {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (k : ℕ) (j : Fin d) (n : ℤ) :
    Set (Configuration d) :=
  {ω | ∃ y ∈ roots, ∃ x ∈ face, (openIn ω B).Reachable y x ∧
    ω ∈ fullyOpenRegion (faceSeedTrial k j n x)}

/-- The single-field seed-face success event is measurable. -/
theorem measurableSet_singleFieldSeedFaceSuccess {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (k : ℕ) (j : Fin d) (n : ℤ) :
    MeasurableSet (singleFieldSeedFaceSuccess B roots face k j n) := by
  have heq : singleFieldSeedFaceSuccess B roots face k j n =
      ⋃ y ∈ roots, ⋃ x ∈ face, {ω | (openIn ω B).Reachable y x} ∩
        fullyOpenRegion (faceSeedTrial k j n x) := by
    ext ω
    simp only [singleFieldSeedFaceSuccess, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor <;> rintro ⟨y, hy, x, hx, hpath, hopen⟩ <;>
      exact ⟨y, hy, x, hx, hpath, hopen⟩
  rw [heq]
  exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
      (measurableSet_openIn_reachable B y x).inter
        (bondSigma_le (localBonds (faceSeedTrial k j n x)) _
          (measurableSet_fullyOpenRegion_localBond (faceSeedTrial k j n x)))

/-- A successful base-and-sprinkling trial gives success in the union field. -/
theorem seedReachableFaceSuccess_subset_sprinkled {d : ℕ} (B : Set (Vertex d))
    (roots face : Finset (Vertex d)) (k : ℕ) (j : Fin d) (n : ℤ) :
    seedReachableFaceSuccess B roots face k j n ⊆
      sprinkledBondConfiguration ⁻¹' singleFieldSeedFaceSuccess B roots face k j n := by
  intro ω hω
  obtain ⟨y, hy, x, hx, hpath, htrial⟩ :=
    Set.mem_iUnion.mp hω |>.imp fun _ h => Set.mem_iUnion.mp h
  have hle : baseBondConfiguration ω ≤ sprinkledBondConfiguration ω := by
    intro e
    change (ω e).1 ≤ ((ω e).1 || (ω e).2)
    cases (ω e).1 <;> cases (ω e).2 <;> decide
  exact ⟨y, hy, x, hx, hpath.mono (openIn_mono_configuration hle B),
    sprinkled_fullyOpenRegion_of_added htrial⟩

/-- A supercritical base and positive sprinkling yield an outward open trial
with arbitrarily high probability under their combined Bernoulli law. -/
theorem exists_seed_eventually_singleFieldFaceSuccess {d : ℕ} (q r : unitInterval)
    (hq : (q : ℝ) < 1) (hθ : 0 < LatticeProb.Percolation.theta d q)
    (hr : 0 < (r : ℝ)) (i : Fin d) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧ ∀ᶠ n in atTop,
      1 - η < (latticeBondLaw d (sprinkledDensity q r)).real (singleFieldSeedFaceSuccess
        (centeredBondCube (M + n)) (centeredBondCubeFinset M)
        (centeredCubeOrthantFace (M + n) i (fun _ => true)) (2 * M + 1) i (M + n)) := by
  haveI : IsProbabilityMeasure (bondPairLaw d q r) := by
    dsimp only [bondPairLaw]
    infer_instance
  obtain ⟨M, hMpos, hM⟩ := exists_seed_eventually_faceSuccess q r hq hθ hr i η hη
  refine ⟨M, hMpos, ?_⟩
  filter_upwards [hM] with n hn
  have hsprinkled : Measurable (@sprinkledBondConfiguration d) := by
    apply measurable_pi_lambda
    intro e
    change Measurable (fun ω : Bond d → Bool × Bool => (ω e).1 || (ω e).2)
    fun_prop
  have hmeas := measurableSet_singleFieldSeedFaceSuccess (centeredBondCube (M + n))
    (centeredBondCubeFinset M) (centeredCubeOrthantFace (M + n) i (fun _ => true))
    (2 * M + 1) i (M + n)
  have hmap : (bondPairLaw d q r).real (sprinkledBondConfiguration ⁻¹'
      singleFieldSeedFaceSuccess (centeredBondCube (M + n)) (centeredBondCubeFinset M)
        (centeredCubeOrthantFace (M + n) i (fun _ => true)) (2 * M + 1) i (M + n)) =
      (latticeBondLaw d (sprinkledDensity q r)).real (singleFieldSeedFaceSuccess
        (centeredBondCube (M + n)) (centeredBondCubeFinset M)
        (centeredCubeOrthantFace (M + n) i (fun _ => true)) (2 * M + 1) i (M + n)) := by
    rw [measureReal_def, ← Measure.map_apply hsprinkled hmeas, bondPairLaw_map_sprinkled]
    rfl
  apply hn.trans_le
  rw [← hmap]
  exact measureReal_mono (seedReachableFaceSuccess_subset_sprinkled _ _ _ _ _ _)
    (measure_ne_top _ _)

/-- Above the critical probability, a centered seed connects to an outward
open trial with arbitrarily high probability on every sufficiently large
positive orthant face. -/
theorem exists_seed_eventually_singleFieldFaceSuccess_of_supercritical {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (i : Fin d)
    (η : ℝ) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧ ∀ᶠ n in atTop,
      1 - η < (latticeBondLaw d p).real (singleFieldSeedFaceSuccess
        (centeredBondCube (M + n)) (centeredBondCubeFinset M)
        (centeredCubeOrthantFace (M + n) i (fun _ => true)) (2 * M + 1) i (M + n)) := by
  obtain ⟨q, r, hθ, hqp, hr, hsum⟩ := exists_supercritical_bond_sprinkling p hp
  have hq : (q : ℝ) < 1 := hqp.trans_le p.property.2
  have hdensity : sprinkledDensity q r = p := Subtype.ext hsum
  simpa only [hdensity] using
    exists_seed_eventually_singleFieldFaceSuccess q r hq hθ hr i η hη

end Rigidity.Percolation

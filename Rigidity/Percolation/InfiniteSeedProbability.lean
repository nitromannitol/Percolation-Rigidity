import Rigidity.Percolation.CubeFaceContactAbundance
import Rigidity.Proofs.Percolation.SupercriticalUniqueness

/-!
# Infinite clusters meeting large seeds

Under supercritical Bernoulli bond percolation, the probability that the
infinite cluster misses a centered cube tends to zero as the cube grows.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

/-- A finite seed meets an infinite open component in a measurable event. -/
theorem measurableSet_seedInfiniteOpenEvent {d : ℕ} (roots : Finset (Vertex d)) :
    MeasurableSet (seedInfiniteOpenEvent roots) :=
  MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _ =>
    measurableSet_infiniteOpenInEvent Set.univ z

/-- Centered cube seeds grow monotonically. -/
theorem monotone_centeredBondCubeFinset {d : ℕ} :
    Monotone (centeredBondCubeFinset (d := d)) := by
  intro n m hnm x hx
  simp only [centeredBondCubeFinset, Set.Finite.mem_toFinset, mem_centeredBondCube] at hx ⊢
  intro i
  exact (hx i).trans (by exact_mod_cast hnm)

/-- The increasing seed events exhaust the event that some vertex belongs to
an infinite open component. -/
theorem iUnion_seedInfiniteOpenEvent_centeredBondCube {d : ℕ} :
    (⋃ n, seedInfiniteOpenEvent (centeredBondCubeFinset (d := d) n)) =
      ⋃ x : Vertex d, infiniteComponentEvent x := by
  have hgraph (ω : Configuration d) : openIn ω Set.univ = openGraph ω := by
    ext x y
    simp only [openIn, Set.mem_univ, and_self, and_true]
  have hevent (x : Vertex d) : infiniteOpenInEvent Set.univ x = infiniteComponentEvent x := by
    ext ω
    rw [mem_infiniteOpenInEvent_iff, mem_infiniteComponentEvent_iff, hgraph]
    simp only [Set.mem_univ, true_and]
  ext ω
  simp only [seedInfiniteOpenEvent, hevent, Set.mem_iUnion]
  constructor
  · rintro ⟨n, x, _, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨LatticeProb.supNorm x, x, ?_, hx⟩
    simpa only [centeredBondCubeFinset, Set.Finite.mem_toFinset, mem_centeredBondCube] using
      (LatticeProb.supNorm_le_iff.mp (le_rfl : LatticeProb.supNorm x ≤ LatticeProb.supNorm x))

/-- Positive percolation probability forces the probability of missing an
infinite component with an expanding centered seed to tend to zero. -/
theorem tendsto_measureReal_noInfiniteSeed_of_theta_pos {d : ℕ} (p : unitInterval)
    (hp : 0 < LatticeProb.Percolation.theta d p) :
    Tendsto (fun n => (latticeBondLaw d p).real
      (seedInfiniteOpenEvent (centeredBondCubeFinset n))ᶜ) atTop (𝓝 0) := by
  let E : ℕ → Set (Configuration d) := fun n => seedInfiniteOpenEvent (centeredBondCubeFinset n)
  have hE : Monotone E := by
    intro n m hnm ω hω
    obtain ⟨x, hx, hxi⟩ := Set.mem_iUnion.mp hω |>.imp fun _ h => Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr
      ⟨monotone_centeredBondCubeFinset hnm hx, hxi⟩⟩
  have hfull : latticeBondLaw d p (⋃ n, E n) = 1 := by
    refine le_antisymm ?_ ?_
    · calc
        _ ≤ latticeBondLaw d p Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    · rw [← uniqueInfiniteComponentEvent_eq_one_of_theta_pos d p hp]
      apply measure_mono
      intro ω hω
      change ω ∈ ⋃ n, seedInfiniteOpenEvent (centeredBondCubeFinset n)
      rw [iUnion_seedInfiniteOpenEvent_centeredBondCube]
      obtain ⟨x, hx⟩ := ((mem_uniqueInfiniteComponentEvent_iff ω).mp hω).1
      exact Set.mem_iUnion.mpr ⟨x, hx⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := latticeBondLaw d p) hE
  rw [hfull] at hlim
  have hreal := (ENNReal.tendsto_toReal (show (1 : ENNReal) ≠ ⊤ by simp)).comp hlim
  change Tendsto (fun n => (latticeBondLaw d p).real (E n)) atTop (𝓝 1) at hreal
  have hcompl := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hreal
  have heq : (fun n => (latticeBondLaw d p).real (E n)ᶜ) =
      (fun n => 1 - (latticeBondLaw d p).real (E n)) := by
    funext n
    rw [measureReal_compl (measurableSet_seedInfiniteOpenEvent _), probReal_univ]
  rw [heq]
  simpa only [sub_self] using hcompl

/-- With positive percolation probability, one centered seed works for every
fixed contact threshold: on sufficiently large orthant faces fewer than that
many contacts occur with arbitrarily small probability. -/
theorem exists_seed_eventually_few_orthantFace_contacts {d : ℕ} (p : unitInterval)
    (hp : (p : ℝ) < 1) (hθ : 0 < LatticeProb.Percolation.theta d p)
    (i : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, ∀ᶠ n in atTop,
      (latticeBondLaw d p).real (fewSeedContacts (centeredBondCube (M + n))
        (centeredBondCubeFinset M) (centeredCubeOrthantFace (M + n) i (fun _ => true)) m) < ε := by
  have hlim := tendsto_measureReal_noInfiniteSeed_of_theta_pos p hθ
  obtain ⟨M, hM, hMpos⟩ := ((hlim.eventually
    (eventually_lt_nhds (pow_pos hε (d * 2 ^ d)))).and (eventually_ge_atTop 1)).exists
  exact ⟨M, hMpos, fun m => eventually_measureReal_few_orthantFace_contacts_lt p hp M m i ε hε.le hM⟩

end Rigidity.Percolation

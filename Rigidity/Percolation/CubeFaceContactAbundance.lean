import Rigidity.Percolation.CubeFaceContactProbability

/-!
# Abundance of contacts on cube faces

Combining boundary contact decay with positive association gives an eventual
lower bound on the number of contacts on any fixed orthant face.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

/-- If the probability that a centered seed has no infinite component is
smaller than `ε` to the number of orthant faces, then sufficiently large cube
faces have at least `m` reached vertices with probability above `1 - ε`. -/
theorem eventually_measureReal_few_orthantFace_contacts_lt {d : ℕ} (p : unitInterval)
    (hp : (p : ℝ) < 1) (M m : ℕ) (i : Fin d) (ε : ℝ) (hε : 0 ≤ ε)
    (hseed : (latticeBondLaw d p).real
      (seedInfiniteOpenEvent (centeredBondCubeFinset M))ᶜ < ε ^ (d * 2 ^ d)) :
    ∀ᶠ n in atTop, (latticeBondLaw d p).real (fewSeedContacts
      (centeredBondCube (M + n)) (centeredBondCubeFinset M)
      (centeredCubeOrthantFace (M + n) i (fun _ => true)) m) < ε := by
  let roots : Finset (Vertex d) := centeredBondCubeFinset M
  let D : ℕ := d * 2 ^ d
  let I : Set (Configuration d) := seedInfiniteOpenEvent roots
  let A : ℕ → Set (Configuration d) := fun n => fewSeedContacts
    (centeredBondCube (M + n)) roots (centeredBondCubeBoundary (M + n)) (D * m)
  have hroots : ∀ z ∈ roots, z ∈ centeredBondCube M := by
    intro z hz
    simpa only [roots, centeredBondCubeFinset, Set.Finite.mem_toFinset] using hz
  have hlim := tendsto_measure_infinite_seed_few_cube_contacts p hp roots M (D * m) hroots
  change Tendsto (fun n => latticeBondLaw d p (I ∩ A n)) atTop (𝓝 0) at hlim
  have hlimReal : Tendsto (fun n => (latticeBondLaw d p).real (I ∩ A n)) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal (show (0 : ENNReal) ≠ ⊤ by simp)).comp hlim
    change Tendsto (fun n => ((latticeBondLaw d p) (I ∩ A n)).toReal) atTop
      (𝓝 (ENNReal.toReal 0)) at h
    exact h
  have hgap : 0 < ε ^ D - (latticeBondLaw d p).real Iᶜ := sub_pos.mpr hseed
  filter_upwards [hlimReal.eventually (eventually_lt_nhds hgap)] with n hn
  apply lt_of_pow_lt_pow_left₀ D hε
  calc
    _ ≤ (latticeBondLaw d p).real (A n) := by
      exact pow_measureReal_orthantFace_contacts_le_boundary p M (M + n) m i
    _ ≤ (latticeBondLaw d p).real ((I ∩ A n) ∪ Iᶜ) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      by_cases hI : ω ∈ I
      · exact Or.inl ⟨hI, hω⟩
      · exact Or.inr hI
    _ ≤ (latticeBondLaw d p).real (I ∩ A n) + (latticeBondLaw d p).real Iᶜ :=
      measureReal_union_le _ _
    _ < ε ^ D := by linarith

end Rigidity.Percolation

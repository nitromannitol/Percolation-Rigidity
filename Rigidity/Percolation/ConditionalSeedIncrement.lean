import Rigidity.Percolation.EquivariantConditionalSeed

/-!
# Positive increments for conditional seed connections

If the explored set contains the central seed and avoids the target face,
its cut inside the ambient cube is nonempty. Thus admissible boundary
thresholds can only exist when the increment is at most one.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- Every positive-orthant cube face contains its normal-axis corner. -/
theorem centeredCubeOrthantFace_nonempty {d : ℕ} (n : ℕ) (i : Fin d) :
    (centeredCubeOrthantFace n i (fun _ => true)).Nonempty := by
  let x : Vertex d := fun j => if j = i then (n : ℤ) else 0
  have hx : x ∈ centeredBondCube n := by
    apply (mem_centeredBondCube n x).mpr
    intro j
    dsimp only [x]
    split_ifs <;> simp only [abs_of_nonneg (Int.natCast_nonneg _), abs_zero] <;> omega
  refine ⟨x, (mem_centeredCubeOrthantFace n i _ x).mpr ⟨?_, ?_, ?_⟩⟩
  · apply (mem_centeredBondCubeBoundary n x).mpr
    refine ⟨hx, i, ?_⟩
    simp only [x, ↓reduceIte, abs_of_nonneg (Int.natCast_nonneg _)]
  · simp only [x, ↓reduceIte]
  · intro j
    simp only [↓reduceIte]
    dsimp only [x]
    split_ifs <;> omega

/-- A finite region containing the central seed and avoiding a cube face has
a boundary bond whose endpoints both lie in the cube. -/
theorem vertexCutBondsIn_nonempty_of_seed_face {d : ℕ} (M n : ℕ) (i : Fin d)
    (R : Finset (Vertex d)) (hseed : centeredBondCubeFinset M ⊆ R)
    (hR : (R : Set (Vertex d)) ⊆ centeredBondCube n)
    (hface : ∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) :
    (vertexCutBondsIn R (centeredBondCube n)).Nonempty := by
  have hzero : (0 : Vertex d) ∈ centeredBondCubeFinset M := by
    simp only [centeredBondCubeFinset, Set.Finite.mem_toFinset, mem_centeredBondCube,
      Pi.zero_apply, abs_zero]
    intro j
    exact Int.natCast_nonneg _
  have hzeroR := hseed hzero
  obtain ⟨z, hz⟩ := centeredCubeOrthantFace_nonempty n i
  have hzD := ((mem_centeredBondCubeBoundary n z).mp
    ((mem_centeredCubeOrthantFace n i _ z).mp hz).1).1
  have hzR := hface z hz
  have hpath : (openIn (allOpen d) (centeredBondCube n)).Reachable 0 z := by
    exact reachable_allOpen_latticeRectangle _ _ (hR hzeroR) hzD
  have hdisj : Disjoint (R : Set (Vertex d)) (centeredBondCube n \ (R : Set (Vertex d))) := by
    rw [Set.disjoint_left]
    intro x hxR hxD
    exact hxD.2 hxR
  have hcover : centeredBondCube n ⊆ (R : Set (Vertex d)) ∪
      (centeredBondCube n \ (R : Set (Vertex d))) := by
    intro x hx
    by_cases hxR : x ∈ R
    · exact Or.inl hxR
    · exact Or.inr ⟨hx, hxR⟩
  obtain ⟨x, hx, y, hy, hxy, _, _⟩ :=
    exists_slab_attachment_of_reachable hdisj hcover hzeroR ⟨hzD, hzR⟩ hpath
  exact ⟨bondOfAdjacent hxy, bondOfAdjacent_mem_vertexCutBondsIn R _ hR hx hy hxy⟩

/-- The conditional seed-and-pad estimate holds for every positive increment;
if the increment exceeds one, the boundary threshold constraints cannot be
satisfied. -/
theorem exists_conditional_markedPadSeedExit_of_pos {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      ∀ R : Finset (Vertex d), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        ∀ β : Bond d → unitInterval,
          (∀ e ∈ vertexCutBondsIn R (centeredBondCube n), (β e : ℝ) + δ ≤ 1) →
          0 < (bondMarkLaw d).real (bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β) ∧
          1 - ε < (bondMarkLaw d).real
              (bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β ∩
                markedPadSeedExit p M n i R β δ) /
            (bondMarkLaw d).real (bondMarksAbove (vertexCutBondsIn R (centeredBondCube n)) β) := by
  by_cases hδ1 : δ ≤ 1
  · exact exists_conditional_markedPadSeedExit p hp hp1 i ε δ hε hδ hδ1
  · obtain ⟨M, n, hM, hn, _⟩ :=
      exists_conditional_markedPadSeedExit p hp hp1 i ε 1 hε (by norm_num) (by norm_num)
    refine ⟨M, n, hM, hn, ?_⟩
    intro R hseed hR hface β hβ
    obtain ⟨e, he⟩ := vertexCutBondsIn_nonempty_of_seed_face M n i R hseed hR hface
    have h := hβ e he
    have hb := (β e).property.1
    have hlarge : 1 < δ := lt_of_not_ge hδ1
    exfalso
    linarith

end Rigidity.Percolation

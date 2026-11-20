import Rigidity.Percolation.SlabRootSurvival
import Rigidity.Percolation.SlabLongRangeCrossing

/-!
# Transverse crossings of cube slabs

Every nonempty slab meets the two cube faces in each transverse direction.
Uniform slab two-point connectivity therefore implies a rooted transverse
crossing probability through positive association.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- A nonempty slab meets both faces of the cube in every transverse direction. -/
theorem IntegerCube.exists_slab_face_points {d : ℕ} (Q : IntegerCube d)
    (j i : Fin d) (hij : i ≠ j) (width k : ℕ) {x : Vertex d}
    (hx : x ∈ Q.slab j width k) :
    (∃ y ∈ Q.slab j width k, y ∈ Q.lowerFace i) ∧
      ∃ y ∈ Q.slab j width k, y ∈ Q.upperFace i := by
  classical
  let a : Vertex d := Function.update x i (Q.corner i)
  let b : Vertex d := Function.update x i (Q.corner i + (Q.size : ℤ) - 1)
  have hsize : (0 : ℤ) < Q.size := by
    have hj := (Q.mem_vertices x).mp hx.1 j
    omega
  have haQ : a ∈ Q.vertices := by
    rw [Q.mem_vertices]
    intro t
    by_cases ht : t = i
    · subst t
      simp only [a, Function.update_self]
      omega
    · simpa only [a, Function.update_of_ne ht] using (Q.mem_vertices x).mp hx.1 t
  have hbQ : b ∈ Q.vertices := by
    rw [Q.mem_vertices]
    intro t
    by_cases ht : t = i
    · subst t
      simp only [b, Function.update_self]
      omega
    · simpa only [b, Function.update_of_ne ht] using (Q.mem_vertices x).mp hx.1 t
  have haj : a j = x j := Function.update_of_ne (Ne.symm hij) _ _
  have hbj : b j = x j := Function.update_of_ne (Ne.symm hij) _ _
  have ha : a ∈ Q.slab j width k := ⟨haQ, by simpa only [haj] using hx.2⟩
  have hb : b ∈ Q.slab j width k := ⟨hbQ, by simpa only [hbj] using hx.2⟩
  refine ⟨⟨a, ha, (Q.mem_lowerFace i a).mpr ⟨haQ, ?_⟩⟩,
    ⟨b, hb, (Q.mem_upperFace i b).mpr ⟨hbQ, ?_⟩⟩⟩
  · simp only [a, Function.update_self]
  · simp only [b, Function.update_self]
    omega

/-- The cube faces transverse to `j`, with unrestricted marks in direction `j`. -/
def IntegerCube.transverseLower {d : ℕ} (Q : IntegerCube d) (j : Fin d) :
    Fin d → Set (Vertex d) := fun i => if i = j then Set.univ else Q.lowerFace i

/-- The upper cube faces transverse to `j`, with unrestricted marks in direction `j`. -/
def IntegerCube.transverseUpper {d : ℕ} (Q : IntegerCube d) (j : Fin d) :
    Fin d → Set (Vertex d) := fun i => if i = j then Set.univ else Q.upperFace i

/-- Uniform two-point connectivity in a slab gives a rooted transverse
crossing probability of at least `ρ ^ (2 * d)`. -/
theorem IntegerCube.pow_le_slab_transverse_crossing {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) (width k : ℕ) (p : unitInterval)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x : Vertex d) (hx : x ∈ Q.slab j width k)
    (hprob : ∀ y ∈ Q.slab j width k, ρ ≤ (latticeBondLaw d p).real
      {ω | (openIn ω (Q.slab j width k)).Reachable x y}) :
    ρ ^ (2 * d) ≤ (latticeBondLaw d p).real
      {ω | IsCrossingRoot ω (Q.slab j width k) (Q.transverseLower j)
        (Q.transverseUpper j) x} := by
  classical
  have hex : ∀ face : Fin d × Bool, ∃ y ∈ Q.slab j width k,
      y ∈ (if face.2 then Q.transverseUpper j face.1 else Q.transverseLower j face.1) := by
    intro ⟨i, b⟩
    by_cases hij : i = j
    · exact ⟨x, hx, by simp [IntegerCube.transverseUpper, IntegerCube.transverseLower, hij]⟩
    · obtain ⟨⟨a, ha, hal⟩, ⟨b', hb, hbu⟩⟩ := Q.exists_slab_face_points j i hij width k hx
      cases b with
      | false => exact ⟨a, ha, by simpa [IntegerCube.transverseLower, hij] using hal⟩
      | true => exact ⟨b', hb, by simpa [IntegerCube.transverseUpper, hij] using hbu⟩
  choose point hpointB hpointFace using hex
  exact pow_le_measureReal_crossingRoot_of_twoPoint p (Q.slab j width k)
    (Q.transverseLower j) (Q.transverseUpper j) x hx point hpointB hpointFace ρ hρ
    (fun face => hprob (point face) (hpointB face))

end Rigidity.Percolation

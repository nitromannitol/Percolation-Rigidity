import Rigidity.Percolation.TriadicInfluenceBounds

/-!
# Counting influenced cubes

At each fixed scale, the centers of all cubes influenced by a given cube lie
in a uniformly bounded set of triadic indices.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The index of an influenced cube is within nine of the cube containing the initial center. -/
theorem TriadicCube.index_sub_le_of_mem_influence {d : ℕ} {Q R A : TriadicCube d}
    (h : R ∈ Q.influence) (hscale : R.scale = A.scale)
    (hA : Q.center ∈ A.vertices) (i : Fin d) :
    |R.index i - A.index i| ≤ 9 := by
  have hs : R.side = A.side := by simp only [side, hscale]
  have hr := abs_le.mp (abs_center_sub_le_of_mem_influence h i)
  have ha := abs_lt.mp (A.abs_coord_sub_lt_side hA A.center_mem i)
  rw [hs] at hr
  simp only [center, hs] at hr ha
  have hpos := A.side_pos
  rcases hr with ⟨hrl, hru⟩
  rcases ha with ⟨hal, hau⟩
  apply abs_le.mpr
  constructor
  · by_contra hn
    have hi : R.index i + 10 ≤ A.index i := by omega
    have hm := mul_le_mul_of_nonneg_left hi (le_of_lt hpos)
    nlinarith
  · by_contra hn
    have hi : A.index i + 10 ≤ R.index i := by omega
    have hm := mul_le_mul_of_nonneg_left hi (le_of_lt hpos)
    nlinarith

/-- The influenced cubes of any given scale form a finite set of size at most `19 ^ d`. -/
theorem TriadicCube.finite_influence_at_scale {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    {R ∈ Q.influence | R.scale = n}.Finite ∧
      {R ∈ Q.influence | R.scale = n}.ncard ≤ 19 ^ d := by
  classical
  obtain ⟨A, ⟨hA, hmem⟩, -⟩ := existsUnique_mem d n Q.center
  let indices : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i => Finset.Icc (A.index i - 9) (A.index i + 9))
  let cubes : Finset (TriadicCube d) := indices.image (fun a => ⟨n, a⟩)
  have hsubset : {R ∈ Q.influence | R.scale = n} ⊆ (cubes : Set (TriadicCube d)) := by
    intro R hR
    have hidx : R.index ∈ indices := by
      simp only [indices, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have h := abs_le.mp (index_sub_le_of_mem_influence hR.1 (hR.2.trans hA.symm) hmem i)
      constructor <;> omega
    apply Finset.mem_coe.mpr
    apply Finset.mem_image.mpr
    refine ⟨R.index, hidx, ?_⟩
    apply TriadicCube.ext
    · exact hR.2.symm
    · rfl
  have hcard : cubes.card ≤ 19 ^ d := by
    calc
      cubes.card ≤ indices.card := Finset.card_image_le
      _ = 19 ^ d := by
        simp only [indices, Fintype.card_piFinset]
        have hprod : ∀ i : Fin d, (Finset.Icc (A.index i - 9) (A.index i + 9)).card = 19 := by
          intro i
          rw [Int.card_Icc]
          omega
        simp only [hprod, Finset.prod_const, Finset.card_fin]
  refine ⟨cubes.finite_toSet.subset hsubset, ?_⟩
  have hn := Set.ncard_le_ncard hsubset cubes.finite_toSet
  rw [Set.ncard_coe_finset] at hn
  exact hn.trans hcard

end Rigidity.Percolation

import Rigidity.Percolation.TriadicWellConnectedGeometry

/-!
# Counting well-connectedness test cubes

The number of integer test cubes grows polynomially in the side length of the
ambient triadic cube. This supports finite union bounds over all test cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The qualifying integer cubes form a finite family, with a polynomial bound
in the side length of the ambient cube. -/
theorem TriadicCube.finite_testCubes_and_ncard_le {d : ℕ} (Q : TriadicCube d)
    (interior : Set (Vertex d)) (hinterior : interior ⊆ Q.vertices) :
    (Q.testCubes interior).Finite ∧
      (Q.testCubes interior).ncard ≤
        (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d := by
  classical
  let indices : Finset (Vertex d) := Fintype.piFinset fun i =>
    Finset.Icc (Q.center i - 3 * Q.side) (Q.center i + 3 * Q.side)
  let sizes : Finset ℕ := Finset.range (3 ^ Q.scale + 1)
  let cubes : Finset (IntegerCube d) := (sizes.product indices).image fun a => ⟨a.2, a.1⟩
  have hsubset : Q.testCubes interior ⊆ (cubes : Set (IntegerCube d)) := by
    intro R hR
    have hpos : 0 < R.size := by
      have hs := Q.side_pos
      have h := hR.1
      exact_mod_cast (show (0 : ℤ) < R.size by omega)
    have hcorner : R.corner ∈ R.vertices := by
      rw [IntegerCube.mem_vertices]
      intro i
      constructor
      · exact le_rfl
      · have : (0 : ℤ) < R.size := by exact_mod_cast hpos
        omega
    have hnear := Q.testCube_vertices_subset_centeredTriple hinterior hR hcorner
    have hidx : R.corner ∈ indices := by
      simp only [indices, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have hi := abs_lt.mp (Q.abs_coord_sub_center_lt_of_mem_centeredTriple hnear i)
      omega
    have hsize : R.size ∈ sizes := by
      simp only [sizes, Finset.mem_range]
      have h := hR.2.1
      have hside : Q.side = ((3 ^ Q.scale : ℕ) : ℤ) := by
        simp only [side, Nat.cast_pow, Nat.cast_ofNat]
      rw [hside] at h
      omega
    apply Finset.mem_coe.mpr
    apply Finset.mem_image.mpr
    exact ⟨(R.size, R.corner), Finset.mem_product.mpr ⟨hsize, hidx⟩, by cases R; rfl⟩
  have hcard : cubes.card ≤ (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d := by
    calc
      cubes.card ≤ (sizes.product indices).card := Finset.card_image_le
      _ = (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d := by
        change (sizes ×ˢ indices).card = _
        rw [Finset.card_product]
        dsimp only [sizes]
        rw [Finset.card_range]
        congr 1
        simp only [indices, Fintype.card_piFinset]
        have hprod : ∀ i : Fin d,
            (Finset.Icc (Q.center i - 3 * Q.side) (Q.center i + 3 * Q.side)).card =
              6 * 3 ^ Q.scale + 1 := by
          intro i
          rw [Int.card_Icc]
          have hside : Q.side = ((3 ^ Q.scale : ℕ) : ℤ) := by
            simp only [side, Nat.cast_pow, Nat.cast_ofNat]
          rw [hside]
          omega
        simp only [hprod, Finset.prod_const, Finset.card_fin]
  refine ⟨cubes.finite_toSet.subset hsubset, ?_⟩
  have hn := Set.ncard_le_ncard hsubset cubes.finite_toSet
  rw [Set.ncard_coe_finset] at hn
  exact hn.trans hcard

end Rigidity.Percolation

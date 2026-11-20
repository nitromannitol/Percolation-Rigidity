import Rigidity.Percolation.SingleFieldSeedFace

/-!
# Aligned outward seed pads

When the side length of a grid cell divides the width of a positive cube
face, a trial selected on the face has its seed inside the corresponding
outward pad.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The outward pad above a positive orthant face of a centered cube. -/
def orthantFaceSeedPad {d : ℕ} (n k : ℕ) (i : Fin d) : Set (Vertex d) :=
  {x | (n : ℤ) + 1 ≤ x i ∧ x i < (n : ℤ) + 1 + (k : ℤ) ∧
    ∀ j, j ≠ i → 0 ≤ x j ∧ x j ≤ n}

/-- If the grid aligns with the upper edge of the face, the seed selected
at any positive-orthant contact lies in the outward pad. -/
theorem faceSeedCell_subset_orthantFaceSeedPad {d k : ℕ} (hk : 0 < k)
    (n : ℕ) (i : Fin d) (x : Vertex d)
    (hx : x ∈ centeredCubeOrthantFace n i (fun _ => true))
    (hdiv : (k : ℤ) ∣ (n : ℤ) + 1) :
    faceSeedCell k i n (seedGridIndex k x) ⊆ orthantFaceSeedPad n k i := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hface := (mem_centeredCubeOrthantFace n i (fun _ => true) x).mp hx
  have hcube := ((mem_centeredBondCubeBoundary n x).mp hface.1).1
  have hnonneg : ∀ j, 0 ≤ x j := by simpa only [↓reduceIte] using hface.2.2
  intro y hy
  refine ⟨hy.1, hy.2.1, ?_⟩
  intro j hj
  have hq : y j / (k : ℤ) = x j / (k : ℤ) := hy.2.2 j hj
  have hxmin := hnonneg j
  have hxmax : x j ≤ (n : ℤ) := ((abs_le.mp ((mem_centeredBondCube n x).mp hcube j)).2)
  have hdivEq : ((n : ℤ) + 1) / (k : ℤ) * k = (n : ℤ) + 1 :=
    Int.ediv_mul_cancel hdiv
  have hqnonneg : 0 ≤ y j / (k : ℤ) := by
    rw [hq]
    exact Int.ediv_nonneg hxmin (le_of_lt hk')
  have hlow : 0 ≤ y j := (mul_nonneg (le_of_lt hk') hqnonneg).trans
    (Int.mul_ediv_self_le (ne_of_gt hk'))
  have hlt : x j / (k : ℤ) < ((n : ℤ) + 1) / (k : ℤ) := by
    apply (Int.ediv_lt_iff_lt_mul hk').mpr
    rw [hdivEq]
    omega
  have hupper := Int.lt_mul_ediv_self_add (x := y j) hk'
  have hmul : (k : ℤ) * (y j / (k : ℤ) + 1) ≤
      (k : ℤ) * (((n : ℤ) + 1) / (k : ℤ)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hk')
    omega
  have hbound : (k : ℤ) * (((n : ℤ) + 1) / (k : ℤ)) = (n : ℤ) + 1 := by
    rw [mul_comm, hdivEq]
  constructor
  · exact hlow
  · rw [mul_add, mul_one] at hmul
    omega

/-- A side-`2M+1` face seed is a translate of the centered cube of radius `M`. -/
theorem faceSeedCell_eq_centeredCube_translate {d : ℕ} (M : ℕ) (i : Fin d)
    (n : ℤ) (x : Vertex d) :
    faceSeedCell (2 * M + 1) i n (seedGridIndex (2 * M + 1) x) =
      (fun z : Vertex d => z + (fun j =>
        (if j = i then n + 1 else ((2 * M + 1 : ℕ) : ℤ) *
          seedGridIndex (2 * M + 1) x j) + (M : ℤ))) '' centeredBondCube M := by
  let k := 2 * M + 1
  have hk : 0 < k := by dsimp [k]; omega
  let lo : Vertex d := fun j => if j = i then n + 1 else (k : ℤ) * seedGridIndex k x j
  let c : Vertex d := fun j => lo j + (M : ℤ)
  change faceSeedCell k i n (seedGridIndex k x) = (fun z : Vertex d => z + c) '' centeredBondCube M
  rw [faceSeedCell_eq_rectangle hk]
  change latticeRectangle lo (fun j => lo j + k) = (fun z : Vertex d => z + c) '' centeredBondCube M
  ext y
  constructor
  · intro hy
    refine ⟨y - c, ?_, sub_add_cancel y c⟩
    apply (mem_centeredBondCube M _).mpr
    intro j
    have hj := hy j
    change lo j ≤ y j ∧ y j < lo j + (k : ℤ) at hj
    change |y j - (lo j + (M : ℤ))| ≤ (M : ℤ)
    rw [abs_le]
    have hkcast : (k : ℤ) = 2 * (M : ℤ) + 1 := by simp only [k, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    omega
  · rintro ⟨z, hz, rfl⟩
    intro j
    have hj := (abs_le.mp ((mem_centeredBondCube M z).mp hz j))
    change lo j ≤ z j + (lo j + (M : ℤ)) ∧
      z j + (lo j + (M : ℤ)) < lo j + (k : ℤ)
    have hkcast : (k : ℤ) = 2 * (M : ℤ) + 1 := by simp only [k, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    omega

end Rigidity.Percolation

import Rigidity.Percolation.TriadicInfluenceCount
import Rigidity.Percolation.TriadicLocalizationGeometry

/-!
# Counting cubes near a triadic cube

At a fixed scale, a polynomial bound holds for the number of cubes within a
fixed multiple of their own side length of a given triadic cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The side of one cube is at most the side of another times the triadic
scale ratio, rounded up to one. -/
theorem TriadicCube.side_le_side_mul_scale_ratio {d : ℕ} (A T : TriadicCube d) :
    A.side ≤ T.side * (3 : ℤ) ^ (A.scale - T.scale) := by
  have hscale : A.scale ≤ T.scale + (A.scale - T.scale) := by omega
  calc
    A.side ≤ (3 : ℤ) ^ (T.scale + (A.scale - T.scale)) :=
      pow_le_pow_right₀ (by norm_num) hscale
    _ = T.side * (3 : ℤ) ^ (A.scale - T.scale) := by rw [pow_add]; rfl

/-- A cube close to a given cube has an index close to the cube containing the
center of the given cube at the same scale. -/
theorem TriadicCube.index_sub_le_of_near {d : ℕ} {A T C : TriadicCube d}
    {x y : Vertex d} (hx : x ∈ A.vertices) (hy : y ∈ T.vertices)
    (hnear : ∀ i, |x i - y i| < 12 * T.side)
    (hscale : T.scale = C.scale) (hC : A.center ∈ C.vertices) (i : Fin d) :
    |T.index i - C.index i| ≤ (3 : ℤ) ^ (A.scale - T.scale) + 14 := by
  have hs : T.side = C.side := by simp only [side, hscale]
  have ha := abs_lt.mp (A.abs_coord_sub_lt_side hx A.center_mem i)
  have ht := abs_lt.mp (T.abs_coord_sub_lt_side hy T.center_mem i)
  have hc := abs_lt.mp (C.abs_coord_sub_lt_side hC C.center_mem i)
  have hn := abs_lt.mp (hnear i)
  have hratio := A.side_le_side_mul_scale_ratio T
  have hpos := T.side_pos
  rw [← hs] at hc
  simp only [center] at ha ht hc
  apply abs_le.mpr
  constructor
  · by_contra hn'
    have hi : T.index i + ((3 : ℤ) ^ (A.scale - T.scale) + 15) ≤ C.index i := by omega
    have hm := mul_le_mul_of_nonneg_left hi (le_of_lt hpos)
    nlinarith
  · by_contra hn'
    have hi : C.index i + ((3 : ℤ) ^ (A.scale - T.scale) + 15) ≤ T.index i := by omega
    have hm := mul_le_mul_of_nonneg_left hi (le_of_lt hpos)
    nlinarith

/-- Cubes at scale `n` near a fixed cube form a finite set with a polynomial
bound in the ratio of side lengths. -/
theorem TriadicCube.finite_near_at_scale {d : ℕ} (A : TriadicCube d) (n : ℕ) :
    {T : TriadicCube d | T.scale = n ∧
      ∃ x ∈ A.vertices, ∃ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side}.Finite ∧
    {T : TriadicCube d | T.scale = n ∧
      ∃ x ∈ A.vertices, ∃ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side}.ncard ≤
        (2 * 3 ^ (A.scale - n) + 29) ^ d := by
  classical
  obtain ⟨C, ⟨hCscale, hC⟩, -⟩ := existsUnique_mem d n A.center
  let k : ℤ := (3 : ℤ) ^ (A.scale - n) + 14
  let indices : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i => Finset.Icc (C.index i - k) (C.index i + k))
  let cubes : Finset (TriadicCube d) := indices.image (fun a => ⟨n, a⟩)
  have hsubset : {T : TriadicCube d | T.scale = n ∧
      ∃ x ∈ A.vertices, ∃ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side} ⊆
      (cubes : Set (TriadicCube d)) := by
    intro T hT
    obtain ⟨hscale, x, hx, y, hy, hnear⟩ := hT
    have hidx : T.index ∈ indices := by
      simp only [indices, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have h := abs_le.mp (index_sub_le_of_near hx hy hnear (hscale.trans hCscale.symm) hC i)
      simp only [hscale] at h
      change C.index i - k ≤ T.index i ∧ T.index i ≤ C.index i + k
      dsimp only [k]
      constructor <;> omega
    apply Finset.mem_coe.mpr
    apply Finset.mem_image.mpr
    exact ⟨T.index, hidx, TriadicCube.ext hscale.symm rfl⟩
  have hcard : cubes.card ≤ (2 * 3 ^ (A.scale - n) + 29) ^ d := by
    calc
      cubes.card ≤ indices.card := Finset.card_image_le
      _ = (2 * 3 ^ (A.scale - n) + 29) ^ d := by
        simp only [indices, Fintype.card_piFinset]
        have hprod : ∀ i : Fin d,
            (Finset.Icc (C.index i - k) (C.index i + k)).card =
              2 * 3 ^ (A.scale - n) + 29 := by
          intro i
          rw [Int.card_Icc]
          dsimp only [k]
          have hpow : (0 : ℤ) ≤ 3 ^ (A.scale - n) := by positivity
          have hcast : (3 : ℤ) ^ (A.scale - n) =
              ((3 ^ (A.scale - n) : ℕ) : ℤ) := by push_cast; rfl
          rw [hcast] at *
          omega
        simp only [hprod, Finset.prod_const, Finset.card_fin]
  refine ⟨cubes.finite_toSet.subset hsubset, ?_⟩
  have hn := Set.ncard_le_ncard hsubset cubes.finite_toSet
  rw [Set.ncard_coe_finset] at hn
  exact hn.trans hcard

end Rigidity.Percolation

import Rigidity.Proofs.Multiscale.Cube
import Rigidity.Vendor.LHCH.Support.WeakNorm.MultiscalePoincareCube

/-!
# Extension of a function from a triadic cube to the closed lattice cube

The triadic cube `3^m z + □_m` is `P + {0, …, 3^m - 1}^d`; the closed lattice cube
`P + {0, …, 3^m}^d` of the lattice multiscale Poincaré inequality has one more layer in each
direction. A function on the triadic cube is extended to it by composing with the clamp
`x_i ↦ min(x_i, P_i + 3^m - 1)`. The clamp has fibers of at most `2^d` points and the increments
of the extension are increments of the function or zero, so the energy of the extension is at
most `2^d` times the edge energy of the function; the extension agrees with the function on the
triadic cube.
-/

namespace Rigidity.Proofs.Multiscale

open LatticeProb LatticeProb.Percolation LatticeHC

variable {d : ℕ}

/-- The clamp of `x` to the corner `P` and side `N`: `x_i ↦ min(x_i, P_i + N - 1)`. -/
def clampSite (P : Site d) (N : ℕ) (x : Site d) : Site d := fun i => min (x i) (P i + N - 1)

/-- The unit vector of the lattice library is `e_i`. -/
theorem unit_eq_unitVec (i : Fin d) : unit i = unitVec i := rfl

/-- The coordinates of `e_j`. -/
theorem unitVec_apply (j i : Fin d) : unitVec j i = if i = j then 1 else 0 := by
  simp only [unitVec, Pi.single_apply]

/-- The triadic cube lies in the closed lattice cube with the same corner and side `3^m`. -/
theorem cube_subset_latticeCube (m : ℕ) (z : Vertex d) :
    cube m z ⊆ latticeCube (cubeCorner m z) (3 ^ m) := by
  intro x hx
  rw [mem_cube_iff_corner] at hx
  rw [mem_latticeCube_iff_coord]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  push_cast
  constructor <;> omega

/-- The clamp fixes the points of the triadic cube. -/
theorem clampSite_of_mem {m : ℕ} {z x : Vertex d} (hx : x ∈ cube m z) :
    clampSite (cubeCorner m z) (3 ^ m) x = x := by
  rw [mem_cube_iff_corner] at hx
  funext i
  obtain ⟨_, h2⟩ := hx i
  simp only [clampSite]
  push_cast
  exact min_eq_left (by omega)

/-- The clamp maps the closed lattice cube to the triadic cube. -/
theorem clampSite_mem {m : ℕ} {z : Vertex d} {x : Site d}
    (hx : x ∈ latticeCube (cubeCorner m z) (3 ^ m)) :
    clampSite (cubeCorner m z) (3 ^ m) x ∈ cube m z := by
  rw [mem_latticeCube_iff_coord] at hx
  rw [mem_cube_iff_corner]
  intro i
  obtain ⟨h1, _⟩ := hx i
  have h3 : (1 : ℤ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
  simp only [clampSite]
  push_cast
  constructor
  · exact le_min h1 (by omega)
  · exact lt_of_le_of_lt (min_le_right _ _) (by omega)

/-- **The clamp has fibers of at most `2^d` points**: for `g ≥ 0`,
`Σ_{x ∈ P + {0, …, 3^m}^d} g(clamp x) ≤ 2^d Σ_{y ∈ 3^m z + □_m} g(y)`. -/
theorem sum_comp_clampSite_le (m : ℕ) (z : Vertex d) (g : Site d → ℝ) (hg : ∀ y, 0 ≤ g y) :
    ∑ x ∈ latticeCube (cubeCorner m z) (3 ^ m), g (clampSite (cubeCorner m z) (3 ^ m) x) ≤
      2 ^ d * ∑ y ∈ cube m z, g y := by
  classical
  set P := cubeCorner m z
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun y => clampSite P (3 ^ m) y)
    (t := cube m z) (fun x hx => clampSite_mem hx), Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const,
    nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hg y)
  have hsub : (latticeCube P (3 ^ m)).filter (fun x => clampSite P (3 ^ m) x = y) ⊆
      Fintype.piFinset fun i => ({y i, y i + 1} : Finset ℤ) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Fintype.mem_piFinset]
    intro i
    have h := congrFun hx.2 i
    have hxi := (mem_latticeCube_iff_coord _ _ _).1 hx.1 i
    simp only [clampSite] at h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_cast at hxi h
    rcases le_total (x i) (P i + 3 ^ m - 1) with hle | hle
    · rw [min_eq_left hle] at h
      exact Or.inl h
    · rw [min_eq_right hle] at h
      omega
  have hcard : ((latticeCube P (3 ^ m)).filter (fun x => clampSite P (3 ^ m) x = y)).card ≤
      2 ^ d := by
    refine (Finset.card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset]
    calc ∏ i : Fin d, ({y i, y i + 1} : Finset ℤ).card ≤ 2 ^ (Finset.univ : Finset (Fin d)).card :=
          Finset.prod_le_pow_card _ _ _ fun i _ => (Finset.card_insert_le _ _).trans (by simp)
      _ = 2 ^ d := by rw [Finset.card_univ, Fintype.card_fin]
  exact_mod_cast hcard

/-- The increment of the extension along an edge of the closed cube is the increment of the
function along an edge of the triadic cube, or zero. -/
theorem sq_sub_clampSite_le (m : ℕ) (z : Vertex d) (u : Vertex d → ℝ) {x : Site d} {j : Fin d}
    (hx : x ∈ latticeCube (cubeCorner m z) (3 ^ m)) :
    (u (clampSite (cubeCorner m z) (3 ^ m) (x + unit j)) -
        u (clampSite (cubeCorner m z) (3 ^ m) x)) ^ 2 ≤
      if clampSite (cubeCorner m z) (3 ^ m) x + unitVec j ∈ cube m z then
        (u (clampSite (cubeCorner m z) (3 ^ m) x + unitVec j) -
          u (clampSite (cubeCorner m z) (3 ^ m) x)) ^ 2
      else 0 := by
  have hc := clampSite_mem hx
  rcases lt_or_ge (x j + 1) ((cubeCorner m z) j + 3 ^ m) with hlt | hge
  · have hshift : clampSite (cubeCorner m z) (3 ^ m) (x + unit j) =
        clampSite (cubeCorner m z) (3 ^ m) x + unitVec j := by
      funext i
      simp only [clampSite, Pi.add_apply, unit_eq_unitVec, unitVec_apply]
      push_cast
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, min_eq_left (by omega), min_eq_left (by omega)]
      · rw [if_neg hij, add_zero, add_zero]
    have hmem : clampSite (cubeCorner m z) (3 ^ m) x + unitVec j ∈ cube m z := by
      rw [mem_cube_iff_corner] at hc ⊢
      intro i
      obtain ⟨h1, h2⟩ := hc i
      simp only [Pi.add_apply, unitVec_apply]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        have : clampSite (cubeCorner m z) (3 ^ m) x i = x i := by
          simp only [clampSite]
          push_cast
          exact min_eq_left (by omega)
        constructor <;> omega
      · rw [if_neg hij, add_zero]
        exact ⟨h1, h2⟩
    rw [hshift, if_pos hmem]
  · have hsame : clampSite (cubeCorner m z) (3 ^ m) (x + unit j) =
        clampSite (cubeCorner m z) (3 ^ m) x := by
      funext i
      simp only [clampSite, Pi.add_apply, unit_eq_unitVec, unitVec_apply]
      push_cast
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, min_eq_right (by omega), min_eq_right (by omega)]
      · rw [if_neg hij, add_zero]
    rw [hsame, sub_self]
    split_ifs <;> simp [sq_nonneg]

/-- **Energy of the extension**: `Σ_{e ⊂ P + {0, …, 3^m}^d} |∇ũ(e)|² ≤ 2^d Σ_{edges of the triadic
cube} |∇u|²`. -/
theorem sum_edgesOf_sq_clampSite_le (m : ℕ) (z : Vertex d) (u : Vertex d → ℝ) :
    ∑ e ∈ edgesOf (cubeCorner m z) (3 ^ m),
        (u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
          u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ^ 2 ≤
      2 ^ d * edgeEnergy (cube m z) u := by
  classical
  set P := cubeCorner m z
  set g : Fin d → Site d → ℝ := fun j y =>
    if y + unitVec j ∈ cube m z then (u (y + unitVec j) - u y) ^ 2 else 0 with hg
  have hg0 : ∀ j y, 0 ≤ g j y := fun j y => by
    simp only [hg]
    split_ifs
    · positivity
    · exact le_rfl
  calc ∑ e ∈ edgesOf P (3 ^ m), (u (clampSite P (3 ^ m) e.tgt) - u (clampSite P (3 ^ m) e.src)) ^ 2
      ≤ ∑ e ∈ edgesOf P (3 ^ m), g e.2 (clampSite P (3 ^ m) e.1) := by
        refine Finset.sum_le_sum fun e he => ?_
        have he' := (mem_edgesOf_iff_endpoints_mem.1 he).1
        exact sq_sub_clampSite_le m z u he'
    _ ≤ ∑ e ∈ latticeCube P (3 ^ m) ×ˢ (Finset.univ : Finset (Fin d)),
          g e.2 (clampSite P (3 ^ m) e.1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (by
          intro e he
          rw [edgesOf, Finset.mem_filter] at he
          exact he.1) fun e _ _ => hg0 _ _
    _ = ∑ j : Fin d, ∑ x ∈ latticeCube P (3 ^ m), g j (clampSite P (3 ^ m) x) := by
        rw [Finset.sum_product, Finset.sum_comm]
    _ ≤ ∑ j : Fin d, 2 ^ d * ∑ y ∈ cube m z, g j y :=
        Finset.sum_le_sum fun j _ => sum_comp_clampSite_le m z (g j) (hg0 j)
    _ = 2 ^ d * edgeEnergy (cube m z) u := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        rfl

/-- The face-weighted mean energy of the extension is at most `2^d` times the normalized edge
energy of the function. -/
theorem cubeAvg_sq_clampSite_le (m : ℕ) (z : Vertex d) (u : Vertex d → ℝ) :
    cubeAvg (cubeCorner m z) (3 ^ m) (fun e =>
        (u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
          u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ^ 2) ≤
      2 ^ d * ((((3 : ℝ) ^ m) ^ d)⁻¹ * edgeEnergy (cube m z) u) := by
  set P := cubeCorner m z
  have hK : 0 ≤ (((3 : ℝ) ^ m) ^ d)⁻¹ := by positivity
  rw [cubeAvg]
  push_cast
  calc (((3 : ℝ) ^ m) ^ d)⁻¹ * ∑ e ∈ edgesOf P (3 ^ m), faceWeight P (3 ^ m) e *
        (u (clampSite P (3 ^ m) e.tgt) - u (clampSite P (3 ^ m) e.src)) ^ 2
      ≤ (((3 : ℝ) ^ m) ^ d)⁻¹ * ∑ e ∈ edgesOf P (3 ^ m),
          (u (clampSite P (3 ^ m) e.tgt) - u (clampSite P (3 ^ m) e.src)) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => ?_) hK
        have hw : faceWeight P (3 ^ m) e ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have hw0 : 0 ≤ faceWeight P (3 ^ m) e := pow_nonneg (by norm_num) _
        nlinarith [sq_nonneg (u (clampSite P (3 ^ m) e.tgt) - u (clampSite P (3 ^ m) e.src))]
    _ ≤ (((3 : ℝ) ^ m) ^ d)⁻¹ * (2 ^ d * edgeEnergy (cube m z) u) :=
        mul_le_mul_of_nonneg_left (sum_edgesOf_sq_clampSite_le m z u) hK
    _ = 2 ^ d * ((((3 : ℝ) ^ m) ^ d)⁻¹ * edgeEnergy (cube m z) u) := by ring

/-- The sum of squared deviations from the mean over the triadic cube is at most that of the
extension from its vertex-weighted mean over the closed cube. -/
theorem sum_sq_sub_finsetMean_le_clampSite (m : ℕ) (z : Vertex d) (u : Vertex d → ℝ) :
    ∑ x ∈ cube m z, (u x - finsetMean (cube m z) u) ^ 2 ≤
      ∑ x ∈ latticeCube (cubeCorner m z) (3 ^ m),
        (u (clampSite (cubeCorner m z) (3 ^ m) x) -
          vertexMean (cubeCorner m z) (3 ^ m)
            (fun y => u (clampSite (cubeCorner m z) (3 ^ m) y))) ^ 2 := by
  set c := vertexMean (cubeCorner m z) (3 ^ m) (fun y => u (clampSite (cubeCorner m z) (3 ^ m) y))
  calc ∑ x ∈ cube m z, (u x - finsetMean (cube m z) u) ^ 2
      ≤ ∑ x ∈ cube m z, (u x - c) ^ 2 := sum_sq_sub_finsetMean_le _ _ _
    _ = ∑ x ∈ cube m z, (u (clampSite (cubeCorner m z) (3 ^ m) x) - c) ^ 2 :=
        Finset.sum_congr rfl fun x hx => by rw [clampSite_of_mem hx]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (cube_subset_latticeCube m z)
        fun _ _ _ => sq_nonneg _

end Rigidity.Proofs.Multiscale

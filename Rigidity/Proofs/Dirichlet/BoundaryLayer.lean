import Rigidity.Percolation.IntegerCube

/-!
# Boundary layers of a lattice cube

The boundary layer of width `r` of an integer cube of side `N` consists of its points with some
coordinate among the `r` extreme slices on either side; it has at most `2 d r N^{d-1}` points.
With Hölder's inequality on a subset, for `p ≥ 2`,
`N^{-d} Σ_{layer} g² ≤ (2 d r / N)^{1 - 2/p} (N^{-d} Σ_{cube} |g|^p)^{2/p}`.
This is the boundary-layer estimate of Armstrong–Dario, Step 3 of the proof of Lemma 6.2 and the
corresponding step in the proof of Lemma 6.3, where `r = 2·3^l` and `N = 3^m` with `l < m`.
-/

open Finset

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Hölder's inequality on a subset**: for `p ≥ 2` and `S ⊆ T`,
`Σ_{x∈S} g(x)² ≤ |S|^{1 - 2/p} (Σ_{x∈T} |g(x)|^p)^{2/p}`. -/
theorem sum_sq_le_card_rpow_mul_sum_rpow {ι : Type*} {S T : Finset ι} (hST : S ⊆ T)
    (g : ι → ℝ) {p : ℝ} (hp : 2 ≤ p) :
    ∑ x ∈ S, g x ^ 2 ≤ (#S : ℝ) ^ (1 - 2 / p) * (∑ x ∈ T, |g x| ^ p) ^ (2 / p) := by
  have hp0 : p ≠ 0 := by positivity
  set r : ℝ := p / 2 with hr
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hr0 : r ≠ 0 := by positivity
  have hS := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S hr1 (f := fun x => g x ^ 2)
    fun x _ => sq_nonneg _
  have hpow : ∀ x, (g x ^ 2) ^ r = |g x| ^ p := by
    intro x
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    rw [hr]
    push_cast
    ring
  simp only [hpow] at hS
  have hsub : ∑ x ∈ S, |g x| ^ p ≤ ∑ x ∈ T, |g x| ^ p :=
    Finset.sum_le_sum_of_subset_of_nonneg hST fun _ _ _ => by positivity
  have hA : 0 ≤ ∑ x ∈ S, g x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ ∑ x ∈ T, |g x| ^ p := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ x ∈ S, g x ^ 2 = ((∑ x ∈ S, g x ^ 2) ^ r) ^ r⁻¹ := (Real.rpow_rpow_inv hA hr0).symm
    _ ≤ ((#S : ℝ) ^ (r - 1) * ∑ x ∈ T, |g x| ^ p) ^ r⁻¹ :=
        Real.rpow_le_rpow (by positivity)
          (hS.trans (mul_le_mul_of_nonneg_left hsub (by positivity))) (by positivity)
    _ = (#S : ℝ) ^ (1 - 2 / p) * (∑ x ∈ T, |g x| ^ p) ^ (2 / p) := by
        rw [Real.mul_rpow (by positivity) hB, ← Real.rpow_mul (by positivity)]
        congr 2
        · rw [hr]
          field_simp
        · rw [hr]
          field_simp

/-- **Normalized Hölder inequality on a subset**: for `p ≥ 2`, `S ⊆ T` and `N > 0`,
`N⁻¹ Σ_{x∈S} g(x)² ≤ (|S|/N)^{1 - 2/p} (N⁻¹ Σ_{x∈T} |g(x)|^p)^{2/p}`. -/
theorem sum_sq_div_le_card_div_rpow_mul {ι : Type*} {S T : Finset ι} (hST : S ⊆ T)
    (g : ι → ℝ) {p : ℝ} (hp : 2 ≤ p) {N : ℝ} (hN : 0 < N) :
    (∑ x ∈ S, g x ^ 2) / N ≤
      ((#S : ℝ) / N) ^ (1 - 2 / p) * ((∑ x ∈ T, |g x| ^ p) / N) ^ (2 / p) := by
  have hB : 0 ≤ ∑ x ∈ T, |g x| ^ p := Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.div_rpow (by positivity) hN.le, Real.div_rpow hB hN.le, div_mul_div_comm,
    ← Real.rpow_add hN, show 1 - 2 / p + 2 / p = 1 by ring, Real.rpow_one]
  exact div_le_div_of_nonneg_right (sum_sq_le_card_rpow_mul_sum_rpow hST g hp) hN.le

/-- The boundary layer of width `r` of an integer cube: its points with some coordinate among the
`r` lowest or the `r` highest values. -/
noncomputable def cubeLayer (Q : IntegerCube d) (r : ℕ) : Finset (Vertex d) :=
  Q.vertices.filter fun x => ∃ i, x i < Q.corner i + r ∨ Q.corner i + Q.size ≤ x i + r

theorem cubeLayer_subset (Q : IntegerCube d) (r : ℕ) : cubeLayer Q r ⊆ Q.vertices :=
  Finset.filter_subset _ _

/-- The integer cube of side `N` has `N^d` points. -/
theorem card_vertices (Q : IntegerCube d) : #Q.vertices = Q.size ^ d := by
  simp [IntegerCube.vertices, Int.card_Ico]

/-- A slab of an integer cube: the coordinate `i` is restricted to `J`. -/
theorem card_piFinset_update (Q : IntegerCube d) (i : Fin d) (J : Finset ℤ) :
    #(Fintype.piFinset (Function.update
      (fun k => Finset.Ico (Q.corner k) (Q.corner k + (Q.size : ℤ))) i J)) =
      #J * Q.size ^ (d - 1) := by
  classical
  rw [Fintype.card_piFinset]
  have hfun : (fun k => #(Function.update
      (fun k => Finset.Ico (Q.corner k) (Q.corner k + (Q.size : ℤ))) i J k)) =
      Function.update (fun _ => Q.size) i #J := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Function.update_of_ne hk, Int.card_Ico]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.prod_const]
  simp [Finset.card_sdiff]

/-- **The boundary layer of width `r` of a cube of side `N` has at most `2 d r N^{d-1}` points.** -/
theorem card_cubeLayer_le (Q : IntegerCube d) (r : ℕ) :
    #(cubeLayer Q r) ≤ 2 * d * r * Q.size ^ (d - 1) := by
  classical
  set I : Fin d → Finset ℤ := fun k => Finset.Ico (Q.corner k) (Q.corner k + (Q.size : ℤ))
  set low : Fin d → Finset (Vertex d) := fun i =>
    Fintype.piFinset (Function.update I i (Finset.Ico (Q.corner i) (Q.corner i + r)))
  set high : Fin d → Finset (Vertex d) := fun i =>
    Fintype.piFinset (Function.update I i
      (Finset.Ico (Q.corner i + Q.size - r) (Q.corner i + Q.size)))
  have hsub : cubeLayer Q r ⊆ Finset.univ.biUnion fun i => low i ∪ high i := by
    intro x hx
    obtain ⟨hxQ, i, hi⟩ := Finset.mem_filter.mp hx
    rw [IntegerCube.mem_vertices] at hxQ
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    have hmem : ∀ J : Finset ℤ, x i ∈ J →
        x ∈ Fintype.piFinset (Function.update I i J) := by
      intro J hJ
      refine Fintype.mem_piFinset.mpr fun k => ?_
      by_cases hk : k = i
      · subst hk
        simpa using hJ
      · rw [Function.update_of_ne hk]
        exact Finset.mem_Ico.mpr (hxQ k)
    rcases hi with hi | hi
    · exact Finset.mem_union_left _ (hmem _ (Finset.mem_Ico.mpr ⟨(hxQ i).1, hi⟩))
    · exact Finset.mem_union_right _ (hmem _ (Finset.mem_Ico.mpr ⟨by linarith, (hxQ i).2⟩))
  have hlow : ∀ i, #(low i) = r * Q.size ^ (d - 1) := fun i => by
    simp only [low, I, card_piFinset_update, Int.card_Ico]
    simp
  have hhigh : ∀ i, #(high i) = r * Q.size ^ (d - 1) := fun i => by
    simp only [high, I, card_piFinset_update, Int.card_Ico]
    simp
  calc #(cubeLayer Q r) ≤ #(Finset.univ.biUnion fun i => low i ∪ high i) :=
        Finset.card_le_card hsub
    _ ≤ ∑ i, #(low i ∪ high i) := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin d, (#(low i) + #(high i)) :=
        Finset.sum_le_sum fun i _ => Finset.card_union_le _ _
    _ = 2 * d * r * Q.size ^ (d - 1) := by
        simp only [hlow, hhigh, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring

/-- The proportion of a cube of side `N` in its boundary layer of width `r` is at most
`2 d r / N`. -/
theorem card_cubeLayer_div_le (Q : IntegerCube d) (hN : 0 < Q.size) (r : ℕ) :
    (#(cubeLayer Q r) : ℝ) / (Q.size : ℝ) ^ d ≤ 2 * d * r / Q.size := by
  have hN' : (0 : ℝ) < Q.size := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by positivity) hN']
  have hcard : (#(cubeLayer Q r) : ℝ) ≤ 2 * d * r * (Q.size : ℝ) ^ (d - 1) := by
    exact_mod_cast card_cubeLayer_le Q r
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.cast_zero, mul_zero, zero_mul] at hcard ⊢
    nlinarith
  · calc (#(cubeLayer Q r) : ℝ) * Q.size ≤ 2 * d * r * (Q.size : ℝ) ^ (d - 1) * Q.size :=
          mul_le_mul_of_nonneg_right hcard hN'.le
      _ = 2 * d * r * (Q.size : ℝ) ^ d := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hd]

/-- **Boundary-layer estimate**: for `p ≥ 2`, the normalized sum of `g²` over the boundary layer
of width `r` of a cube of side `N` is at most
`(2 d r / N)^{1 - 2/p} (N^{-d} Σ_{cube} |g|^p)^{2/p}`. -/
theorem sum_sq_cubeLayer_div_le (Q : IntegerCube d) (hN : 0 < Q.size) (r : ℕ)
    (g : Vertex d → ℝ) {p : ℝ} (hp : 2 ≤ p) :
    (∑ x ∈ cubeLayer Q r, g x ^ 2) / (Q.size : ℝ) ^ d ≤
      (2 * d * r / Q.size) ^ (1 - 2 / p) *
        ((∑ x ∈ Q.vertices, |g x| ^ p) / (Q.size : ℝ) ^ d) ^ (2 / p) := by
  have hN' : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  refine (sum_sq_div_le_card_div_rpow_mul (cubeLayer_subset Q r) g hp hN').trans ?_
  have he : 0 ≤ 1 - 2 / p := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hp
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by positivity) (card_cubeLayer_div_le Q hN r) he) (by positivity)

end Rigidity.Dirichlet

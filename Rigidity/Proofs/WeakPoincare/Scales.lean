import Rigidity.Proofs.WeakPoincare.Ball

/-!
# Good scales for the weak Poincaré inequality on balls of the infinite cluster

Ingredients of the probabilistic part of the weak Poincaré inequality on balls of `𝒞_∞` in every
dimension `d ≥ 2`: the triple `enl 1 m y` of the triadic cube of scale `m` containing `y` is covered
by the `3^d` triadic cubes of scale `m` whose index is within `1` of that of `y`
(`idx_sub_le_of_mem_enl`, `sum_enl_le_sum_cubes`). If the reach of the partition is dominated by
`ss` and `Σ_{□_m(e)} ss^{d(d+2)} ≤ C 3^{dm}` on these cubes, with `C 3^{dm + 2d(d+2)} < 3^{d(d+2)m}`,
then the partition cubes of the vertices of the triple have scale at most `m - 3` and
`Σ_{triple} ss^{d(d+2)} ≤ 3^d C 3^{dm}` (`goodScale_consequences`): the hypotheses of
`sum_sq_sub_finAvg_clusterBall_le`. This is the planar argument of
`Rigidity.Green.goodScale_consequences` in every dimension.
-/

open Finset LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
open scoped ENNReal

namespace Rigidity.WeakPoincare

variable {d : ℕ}

/-- The vertices of the triple `enl 1 m y` lie in the triadic cubes of scale `m` whose index is
within `1` of that of `y`. -/
theorem idx_sub_le_of_mem_enl {m : ℕ} {y z : Vertex d} (hz : z ∈ enl 1 m y) (i : Fin d) :
    |idx m z i - idx m y i| ≤ 1 := by
  rw [enl, mem_box] at hz
  have h1 := hz i
  have hh := two_mul_halfSide_add_one m
  have hs : halfSide (m + 1) = 3 * halfSide m + 1 := rfl
  have hP : (0 : ℤ) < 3 ^ m := by positivity
  have hc : center m y i = 3 ^ m * idx m y i := rfl
  rw [abs_le] at h1 ⊢
  set a := idx m y i
  have hlo : (a - 1) * 3 ^ m ≤ z i + halfSide m := by
    have e : (a - 1) * 3 ^ m = 3 ^ m * a - 3 ^ m := by ring
    linarith [h1.1]
  have hhi : z i + halfSide m < (a + 2) * 3 ^ m := by
    have e : (a + 2) * 3 ^ m = 3 ^ m * a + 2 * 3 ^ m := by ring
    linarith [h1.2]
  have g1 : a - 1 ≤ idx m z i := (Int.le_ediv_iff_mul_le hP).2 hlo
  have g2 : idx m z i < a + 2 := (Int.ediv_lt_iff_lt_mul hP).2 hhi
  constructor <;> linarith

/-- The sum of a nonnegative function over a union is at most the sum of its sums. -/
theorem sum_biUnion_le_sum_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (T : ι → Finset (Vertex d)) {f : Vertex d → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ s.biUnion T, f z ≤ ∑ i ∈ s, ∑ z ∈ T i, f z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := T a) (s₂ := s.biUnion T) (f := f)
    have h0 : 0 ≤ ∑ z ∈ T a ∩ s.biUnion T, f z := Finset.sum_nonneg fun z _ => hf z
    linarith

/-- A vertex lies in the triadic cube of scale `m` of its own index. -/
theorem mem_triadicCube_idx_self (m : ℕ) (z : Vertex d) :
    z ∈ (⟨m, idx m z⟩ : TriadicCube d).toIntegerCube.vertices := by
  rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
  exact mem_cube_self m z

/-- **The `3^d` subcubes of the triple.** For `f ≥ 0`,
`Σ_{z ∈ enl 1 m y} f(z) ≤ Σ_{|e - idx_m(y)| ≤ 1} Σ_{z ∈ □_m(e)} f(z)`. -/
theorem sum_enl_le_sum_cubes (m : ℕ) (y : Vertex d) {f : Vertex d → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ enl 1 m y, f z ≤
      ∑ e ∈ box (idx m y) 1, ∑ z ∈ (⟨m, e⟩ : TriadicCube d).toIntegerCube.vertices, f z := by
  classical
  have hsub : enl 1 m y ⊆ (box (idx m y) 1).biUnion
      (fun e => (⟨m, e⟩ : TriadicCube d).toIntegerCube.vertices) := by
    intro z hz
    rw [Finset.mem_biUnion]
    exact ⟨idx m z, mem_box.2 fun i => idx_sub_le_of_mem_enl hz i, mem_triadicCube_idx_self m z⟩
  calc ∑ z ∈ enl 1 m y, f z
      ≤ ∑ z ∈ (box (idx m y) 1).biUnion
          (fun e => (⟨m, e⟩ : TriadicCube d).toIntegerCube.vertices), f z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hf z
    _ ≤ _ := sum_biUnion_le_sum_sum _ _ hf

theorem card_box_one (c : Vertex d) : ((box c 1).card : ℝ) = 3 ^ d := by
  rw [card_box c (by norm_num)]
  norm_num

/-- **A good scale.** If the reach of the partition is dominated by `ss` and
`Σ_{□_m(e)} ss^{d(d+2)} ≤ C 3^{dm}` on the `3^d` cubes of scale `m` around `y`, with
`C 3^{dm + 2d(d+2)} < 3^{d(d+2)m}`, then the partition cubes of the vertices of the triple have
scale at most `m - 3` and `Σ_{triple} ss^{d(d+2)} ≤ 3^d C 3^{dm}`. -/
theorem goodScale_consequences {ω : Configuration d} (hP : PartitionEvent ω) {y : Vertex d}
    {m : ℕ} {Cf : ℝ} (ss : Vertex d → ℝ)
    (hreach : ∀ z, partitionReach ω z ≤ ENNReal.ofReal (ss z))
    (hgood : ∀ e ∈ box (idx m y) 1,
      ∑ z ∈ (⟨m, e⟩ : TriadicCube d).toIntegerCube.vertices, ss z ^ (d * (d + 2)) ≤
        Cf * 3 ^ (d * m))
    (hm : Cf * 3 ^ (d * m + 2 * (d * (d + 2))) < 3 ^ (d * (d + 2) * m)) :
    (∀ z ∈ enl 1 m y, (partitionCube ω z).scale + 3 ≤ m) ∧
      ∑ z ∈ enl 1 m y, ss z ^ (d * (d + 2)) ≤ 3 ^ d * Cf * 3 ^ (d * m) := by
  set τ := d * (d + 2) with hτ
  have h3 : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ ss z := fun z =>
    three_pow_le_of_partitionReach_le (three_pow_scale_le_partitionReach hP z) (hreach z)
  have hss1 : ∀ z, 1 ≤ ss z := fun z => (one_le_pow₀ (by norm_num)).trans (h3 z)
  have hss0 : ∀ z, 0 ≤ ss z := fun z => zero_le_one.trans (hss1 z)
  have hpt : ∀ z ∈ enl 1 m y, ss z ^ τ ≤ Cf * 3 ^ (d * m) := by
    intro z hz
    refine le_trans ?_ (hgood (idx m z) (mem_box.2 fun i => idx_sub_le_of_mem_enl hz i))
    exact Finset.single_le_sum (f := fun z => ss z ^ τ) (fun z _ => pow_nonneg (hss0 z) _)
      (mem_triadicCube_idx_self m z)
  refine ⟨fun z hz => ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hk : m ≤ (partitionCube ω z).scale + 2 := by omega
    set k := (partitionCube ω z).scale
    have h4 : (3 : ℝ) ^ (τ * k) ≤ Cf * 3 ^ (d * m) := by
      calc (3 : ℝ) ^ (τ * k) = ((3 : ℝ) ^ k) ^ τ := by rw [← pow_mul, mul_comm]
        _ ≤ ss z ^ τ := pow_le_pow_left₀ (by positivity) (h3 z) τ
        _ ≤ _ := hpt z hz
    have h5 : (3 : ℝ) ^ (τ * m) ≤ 3 ^ (τ * k) * 3 ^ (2 * τ) := by
      rw [← pow_add]
      refine pow_le_pow_right₀ (by norm_num) ?_
      calc τ * m ≤ τ * (k + 2) := Nat.mul_le_mul_left τ hk
        _ = τ * k + 2 * τ := by ring
    have h7 : (0 : ℝ) < 3 ^ (2 * τ) := by positivity
    have h8 := mul_le_mul_of_nonneg_right h4 h7.le
    have h6 : Cf * 3 ^ (d * m) * 3 ^ (2 * τ) = Cf * 3 ^ (d * m + 2 * τ) := by
      rw [pow_add]
      ring
    linarith
  · calc ∑ z ∈ enl 1 m y, ss z ^ τ
        ≤ ∑ e ∈ box (idx m y) 1, ∑ z ∈ (⟨m, e⟩ : TriadicCube d).toIntegerCube.vertices,
            ss z ^ τ := sum_enl_le_sum_cubes m y fun z => pow_nonneg (hss0 z) _
      _ ≤ ∑ _e ∈ box (idx m y) 1, Cf * 3 ^ (d * m) := Finset.sum_le_sum fun e he => hgood e he
      _ = 3 ^ d * Cf * 3 ^ (d * m) := by
          rw [Finset.sum_const, nsmul_eq_mul, card_box_one]
          ring

end Rigidity.WeakPoincare

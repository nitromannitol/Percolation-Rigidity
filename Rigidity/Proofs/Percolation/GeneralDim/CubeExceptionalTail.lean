import Rigidity.Proofs.Percolation.GeneralDim.CubeNuSubadditiveError
import Rigidity.Proofs.Partition.Resolution

/-!
# The expected number of exceptional vertices

A vertex `x` of a triadic cube `U` is exceptional at scale `n` (`IsSubcubeExceptional`) only if its
subcube `V(x)` of scale `n` is unresolved, or its partition cube `□` (side `s`) is large compared
with the distance of `x` to the complement of `V(x)`: the region `□.parent ∪ (x + Q_{s-1})` lies
within `ℓ∞` distance `3s` of `x`. Both events are controlled by the exponential moments of the
partition sizes (Armstrong and Dario, Proposition 2.1 and the bound after Definition 2.9): the
first has probability at most `C exp(-c 3ⁿ)`, the second at most `e exp(-m / (3θ))` for a vertex at
distance `m` from the faces of its subcube. Summing over the vertices, the expected number of
exceptional vertices of `U` is at most `|U| (C exp(-c 3ⁿ) + C' 3^{-n})` (the bound on the boundary
layers of the subcubes in the proof of Lemma 4.8 of Armstrong and Dario).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The distance of a vertex to the faces of a triadic cube, in direction `i`. -/
def TriadicCube.margin (V : TriadicCube d) (x : Vertex d) (i : Fin d) : ℤ :=
  min (x i - V.toIntegerCube.corner i) (V.toIntegerCube.corner i + 3 ^ V.scale - 1 - x i)

/-- **The local path region lies in the subcube** if the partition cube is small compared with the
margins. -/
theorem region_subset_triadicCubeAt {ω : Configuration d} (hP : PartitionEvent ω) {n : ℕ}
    {x : Vertex d}
    (h : ∀ i, (3 : ℤ) ^ ((partitionCube ω x).scale + 1) ≤ (triadicCubeAt n x).margin x i) :
    (partitionCube ω x).parent.vertices ∪ cubeAt x (3 ^ (partitionCube ω x).scale - 1) ⊆
      (triadicCubeAt n x).vertices := by
  set V := triadicCubeAt n x
  set s := (partitionCube ω x).scale
  have hxQ := mem_partitionCube hP x
  have hclose : ∀ y ∈ (partitionCube ω x).parent.vertices ∪ cubeAt x (3 ^ s - 1), ∀ i,
      |y i - x i| < (3 : ℤ) ^ (s + 1) := by
    intro y hy i
    rcases hy with hy | hy
    · have := TriadicCube.abs_coord_sub_lt_side hy
        ((partitionCube ω x).vertices_subset_parent hxQ) i
      exact this
    · have h1 : |y i - x i| ≤ ((3 ^ s - 1 : ℕ) : ℤ) := hy i
      have h2 : ((3 ^ s - 1 : ℕ) : ℤ) < (3 : ℤ) ^ (s + 1) := by
        have : 3 ^ s - 1 < 3 ^ (s + 1) := by
          have := Nat.one_le_pow s 3 (by norm_num)
          rw [pow_succ]
          omega
        exact_mod_cast this
      exact h1.trans_lt h2
  intro y hy
  refine TriadicCube.mem_of_coord_bounds fun i => ?_
  have hm := h i
  unfold TriadicCube.margin at hm
  rw [le_min_iff] at hm
  have hc := hclose y hy i
  rw [abs_lt] at hc
  constructor <;> omega

/-- A measurable majorant of the exceptional vertices: some vertex of the subcube has a partition
size larger than the subcube, or the partition size at the vertex exceeds a third of a margin. -/
def ExceptionalMajorant (ω : Configuration d) (n : ℕ) (x : Vertex d) : Prop :=
  (∃ z ∈ (triadicCubeAt n x).toIntegerCube.vertices,
      (3 : ℝ) ^ n < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) ∨
    ∃ i, ((triadicCubeAt n x).margin x i : ℝ) <
      3 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x

theorem measurableSet_exceptionalMajorant (n : ℕ) (x : Vertex d) :
    MeasurableSet {ω : Configuration d | ExceptionalMajorant ω n x} := by
  have hm : ∀ z : Vertex d, Measurable fun ω : Configuration d =>
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z := fun z =>
    TriadicCube.measurable_stoppingSize (fun ω => TriadicCube.goodCubes ω)
      (fun Q => Q.measurableSet_mem_goodCubes) z
  unfold ExceptionalMajorant
  exact measurableSet_setOf.2 ((Measurable.exists fun z => measurable_const.and
    (measurableSet_setOf.1 (measurableSet_lt measurable_const (hm z)))).or
    (Measurable.exists fun i => measurableSet_setOf.1
      (measurableSet_lt measurable_const ((hm x).const_mul 3))))

/-- On the partition event, exceptional vertices satisfy the majorant. -/
theorem exceptionalMajorant_of_isSubcubeExceptional {ω : Configuration d}
    (hP : PartitionEvent ω) {n : ℕ} {x : Vertex d} (h : IsSubcubeExceptional ω n x) :
    ExceptionalMajorant ω n x := by
  unfold IsSubcubeExceptional at h
  by_cases hres : PartitionResolved ω (triadicCubeAt n x)
  · right
    have hreg : ¬ ((partitionCube ω x).parent.vertices ∪
        cubeAt x (3 ^ (partitionCube ω x).scale - 1) ⊆ (triadicCubeAt n x).vertices) :=
      fun hreg => h ⟨hres, hreg⟩
    by_contra hcon
    push Not at hcon
    refine hreg (region_subset_triadicCubeAt hP fun i => ?_)
    have h1 := hcon i
    rw [stoppingSize_goodCubes_eq hP x] at h1
    have h2 : ((3 : ℤ) ^ ((partitionCube ω x).scale + 1) : ℝ) ≤
        ((triadicCubeAt n x).margin x i : ℝ) := by
      push_cast
      rw [pow_succ]
      linarith
    exact_mod_cast h2
  · left
    unfold PartitionResolved at hres
    push Not at hres
    obtain ⟨z, hz, hlt⟩ := hres
    refine ⟨z, ((triadicCubeAt n x).mem_toIntegerCube_vertices z).2 hz, ?_⟩
    rw [stoppingSize_goodCubes_eq hP z]
    rw [scale_triadicCubeAt] at hlt
    exact pow_lt_pow_right₀ (by norm_num) hlt

/-- `exp(-min(u, w) / a) ≤ exp(-u / a) + exp(-w / a)`. -/
theorem exp_neg_min_div_le (u w a : ℝ) :
    Real.exp (-(min u w) / a) ≤ Real.exp (-u / a) + Real.exp (-w / a) := by
  rcases min_choice u w with h | h <;> rw [h] <;>
    linarith [Real.exp_pos (-u / a), Real.exp_pos (-w / a)]

/-- **Sums over a slice.** A function of one coordinate summed over an integer cube. -/
theorem IntegerCube.sum_vertices_comp_apply (R : IntegerCube d) (i : Fin d) (h : ℤ → ℝ) :
    ∑ x ∈ R.vertices, h (x i) =
      (R.size : ℝ) ^ (d - 1) * ∑ t ∈ Finset.Ico (R.corner i) (R.corner i + R.size), h t := by
  unfold IntegerCube.vertices
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : Vertex d => x i)
    (t := Finset.Ico (R.corner i) (R.corner i + R.size))
    (fun x hx => Fintype.mem_piFinset.1 hx i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.sum_congr rfl (g := fun _ => h t) fun x hx => by rw [(Finset.mem_filter.1 hx).2],
    Finset.sum_const, nsmul_eq_mul]
  have hcard := Fintype.card_filter_piFinset_eq_of_mem
    (fun j => Finset.Ico (R.corner j) (R.corner j + R.size)) i ht
  rw [hcard]
  have hj : ∀ j, (Finset.Ico (R.corner j) (R.corner j + (R.size : ℤ))).card = R.size := by
    intro j
    rw [Int.card_Ico]
    omega
  have hprod : ∏ j ∈ Finset.univ.erase i, (Finset.Ico (R.corner j) (R.corner j + R.size)).card =
      R.size ^ (d - 1) := by
    simp only [hj, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  push_cast
  ring

/-- A sum over an integer interval of a nonnegative function of an injective relabelling into
`range L` is at most the sum over `range L`. -/
theorem sum_Ico_le_sum_range {c : ℤ} {L : ℕ} (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (φ : ℤ → ℕ)
    (hφ : ∀ t ∈ Finset.Ico c (c + L), φ t < L)
    (hinj : ∀ t ∈ Finset.Ico c (c + L), ∀ t' ∈ Finset.Ico c (c + L), φ t = φ t' → t = t') :
    ∑ t ∈ Finset.Ico c (c + L), f (φ t) ≤ ∑ k ∈ Finset.range L, f k := by
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hf k
  intro k hk
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hk
  exact Finset.mem_range.2 (hφ t ht)

/-- **Exponential sums over the margins of a cube.** -/
theorem sum_exp_neg_margin_le (V : TriadicCube d) (i : Fin d) {a : ℝ} (ha : 0 < a) :
    ∑ x ∈ V.toIntegerCube.vertices, Real.exp (-(V.margin x i : ℝ) / a) ≤
      2 * ((3 : ℝ) ^ V.scale) ^ (d - 1) * (1 - Real.exp (-1 / a))⁻¹ := by
  set c := V.toIntegerCube.corner i
  set L : ℕ := V.toIntegerCube.size
  have hL : (L : ℤ) = 3 ^ V.scale := by
    change ((3 ^ V.scale : ℕ) : ℤ) = _
    push_cast
    rfl
  have hLr : (L : ℝ) = (3 : ℝ) ^ V.scale := by
    change ((3 ^ V.scale : ℕ) : ℝ) = _
    push_cast
    rfl
  set r := Real.exp (-1 / a)
  have hr0 : r ≠ 0 := (Real.exp_pos _).ne'
  have hr1 : r < 1 := by
    have h := Real.exp_lt_exp.2 (div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) ha)
    rwa [Real.exp_zero] at h
  have hgeom : ∑ k ∈ Finset.range L, Real.exp (-(k : ℝ) / a) ≤ (1 - r)⁻¹ := by
    have e : ∀ k : ℕ, Real.exp (-(k : ℝ) / a) = r ^ k := by
      intro k
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [e]
    rw [geom_sum_eq hr1.ne]
    have h1r : 0 < 1 - r := by linarith
    have hrL : 0 ≤ r ^ L := pow_nonneg (Real.exp_pos _).le L
    calc (r ^ L - 1) / (r - 1) = (1 - r ^ L) / (1 - r) := by
          rw [div_eq_div_iff (by linarith) (by linarith)]
          ring
      _ ≤ 1 / (1 - r) := div_le_div_of_nonneg_right (by linarith) h1r.le
      _ = (1 - r)⁻¹ := one_div _
  have hmin : ∀ x : Vertex d, Real.exp (-(V.margin x i : ℝ) / a) ≤
      Real.exp (-((x i - c : ℤ) : ℝ) / a) + Real.exp (-((c + 3 ^ V.scale - 1 - x i : ℤ) : ℝ) / a) := by
    intro x
    have := exp_neg_min_div_le ((x i - c : ℤ) : ℝ) ((c + 3 ^ V.scale - 1 - x i : ℤ) : ℝ) a
    unfold TriadicCube.margin
    push_cast at this ⊢
    exact this
  have h1 : ∑ t ∈ Finset.Ico c (c + L), Real.exp (-((t - c : ℤ) : ℝ) / a) ≤ (1 - r)⁻¹ := by
    have := sum_Ico_le_sum_range (c := c) (L := L) (fun k => Real.exp (-(k : ℝ) / a))
      (fun k => (Real.exp_pos _).le) (fun t => (t - c).toNat)
      (fun t ht => by rw [Finset.mem_Ico] at ht; omega)
      (fun t ht t' ht' h => by rw [Finset.mem_Ico] at ht ht'; omega)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun t ht => ?_)) (this.trans hgeom)
    rw [Finset.mem_Ico] at ht
    show Real.exp (-((t - c : ℤ) : ℝ) / a) = Real.exp (-(((t - c).toNat : ℕ) : ℝ) / a)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  have h2 : ∑ t ∈ Finset.Ico c (c + L),
      Real.exp (-((c + 3 ^ V.scale - 1 - t : ℤ) : ℝ) / a) ≤ (1 - r)⁻¹ := by
    have := sum_Ico_le_sum_range (c := c) (L := L) (fun k => Real.exp (-(k : ℝ) / a))
      (fun k => (Real.exp_pos _).le) (fun t => (c + 3 ^ V.scale - 1 - t).toNat)
      (fun t ht => by rw [Finset.mem_Ico] at ht; omega)
      (fun t ht t' ht' h => by rw [Finset.mem_Ico] at ht ht'; omega)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun t ht => ?_)) (this.trans hgeom)
    rw [Finset.mem_Ico] at ht
    show Real.exp (-((c + 3 ^ V.scale - 1 - t : ℤ) : ℝ) / a) =
      Real.exp (-(((c + 3 ^ V.scale - 1 - t).toNat : ℕ) : ℝ) / a)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  have hs1 := V.toIntegerCube.sum_vertices_comp_apply i (fun t => Real.exp (-((t - c : ℤ) : ℝ) / a))
  have hs2 := V.toIntegerCube.sum_vertices_comp_apply i
    (fun t => Real.exp (-((c + 3 ^ V.scale - 1 - t : ℤ) : ℝ) / a))
  beta_reduce at hs1 hs2
  have hLd : 0 ≤ (L : ℝ) ^ (d - 1) := by positivity
  calc ∑ x ∈ V.toIntegerCube.vertices, Real.exp (-(V.margin x i : ℝ) / a)
      ≤ ∑ x ∈ V.toIntegerCube.vertices, (Real.exp (-((x i - c : ℤ) : ℝ) / a) +
          Real.exp (-((c + 3 ^ V.scale - 1 - x i : ℤ) : ℝ) / a)) :=
        Finset.sum_le_sum fun x _ => hmin x
    _ = (L : ℝ) ^ (d - 1) * ∑ t ∈ Finset.Ico c (c + L), Real.exp (-((t - c : ℤ) : ℝ) / a) +
        (L : ℝ) ^ (d - 1) * ∑ t ∈ Finset.Ico c (c + L),
          Real.exp (-((c + 3 ^ V.scale - 1 - t : ℤ) : ℝ) / a) := by
        rw [Finset.sum_add_distrib, hs1, hs2]
    _ ≤ (L : ℝ) ^ (d - 1) * (1 - r)⁻¹ + (L : ℝ) ^ (d - 1) * (1 - r)⁻¹ := by
        gcongr
    _ = 2 * ((3 : ℝ) ^ V.scale) ^ (d - 1) * (1 - r)⁻¹ := by rw [hLr]; ring

end Rigidity.Percolation

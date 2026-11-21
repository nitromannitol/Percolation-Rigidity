import Rigidity.Proofs.Partition.BadCubes
import Rigidity.Percolation.IntegerCubeCoalescenceScales

/-!
# Large partition cubes are controlled by bad cubes

Let `Q_m` be the triadic cube of scale `m` centred at the origin. If no bad cube of scale at least
`J` has its centre within eleven of its side lengths of `Q_m`, then every partition cube meeting
`Q_m` has scale at most `J`, and for every `τ`

`∑_{x ∈ Q_m} 3^{τ n(x)} ≤ ∑_{j < J} 3^{τ (j + 1)} (22 · 3^j + 1)^d N_j`,

where `n(x)` is the scale of the partition cube of `x` and `N_j` is the number of bad cubes of
scale `j` whose centre is within eleven of their side lengths of `Q_m`: each vertex is charged to
a bad cube near it (`exists_bad_near_partitionCube`), and a bad cube of scale `j` is charged by at
most `(22 · 3^j + 1)^d` vertices.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The indices `ι` with `|ι_i| ≤ 3^{m-j} + 11`: they contain the indices of the cubes of scale
`j` whose centre is within eleven of their side lengths of the cube of scale `m` centred at the
origin. -/
noncomputable def nearIndices (d m j : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-((3 : ℤ) ^ (m - j) + 11)) ((3 : ℤ) ^ (m - j) + 11)

theorem card_nearIndices (d m j : ℕ) :
    ((nearIndices d m j).card : ℝ) = (2 * (3 : ℝ) ^ (m - j) + 23) ^ d := by
  rw [nearIndices, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  have h : ((3 : ℤ) ^ (m - j) + 11 + 1 - -((3 : ℤ) ^ (m - j) + 11)).toNat =
      2 * 3 ^ (m - j) + 23 := by
    have hpos : (0 : ℤ) ≤ 3 ^ (m - j) := by positivity
    have : (3 : ℤ) ^ (m - j) + 11 + 1 - -((3 : ℤ) ^ (m - j) + 11) =
        ((2 * 3 ^ (m - j) + 23 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [h]
  push_cast
  ring

/-- The index of a cube whose centre is near the cube of scale `m` centred at the origin lies in
`nearIndices`. -/
theorem index_mem_nearIndices {m : ℕ} {T : TriadicCube d} {x : Vertex d}
    (hx : x ∈ (⟨m, 0⟩ : TriadicCube d).vertices) (hT : ∀ i, |x i - T.center i| ≤ 11 * T.side) :
    T.index ∈ nearIndices d m T.scale := by
  rw [nearIndices, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hxi := ((⟨m, 0⟩ : TriadicCube d).mem_vertices_iff_coord x).1 hx i
  have hc0 : (⟨m, 0⟩ : TriadicCube d).center i = 0 := by
    simp [TriadicCube.center]
  have hr : (⟨m, 0⟩ : TriadicCube d).radius ≤ (3 : ℤ) ^ m := by
    have h := (⟨m, 0⟩ : TriadicCube d).side_eq_two_mul_radius_add_one
    have hs : (⟨m, 0⟩ : TriadicCube d).side = (3 : ℤ) ^ m := rfl
    have hpos : (0 : ℤ) < 3 ^ m := by positivity
    omega
  rw [hc0] at hxi
  have hTi := abs_le.mp (hT i)
  have hpos : (0 : ℤ) < (3 : ℤ) ^ T.scale := by positivity
  have hpow : (3 : ℤ) ^ m ≤ (3 : ℤ) ^ T.scale * (3 : ℤ) ^ (m - T.scale) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hcT : T.center i = (3 : ℤ) ^ T.scale * T.index i := rfl
  have hsT : T.side = (3 : ℤ) ^ T.scale := rfl
  rw [hcT, hsT] at hTi
  constructor
  · have h : (3 : ℤ) ^ T.scale * (-((3 : ℤ) ^ (m - T.scale) + 11)) ≤
        (3 : ℤ) ^ T.scale * T.index i := by nlinarith
    exact le_of_mul_le_mul_left h hpos
  · have h : (3 : ℤ) ^ T.scale * T.index i ≤
        (3 : ℤ) ^ T.scale * ((3 : ℤ) ^ (m - T.scale) + 11) := by nlinarith
    exact le_of_mul_le_mul_left h hpos

/-- The indices `ι` with `|ι_i - ⌊c_i / 3^j⌋| ≤ 3^{m-j} + 11`, `c` the centre of a cube `Q`: for
`Q.scale ≤ m` they contain the indices of the cubes of scale `j` whose centre is within eleven of
their side lengths of `Q`. For `Q` of scale `m` centred at the origin these are `nearIndices d m j`.
-/
noncomputable def nearIndicesAt (Q : TriadicCube d) (m j : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (Q.center i / 3 ^ j - ((3 : ℤ) ^ (m - j) + 11))
    (Q.center i / 3 ^ j + ((3 : ℤ) ^ (m - j) + 11))

theorem card_nearIndicesAt (Q : TriadicCube d) (m j : ℕ) :
    ((nearIndicesAt Q m j).card : ℝ) = (2 * (3 : ℝ) ^ (m - j) + 23) ^ d := by
  rw [nearIndicesAt, Fintype.card_piFinset]
  have h : ∀ i : Fin d, (Finset.Icc (Q.center i / 3 ^ j - ((3 : ℤ) ^ (m - j) + 11))
      (Q.center i / 3 ^ j + ((3 : ℤ) ^ (m - j) + 11))).card = 2 * 3 ^ (m - j) + 23 := by
    intro i
    rw [Int.card_Icc]
    have : Q.center i / 3 ^ j + ((3 : ℤ) ^ (m - j) + 11) + 1 -
        (Q.center i / 3 ^ j - ((3 : ℤ) ^ (m - j) + 11)) = ((2 * 3 ^ (m - j) + 23 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  push_cast
  ring

/-- The index of a cube whose centre is near a cube `Q` of scale at most `m` lies in
`nearIndicesAt Q m`. -/
theorem index_mem_nearIndicesAt {Q : TriadicCube d} {m : ℕ} (hQm : Q.scale ≤ m)
    {T : TriadicCube d} {x : Vertex d} (hx : x ∈ Q.vertices)
    (hT : ∀ i, |x i - T.center i| ≤ 11 * T.side) :
    T.index ∈ nearIndicesAt Q m T.scale := by
  rw [nearIndicesAt, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hxi := (Q.mem_vertices_iff_coord x).1 hx i
  have hr : Q.radius ≤ Q.side := by
    have h := Q.side_eq_two_mul_radius_add_one
    have hpos : (0 : ℤ) ≤ Q.radius := by omega
    omega
  have hsQ : Q.side = (3 : ℤ) ^ Q.scale := rfl
  have hpos : (0 : ℤ) < (3 : ℤ) ^ T.scale := by positivity
  have hpow : (3 : ℤ) ^ Q.scale ≤ (3 : ℤ) ^ T.scale * (3 : ℤ) ^ (m - T.scale) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv := Int.emod_add_ediv_mul (Q.center i) ((3 : ℤ) ^ T.scale)
  have hmod0 := Int.emod_nonneg (Q.center i) hpos.ne'
  have hmod1 := Int.emod_lt_of_pos (Q.center i) hpos
  have hTi := abs_le.mp (hT i)
  have hcT : T.center i = (3 : ℤ) ^ T.scale * T.index i := rfl
  have hsT : T.side = (3 : ℤ) ^ T.scale := rfl
  rw [hcT, hsT] at hTi
  set κ := Q.center i / (3 : ℤ) ^ T.scale
  set a := (3 : ℤ) ^ T.scale
  set b := (3 : ℤ) ^ (m - T.scale)
  constructor
  · have h : a * (κ - (b + 12)) < a * T.index i := by nlinarith
    have := lt_of_mul_lt_mul_left h hpos.le
    omega
  · have h : a * T.index i < a * (κ + b + 12) := by nlinarith
    have := lt_of_mul_lt_mul_left h hpos.le
    omega

/-- The vertices of a finite set within distance `R` of a point are at most `(2R + 1)^d`. -/
theorem card_filter_near_le (A : Finset (Vertex d)) (c : Vertex d) (R : ℕ) :
    ((A.filter fun x => ∀ i, |x i - c i| ≤ (R : ℤ)).card : ℝ) ≤ (2 * (R : ℝ) + 1) ^ d := by
  classical
  let B : IntegerCube d := ⟨fun i => c i - R, 2 * R + 1⟩
  have hsub : (A.filter fun x => ∀ i, |x i - c i| ≤ (R : ℤ)) ⊆ B.vertices := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [IntegerCube.mem_vertices]
    intro i
    have := abs_le.mp (hx.2 i)
    change c i - R ≤ x i ∧ x i < c i - R + ((2 * R + 1 : ℕ) : ℤ)
    push_cast
    constructor <;> omega
  have h := Finset.card_le_card hsub
  rw [IntegerCube.card_vertices] at h
  have h' : ((A.filter fun x => ∀ i, |x i - c i| ≤ (R : ℤ)).card : ℝ) ≤
      ((B.size ^ d : ℕ) : ℝ) := by exact_mod_cast h
  refine h'.trans (le_of_eq ?_)
  change (((2 * R + 1) ^ d : ℕ) : ℝ) = _
  push_cast
  ring

open scoped Classical in
/-- **Large partition cubes are charged to bad cubes.** If no bad cube of scale at least `J` has
its centre within eleven of its side lengths of the cube `Q_m` of scale `m` centred at the
origin, then `∑_{x ∈ Q_m} 3^{τ n(x)} ≤ ∑_{j < J} 3^{τ (j + 1)} (22 · 3^j + 1)^d N_j`, with `n(x)`
the scale of the partition cube of `x` and `N_j` the number of bad cubes of scale `j` with index
in `nearIndices d m j`. -/
theorem sum_pow_scale_partitionCube_le {ω : Configuration d} (hP : PartitionEvent ω)
    (m J τ : ℕ)
    (hfar : ∀ T : TriadicCube d, J ≤ T.scale → T ∉ TriadicCube.goodCubes ω →
      ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, ¬ ∀ i, |x i - T.center i| ≤ 11 * T.side) :
    ∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
        (3 : ℝ) ^ (τ * (partitionCube ω x).scale) ≤
      ∑ j ∈ Finset.range J, (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d *
        ((nearIndices d m j).filter
          fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card := by
  set A := (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices with hAdef
  let near : Vertex d → ℕ → (Fin d → ℤ) → Prop := fun x j ι =>
    (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω ∧
      ∀ i, |x i - (⟨j, ι⟩ : TriadicCube d).center i| ≤ 11 * (3 : ℤ) ^ j
  let F : Vertex d → ℕ → (Fin d → ℤ) → ℝ := fun x j ι =>
    if near x j ι then (3 : ℝ) ^ (τ * (j + 1)) else 0
  have hF0 : ∀ x j ι, 0 ≤ F x j ι := fun x j ι => by
    simp only [F]
    split_ifs <;> positivity
  -- each vertex is charged to a bad cube near it
  have hstep : ∀ x ∈ A, (3 : ℝ) ^ (τ * (partitionCube ω x).scale) ≤
      ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, F x j ι := by
    intro x hxA
    have hx : x ∈ (⟨m, 0⟩ : TriadicCube d).vertices :=
      ((⟨m, 0⟩ : TriadicCube d).mem_toIntegerCube_vertices x).1 hxA
    obtain ⟨T, hTbad, hTscale, hTnear⟩ := exists_bad_near_partitionCube hP x
    have hTJ : T.scale < J := by
      by_contra h
      exact hfar T (not_lt.1 h) hTbad x hx hTnear
    have hTeq : (⟨T.scale, T.index⟩ : TriadicCube d) = T := rfl
    have hι := index_mem_nearIndices hx hTnear
    have hterm : F x T.scale T.index = (3 : ℝ) ^ (τ * (T.scale + 1)) := by
      simp only [F, near, hTeq]
      rw [if_pos ⟨hTbad, hTnear⟩]
    calc (3 : ℝ) ^ (τ * (partitionCube ω x).scale) ≤ (3 : ℝ) ^ (τ * (T.scale + 1)) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hTscale)
      _ = F x T.scale T.index := hterm.symm
      _ ≤ ∑ ι ∈ nearIndices d m T.scale, F x T.scale ι :=
          Finset.single_le_sum (fun ι _ => hF0 x _ ι) hι
      _ ≤ ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, F x j ι :=
          Finset.single_le_sum (f := fun j => ∑ ι ∈ nearIndices d m j, F x j ι)
            (fun j _ => Finset.sum_nonneg fun ι _ => hF0 x j ι) (Finset.mem_range.2 hTJ)
  -- each bad cube is charged by few vertices
  have hcharge : ∀ j ι, ∑ x ∈ A, F x j ι ≤
      (if (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω then
        (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d else 0) := by
    intro j ι
    by_cases hbad : (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω
    · rw [if_pos hbad]
      have hsum : ∑ x ∈ A, F x j ι =
          ∑ x ∈ A.filter (fun x => ∀ i, |x i - (⟨j, ι⟩ : TriadicCube d).center i| ≤
            ((11 * 3 ^ j : ℕ) : ℤ)), (3 : ℝ) ^ (τ * (j + 1)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [F, near]
        push_cast
        by_cases h : ∀ i, |x i - (⟨j, ι⟩ : TriadicCube d).center i| ≤ 11 * (3 : ℤ) ^ j
        · rw [if_pos ⟨hbad, h⟩, if_pos h]
        · rw [if_neg (fun h' => h h'.2), if_neg h]
      rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hcard := card_filter_near_le A (⟨j, ι⟩ : TriadicCube d).center (11 * 3 ^ j)
      have hR : 2 * ((11 * 3 ^ j : ℕ) : ℝ) + 1 = 22 * (3 : ℝ) ^ j + 1 := by push_cast; ring
      rw [hR] at hcard
      exact mul_le_mul_of_nonneg_left hcard (by positivity)
    · rw [if_neg hbad]
      refine le_of_eq (Finset.sum_eq_zero fun x _ => ?_)
      simp only [F, near]
      rw [if_neg (fun h => hbad h.1)]
  calc ∑ x ∈ A, (3 : ℝ) ^ (τ * (partitionCube ω x).scale)
      ≤ ∑ x ∈ A, ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, F x j ι :=
        Finset.sum_le_sum hstep
    _ = ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, ∑ x ∈ A, F x j ι := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j,
          (if (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω then
            (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d else 0) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ι _ => hcharge j ι
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end Rigidity.Percolation

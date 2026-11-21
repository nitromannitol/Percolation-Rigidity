import Rigidity.Proofs.Partition.LambdaMinimalScale

/-!
# Minimal scales for general partitions: counting

The counting argument behind `exists_scale_sum_pow_partitionCube_le` uses only the stopping
structure of the partition and the independence of bad events of separated cubes. It applies to
the partition of `ℤᵈ` into maximal stopping cubes of any collection `G` of good cubes (Armstrong and
Dario, Proposition 2.1): a maximal stopping cube of positive scale has a cube outside `G` of scale
at least one less within eleven of its side lengths of each of its vertices, so the sum over the
triadic cube `Q_m` of the `τ`-th powers of the partition sizes is at most
`3^{d m} + ∑_{j < J} 3^{τ (j + 1)} (22 · 3^j + 1)^d N_j` when no bad cube of scale at least `J` is
near `Q_m`, with `N_j` the number of bad cubes of scale `j` near `Q_m`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **A bad cube near a maximal stopping cube.** A maximal stopping cube `Q` of positive scale
has, near each of its vertices `x`, a cube outside `G` of scale at least one less than `Q`, whose
centre is within eleven of its side lengths of `x`. -/
theorem TriadicCube.IsMaximalStopping.exists_bad_near {G : Set (TriadicCube d)}
    {Q : TriadicCube d} {x : Vertex d} (hQ : Q.IsMaximalStopping G) (hx : x ∈ Q.vertices)
    (hpos : 0 < Q.scale) :
    ∃ T : TriadicCube d, T ∉ G ∧ Q.scale ≤ T.scale + 1 ∧
      ∀ i, |x i - T.center i| ≤ 11 * T.side := by
  obtain ⟨-, hstop⟩ := hQ.1
  rcases hstop with h0 | ⟨digits, hbad⟩
  · omega
  simp only [TriadicCube.stableGood, Set.mem_setOf_eq, Set.not_subset] at hbad
  obtain ⟨T, hT, hTbad⟩ := hbad
  have hscale := TriadicCube.scale_le_of_mem_influence hT
  have hcs : (Q.child digits).scale = Q.scale - 1 := rfl
  refine ⟨T, hTbad, by omega, fun i => ?_⟩
  have h1 := TriadicCube.abs_center_sub_le_of_mem_influence hT i
  have hcQ : (Q.child digits).vertices ⊆ Q.vertices := Q.vertices_child_subset digits hpos
  have h2 := TriadicCube.abs_coord_sub_lt_side hx (hcQ (Q.child digits).center_mem) i
  have hside3 : 3 * (Q.child digits).side = Q.side := by
    rw [← TriadicCube.side_parent, TriadicCube.child_parent _ _ hpos]
  have hsideT : (Q.child digits).side ≤ T.side :=
    pow_le_pow_right₀ (by norm_num) hscale
  have h4 := abs_sub_le (x i) ((Q.child digits).center i) (T.center i)
  change |x i - (Q.child digits).center i| < Q.side at h2
  linarith

open scoped Classical in
/-- **Large stopping cubes are charged to bad cubes** (general partitions). If every vertex lies in
a unique maximal stopping cube of `G` and no cube outside `G` of scale at least `J` is near the
cube `Q_m`, then `∑_{x ∈ Q_m} size(x)^τ ≤ 3^{d m} + ∑_{j < J} 3^{τ (j + 1)} (22 · 3^j + 1)^d N_j`,
where `size` is the stopping size and `N_j` the number of cubes of scale `j` outside `G` with index
in `nearIndices d m j`. -/
theorem sum_stoppingSize_pow_le {G : Set (TriadicCube d)}
    (hPG : ∀ x : Vertex d, ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping G)
    (m J τ : ℕ)
    (hfar : ∀ T : TriadicCube d, J ≤ T.scale → T ∉ G →
      ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, ¬ ∀ i, |x i - T.center i| ≤ 11 * T.side) :
    ∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, TriadicCube.stoppingSize G x ^ τ ≤
      (3 : ℝ) ^ (d * m) + ∑ j ∈ Finset.range J, (3 : ℝ) ^ (τ * (j + 1)) *
        (22 * (3 : ℝ) ^ j + 1) ^ d *
        ((nearIndices d m j).filter fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ G).card := by
  set A := (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices with hAdef
  let near : Vertex d → ℕ → (Fin d → ℤ) → Prop := fun x j ι =>
    (⟨j, ι⟩ : TriadicCube d) ∉ G ∧
      ∀ i, |x i - (⟨j, ι⟩ : TriadicCube d).center i| ≤ 11 * (3 : ℤ) ^ j
  let F : Vertex d → ℕ → (Fin d → ℤ) → ℝ := fun x j ι =>
    if near x j ι then (3 : ℝ) ^ (τ * (j + 1)) else 0
  have hF0 : ∀ x j ι, 0 ≤ F x j ι := fun x j ι => by
    simp only [F]
    split_ifs <;> positivity
  -- each vertex is charged to a bad cube near it
  have hstep : ∀ x ∈ A, TriadicCube.stoppingSize G x ^ τ ≤
      1 + ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, F x j ι := by
    intro x hxA
    have hx : x ∈ (⟨m, 0⟩ : TriadicCube d).vertices :=
      ((⟨m, 0⟩ : TriadicCube d).mem_toIntegerCube_vertices x).1 hxA
    obtain ⟨Q, ⟨hxQ, hQ⟩, -⟩ := hPG x
    have hsize : TriadicCube.stoppingSize G x ^ τ = (3 : ℝ) ^ (τ * Q.scale) := by
      rw [TriadicCube.stoppingSize_eq_of_mem hxQ hQ, ← pow_mul, mul_comm]
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, F x j ι :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun ι _ => hF0 x j ι
    rw [hsize]
    rcases Nat.eq_zero_or_pos Q.scale with h0 | hpos
    · rw [h0, mul_zero, pow_zero]
      linarith
    refine le_trans ?_ (le_add_of_nonneg_left zero_le_one)
    obtain ⟨T, hTbad, hTscale, hTnear⟩ := hQ.exists_bad_near hxQ hpos
    have hTJ : T.scale < J := by
      by_contra h
      exact hfar T (not_lt.1 h) hTbad x hx hTnear
    have hTeq : (⟨T.scale, T.index⟩ : TriadicCube d) = T := rfl
    have hι := index_mem_nearIndices hx hTnear
    have hterm : F x T.scale T.index = (3 : ℝ) ^ (τ * (T.scale + 1)) := by
      simp only [F, near, hTeq]
      rw [if_pos ⟨hTbad, hTnear⟩]
    calc (3 : ℝ) ^ (τ * Q.scale) ≤ (3 : ℝ) ^ (τ * (T.scale + 1)) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hTscale)
      _ = F x T.scale T.index := hterm.symm
      _ ≤ ∑ ι ∈ nearIndices d m T.scale, F x T.scale ι :=
          Finset.single_le_sum (fun ι _ => hF0 x _ ι) hι
      _ ≤ ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, F x j ι :=
          Finset.single_le_sum (f := fun j => ∑ ι ∈ nearIndices d m j, F x j ι)
            (fun j _ => Finset.sum_nonneg fun ι _ => hF0 x j ι) (Finset.mem_range.2 hTJ)
  -- each bad cube is charged by few vertices
  have hcharge : ∀ j ι, ∑ x ∈ A, F x j ι ≤
      (if (⟨j, ι⟩ : TriadicCube d) ∉ G then
        (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d else 0) := by
    intro j ι
    by_cases hbad : (⟨j, ι⟩ : TriadicCube d) ∉ G
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
  have hcardA : ((A.card : ℕ) : ℝ) = (3 : ℝ) ^ (d * m) := by
    rw [hAdef, IntegerCube.card_vertices]
    change (((3 ^ m) ^ d : ℕ) : ℝ) = _
    push_cast
    rw [← pow_mul, mul_comm]
  calc ∑ x ∈ A, TriadicCube.stoppingSize G x ^ τ
      ≤ ∑ x ∈ A, (1 + ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, F x j ι) :=
        Finset.sum_le_sum hstep
    _ = (3 : ℝ) ^ (d * m) + ∑ x ∈ A, ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, F x j ι := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcardA]
    _ = (3 : ℝ) ^ (d * m) + ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j, ∑ x ∈ A, F x j ι := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ ≤ (3 : ℝ) ^ (d * m) + ∑ j ∈ Finset.range J, ∑ ι ∈ nearIndices d m j,
          (if (⟨j, ι⟩ : TriadicCube d) ∉ G then
            (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d else 0) := by
        gcongr with j _ ι _
        exact hcharge j ι
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]


open scoped Classical in
/-- The number of cubes of scale `j` near the cube of scale `m` centred at the origin, with
index of residues `r`, satisfying a predicate. -/
noncomputable def classCount (bad : TriadicCube d → Prop) (m j : ℕ) (r : Fin d → Fin 3) : ℕ :=
  (((nearIndices d m j).subtype fun ι => residue ι = r).filter
    fun ι => bad (⟨j, ι.1⟩ : TriadicCube d)).card

open scoped Classical in
/-- The cubes near the cube of scale `m` satisfying a predicate split into residue classes. -/
theorem card_filter_eq_sum_classCount (bad : TriadicCube d → Prop) (m j : ℕ) :
    ((nearIndices d m j).filter fun ι => bad (⟨j, ι⟩ : TriadicCube d)).card =
      ∑ r : Fin d → Fin 3, classCount bad m j r := by
  rw [Finset.card_eq_sum_card_fiberwise (f := residue) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold classCount
  rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
  congr 1
  ext ι
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_subtype, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨hι, hbad⟩, hr⟩
    exact ⟨⟨ι, hr⟩, ⟨hι, hbad⟩, rfl⟩
  · rintro ⟨⟨ι', hr⟩, ⟨hι, hbad⟩, rfl⟩
    exact ⟨⟨hι, hbad⟩, hr⟩

open scoped Classical in
/-- **The weighted count of bad cubes** (general predicate). If for `j0 ≤ j < J ≤ m` every residue
class has fewer than `3^{e_j}` cubes of scale `j` near `Q_m` satisfying `bad`,
`e_j = d (m - j) - (τ + 1)(j + 1)`, then
`∑_{j < J} 3^{τ (j + 1)} (22 · 3^j + 1)^d N_j ≤ (j0 · 575ᵈ · 3^{τ j0} + 69ᵈ) 3^{d m}`. -/
theorem sum_weights_le_of_counts (bad : TriadicCube d → Prop) (m J j0 τ : ℕ) (hJm : J ≤ m)
    (hexp : ∀ j < J, (τ + 1) * (j + 1) + d * j ≤ d * m)
    (hmid : ∀ j, j0 ≤ j → j < J → ∀ r,
      classCount bad m j r < 3 ^ (d * (m - j) - (τ + 1) * (j + 1))) :
    ∑ j ∈ Finset.range J, (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d *
        ((nearIndices d m j).filter fun ι => bad (⟨j, ι⟩ : TriadicCube d)).card ≤
      ((j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d) * 3 ^ (d * m) := by
  set g : ℕ → ℝ := fun j => if j < j0 then 575 ^ d * 3 ^ (τ * j0) * 3 ^ (d * m)
    else 69 ^ d * 3 ^ (d * m) * (1 / 3) ^ (j + 1) with hgdef
  have hterm : ∀ j ∈ Finset.range J, (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d *
      (((nearIndices d m j).filter
        fun ι => bad (⟨j, ι⟩ : TriadicCube d)).card : ℝ) ≤ g j := by
    intro j hj
    have hjJ := Finset.mem_range.1 hj
    have hjm : j ≤ m := by omega
    have h3j : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
    have hA : 22 * (3 : ℝ) ^ j + 1 ≤ 23 * 3 ^ j := by linarith
    have hpowm : (3 : ℝ) ^ j * 3 ^ (m - j) = 3 ^ m := by
      rw [← pow_add, Nat.add_sub_cancel' hjm]
    by_cases hj0 : j < j0
    · rw [hgdef]
      simp only [if_pos hj0]
      have hN : (((nearIndices d m j).filter
          fun ι => bad (⟨j, ι⟩ : TriadicCube d)).card : ℝ) ≤
          (25 * (3 : ℝ) ^ (m - j)) ^ d := by
        have h1 : (((nearIndices d m j).filter
            fun ι => bad (⟨j, ι⟩ : TriadicCube d)).card : ℝ) ≤
            (nearIndices d m j).card := by exact_mod_cast Finset.card_filter_le _ _
        rw [card_nearIndices] at h1
        refine h1.trans ?_
        have h3 : (1 : ℝ) ≤ 3 ^ (m - j) := one_le_pow₀ (by norm_num)
        gcongr
        linarith
      have hτ : (3 : ℝ) ^ (τ * (j + 1)) ≤ 3 ^ (τ * j0) :=
        pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hj0)
      calc (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d *
            (((nearIndices d m j).filter
              fun ι => bad (⟨j, ι⟩ : TriadicCube d)).card : ℝ)
          ≤ 3 ^ (τ * j0) * (23 * 3 ^ j) ^ d * (25 * (3 : ℝ) ^ (m - j)) ^ d := by
            gcongr
        _ = 575 ^ d * 3 ^ (τ * j0) * 3 ^ (d * m) := by
            have h : (3 : ℝ) ^ (d * m) = ((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ (m - j)) ^ d := by
              rw [pow_mul', ← hpowm, mul_pow]
            rw [h, show (575 : ℝ) = 23 * 25 by norm_num, mul_pow, mul_pow, mul_pow]
            ring
    · rw [hgdef]
      simp only [if_neg hj0]
      have hj0' : j0 ≤ j := not_lt.1 hj0
      set e := d * (m - j) - (τ + 1) * (j + 1) with hedef
      have hN : (((nearIndices d m j).filter
          fun ι => bad (⟨j, ι⟩ : TriadicCube d)).card : ℝ) ≤
          3 ^ d * 3 ^ e := by
        rw [card_filter_eq_sum_classCount bad]
        push_cast
        calc ∑ r : Fin d → Fin 3, (classCount bad m j r : ℝ)
            ≤ ∑ _r : Fin d → Fin 3, (3 : ℝ) ^ e :=
              Finset.sum_le_sum fun r _ => by
                have := hmid j hj0' hjJ r
                exact_mod_cast this.le
          _ = 3 ^ d * 3 ^ e := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
      have hexpj := hexp j hjJ
      have hsum : τ * (j + 1) + d * j + e + (j + 1) = d * m := by
        have h1 : d * (m - j) + d * j = d * m := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hjm]
        have h2 : τ * (j + 1) + (j + 1) = (τ + 1) * (j + 1) := by ring
        have hYX : (τ + 1) * (j + 1) ≤ d * (m - j) := by linarith
        have he : e + (τ + 1) * (j + 1) = d * (m - j) := Nat.sub_add_cancel hYX
        linarith
      have hpow : (3 : ℝ) ^ (τ * (j + 1)) * (3 ^ j) ^ d * 3 ^ e =
          3 ^ (d * m) * (1 / 3) ^ (j + 1) := by
        rw [← pow_mul, ← pow_add, ← pow_add, one_div, inv_pow, ← hsum]
        rw [pow_add (3 : ℝ) (τ * (j + 1) + d * j + e), mul_assoc, mul_inv_cancel₀ (by positivity),
          mul_one]
        ring_nf
      calc (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d *
            (((nearIndices d m j).filter
              fun ι => bad (⟨j, ι⟩ : TriadicCube d)).card : ℝ)
          ≤ 3 ^ (τ * (j + 1)) * (23 * 3 ^ j) ^ d * (3 ^ d * 3 ^ e) := by gcongr
        _ = 69 ^ d * ((3 : ℝ) ^ (τ * (j + 1)) * (3 ^ j) ^ d * 3 ^ e) := by
            rw [mul_pow, show (69 : ℝ) = 23 * 3 by norm_num, mul_pow]
            ring
        _ = 69 ^ d * 3 ^ (d * m) * (1 / 3) ^ (j + 1) := by rw [hpow]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  set A : ℝ := 575 ^ d * 3 ^ (τ * j0) * 3 ^ (d * m) with hAdef
  set B : ℕ → ℝ := fun j => 69 ^ d * 3 ^ (d * m) * (1 / 3) ^ (j + 1) with hBdef
  have hA0 : 0 ≤ A := by positivity
  have hB0 : ∀ j, 0 ≤ B j := fun j => by positivity
  have hg : ∀ j, g j ≤ (if j < j0 then A else 0) + B j := by
    intro j
    rw [hgdef]
    by_cases h : j < j0
    · simp only [if_pos h]
      linarith [hB0 j]
    · simp only [if_neg h, zero_add, hBdef, le_refl]
  have hite : ∑ j ∈ Finset.range J, (if j < j0 then A else 0) ≤ j0 * A := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range J).filter (fun j => j < j0)).card ≤ j0 := by
      calc ((Finset.range J).filter (fun j => j < j0)).card ≤ (Finset.range j0).card :=
            Finset.card_le_card fun j hj => Finset.mem_range.2 (Finset.mem_filter.1 hj).2
        _ = j0 := Finset.card_range j0
    have hcard' : (((Finset.range J).filter (fun j => j < j0)).card : ℝ) ≤ j0 := by
      exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right hcard' hA0
  have hgeom : ∑ j ∈ Finset.range J, (1 / 3 : ℝ) ^ (j + 1) ≤ 1 := by
    have h := geom_sum_eq (show (1 / 3 : ℝ) ≠ 1 by norm_num) J
    have h' : ∑ j ∈ Finset.range J, (1 / 3 : ℝ) ^ (j + 1) =
        (1 / 3) * ∑ j ∈ Finset.range J, (1 / 3 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h', h]
    have hpos : (0 : ℝ) ≤ (1 / 3) ^ J := by positivity
    have hle : ((1 : ℝ) / 3) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have : ((1 : ℝ) / 3) * (((1 / 3) ^ J - 1) / (1 / 3 - 1)) = (1 - (1 / 3) ^ J) / 2 := by
      field_simp
      ring
    rw [this]
    linarith
  have hBsum : ∑ j ∈ Finset.range J, B j ≤ 69 ^ d * 3 ^ (d * m) := by
    rw [hBdef]
    simp only
    rw [← Finset.mul_sum]
    have h69 : (0 : ℝ) ≤ 69 ^ d * 3 ^ (d * m) := by positivity
    calc 69 ^ d * 3 ^ (d * m) * ∑ j ∈ Finset.range J, (1 / 3 : ℝ) ^ (j + 1)
        ≤ 69 ^ d * 3 ^ (d * m) * 1 := mul_le_mul_of_nonneg_left hgeom h69
      _ = 69 ^ d * 3 ^ (d * m) := mul_one _
  calc ∑ j ∈ Finset.range J, g j
      ≤ ∑ j ∈ Finset.range J, ((if j < j0 then A else 0) + B j) := Finset.sum_le_sum fun j _ => hg j
    _ = ∑ j ∈ Finset.range J, (if j < j0 then A else 0) + ∑ j ∈ Finset.range J, B j :=
        Finset.sum_add_distrib
    _ ≤ j0 * A + 69 ^ d * 3 ^ (d * m) := add_le_add hite hBsum
    _ = ((j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d) * 3 ^ (d * m) := by
        rw [hAdef]
        ring

end Rigidity.Percolation

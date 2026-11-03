import LatticeProb.Prob.Percolation.LatticeClusterBall

/-!
# The decay profile `(1 + |x|)^{-3/4}` on a cluster of `ℤ²`

The profile `x ↦ (1 + |x|)^{-3/4}` on an open component of `ℤ²` has finite superlevel sets
(`profile_finite`), and every finite subset of the component is contained in a finite set `B`
(a cube exhaustion) whose boundary energy `∑_{x ∈ B} ∑_{y ∼ x, y ∉ B} (u x + u y)^2` is
as small as we wish (`profile_boundary`): the cube of radius `n` has `O(n)` boundary vertices of
bounded degree, each carrying a term of size `O(n^{-3/2})`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LatticeProb.Percolation

namespace Rigidity.Proofs.S3.NetworkTrace

/-- The Euclidean distance of a lattice point to the origin is its Euclidean norm. -/
theorem dist_embedding_zero (x : Vertex 2) :
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding (0 : Vertex 2)) =
      ‖latticeEuclideanEmbedding x‖ := by
  have hz : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext i
    change ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero
  rw [dist_eq_norm, hz, sub_zero]

/-- The Euclidean norm dominates each coordinate. -/
theorem abs_coord_le_norm (x : Vertex 2) (i : Fin 2) :
    |(x i : ℝ)| ≤ ‖latticeEuclideanEmbedding x‖ :=
  PiLp.norm_apply_le (latticeEuclideanEmbedding x) i

theorem profile_finite {ω : Configuration 2} (C : OpenComponent ω) (ε : ℝ) (hε : 0 < ε) :
    {x : C | ε ≤ (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ))}.Finite := by
  refine (finite_componentEuclideanBall C 0 (ε ^ (-(4 / 3 : ℝ)))).subset ?_
  intro x hx
  have hx' : ε ≤ (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) := hx
  have hρ : 0 ≤ ‖latticeEuclideanEmbedding x.val‖ := norm_nonneg _
  have hε' : (ε ^ (-(4 / 3 : ℝ))) ^ (-(3 / 4 : ℝ)) = ε := by
    rw [← Real.rpow_mul hε.le]
    norm_num
  have hpos : 0 < ε ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos hε _
  have hle : (ε ^ (-(4 / 3 : ℝ))) ^ (-(3 / 4 : ℝ)) ≤
      (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) := hε'.symm ▸ hx'
  rw [Real.rpow_le_rpow_iff_of_neg hpos (by linarith) (by norm_num)] at hle
  show dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding (0 : Vertex 2)) <
    ε ^ (-(4 / 3 : ℝ))
  rw [dist_embedding_zero]
  linarith

/-- The boundary shell of the integer cube of radius `n` in `ℤ²`. -/
noncomputable def cubeShell (n : ℕ) : Finset (Vertex 2) :=
  (Finset.Icc (-(n : ℤ)) n).image (fun j => ![(n : ℤ), j]) ∪
    (Finset.Icc (-(n : ℤ)) n).image (fun j => ![-(n : ℤ), j]) ∪
    (Finset.Icc (-(n : ℤ)) n).image (fun j => ![j, (n : ℤ)]) ∪
    (Finset.Icc (-(n : ℤ)) n).image (fun j => ![j, -(n : ℤ)])

theorem card_cubeShell_le (n : ℕ) : (cubeShell n).card ≤ 4 * (2 * n + 1) := by
  have h1 : ((Finset.Icc (-(n : ℤ)) n).image (fun j => ![(n : ℤ), j])).card ≤ 2 * n + 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Int.card_Icc]
    omega
  have h2 : ((Finset.Icc (-(n : ℤ)) n).image (fun j => ![-(n : ℤ), j])).card ≤ 2 * n + 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Int.card_Icc]
    omega
  have h3 : ((Finset.Icc (-(n : ℤ)) n).image (fun j => ![j, (n : ℤ)])).card ≤ 2 * n + 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Int.card_Icc]
    omega
  have h4 : ((Finset.Icc (-(n : ℤ)) n).image (fun j => ![j, -(n : ℤ)])).card ≤ 2 * n + 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Int.card_Icc]
    omega
  unfold cubeShell
  have := Finset.card_union_le
    (((Finset.Icc (-(n : ℤ)) n).image (fun j => ![(n : ℤ), j]) ∪
      (Finset.Icc (-(n : ℤ)) n).image (fun j => ![-(n : ℤ), j])) ∪
      (Finset.Icc (-(n : ℤ)) n).image (fun j => ![j, (n : ℤ)]))
    ((Finset.Icc (-(n : ℤ)) n).image (fun j => ![j, -(n : ℤ)]))
  have h12 := Finset.card_union_le ((Finset.Icc (-(n : ℤ)) n).image (fun j => ![(n : ℤ), j]))
    ((Finset.Icc (-(n : ℤ)) n).image (fun j => ![-(n : ℤ), j]))
  have h123 := Finset.card_union_le
    (((Finset.Icc (-(n : ℤ)) n).image (fun j => ![(n : ℤ), j]) ∪
      (Finset.Icc (-(n : ℤ)) n).image (fun j => ![-(n : ℤ), j])))
    ((Finset.Icc (-(n : ℤ)) n).image (fun j => ![j, (n : ℤ)]))
  omega

theorem mem_cubeShell {n : ℕ} {x : Vertex 2} (hx : ∀ i, |x i| ≤ n) (i : Fin 2)
    (hi : |x i| = n) : x ∈ cubeShell n := by
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hi' : |x 0| = n ∨ |x 1| = n :=
    (Fin.exists_fin_two (p := fun j => |x j| = (n : ℤ))).mp ⟨i, hi⟩
  unfold cubeShell
  rcases hi' with hi' | hi'
  · rcases (abs_eq hn).mp hi' with h | h
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
      exact Finset.mem_image.mpr ⟨x 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        funext (Fin.forall_fin_two.mpr ⟨h.symm, rfl⟩)⟩
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
      exact Finset.mem_image.mpr ⟨x 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        funext (Fin.forall_fin_two.mpr ⟨by simp [h], rfl⟩)⟩
  · rcases (abs_eq hn).mp hi' with h | h
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      exact Finset.mem_image.mpr ⟨x 0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        funext (Fin.forall_fin_two.mpr ⟨rfl, h.symm⟩)⟩
    · refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨x 0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        funext (Fin.forall_fin_two.mpr ⟨rfl, by simp [h]⟩)⟩

/-- Component-graph neighbours are at lattice `ℓ¹` distance one. -/
theorem abs_coord_sub_le_one {ω : Configuration 2} {C : OpenComponent ω} {x y : C}
    (h : (componentGraph C).Adj x y) (i : Fin 2) : |x.val i - y.val i| ≤ 1 := by
  have h1 : latticeL1Dist x.val y.val = 1 := lattice_adj_iff_l1Dist.mp (openGraph_le ω h)
  unfold latticeL1Dist at h1
  rw [Fin.sum_univ_two] at h1
  have h0 := abs_nonneg (x.val 0 - y.val 0)
  have h1' := abs_nonneg (x.val 1 - y.val 1)
  fin_cases i
  · change |x.val 0 - y.val 0| ≤ 1
    omega
  · change |x.val 1 - y.val 1| ≤ 1
    omega

/-- The vertices of the component in the integer cube of radius `n`, as a finite set. -/
theorem finite_cubeIn {ω : Configuration 2} (C : OpenComponent ω) (n : ℕ) :
    {x : C | ∀ i, |x.val i| ≤ (n : ℤ)}.Finite := by
  have hbox := Set.Finite.pi' (fun _ : Fin 2 => Set.finite_Icc (-(n : ℤ)) n)
  refine (hbox.preimage Subtype.val_injective.injOn).subset ?_
  intro x hx i
  exact abs_le.mp (hx i)

/-- The vertices of the component in the integer cube of radius `n`. -/
noncomputable def cubeIn {ω : Configuration 2} (C : OpenComponent ω) (n : ℕ) : Finset C :=
  (finite_cubeIn C n).toFinset

theorem mem_cubeIn {ω : Configuration 2} (C : OpenComponent ω) (n : ℕ) (x : C) :
    x ∈ cubeIn C n ↔ ∀ i, |x.val i| ≤ (n : ℤ) :=
  Set.Finite.mem_toFinset _

/-- A boundary edge of the cube: the inner endpoint lies on the shell and both endpoints have
profile at most `(1 + n)^{-3/4}`. -/
theorem boundary_edge {ω : Configuration 2} (C : OpenComponent ω) (n : ℕ) {x y : C}
    (hx : x ∈ cubeIn C n) (hxy : (componentGraph C).Adj x y) (hy : y ∉ cubeIn C n) :
    x.val ∈ cubeShell n ∧
      ((1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) +
        (1 + ‖latticeEuclideanEmbedding y.val‖) ^ (-(3 / 4 : ℝ))) ^ 2 ≤
      4 * ((1 + (n : ℝ)) ^ (-(3 / 4 : ℝ))) ^ 2 := by
  rw [mem_cubeIn] at hx hy
  push Not at hy
  obtain ⟨j, hj⟩ := hy
  have hxj := hx j
  have hadj := abs_coord_sub_le_one hxy j
  have hxn : |x.val j| = n := by
    have h1 := abs_le.mp hadj
    have h2 := abs_le.mp hxj
    have h3 : (n : ℤ) < |y.val j| := hj
    rcases abs_cases (y.val j) with ⟨h4, _⟩ | ⟨h4, _⟩ <;> rw [h4] at h3 <;>
      rcases abs_cases (x.val j) with ⟨h5, _⟩ | ⟨h5, _⟩ <;> rw [h5] <;> omega
  refine ⟨mem_cubeShell hx j hxn, ?_⟩
  have hxr : (n : ℝ) ≤ ‖latticeEuclideanEmbedding x.val‖ := by
    have := abs_coord_le_norm x.val j
    rw [← Int.cast_abs, hxn] at this
    simpa using this
  have hyr : (n : ℝ) ≤ ‖latticeEuclideanEmbedding y.val‖ := by
    have := abs_coord_le_norm y.val j
    rw [← Int.cast_abs] at this
    have h3 : (n : ℝ) ≤ ((|y.val j| : ℤ) : ℝ) := by exact_mod_cast hj.le
    linarith
  have hn : (0 : ℝ) < 1 + (n : ℝ) := by positivity
  have hax : (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) ≤
      (1 + (n : ℝ)) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hn (by linarith) (by norm_num)
  have hay : (1 + ‖latticeEuclideanEmbedding y.val‖) ^ (-(3 / 4 : ℝ)) ≤
      (1 + (n : ℝ)) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hn (by linarith) (by norm_num)
  have hsum : (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) +
      (1 + ‖latticeEuclideanEmbedding y.val‖) ^ (-(3 / 4 : ℝ)) ≤
      2 * (1 + (n : ℝ)) ^ (-(3 / 4 : ℝ)) := by linarith
  have hnn : 0 ≤ (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) +
      (1 + ‖latticeEuclideanEmbedding y.val‖) ^ (-(3 / 4 : ℝ)) := by positivity
  calc _ ≤ (2 * (1 + (n : ℝ)) ^ (-(3 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ hnn hsum 2
    _ = _ := by ring

/-- The boundary energy of the cube of radius `n` is at most `64 (2 n + 1) (1 + n)^{-3/2}`. -/
theorem boundary_sum_le {ω : Configuration 2} (C : OpenComponent ω) (n : ℕ) :
    ∑ x ∈ cubeIn C n,
      ∑ y ∈ ((componentGraph C).neighborFinset x).filter (· ∉ cubeIn C n),
      ((1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) +
        (1 + ‖latticeEuclideanEmbedding y.val‖) ^ (-(3 / 4 : ℝ))) ^ 2 ≤
    (4 * (2 * n + 1) : ℕ) * (4 * (4 * ((1 + (n : ℝ)) ^ (-(3 / 4 : ℝ))) ^ 2)) := by
  set t : ℝ := (1 + (n : ℝ)) ^ (-(3 / 4 : ℝ)) with ht
  have ht0 : 0 ≤ t := by positivity
  calc _ ≤ ∑ x ∈ cubeIn C n, if x.val ∈ cubeShell n then 4 * (4 * t ^ 2) else 0 := by
        refine Finset.sum_le_sum fun x hx => ?_
        by_cases hs : x.val ∈ cubeShell n
        · rw [if_pos hs]
          calc _ ≤ (((componentGraph C).neighborFinset x).filter (· ∉ cubeIn C n)).card •
                (4 * t ^ 2) := by
                refine Finset.sum_le_card_nsmul _ _ _ fun y hy => ?_
                obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
                exact (boundary_edge C n hx
                  ((SimpleGraph.mem_neighborFinset _ _ _).mp hy1) hy2).2
            _ ≤ 4 • (4 * t ^ 2) := by
                refine nsmul_le_nsmul_left (by positivity) ?_
                calc _ ≤ ((componentGraph C).neighborFinset x).card := Finset.card_filter_le _ _
                  _ = (componentGraph C).degree x := SimpleGraph.card_neighborFinset_eq_degree _ _
                  _ ≤ 2 * 2 := componentGraph_degree_le C x
            _ = _ := by rw [nsmul_eq_mul]; norm_num
        · rw [if_neg hs]
          refine le_of_eq (Finset.sum_eq_zero fun y hy => ?_)
          obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
          exact absurd (boundary_edge C n hx
            ((SimpleGraph.mem_neighborFinset _ _ _).mp hy1) hy2).1 hs
    _ = ((cubeIn C n).filter (fun x => x.val ∈ cubeShell n)).card • (4 * (4 * t ^ 2)) := by
        rw [← Finset.sum_filter, Finset.sum_const]
    _ ≤ (cubeShell n).card • (4 * (4 * t ^ 2)) := by
        refine nsmul_le_nsmul_left (by positivity) ?_
        refine Finset.card_le_card_of_injOn Subtype.val (fun x hx => (Finset.mem_filter.mp hx).2)
          Subtype.val_injective.injOn
    _ ≤ (4 * (2 * n + 1)) • (4 * (4 * t ^ 2)) :=
        nsmul_le_nsmul_left (by positivity) (card_cubeShell_le n)
    _ = _ := by rw [nsmul_eq_mul]

/-- The cube boundary bound tends to zero. -/
theorem exists_cube_bound_le (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((4 * (2 * n + 1) : ℕ) : ℝ) *
        (4 * (4 * ((1 + (n : ℝ)) ^ (-(3 / 4 : ℝ))) ^ 2)) ≤ ε := by
  have hlim := tendsto_rpow_neg_atTop (y := (1 / 2 : ℝ)) (by norm_num)
  obtain ⟨X, hX⟩ :=
    Filter.eventually_atTop.mp ((tendsto_order.1 hlim).2 (ε / 128) (by positivity))
  refine ⟨⌈X⌉₊, fun n hn => ?_⟩
  have hu : (0 : ℝ) < 1 + (n : ℝ) := by positivity
  have hXn : X ≤ 1 + (n : ℝ) := by
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hdec := hX _ hXn
  have hsq : ((1 + (n : ℝ)) ^ (-(3 / 4 : ℝ))) ^ 2 = (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    norm_num
  have hmul : (1 + (n : ℝ)) * (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ)) =
      (1 + (n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    rw [mul_comm, ← Real.rpow_add_one hu.ne']
    norm_num
  have hpos : 0 ≤ (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ)) := by positivity
  rw [hsq]
  push_cast
  nlinarith [hmul, hdec, hpos, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem profile_boundary {ω : Configuration 2} (C : OpenComponent ω) (ε : ℝ) (hε : 0 < ε)
    (S : Finset C) : ∃ B : Finset C, S ⊆ B ∧
      ∑ x ∈ B, ∑ y ∈ ((componentGraph C).neighborFinset x).filter (· ∉ B),
        ((1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) +
          (1 + ‖latticeEuclideanEmbedding y.val‖) ^ (-(3 / 4 : ℝ))) ^ 2 ≤ ε := by
  obtain ⟨N, hN⟩ := exists_cube_bound_le ε hε
  set M : ℕ := S.sup fun x => (|x.val 0| + |x.val 1|).toNat with hM
  refine ⟨cubeIn C (max N M), ?_, (boundary_sum_le C (max N M)).trans (hN _ (le_max_left _ _))⟩
  intro x hx
  rw [mem_cubeIn]
  have hxM : (|x.val 0| + |x.val 1|).toNat ≤ M :=
    Finset.le_sup (f := fun x : C => (|x.val 0| + |x.val 1|).toNat) hx
  have hM' : M ≤ max N M := le_max_right _ _
  have h0 := abs_nonneg (x.val 0)
  have h1 := abs_nonneg (x.val 1)
  intro i
  fin_cases i
  · change |x.val 0| ≤ ((max N M : ℕ) : ℤ)
    omega
  · change |x.val 1| ≤ ((max N M : ℕ) : ℤ)
    omega

end Rigidity.Proofs.S3.NetworkTrace

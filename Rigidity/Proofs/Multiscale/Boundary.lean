import Rigidity.Proofs.Multiscale.Extension

/-!
# Block means of closed cubes against spatial averages over half-open cubes

For the closed lattice cube `c + {0, …, L}^d` and the half-open cube `c + {0, …, L - 1}^d`, the
face-weighted block mean of a gradient and the normalized spatial sum `L^{-d} ⟨∇v⟩` over the
half-open cube differ only through the edges near the boundary: the edges `(x, j)` with
`c_i < x_i` and `x_i + 1 < c_i + L` for every `i` lie in the half-open cube, have face weight one
and enter both sums. There are at most `3 d (L + 1)^{d-1}` other edges in each direction, so by
Cauchy–Schwarz the squared difference is at most `C(d) L^{-1}` times the face-weighted mean energy
of `v` on the closed cube.
-/

namespace Rigidity.Proofs.Multiscale

open LatticeProb LatticeProb.Percolation LatticeHC

variable {d : ℕ}

/-- **Comparison of a weighted sum with a partial sum.** If `i ⊆ s ⊆ t`, the weights lie in
`[0, 1]` on `t` and equal one on `i`, then `|Σ_t w f - Σ_s f| ≤ 2 Σ_{t \ i} |f|`. -/
theorem abs_sum_weighted_sub_sum_le {ι : Type*} [DecidableEq ι] {s t i : Finset ι}
    (hst : s ⊆ t) (his : i ⊆ s) (w f : ι → ℝ) (hw1 : ∀ e ∈ i, w e = 1)
    (hw : ∀ e ∈ t, 0 ≤ w e ∧ w e ≤ 1) :
    |∑ e ∈ t, w e * f e - ∑ e ∈ s, f e| ≤ 2 * ∑ e ∈ t \ i, |f e| := by
  have hit : i ⊆ t := his.trans hst
  rw [← Finset.sum_sdiff hit, ← Finset.sum_sdiff his]
  have hi : ∑ e ∈ i, w e * f e = ∑ e ∈ i, f e :=
    Finset.sum_congr rfl fun e he => by rw [hw1 e he, one_mul]
  rw [hi]
  have h1 : |∑ e ∈ t \ i, w e * f e| ≤ ∑ e ∈ t \ i, |f e| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
    have hwe := hw e (Finset.mem_sdiff.1 he).1
    rw [abs_mul, abs_of_nonneg hwe.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hwe.2
  have h2 : |∑ e ∈ s \ i, f e| ≤ ∑ e ∈ t \ i, |f e| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.sdiff_subset_sdiff hst le_rfl) fun _ _ _ => abs_nonneg _)
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

/-- A slab of the closed cube `c + {0, …, L}^d`, where the `i`-th coordinate takes values in `V`,
has at most `|V| (L + 1)^{d-1}` points. -/
theorem card_filter_latticeCube_coord_mem_le (c : Site d) (L : ℕ) (i : Fin d) (V : Finset ℤ) :
    ((latticeCube c L).filter fun x => x i ∈ V).card ≤ V.card * (L + 1) ^ (d - 1) := by
  classical
  set F : Fin d → Finset ℤ := fun i' => Finset.Icc (c i') (c i' + L)
  have hsub : (latticeCube c L).filter (fun x => x i ∈ V) ⊆
      Fintype.piFinset (Function.update F i V) := by
    intro x hx
    rw [Finset.mem_filter, mem_latticeCube_iff_coord] at hx
    rw [Fintype.mem_piFinset]
    intro i'
    by_cases h : i' = i
    · subst h
      simpa using hx.2
    · rw [Function.update_of_ne h]
      exact Finset.mem_Icc.2 (hx.1 i')
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i),
    Function.update_self]
  have hF : ∀ i' ∈ (Finset.univ : Finset (Fin d)) \ {i},
      (Function.update F i V i').card = L + 1 := by
    intro i' hi'
    have h : i' ≠ i := by simpa using hi'
    rw [Function.update_of_ne h, Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl hF, Finset.prod_const]
  have hcard : ((Finset.univ : Finset (Fin d)) \ {i}).card = d - 1 := by
    rw [Finset.card_sdiff_of_subset (by simp), Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton]
  rw [hcard]

/-- The edges of the closed cube `c + {0, …, L}^d` in direction `j` near its boundary: those
`(x, j)` for which some coordinate fails `c_i < x_i ∧ x_i + 1 < c_i + L`. -/
noncomputable def boundaryEdges (c : Site d) (L : ℕ) (j : Fin d) : Finset (Edge d) :=
  ((edgesOf c L).filter fun e => e.2 = j).filter fun e =>
    ¬ ∀ i, c i < e.1 i ∧ e.1 i + 1 < c i + L

/-- There are at most `3 d (L + 1)^{d-1}` boundary edges in each direction. -/
theorem card_boundaryEdges_le (c : Site d) (L : ℕ) (j : Fin d) :
    (boundaryEdges c L j).card ≤ 3 * d * (L + 1) ^ (d - 1) := by
  classical
  set U : Finset (Site d) := Finset.univ.biUnion fun i =>
    (latticeCube c L).filter fun x => x i ∈ ({c i, c i + L - 1, c i + L} : Finset ℤ)
  have hmaps : Set.MapsTo (fun e : Edge d => e.1) (boundaryEdges c L j) U := by
    intro e he
    have he' : e ∈ boundaryEdges c L j := he
    simp only [boundaryEdges, Finset.mem_filter] at he'
    obtain ⟨⟨he, -⟩, hnot⟩ := he'
    have hsrc := (mem_edgesOf_iff_endpoints_mem.1 he).1
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    have hc := (mem_latticeCube_iff_coord _ _ _).1 hsrc i
    simp only [Edge.src] at hc hsrc
    show e.1 ∈ U
    simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton]
    refine ⟨i, hsrc, ?_⟩
    by_cases h1 : c i < e.1 i
    · have h2 := hi h1
      omega
    · omega
  have hinj : Set.InjOn (fun e : Edge d => e.1) (boundaryEdges c L j) := by
    intro e he e' he' h
    have h1 : e ∈ boundaryEdges c L j := he
    have h2 : e' ∈ boundaryEdges c L j := he'
    simp only [boundaryEdges, Finset.mem_filter] at h1 h2
    exact Prod.ext h (h1.1.2.trans h2.1.2.symm)
  refine (Finset.card_le_card_of_injOn _ hmaps hinj).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ i : Fin d, ((latticeCube c L).filter fun x =>
        x i ∈ ({c i, c i + L - 1, c i + L} : Finset ℤ)).card
      ≤ ∑ _i : Fin d, 3 * (L + 1) ^ (d - 1) := by
        refine Finset.sum_le_sum fun i _ => (card_filter_latticeCube_coord_mem_le c L i _).trans ?_
        refine Nat.mul_le_mul_right _ ?_
        refine (Finset.card_insert_le _ _).trans ?_
        exact Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))
    _ = 3 * d * (L + 1) ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring

/-- The half-open cube `c + {0, …, L - 1}^d`. -/
noncomputable def halfOpenCube (c : Site d) (L : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => Finset.Ico (c i) (c i + L)

/-- The spatial sum over the half-open cube, as a sum over its edges in direction `j`. -/
theorem gradSum_halfOpenCube_eq (c : Site d) (L : ℕ) (v : Site d → ℝ) (j : Fin d) :
    gradSum (halfOpenCube c L) v j =
      ∑ e ∈ ((halfOpenCube c L).filter fun x => x + unitVec j ∈ halfOpenCube c L).map
          (⟨fun x => (x, j), fun _ _ h => (Prod.mk.inj h).1⟩ : Site d ↪ Edge d),
        (v (Edge.tgt e) - v (Edge.src e)) := by
  rw [Finset.sum_map, gradSum, Finset.sum_filter]
  rfl

/-- **The block mean against the spatial average, direction by direction**:
`|(∇v)_□ · e_j - L^{-d} ⟨∇v⟩_{c + {0, …, L-1}^d} · e_j| ≤ 2 L^{-d} Σ_{boundary edges} |∇v|`. -/
theorem abs_blockMean_sub_gradSum_le (c : Site d) (L : ℕ) (v : Site d → ℝ) (j : Fin d) :
    |blockMean c L (fun e => v e.tgt - v e.src) j -
        ((L : ℝ) ^ d)⁻¹ * gradSum (halfOpenCube c L) v j| ≤
      ((L : ℝ) ^ d)⁻¹ * (2 * ∑ e ∈ boundaryEdges c L j, |v e.tgt - v e.src|) := by
  classical
  set t := (edgesOf c L).filter fun e => e.2 = j
  set i := t.filter fun e => ∀ i, c i < e.1 i ∧ e.1 i + 1 < c i + L
  set s := ((halfOpenCube c L).filter fun x => x + unitVec j ∈ halfOpenCube c L).map
    (⟨fun x => (x, j), fun _ _ h => (Prod.mk.inj h).1⟩ : Site d ↪ Edge d)
  have hK : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  have hsub : halfOpenCube c L ⊆ latticeCube c L := by
    intro x hx
    rw [halfOpenCube, Fintype.mem_piFinset] at hx
    rw [mem_latticeCube_iff_coord]
    intro i'
    have := Finset.mem_Ico.1 (hx i')
    constructor <;> omega
  have hst : s ⊆ t := by
    intro e he
    simp only [s, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk] at he
    obtain ⟨x, ⟨hx, hxj⟩, rfl⟩ := he
    simp only [t, Finset.mem_filter, and_true]
    exact (mem_edgesOf_iff c L x j).2 ⟨hsub hx, hsub hxj⟩
  have his : i ⊆ s := by
    intro e he
    simp only [i, t, Finset.mem_filter] at he
    obtain ⟨⟨he, hj⟩, hin⟩ := he
    simp only [s, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk]
    refine ⟨e.1, ⟨?_, ?_⟩, Prod.ext rfl hj.symm⟩
    · rw [halfOpenCube, Fintype.mem_piFinset]
      intro i'
      obtain ⟨h1, h2⟩ := hin i'
      exact Finset.mem_Ico.2 ⟨h1.le, by omega⟩
    · rw [halfOpenCube, Fintype.mem_piFinset]
      intro i'
      obtain ⟨h1, h2⟩ := hin i'
      rw [← unit_eq_unitVec, add_unit_apply_coord]
      refine Finset.mem_Ico.2 ⟨?_, ?_⟩ <;> split_ifs <;> omega
  have hw1 : ∀ e ∈ i, faceWeight c L e = 1 := by
    intro e he
    simp only [i, Finset.mem_filter] at he
    have hcount : faceCount c L e = 0 := by
      rw [faceCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i' _ h
      obtain ⟨h1, h2⟩ := he.2 i'
      rcases h.2 with h3 | h3 <;> omega
    rw [faceWeight, hcount, pow_zero]
  have hw : ∀ e ∈ t, 0 ≤ faceWeight c L e ∧ faceWeight c L e ≤ 1 := fun e _ =>
    ⟨pow_nonneg (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num)⟩
  have hmain := abs_sum_weighted_sub_sum_le hst his (faceWeight c L)
    (fun e => v e.tgt - v e.src) hw1 hw
  have htdi : t \ i = boundaryEdges c L j := by
    rw [boundaryEdges, Finset.filter_not]
  rw [htdi] at hmain
  rw [gradSum_halfOpenCube_eq, blockMean, ← mul_sub, abs_mul, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left hmain hK

/-- The number of faces containing an edge is at most `d`. -/
theorem faceCount_le (c : Site d) (L : ℕ) (e : Edge d) : faceCount c L e ≤ d := by
  classical
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]

/-- **The block mean against the spatial average**: for `L ≥ 1`,
`|(∇v)_□ - L^{-d} ⟨∇v⟩_{c + {0, …, L-1}^d}|² ≤ 12 d 4^d L⁻¹ cubeAvg(|∇v|²)` on
`□ = c + {0, …, L}^d`. -/
theorem sum_sq_blockMean_sub_gradSum_le (c : Site d) {L : ℕ} (hL : 1 ≤ L) (v : Site d → ℝ) :
    ∑ j : Fin d, (blockMean c L (fun e => v e.tgt - v e.src) j -
        ((L : ℝ) ^ d)⁻¹ * gradSum (halfOpenCube c L) v j) ^ 2 ≤
      12 * d * 4 ^ d * (L : ℝ)⁻¹ * cubeAvg c L (fun e => (v e.tgt - v e.src) ^ 2) := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  set F : Edge d → ℝ := fun e => v e.tgt - v e.src with hF
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  set K : ℝ := ((L : ℝ) ^ d)⁻¹ with hKdef
  have hK : 0 < K := by positivity
  set B : ℝ := 3 * d * ((L : ℝ) + 1) ^ (d - 1) with hB
  have hB0 : 0 ≤ B := by positivity
  have hj : ∀ j : Fin d, (blockMean c L F j - K * gradSum (halfOpenCube c L) v j) ^ 2 ≤
      K ^ 2 * (4 * B) * ∑ e ∈ (edgesOf c L).filter (fun e => e.2 = j), F e ^ 2 := by
    intro j
    have h1 := abs_blockMean_sub_gradSum_le c L v j
    set S := ∑ e ∈ boundaryEdges c L j, |F e| with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun e _ => abs_nonneg _
    have h2 : S ^ 2 ≤ ((boundaryEdges c L j).card : ℝ) *
        ∑ e ∈ boundaryEdges c L j, F e ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := boundaryEdges c L j) (f := fun e => |F e|)
      simpa only [sq_abs] using this
    have h3 : ∑ e ∈ boundaryEdges c L j, F e ^ 2 ≤
        ∑ e ∈ (edgesOf c L).filter (fun e => e.2 = j), F e ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => sq_nonneg _
    have h4 : ((boundaryEdges c L j).card : ℝ) ≤ B := by
      have := card_boundaryEdges_le c L j
      rw [hB]
      exact_mod_cast this
    have hT0 : 0 ≤ ∑ e ∈ (edgesOf c L).filter (fun e => e.2 = j), F e ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hb0 : 0 ≤ ∑ e ∈ boundaryEdges c L j, F e ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc (blockMean c L F j - K * gradSum (halfOpenCube c L) v j) ^ 2
        = |blockMean c L F j - K * gradSum (halfOpenCube c L) v j| ^ 2 := (sq_abs _).symm
      _ ≤ (K * (2 * S)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = K ^ 2 * 4 * S ^ 2 := by ring
      _ ≤ K ^ 2 * 4 * (B * ∑ e ∈ (edgesOf c L).filter (fun e => e.2 = j), F e ^ 2) := by
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
        exact mul_le_mul h4 h3 hb0 hB0
      _ = K ^ 2 * (4 * B) * ∑ e ∈ (edgesOf c L).filter (fun e => e.2 = j), F e ^ 2 := by ring
  have hsum : ∑ j : Fin d, ∑ e ∈ (edgesOf c L).filter (fun e => e.2 = j), F e ^ 2 =
      ∑ e ∈ edgesOf c L, F e ^ 2 := Finset.sum_fiberwise _ _ _
  have hw : ∑ e ∈ edgesOf c L, F e ^ 2 ≤
      2 ^ d * ∑ e ∈ edgesOf c L, faceWeight c L e * F e ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have hfw : (1 / 2 : ℝ) ^ d ≤ faceWeight c L e :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (faceCount_le c L e)
    have h2d : (2 : ℝ) ^ d * (1 / 2) ^ d = 1 := by rw [← mul_pow]; norm_num
    calc F e ^ 2 = 2 ^ d * ((1 / 2) ^ d * F e ^ 2) := by rw [← mul_assoc, h2d, one_mul]
      _ ≤ 2 ^ d * (faceWeight c L e * F e ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfw (sq_nonneg _)) (by positivity)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpow : ((L : ℝ) + 1) ^ (d - 1) ≤ 2 ^ (d - 1) * (L : ℝ) ^ (d - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hKL : K * (L : ℝ) ^ (d - 1) = (L : ℝ)⁻¹ := by
    have hL0 : (L : ℝ) ≠ 0 := hLpos.ne'
    have hLd : (L : ℝ) ^ d = (L : ℝ) ^ (d - 1) * L := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hKdef, hLd]
    field_simp
  have h4d : (2 : ℝ) ^ d * 2 ^ (d - 1) ≤ 4 ^ d := by
    have : (4 : ℝ) ^ d = 2 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  have hca : cubeAvg c L (fun e => (v e.tgt - v e.src) ^ 2) =
      K * ∑ e ∈ edgesOf c L, faceWeight c L e * F e ^ 2 := rfl
  have hE0 : 0 ≤ ∑ e ∈ edgesOf c L, faceWeight c L e * F e ^ 2 :=
    Finset.sum_nonneg fun e _ => mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg _)
  rw [hca]
  calc ∑ j : Fin d, (blockMean c L F j - K * gradSum (halfOpenCube c L) v j) ^ 2
      ≤ ∑ j : Fin d, K ^ 2 * (4 * B) *
          ∑ e ∈ (edgesOf c L).filter (fun e => e.2 = j), F e ^ 2 := Finset.sum_le_sum fun j _ => hj j
    _ = K ^ 2 * (4 * B) * ∑ e ∈ edgesOf c L, F e ^ 2 := by rw [← Finset.mul_sum, hsum]
    _ ≤ K ^ 2 * (4 * B) * (2 ^ d * ∑ e ∈ edgesOf c L, faceWeight c L e * F e ^ 2) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = 12 * d * 2 ^ d * (K * ((L : ℝ) + 1) ^ (d - 1)) *
          (K * ∑ e ∈ edgesOf c L, faceWeight c L e * F e ^ 2) := by rw [hB]; ring
    _ ≤ 12 * d * 2 ^ d * (K * (2 ^ (d - 1) * (L : ℝ) ^ (d - 1))) *
          (K * ∑ e ∈ edgesOf c L, faceWeight c L e * F e ^ 2) := by
        gcongr
    _ = 12 * d * (2 ^ d * 2 ^ (d - 1)) * (L : ℝ)⁻¹ *
          (K * ∑ e ∈ edgesOf c L, faceWeight c L e * F e ^ 2) := by
        rw [← hKL]; ring
    _ ≤ 12 * d * 4 ^ d * (L : ℝ)⁻¹ * (K * ∑ e ∈ edgesOf c L, faceWeight c L e * F e ^ 2) := by
        gcongr

end Rigidity.Proofs.Multiscale

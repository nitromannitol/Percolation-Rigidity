import Rigidity.Proofs.Green.DarioGuPoincareBall

/-!
# The triple of a triadic cube and its nine subcubes

Ingredients of the probabilistic part of the weak Poincaré inequality on balls of the planar
infinite cluster (`ClusterPoincareTwo`): the triple `enl 1 m y` of the triadic cube of scale `m`
containing `y` is covered by the nine triadic cubes of scale `m` whose index is within `1` of that
of `y` (`idx_sub_le_of_mem_enl`), so a sum of a nonnegative function over the triple is at most the
sum of its sums over these nine cubes (`sum_enl_le_sum_cubes`).
-/

open Finset LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster

namespace Rigidity.Green

/-- The vertices of the triple `enl 1 m y` lie in the triadic cubes of scale `m` whose index is
within `1` of that of `y`. -/
theorem idx_sub_le_of_mem_enl {m : ℕ} {y z : Vertex 2} (hz : z ∈ enl 1 m y) (i : Fin 2) :
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
    (T : ι → Finset (Vertex 2)) {f : Vertex 2 → ℝ} (hf : ∀ z, 0 ≤ f z) :
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
theorem mem_triadicCube_idx_self (m : ℕ) (z : Vertex 2) :
    z ∈ (⟨m, idx m z⟩ : TriadicCube 2).toIntegerCube.vertices := by
  rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
  exact mem_cube_self m z

/-- **The nine subcubes of the triple.** For `f ≥ 0`,
`Σ_{z ∈ enl 1 m y} f(z) ≤ Σ_{|e - idx_m(y)| ≤ 1} Σ_{z ∈ □_m(e)} f(z)`. -/
theorem sum_enl_le_sum_cubes (m : ℕ) (y : Vertex 2) {f : Vertex 2 → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ enl 1 m y, f z ≤
      ∑ e ∈ indexBox (idx m y) 1, ∑ z ∈ (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices, f z := by
  classical
  have hsub : enl 1 m y ⊆ (indexBox (idx m y) 1).biUnion
      (fun e => (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices) := by
    intro z hz
    rw [Finset.mem_biUnion]
    exact ⟨idx m z, mem_indexBox.2 fun i => idx_sub_le_of_mem_enl hz i,
      mem_triadicCube_idx_self m z⟩
  calc ∑ z ∈ enl 1 m y, f z
      ≤ ∑ z ∈ (indexBox (idx m y) 1).biUnion
          (fun e => (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices), f z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hf z
    _ ≤ _ := sum_biUnion_le_sum_sum _ _ hf

theorem card_indexBox_one (c : Vertex 2) : (indexBox c 1).card = 9 := by
  have := card_indexBox c (R := 1)
  simpa using this

open scoped ENNReal in
/-- **A good scale.** If the reach is dominated by `ss` and `Σ_{□_m(e)} ss⁴ ≤ C 9^m` on the nine
cubes of scale `m` around `y`, with `6561 C < 9^m`, then the partition cubes of the vertices of the
triple have scale at most `m - 3` and `Σ_{triple} (ρ² + 3ρ)² ≤ 144 C 9^m`: the hypotheses of
`sum_sq_sub_finAvg_clusterBall_le`. -/
theorem goodScale_consequences {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {y : Vertex 2}
    {m : ℕ} {Cf : ℝ} (ss : Vertex 2 → ℝ) (hreach : ∀ z, planarReach ω z ≤ ENNReal.ofReal (ss z))
    (hgood : ∀ e ∈ indexBox (idx m y) 1,
      ∑ z ∈ (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices, ss z ^ 4 ≤ Cf * 9 ^ m)
    (hm : 6561 * Cf < 9 ^ m) :
    (∀ z ∈ enl 1 m y, (planarPartCube ω z).scale + 3 ≤ m) ∧
      ∑ z ∈ enl 1 m y, (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2 ≤
        ENNReal.ofReal (144 * Cf * 9 ^ m) := by
  -- `3^{scale} ≤ ss`
  have h3 : ∀ z, (3 : ℝ) ^ (planarPartCube ω z).scale ≤ ss z := by
    intro z
    have h := (Rigidity.Proofs.Regularity.three_pow_planarPartCube_scale_le_planarReach hP z).trans
      (hreach z)
    rw [show (3 : ℝ≥0∞) ^ (planarPartCube ω z).scale =
      ENNReal.ofReal ((3 : ℝ) ^ (planarPartCube ω z).scale) by
        rw [ENNReal.ofReal_pow (by norm_num)]; norm_num] at h
    exact (ENNReal.ofReal_le_ofReal_iff' |>.1 h).resolve_right (by
      intro h'; have := (pow_pos (by norm_num : (0 : ℝ) < 3) (planarPartCube ω z).scale); linarith)
  have hss1 : ∀ z, 1 ≤ ss z := fun z => (one_le_pow₀ (by norm_num)).trans (h3 z)
  have hss0 : ∀ z, 0 ≤ ss z := fun z => zero_le_one.trans (hss1 z)
  -- `ss⁴ ≤ C 9^m` on the triple
  have hpt : ∀ z ∈ enl 1 m y, ss z ^ 4 ≤ Cf * 9 ^ m := by
    intro z hz
    refine le_trans ?_ (hgood (idx m z) (mem_indexBox.2 fun i => idx_sub_le_of_mem_enl hz i))
    exact Finset.single_le_sum (f := fun z => ss z ^ 4) (fun z _ => by positivity)
      (mem_triadicCube_idx_self m z)
  refine ⟨fun z hz => ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hk : m ≤ (planarPartCube ω z).scale + 2 := by omega
    set k := (planarPartCube ω z).scale
    have h4 : (3 : ℝ) ^ (4 * k) ≤ Cf * 9 ^ m := by
      calc (3 : ℝ) ^ (4 * k) = ((3 : ℝ) ^ k) ^ 4 := by rw [← pow_mul, mul_comm]
        _ ≤ ss z ^ 4 := pow_le_pow_left₀ (by positivity) (h3 z) 4
        _ ≤ _ := hpt z hz
    have h9 : (9 : ℝ) ^ m * 9 ^ m ≤ 6561 * 3 ^ (4 * k) := by
      have e1 : (9 : ℝ) ^ m * 9 ^ m = 3 ^ (4 * m) := by
        rw [← pow_add, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]; ring_nf
      have e2 : (6561 : ℝ) * 3 ^ (4 * k) = 3 ^ (4 * k + 8) := by
        rw [pow_add]; norm_num; ring
      rw [e1, e2]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h9m : (0 : ℝ) < 9 ^ m := by positivity
    nlinarith
  · have hterm : ∀ z ∈ enl 1 m y, (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2 ≤
        ENNReal.ofReal (16 * ss z ^ 4) := by
      intro z _
      have h1 : (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2 ≤
          (ENNReal.ofReal (ss z) ^ 2 + 3 * ENNReal.ofReal (ss z)) ^ 2 := by
        gcongr
        · exact hreach z
        · exact hreach z
      have he : (ENNReal.ofReal (ss z) ^ 2 + 3 * ENNReal.ofReal (ss z)) ^ 2 =
          ENNReal.ofReal ((ss z ^ 2 + 3 * ss z) ^ 2) := by
        rw [ENNReal.ofReal_pow (by have := hss0 z; positivity), ENNReal.ofReal_add
          (by have := hss0 z; positivity) (by have := hss0 z; positivity),
          ENNReal.ofReal_pow (hss0 z), ENNReal.ofReal_mul (by norm_num)]
        norm_num
      have hle : (ss z ^ 2 + 3 * ss z) ^ 2 ≤ 16 * ss z ^ 4 := by
        have := hss1 z
        nlinarith [sq_nonneg (ss z), sq_nonneg (ss z - 1)]
      exact h1.trans (he.le.trans (ENNReal.ofReal_le_ofReal hle))
    calc ∑ z ∈ enl 1 m y, (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2
        ≤ ∑ z ∈ enl 1 m y, ENNReal.ofReal (16 * ss z ^ 4) := Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (∑ z ∈ enl 1 m y, 16 * ss z ^ 4) :=
          (ENNReal.ofReal_sum_of_nonneg fun z _ => by have := hss0 z; positivity).symm
      _ ≤ ENNReal.ofReal (144 * Cf * 9 ^ m) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 := sum_enl_le_sum_cubes m y (f := fun z => 16 * ss z ^ 4)
            (fun z => by have := hss0 z; positivity)
          refine h1.trans ?_
          calc ∑ e ∈ indexBox (idx m y) 1, ∑ z ∈ (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices,
                16 * ss z ^ 4
              ≤ ∑ _e ∈ indexBox (idx m y) 1, 16 * (Cf * 9 ^ m) := by
                refine Finset.sum_le_sum fun e he => ?_
                rw [← Finset.mul_sum]
                exact mul_le_mul_of_nonneg_left (hgood e he) (by norm_num)
            _ = 144 * Cf * 9 ^ m := by
                rw [Finset.sum_const, card_indexBox_one, nsmul_eq_mul]
                push_cast
                ring

end Rigidity.Green

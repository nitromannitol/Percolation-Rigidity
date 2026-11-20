import Rigidity.Proofs.Percolation.PlanarBoundaryWeight

/-!
# Weights of sets of lattice edges

For a set `F` of lattice edges of a resolved cube `U`, the weight `W_F(a)` counts the edges of `F`
whose window contains `a`. Each window lies in the square of side `9s` around the partition cube of
one of the endpoints of its edge. Two such squares around `x` and `x'` intersect only if
`|x - x'|_∞ ≤ 5 (s_x + s_{x'})`, and then in at most `81 s_x s_{x'}` vertices; bounding the
indicator of `|x - x'|_∞ ≤ 10 max(s_x, s_{x'})` by `(10 max(s_x, s_{x'}) / max(|x - x'|_∞, 1)) ^ 4`
and using that `∑_{z ∈ ℤ²} max(|z|_∞, 1) ^ (-4) ≤ 25`, we get

`∑_{a ∈ C_*(U)} W_F(a) ^ 2 ≤ 162000000 ∑_{(x, x + e_i) ∈ F} (s_x ^ 6 + s_{x + e_i} ^ 6)`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The weight of a set of lattice edges at a vertex. -/
noncomputable def edgeSetWeight (ω : Configuration 2) (U : TriadicCube 2)
    (F : Finset (Vertex 2 × Fin 2)) (a : Vertex 2) : ℝ :=
  ∑ k ∈ F, if a ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2) then 1 else 0

theorem edgeSetWeight_nonneg (U : TriadicCube 2) (F : Finset (Vertex 2 × Fin 2))
    (a : Vertex 2) : 0 ≤ edgeSetWeight ω U F a :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem coarseWeight_eq_edgeSetWeight (U : TriadicCube 2) (a : Vertex 2) :
    coarseWeight ω U a = edgeSetWeight ω U (latticeEdgesIn U) a := rfl

/-- **The two-dimensional kernel is summable.** -/
theorem sum_invQuartic_le (S : Finset (Vertex 2)) (x : Vertex 2) :
    ∑ x' ∈ S, 1 / (max (supDist x x' : ℝ) 1) ^ 4 ≤ 25 := by
  have hpt : ∀ x' : Vertex 2, 1 / (max (supDist x x' : ℝ) 1) ^ 4 ≤
      invSqProfile (x 0 - x' 0) * invSqProfile (x 1 - x' 1) := by
    intro x'
    unfold invSqProfile
    have h0 : |((x 0 - x' 0 : ℤ) : ℝ)| ≤ (supDist x x' : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast abs_sub_le_supDist x x' 0
    have h1 : |((x 1 - x' 1 : ℤ) : ℝ)| ≤ (supDist x x' : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast abs_sub_le_supDist x x' 1
    set a := max (|((x 0 - x' 0 : ℤ) : ℝ)|) 1
    set b := max (|((x 1 - x' 1 : ℤ) : ℝ)|) 1
    set m := max (supDist x x' : ℝ) 1
    have ha : 1 ≤ a := le_max_right _ _
    have hb : 1 ≤ b := le_max_right _ _
    have ham : a ≤ m := max_le_max h0 le_rfl
    have hbm : b ≤ m := max_le_max h1 le_rfl
    rw [div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    calc a ^ 2 * b ^ 2 ≤ m ^ 2 * m ^ 2 := by gcongr
      _ = m ^ 4 := by ring
  have hinj : Set.InjOn (fun x' : Vertex 2 => (x' 0, x' 1)) ↑S := by
    intro y _ z _ h
    simp only [Prod.mk.injEq] at h
    funext l
    fin_cases l
    · exact h.1
    · exact h.2
  have hfac : ∀ T : Finset ℤ, ∀ m : ℤ, ∑ t ∈ T, invSqProfile (m - t) ≤ 5 := by
    intro T m
    rw [← Finset.sum_image (f := invSqProfile) (s := T) (g := fun t => m - t)
      (fun t _ t' _ h => by simpa using h)]
    exact sum_invSqProfile_le _
  calc ∑ x' ∈ S, 1 / (max (supDist x x' : ℝ) 1) ^ 4
      ≤ ∑ x' ∈ S, invSqProfile (x 0 - x' 0) * invSqProfile (x 1 - x' 1) :=
        Finset.sum_le_sum fun x' _ => hpt x'
    _ = ∑ t ∈ S.image (fun x' : Vertex 2 => (x' 0, x' 1)),
          invSqProfile (x 0 - t.1) * invSqProfile (x 1 - t.2) :=
        (Finset.sum_image (f := fun t : ℤ × ℤ =>
          invSqProfile (x 0 - t.1) * invSqProfile (x 1 - t.2)) hinj).symm
    _ ≤ ∑ t ∈ S.image (fun x' : Vertex 2 => x' 0) ×ˢ S.image (fun x' : Vertex 2 => x' 1),
          invSqProfile (x 0 - t.1) * invSqProfile (x 1 - t.2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ =>
          mul_nonneg (invSqProfile_nonneg _) (invSqProfile_nonneg _)
        intro t ht
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ht
        exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hy, Finset.mem_image_of_mem _ hy⟩
    _ = (∑ t ∈ S.image (fun x' : Vertex 2 => x' 0), invSqProfile (x 0 - t)) *
          ∑ t ∈ S.image (fun x' : Vertex 2 => x' 1), invSqProfile (x 1 - t) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
    _ ≤ 5 * 5 := by
        gcongr
        · exact Finset.sum_nonneg fun _ _ => invSqProfile_nonneg _
        · exact hfac _ _
        · exact hfac _ _
    _ = 25 := by norm_num

/-- `a b (a + b) ^ 4 ≤ 16 (a ^ 6 + b ^ 6)` for nonnegative `a, b`. -/
theorem six_power_aux {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b * (a + b) ^ 4 ≤ 16 * (a ^ 6 + b ^ 6) := by
  have hA : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have hB : (a ^ 2 + b ^ 2) ^ 2 ≤ 2 * (a ^ 4 + b ^ 4) := by nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have h1 : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
    calc (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hA 2
      _ = 4 * (a ^ 2 + b ^ 2) ^ 2 := by ring
      _ ≤ 4 * (2 * (a ^ 4 + b ^ 4)) := by gcongr
      _ = 8 * (a ^ 4 + b ^ 4) := by ring
  have h2 : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  have h3 : (a ^ 2 + b ^ 2) * (a ^ 4 + b ^ 4) ≤ 2 * (a ^ 6 + b ^ 6) := by
    nlinarith [mul_nonneg (sq_nonneg (a ^ 2 - b ^ 2)) (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  calc a * b * (a + b) ^ 4 ≤ (a ^ 2 + b ^ 2) / 2 * (8 * (a ^ 4 + b ^ 4)) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = 4 * ((a ^ 2 + b ^ 2) * (a ^ 4 + b ^ 4)) := by ring
    _ ≤ 4 * (2 * (a ^ 6 + b ^ 6)) := by gcongr
    _ ≤ 16 * (a ^ 6 + b ^ 6) := by nlinarith [pow_nonneg ha 6, pow_nonneg hb 6]

/-- **Intersections of squares around partition cubes**, with a fourth-power kernel. -/
theorem card_inter_ninefold_le_four (x x' : Vertex 2) :
    (((planarPartCube ω x).ninefold.vertices ∩ (planarPartCube ω x').ninefold.vertices).card : ℝ)
      * (max (supDist x x' : ℝ) 1) ^ 4 ≤
      810000 * (partSide ω x ^ 6 + partSide ω x' ^ 6) := by
  set Q := planarPartCube ω x
  set Q' := planarPartCube ω x'
  set ρ := partSide ω x with hρ
  set ρ' := partSide ω x' with hρ'
  have hρ1 : 1 ≤ ρ := one_le_partSide x
  have hρ1' : 1 ≤ ρ' := one_le_partSide x'
  have hcardN : ∀ R : TriadicCube 2, ((R.ninefold.vertices.card : ℕ) : ℝ) =
      81 * ((3 : ℝ) ^ R.scale) ^ 2 := by
    intro R
    rw [IntegerCube.card_vertices]
    change (((9 * 3 ^ R.scale) ^ 2 : ℕ) : ℝ) = _
    push_cast
    ring
  rcases (Q.ninefold.vertices ∩ Q'.ninefold.vertices).eq_empty_or_nonempty with he | ⟨a, ha⟩
  · rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  have hcard : ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) ≤ 81 * ρ * ρ' := by
    have h1 : ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) ≤ 81 * ρ ^ 2 := by
      rw [hρ, partSide, ← hcardN Q]
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    have h2 : ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) ≤ 81 * ρ' ^ 2 := by
      rw [hρ', partSide, ← hcardN Q']
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    rcases le_total ρ ρ' with h | h
    · nlinarith
    · nlinarith
  obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
  have hd : (supDist x x' : ℝ) ≤ 5 * ρ + 5 * ρ' := by
    have hx : x ∈ Q.vertices := mem_planarPartCube x
    have hx' : x' ∈ Q'.vertices := mem_planarPartCube x'
    have hdist : ∀ i, |x i - x' i| ≤ 5 * 3 ^ Q.scale + 5 * 3 ^ Q'.scale := by
      intro i
      have h1 := (TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 ha1)) i
      have h2 := (TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 ha2)) i
      have h3 := Q.abs_sub_center_le hx i
      have h4 := Q'.abs_sub_center_le hx' i
      have h5 := Q.two_mul_ninefoldRadius
      have h6 := Q'.two_mul_ninefoldRadius
      have h7 := le_abs_self (x i - Q.center i)
      have h8 := neg_abs_le (x i - Q.center i)
      have h9 := le_abs_self (x' i - Q'.center i)
      have h10 := neg_abs_le (x' i - Q'.center i)
      rw [abs_le] at h1 h2 ⊢
      constructor <;> omega
    have hmax : supDist x x' ≤ 5 * 3 ^ Q.scale + 5 * 3 ^ Q'.scale :=
      max_le (hdist 0) (hdist 1)
    have : ((supDist x x' : ℤ) : ℝ) ≤ ((5 * 3 ^ Q.scale + 5 * 3 ^ Q'.scale : ℤ) : ℝ) := by
      exact_mod_cast hmax
    push_cast at this
    rw [hρ, hρ', partSide, partSide]
    exact this
  have hm : (max (supDist x x') 1 : ℝ) ≤ 5 * ρ + 5 * ρ' := max_le hd (by linarith)
  have hm0 : (0 : ℝ) ≤ (max (supDist x x') 1 : ℝ) := le_trans zero_le_one (le_max_right _ _)
  have hsq : (max (supDist x x') 1 : ℝ) ^ 4 ≤ (5 * ρ + 5 * ρ') ^ 4 :=
    pow_le_pow_left₀ hm0 hm 4
  have hρρ : 0 < ρ * ρ' := by positivity
  calc ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) *
        (max (supDist x x') 1 : ℝ) ^ 4
      ≤ (81 * ρ * ρ') * (5 * ρ + 5 * ρ') ^ 4 :=
        mul_le_mul hcard hsq (by positivity) (by positivity)
    _ = 50625 * (ρ * ρ' * (ρ + ρ') ^ 4) := by ring
    _ ≤ 50625 * (16 * (ρ ^ 6 + ρ' ^ 6)) :=
        mul_le_mul_of_nonneg_left (six_power_aux (by linarith) (by linarith)) (by norm_num)
    _ = 810000 * (ρ ^ 6 + ρ' ^ 6) := by ring

/-- Squares of sums of indicators, summed over a finite set, are at most the sizes of pairwise
intersections. -/
theorem sum_sq_indicator_le_card {J : Type*} (A : Finset (Vertex 2)) (I : Finset J)
    (N : J → Finset (Vertex 2)) :
    ∑ a ∈ A, (∑ j ∈ I, (if a ∈ N j then (1 : ℝ) else 0)) ^ 2 ≤
      ∑ j ∈ I, ∑ j' ∈ I, ((N j ∩ N j').card : ℝ) := by
  calc ∑ a ∈ A, (∑ j ∈ I, (if a ∈ N j then (1 : ℝ) else 0)) ^ 2
      = ∑ j ∈ I, ∑ j' ∈ I, ∑ a ∈ A, (if a ∈ N j ∩ N j' then (1 : ℝ) else 0) := by
        simp only [sq, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun a _ => ?_
        by_cases h1 : a ∈ N j <;> by_cases h2 : a ∈ N j' <;> simp [h1, h2]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => ?_
        rw [Finset.sum_boole]
        exact_mod_cast Finset.card_le_card fun a ha => (Finset.mem_filter.1 ha).2

/-- The endpoint of an oriented edge: the upper one for `true`, the lower one for `false`. -/
def edgeEnd (k : (Vertex 2 × Fin 2) × Bool) : Vertex 2 :=
  if k.2 then k.1.1 + unitVertex k.1.2 else k.1.1

theorem sum_edgeEnd (F : Finset (Vertex 2 × Fin 2)) (f : Vertex 2 → ℝ) :
    ∑ k ∈ F ×ˢ (Finset.univ : Finset Bool), f (edgeEnd k) =
      ∑ k ∈ F, (f (k.1 + unitVertex k.2) + f k.1) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  rfl

/-- **Squared edge-set weights.** -/
theorem sum_sq_edgeSetWeight_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {F : Finset (Vertex 2 × Fin 2)} (hF : F ⊆ latticeEdgesIn U) :
    ∑ x : ↥(clusterVertices ω U), edgeSetWeight ω U F x.1 ^ 2 ≤
      162000000 * ∑ k ∈ F, (partSide ω (k.1 + unitVertex k.2) ^ 6 + partSide ω k.1 ^ 6) := by
  set J := F ×ˢ (Finset.univ : Finset Bool)
  set N : (Vertex 2 × Fin 2) × Bool → Finset (Vertex 2) := fun j =>
    (planarPartCube ω (edgeEnd j)).ninefold.vertices with hN
  -- the weight is at most the number of endpoints whose square contains the vertex
  have hW : ∀ a : Vertex 2, edgeSetWeight ω U F a ≤
      ∑ j ∈ J, (if a ∈ N j then (1 : ℝ) else 0) := by
    intro a
    rw [sum_edgeEnd F (fun z => if a ∈ (planarPartCube ω z).ninefold.vertices then 1 else 0)]
    refine Finset.sum_le_sum fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 (hF hk)
    have hx : k.1 ∈ U.vertices :=
      (U.mem_toIntegerCube_vertices _).1 (Finset.mem_product.1 hk1).1
    have hy : k.1 + unitVertex k.2 ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hk2
    have h := indicator_le_add_indicator (P := a ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2))
      (R := a ∈ (planarPartCube ω k.1).ninefold.vertices)
      (S := a ∈ (planarPartCube ω (k.1 + unitVertex k.2)).ninefold.vertices)
      fun h => mem_ninefold_of_mem_coarseEdgeWindow hP hU hx hy (abs_sub_unitVertex_le k.1 k.2) h
    linarith
  -- squares to intersections
  have h1 : ∑ x : ↥(clusterVertices ω U), edgeSetWeight ω U F x.1 ^ 2 ≤
      ∑ j ∈ J, ∑ j' ∈ J, ((N j ∩ N j').card : ℝ) := by
    calc ∑ x : ↥(clusterVertices ω U), edgeSetWeight ω U F x.1 ^ 2
        ≤ ∑ x : ↥(clusterVertices ω U), (∑ j ∈ J, (if x.1 ∈ N j then (1 : ℝ) else 0)) ^ 2 :=
          Finset.sum_le_sum fun x _ =>
            pow_le_pow_left₀ (edgeSetWeight_nonneg U F x.1) (hW x.1) 2
      _ = ∑ a ∈ clusterVertices ω U, (∑ j ∈ J, (if a ∈ N j then (1 : ℝ) else 0)) ^ 2 :=
          Finset.sum_coe_sort (clusterVertices ω U)
            (fun a => (∑ j ∈ J, (if a ∈ N j then (1 : ℝ) else 0)) ^ 2)
      _ ≤ _ := sum_sq_indicator_le_card _ J N
  -- the kernel along the endpoints
  have hker : ∀ j ∈ J, ∑ j' ∈ J, 1 / (max (supDist (edgeEnd j) (edgeEnd j') : ℝ) 1) ^ 4 ≤ 100 := by
    intro j _
    set f : Vertex 2 → ℝ := fun z => 1 / (max (supDist (edgeEnd j) z : ℝ) 1) ^ 4 with hf
    have hf0 : ∀ z, 0 ≤ f z := fun z => by
      simp only [hf]
      positivity
    rw [sum_edgeEnd F f]
    calc ∑ k ∈ F, (f (k.1 + unitVertex k.2) + f k.1)
        ≤ ∑ k ∈ latticeEdgesIn U, (f (k.1 + unitVertex k.2) + f k.1) :=
          Finset.sum_le_sum_of_subset_of_nonneg hF fun k _ _ => add_nonneg (hf0 _) (hf0 _)
      _ = ∑ k ∈ latticeEdgesIn U, f (k.1 + unitVertex k.2) +
            ∑ k ∈ latticeEdgesIn U, f k.1 := Finset.sum_add_distrib
      _ ≤ 2 * ∑ z ∈ U.toIntegerCube.vertices, f z + 2 * ∑ z ∈ U.toIntegerCube.vertices, f z :=
          add_le_add (sum_latticeEdgesIn_snd_le U f hf0) (sum_latticeEdgesIn_fst_le U f hf0)
      _ ≤ 2 * 25 + 2 * 25 := by
          gcongr
          · exact sum_invQuartic_le _ _
          · exact sum_invQuartic_le _ _
      _ = 100 := by norm_num
  have hm_pos : ∀ j j' : (Vertex 2 × Fin 2) × Bool,
      0 < (max (supDist (edgeEnd j) (edgeEnd j') : ℝ) 1) ^ 4 :=
    fun _ _ => pow_pos (lt_max_of_lt_right one_pos) 4
  have h2 : ∀ j j' : (Vertex 2 × Fin 2) × Bool, ((N j ∩ N j').card : ℝ) ≤
      (810000 * partSide ω (edgeEnd j) ^ 6 + 810000 * partSide ω (edgeEnd j') ^ 6) /
        (max (supDist (edgeEnd j) (edgeEnd j') : ℝ) 1) ^ 4 := by
    intro j j'
    rw [le_div_iff₀ (hm_pos j j')]
    have := card_inter_ninefold_le_four (ω := ω) (edgeEnd j) (edgeEnd j')
    linarith
  have hsum := sum_sum_add_div_le J (fun j => 810000 * partSide ω (edgeEnd j) ^ 6)
    (fun j j' => (max (supDist (edgeEnd j) (edgeEnd j') : ℝ) 1) ^ 4)
    (fun j => by have := one_le_partSide (ω := ω) (edgeEnd j); positivity)
    (fun j j' => by simp only [supDist_comm]) 100 hker
  calc ∑ x : ↥(clusterVertices ω U), edgeSetWeight ω U F x.1 ^ 2
      ≤ ∑ j ∈ J, ∑ j' ∈ J, ((N j ∩ N j').card : ℝ) := h1
    _ ≤ ∑ j ∈ J, ∑ j' ∈ J,
          (810000 * partSide ω (edgeEnd j) ^ 6 + 810000 * partSide ω (edgeEnd j') ^ 6) /
            (max (supDist (edgeEnd j) (edgeEnd j') : ℝ) 1) ^ 4 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => h2 j j'
    _ ≤ 2 * 100 * ∑ j ∈ J, 810000 * partSide ω (edgeEnd j) ^ 6 := hsum
    _ = 162000000 * ∑ k ∈ F, (partSide ω (k.1 + unitVertex k.2) ^ 6 + partSide ω k.1 ^ 6) := by
        rw [← Finset.mul_sum, sum_edgeEnd F (fun z => partSide ω z ^ 6)]
        ring

end Rigidity.Percolation

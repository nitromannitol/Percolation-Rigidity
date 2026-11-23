import Rigidity.Proofs.Corrector.DarioCoarseHeatField

/-!
# Growth of functions of finite energy on the planar cluster

In the proof of Lemma 3.3, Case 3 of Step 2, Dario asserts that the function
`χ_p - χ_p^e - c ∇G(e, ·)` has sublinear growth, "by the sublinear growth of the corrector, the
`L²` bound (2.14) on `∇∇G(e, ·)` and a version of the Poincaré inequality on the cluster", and
concludes by the Liouville theorem. The missing ingredient is the sublinear growth of a function
`W` of finite energy on the infinite cluster. This file proves the deterministic estimate behind it,
with the planar partition: if all partition cubes of the points of the square `|y|_∞ ≤ R` have side
at most `s`, then for every vertex `z` of that square in an infinite open cluster

`|W(z) - W([0]_𝒫)| ≤ 400 s^{3/2} (R + 1)^{1/2} E^{1/2}`,

where `E` bounds the energy of `W` on every finite set (`abs_sub_coarseAnchor_zero_le`). The proof
compares `W` with its coarsening ((2.8)-(2.10) of Armstrong and Dario, in main's planar form
`abs_sub_coarseAnchor_le`, `abs_coarseAnchor_sub_le`), bounds the total variation over the square
of side `9s` around a partition cube by Cauchy-Schwarz (`edgeVariationIn_le`), and sums along two
straight segments from the origin to `z`, where each vertex lies in at most `10s + 1` of the
squares (`sum_localEnergy_le`).
-/

namespace Rigidity.Corrector

open Filter Topology LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

variable (ω : Configuration 2)

/-- The energy `Σ_{x, y ∈ S, x ∼ y open} (W(x) - W(y))²` of `W` inside a finite set, each open edge
counted in both orientations. -/
noncomputable def localEnergy (S : Finset (Vertex 2)) (W : Vertex 2 → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, if (openGraph ω).Adj x y then (W x - W y) ^ 2 else 0

theorem localEnergy_nonneg (S : Finset (Vertex 2)) (W : Vertex 2 → ℝ) :
    0 ≤ localEnergy ω S W :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem sum_adj_le_four (S : Finset (Vertex 2)) (x : Vertex 2) :
    (∑ y ∈ S, if (openGraph ω).Adj x y then (1 : ℝ) else 0) ≤ 4 := by
  rw [Finset.sum_boole]
  have h : (S.filter fun y => (openGraph ω).Adj x y).card ≤ (openGraph ω).degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card fun y hy =>
      (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hy).2
  have h4 := Rigidity.Green.openGraph_degree_le_four ω x
  exact_mod_cast h.trans h4

/-- **Total variation by energy**: `TV_S(W) ≤ (4|S|)^{1/2} E_S(W)^{1/2}`. -/
theorem edgeVariationIn_le (S : Finset (Vertex 2)) (W : Vertex 2 → ℝ) :
    edgeVariationIn ω S W ≤ Real.sqrt (4 * S.card) * Real.sqrt (localEnergy ω S W) := by
  set f : Vertex 2 × Vertex 2 → ℝ := fun q => if (openGraph ω).Adj q.1 q.2 then 1 else 0
  set g : Vertex 2 × Vertex 2 → ℝ := fun q =>
    if (openGraph ω).Adj q.1 q.2 then |W q.1 - W q.2| else 0
  have h1 : edgeVariationIn ω S W = ∑ q ∈ S ×ˢ S, f q * g q := by
    unfold edgeVariationIn
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [f, g]
    split_ifs <;> simp
  have h2 : ∑ q ∈ S ×ˢ S, f q ^ 2 ≤ 4 * S.card := by
    rw [Finset.sum_product]
    calc ∑ x ∈ S, ∑ y ∈ S, f (x, y) ^ 2
        = ∑ x ∈ S, ∑ y ∈ S, (if (openGraph ω).Adj x y then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          simp only [f]
          split_ifs <;> simp
      _ ≤ ∑ _x ∈ S, (4 : ℝ) := Finset.sum_le_sum fun x _ => sum_adj_le_four ω S x
      _ = 4 * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have h3 : ∑ q ∈ S ×ˢ S, g q ^ 2 = localEnergy ω S W := by
    unfold localEnergy
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [g]
    split_ifs <;> simp [sq_abs]
  rw [h1, ← h3]
  exact (Real.sum_mul_le_sqrt_mul_sqrt _ f g).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _))

/-- **Energies of overlapping sets**: if every vertex lies in at most `M` of the sets `S_k`,
`k < n`, then `Σ_k E_{S_k}(W) ≤ M E`. -/
theorem sum_localEnergy_le {W : Vertex 2 → ℝ} {E : ℝ}
    (hE : ∀ F : Finset (Vertex 2), localEnergy ω F W ≤ E) (S : ℕ → Finset (Vertex 2)) (n M : ℕ)
    (hM : ∀ x, ((Finset.range n).filter fun k => x ∈ S k).card ≤ M) :
    ∑ k ∈ Finset.range n, localEnergy ω (S k) W ≤ M * E := by
  set U := (Finset.range n).biUnion S with hU
  set e : Vertex 2 → ℝ := fun x =>
    ∑ y ∈ U, if (openGraph ω).Adj x y then (W x - W y) ^ 2 else 0 with he
  have he0 : ∀ x, 0 ≤ e x := fun x => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  have hSU : ∀ k ∈ Finset.range n, S k ⊆ U := fun k hk => Finset.subset_biUnion_of_mem S hk
  have step1 : ∀ k ∈ Finset.range n,
      localEnergy ω (S k) W ≤ ∑ x ∈ U, (if x ∈ S k then e x else 0) := by
    intro k hk
    rw [← Finset.sum_filter]
    have hf : U.filter (fun x => x ∈ S k) = S k := by
      ext x
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun h => hSU k hk h
    rw [hf]
    unfold localEnergy
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg (hSU k hk)
      (fun y _ _ => by split_ifs <;> positivity)
  calc ∑ k ∈ Finset.range n, localEnergy ω (S k) W
      ≤ ∑ k ∈ Finset.range n, ∑ x ∈ U, (if x ∈ S k then e x else 0) := Finset.sum_le_sum step1
    _ = ∑ x ∈ U, ∑ k ∈ Finset.range n, (if x ∈ S k then e x else 0) := Finset.sum_comm
    _ = ∑ x ∈ U, (((Finset.range n).filter fun k => x ∈ S k).card : ℝ) * e x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ U, (M : ℝ) * e x := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast hM x) (he0 x)
    _ = M * localEnergy ω U W := by rw [← Finset.mul_sum]; rfl
    _ ≤ M * E := mul_le_mul_of_nonneg_left (hE U) (Nat.cast_nonneg M)

/-! ### Coarse anchors along chains -/

/-- The square of side `9s` around the partition cube of `x`. -/
noncomputable def cubeRegion (x : Vertex 2) : Finset (Vertex 2) :=
  (planarPartCube ω x).ninefold.vertices

theorem card_cubeRegion (x : Vertex 2) :
    (cubeRegion ω x).card = (9 * 3 ^ (planarPartCube ω x).scale) ^ 2 :=
  IntegerCube.card_vertices _

theorem abs_sub_le_of_mem_cubeRegion {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x y : Vertex 2} (hx : x ∈ cubeRegion ω y) (i : Fin 2) :
    |x i - y i| ≤ 5 * 3 ^ (planarPartCube ω y).scale := by
  set Q := planarPartCube ω y
  have h1 : |x i - Q.center i| ≤ Q.ninefoldRadius :=
    (TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 hx)) i
  have h2 := TriadicCube.abs_sub_center_le (planarPartCube_spec hP y).1 i
  have h3 := Q.two_mul_ninefoldRadius
  have h4 : |x i - y i| ≤ |x i - Q.center i| + |y i - Q.center i| := by
    rw [abs_sub_comm (y i)]
    exact abs_sub_le _ _ _
  linarith

theorem abs_coarseAnchor_sub_le_add {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x y : Vertex 2} (hnear : ∀ i, |x i - y i| ≤ 1) (W : Vertex 2 → ℝ) :
    |W (planarCoarseAnchor ω x) - W (planarCoarseAnchor ω y)| ≤
      edgeVariationIn ω (cubeRegion ω x) W + edgeVariationIn ω (cubeRegion ω y) W := by
  have h0x := edgeVariationIn_nonneg ω (cubeRegion ω x) W
  have h0y := edgeVariationIn_nonneg ω (cubeRegion ω y) W
  rcases le_total (planarPartCube ω x).scale (planarPartCube ω y).scale with h | h
  · have := abs_coarseAnchor_sub_le hP hnear h W
    unfold cubeRegion at h0x h0y ⊢
    linarith
  · have hnear' : ∀ i, |y i - x i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    have := abs_coarseAnchor_sub_le hP hnear' h W
    rw [abs_sub_comm] at this
    unfold cubeRegion at h0x h0y ⊢
    linarith

/-- Along a chain of neighbouring points the coarsened function changes by at most twice the sum of
the total variations over the squares of the chain. -/
theorem abs_coarseAnchor_chain_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (z : ℕ → Vertex 2) (W : Vertex 2 → ℝ) (n : ℕ)
    (hstep : ∀ k < n, ∀ i, |z k i - z (k + 1) i| ≤ 1) :
    |W (planarCoarseAnchor ω (z n)) - W (planarCoarseAnchor ω (z 0))| ≤
      2 * ∑ k ∈ Finset.range (n + 1), edgeVariationIn ω (cubeRegion ω (z k)) W := by
  have key : ∀ n, (∀ k < n, ∀ i, |z k i - z (k + 1) i| ≤ 1) →
      |W (planarCoarseAnchor ω (z n)) - W (planarCoarseAnchor ω (z 0))| +
          edgeVariationIn ω (cubeRegion ω (z n)) W ≤
        2 * ∑ k ∈ Finset.range (n + 1), edgeVariationIn ω (cubeRegion ω (z k)) W := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [sub_self, abs_zero, zero_add, Finset.range_one, Finset.sum_singleton]
      have := edgeVariationIn_nonneg ω (cubeRegion ω (z 0)) W
      linarith
    | succ n ih =>
      intro hstep
      have ih' := ih fun k hk => hstep k (by omega)
      have hs := abs_coarseAnchor_sub_le_add hP (hstep n (by omega)) W
      have htri := abs_sub_le (W (planarCoarseAnchor ω (z (n + 1))))
        (W (planarCoarseAnchor ω (z n))) (W (planarCoarseAnchor ω (z 0)))
      have hsw := abs_sub_comm (W (planarCoarseAnchor ω (z (n + 1))))
        (W (planarCoarseAnchor ω (z n)))
      rw [Finset.sum_range_succ]
      linarith
  have h := key n hstep
  have := edgeVariationIn_nonneg ω (cubeRegion ω (z n)) W
  linarith

/-! ### Straight segments -/

/-- The point `u + σ k e_j`. -/
def segPoint (u : Vertex 2) (j : Fin 2) (σ : ℤ) (k : ℕ) : Vertex 2 :=
  fun i => if i = j then u i + σ * k else u i

theorem segPoint_apply_self (u : Vertex 2) (j : Fin 2) (σ : ℤ) (k : ℕ) :
    segPoint u j σ k j = u j + σ * k := by
  simp [segPoint]

theorem segPoint_zero (u : Vertex 2) (j : Fin 2) (σ : ℤ) : segPoint u j σ 0 = u := by
  funext i
  unfold segPoint
  split_ifs <;> simp

theorem abs_segPoint_step_le (u : Vertex 2) (j : Fin 2) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (k : ℕ)
    (i : Fin 2) : |segPoint u j σ k i - segPoint u j σ (k + 1) i| ≤ 1 := by
  unfold segPoint
  split_ifs
  · push_cast
    rcases hσ with rfl | rfl <;> simp
  · simp

/-- A segment meets the square of half-side `ρ` around `x` in at most `2ρ + 1` points. -/
theorem card_filter_segPoint_le (u : Vertex 2) (j : Fin 2) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (N : ℕ) (x : Vertex 2) (ρ : ℕ) :
    ((Finset.range N).filter fun k => |x j - segPoint u j σ k j| ≤ ρ).card ≤ 2 * ρ + 1 := by
  have hmap : ∀ k ∈ (Finset.range N).filter (fun k => |x j - segPoint u j σ k j| ≤ ρ),
      x j - segPoint u j σ k j ∈ Finset.Icc (-(ρ : ℤ)) ρ := by
    intro k hk
    rw [Finset.mem_Icc, ← abs_le]
    exact (Finset.mem_filter.1 hk).2
  have hinj : Set.InjOn (fun k : ℕ => x j - segPoint u j σ k j)
      ((Finset.range N).filter (fun k => |x j - segPoint u j σ k j| ≤ ρ)) := by
    intro k₁ _ k₂ _ h
    simp only [segPoint_apply_self] at h
    rcases hσ with rfl | rfl <;> omega
  have hc := Finset.card_le_card_of_injOn _ hmap hinj
  rw [Int.card_Icc] at hc
  omega

/-! ### The growth estimate -/

theorem sqrt_four_card_cubeRegion_le {ω : Configuration 2} {s : ℕ} {y : Vertex 2}
    (hy : 3 ^ (planarPartCube ω y).scale ≤ s) :
    Real.sqrt (4 * (cubeRegion ω y).card) ≤ 18 * s := by
  rw [card_cubeRegion]
  have h : (4 * ((9 * 3 ^ (planarPartCube ω y).scale) ^ 2 : ℕ) : ℝ) ≤ (18 * s) ^ 2 := by
    have : ((3 ^ (planarPartCube ω y).scale : ℕ) : ℝ) ≤ s := by exact_mod_cast hy
    push_cast at this ⊢
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (planarPartCube ω y).scale]
  calc Real.sqrt (4 * ((9 * 3 ^ (planarPartCube ω y).scale) ^ 2 : ℕ))
      ≤ Real.sqrt ((18 * s) ^ 2) := Real.sqrt_le_sqrt (by exact_mod_cast h)
    _ = 18 * s := Real.sqrt_sq (by positivity)

/-- **Growth along a segment**: if the partition cubes of the points of a segment of `n` steps
have side at most `s`, the coarsened function changes along it by at most
`144 s^{3/2} (n + 1)^{1/2} E^{1/2}`. -/
theorem abs_coarseAnchor_segment_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {W : Vertex 2 → ℝ} {E : ℝ} (hE : ∀ F : Finset (Vertex 2), localEnergy ω F W ≤ E) {s : ℕ}
    (u : Vertex 2) (j : Fin 2) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (n : ℕ)
    (hs : ∀ k ≤ n, 3 ^ (planarPartCube ω (segPoint u j σ k)).scale ≤ s) :
    |W (planarCoarseAnchor ω (segPoint u j σ n)) - W (planarCoarseAnchor ω (segPoint u j σ 0))| ≤
      144 * s * Real.sqrt s * Real.sqrt (n + 1) * Real.sqrt E := by
  set S : ℕ → Finset (Vertex 2) := fun k => cubeRegion ω (segPoint u j σ k) with hS
  set Ek : ℕ → ℝ := fun k => localEnergy ω (S k) W with hEk
  have hE0 : 0 ≤ E := (localEnergy_nonneg ω ∅ W).trans (hE ∅)
  have hchain := abs_coarseAnchor_chain_le hP (segPoint u j σ) W n
    (fun k _ i => abs_segPoint_step_le u j hσ k i)
  have hTV : ∀ k ∈ Finset.range (n + 1),
      edgeVariationIn ω (S k) W ≤ 18 * s * Real.sqrt (Ek k) := by
    intro k hk
    refine (edgeVariationIn_le ω (S k) W).trans ?_
    exact mul_le_mul_of_nonneg_right
      (sqrt_four_card_cubeRegion_le (hs k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))))
      (Real.sqrt_nonneg _)
  have hmult : ∀ x, ((Finset.range (n + 1)).filter fun k => x ∈ S k).card ≤ 10 * s + 1 := by
    intro x
    refine (Finset.card_le_card ?_).trans
      ((card_filter_segPoint_le u j hσ (n + 1) x (5 * s)).trans (by omega))
    intro k hk
    obtain ⟨hk, hxk⟩ := Finset.mem_filter.1 hk
    refine Finset.mem_filter.2 ⟨hk, ?_⟩
    have h1 := abs_sub_le_of_mem_cubeRegion hP hxk j
    have h2 : (3 : ℤ) ^ (planarPartCube ω (segPoint u j σ k)).scale ≤ s := by
      exact_mod_cast hs k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    push_cast
    linarith
  have hsumE := sum_localEnergy_le ω hE S (n + 1) (10 * s + 1) hmult
  have hsqrt : ∑ k ∈ Finset.range (n + 1), Real.sqrt (Ek k) ≤
      Real.sqrt (n + 1) * Real.sqrt (∑ k ∈ Finset.range (n + 1), Ek k) := by
    have h := Real.sum_sqrt_mul_sqrt_le (Finset.range (n + 1)) (f := fun _ => (1 : ℝ))
      (g := Ek) (fun _ => zero_le_one) (fun k => localEnergy_nonneg ω _ W)
    simp only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at h
    push_cast at h
    exact h
  have hs1 : (1 : ℝ) ≤ s := by
    have := hs 0 (Nat.zero_le _)
    have h3 : 1 ≤ 3 ^ (planarPartCube ω (segPoint u j σ 0)).scale :=
      Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast h3.trans this
  have hbound : Real.sqrt (∑ k ∈ Finset.range (n + 1), Ek k) ≤ 4 * Real.sqrt s * Real.sqrt E := by
    have h11 : ((10 * s + 1 : ℕ) : ℝ) * E ≤ (4 * Real.sqrt s * Real.sqrt E) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hE0]
      push_cast
      nlinarith
    calc Real.sqrt (∑ k ∈ Finset.range (n + 1), Ek k)
        ≤ Real.sqrt ((4 * Real.sqrt s * Real.sqrt E) ^ 2) :=
          Real.sqrt_le_sqrt (hsumE.trans h11)
      _ = 4 * Real.sqrt s * Real.sqrt E := Real.sqrt_sq (by positivity)
  calc |W (planarCoarseAnchor ω (segPoint u j σ n)) -
        W (planarCoarseAnchor ω (segPoint u j σ 0))|
      ≤ 2 * ∑ k ∈ Finset.range (n + 1), edgeVariationIn ω (S k) W := hchain
    _ ≤ 2 * ∑ k ∈ Finset.range (n + 1), 18 * s * Real.sqrt (Ek k) := by
        gcongr with k hk
        exact hTV k hk
    _ = 36 * s * ∑ k ∈ Finset.range (n + 1), Real.sqrt (Ek k) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 36 * s * (Real.sqrt (n + 1) * (4 * Real.sqrt s * Real.sqrt E)) := by
        gcongr
        exact hsqrt.trans (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _))
    _ = 144 * s * Real.sqrt s * Real.sqrt (n + 1) * Real.sqrt E := by ring

/-- **Sublinear growth of finite-energy functions, deterministic form**: if every partition cube of
a point of the square `|y|_∞ ≤ R` has side at most `s` and `W` has energy at most `E` on every
finite set, then every vertex `z` of the square in an infinite open cluster satisfies
`|W(z) - W([0]_𝒫)| ≤ 400 s^{3/2} (R + 1)^{1/2} E^{1/2}`. -/
theorem abs_sub_coarseAnchor_zero_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {W : Vertex 2 → ℝ} {E : ℝ} (hE : ∀ F : Finset (Vertex 2), localEnergy ω F W ≤ E) {R s : ℕ}
    (hs : ∀ y : Vertex 2, (∀ i, |y i| ≤ R) → 3 ^ (planarPartCube ω y).scale ≤ s)
    {z : Vertex 2} (hz : ∀ i, |z i| ≤ R)
    (hinf : ((openGraph ω).connectedComponentMk z).supp.Infinite) :
    |W z - W (planarCoarseAnchor ω 0)| ≤
      400 * s * Real.sqrt s * Real.sqrt (R + 1) * Real.sqrt E := by
  have hs1 : (1 : ℝ) ≤ s := by
    have := hs 0 (fun i => by simp)
    have h3 : 1 ≤ 3 ^ (planarPartCube ω 0).scale := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast h3.trans this
  set σ₀ : ℤ := if z 0 < 0 then -1 else 1 with hσ₀
  set σ₁ : ℤ := if z 1 < 0 then -1 else 1 with hσ₁
  have hσ₀' : σ₀ = 1 ∨ σ₀ = -1 := by rw [hσ₀]; split_ifs <;> simp
  have hσ₁' : σ₁ = 1 ∨ σ₁ = -1 := by rw [hσ₁]; split_ifs <;> simp
  have hn₀ : σ₀ * ((z 0).natAbs : ℤ) = z 0 := by rw [hσ₀]; split_ifs <;> omega
  have hn₁ : σ₁ * ((z 1).natAbs : ℤ) = z 1 := by rw [hσ₁]; split_ifs <;> omega
  have hn₀' : σ₀ * |z 0| = z 0 := by rw [← Int.natCast_natAbs]; exact hn₀
  have hn₁' : σ₁ * |z 1| = z 1 := by rw [← Int.natCast_natAbs]; exact hn₁
  set m : Vertex 2 := segPoint 0 0 σ₀ (z 0).natAbs with hm
  have hm0 : m 0 = z 0 := by simp [hm, segPoint, hn₀']
  have hm1 : m 1 = 0 := by simp [hm, segPoint]
  have hend : segPoint m 1 σ₁ (z 1).natAbs = z := by
    funext i
    fin_cases i
    · simp [segPoint, hm0]
    · simp [segPoint, hm1, hn₁']
  have hR0 : ((z 0).natAbs : ℝ) ≤ R := by
    have := abs_le.1 (hz 0)
    have : ((z 0).natAbs : ℤ) ≤ R := by omega
    exact_mod_cast this
  have hR1 : ((z 1).natAbs : ℝ) ≤ R := by
    have := abs_le.1 (hz 1)
    have : ((z 1).natAbs : ℤ) ≤ R := by omega
    exact_mod_cast this
  have habs₀ : |σ₀| = 1 := by rcases hσ₀' with h | h <;> simp [h]
  have habs₁ : |σ₁| = 1 := by rcases hσ₁' with h | h <;> simp [h]
  have hk0 : ∀ k ≤ (z 0).natAbs, (k : ℤ) ≤ R := by
    intro k hk
    have := abs_le.1 (hz 0)
    omega
  have hk1 : ∀ k ≤ (z 1).natAbs, (k : ℤ) ≤ R := by
    intro k hk
    have := abs_le.1 (hz 1)
    omega
  have hseg0 : ∀ k ≤ (z 0).natAbs, 3 ^ (planarPartCube ω (segPoint 0 0 σ₀ k)).scale ≤ s := by
    intro k hk
    refine hs _ fun i => ?_
    unfold segPoint
    split_ifs
    · rw [Pi.zero_apply, zero_add, abs_mul, habs₀, one_mul, Nat.abs_cast]
      exact hk0 k hk
    · simp
  have hseg1 : ∀ k ≤ (z 1).natAbs, 3 ^ (planarPartCube ω (segPoint m 1 σ₁ k)).scale ≤ s := by
    intro k hk
    refine hs _ fun i => ?_
    unfold segPoint
    split_ifs with hi
    · subst hi
      rw [hm1, zero_add, abs_mul, habs₁, one_mul, Nat.abs_cast]
      exact hk1 k hk
    · have hi0 : i = 0 := by fin_cases i <;> simp_all
      subst hi0
      rw [hm0]
      exact hz 0
  have hA := abs_coarseAnchor_segment_le hP hE 0 0 hσ₀' (z 0).natAbs hseg0
  have hB := abs_coarseAnchor_segment_le hP hE m 1 hσ₁' (z 1).natAbs hseg1
  rw [segPoint_zero] at hA hB
  rw [← hm] at hA
  rw [hend] at hB
  have hC := abs_sub_coarseAnchor_le hP hinf W
  have hzs := hs z hz
  have hTVz : edgeVariationIn ω (cubeRegion ω z) W ≤ 18 * s * Real.sqrt E :=
    (edgeVariationIn_le ω _ W).trans (mul_le_mul (sqrt_four_card_cubeRegion_le hzs)
      (Real.sqrt_le_sqrt (hE _)) (Real.sqrt_nonneg _) (by positivity))
  have hsq0 : Real.sqrt ((z 0).natAbs + 1) ≤ Real.sqrt (R + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsq1 : Real.sqrt ((z 1).natAbs + 1) ≤ Real.sqrt (R + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hss : 1 ≤ Real.sqrt s := by rw [Real.one_le_sqrt]; exact hs1
  have hsR : 1 ≤ Real.sqrt (R + 1) := by
    rw [Real.one_le_sqrt]
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  have hsqE := Real.sqrt_nonneg E
  have key1 : 144 * s * Real.sqrt s * Real.sqrt ((z 0).natAbs + 1) * Real.sqrt E ≤
      144 * s * Real.sqrt s * Real.sqrt (R + 1) * Real.sqrt E := by
    gcongr
  have key2 : 144 * s * Real.sqrt s * Real.sqrt ((z 1).natAbs + 1) * Real.sqrt E ≤
      144 * s * Real.sqrt s * Real.sqrt (R + 1) * Real.sqrt E := by
    gcongr
  have key3 : 18 * s * Real.sqrt E ≤ 18 * s * Real.sqrt s * Real.sqrt (R + 1) * Real.sqrt E := by
    calc 18 * (s : ℝ) * Real.sqrt E = 18 * ((s : ℝ) * 1 * 1) * Real.sqrt E := by ring
      _ ≤ 18 * ((s : ℝ) * Real.sqrt s * Real.sqrt (R + 1)) * Real.sqrt E := by gcongr
      _ = 18 * s * Real.sqrt s * Real.sqrt (R + 1) * Real.sqrt E := by ring
  have htri : |W z - W (planarCoarseAnchor ω 0)| ≤
      |W z - W (planarCoarseAnchor ω z)| +
        |W (planarCoarseAnchor ω z) - W (planarCoarseAnchor ω m)| +
          |W (planarCoarseAnchor ω m) - W (planarCoarseAnchor ω 0)| := by
    have h1 := abs_sub_le (W z) (W (planarCoarseAnchor ω z)) (W (planarCoarseAnchor ω 0))
    have h2 := abs_sub_le (W (planarCoarseAnchor ω z)) (W (planarCoarseAnchor ω m))
      (W (planarCoarseAnchor ω 0))
    linarith
  unfold cubeRegion at hTVz
  have hX : 0 ≤ (s : ℝ) * Real.sqrt s * Real.sqrt (R + 1) * Real.sqrt E := by positivity
  linarith

end Rigidity.Corrector

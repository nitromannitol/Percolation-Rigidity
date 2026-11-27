import Rigidity.Proofs.Corrector.GeneralStepOneLocal
import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralScaleForms

/-!
# Growth of functions of finite energy on the infinite cluster of `ℤᵈ`

In the proof of Lemma 3.3, Case 3 of Step 2, Dario asserts that the function
`χ_p - χ_p^e - c ∇G(e, ·)` has sublinear growth, "by the sublinear growth of the corrector, the
`L²` bound (2.14) on `∇∇G(e, ·)` and a version of the Poincaré inequality on the cluster", and
concludes by the Liouville theorem. The missing ingredient is the sublinear growth of a function
`W` of finite energy on the infinite cluster. This is the argument of the planar file
`DarioFiniteEnergyGrowth` for the partition into good cubes of `ℤᵈ`:

* `abs_partitionAnchor_sub_le_of_adj` (in `GeneralStepOneLocal`): the anchors of the partition cubes of lattice neighbours are
  joined inside the union of the two cubes (Armstrong and Dario, Corollary 2.10,
  `reachable_partitionAnchor_of_adj`), so `W` changes between them by at most its total variation
  over the box of radius `s` around the first point, `s` bounding the sides of the two cubes;
* `abs_partitionAnchor_segment_le`: along a straight segment of `n` steps whose points have
  partition cubes of side at most `s`, the change of `W` at the anchors is at most
  `(2d (2s + 1)^d)^{1/2} n^{1/2} ((2s + 1) E)^{1/2}`, where `E` bounds the energy of `W` on every
  finite set (each point lies in at most `2s + 1` of the boxes);
* `sq_abs_sub_partitionAnchor_zero_le`: if the partition cubes of the points of the box
  `|y|_∞ ≤ R` have side at most `s ≥ 1`, then every vertex `z` of the box in an infinite open
  cluster satisfies `|W(z) - W(a_𝒫(0))|² ≤ K_d s^{d+1} R E`, by `d` segments along the coordinate
  axes and the path from `z` to its anchor inside `anchorBox`;
* `ae_abs_sub_partitionAnchor_le_of_finiteEnergy`: with the minimal scales of the partition
  (Armstrong and Dario, Proposition 2.4, `cubeMinimalScales_holds`), almost surely
  `|W(z) - W(a_𝒫(0))| ≤ ε R` for `|z|_∞ ≤ R` large, for every `W` of finite energy.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

variable {d : ℕ}

/-- The energy `Σ_{x, y ∈ S, x ∼ y open} (W(x) - W(y))²` of `W` inside a finite set, each open edge
counted in both orientations. -/
noncomputable def localEnergy (ω : Configuration d) (S : Finset (Vertex d)) (W : Vertex d → ℝ) :
    ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, if (openGraph ω).Adj x y then (W x - W y) ^ 2 else 0

theorem localEnergy_nonneg (ω : Configuration d) (S : Finset (Vertex d)) (W : Vertex d → ℝ) :
    0 ≤ localEnergy ω S W :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem sum_adj_le_two_mul (ω : Configuration d) (S : Finset (Vertex d)) (x : Vertex d) :
    (∑ y ∈ S, if (openGraph ω).Adj x y then (1 : ℝ) else 0) ≤ 2 * d := by
  rw [Finset.sum_boole]
  exact_mod_cast card_filter_adj_le ω S x

/-- **Total variation by energy**: `TV_S(W) ≤ (2d |S|)^{1/2} E_S(W)^{1/2}`. -/
theorem edgeVariationIn_le_sqrt (ω : Configuration d) (S : Finset (Vertex d)) (W : Vertex d → ℝ) :
    edgeVariationIn ω S W ≤ Real.sqrt (2 * d * S.card) * Real.sqrt (localEnergy ω S W) := by
  set f : Vertex d × Vertex d → ℝ := fun q => if (openGraph ω).Adj q.1 q.2 then 1 else 0
  set g : Vertex d × Vertex d → ℝ := fun q =>
    if (openGraph ω).Adj q.1 q.2 then |W q.1 - W q.2| else 0
  have h1 : edgeVariationIn ω S W = ∑ q ∈ S ×ˢ S, f q * g q := by
    unfold edgeVariationIn
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [f, g]
    split_ifs <;> simp
  have h2 : ∑ q ∈ S ×ˢ S, f q ^ 2 ≤ 2 * d * S.card := by
    rw [Finset.sum_product]
    calc ∑ x ∈ S, ∑ y ∈ S, f (x, y) ^ 2
        = ∑ x ∈ S, ∑ y ∈ S, (if (openGraph ω).Adj x y then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          simp only [f]
          split_ifs <;> simp
      _ ≤ ∑ _x ∈ S, (2 * d : ℝ) := Finset.sum_le_sum fun x _ => sum_adj_le_two_mul ω S x
      _ = 2 * d * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
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
theorem sum_localEnergy_le (ω : Configuration d) {W : Vertex d → ℝ} {E : ℝ}
    (hE : ∀ F : Finset (Vertex d), localEnergy ω F W ≤ E) (S : ℕ → Finset (Vertex d)) (n M : ℕ)
    (hM : ∀ x, ((Finset.range n).filter fun k => x ∈ S k).card ≤ M) :
    ∑ k ∈ Finset.range n, localEnergy ω (S k) W ≤ M * E := by
  set U := (Finset.range n).biUnion S with hU
  set e : Vertex d → ℝ := fun x =>
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

/-! ### Anchors of neighbouring points -/

/-- Along a chain of lattice neighbours whose partition cubes have side at most `s`, `W` changes at
the anchors by at most the sum of its total variations over the boxes of radius `s`. -/
theorem abs_partitionAnchor_chain_le (hd : 0 < d) {ω : Configuration d} (hP : PartitionEvent ω)
    (z : ℕ → Vertex d) (W : Vertex d → ℝ) (n s : ℕ)
    (hstep : ∀ k < n, (nearestNeighborGraph d).Adj (z k) (z (k + 1)))
    (hs : ∀ k ≤ n, 3 ^ (partitionCube ω (z k)).scale ≤ s) :
    |W (partitionAnchor ω (z n)) - W (partitionAnchor ω (z 0))| ≤
      ∑ k ∈ Finset.range n, edgeVariationIn ω (LatticeProb.boxFinset (z k) s) W := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun k hk => hstep k (by omega)) (fun k hk => hs k (by omega))
    have hst := abs_partitionAnchor_sub_le_of_adj hd hP (hstep n (by omega)) (hs n (by omega))
      (hs (n + 1) le_rfl) W
    have htri := abs_sub_le (W (partitionAnchor ω (z (n + 1))))
      (W (partitionAnchor ω (z n))) (W (partitionAnchor ω (z 0)))
    rw [abs_sub_comm] at hst
    rw [Finset.sum_range_succ]
    linarith

/-! ### Straight segments -/

/-- The point `u + σ k e_j`. -/
def segPoint (u : Vertex d) (j : Fin d) (σ : ℤ) (k : ℕ) : Vertex d :=
  fun i => if i = j then u i + σ * k else u i

theorem segPoint_apply_self (u : Vertex d) (j : Fin d) (σ : ℤ) (k : ℕ) :
    segPoint u j σ k j = u j + σ * k := by
  simp [segPoint]

theorem segPoint_zero (u : Vertex d) (j : Fin d) (σ : ℤ) : segPoint u j σ 0 = u := by
  funext i
  unfold segPoint
  split_ifs <;> simp

theorem adj_segPoint_succ (u : Vertex d) (j : Fin d) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (k : ℕ) :
    (nearestNeighborGraph d).Adj (segPoint u j σ k) (segPoint u j σ (k + 1)) := by
  refine LatticeProb.Graph.Zd.adj_iff.2 ⟨j, ?_⟩
  rcases hσ with rfl | rfl
  · left
    funext i
    simp only [segPoint, Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
  · right
    funext i
    simp only [segPoint, Pi.sub_apply, LatticeProb.unit, Pi.single_apply]
    split_ifs <;> push_cast <;> ring

/-- A segment meets the slab `|x_j - y_j| ≤ ρ` in at most `2ρ + 1` points. -/
theorem card_filter_segPoint_le (u : Vertex d) (j : Fin d) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (N : ℕ) (x : Vertex d) (ρ : ℕ) :
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

theorem card_boxFinset_eq (x : Vertex d) (r : ℕ) :
    (LatticeProb.boxFinset x r).card = (2 * r + 1) ^ d := by
  rw [LatticeProb.boxFinset, Fintype.card_piFinset]
  have hfac : ∀ i : Fin d, (Finset.Icc (x i - r) (x i + r)).card = 2 * r + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **Growth along a segment**: if the partition cubes of the points of a segment of `n` steps
have side at most `s`, the function changes at the anchors along it by at most
`(2d (2s + 1)^d)^{1/2} n^{1/2} ((2s + 1) E)^{1/2}`. -/
theorem abs_partitionAnchor_segment_le (hd : 0 < d) {ω : Configuration d} (hP : PartitionEvent ω)
    {W : Vertex d → ℝ} {E : ℝ} (hE : ∀ F : Finset (Vertex d), localEnergy ω F W ≤ E) {s : ℕ}
    (u : Vertex d) (j : Fin d) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (n : ℕ)
    (hs : ∀ k ≤ n, 3 ^ (partitionCube ω (segPoint u j σ k)).scale ≤ s) :
    |W (partitionAnchor ω (segPoint u j σ n)) - W (partitionAnchor ω (segPoint u j σ 0))| ≤
      Real.sqrt (2 * d * (2 * s + 1) ^ d) * Real.sqrt n * Real.sqrt ((2 * s + 1) * E) := by
  have hchain := abs_partitionAnchor_chain_le hd hP (segPoint u j σ) W n s
    (fun k _ => adj_segPoint_succ u j hσ k) hs
  have hc : ∀ k, ((LatticeProb.boxFinset (segPoint u j σ k) s).card : ℝ) = (2 * s + 1) ^ d :=
    fun k => by exact_mod_cast card_boxFinset_eq (segPoint u j σ k) s
  have hTV : ∀ k ∈ Finset.range n,
      edgeVariationIn ω (LatticeProb.boxFinset (segPoint u j σ k) s) W ≤
        Real.sqrt (2 * d * (2 * s + 1) ^ d) *
          Real.sqrt (localEnergy ω (LatticeProb.boxFinset (segPoint u j σ k) s) W) := by
    intro k _
    have h := edgeVariationIn_le_sqrt ω (LatticeProb.boxFinset (segPoint u j σ k) s) W
    rwa [hc k] at h
  have hmult : ∀ x, ((Finset.range n).filter fun k =>
      x ∈ LatticeProb.boxFinset (segPoint u j σ k) s).card ≤ 2 * s + 1 := by
    intro x
    refine (Finset.card_le_card ?_).trans (card_filter_segPoint_le u j hσ n x s)
    intro k hk
    obtain ⟨hk, hxk⟩ := Finset.mem_filter.1 hk
    refine Finset.mem_filter.2 ⟨hk, ?_⟩
    exact (LatticeProb.mem_boxFinset_iff.1 hxk) j
  have hsumE := sum_localEnergy_le ω hE (fun k => LatticeProb.boxFinset (segPoint u j σ k) s) n
    (2 * s + 1) hmult
  have hsqrt : ∑ k ∈ Finset.range n,
      Real.sqrt (localEnergy ω (LatticeProb.boxFinset (segPoint u j σ k) s) W) ≤
      Real.sqrt n * Real.sqrt (∑ k ∈ Finset.range n,
        localEnergy ω (LatticeProb.boxFinset (segPoint u j σ k) s) W) := by
    have h := Real.sum_sqrt_mul_sqrt_le (Finset.range n) (f := fun _ => (1 : ℝ))
      (g := fun k => localEnergy ω (LatticeProb.boxFinset (segPoint u j σ k) s) W)
      (fun _ => zero_le_one) (fun k => localEnergy_nonneg ω _ W)
    simp only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at h
    exact h
  have hbound : Real.sqrt (∑ k ∈ Finset.range n,
      localEnergy ω (LatticeProb.boxFinset (segPoint u j σ k) s) W) ≤
        Real.sqrt ((2 * s + 1) * E) :=
    Real.sqrt_le_sqrt (hsumE.trans (le_of_eq (by simp)))
  calc |W (partitionAnchor ω (segPoint u j σ n)) - W (partitionAnchor ω (segPoint u j σ 0))|
      ≤ ∑ k ∈ Finset.range n, edgeVariationIn ω (LatticeProb.boxFinset (segPoint u j σ k) s) W :=
        hchain
    _ ≤ ∑ k ∈ Finset.range n, Real.sqrt (2 * d * (2 * s + 1) ^ d) *
          Real.sqrt (localEnergy ω (LatticeProb.boxFinset (segPoint u j σ k) s) W) :=
        Finset.sum_le_sum hTV
    _ = Real.sqrt (2 * d * (2 * s + 1) ^ d) * ∑ k ∈ Finset.range n,
          Real.sqrt (localEnergy ω (LatticeProb.boxFinset (segPoint u j σ k) s) W) := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt (2 * d * (2 * s + 1) ^ d) * (Real.sqrt n * Real.sqrt ((2 * s + 1) * E)) := by
        gcongr
        exact hsqrt.trans (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _))
    _ = Real.sqrt (2 * d * (2 * s + 1) ^ d) * Real.sqrt n * Real.sqrt ((2 * s + 1) * E) := by
        ring

/-! ### The growth estimate -/

/-- The point with the first `m` coordinates of `z` and the others zero. -/
def stairPoint (z : Vertex d) (m : ℕ) : Vertex d :=
  fun i => if (i : ℕ) < m then z i else 0

theorem stairPoint_zero (z : Vertex d) : stairPoint z 0 = 0 := by
  funext i
  simp [stairPoint]

theorem stairPoint_dim (z : Vertex d) : stairPoint z d = z := by
  funext i
  simp [stairPoint, i.isLt]

/-- The sign of an integer, `-1` for the negative ones and `1` otherwise. -/
def sgn' (a : ℤ) : ℤ := if a < 0 then -1 else 1

theorem sgn'_cases (a : ℤ) : sgn' a = 1 ∨ sgn' a = -1 := by
  unfold sgn'
  split_ifs <;> simp

theorem sgn'_mul_natAbs (a : ℤ) : sgn' a * (a.natAbs : ℤ) = a := by
  unfold sgn'
  split_ifs <;> omega

theorem segPoint_stairPoint (z : Vertex d) {m : ℕ} (hm : m < d) :
    segPoint (stairPoint z m) ⟨m, hm⟩ (sgn' (z ⟨m, hm⟩)) (z ⟨m, hm⟩).natAbs =
      stairPoint z (m + 1) := by
  funext i
  have h := sgn'_mul_natAbs (z ⟨m, hm⟩)
  unfold segPoint stairPoint
  by_cases hi : i = ⟨m, hm⟩
  · subst hi
    simpa using h
  · have hi' : (i : ℕ) ≠ m := fun e => hi (Fin.ext e)
    rw [if_neg hi]
    by_cases hlt : (i : ℕ) < m
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

theorem abs_segPoint_stairPoint_le (z : Vertex d) {R : ℕ} (hz : ∀ i, |z i| ≤ R) {m : ℕ}
    (hm : m < d) {k : ℕ} (hk : k ≤ (z ⟨m, hm⟩).natAbs) (i : Fin d) :
    |segPoint (stairPoint z m) ⟨m, hm⟩ (sgn' (z ⟨m, hm⟩)) k i| ≤ R := by
  unfold segPoint stairPoint
  have hzm := abs_le.1 (hz ⟨m, hm⟩)
  split_ifs with h1 h2 h2
  · subst h1
    simp at h2
  · subst h1
    have hs := sgn'_cases (z ⟨m, hm⟩)
    rw [zero_add, abs_mul, Nat.abs_cast]
    rcases hs with hs | hs <;> rw [hs] <;> simp <;> omega
  · exact hz i
  · simp

/-- **Sublinear growth of finite-energy functions, deterministic form**: if every partition cube
of a point of the box `|y|_∞ ≤ R` has side at most `s` and `W` has energy at most `E` on every
finite set, then every vertex `z` of the box in an infinite open cluster satisfies
`|W(z) - W(a_𝒫(0))|² ≤ K_d s^{d+1} R E`, `K_d = 4d 7^d + 4d³ 3^{d+1}`. -/
theorem sq_abs_sub_partitionAnchor_zero_le (hd : 0 < d) {ω : Configuration d}
    (hP : PartitionEvent ω) {W : Vertex d → ℝ} {E : ℝ}
    (hE : ∀ F : Finset (Vertex d), localEnergy ω F W ≤ E) {R s : ℕ} (hR : 1 ≤ R)
    (hs : ∀ y : Vertex d, (∀ i, |y i| ≤ R) → 3 ^ (partitionCube ω y).scale ≤ s)
    {z : Vertex d} (hz : ∀ i, |z i| ≤ R) (hinf : ω ∈ infiniteComponentEvent z) :
    |W z - W (partitionAnchor ω 0)| ^ 2 ≤
      (4 * d * 7 ^ d + 4 * d ^ 3 * 3 ^ (d + 1)) * (s : ℝ) ^ (d + 1) * R * E := by
  have hE0 : 0 ≤ E := (localEnergy_nonneg ω ∅ W).trans (hE ∅)
  have hs1 : (1 : ℝ) ≤ s := by
    have := hs 0 (fun i => by simp)
    have h3 : 1 ≤ 3 ^ (partitionCube ω 0).scale := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast h3.trans this
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  -- the segment bound, uniform in the coordinate
  set B : ℝ := Real.sqrt (2 * d * (2 * s + 1) ^ d) * Real.sqrt R * Real.sqrt ((2 * s + 1) * E)
    with hB
  have hseg : ∀ m < d, |W (partitionAnchor ω (stairPoint z (m + 1))) -
      W (partitionAnchor ω (stairPoint z m))| ≤ B := by
    intro m hm
    have hk : ∀ k ≤ (z ⟨m, hm⟩).natAbs, 3 ^ (partitionCube ω
        (segPoint (stairPoint z m) ⟨m, hm⟩ (sgn' (z ⟨m, hm⟩)) k)).scale ≤ s :=
      fun k hk => hs _ (abs_segPoint_stairPoint_le z hz hm hk)
    have h := abs_partitionAnchor_segment_le hd hP hE (stairPoint z m) ⟨m, hm⟩
      (sgn'_cases _) _ hk
    rw [segPoint_stairPoint z hm, segPoint_zero] at h
    refine h.trans ?_
    have hn : ((z ⟨m, hm⟩).natAbs : ℝ) ≤ R := by
      have := abs_le.1 (hz ⟨m, hm⟩)
      have : ((z ⟨m, hm⟩).natAbs : ℤ) ≤ R := by omega
      exact_mod_cast this
    rw [hB]
    gcongr
  have hstair : ∀ m ≤ d, |W (partitionAnchor ω (stairPoint z m)) -
      W (partitionAnchor ω 0)| ≤ m * B := by
    intro m
    induction m with
    | zero => intro _; simp [stairPoint_zero]
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hseg m (by omega)
      have htri := abs_sub_le (W (partitionAnchor ω (stairPoint z (m + 1))))
        (W (partitionAnchor ω (stairPoint z m))) (W (partitionAnchor ω 0))
      have e : ((m + 1 : ℕ) : ℝ) * B = m * B + B := by push_cast; ring
      rw [e]
      linarith
  have hA := hstair d le_rfl
  rw [stairPoint_dim] at hA
  -- from `z` to its anchor
  have hzs := hs z hz
  have hbox : (anchorBox ω z).card ≤ (6 * s + 1) ^ d := by
    rw [anchorBox, card_boxFinset_eq]
    have : 3 ^ ((partitionCube ω z).scale + 1) ≤ 3 * s := by rw [pow_succ]; omega
    exact Nat.pow_le_pow_left (by omega) d
  have hC : |W z - W (partitionAnchor ω z)| ≤
      Real.sqrt (2 * d * (6 * s + 1) ^ d) * Real.sqrt E := by
    refine (abs_sub_le_edgeVariationIn_of_reachable _ W
      (reachable_anchorBox hd hP hinf)).trans ?_
    refine (edgeVariationIn_le_sqrt ω _ W).trans ?_
    refine mul_le_mul (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by exact_mod_cast hbox)
      (by positivity))) (Real.sqrt_le_sqrt (hE _)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have htri := abs_sub_le (W z) (W (partitionAnchor ω z)) (W (partitionAnchor ω 0))
  have hsum : |W z - W (partitionAnchor ω 0)| ≤
      Real.sqrt (2 * d * (6 * s + 1) ^ d) * Real.sqrt E + d * B := by linarith
  have h0 : 0 ≤ |W z - W (partitionAnchor ω 0)| := abs_nonneg _
  -- squares
  have hsq1 : (Real.sqrt (2 * d * (6 * s + 1) ^ d) * Real.sqrt E) ^ 2 =
      2 * d * (6 * s + 1) ^ d * E := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hE0]
  have hsq2 : B ^ 2 = 2 * d * (2 * s + 1) ^ d * R * ((2 * s + 1) * E) := by
    rw [hB, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
  have h7 : (6 * (s : ℝ) + 1) ^ d ≤ 7 ^ d * (s : ℝ) ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have h3 : (2 * (s : ℝ) + 1) ^ d ≤ 3 ^ d * (s : ℝ) ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hsd : (s : ℝ) ^ d ≤ (s : ℝ) ^ (d + 1) := pow_le_pow_right₀ hs1 (by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hX : 0 ≤ (s : ℝ) ^ d := by positivity
  calc |W z - W (partitionAnchor ω 0)| ^ 2
      ≤ (Real.sqrt (2 * d * (6 * s + 1) ^ d) * Real.sqrt E + d * B) ^ 2 :=
        pow_le_pow_left₀ h0 hsum 2
    _ ≤ 2 * (Real.sqrt (2 * d * (6 * s + 1) ^ d) * Real.sqrt E) ^ 2 + 2 * (d * B) ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt (2 * d * (6 * s + 1) ^ d) * Real.sqrt E - d * B)]
    _ = 4 * d * (6 * s + 1) ^ d * E + 4 * d ^ 3 * (2 * s + 1) ^ (d + 1) * R * E := by
        rw [hsq1, mul_pow, hsq2]
        ring
    _ ≤ 4 * d * (7 ^ d * (s : ℝ) ^ (d + 1)) * R * E +
        4 * d ^ 3 * (3 ^ (d + 1) * (s : ℝ) ^ (d + 1)) * R * E := by
        have e1 : (6 * (s : ℝ) + 1) ^ d * E ≤ 7 ^ d * (s : ℝ) ^ (d + 1) * R * E := by
          have a1 : (6 * (s : ℝ) + 1) ^ d ≤ 7 ^ d * (s : ℝ) ^ (d + 1) * R := by
            calc (6 * (s : ℝ) + 1) ^ d ≤ 7 ^ d * (s : ℝ) ^ d := h7
              _ ≤ 7 ^ d * (s : ℝ) ^ (d + 1) := mul_le_mul_of_nonneg_left hsd (by positivity)
              _ = 7 ^ d * (s : ℝ) ^ (d + 1) * 1 := (mul_one _).symm
              _ ≤ 7 ^ d * (s : ℝ) ^ (d + 1) * R :=
                  mul_le_mul_of_nonneg_left hR1 (by positivity)
          exact mul_le_mul_of_nonneg_right a1 hE0
        have e3 : (2 * (s : ℝ) + 1) ^ (d + 1) * R * E ≤
            3 ^ (d + 1) * (s : ℝ) ^ (d + 1) * R * E := by
          have a3 : (2 * (s : ℝ) + 1) ^ (d + 1) ≤ 3 ^ (d + 1) * (s : ℝ) ^ (d + 1) := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) (by linarith) _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right a3 (by positivity)) hE0
        have f1 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 4 * d)
        have f3 := mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ 4 * d ^ 3)
        linarith
    _ = (4 * d * 7 ^ d + 4 * d ^ 3 * 3 ^ (d + 1)) * (s : ℝ) ^ (d + 1) * R * E := by ring

/-! ### The almost sure growth -/

/-- The box `|y|_∞ ≤ R` lies in the triadic cube of scale `m` centred at the origin when
`2R + 1 ≤ 3^m`. -/
theorem mem_triadicCube_zero_of_abs_le {m R : ℕ} (hR : 2 * R + 1 ≤ 3 ^ m) {y : Vertex d}
    (hy : ∀ i, |y i| ≤ R) : y ∈ (⟨m, 0⟩ : TriadicCube d).vertices := by
  intro i
  obtain ⟨h1, h2⟩ := abs_le.1 (hy i)
  have hR' : (2 * R + 1 : ℤ) ≤ 3 ^ m := by exact_mod_cast hR
  show |2 * (y i - (3 : ℤ) ^ m * 0)| < (3 : ℤ) ^ m
  rw [mul_zero, sub_zero, abs_lt]
  constructor <;> linarith

/-- The numerical step: if `S⁴ ≤ 9R`, `R ≥ 1` and `R > 9 (K E)⁴ / ε⁸`, then `K S R E ≤ (ε R)²`. -/
theorem growth_bound_le' {S R K E ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) (hS4 : S ^ 4 ≤ 9 * R) (hRC : 9 * (K * E) ^ 4 / ε ^ 8 < R) :
    K * S * R * E ≤ (ε * R) ^ 2 := by
  have hR0 : 0 < R := by linarith
  have h8 : 0 < ε ^ 8 := by positivity
  have h1 : 9 * (K * E) ^ 4 < ε ^ 8 * R := by
    rw [div_lt_iff₀ h8] at hRC
    linarith
  have h2 : (K * E * S) ^ 4 ≤ (ε ^ 2 * R) ^ 4 := by
    have hpow : (K * E * S) ^ 4 = (K * E) ^ 4 * S ^ 4 := by ring
    have hKE4 : 0 ≤ (K * E) ^ 4 := by positivity
    calc (K * E * S) ^ 4 = (K * E) ^ 4 * S ^ 4 := hpow
      _ ≤ (K * E) ^ 4 * (9 * R) := mul_le_mul_of_nonneg_left hS4 hKE4
      _ = 9 * (K * E) ^ 4 * R := by ring
      _ ≤ ε ^ 8 * R * R := by nlinarith
      _ ≤ ε ^ 8 * R * R * (R * R) := by
          have : 1 ≤ R * R := by nlinarith
          have h0 : 0 ≤ ε ^ 8 * R * R := by positivity
          nlinarith
      _ = (ε ^ 2 * R) ^ 4 := by ring
  have h3 : K * E * S ≤ ε ^ 2 * R :=
    le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h2
  have h4 : K * S * R * E = (K * E * S) * R := by ring
  rw [h4]
  calc (K * E * S) * R ≤ (ε ^ 2 * R) * R := mul_le_mul_of_nonneg_right h3 hR0.le
    _ = (ε * R) ^ 2 := by ring

/-- **Sublinear growth of functions of finite energy on the infinite cluster of `ℤᵈ`**: almost
surely, for every `W` whose energy on every finite set is at most `E` and every `ε > 0`, there is
`R₀` such that `|W(z) - W(a_𝒫(0))| ≤ ε R` for every `R ≥ R₀` and every vertex `z` with
`|z|_∞ ≤ R` in an infinite open cluster. -/
theorem ae_abs_sub_partitionAnchor_le_of_finiteEnergy [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (W : Vertex d → ℝ) (E : ℝ),
      (∀ F : Finset (Vertex d), localEnergy ω F W ≤ E) →
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ z : Vertex d, (∀ i, |z i| ≤ R) →
        ω ∈ infiniteComponentEvent z → |W z - W (partitionAnchor ω 0)| ≤ ε * R := by
  have hd0 : 0 < d := by omega
  set D : ℕ := 4 * (d + 1) with hD
  have ht : (1 : ℝ) ≤ (4 * (d + 1) * d - d : ℝ) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    nlinarith
  obtain ⟨_, _, -, -, M, -, -, -, hae⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc _ ht
  filter_upwards [hae, ae_partitionEvent hd hpc] with ω hω hP
  intro W E hE ε hε
  have hE0 : 0 ≤ E := (localEnergy_nonneg ω ∅ W).trans (hE ∅)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * d * 7 ^ d + 4 * d ^ 3 * 3 ^ (d + 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (M ω) (by norm_num : (1 : ℝ) < 3)
  obtain ⟨R₁, hR₁⟩ := exists_nat_gt (9 * (K * E) ^ 4 / ε ^ 8)
  refine ⟨max (max (3 ^ m₀) 1) R₁, fun R hR z hz hinf => ?_⟩
  have hR3 : 3 ^ m₀ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR1 : 1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRR₁ : R₁ ≤ R := le_trans (le_max_right _ _) hR
  set m := Nat.clog 3 (2 * R + 1) with hmdef
  have hm1 : 2 * R + 1 ≤ 3 ^ m := Nat.le_pow_clog (by norm_num) _
  have hmpos : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, pow_zero] at hm1
    omega
  have hm2 : 3 ^ m ≤ 9 * R := by
    have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 3) (by omega : 1 < 2 * R + 1)
    rw [← hmdef] at h
    have h' : 3 ^ (m - 1) < 2 * R + 1 := by simpa [Nat.pred_eq_sub_one] using h
    have e : 3 ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hm₀m : 3 ^ m₀ ≤ 3 ^ m := by omega
  have hMm : M ω ≤ 3 ^ m := hm₀.le.trans (by exact_mod_cast hm₀m)
  obtain ⟨-, hsize⟩ := hω m hMm
  have hs : ∀ y : Vertex d, (∀ i, |y i| ≤ R) → 3 ^ (partitionCube ω y).scale ≤ 3 ^ (m / D) := by
    intro y hy
    have hb := hsize y (mem_triadicCube_zero_of_abs_le hm1 hy)
    have hexp : (d : ℝ) * m / (d + (4 * (d + 1) * d - d)) = (m : ℝ) / D := by
      have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      have hden : (d : ℝ) + (4 * (d + 1) * d - d) = d * (4 * (d + 1)) := by ring
      rw [hden, mul_div_mul_left _ _ hdne, hD]
      norm_num
    rw [hexp] at hb
    have hpow := pow_le_pow_left₀ (by positivity) hb D
    rw [← Real.rpow_natCast (((3 : ℝ) ^ ((m : ℝ) / D))) D, ← Real.rpow_mul (by positivity)] at hpow
    have hD0 : (D : ℝ) ≠ 0 := by rw [hD]; positivity
    rw [div_mul_cancel₀ _ hD0, Real.rpow_natCast, ← pow_mul] at hpow
    have hle : (partitionCube ω y).scale * D ≤ m :=
      (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hpow
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.le_div_iff_mul_le (by omega)).2 hle)
  have hbound := sq_abs_sub_partitionAnchor_zero_le hd0 hP hE hR1 hs hz hinf
  set s : ℕ := 3 ^ (m / D) with hsdef
  have hS4 : (((s : ℝ) ^ (d + 1)) ^ 4) ≤ 9 * (R : ℝ) := by
    have h1 : (s ^ (d + 1)) ^ 4 ≤ 3 ^ m := by
      rw [hsdef, ← pow_mul, ← pow_mul]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have e : (d + 1) * 4 = D := by rw [hD]; ring
      rw [e]
      exact Nat.div_mul_le_self m D
    have h2 : (s ^ (d + 1)) ^ 4 ≤ 9 * R := h1.trans hm2
    exact_mod_cast h2
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hRC : 9 * (K * E) ^ 4 / ε ^ 8 < (R : ℝ) :=
    lt_of_lt_of_le hR₁ (by exact_mod_cast hRR₁)
  have hfin := growth_bound_le' hRreal hε hS4 hRC
  rw [← hK] at hbound
  have hsq := hbound.trans hfin
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

end Rigidity.Corrector.GeneralDim

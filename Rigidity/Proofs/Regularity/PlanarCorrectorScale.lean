import Rigidity.Proofs.Regularity.PlanarCorrectorDensity

/-!
# The bounds on the corrector at one triadic scale

For the corrector `χ = u - q · x` of `u ∈ 𝒜_1(𝒞_∞)` and the box `{|z_i| ≤ 3N}`, `N = 3^m`:

* `abs_extend_sub_le_of_adj`: the increments of the extension of `χ` by zero along the open
  edges of the box are at most `C_L y³ |q|` when the minimal scales of the Lipschitz estimate at
  the vertices of the box are at most `y ≤ N/4` and `‖χ‖_{L̲²(𝒞_∞ ∩ B_N(a))} ≤ C_B |q| N` at these
  vertices (Armstrong and Dario, arXiv:1609.09431v2, Remark after (1.19), the bound on
  `|∇χ_p 1_{a≠0}|`);
* `componentBallL2_corrector_le`: that bound from (1.18) on `B_{6N}` and the density of the cluster
  in the balls `B_N(a)`;
* `sum_sq_extend_le`: the sum of the squares of the extension on the box from (1.18) on `B_{6N}`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.S2
open Rigidity.External
open scoped Classical

variable {ω : Configuration 2}

theorem extend_of_not_mem (C : OpenComponent ω) (f : C → ℝ) {x : Vertex 2} (hx : x ∉ C.supp) :
    Rigidity.Section3.extend C f x = 0 := by
  simp [Rigidity.Section3.extend, hx]

theorem extend_of_mem (C : OpenComponent ω) (f : C → ℝ) {x : Vertex 2} (hx : x ∈ C.supp) :
    Rigidity.Section3.extend C f x = f ⟨x, hx⟩ := by
  simp [Rigidity.Section3.extend, hx]

/-- Neighbours on the lattice are at Euclidean distance one. -/
theorem dist_le_one_of_lattice_adj {x y : Vertex 2} (h : (nearestNeighborGraph 2).Adj x y) :
    dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding x) ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [hi, EuclideanSpace.dist_eq, Fin.sum_univ_two]
    fin_cases i <;> simp [latticeEuclideanEmbedding, unit_apply_two]
  · rw [hi, EuclideanSpace.dist_eq, Fin.sum_univ_two]
    fin_cases i <;> simp [latticeEuclideanEmbedding, unit_apply_two]

theorem dist_zero_lt_of_abs_le {a : Vertex 2} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, |((a i : ℤ) : ℝ)| ≤ M) :
    dist (latticeEuclideanEmbedding a) (latticeEuclideanEmbedding (0 : Vertex 2)) ≤ 3 / 2 * M := by
  have h0 : ∀ i, |((a i : ℤ) : ℝ) - latticeEuclideanEmbedding (0 : Vertex 2) i| ≤ M := by
    intro i
    have e : latticeEuclideanEmbedding (0 : Vertex 2) i = 0 := by simp [latticeEuclideanEmbedding]
    rw [e, sub_zero]; exact ha i
  have hd := dist_latticeEuclideanEmbedding_le hM h0
  have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc _ ≤ Real.sqrt ((2 : ℕ) : ℝ) * M := hd
    _ ≤ 3 / 2 * M := mul_le_mul_of_nonneg_right hs hM

theorem cast_abs_le {a : ℤ} {n : ℕ} {c : ℕ} (h : |a| ≤ c * n) :
    |((a : ℤ) : ℝ)| ≤ c * (n : ℝ) := by
  have h' : ((|a| : ℤ) : ℝ) ≤ ((c * n : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

/-- **The normalized norm of the corrector on `B_N(a)`** from (1.18) on `B_{6N}` and the density
of the cluster in `B_N(a)`. -/
theorem componentBallL2_corrector_le (C : OpenComponent ω) {ℓ κ : ℝ} (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C 0 54 ℓ κ) {m : ℕ} (hm : ℓ ≤ 3 ^ m) (f : C → ℝ) {B : ℝ}
    (hB : componentBallL2 C 0 (6 * (9 * 3 ^ m)) f ≤ B) {a : C}
    (ha : ∀ i, |a.val i| ≤ 3 * (9 * 3 ^ m)) :
    componentBallL2 C a.val (9 * 3 ^ m) f ≤ Real.sqrt (18225 / κ) * B := by
  set N : ℝ := 9 * 3 ^ m with hN
  have hN0 : 0 < N := by positivity
  have hdens := card_componentEuclideanBall_ge C hcube hm (x := a.val) fun i => by
    have := ha i; linarith
  rw [← hN] at hdens
  have hsub : componentEuclideanBall C a.val N ⊆ componentEuclideanBall C 0 (6 * N) := by
    intro z hz
    rw [mem_componentEuclideanBall] at hz ⊢
    have ha' : ∀ i, |((a.val i : ℤ) : ℝ)| ≤ 3 * N := fun i => by
      have h1 := ha i
      have h2 : ((|a.val i| : ℤ) : ℝ) ≤ ((3 * (9 * 3 ^ m) : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      rw [hN]; linarith
    have hd := dist_zero_lt_of_abs_le (by positivity) ha'
    have := dist_triangle (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding a.val)
      (latticeEuclideanEmbedding (0 : Vertex 2))
    linarith
  have hpos : 0 < (componentEuclideanBall C a.val N).card := by
    refine Finset.card_pos.2 ⟨a, ?_⟩
    rw [mem_componentEuclideanBall, dist_self]; exact hN0
  have h := componentBallL2_le_of_subset C hsub hpos f
  have hbig := card_componentEuclideanBall_le C (0 : Vertex 2) (by positivity : (0 : ℝ) ≤ 6 * N)
  have hratio : ((componentEuclideanBall C 0 (6 * N)).card : ℝ) /
      ((componentEuclideanBall C a.val N).card : ℝ) ≤ 18225 / κ := by
    have hn : (0 : ℝ) < (componentEuclideanBall C a.val N).card := by exact_mod_cast hpos
    rw [div_le_div_iff₀ hn hκ]
    have h9 : κ * 9 ^ m * 81 = κ * N ^ 2 := by
      rw [hN, mul_pow, ← pow_mul, mul_comm m 2, pow_mul]; norm_num; ring
    have hb : (2 * (6 * N) + 3) ^ 2 ≤ 225 * N ^ 2 := by
      have : (1 : ℝ) ≤ N := by rw [hN]; have := one_le_pow₀ (M₀ := ℝ) (a := 3) (by norm_num) (n := m); linarith
      nlinarith
    calc ((componentEuclideanBall C 0 (6 * N)).card : ℝ) * κ ≤ (2 * (6 * N) + 3) ^ 2 * κ :=
          mul_le_mul_of_nonneg_right hbig hκ.le
      _ ≤ 225 * N ^ 2 * κ := mul_le_mul_of_nonneg_right hb hκ.le
      _ = 225 * 81 * (κ * 9 ^ m) := by
          rw [show 225 * N ^ 2 * κ = 225 * (κ * N ^ 2) by ring, ← h9]; ring
      _ ≤ 225 * 81 * (componentEuclideanBall C a.val N).card := by
          exact mul_le_mul_of_nonneg_left hdens (by norm_num)
      _ = 18225 * (componentEuclideanBall C a.val N).card := by ring
  calc componentBallL2 C a.val N f ≤ _ := h
    _ ≤ Real.sqrt (18225 / κ) * componentBallL2 C 0 (6 * N) f :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hratio) (componentBallL2_nonneg _ _ _ _)
    _ ≤ Real.sqrt (18225 / κ) * B := mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)

/-- **The increments of the corrector** along the open edges of the box `{|z_i| ≤ 3N}`. -/
theorem abs_extend_sub_le_of_adj (C : OpenComponent ω) (q : Fin 2 → ℝ) (u : C → ℝ)
    (hu : u ∈ harmonicGrowthSpace C 1) {N y C₀ CB : ℝ} (hN : 0 < N) (hC₀ : 0 ≤ C₀)
    (hCB : 0 ≤ CB) (hy1 : 1 ≤ y) (hyN : 4 * y ≤ N) (Yv : Vertex 2 → ℝ) {M : ℤ}
    (hR3 : ∀ a : Vertex 2, (∀ i, |a i| ≤ M) → ∀ (R : ℝ), 2 * Yv a ≤ R → ∀ v : C → ℝ,
      (∀ x ∈ componentEuclideanBall C a R,
        (∀ z : C, (componentGraph C).Adj x z → z ∈ componentEuclideanBall C a R) →
          componentLaplacian C v x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, Yv a ≤ r → r ≤ R / 2 →
        componentBallL2 C a r (v - fun _ => c) ≤ C₀ * (r / R) * componentBallL2 C a R v)
    (hYle : ∀ a : Vertex 2, (∀ i, |a i| ≤ M) → Yv a ≤ y)
    (hB : ∀ a : C, (∀ i, |a.val i| ≤ M) →
      componentBallL2 C a.val N (componentCorrector C q u) ≤ CB * (|q 0| + |q 1|) * N)
    (a b : Vertex 2) (ha : ∀ i, |a i| ≤ M) (hab : (openGraph ω).Adj a b) :
    |Rigidity.Section3.extend C (componentCorrector C q u) a -
        Rigidity.Section3.extend C (componentCorrector C q u) b| ≤
      (196 * C₀ * (CB + 1) + 1) * y ^ 3 * (|q 0| + |q 1|) := by
  have hq0 : 0 ≤ |q 0| + |q 1| := by positivity
  have hbound0 : 0 ≤ (196 * C₀ * (CB + 1) + 1) * y ^ 3 * (|q 0| + |q 1|) := by positivity
  by_cases haC : a ∈ C.supp
  · have hbC : b ∈ C.supp := C.mem_supp_of_adj_mem_supp haC hab
    rw [extend_of_mem C _ haC, extend_of_mem C _ hbC, abs_sub_comm]
    set x : C := ⟨a, haC⟩
    set z : C := ⟨b, hbC⟩
    set ρ : ℝ := max (Yv a) 2 with hρ
    have hρ2 : 2 ≤ ρ := le_max_right _ _
    have hYa := hYle a ha
    have hρy : ρ ≤ 2 * y := max_le (by linarith) (by linarith)
    have happ : ∀ a' : ℝ, ∃ c : ℝ, componentBallL2 C x.val ρ ((fun w => u w - a') - fun _ => c) ≤
        C₀ * (ρ / N) * componentBallL2 C x.val N (fun w => u w - a') := by
      intro a'
      have hv : (fun w => u w - a') ∈ harmonicGrowthSpace C 1 :=
        Submodule.sub_mem _ hu (const_mem_harmonicGrowthSpace C 1 a')
      obtain ⟨c, hc⟩ := hR3 a ha N (by linarith) (fun w => u w - a') fun w _ _ => hv.1 w
      exact ⟨c, hc ρ (le_max_left _ _) (by rw [hρ]; exact max_le (by linarith) (by linarith))⟩
    have hxb : x ∈ componentEuclideanBall C x.val ρ := by
      rw [mem_componentEuclideanBall, dist_self]; linarith
    have hd1 := dist_le_one_of_lattice_adj (openGraph_le ω hab)
    have hzb : z ∈ componentEuclideanBall C x.val ρ := by
      rw [mem_componentEuclideanBall]; linarith
    have h := abs_corrector_sub_le C q u x hN hC₀ (by linarith) happ hxb hzb hd1
    have hBx := hB x ha
    calc |componentCorrector C q u z - componentCorrector C q u x|
        ≤ 2 * (2 * ρ + 3) ^ 2 * C₀ * (ρ / N) *
            (componentBallL2 C x.val N (componentCorrector C q u) + (|q 0| + |q 1|) * N) +
          (|q 0| + |q 1|) := h
      _ ≤ 2 * (7 * y) ^ 2 * C₀ * (2 * y / N) * (CB * (|q 0| + |q 1|) * N + (|q 0| + |q 1|) * N) +
          (|q 0| + |q 1|) := by
          have h1 : 2 * ρ + 3 ≤ 7 * y := by linarith
          gcongr
          exact add_nonneg (componentBallL2_nonneg _ _ _ _) (by positivity)
      _ = 196 * C₀ * (CB + 1) * y ^ 3 * (|q 0| + |q 1|) + (|q 0| + |q 1|) := by
          field_simp; ring
      _ ≤ (196 * C₀ * (CB + 1) + 1) * y ^ 3 * (|q 0| + |q 1|) := by
          have : (1 : ℝ) ≤ y ^ 3 := one_le_pow₀ hy1
          nlinarith
  · have hbC : b ∉ C.supp := fun hb => haC (C.mem_supp_of_adj_mem_supp hb hab.symm)
    rw [extend_of_not_mem C _ haC, extend_of_not_mem C _ hbC, sub_zero, abs_zero]
    exact hbound0

/-- **The sum of the squares of the corrector on the box** `{|z_i| ≤ 3N}` from its normalized
norm on `B_{6N}`. -/
theorem sum_sq_extend_le (C : OpenComponent ω) (f : C → ℝ) {N : ℕ} {B : ℝ} (hN : 1 ≤ N)
    (hB : componentBallL2 C 0 (6 * N) f ≤ B) :
    ∑ z ∈ centredBox (3 * N), Rigidity.Section3.extend C f z ^ 2 ≤ 225 * (N : ℝ) ^ 2 * B ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set S := componentEuclideanBall C (0 : Vertex 2) (6 * N) with hS
  have hsum : ∑ z ∈ centredBox (3 * N), Rigidity.Section3.extend C f z ^ 2 ≤
      ∑ x ∈ S, f x ^ 2 := by
    calc ∑ z ∈ centredBox (3 * N), Rigidity.Section3.extend C f z ^ 2
        = ∑ z ∈ (centredBox (3 * N)).filter (· ∈ C.supp), Rigidity.Section3.extend C f z ^ 2 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun z _ => ?_
          split_ifs with hz
          · rfl
          · rw [extend_of_not_mem C f hz]; ring
      _ ≤ ∑ z ∈ S.map (Function.Embedding.subtype _), Rigidity.Section3.extend C f z ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_) fun _ _ _ => sq_nonneg _
          obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
          rw [Finset.mem_map]
          refine ⟨⟨z, hz2⟩, ?_, rfl⟩
          rw [hS, mem_componentEuclideanBall]
          have hz' : ∀ i, |((z i : ℤ) : ℝ)| ≤ 3 * N := fun i => by
            have := (mem_centredBox.1 hz1) i
            exact_mod_cast cast_abs_le (c := 3) (n := N) (by exact_mod_cast this)
          have hd := dist_zero_lt_of_abs_le (by positivity) hz'
          change dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding (0 : Vertex 2)) < _
          linarith
      _ = ∑ x ∈ S, f x ^ 2 := by
          rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [Rigidity.Section3.extend]
  have hcard := card_componentEuclideanBall_le C (0 : Vertex 2) (by positivity : (0 : ℝ) ≤ 6 * N)
  rw [← hS] at hcard
  have hL := hB
  unfold componentBallL2 at hL
  rw [← hS] at hL
  rcases Nat.eq_zero_or_pos S.card with h0 | h0
  · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty] at hsum
    refine hsum.trans (by positivity)
  · have hn : (0 : ℝ) < S.card := by exact_mod_cast h0
    have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans hL
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL 2
    rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hn.le),
      div_le_iff₀ hn] at hsq
    have hb : (2 * (6 * (N : ℝ)) + 3) ^ 2 ≤ 225 * (N : ℝ) ^ 2 := by nlinarith
    calc _ ≤ ∑ x ∈ S, f x ^ 2 := hsum
      _ ≤ B ^ 2 * S.card := hsq
      _ ≤ B ^ 2 * (225 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hcard.trans hb) (sq_nonneg _)
      _ = 225 * (N : ℝ) ^ 2 * B ^ 2 := by ring

end Rigidity.Proofs.Regularity

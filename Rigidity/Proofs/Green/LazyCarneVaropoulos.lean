import Rigidity.Proofs.Green.PlanarGreenDeterministic
import LatticeProb.Graph.CarneVaropoulos

/-!
# A Carne–Varopoulos bound for the lazy walk and small times of the planar heat kernel

For the lazy walk `Q(x, z) = 1/D` for `z ∼ x`, `Q(x, x) = 1 - deg x / D` on a locally finite graph
with degrees at most `D`, Carne's argument gives `Qⁿ(x, y) ≤ 2 e^{-dist(x, y)²/(2n)}`
(`lazyPow_le_carneVaropoulos`): on the ball `B` of radius `n` about `x`, `Qⁿ(x, y)` is the `(x, y)`
entry of the `n`-th power of the symmetric substochastic matrix of `Q` killed off `B`; in the
Chebyshev expansion `Aⁿ = Σ_k p_n(k) T_k(A)` the entries of `T_k(A)` are at most `1` and vanish for
`|k| < dist(x, y)`, so `Aⁿ(x, y)` is at most the tail `Σ_{|k| ≥ dist} p_n(k) ≤ 2 e^{-dist²/(2n)}` of
the walk on `ℤ`. The Chebyshev expansion, the eigenvalue bound and the tail bound are those of the
Carne–Varopoulos bound for the simple random walk in the pinned Lattice-Probability library
(`LatticeProb.Graph.heat_le_carneVaropoulos`), which this file follows for the lazy walk.

Averaging over the Poisson number of steps, the heat kernel of the planar open graph satisfies
`p(t, x, y) ≤ 3 e^{-|x - y|/18}` for `0 < t ≤ |x - y|` (`openHeat_le_exp_of_le_norm`): the steps
`n < N = ⌈8 |x - y|⌉` contribute at most `2 e^{-dist²/(2N)}`, and the steps `n ≥ N` at most
`2^{-N} E[2^{Pois(4t)}] = 2^{-N} e^{4t}`. This is the bound that the proof of Dario–Gu, Theorem 2,
takes from their Proposition 2.11 (Davies 1993).
-/

open scoped Classical
open Polynomial Finset LatticeProb.Graph LatticeProb.Percolation

namespace Rigidity.Green

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (D : ℕ)

/-- The lazy kernel killed off a finite set `S`. -/
noncomputable def lazyMat (S : Finset V) : Matrix S S ℝ :=
  fun u v => if u = v then 1 - (G.degree (u : V) : ℝ) / D else if G.Adj (u : V) v then 1 / D else 0

variable {G D}

theorem lazyMat_isHermitian (S : Finset V) : (lazyMat G D S).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u v => ?_
  simp only [lazyMat, star_trivial]
  by_cases h : u = v
  · subst h
    rfl
  · rw [if_neg (Ne.symm h), if_neg h]
    by_cases ha : G.Adj (u : V) v
    · rw [if_pos ha.symm, if_pos ha]
    · rw [if_neg (fun h' => ha h'.symm), if_neg ha]

theorem lazyMat_nonneg (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (S : Finset V) (u v : S) :
    0 ≤ lazyMat G D S u v := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hdx : (G.degree (u : V) : ℝ) ≤ D := by exact_mod_cast hdeg u
  simp only [lazyMat]
  split_ifs
  · rw [sub_nonneg, div_le_one hDr]
    exact hdx
  · positivity
  · exact le_rfl

theorem sum_lazyMat_le_one (hD : 0 < D) (S : Finset V) (u : S) :
    ∑ v, lazyMat G D S u v ≤ 1 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hsplit : ∀ v : S, lazyMat G D S u v =
      (if u = v then 1 - (G.degree (u : V) : ℝ) / D else 0) +
        (if G.Adj (u : V) v then 1 / (D : ℝ) else 0) := by
    intro v
    simp only [lazyMat]
    by_cases h : u = v
    · subst h
      simp
    · simp [h]
  rw [Finset.sum_congr rfl fun v _ => hsplit v, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ u), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun v : S => G.Adj (u : V) v).card
      ≤ (G.neighborFinset (u : V)).card := by
    refine Finset.card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn
    intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
    exact (G.mem_neighborFinset _ _).2 hv
  rw [G.card_neighborFinset_eq_degree] at hcard
  have hcard' : ((Finset.univ.filter fun v : S => G.Adj (u : V) v).card : ℝ)
      ≤ G.degree (u : V) := by exact_mod_cast hcard
  have : ((Finset.univ.filter fun v : S => G.Adj (u : V) v).card : ℝ) * (1 / (D : ℝ)) ≤
      (G.degree (u : V) : ℝ) / D := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hcard' hDr.le
  linarith

/-- On the ball `B` of radius `n` about `x`, `Qʲ(u, y)` is the `(u, y)` entry of the `j`-th power of
the lazy kernel killed off `B`, when `u` is within `i` steps of `x` and `i + j ≤ n`. -/
theorem lazyPow_eq_lazyMat_pow (x : V) (n : ℕ) {i j : ℕ} (hij : i + j ≤ n) {u y : V}
    (hu : u ∈ ballFinset G x i) (hy : y ∈ ballFinset G x n) :
    lazyPow G D j u y
      = (lazyMat G D (ballFinset G x n) ^ j)
          ⟨u, ballFinset_mono G x (by omega) hu⟩ ⟨y, hy⟩ := by
  set S := ballFinset G x n
  induction j generalizing i u with
  | zero =>
      rw [pow_zero, Matrix.one_apply, lazyPow_zero]
      by_cases h : u = y
      · subst h
        simp
      · rw [if_neg h, if_neg (fun h' => h (congrArg Subtype.val h'))]
  | succ j ih =>
      set Q := lazyMat G D S
      have huS : u ∈ S := ballFinset_mono G x (by omega) hu
      have hN : G.neighborFinset u ⊆ S := fun z hz =>
        ballFinset_mono G x (by omega)
          (mem_ballFinset_succ_of_adj G hu ((G.mem_neighborFinset u z).1 hz))
      have hins : insert u (G.neighborFinset u) ⊆ S := Finset.insert_subset huS hN
      set F : V → ℝ := fun z =>
        if h : z ∈ S then Q ⟨u, huS⟩ ⟨z, h⟩ * (Q ^ j) ⟨z, h⟩ ⟨y, hy⟩ else 0 with hF
      have hsum : ∑ w : S, Q ⟨u, huS⟩ w * (Q ^ j) w ⟨y, hy⟩ = ∑ z ∈ S, F z := by
        rw [← Finset.sum_coe_sort S F]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hF]
        dsimp only
        rw [dif_pos w.2]
      have hzero : ∀ z ∈ S, z ∉ insert u (G.neighborFinset u) → F z = 0 := by
        intro z hz hzN
        rw [hF]
        dsimp only
        rw [dif_pos hz]
        have hne : u ≠ z := fun h => hzN (h ▸ Finset.mem_insert_self u _)
        have hadj : ¬ G.Adj u z := fun h =>
          hzN (Finset.mem_insert_of_mem ((G.mem_neighborFinset u z).2 h))
        have : Q ⟨u, huS⟩ ⟨z, hz⟩ = 0 := by
          simp only [Q, lazyMat]
          rw [if_neg (fun h => hne (congrArg Subtype.val h)), if_neg hadj]
        rw [this, zero_mul]
      have hself : F u = (1 - (G.degree u : ℝ) / D) * lazyPow G D j u y := by
        rw [hF]
        dsimp only
        rw [dif_pos huS, ih (i := i) (by omega) hu]
        simp [Q, lazyMat]
      have hnb : ∀ z ∈ G.neighborFinset u, F z = 1 / (D : ℝ) * lazyPow G D j z y := by
        intro z hz
        have hadj : G.Adj u z := (G.mem_neighborFinset u z).1 hz
        rw [hF]
        dsimp only
        rw [dif_pos (hN hz), ih (i := i + 1) (by omega) (mem_ballFinset_succ_of_adj G hu hadj)]
        simp only [Q, lazyMat]
        rw [if_neg (fun h => hadj.ne (congrArg Subtype.val h)), if_pos hadj]
      have hu_nb : u ∉ G.neighborFinset u := fun h =>
        ((G.mem_neighborFinset u u).1 h).ne rfl
      rw [pow_succ', Matrix.mul_apply, hsum, ← Finset.sum_subset hins hzero,
        Finset.sum_insert hu_nb, hself, Finset.sum_congr rfl hnb, ← Finset.mul_sum, lazyPow_succ]

/-- A nonzero entry of `Qⁿ` comes from a walk of length at most `n`. -/
theorem exists_walk_of_lazyPow_ne_zero :
    ∀ (n : ℕ) (x y : V), lazyPow G D n x y ≠ 0 → ∃ q : G.Walk x y, q.length ≤ n := by
  intro n
  induction n with
  | zero =>
      intro x y h
      rw [lazyPow_zero] at h
      split_ifs at h with hxy
      · subst hxy
        exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
      · exact absurd rfl h
  | succ n ih =>
      intro x y h
      rw [lazyPow_succ] at h
      by_cases h1 : lazyPow G D n x y = 0
      · rw [h1, mul_zero, zero_add] at h
        have h2 : ∑ z ∈ G.neighborFinset x, lazyPow G D n z y ≠ 0 := fun h0 => h (by
          rw [h0, mul_zero])
        obtain ⟨z, hz, hz0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
        obtain ⟨q, hq⟩ := ih z y hz0
        exact ⟨SimpleGraph.Walk.cons ((G.mem_neighborFinset x z).1 hz) q, by
          rw [SimpleGraph.Walk.length_cons]; omega⟩
      · obtain ⟨q, hq⟩ := ih x y h1
        exact ⟨q, by omega⟩

/-- `Qⁿ(x, y) = 0` outside the ball of radius `n` about `x`. -/
theorem lazyPow_eq_zero_of_notMem_ballFinset (x y : V) (n : ℕ) (hy : y ∉ ballFinset G x n) :
    lazyPow G D n x y = 0 := by
  by_contra h
  obtain ⟨q, hq⟩ := exists_walk_of_lazyPow_ne_zero n x y h
  apply hy
  rw [ballFinset, Finset.mem_biUnion]
  exact ⟨q.length, Finset.mem_range.2 (by omega), mem_reach_of_walk G q⟩

/-- The entries of `p(A)` vanish between vertices farther apart than the degree of `p`. -/
theorem aeval_lazyMat_apply_eq_zero (S : Finset V) (p : ℝ[X]) (u v : S)
    (hp : p.natDegree < G.dist u v) : (aeval (lazyMat G D S) p) u v = 0 := by
  have hwalk : ∀ (j : ℕ) (a b : S), (lazyMat G D S ^ j) a b ≠ 0 →
      ∃ q : G.Walk (a : V) b, q.length ≤ j := by
    intro j
    induction j with
    | zero =>
        intro a b h
        rw [pow_zero, Matrix.one_apply] at h
        split_ifs at h with hab
        · subst hab
          exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
        · exact absurd rfl h
    | succ j ih =>
        intro a b h
        rw [pow_succ', Matrix.mul_apply] at h
        obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
        obtain ⟨q, hq⟩ := ih w b (fun h0 => hw (by rw [h0, mul_zero]))
        by_cases haw : a = w
        · subst haw
          exact ⟨q, by omega⟩
        · have hadj : G.Adj (a : V) w := by
            by_contra hna
            apply hw
            simp only [lazyMat, if_neg haw, if_neg hna, zero_mul]
          exact ⟨SimpleGraph.Walk.cons hadj q, by rw [SimpleGraph.Walk.length_cons]; omega⟩
  have hzero : ∀ j, j < G.dist u v → (lazyMat G D S ^ j) u v = 0 := by
    intro j hj
    by_contra h
    obtain ⟨q, hq⟩ := hwalk j u v h
    have := SimpleGraph.dist_le q
    omega
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Matrix.smul_apply, hzero j (by rw [Finset.mem_range] at hj; omega), smul_zero]

/-- **The Carne–Varopoulos bound for the lazy walk**: `Qⁿ(x, y) ≤ 2 e^{-dist(x, y)²/(2n)}`. -/
theorem lazyPow_le_carneVaropoulos (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (x y : V) (n : ℕ)
    (hn : 1 ≤ n) :
    lazyPow G D n x y ≤ 2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by
  set S := ballFinset G x n
  have hRHS : 0 ≤ 2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by positivity
  by_cases hy : y ∈ S
  swap
  · rw [lazyPow_eq_zero_of_notMem_ballFinset x y n hy]
    exact hRHS
  have hx : x ∈ S := self_mem_ballFinset G x n
  set x' : S := ⟨x, hx⟩
  set y' : S := ⟨y, hy⟩
  set A := lazyMat G D S with hAdef
  have hA : A.IsHermitian := lazyMat_isHermitian S
  have hev : ∀ i, |hA.eigenvalues i| ≤ 1 :=
    abs_eigenvalues_le_one hA (lazyMat_nonneg hD hdeg S) (sum_lazyMat_le_one hD S)
      (fun _ => 1) (fun _ => one_pos) (fun i j => by simp [hAdef])
  have h1 : lazyPow G D n x y = (A ^ n) x' y' :=
    lazyPow_eq_lazyMat_pow x n (i := 0) (by omega) (self_mem_ballFinset G x 0) hy
  have hpow : (A ^ n) x' y'
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          lineWalk n k * (aeval A (Chebyshev.T ℝ k)) x' y' := by
    rw [← aeval_X_pow (R := ℝ) A (n := n), X_pow_eq_sum_lineWalk_T, map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_C, ← Algebra.smul_def, Matrix.smul_apply, smul_eq_mul]
  have hterm : ∀ k ∈ Finset.Icc (-(n : ℤ)) n,
      lineWalk n k * (aeval A (Chebyshev.T ℝ k)) x' y'
        ≤ if (G.dist x y : ℝ) ≤ |(k : ℝ)| then lineWalk n k else 0 := by
    intro k _
    split_ifs with hk
    · calc lineWalk n k * (aeval A (Chebyshev.T ℝ k)) x' y'
          ≤ lineWalk n k * |(aeval A (Chebyshev.T ℝ k)) x' y'| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (lineWalk_nonneg n k)
        _ ≤ lineWalk n k * 1 :=
            mul_le_mul_of_nonneg_left (abs_aeval_T_apply_le_one hA hev k x' y')
              (lineWalk_nonneg n k)
        _ = lineWalk n k := mul_one _
    · have hlt : (Chebyshev.T ℝ k).natDegree < G.dist x y := by
        rw [Chebyshev.natDegree_T]
        have hcast : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        have : ((k.natAbs : ℕ) : ℝ) < (G.dist x y : ℝ) := by rw [hcast]; linarith
        exact_mod_cast this
      rw [aeval_lazyMat_apply_eq_zero S _ x' y' hlt, mul_zero]
  rw [h1, hpow]
  calc ∑ k ∈ Finset.Icc (-(n : ℤ)) n, lineWalk n k * (aeval A (Chebyshev.T ℝ k)) x' y'
      ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          if (G.dist x y : ℝ) ≤ |(k : ℝ)| then lineWalk n k else 0 :=
        Finset.sum_le_sum hterm
    _ = ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter
            (fun k : ℤ => (G.dist x y : ℝ) ≤ |(k : ℝ)|),
          lineWalk n k := (Finset.sum_filter _ _).symm
    _ ≤ 2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) :=
        sum_lineWalk_tail_le n hn _ (Nat.cast_nonneg _)

/-! ### Small times for the planar heat kernel -/

/-- Along a walk of the open graph, the `ℓ¹` displacement is at most the length. -/
theorem sum_abs_sub_le_length_openGraph {ω : Configuration 2} :
    ∀ {a b : Vertex 2} (q : (openGraph ω).Walk a b), ∑ i, |b i - a i| ≤ q.length := by
  intro a b q
  induction q with
  | nil => simp
  | cons hadj q ih =>
      rename_i u v w
      have h1 : latticeL1Dist u v = 1 := lattice_adj_iff_l1Dist.mp (openGraph_le ω hadj)
      have h2 : ∑ i, |w i - u i| ≤ ∑ i, (|w i - v i| + |v i - u i|) :=
        Finset.sum_le_sum fun i _ => abs_sub_le _ _ _
      have h3 : ∑ i, |v i - u i| = 1 := by
        rw [← h1, latticeL1Dist]
        exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
      rw [Finset.sum_add_distrib, h3] at h2
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- The Euclidean distance of two vertices joined by a walk of the open graph is at most the
length of the walk. -/
theorem norm_edz_le_length {ω : Configuration 2} {x y : Vertex 2} (q : (openGraph ω).Walk x y) :
    ‖edz x y‖ ≤ q.length := by
  have h := sum_abs_sub_le_length_openGraph q
  have hR : ∑ i, |((y i - x i : ℤ) : ℝ)| ≤ q.length := by
    have h' : ((∑ i, |y i - x i| : ℤ) : ℝ) ≤ ((q.length : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h' ⊢
    exact h'
  have hl2 : ‖edz x y‖ ≤ ∑ i, |((y i - x i : ℤ) : ℝ)| := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
    have hsq : ∀ i : Fin 2, ‖edz x y i‖ ^ 2 = |((y i - x i : ℤ) : ℝ)| ^ 2 := by
      intro i
      change ‖((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)‖ ^ 2 = _
      rw [Real.norm_eq_abs, sq_abs, sq_abs]
      push_cast
      ring
    simp only [hsq, Fin.sum_univ_two]
    nlinarith [mul_nonneg (abs_nonneg ((y 0 - x 0 : ℤ) : ℝ)) (abs_nonneg ((y 1 - x 1 : ℤ) : ℝ))]
  exact hl2.trans hR

/-- The Poisson weights against `2^n` sum to `e^{Dt}`. -/
theorem hasSum_poissonWeight_mul_two_pow (D : ℕ) (t : ℝ) :
    HasSum (fun n => poissonWeight D t n * 2 ^ n) (Real.exp (D * t)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (2 * ((D : ℝ) * t))
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-D * t))
  have he : Real.exp (-D * t) * Real.exp (2 * (D * t)) = Real.exp (D * t) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he] at h2
  have hf : (fun n => poissonWeight D t n * 2 ^ n) =
      fun i => Real.exp (-D * t) * ((2 * ((D : ℝ) * t)) ^ i / i.factorial) := by
    funext n
    unfold poissonWeight
    rw [mul_pow]
    ring
  rw [hf]
  exact h2

/-- **Small times for the planar heat kernel**: `p(t, x, y) ≤ 3 e^{-|x - y|/18}` for
`0 < t ≤ |x - y|`. -/
theorem openHeat_le_exp_of_le_norm (ω : Configuration 2) {x y : Vertex 2} {t : ℝ} (ht : 0 < t)
    (htx : t ≤ ‖edz x y‖) : openHeat ω t x y ≤ 3 * Real.exp (-(‖edz x y‖ / 18)) := by
  set r := ‖edz x y‖ with hr
  have hr0 : 0 < r := lt_of_lt_of_le ht htx
  have hxy : x ≠ y := by
    intro h
    rw [hr, h, edz_self, norm_zero] at hr0
    exact lt_irrefl 0 hr0
  have hr1 : 1 ≤ r := one_le_norm_edz hxy
  set N : ℕ := ⌈8 * r⌉₊ with hN
  have hN1 : 8 * r ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ 9 * r := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 8 * r by positivity)
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hdeg := openGraph_degree_le_four ω
  -- pointwise bound on `Qⁿ(x, y)`
  have hpt : ∀ n : ℕ, lazyPow (openGraph ω) 4 n x y ≤
      2 * Real.exp (-(r / 18)) + (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
    intro n
    have h01 := lazyPow_mem_Icc (by norm_num) hdeg n x y
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [lazyPow_zero, if_neg hxy]
      positivity
    by_cases hnN : n < N
    · by_cases hreach : (openGraph ω).Reachable x y
      · obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
        have hd : r ≤ (openGraph ω).dist x y := by
          have := norm_edz_le_length q
          rwa [hq] at this
        have hcv := lazyPow_le_carneVaropoulos (by norm_num) hdeg x y n hnpos
        have hn' : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
        have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
        have hexp : -((((openGraph ω).dist x y : ℕ) : ℝ) ^ 2) / (2 * n) ≤ -(r / 18) := by
          rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
          have hd2 : r ^ 2 ≤ (((openGraph ω).dist x y : ℕ) : ℝ) ^ 2 :=
            pow_le_pow_left₀ hr0.le hd 2
          nlinarith
        calc lazyPow (openGraph ω) 4 n x y ≤ 2 * Real.exp (-(r / 18)) := by
              refine hcv.trans ?_
              gcongr
          _ ≤ 2 * Real.exp (-(r / 18)) + (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
              have : 0 ≤ (2 : ℝ)⁻¹ ^ N * 2 ^ n := by positivity
              linarith
      · have h0 : lazyPow (openGraph ω) 4 n x y = 0 := by
          by_contra hne
          obtain ⟨q, -⟩ := exists_walk_of_lazyPow_ne_zero n x y hne
          exact hreach ⟨q⟩
        rw [h0]
        positivity
    · have hpow : 1 ≤ (2 : ℝ)⁻¹ ^ N * 2 ^ n := by
        rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
        exact pow_le_pow_right₀ (by norm_num) (not_lt.1 hnN)
      have : 0 ≤ 2 * Real.exp (-(r / 18)) := by positivity
      linarith [h01.2]
  have hs1 := hasSum_poissonWeight (D := 4) t
  have hs2 := hasSum_poissonWeight_mul_two_pow 4 t
  have hsum : HasSum (fun n => poissonWeight 4 t n *
      (2 * Real.exp (-(r / 18)) + (2 : ℝ)⁻¹ ^ N * 2 ^ n))
      (2 * Real.exp (-(r / 18)) + (2 : ℝ)⁻¹ ^ N * Real.exp (4 * t)) := by
    have := (hs1.mul_left (2 * Real.exp (-(r / 18)))).add (hs2.mul_left ((2 : ℝ)⁻¹ ^ N))
    have hf : (fun n => poissonWeight 4 t n * (2 * Real.exp (-(r / 18)) + (2 : ℝ)⁻¹ ^ N * 2 ^ n)) =
        fun n => 2 * Real.exp (-(r / 18)) * poissonWeight 4 t n +
          (2 : ℝ)⁻¹ ^ N * (poissonWeight 4 t n * 2 ^ n) := by
      funext n
      ring
    have hv : 2 * Real.exp (-(r / 18)) * 1 + (2 : ℝ)⁻¹ ^ N * Real.exp (((4 : ℕ) : ℝ) * t) =
        2 * Real.exp (-(r / 18)) + (2 : ℝ)⁻¹ ^ N * Real.exp (4 * t) := by
      push_cast
      ring
    rw [hf, ← hv]
    exact this
  have hle : openHeat ω t x y ≤ 2 * Real.exp (-(r / 18)) + (2 : ℝ)⁻¹ ^ N * Real.exp (4 * t) := by
    rw [openHeat, vsrwHeat, ← hsum.tsum_eq]
    refine Summable.tsum_le_tsum (fun n => ?_)
      (summable_vsrwHeat (by norm_num) hdeg t x y) hsum.summable
    exact mul_le_mul_of_nonneg_left (hpt n) (poissonWeight_nonneg ht.le n)
  have htail : (2 : ℝ)⁻¹ ^ N * Real.exp (4 * t) ≤ Real.exp (-(r / 18)) := by
    have h2 : (2 : ℝ)⁻¹ ^ N = Real.exp (-(N * Real.log 2)) := by
      rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), inv_pow]
    rw [h2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl2 := Real.log_two_gt_d9
    nlinarith
  linarith

end Rigidity.Green

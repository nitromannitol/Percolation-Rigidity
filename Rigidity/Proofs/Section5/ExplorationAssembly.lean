import Rigidity.Steps.Section5.LargeGradientSensitive
import Rigidity.Proofs.Section5.InfiniteBranches
import Rigidity.Proofs.Section5.ExplorationBlocks
import Rigidity.Proofs.Section5.GreedyExploration

/-! # Lemma 5.27, Step 6: the exploration cannot be too long

## The termination window

Proof of `TerminationWindowStep` (step:5.27-terminate, L2641-2652 of the corrected draft).

Let `γ` be an exploration path of length `n` from `x₀` through `x₁`, `y = γ n`, `𝒢` the
exploration graph (vertex set `V`). We reindex `γ` by `ℕ` (`NatPath`), and write `γ_j` for `γ j`.

* `γ_j ∈ V` for `1 ≤ j ≤ n` (the prefix of `γ` is a witness), `ℓ` is strictly increasing along
  `γ_1, ..., γ_n`, hence `γ` is injective there, and consecutive points are adjacent in `𝒢`;
* `l1 (γ_j - x₀) ≤ j`, so `|y - x₀|₁ ≥ W + 1` forces `n ≥ W + 1`;
* (counting) a set of at least `W + 1` points of `ℤ²`, with `4 R² ≤ W`, contains two points at
  `l¹`-distance at least `R`: it injects, after translation by the coordinatewise minimum, into a
  square of side `⌈R⌉` if all pairwise distances were `< R`;
* (block continuation) if `γ_{m-1}, γ_m` lie in a block `B`, `γ_m` is not a separator and
  `m < n`, then `γ_{m+1} ∈ B`: a block `B' ⊇ {γ_m, γ_{m+1}}` different from `B` would be separated
  from `B` by `γ_m`, whereas `γ_{m+1} → y → x₁ → γ_{m-1}` avoids `γ_m` (the middle part is a walk
  of `𝒢` from `x₁` to `y` missing the non-separator `γ_m`);
* (window) if `ω ∈ E_R(γ_i)` and no separator is visited within `W` of `i`, the points
  `γ_a, ..., γ_b` (`a = max 1 (i - W)`, `b = min n (i + W)`, `b - a ≥ W`) lie in one block `B`.
  The set `S = {γ_a, ..., γ_b}` is finite, connected, contains `γ_i` and has `≥ W + 1` points, hence
  two points at `l¹`-distance `≥ R`; `E_R(γ_i)` gives `C_f + 1` disjoint paths to infinity from
  `S ⊆ B`, contradicting the assumption on blocks;
* (count) the good indices lie in the union over the separator indices `j` of the windows
  `{i : |i - j| ≤ W}`, each of at most `2 W + 1` elements.

## Assembly of the exploration conclusion

Proof of `ExplorationAssemblyStep` (step:5.27-explore, Step 6, Cases 1 and 2, L2606-2627 and
L2655-2656 of the corrected draft).

Let `B 0 = B₀, c 1, B 1, c 2, …` be the greedy path of `GreedyPath`, of length `N ≤ ∞`, and
`E = ⋃_{k ≤ N} B k ⊆ 𝒢`.

* **Memberships.** `c (k + 1) ∈ B k ∩ B (k + 1)`, as the block-cut tree joins a block to the
  cut-vertices it contains.
* **Growth.** `ℓ(c t) ≥ ℓ(x₁) + t i / 4` for `1 ≤ t ≤ N`, by induction on `t` from
  `FluxGrowth` and the flux bound `i ≤ i_in` along the path.
* **Separators.** For `y ∈ B k`, every point of `𝒢` separating `x₁` from `y` is some `c t` with
  `1 ≤ t ≤ k`: if `s ≠ x₁` is none of them, every `z ∈ B k \ {s}` is joined to `x₁` in
  `𝒢 \ {s}`, by induction on `k` (a block minus a point is connected, and `c (k + 1) ∈ B k`).
* **Bound.** On an exploration path `γ` to `y ∈ B k`, `ℓ` is strictly increasing, so `j ↦ t j`
  with `γ j = c (t j)` is injective on the indices of separators; its maximum `t*` is at least
  their number, and `ℓ y ≥ ℓ (c t*) ≥ ℓ x₁ + t* i / 4 ≥ ℓ x₀ + #separators · i / 4`.
* **Dichotomy.** If `N = K` is finite, the last block `B K` is infinite (then `E` is infinite),
  or it is finite, kept, and prunes or has no child, so `LeafSensitive` gives a sensitive edge in
  `B K ⊆ E`. If `N = ∞`, the sequence `B 0, c 1, B 1, …` of the block-cut tree consists of
  adjacent vertices, each a strict ancestor of the next, hence is injective (a path in a tree
  cannot return), so `k ↦ c (k + 1)` is injective with values in `E`: `E` is infinite. An
  infinite subset of `ℤ²` is unbounded, as cubes are finite.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5.Termination

/-! ### `l¹` and counting -/

/-- The triangle inequality for `l1`. -/
theorem l1_add_le (a b : Vertex 2) : l1 (a + b) ≤ l1 a + l1 b := by
  simp only [l1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa using abs_add_le ((a i : ℤ) : ℝ) ((b i : ℤ) : ℝ)

/-- Lattice-adjacent sites are at `l1`-distance at most one. -/
theorem l1_sub_le_one_of_lattice_adj {a b : Vertex 2} (h : (LatticeProb.lattice 2).Adj a b) :
    l1 (b - a) ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · have : b - a = LatticeProb.unit i := by rw [hi]; abel
    rw [this]; simp only [l1, Fin.sum_univ_two]
    fin_cases i <;> simp [LatticeProb.unit]
  · have : b - a = -LatticeProb.unit i := by rw [hi]; abel
    rw [this]; simp only [l1, Fin.sum_univ_two]
    fin_cases i <;> simp [LatticeProb.unit]

/-- A finite set of more than `4 R²` points of `ℤ²` contains two points at `l¹`-distance at
least `R`: otherwise it injects into a square of side `⌈R⌉`. -/
theorem exists_far_pair {S : Finset (Vertex 2)} {R : ℝ} {W : ℕ} (hR : 1 ≤ R)
    (hW : 4 * R ^ 2 ≤ W) (hS : W + 1 ≤ S.card) : ∃ a ∈ S, ∃ b ∈ S, R ≤ l1 (a - b) := by
  by_contra hcon
  push Not at hcon
  have hne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨m, hm, hmle⟩ : ∃ m : Fin 2 → ℤ, (∀ k, ∃ z' ∈ S, m k = z' k) ∧
      ∀ z ∈ S, ∀ k, m k ≤ z k :=
    ⟨fun k => S.inf' hne fun z => z k, fun k => Finset.exists_mem_eq_inf' hne _,
      fun z hz k => Finset.inf'_le _ hz⟩
  have hdiff : ∀ z ∈ S, ∀ k, ((z k - m k : ℤ) : ℝ) < R := by
    intro z hz k
    obtain ⟨z', hz', hk⟩ := hm k
    have h1 := abs_le_l1 (z - z') k
    have h2 := hcon z hz z' hz'
    have h3 : ((z k - m k : ℤ) : ℝ) = (((z - z') k : ℤ) : ℝ) := by rw [hk]; rfl
    rw [h3]
    exact lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt h1 h2)
  set N : ℕ := ⌈R⌉₊ with hN
  have hmaps : ∀ z ∈ S, ((z 0 - m 0).toNat, (z 1 - m 1).toNat) ∈
      Finset.range N ×ˢ Finset.range N := by
    intro z hz
    have key : ∀ k, (z k - m k).toNat < N := by
      intro k
      refine Nat.lt_ceil.2 ?_
      have e : (((z k - m k).toNat : ℕ) : ℤ) = z k - m k :=
        Int.toNat_of_nonneg (by linarith [hmle z hz k])
      have h := hdiff z hz k
      rw [← e] at h
      exact_mod_cast h
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (key 0), Finset.mem_range.2 (key 1)⟩
  have hinj : Set.InjOn (fun z : Vertex 2 => ((z 0 - m 0).toNat, (z 1 - m 1).toNat)) S := by
    intro z hz z' hz' h
    have h0 := hmle z hz 0
    have h1 := hmle z hz 1
    have h0' := hmle z' hz' 0
    have h1' := hmle z' hz' 1
    rw [Prod.mk.injEq] at h
    funext k
    fin_cases k
    · simp only [Fin.zero_eta]; omega
    · simp only [Fin.mk_one]; omega
  have hcard := Finset.card_le_card_of_injOn
    (fun z : Vertex 2 => ((z 0 - m 0).toNat, (z 1 - m 1).toNat)) hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  have hNR : (N : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  have h1 : ((W : ℝ) + 1) ≤ (N : ℝ) * N := by exact_mod_cast hS.trans hcard
  have h2 : (N : ℝ) * N < (R + 1) * (R + 1) := mul_self_lt_mul_self (Nat.cast_nonneg N) hNR
  nlinarith

/-- The window `{i : |i - j| ≤ W}` of `Fin (n + 1)` has at most `2 W + 1` elements. -/
theorem card_window_le {n : ℕ} (W : ℕ) (j : Fin (n + 1)) :
    (Finset.univ.filter fun i : Fin (n + 1) => (i : ℕ) ≤ j + W ∧ (j : ℕ) ≤ i + W).card
      ≤ 2 * W + 1 := by
  calc _ ≤ (Finset.Icc ((j : ℕ) - W) (j + W)).card :=
        Finset.card_le_card_of_injOn (fun i : Fin (n + 1) => (i : ℕ))
          (fun i hi => by
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
            simp only [Finset.coe_Icc, Set.mem_Icc]
            omega)
          (fun a _ b _ h => Fin.ext h)
    _ ≤ 2 * W + 1 := by rw [Nat.card_Icc]; omega

/-- A family of indices covered by the `W`-windows of the indices of `J` has at most
`(2 W + 1) |J|` elements. -/
theorem card_le_of_window_cover {n W : ℕ} {A J : Finset (Fin (n + 1))}
    (hcov : ∀ i ∈ A, ∃ j ∈ J, (i : ℕ) ≤ j + W ∧ (j : ℕ) ≤ i + W) :
    A.card ≤ (2 * W + 1) * J.card := by
  classical
  calc A.card
      ≤ (J.biUnion fun j => Finset.univ.filter fun i : Fin (n + 1) =>
          (i : ℕ) ≤ j + W ∧ (j : ℕ) ≤ i + W).card :=
        Finset.card_le_card fun i hi => by
          obtain ⟨j, hj, h⟩ := hcov i hi
          exact Finset.mem_biUnion.2 ⟨j, hj, by simpa using h⟩
    _ ≤ ∑ j ∈ J, (Finset.univ.filter fun i : Fin (n + 1) =>
          (i : ℕ) ≤ j + W ∧ (j : ℕ) ≤ i + W).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ J, (2 * W + 1) := Finset.sum_le_sum fun j _ => card_window_le W j
    _ = (2 * W + 1) * J.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### The path reindexed by `ℕ` -/

section NatPath

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- The adjacency of `𝒞_∞` is the lattice adjacency of the underlying sites. -/
theorem lattice_adj_of_componentAdj {a b : C} (h : (componentGraph C).Adj a b) :
    (LatticeProb.lattice 2).Adj a.val b.val :=
  openGraph_le ω ((C.toSimpleGraph_adj _ _).1 h)

/-- An exploration path of length `n`, reindexed by `ℕ`. -/
structure NatPath (u ℓ : C → ℝ) (x₀ x₁ : C) (n : ℕ) (g : ℕ → C) : Prop where
  one_le : 1 ≤ n
  adj : ∀ i < n, (componentGraph C).Adj (g i) (g (i + 1))
  level : ∀ i ≤ n, u (g i) = u x₀
  zero : g 0 = x₀
  one : g 1 = x₁
  inc : ∀ i, 1 ≤ i → i < n → ℓ (g i) < ℓ (g (i + 1))

/-- An exploration path is the restriction of a `NatPath`. -/
theorem NatPath.of_isExplorationPath {n : ℕ} {γ : Fin (n + 1) → C}
    (hγ : IsExplorationPath C u ℓ x₀ x₁ γ) :
    ∃ g : ℕ → C, NatPath u ℓ x₀ x₁ n g ∧ ∀ i : Fin (n + 1), g i = γ i := by
  obtain ⟨hn, hadj, hu, h0, h1, hinc⟩ := hγ
  let g : ℕ → C := fun i => γ ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hg : ∀ i (hi : i ≤ n), g i = γ ⟨i, Nat.lt_succ_of_le hi⟩ :=
    fun i hi => congrArg γ (Fin.ext (min_eq_left hi))
  refine ⟨g, ⟨hn, fun i hi => ?_, fun i hi => ?_, ?_, ?_, fun i h1i hi => ?_⟩, fun i => ?_⟩
  · rw [hg i hi.le, hg (i + 1) hi]
    exact hadj ⟨i, hi⟩
  · rw [hg i hi]
    exact hu _
  · rw [hg 0 (Nat.zero_le _)]
    exact (congrArg γ (Fin.ext (by simp))).trans h0
  · rw [hg 1 hn]
    exact (congrArg γ (Fin.ext (by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]))).trans h1
  · rw [hg i hi.le, hg (i + 1) hi]
    exact hinc ⟨i, hi⟩ h1i
  · rw [hg i (Nat.lt_succ_iff.1 i.2)]

variable {n : ℕ} {g : ℕ → C}

/-- The points `γ_j`, `1 ≤ j ≤ n`, lie in `𝒢`. -/
theorem NatPath.mem (hg : NatPath u ℓ x₀ x₁ n g) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    g j ∈ explorationSet C u ℓ x₀ x₁ :=
  mem_explorationSet_iff.2 ⟨j, hj1, g, fun i hi => hg.adj i (by omega),
    fun i hi => hg.level i (by omega), hg.zero, hg.one, rfl,
    fun i h1 hi => hg.inc i h1 (by omega)⟩

/-- `ℓ` is strictly increasing along `γ_1, ..., γ_n`. -/
theorem NatPath.lt (hg : NatPath u ℓ x₀ x₁ n g) {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k)
    (hk : k ≤ n) : ℓ (g j) < ℓ (g k) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d + 1 := ⟨k - j - 1, by omega⟩
  induction d with
  | zero => simpa using hg.inc j hj (by omega)
  | succ d ih => exact (ih (by omega) (by omega)).trans (hg.inc (j + d + 1) (by omega) (by omega))

/-- `γ` is injective on the indices `1, ..., n`. -/
theorem NatPath.eq_of_eq (hg : NatPath u ℓ x₀ x₁ n g) {j k : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (h : g j = g k) : j = k := by
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · exact absurd (congrArg ℓ h) (hg.lt hj1 hjk hkn).ne
  · exact hjk
  · exact absurd (congrArg ℓ h) (hg.lt hk1 hjk hjn).ne'

/-- Consecutive points `γ_j, γ_{j+1}`, `1 ≤ j < n`, are adjacent in `𝒢`. -/
theorem NatPath.adj_G (hg : NatPath u ℓ x₀ x₁ n g) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) :
    (explorationGraph C u ℓ x₀ x₁).Adj (g j) (g (j + 1)) :=
  ⟨hg.mem hj1 hjn.le, hg.mem (by omega) hjn, hg.adj j hjn, (hg.inc j hj1 hjn).ne⟩

/-- `γ_a` reaches `γ_b` inside any set `S` containing `γ_a, ..., γ_b`. -/
theorem NatPath.reachIn_interval (hg : NatPath u ℓ x₀ x₁ n g) {S : Set C} {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hbn : b ≤ n) (hS : ∀ k, a ≤ k → k ≤ b → g k ∈ S) :
    GraphReachIn (explorationGraph C u ℓ x₀ x₁) S (g a) (g b) := by
  induction b, hab using Nat.le_induction with
  | base => exact .refl (hS a le_rfl le_rfl)
  | succ b hab ih =>
    exact (ih (by omega) fun k h1 h2 => hS k h1 (by omega)).trans
      (.of_adj (hS b hab (by omega)) (hS (b + 1) (by omega) le_rfl)
        (hg.adj_G (by omega) (by omega)))

/-- Every vertex of a walk of `𝒢` starting in `𝒢` lies in `𝒢`. -/
theorem walk_support_mem_explorationSet {a b : C}
    (q : (explorationGraph C u ℓ x₀ x₁).Walk a b) (ha : a ∈ explorationSet C u ℓ x₀ x₁) :
    ∀ v ∈ q.support, v ∈ explorationSet C u ℓ x₀ x₁ := by
  induction q with
  | nil => simpa using ha
  | cons h p ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact ih h.2.1 v hv

/-- `|γ_j - x₀|₁ ≤ j`. -/
theorem NatPath.l1_le (hg : NatPath u ℓ x₀ x₁ n g) {j : ℕ} (hj : j ≤ n) :
    l1 ((g j).val - x₀.val) ≤ j := by
  induction j with
  | zero => simp [hg.zero, l1]
  | succ j ih =>
    have h1 := ih (by omega)
    have h2 := l1_sub_le_one_of_lattice_adj (lattice_adj_of_componentAdj (hg.adj j (by omega)))
    have e : (g (j + 1)).val - x₀.val = ((g (j + 1)).val - (g j).val) + ((g j).val - x₀.val) := by
      abel
    rw [e]
    push_cast
    linarith [l1_add_le ((g (j + 1)).val - (g j).val) ((g j).val - x₀.val)]

/-- **Block continuation.** If `γ_m, γ_{m+1}` lie in a block `B` and `γ_{m+1}` (with `m + 2 ≤ n`)
is not a separator, then `γ_{m+2} ∈ B`. -/
theorem NatPath.mem_block_succ (hg : NatPath u ℓ x₀ x₁ n g) {B : Set C}
    (hB : IsBlock C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) B) {m : ℕ}
    (hm1 : 1 ≤ m) (hmn : m + 2 ≤ n) (hsep : g (m + 1) ∉ separators C u ℓ x₀ x₁ (g n))
    (h1 : g m ∈ B) (h2 : g (m + 1) ∈ B) : g (m + 2) ∈ B := by
  by_contra h3
  obtain ⟨B', hB', hsub⟩ := exists_isBlock_superset
    (biconnectedIn_pair (hg.mem (by omega) (by omega) : g (m + 1) ∈ explorationSet C u ℓ x₀ x₁)
      (hg.mem (by omega) hmn : g (m + 2) ∈ explorationSet C u ℓ x₀ x₁)
      (hg.adj_G (by omega) (by omega)))
  have hx' : g (m + 1) ∈ B' := hsub (by simp)
  have hb' : g (m + 2) ∈ B' := hsub (by simp)
  have hne : B ≠ B' := fun h => h3 (by rw [h]; exact hb')
  have hSk : ∀ k, 1 ≤ k → k ≤ n → k ≠ m + 1 →
      g k ∈ explorationSet C u ℓ x₀ x₁ \ {g (m + 1)} := fun k hk1 hkn hk =>
    ⟨hg.mem hk1 hkn, fun h => hk (hg.eq_of_eq hk1 hkn (by omega) (by omega)
      (Set.mem_singleton_iff.1 h))⟩
  have hne1 : g (m + 1) ≠ x₁ := fun h => by
    have := hg.eq_of_eq (by omega) (by omega) (by omega) (by omega) (h.trans hg.one.symm)
    omega
  have hne2 : g (m + 1) ≠ g n := fun h => by
    have := hg.eq_of_eq (by omega) (by omega) (by omega) (by omega) h
    omega
  obtain ⟨q, hq⟩ : ∃ q : (explorationGraph C u ℓ x₀ x₁).Walk x₁ (g n), g (m + 1) ∉ q.support := by
    by_contra hcon
    push Not at hcon
    exact hsep ⟨hne1, hne2, hcon⟩
  have hx1V : x₁ ∈ explorationSet C u ℓ x₀ x₁ := by
    have := hg.mem (j := 1) le_rfl (by omega)
    rwa [hg.one] at this
  have hqS : ∀ v ∈ q.reverse.support, v ∈ explorationSet C u ℓ x₀ x₁ \ {g (m + 1)} := by
    intro v hv
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    exact ⟨walk_support_mem_explorationSet q hx1V v hv,
      fun h => hq (Set.mem_singleton_iff.1 h ▸ hv)⟩
  have r1 : GraphReachIn (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁ \ {g (m + 1)}) (g (m + 2)) (g n) :=
    hg.reachIn_interval (by omega) hmn le_rfl fun k h1 h2 => hSk k (by omega) (by omega) (by omega)
  have r2 : GraphReachIn (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁ \ {g (m + 1)}) (g n) x₁ := ⟨q.reverse, hqS⟩
  have r3 : GraphReachIn (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁ \ {g (m + 1)}) (g 1) (g m) :=
    hg.reachIn_interval le_rfl hm1 (by omega) fun k h1 h2 => hSk k (by omega) (by omega) (by omega)
  rw [hg.one] at r3
  exact IsBlock.not_reachIn hB hB' hne h2 hx' h1 hb' (r1.trans (r2.trans r3))

end NatPath

/-! ### The window around a good index -/

section Window

variable {ω : Configuration 2} {h : HasUniqueInfiniteOpenComponent ω}
  {u ℓ : uniqueInfiniteComponent h → ℝ} {x₀ x₁ : uniqueInfiniteComponent h} {n : ℕ}
  {g : ℕ → uniqueInfiniteComponent h}

/-- **Window.** If `ω ∈ E_R(γ_i)`, `n ≥ W + 1`, and no block of `𝒢` is connected to infinity by
`C_f + 1` disjoint paths, then some index `j` within `W` of `i` has `γ_j` a separator. -/
theorem NatPath.exists_separator_window (hg : NatPath u ℓ x₀ x₁ n g) {Cf : ℕ} {R : ℝ} {W : ℕ}
    (hR : 1 ≤ R) (hW : 4 * R ^ 2 ≤ W)
    (hblocks : ∀ S, IsBlock _ (explorationGraph _ u ℓ x₀ x₁) (explorationSet _ u ℓ x₀ x₁) S →
      ¬ HasDisjointPathsToInfinity _ S (Cf + 1))
    (hn : W + 1 ≤ n) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) (hE : ω ∈ eventE Cf R (g i).val) :
    ∃ j ≤ n, g j ∈ separators _ u ℓ x₀ x₁ (g n) ∧ i ≤ j + W ∧ j ≤ i + W := by
  by_contra hno
  have hnosep : ∀ j, j ≤ n → g j ∈ separators _ u ℓ x₀ x₁ (g n) →
      ¬ (i ≤ j + W ∧ j ≤ i + W) := fun j hj hs hij => hno ⟨j, hj, hs, hij.1, hij.2⟩
  have hW1 : 1 ≤ W := by
    have : (1 : ℝ) ≤ W := by nlinarith
    exact_mod_cast this
  obtain ⟨a, b, ha1, haW, hai, hib, hbn, hbW, hab⟩ : ∃ a b : ℕ, 1 ≤ a ∧ i ≤ a + W ∧ a ≤ i ∧
      i ≤ b ∧ b ≤ n ∧ b ≤ i + W ∧ a + W ≤ b :=
    ⟨max 1 (i - W), min n (i + W), by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨B, hB, hsubB⟩ := exists_isBlock_superset
    (biconnectedIn_pair (hg.mem ha1 (by omega) : g a ∈ explorationSet _ u ℓ x₀ x₁)
      (hg.mem (by omega) (by omega) : g (a + 1) ∈ explorationSet _ u ℓ x₀ x₁)
      (hg.adj_G ha1 (by omega)))
  have hBa : g a ∈ B := hsubB (by simp)
  have hBa1 : g (a + 1) ∈ B := hsubB (by simp)
  have hstep : ∀ k, a ≤ k → k + 1 ≤ b → g k ∈ B ∧ g (k + 1) ∈ B := by
    intro k hak
    induction k, hak using Nat.le_induction with
    | base => exact fun _ => ⟨hBa, hBa1⟩
    | succ k hak ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨h2, hg.mem_block_succ hB (m := k) (by omega) (by omega) (fun hs => ?_) h1 h2⟩
      exact hnosep (k + 1) (by omega) hs ⟨by omega, by omega⟩
  have hmem : ∀ k, a ≤ k → k ≤ b → g k ∈ B := by
    intro k hak hkb
    rcases Nat.lt_or_ge k b with hlt | hge
    · exact (hstep k hak hlt).1
    · have e : b - 1 + 1 = k := by omega
      have := (hstep (b - 1) (by omega) (by omega)).2
      rwa [e] at this
  have hSk : ∀ k, a ≤ k → k ≤ b → g k ∈ g '' Set.Icc a b := fun k h1 h2 => ⟨k, ⟨h1, h2⟩, rfl⟩
  have hSB : g '' Set.Icc a b ⊆ B := by
    rintro _ ⟨k, ⟨hk1, hk2⟩, rfl⟩
    exact hmem k hk1 hk2
  have hfin : (g '' Set.Icc a b).Finite := (Set.finite_Icc a b).image g
  have hconn : IsConnectedSet _ (g '' Set.Icc a b) := by
    refine isConnectedSet_of_connectedIn (u := u) (ℓ := ℓ) (x₀ := x₀) (x₁ := x₁) _
      (connectedIn_iff.2 ?_)
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩ _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    rcases le_total p q with hpq | hpq
    · exact hg.reachIn_interval (by omega) hpq (by omega) fun k h1 h2 =>
        hSk k (by omega) (by omega)
    · exact (hg.reachIn_interval (by omega) hpq (by omega) fun k h1 h2 =>
        hSk k (by omega) (by omega)).symm
  have hxS : ∃ y ∈ g '' Set.Icc a b, y.val = (g i).val := ⟨g i, hSk i hai hib, rfl⟩
  classical
  have hTcard : W + 1 ≤ ((Finset.Icc a b).image fun k => (g k).val).card := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro k hk k' hk' hkk
      simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
      exact hg.eq_of_eq (by omega) (by omega) (by omega) (by omega) (Subtype.ext hkk)
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_far_pair hR hW hTcard
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hz
  rw [Finset.mem_Icc] at hk hk'
  have hfar : ∃ y ∈ g '' Set.Icc a b, ∃ z ∈ g '' Set.Icc a b, R ≤ l1 (y.val - z.val) :=
    ⟨g k, hSk k hk.1 hk.2, g k', hSk k' hk'.1 hk'.2, hyz⟩
  obtain ⟨γ, hγ1, hγ2⟩ := hE h _ hfin hconn hxS hfar
  exact hblocks B hB ⟨γ, fun j => ⟨(hγ1 j).1, hSB (hγ1 j).2⟩, hγ2⟩

end Window

end Rigidity.Proofs.Section5.Termination

namespace Rigidity.Proofs.Section5

/-- **step:5.27-terminate** (Step 6, L2641-2652): along an exploration path `γ` with
`|γ(end) - x₀|₁ ≥ W + 1` and `W ≥ 4 R²`, every good index lies within `W` of a separator index;
the good indices are therefore at most `(2 W + 1)` times the number of separator visits. -/
theorem terminationWindowStep : TerminationWindowStep := by
  intro ω h u ℓ x₀ x₁ Cf R W _h01 hR hW hblocks n γ hγ hl1
  obtain ⟨g, hg, hgγ⟩ := Termination.NatPath.of_isExplorationPath hγ
  have e : g n = γ (Fin.last n) := (congrArg g (Fin.val_last n).symm).trans (hgγ (Fin.last n))
  have hn : W + 1 ≤ n := by
    have h1 := hg.l1_le (j := n) le_rfl
    rw [e] at h1
    exact_mod_cast hl1.trans h1
  have hcount : goodCount ω Cf R γ ≤ (2 * W + 1) * separatorCount _ u ℓ x₀ x₁ γ := by
    refine Termination.card_le_of_window_cover fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hi0, hiE⟩ := hi
    have hi1 : 1 ≤ (i : ℕ) := Nat.pos_of_ne_zero fun h0 => hi0 (Fin.ext h0)
    rw [← hgγ i] at hiE
    obtain ⟨j, hjn, hjsep, hj1, hj2⟩ :=
      Termination.NatPath.exists_separator_window hg hR hW hblocks hn hi1
        (Nat.lt_succ_iff.1 i.2) hiE
    refine ⟨⟨j, Nat.lt_succ_of_le hjn⟩, ?_, hj1, hj2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hgγ ⟨j, Nat.lt_succ_of_le hjn⟩, ← e]
    exact hjsep
  exact_mod_cast hcount

end Rigidity.Proofs.Section5

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5 Classical

namespace Rigidity.Proofs.Section5.Assembly

section Tree

variable {β : Type*} {T : SimpleGraph β}

/-- A sequence of adjacent vertices, each a strict ancestor of the next one with respect to the
root `v 0`, is injective: the walk along the sequence is a path. -/
theorem injective_of_strictAncestor_chain (v : ℕ → β) (hadj : ∀ j, T.Adj (v j) (v (j + 1)))
    (hanc : ∀ j, IsStrictAncestor T (v 0) (v j) (v (j + 1))) : Function.Injective v := by
  have hpath : ∀ m, (rayPrefix v hadj m).IsPath := by
    intro m
    induction m with
    | zero => exact SimpleGraph.Walk.IsPath.nil
    | succ m ih =>
      refine (SimpleGraph.Walk.concat_isPath_iff (hadj m)).2 ⟨ih, fun hmem => ?_⟩
      have hW' := ih.takeUntil hmem
      have hm := (hanc m).2 _ hW'
      have hne : v (m + 1) ≠ v m := (hanc m).1.symm
      have hnd := ih.support_nodup
      rw [← (rayPrefix v hadj m).take_spec hmem, SimpleGraph.Walk.support_append] at hnd
      exact (List.nodup_append.1 hnd).2.2 _ hm _
        (SimpleGraph.Walk.end_mem_tail_support_of_ne hne _) rfl
  intro a b hab
  have hnd := (hpath (a + b)).support_nodup
  rw [support_rayPrefix] at hnd
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 (by omega)) (List.mem_range.2 (by omega))
    hab

end Tree

section Cubes

/-- A cube of `ℤ²` is finite. -/
theorem finite_cubeAt_two (x : Vertex 2) (r : ℕ) : (cubeAt x r).Finite := by
  refine (Set.finite_Icc (x - fun _ => (r : ℤ)) (x + fun _ => (r : ℤ))).subset fun y hy => ?_
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
  · have := abs_le.mp (hy i)
    simp only [Pi.sub_apply, Pi.add_apply]
    linarith

/-- An infinite set of vertices of a cluster is unbounded for the `l¹` distance to `x₀`. -/
theorem unbounded_of_infinite {ω : Configuration 2} {C : OpenComponent ω} {E : Set C}
    (hE : E.Infinite) (x₀ : C) : ∀ D : ℝ, ∃ y ∈ E, D ≤ l1 (y.val - x₀.val) := by
  intro D
  by_contra hcon
  push Not at hcon
  apply hE
  have hsub : Subtype.val '' E ⊆ cubeAt x₀.val ⌈D⌉₊ := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_cubeAt_of_l1_le ((hcon y hy).le.trans (Nat.le_ceil D))
  exact ((finite_cubeAt_two _ _).subset hsub).of_finite_image Subtype.val_injective.injOn

end Cubes

section Links

variable {ω : Configuration 2} (C : OpenComponent ω)

/-- The first two clauses of `GreedyPath`: the path `B 0 = B₀, c 1, B 1, c 2, …` of `𝒢_tree` going
down from the root, of length `N`, with incoming flux at least `i` at each cut-vertex. -/
structure Links (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁) (i : ℝ) (N : ℕ∞)
    (B : ℕ → ExplorationBlock C u ℓ x₀ x₁) (c : ℕ → ExplorationCut C u ℓ x₀ x₁) : Prop where
  root : B 0 = B₀
  link : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) ≤ N →
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inl (B k)) (.inr (c (k + 1))) ∧
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inr (c (k + 1))) (.inl (B (k + 1))) ∧
    i ≤ incomingFlux C ℓ (B k).val (c (k + 1)).val

/-- The set `E = ⋃_{k ≤ N} B k` of points of the blocks of the path. -/
def pathSet {u ℓ : C → ℝ} {x₀ x₁ : C} (N : ℕ∞) (B : ℕ → ExplorationBlock C u ℓ x₀ x₁) : Set C :=
  {y | ∃ k : ℕ, (k : ℕ∞) ≤ N ∧ y ∈ (B k).val}

/-- The sequence `B 0, c 1, B 1, c 2, …` of vertices of the block-cut tree. -/
def chain {u ℓ : C → ℝ} {x₀ x₁ : C} (B : ℕ → ExplorationBlock C u ℓ x₀ x₁)
    (c : ℕ → ExplorationCut C u ℓ x₀ x₁) :
    ℕ → BlockCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) :=
  fun n => if n % 2 = 0 then .inl (B (n / 2)) else .inr (c (n / 2 + 1))

end Links

section Chain

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}
  {B₀ : ExplorationBlock C u ℓ x₀ x₁} {i : ℝ} {N : ℕ∞}
  {B : ℕ → ExplorationBlock C u ℓ x₀ x₁} {c : ℕ → ExplorationCut C u ℓ x₀ x₁}

/-- The sequence `chain` starts with `B 0`. -/
theorem chain_zero : chain C B c 0 = .inl (B 0) := by simp [chain]

/-- The even terms of `chain` are the blocks. -/
theorem chain_even (k : ℕ) : chain C B c (2 * k) = .inl (B k) := by
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  simp [chain, h1, h2]

/-- The odd terms of `chain` are the cut-vertices. -/
theorem chain_odd (k : ℕ) : chain C B c (2 * k + 1) = .inr (c (k + 1)) := by
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [chain, h2]

/-- For an infinite path, the sequence `B 0, c 1, B 1, …` is a chain of strict ancestors in the
block-cut tree, hence injective. -/
theorem Links.injective_chain (hL : Links C u ℓ x₀ x₁ B₀ i ⊤ B c) :
    Function.Injective (chain C B c) := by
  have hadj : ∀ j, (blockCutTree C (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁)).Adj (chain C B c j) (chain C B c (j + 1)) ∧
      IsStrictAncestor (blockCutTree C (explorationGraph C u ℓ x₀ x₁)
        (explorationSet C u ℓ x₀ x₁)) (chain C B c 0) (chain C B c j) (chain C B c (j + 1)) := by
    intro j
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · obtain ⟨h1, -, -⟩ := hL.link k le_top
      rw [chain_zero, hL.root, chain_even, chain_odd]
      exact ⟨h1.2.2.1, h1.2.2.2⟩
    · obtain ⟨-, h2, -⟩ := hL.link k le_top
      rw [chain_zero, hL.root, chain_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, chain_even]
      exact ⟨h2.2.2.1, h2.2.2.2⟩
  exact injective_of_strictAncestor_chain _ (fun j => (hadj j).1) fun j => (hadj j).2

end Chain

section Path

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}
  {B₀ : ExplorationBlock C u ℓ x₀ x₁} {i : ℝ} {N : ℕ∞}
  {B : ℕ → ExplorationBlock C u ℓ x₀ x₁} {c : ℕ → ExplorationCut C u ℓ x₀ x₁}

/-- The cut-vertex `c (k + 1)` lies in the block `B k` before it. -/
theorem Links.mem_left (hL : Links C u ℓ x₀ x₁ B₀ i N B c) {k : ℕ}
    (hk : ((k + 1 : ℕ) : ℕ∞) ≤ N) : (c (k + 1)).val ∈ (B k).val :=
  (hL.link k hk).1.2.2.1

/-- The cut-vertex `c (k + 1)` lies in the block `B (k + 1)` after it. -/
theorem Links.mem_right (hL : Links C u ℓ x₀ x₁ B₀ i N B c) {k : ℕ}
    (hk : ((k + 1 : ℕ) : ℕ∞) ≤ N) : (c (k + 1)).val ∈ (B (k + 1)).val :=
  (hL.link k hk).2.1.2.2.1

/-- The points of the blocks of the path lie in `𝒢`. -/
theorem pathSet_subset : pathSet C N B ⊆ explorationSet C u ℓ x₀ x₁ := by
  rintro y ⟨k, -, hy⟩
  exact (B k).property.1.1 hy

/-- `ℓ(c t) ≥ ℓ(x₁) + t i / 4` along the path: `ℓ` grows by a quarter of the incoming flux across
each block. -/
theorem Links.growth (hL : Links C u ℓ x₀ x₁ B₀ i N B c) (hFG : FluxGrowth C u ℓ x₀ x₁ B₀) :
    ∀ s : ℕ, ((s + 1 : ℕ) : ℕ∞) ≤ N →
      ℓ x₁ + ((s + 1 : ℕ) : ℝ) * i / 4 ≤ ℓ (c (s + 1)).val := by
  intro s
  induction s with
  | zero =>
    intro hs
    obtain ⟨h1, -, hi⟩ := hL.link 0 hs
    rw [hL.root] at h1 hi
    have := hFG.1 (c (0 + 1)) h1
    push_cast
    linarith
  | succ s ih =>
    intro hs
    have hs' : ((s + 1 : ℕ) : ℕ∞) ≤ N := le_trans (by exact_mod_cast Nat.le_succ _) hs
    obtain ⟨-, h2, -⟩ := hL.link s hs'
    obtain ⟨h3, -, hi⟩ := hL.link (s + 1) hs
    have := hFG.2 (B (s + 1)) (c (s + 1)) (c (s + 1 + 1)) h2 h3
    have h4 := ih hs'
    push_cast at h4 ⊢
    linarith

/-- Away from the separator `s`, every point of the blocks `B 0, …, B k` is joined to `x₁` in
`𝒢 \ {s}`, if `s` is none of `c 1, …, c k`. -/
theorem Links.reach (hL : Links C u ℓ x₀ x₁ B₀ i N B c) (hx₁ : x₁ ∈ B₀.val) (s : C) (hsx : s ≠ x₁) :
    ∀ k : ℕ, (k : ℕ∞) ≤ N → (∀ t, 1 ≤ t → t ≤ k → s ≠ (c t).val) →
      ∀ z ∈ (B k).val, z ≠ s →
        GraphReachIn (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁ \ {s}) x₁ z := by
  intro k
  induction k with
  | zero =>
    intro _ _ z hz hzs
    rw [hL.root] at hz
    have hc := connectedIn_iff.1 (BiconnectedIn.connectedIn_diff B₀.property.1 s)
    exact (hc x₁ ⟨hx₁, fun h => hsx h.symm⟩ z ⟨hz, hzs⟩).mono
      (Set.sdiff_subset_sdiff_left B₀.property.1.1)
  | succ k ih =>
    intro hk hs z hz hzs
    have hk' : (k : ℕ∞) ≤ N := le_trans (by exact_mod_cast Nat.le_succ _) hk
    have hmem := hL.mem_left hk
    have hcs : (c (k + 1)).val ≠ s := (hs (k + 1) le_add_self le_rfl).symm
    have h1 := ih hk' (fun t h1 h2 => hs t h1 (by omega)) _ hmem hcs
    have hc := connectedIn_iff.1 (BiconnectedIn.connectedIn_diff (B (k + 1)).property.1 s)
    have h2 := (hc _ ⟨hL.mem_right hk, hcs⟩ z ⟨hz, hzs⟩).mono
      (Set.sdiff_subset_sdiff_left (B (k + 1)).property.1.1)
    exact h1.trans h2

/-- A point of `𝒢` separating `x₁` from a point `y` of the block `B k` is one of
`c 1, …, c k`. -/
theorem Links.separator_mem (hL : Links C u ℓ x₀ x₁ B₀ i N B c) (hx₁ : x₁ ∈ B₀.val) {k : ℕ}
    (hk : (k : ℕ∞) ≤ N) {y : C} (hy : y ∈ (B k).val) {s : C}
    (hs : s ∈ separators C u ℓ x₀ x₁ y) : ∃ t, 1 ≤ t ∧ t ≤ k ∧ s = (c t).val := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hsx, hsy, hall⟩ := hs
  obtain ⟨q, hq⟩ := hL.reach hx₁ s hsx k hk (fun t h1 h2 => hcon t h1 h2) y hy (Ne.symm hsy)
  exact (hq s (hall q)).2 (Set.mem_singleton s)

/-- The bound of the first clause of `ExplorationConclusion` for a point of the block `B k`. -/
theorem Links.bound (hL : Links C u ℓ x₀ x₁ B₀ i N B c) (hFG : FluxGrowth C u ℓ x₀ x₁ B₀)
    (hx₁ : x₁ ∈ B₀.val) (h01 : ℓ x₀ < ℓ x₁) {k : ℕ} (hk : (k : ℕ∞) ≤ N) {y : C}
    (hy : y ∈ (B k).val) {n : ℕ} {γ : Fin (n + 1) → C} (hγ : IsExplorationPath C u ℓ x₀ x₁ γ)
    (hlast : γ (Fin.last n) = y) :
    i / 4 * (separatorCount C u ℓ x₀ x₁ γ : ℝ) ≤ ℓ y - ℓ x₀ := by
  have hyV : y ∈ explorationSet C u ℓ x₀ x₁ := (B k).property.1.1 hy
  have hy1 : ℓ x₁ ≤ ℓ y := le_of_mem_explorationSet C hyV
  have hmono : Monotone (ℓ ∘ γ) := (hγ.strictMono h01).monotone
  have hinj : Function.Injective γ := (hγ.strictMono h01).injective.of_comp
  by_cases hi : i ≤ 0
  · have : i / 4 * (separatorCount C u ℓ x₀ x₁ γ : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  push Not at hi
  set J : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun j => γ j ∈ separators C u ℓ x₀ x₁ (γ (Fin.last n)) with hJ
  have hcard : separatorCount C u ℓ x₀ x₁ γ = J.card := rfl
  have hsep : ∀ j ∈ J, ∃ t, 1 ≤ t ∧ t ≤ k ∧ γ j = (c t).val := by
    intro j hj
    obtain ⟨t, h1, h2, h3⟩ := hL.separator_mem hx₁ hk hy (hlast ▸ (Finset.mem_filter.1 hj).2)
    exact ⟨t, h1, h2, h3⟩
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · rw [hcard, hJe]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
    linarith
  choose! tt htt using hsep
  obtain ⟨j, hjJ, hjmax⟩ := Finset.exists_max_image J tt hJne
  have hinjOn : Set.InjOn tt J := by
    intro a ha b hb hab
    apply hinj
    rw [(htt a ha).2.2, (htt b hb).2.2, hab]
  have hcardle : J.card ≤ tt j := by
    calc J.card = (J.image tt).card := (Finset.card_image_of_injOn hinjOn).symm
      _ ≤ (Finset.Icc 1 (tt j)).card := by
        refine Finset.card_le_card fun t ht => ?_
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
        exact Finset.mem_Icc.2 ⟨(htt a ha).1, hjmax a ha⟩
      _ = tt j := by simp
  obtain ⟨h1, h2, h3⟩ := htt j hjJ
  obtain ⟨s, hs⟩ : ∃ s, tt j = s + 1 := ⟨tt j - 1, by omega⟩
  have hsN : ((s + 1 : ℕ) : ℕ∞) ≤ N := by
    refine le_trans ?_ hk
    rw [← hs]
    exact_mod_cast h2
  have hg := hL.growth hFG s hsN
  have hlj : ℓ (c (tt j)).val ≤ ℓ y := by
    have := hmono (Fin.le_last j)
    rw [Function.comp_apply, Function.comp_apply, hlast, h3] at this
    exact this
  rw [hs] at hlj hcardle
  have hcast : (J.card : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast hcardle
  have hmul : i / 4 * (J.card : ℝ) ≤ i / 4 * ((s + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hcast (by linarith)
  have hring : ((s + 1 : ℕ) : ℝ) * i / 4 = i / 4 * ((s + 1 : ℕ) : ℝ) := by ring
  rw [hcard]
  linarith

/-- The block `B K` of the path is kept in `𝒢_tree`. -/
theorem Links.kept (hL : Links C u ℓ x₀ x₁ B₀ i N B c) {K : ℕ} (hK : (K : ℕ∞) ≤ N) :
    Sum.inl (B K) ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀) := by
  cases K with
  | zero =>
    rw [hL.root]
    exact (prunedRoot C u ℓ x₀ x₁ B₀).2
  | succ k =>
    exact (hL.link k hK).2.1.2.1

/-- An infinite path visits infinitely many cut-vertices, hence `E` is infinite. -/
theorem Links.infinite_top (hL : Links C u ℓ x₀ x₁ B₀ i ⊤ B c) : (pathSet C ⊤ B).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (c (k + 1)).val) ?_ ?_
  · intro a b hab
    have h : c (a + 1) = c (b + 1) := Subtype.ext hab
    have h2 : chain C B c (2 * a + 1) = chain C B c (2 * b + 1) := by
      rw [chain_odd, chain_odd, h]
    have := hL.injective_chain h2
    omega
  · intro k
    exact ⟨k, le_top, hL.mem_left le_top⟩

/-- The dichotomy of the second clause of `ExplorationConclusion`: a sensitive edge in `E`, or
`E` is infinite. -/
theorem Links.dichotomy (hL : Links C u ℓ x₀ x₁ B₀ i N B c)
    (hend : ∀ k : ℕ, (k : ℕ∞) = N → (¬ (B k).val.Finite ∨
      IsPruningBlock C u ℓ (u x₀) (B k).val ∨
      ∀ c' : ExplorationCut C u ℓ x₀ x₁, ¬ IsTreeChild C u ℓ x₀ x₁ B₀ (.inl (B k)) (.inr c')))
    (hLeaf : LeafSensitive C u ℓ x₀ x₁ B₀) :
    (∃ y ∈ pathSet C N B, ∃ z, IsSensitiveEdge C u ℓ y z) ∨ (pathSet C N B).Infinite := by
  rcases eq_or_ne N ⊤ with rfl | hN
  · exact Or.inr hL.infinite_top
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.1 hN
  by_cases hfin : (B K).val.Finite
  · left
    have hrest : IsPruningBlock C u ℓ (u x₀) (B K).val ∨
        ∀ c' : ExplorationCut C u ℓ x₀ x₁,
          ¬ IsTreeChild C u ℓ x₀ x₁ B₀ (.inl (B K)) (.inr c') := by
      rcases hend K hK with h | h
      · exact absurd hfin h
      · exact h
    obtain ⟨y, hy, z, hz⟩ := hLeaf (B K) (hL.kept hK.le) hfin hrest
    exact ⟨y, ⟨K, hK.le, hy⟩, z, hz⟩
  · right
    exact fun h => hfin (h.subset fun y hy => ⟨K, hK.le, hy⟩)

end Path

end Rigidity.Proofs.Section5.Assembly

namespace Rigidity.Proofs.Section5

/-- Step 6 (L2606-2627, L2655-2656) when `𝒢` has a cut-vertex: the union `E` of the blocks of a
path of `𝒢_tree` given by `Links`, ending as in `GreedyPath`, satisfies `ExplorationConclusion`. -/
theorem explorationConclusion_of_links {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ}
    {x₀ x₁ : C} (h01 : ℓ x₀ < ℓ x₁) {B₀ : ExplorationBlock C u ℓ x₀ x₁} (hx₁ : x₁ ∈ B₀.val)
    {i : ℝ} {N : ℕ∞} {B : ℕ → ExplorationBlock C u ℓ x₀ x₁} {c : ℕ → ExplorationCut C u ℓ x₀ x₁}
    (hL : Assembly.Links C u ℓ x₀ x₁ B₀ i N B c)
    (hend : ∀ k : ℕ, (k : ℕ∞) = N → (¬ (B k).val.Finite ∨
      IsPruningBlock C u ℓ (u x₀) (B k).val ∨
      ∀ c' : ExplorationCut C u ℓ x₀ x₁, ¬ IsTreeChild C u ℓ x₀ x₁ B₀ (.inl (B k)) (.inr c')))
    (hFG : FluxGrowth C u ℓ x₀ x₁ B₀) (hLeaf : LeafSensitive C u ℓ x₀ x₁ B₀) :
    ExplorationConclusion C u ℓ x₀ x₁ i := by
  refine ⟨Assembly.pathSet C N B, Assembly.pathSet_subset, ?_, ?_⟩
  · rintro y ⟨k, hk, hy⟩ n γ hγ hlast
    exact hL.bound hFG hx₁ h01 hk hy hγ hlast
  · rcases hL.dichotomy hend hLeaf with h | h
    · exact Or.inl h
    · exact Or.inr (Assembly.unbounded_of_infinite h x₀)

/-- **step:5.27-explore, Step 6** (L2606-2627, L2655-2656): the union `E` of the blocks of the
greedy path satisfies `ExplorationConclusion`. If `𝒢` has a cut-vertex this is
`explorationConclusion_of_links`. Otherwise the greedy path is the root block `B₀` alone (a link
would give a cut-vertex), no point of `𝒢` separates `x₁` from another (a separator is a
cut-vertex), and `B₀` is infinite, hence unbounded, or finite and a pruning block or without
child, so it carries a sensitive edge. -/
theorem explorationAssemblyStep : ExplorationAssemblyStep := by
  intro ω C u ℓ x₀ x₁ h01 hℓ hu B₀ hx₁ i hG hFG hLeaf
  obtain ⟨N, B, c, hB0, hlink, hend⟩ := hG
  by_cases hne : Nonempty (ExplorationCut C u ℓ x₀ x₁)
  · refine explorationConclusion_of_links hℓ hx₁ (c := fun k =>
      if hc : IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) (c k)
      then ⟨c k, hc⟩ else Classical.arbitrary _) ⟨hB0, fun k hk => ?_⟩ hend hFG hLeaf
    obtain ⟨hc, h1, h2, h3⟩ := hlink k hk
    simp only [dif_pos hc]
    exact ⟨h1, h2, h3⟩
  have hN : N = 0 := by
    by_contra hN0
    obtain ⟨hc, -⟩ := hlink 0 (by
      rw [Nat.zero_add, Nat.cast_one]
      exact Order.one_le_iff_ne_zero.2 hN0)
    exact hne ⟨⟨c 1, hc⟩⟩
  have hV : x₁ ∈ explorationSet C u ℓ x₀ x₁ := x₁_mem_explorationSet h01 hu
  have hsep : ∀ y ∈ explorationSet C u ℓ x₀ x₁, ∀ s, s ∉ separators C u ℓ x₀ x₁ y := by
    rintro y hy s ⟨hs1, hsy, hall⟩
    obtain ⟨w, hw⟩ := connectedIn_iff.1 (connectedIn_explorationSet hV) x₁ hV y hy
    refine hne ⟨⟨s, hw s (hall w), fun hcon => ?_⟩⟩
    obtain ⟨w', hw'⟩ := connectedIn_iff.1 hcon x₁ ⟨hV, fun h => hs1 h.symm⟩ y
      ⟨hy, fun h => hsy h.symm⟩
    exact (hw' s (hall w')).2 rfl
  refine ⟨B₀.val, B₀.2.1.1, fun y hy n γ _ hγy => ?_, ?_⟩
  · have hyV := B₀.2.1.1 hy
    have h0 : separatorCount C u ℓ x₀ x₁ γ = 0 := by
      unfold separatorCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      rw [hγy]
      exact hsep y hyV _
    rw [h0, Nat.cast_zero, mul_zero, sub_nonneg]
    exact hℓ.le.trans (le_of_mem_explorationSet C hyV)
  · have hend0 := hend 0 (by rw [hN, Nat.cast_zero])
    rw [hB0] at hend0
    by_cases hfin : B₀.val.Finite
    · exact Or.inl (hLeaf B₀ (prunedRoot C u ℓ x₀ x₁ B₀).2 hfin
        (hend0.resolve_left (not_not.2 hfin)))
    · exact Or.inr (Assembly.unbounded_of_infinite hfin x₀)

end Rigidity.Proofs.Section5

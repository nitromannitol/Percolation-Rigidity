import Rigidity.External.WellConnected

/-!
# A chemical-distance bound on the infinite cluster from well-connected cubes

The step `step:lip-in-A1` of Lemma 3.1 (paper L820 of the corrected draft) bounds the Euclidean
growth of a function which is Lipschitz for the graph (chemical) distance of the infinite cluster.
This needs a comparison of the chemical distance with the Euclidean distance; it is derived here
from Proposition 2.3 (`Rigidity.External.WellConnectedInput`).

In a well-connected cube `Q_N`, every cube `z + Q_M` of radius `M = ⌈N^δ/2⌉`, `δ = 1/(10d)²`,
centred in `Q_N` is a good subcube, with a largest cluster `𝒞_*(z + Q_M)`:
* a vertex `x` of an infinite cluster lies in `𝒞_*(x + Q_M)`, since the first `M` steps of an open
  path from `x` to infinity stay in `x + Q_M`;
* the clusters `𝒞_*(z + Q_M)` and `𝒞_*(z + e_j + Q_M)` meet, at a point of the first cluster on
  the face `{y_j = z_j + M}`, from which the cluster crosses the cube;
* two points of `𝒞_*(z + Q_M)` are joined by an open path of at most `(2M + 1)^d` steps.
Chaining along a lattice path of `|x - y|₁ ≤ 2dN` unit steps, two points of infinite clusters in
`Q_N` are at chemical distance at most `(2dN + 1)(2M + 1)^d`; we use the crude consequence
`(2d + 1) 4^d N^{3/2}`, which is subquadratic, hence enough for the growth condition of `A₁`.
By the Borel–Cantelli lemma, `Q_N` is well-connected for all large `N`, almost surely.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- A lattice step changes each coordinate by at most one. -/
theorem abs_coord_sub_le_one_of_adj {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y)
    (k : Fin d) : |y k - x k| ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := Graph.Zd.adj_iff.mp h <;> subst hi <;>
    by_cases hk : k = i <;> simp [unit, hk]

/-- After `i` steps of a lattice walk, each coordinate has moved by at most `i`. -/
theorem abs_getVert_sub_le {G : SimpleGraph (Vertex d)} (hG : G ≤ nearestNeighborGraph d)
    {a b : Vertex d} (p : G.Walk a b) (i : ℕ) (k : Fin d) :
    |p.getVert i k - a k| ≤ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    by_cases hi : i < p.length
    · have h1 := abs_coord_sub_le_one_of_adj (hG (p.adj_getVert_succ hi)) k
      calc |p.getVert (i + 1) k - a k|
          = |(p.getVert (i + 1) k - p.getVert i k) + (p.getVert i k - a k)| := by ring_nf
        _ ≤ |p.getVert (i + 1) k - p.getVert i k| + |p.getVert i k - a k| := abs_add_le _ _
        _ ≤ 1 + i := add_le_add h1 ih
        _ = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    · rw [p.getVert_of_length_le (by omega)]
      rw [p.getVert_of_length_le (by omega)] at ih
      exact ih.trans (by push_cast; omega)

/-- The open graph inside `B` is a subgraph of the open graph. -/
theorem openIn_le (ω : Configuration d) (B : Set (Vertex d)) : openIn ω B ≤ openGraph ω :=
  fun _ _ h => h.1

/-- A walk of open edges inside `B` that starts in `B` stays in `B`. -/
theorem mem_of_mem_support_openIn {ω : Configuration d} {B : Set (Vertex d)} {a b : Vertex d}
    (p : (openIn ω B).Walk a b) (ha : a ∈ B) : ∀ v ∈ p.support, v ∈ B := by
  induction p with
  | nil => simpa using ha
  | cons h q ih =>
    intro v hv
    rcases (SimpleGraph.Walk.mem_support_iff _).mp hv with rfl | hv
    · exact ha
    · exact ih h.2.2 v hv

/-- The cube `z + Q_r` as a finset. -/
noncomputable def cubeFinset (z : Vertex d) (r : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc (z i - r) (z i + r)

theorem mem_cubeFinset {z y : Vertex d} {r : ℕ} : y ∈ cubeFinset z r ↔ y ∈ cubeAt z r := by
  simp only [cubeFinset, Fintype.mem_piFinset, Finset.mem_Icc, cubeAt, Set.mem_setOf_eq, abs_le]
  exact forall_congr' fun i => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

theorem card_cubeFinset (z : Vertex d) (r : ℕ) : (cubeFinset z r).card = (2 * r + 1) ^ d := by
  rw [cubeFinset, Fintype.card_piFinset,
    Finset.prod_congr rfl (g := fun _ => 2 * r + 1) (fun i _ => by rw [Int.card_Icc]; omega)]
  simp

theorem finite_cubeAt (z : Vertex d) (r : ℕ) : (cubeAt z r).Finite :=
  (cubeFinset z r).finite_toSet.subset fun _ hy => mem_cubeFinset.mpr hy

/-- Two points joined by open edges inside `z + Q_r` are joined by an open path of fewer than
`(2r + 1)^d` steps. -/
theorem exists_walk_length_lt_of_reachable_openIn {ω : Configuration d} {z : Vertex d} {r : ℕ}
    {a b : Vertex d} (ha : a ∈ cubeAt z r) (h : (openIn ω (cubeAt z r)).Reachable a b) :
    ∃ p : (openGraph ω).Walk a b, p.length < (2 * r + 1) ^ d := by
  obtain ⟨w⟩ := h
  refine ⟨w.bypass.mapLe (openIn_le ω _), ?_⟩
  have hsub : w.bypass.support.toFinset ⊆ cubeFinset z r := fun v hv =>
    mem_cubeFinset.mpr (mem_of_mem_support_openIn _ ha v (List.mem_toFinset.mp hv))
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup w.bypass_isPath.support_nodup, SimpleGraph.Walk.length_support,
    card_cubeFinset] at hcard
  show (w.bypass.map _).length < _
  rw [SimpleGraph.Walk.length_map]
  omega

/-- `V` is a largest cluster `𝒞_*` witnessing that `z + Q_M` is a good subcube. -/
def IsGoodCluster (ω : Configuration d) (z : Vertex d) (M : ℕ) (V : Set (Vertex d)) : Prop :=
  IsLargestClusterIn ω (cubeAt z M) V ∧ CrossesCube z M V ∧
    ∀ (n : ℕ) (γ : Fin (n + 1) → Vertex d), Function.Injective γ →
      (∀ i : Fin n, (openIn ω (cubeAt z M)).Adj (γ i.castSucc) (γ i.succ)) →
      (M : ℝ) / 100 ≤ n → ∃ y ∈ V, (openIn ω (cubeAt z M)).Reachable (γ 0) y

theorem isGoodSubcube_iff {ω : Configuration d} {z : Vertex d} {M : ℕ} :
    IsGoodSubcube ω z M ↔ ∃ V, IsGoodCluster ω z M V := Iff.rfl

/-- A largest cluster of `B` is closed under open connections inside `B`. -/
theorem mem_of_reachable_of_isLargestClusterIn {ω : Configuration d} {B V : Set (Vertex d)}
    (hV : IsLargestClusterIn ω B V) {a y : Vertex d} (hy : y ∈ V)
    (h : (openIn ω B).Reachable a y) : a ∈ V := by
  obtain ⟨⟨x₀, _, rfl⟩, _⟩ := hV
  exact (show (openIn ω B).Reachable x₀ y from hy).trans h.symm

/-- Two points of a largest cluster of `B` are joined by open edges inside `B`. -/
theorem reachable_of_isLargestClusterIn {ω : Configuration d} {B V : Set (Vertex d)}
    (hV : IsLargestClusterIn ω B V) {a b : Vertex d} (ha : a ∈ V) (hb : b ∈ V) :
    (openIn ω B).Reachable a b := by
  obtain ⟨⟨x₀, _, rfl⟩, _⟩ := hV
  exact (show (openIn ω B).Reachable x₀ a from ha).symm.trans hb

/-- A largest cluster of `B` lies in `B`. -/
theorem subset_of_isLargestClusterIn {ω : Configuration d} {B V : Set (Vertex d)}
    (hV : IsLargestClusterIn ω B V) : V ⊆ B := by
  obtain ⟨⟨x₀, hx₀, rfl⟩, _⟩ := hV
  intro y ⟨w⟩
  exact mem_of_mem_support_openIn w hx₀ y w.end_mem_support

/-- The start of an open path of at least `M` steps whose first `M` steps stay in a good cube
`z + Q_M` lies in its largest cluster. -/
theorem mem_of_isGoodCluster_of_isPath {ω : Configuration d} {z : Vertex d} {M : ℕ}
    {V : Set (Vertex d)} (hV : IsGoodCluster ω z M V) {G : SimpleGraph (Vertex d)}
    (hG : G ≤ openGraph ω) {a b : Vertex d} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : M < p.length + 1) (hin : ∀ i ≤ M, p.getVert i ∈ cubeAt z M) : a ∈ V := by
  have hinj : Function.Injective fun i : Fin (M + 1) => p.getVert i := by
    intro i j hij
    exact Fin.ext (hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hij)
  obtain ⟨y, hy, hr⟩ := hV.2.2 M (fun i => p.getVert i) hinj
    (fun i => ⟨hG (p.adj_getVert_succ (by simp only [Fin.val_castSucc]; omega)),
      hin _ (by simp only [Fin.val_castSucc]; omega), hin _ (by simp only [Fin.val_succ]; omega)⟩)
    (div_le_self (Nat.cast_nonneg _) (by norm_num))
  simp only [Fin.val_zero, SimpleGraph.Walk.getVert_zero] at hr
  exact mem_of_reachable_of_isLargestClusterIn hV.1 hy hr

/-- A vertex of an infinite open cluster lies in the largest cluster of the good cube around it:
the first `M` steps of an open path from `x` to a vertex outside `x + Q_M` stay in the cube. -/
theorem mem_of_isGoodCluster_of_infinite {ω : Configuration d} {x : Vertex d} {M : ℕ}
    {V : Set (Vertex d)} (hV : IsGoodCluster ω x M V)
    (hx : ((openGraph ω).connectedComponentMk x).supp.Infinite) : x ∈ V := by
  obtain ⟨y, hy, hyB⟩ : ∃ y ∈ ((openGraph ω).connectedComponentMk x).supp, y ∉ cubeAt x M :=
    (hx.sdiff (finite_cubeAt x M)).nonempty
  have hr : (openGraph ω).Reachable x y :=
    (SimpleGraph.ConnectedComponent.eq.mp
      ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hy)).symm
  obtain ⟨w⟩ := hr
  have hcoord := abs_getVert_sub_le (openGraph_le ω) w.bypass
  refine mem_of_isGoodCluster_of_isPath hV le_rfl _ w.bypass_isPath ?_ ?_
  · by_contra hlen
    apply hyB
    intro k
    have := hcoord w.bypass.length k
    rw [SimpleGraph.Walk.getVert_length] at this
    exact this.trans (by omega)
  · intro i hi k
    exact (hcoord i k).trans (by exact_mod_cast hi)

/-- The largest clusters of the good cubes `z + Q_M` and `z + e_j + Q_M` meet: a point `y'` of the
first one on the face `{y_j = z_j + M}` starts an open path of the cluster to the opposite face,
whose first `M` steps stay in `z + e_j + Q_M`. -/
theorem exists_mem_inter_of_isGoodCluster {ω : Configuration d} {z : Vertex d} {M : ℕ}
    (hM : 1 ≤ M) (j : Fin d) {V V' : Set (Vertex d)} (hV : IsGoodCluster ω z M V)
    (hV' : IsGoodCluster ω (z + unit j) M V') : ∃ w ∈ V, w ∈ V' := by
  obtain ⟨⟨y, hy, hyj⟩, ⟨y', hy', hy'j⟩⟩ := hV.2.1 j
  obtain ⟨w⟩ := reachable_of_isLargestClusterIn hV.1 hy' hy
  have hcoord := abs_getVert_sub_le ((openIn_le ω _).trans (openGraph_le ω)) w.bypass
  have hlen : 2 * M ≤ w.bypass.length := by
    have := hcoord w.bypass.length j
    rw [SimpleGraph.Walk.getVert_length, hyj, hy'j, abs_le] at this
    omega
  refine ⟨y', hy', mem_of_isGoodCluster_of_isPath hV' (openIn_le ω _) w.bypass w.bypass_isPath
    (by omega) ?_⟩
  intro i hi k
  have hB := (w.bypass.adj_getVert_succ (show i < w.bypass.length by omega)).2.1 k
  have hj := hcoord i j
  rw [hy'j, abs_le] at hj
  rw [abs_le] at hB ⊢
  by_cases hkj : k = j
  · subst hkj
    simp only [Pi.add_apply, unit, Pi.single_eq_same]
    constructor <;> omega
  · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hkj, add_zero]
    exact hB

/-- Moving `z` one step closer to `w` in one coordinate lowers `|z - w|₁` by one. -/
theorem sum_natAbs_sub_succ {z z' w : Vertex d} (j : Fin d) (hz' : ∀ k ≠ j, z' k = z k)
    (hj : (z' j - w j).natAbs + 1 = (z j - w j).natAbs) :
    ∑ i, (z' i - w i).natAbs + 1 = ∑ i, (z i - w i).natAbs := by
  have he : ∑ k ∈ Finset.univ.erase j, (z' k - w k).natAbs =
      ∑ k ∈ Finset.univ.erase j, (z k - w k).natAbs :=
    Finset.sum_congr rfl fun k hk => by rw [hz' k (Finset.ne_of_mem_erase hk)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j), he]
  omega

/-- Chaining good cubes along a lattice path of `n` unit steps inside `c + Q_N`: a point of the
largest cluster of the first cube and a point of the largest cluster of the last one are joined by
an open path of at most `(n + 1)(2M + 1)^d` steps. -/
theorem exists_walk_of_isGoodCluster_chain {ω : Configuration d} {c : Vertex d} {N M : ℕ}
    (hM : 1 ≤ M) (V : Vertex d → Set (Vertex d))
    (hV : ∀ z ∈ cubeAt c N, IsGoodCluster ω z M (V z)) (n : ℕ) :
    ∀ z ∈ cubeAt c N, ∀ w ∈ cubeAt c N, ∑ i, (z i - w i).natAbs = n →
      ∀ a ∈ V z, ∀ b ∈ V w, ∃ p : (openGraph ω).Walk a b,
        p.length ≤ (n + 1) * (2 * M + 1) ^ d := by
  induction n with
  | zero =>
    intro z hz w _ hzw a ha b hb
    obtain rfl : z = w := funext fun i => by
      have := (Finset.sum_eq_zero_iff.mp hzw) i (Finset.mem_univ i)
      omega
    obtain ⟨p, hp⟩ := exists_walk_length_lt_of_reachable_openIn
      (subset_of_isLargestClusterIn (hV z hz).1 ha)
      (reachable_of_isLargestClusterIn (hV z hz).1 ha hb)
    exact ⟨p, by omega⟩
  | succ n ih =>
    intro z hz w hw hzw a ha b hb
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ w j := by
      by_contra hne
      push Not at hne
      simp [hne] at hzw
    obtain ⟨z', hz', ⟨e, he, he'⟩, hdist⟩ : ∃ z' ∈ cubeAt c N, (∃ e ∈ V z, e ∈ V z') ∧
        ∑ i, (z' i - w i).natAbs = n := by
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have hz'B : z + unit j ∈ cubeAt c N := fun k => by
          have h1 := hz k; have h2 := hw k
          rw [abs_le] at h1 h2 ⊢
          by_cases hkj : k = j
          · subst hkj; simp only [Pi.add_apply, unit, Pi.single_eq_same]; constructor <;> omega
          · simpa only [Pi.add_apply, unit, Pi.single_eq_of_ne hkj, add_zero] using h1
        refine ⟨z + unit j, hz'B,
          exists_mem_inter_of_isGoodCluster hM j (hV z hz) (hV _ hz'B), ?_⟩
        have := sum_natAbs_sub_succ (z := z) (z' := z + unit j) (w := w) j
          (fun k hkj => by simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hkj, add_zero])
          (by simp only [Pi.add_apply, unit, Pi.single_eq_same]; omega)
        omega
      · have hz'B : z - unit j ∈ cubeAt c N := fun k => by
          have h1 := hz k; have h2 := hw k
          rw [abs_le] at h1 h2 ⊢
          by_cases hkj : k = j
          · subst hkj; simp only [Pi.sub_apply, unit, Pi.single_eq_same]; constructor <;> omega
          · simpa only [Pi.sub_apply, unit, Pi.single_eq_of_ne hkj, sub_zero] using h1
        obtain ⟨e, he', he⟩ := exists_mem_inter_of_isGoodCluster hM j (hV _ hz'B)
          (by simpa only [sub_add_cancel] using hV z hz)
        refine ⟨z - unit j, hz'B, ⟨e, by simpa only [sub_add_cancel] using he, he'⟩, ?_⟩
        have := sum_natAbs_sub_succ (z := z) (z' := z - unit j) (w := w) j
          (fun k hkj => by simp only [Pi.sub_apply, unit, Pi.single_eq_of_ne hkj, sub_zero])
          (by simp only [Pi.sub_apply, unit, Pi.single_eq_same]; omega)
        omega
    obtain ⟨p, hp⟩ := exists_walk_length_lt_of_reachable_openIn
      (subset_of_isLargestClusterIn (hV z hz).1 ha)
      (reachable_of_isLargestClusterIn (hV z hz).1 ha he)
    obtain ⟨q, hq⟩ := ih z' hz' w hw hdist e he' b hb
    refine ⟨p.append q, ?_⟩
    rw [SimpleGraph.Walk.length_append]
    calc p.length + q.length ≤ (2 * M + 1) ^ d + (n + 1) * (2 * M + 1) ^ d :=
          Nat.add_le_add hp.le hq
      _ = (n + 1 + 1) * (2 * M + 1) ^ d := by ring

/-- In a well-connected cube `c + Q_N`, `N ≥ 1`, two vertices of infinite open clusters in the
cube are joined by an open path of at most `(2dN + 1)(2M + 1)^d` steps, `M = ⌈N^δ/2⌉`,
`δ = 1/(10d)²`: all the cubes `z + Q_M` centred in `c + Q_N` are good subcubes. -/
theorem exists_walk_of_isWellConnected {ω : Configuration d} {c : Vertex d} {N : ℕ}
    (hN : 1 ≤ N) (hwc : IsWellConnected ω c N) {x y : Vertex d} (hx : x ∈ cubeAt c N)
    (hy : y ∈ cubeAt c N) (hxi : ((openGraph ω).connectedComponentMk x).supp.Infinite)
    (hyi : ((openGraph ω).connectedComponentMk y).supp.Infinite) :
    ∃ p : (openGraph ω).Walk x y,
      p.length ≤ (2 * d * N + 1) * (2 * ⌈(N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2⌉₊ + 1) ^ d := by
  obtain ⟨hsmall, -, hgood⟩ := hwc
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hM : 1 ≤ ⌈(N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2⌉₊ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hMN : (⌈(N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2⌉₊ : ℝ) ≤ N / 10 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2 by positivity)
    linarith
  have hV : ∀ z ∈ cubeAt c N, ∃ V, IsGoodCluster ω z ⌈(N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2⌉₊ V :=
    fun z hz => hgood z _ (Nat.le_ceil _) hMN ⟨z, fun i => by simp, hz⟩
  choose! V hV using hV
  obtain ⟨p, hp⟩ := exists_walk_of_isGoodCluster_chain hM V hV _ x hx y hy rfl x
    (mem_of_isGoodCluster_of_infinite (hV x hx) hxi) y
    (mem_of_isGoodCluster_of_infinite (hV y hy) hyi)
  refine ⟨p, hp.trans (Nat.mul_le_mul_right _ ?_)⟩
  have hi : ∀ i, (x i - y i).natAbs ≤ 2 * N := fun i => by
    have h1 := hx i; have h2 := hy i
    rw [abs_le] at h1 h2
    omega
  calc ∑ i, (x i - y i).natAbs + 1 ≤ ∑ _i : Fin d, 2 * N + 1 :=
        Nat.add_le_add_right (Finset.sum_le_sum fun i _ => hi i) 1
    _ = 2 * d * N + 1 := by simp [Finset.sum_const]; ring

/-- The crude form `(2dN + 1)(2M + 1)^d ≤ (2d + 1) 4^d N^{3/2}` of the chaining bound, using
`2M + 1 ≤ N^δ + 3 ≤ 4 N^δ` and `δ d = 1/(100 d) ≤ 1/2`. -/
theorem chainBound_le [NeZero d] {N : ℕ} (hN : 1 ≤ N) :
    (((2 * d * N + 1) * (2 * ⌈(N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2⌉₊ + 1) ^ d : ℕ) : ℝ) ≤
      (2 * d + 1) * 4 ^ d * (N : ℝ) ^ (3 / 2 : ℝ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  set a := (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow hN' (by positivity)
  have hM : (2 * (⌈a / 2⌉₊ : ℝ) + 1) ≤ 4 * a := by
    have := Nat.ceil_lt_add_one (show 0 ≤ a / 2 by positivity)
    linarith
  have hpow : a ^ d ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    refine Real.rpow_le_rpow_of_exponent_le hN' ?_
    rw [mul_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h32 : (N : ℝ) ^ (3 / 2 : ℝ) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
  push_cast
  rw [h32]
  calc (2 * d * N + 1 : ℝ) * (2 * (⌈a / 2⌉₊ : ℝ) + 1) ^ d
      ≤ ((2 * d + 1) * N) * (4 * a) ^ d := by
        gcongr
        nlinarith
    _ = (2 * d + 1) * 4 ^ d * (N * a ^ d) := by rw [mul_pow]; ring
    _ ≤ (2 * d + 1) * 4 ^ d * (N * (N : ℝ) ^ (1 / 2 : ℝ)) := by gcongr

/-- A stretched exponential is summable over the integers. -/
theorem summable_exp_neg_mul_rpow {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    Summable fun N : ℕ => Real.exp (-(c * (N : ℝ) ^ s)) := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  have h := ((isLittleO_exp_neg_mul_rpow_atTop hc (-2 / s)).comp_tendsto hlim).isBigO
  refine summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num))
    (h.congr (fun N => by simp only [Function.comp, neg_mul]) (fun N => ?_))
  simp only [Function.comp]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  field_simp

/-- Borel–Cantelli: almost surely the cube `c + Q_N` is well-connected for all large `N`. -/
theorem ae_eventually_isWellConnected [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput)
    (c : Vertex d) : ∀ᵐ ω ∂latticeBondLaw d p, ∀ᶠ N in atTop, IsWellConnected ω c N := by
  obtain ⟨κ, K, s, hκ, hK, hs, hbound⟩ := hwc d hd p hpc hp1
  have hsum : ∑' N : ℕ, latticeBondLaw d p {ω | ¬ IsWellConnected ω c N} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun N => hbound c N)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity)
      ((summable_exp_neg_mul_rpow hκ hs).mul_left K)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  exact hω.mono fun N hN => by simpa using hN

/-- An open walk between two vertices of a component has length at least their distance in the
component. -/
theorem componentGraph_dist_le {ω : Configuration d} (C : OpenComponent ω) (x y : C)
    (q : (openGraph ω).Walk x y) : (componentGraph C).dist x y ≤ q.length := by
  classical
  have hq : ∀ v ∈ q.support, v ∈ C.supp := fun v hv =>
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
      ((SimpleGraph.ConnectedComponent.eq.mpr (q.takeUntil v hv).reachable.symm).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp x.2))
  have h := SimpleGraph.dist_le (q.induce C.supp hq)
  have hlen : (q.induce C.supp hq).length = q.length := by
    exact (SimpleGraph.Walk.length_map _ _).symm.trans
      (congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.map_induce q hq))
  exact hlen ▸ h

/-- **Chemical distance on the infinite cluster.** For `d ≥ 2` and `p_c(d) < p < 1`, almost surely
there is `N₀` such that for every `N ≥ N₀`, two vertices `x, y` of an infinite open cluster `C` in
the cube `Q_N` are at chemical distance `d_C(x, y) ≤ (2d + 1) 4^d N^{3/2}`. -/
theorem ae_componentDist_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ C : OpenComponent ω,
      C.supp.Infinite → ∀ x y : C, x.val ∈ cubeAt 0 N → y.val ∈ cubeAt 0 N →
        ((componentGraph C).dist x y : ℝ) ≤ (2 * d + 1) * 4 ^ d * (N : ℝ) ^ (3 / 2 : ℝ) := by
  filter_upwards [ae_eventually_isWellConnected hd hpc hp1 hwc 0] with ω hω
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hω
  refine ⟨max N₁ 1, fun N hN C hC x y hx hy => ?_⟩
  have hCx : (openGraph ω).connectedComponentMk x.val = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp x.2
  have hCy : (openGraph ω).connectedComponentMk y.val = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp y.2
  obtain ⟨q, hq⟩ := exists_walk_of_isWellConnected (le_of_max_le_right hN)
    (hN₁ N (le_of_max_le_left hN)) hx hy (by rw [hCx]; exact hC) (by rw [hCy]; exact hC)
  calc ((componentGraph C).dist x y : ℝ) ≤ q.length := by
        exact_mod_cast componentGraph_dist_le C x y q
    _ ≤ _ := by exact_mod_cast hq
    _ ≤ _ := chainBound_le (le_of_max_le_right hN)

end Rigidity.Proofs.S3

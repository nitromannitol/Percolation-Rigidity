import Rigidity.Proofs.Green.Cheeger
import Rigidity.Proofs.S3.ChemicalDistance

/-!
# Isoperimetry of an infinite cluster in a cube from good subcubes

Let `C` be an infinite open cluster and suppose that every cube `z + Q_M` with `z` in
`y + Q_{R+M+1}` is a good subcube, with chosen largest cluster `V_z`. If `ℤ^d` satisfies the
isoperimetric inequality `|F|^{(d-1)/d} ≤ |∂F|` (`LatticeIsoperimetry`), then every finite set
`A` of vertices of `C` inside `y + Q_R` has at least `|A|^{(d-1)/d} / (4 d (2M+1)^d)` boundary
edges in `C` (`isoperimetricOn_of_isGoodSubcube`).

The coarse graining uses the cubes `z + Q_M` for all `z`: every vertex `x` of `A` lies in `V_x`
(`Rigidity.Proofs.S3.mem_of_isGoodCluster_of_infinite`), and `V_z` meets `V_{z ± e_j}`
(`Rigidity.Proofs.S3.exists_mem_inter_of_isGoodCluster`). With `F` the set of `z` with
`∅ ≠ V_z ⊆ A` and `P` the set of `z` for which `V_z` meets `A` without lying in it,
* `|A| ≤ |F| + |P|`;
* for `z ∈ P` the cluster `V_z`, connected by open edges inside `z + Q_M`, has a boundary edge of
  `A` with inner vertex in `z + Q_M`, so `|P| ≤ (2M+1)^d |∂A|`;
* a lattice neighbour `w ∉ F` of `z ∈ F` lies in `P`, so `|∂F| ≤ 2d |P|`.
If `|F| ≤ |P|` then `|A|^{(d-1)/d} ≤ |A| ≤ 2|P|`; otherwise
`|A|^{(d-1)/d} ≤ 2 |F|^{(d-1)/d} ≤ 4d |P|`.
-/

open LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S3
open scoped Classical

namespace Rigidity.Green

variable {d : ℕ}

/-- The isoperimetric inequality of `ℤ^d` with constant one: a finite set `F` has at least
`|F|^{(d-1)/d}` boundary edges. -/
def LatticeIsoperimetry (d : ℕ) : Prop :=
  ∀ F : Finset (Vertex d),
    (F.card : ℝ) ^ (((d : ℝ) - 1) / d) ≤ edgeBoundaryCard (nearestNeighborGraph d) F

/-- The isoperimetric inequality survives lowering the constant. -/
theorem IsoperimetricOn.mono_const {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {B : Set V}
    {D κ κ' s₀ : ℝ} (h : IsoperimetricOn G B D κ s₀) (hκ : κ' ≤ κ) :
    IsoperimetricOn G B D κ' s₀ := fun U hU hs =>
  (mul_le_mul_of_nonneg_right hκ (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans (h U hU hs)

/-- The largest cluster chosen for a good subcube, and the empty set for other cubes. -/
noncomputable def goodCluster (ω : Configuration d) (z : Vertex d) (M : ℕ) : Set (Vertex d) :=
  if h : IsGoodSubcube ω z M then Classical.choose (isGoodSubcube_iff.mp h) else ∅

theorem isGoodCluster_goodCluster {ω : Configuration d} {z : Vertex d} {M : ℕ}
    (h : IsGoodSubcube ω z M) : IsGoodCluster ω z M (goodCluster ω z M) := by
  rw [goodCluster, dif_pos h]
  exact Classical.choose_spec (isGoodSubcube_iff.mp h)

theorem isGoodSubcube_of_nonempty {ω : Configuration d} {z : Vertex d} {M : ℕ}
    (h : (goodCluster ω z M).Nonempty) : IsGoodSubcube ω z M := by
  by_contra hg
  rw [goodCluster, dif_neg hg] at h
  exact Set.not_nonempty_empty h

theorem mem_cubeAt_comm {x z : Vertex d} {r : ℕ} : x ∈ cubeAt z r ↔ z ∈ cubeAt x r := by
  simp only [cubeAt, Set.mem_setOf_eq, abs_sub_comm]

theorem cubeAt_mono {x : Vertex d} {r s : ℕ} (h : r ≤ s) : cubeAt x r ⊆ cubeAt x s :=
  fun _ hy i => (hy i).trans (by exact_mod_cast h)

theorem mem_cubeAt_trans {x z y : Vertex d} {r s : ℕ} (hx : x ∈ cubeAt z r)
    (hz : z ∈ cubeAt y s) : x ∈ cubeAt y (s + r) := by
  intro i
  have h1 := hx i
  have h2 := hz i
  have := abs_sub_le (x i) (z i) (y i)
  push_cast
  linarith

/-- **Isoperimetry of an infinite cluster in `y + Q_R` from good subcubes of radius `M`.** -/
theorem isoperimetricOn_of_isGoodSubcube {ω : Configuration d} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (y : Vertex d) {R M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hgood : ∀ z ∈ cubeAt y (R + M + 1), IsGoodSubcube ω z M) (hLI : LatticeIsoperimetry d) :
    IsoperimetricOn (componentGraph C) {v | v.val ∈ cubeAt y R} d
      (1 / (4 * d * (2 * M + 1) ^ d)) 1 := by
  intro U hU hs
  set A : Set (Vertex d) := Subtype.val '' (↑U : Set C) with hA
  set Zp : Finset (Vertex d) := U.biUnion fun u => cubeFinset u.val M with hZp
  set F := Zp.filter fun z => (goodCluster ω z M).Nonempty ∧ goodCluster ω z M ⊆ A with hF
  set P := Zp.filter fun z => (goodCluster ω z M ∩ A).Nonempty ∧ ¬ goodCluster ω z M ⊆ A
    with hP
  have hUR : ∀ u ∈ U, u.val ∈ cubeAt y R := fun u hu => hU hu
  have hself : ∀ u ∈ U, u.val ∈ goodCluster ω u.val M := by
    intro u hu
    have hg := hgood u.val (cubeAt_mono (by omega) (hUR u hu))
    refine mem_of_isGoodCluster_of_infinite (isGoodCluster_goodCluster hg) ?_
    have hu2 : u.val ∈ C.supp := u.2
    rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hu2]
    exact hC
  have hcardU : U.card ≤ F.card + P.card := by
    have h1 : U.card ≤ (F ∪ P).card := by
      refine Finset.card_le_card_of_injOn (fun u => u.val) (by
        intro u hu
        have hZ : u.val ∈ Zp := Finset.mem_biUnion.mpr
          ⟨u, hu, mem_cubeFinset.mpr fun i => by simp⟩
        have hA' : u.val ∈ A := ⟨u, hu, rfl⟩
        by_cases hsub : goodCluster ω u.val M ⊆ A
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hZ, ⟨_, hself u hu⟩, hsub⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hZ, ⟨_, hself u hu, hA'⟩, hsub⟩))
        (fun u _ v _ h => Subtype.ext h)
    exact h1.trans (Finset.card_union_le _ _)
  have hE : edgeBoundaryCard (componentGraph C) U =
      ∑ u ∈ U, (((componentGraph C).neighborFinset u).filter (fun v => v ∉ U)).card := by
    unfold edgeBoundaryCard
    exact Finset.sum_congr rfl fun u _ => by congr
  have hP_edge : ∀ z ∈ P, ∃ u ∈ U, u.val ∈ cubeAt z M ∧
      1 ≤ (((componentGraph C).neighborFinset u).filter (fun v => v ∉ U)).card := by
    intro z hz
    obtain ⟨-, ⟨a, haV, haA⟩, hns⟩ := Finset.mem_filter.mp hz
    obtain ⟨b, hbV, hbA⟩ := Set.not_subset.mp hns
    have hV := isGoodCluster_goodCluster (isGoodSubcube_of_nonempty ⟨a, haV⟩)
    obtain ⟨w⟩ := reachable_of_isLargestClusterIn hV.1 haV hbV
    obtain ⟨dt, -, hd1, hd2⟩ := w.exists_boundary_dart A haA hbA
    obtain ⟨u, hu, hux⟩ := hd1
    have hadj := dt.adj
    have hopen : (openGraph ω).Adj u.val dt.snd := by rw [hux]; exact hadj.1
    have hsnd : dt.snd ∈ C.supp := by
      have hu2 : u.val ∈ C.supp := u.2
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu2 ⊢
      rw [← hu2]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hopen).symm
    refine ⟨u, hu, by rw [hux]; exact hadj.2.1, Finset.card_pos.mpr
      ⟨⟨dt.snd, hsnd⟩, Finset.mem_filter.mpr ⟨?_, fun hmem => hd2 ⟨_, hmem, rfl⟩⟩⟩⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact hopen
  have hPcard : P.card ≤ (2 * M + 1) ^ d * edgeBoundaryCard (componentGraph C) U := by
    set b : C → ℕ := fun u =>
      (((componentGraph C).neighborFinset u).filter (fun v => v ∉ U)).card with hb
    calc P.card = ∑ _z ∈ P, 1 := by simp
      _ ≤ ∑ z ∈ P, ∑ u ∈ U, if u.val ∈ cubeAt z M then b u else 0 := by
          refine Finset.sum_le_sum fun z hz => ?_
          obtain ⟨u, hu, huz, hbu⟩ := hP_edge z hz
          refine le_trans ?_ (Finset.single_le_sum (f := fun u : C =>
            if u.val ∈ cubeAt z M then b u else 0) (fun _ _ => Nat.zero_le _) hu)
          simp only [huz, if_true]
          exact hbu
      _ = ∑ u ∈ U, ∑ z ∈ P, if u.val ∈ cubeAt z M then b u else 0 := Finset.sum_comm
      _ ≤ ∑ u ∈ U, (2 * M + 1) ^ d * b u := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
          refine Nat.mul_le_mul_right _ ?_
          calc (P.filter fun z => u.val ∈ cubeAt z M).card ≤ (cubeFinset u.val M).card :=
                Finset.card_le_card fun z hz =>
                  mem_cubeFinset.mpr (mem_cubeAt_comm.mp (Finset.mem_filter.mp hz).2)
            _ = (2 * M + 1) ^ d := card_cubeFinset _ _
      _ = (2 * M + 1) ^ d * edgeBoundaryCard (componentGraph C) U := by
          rw [← Finset.mul_sum, hE]
  have hFP : ∀ z ∈ F, ∀ w, (nearestNeighborGraph d).Adj z w → w ∉ F → w ∈ P := by
    intro z hz w hzw hwF
    obtain ⟨hzZ, hne, hsub⟩ := Finset.mem_filter.mp hz
    obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.mp hzZ
    have hzy : z ∈ cubeAt y (R + M) := mem_cubeAt_trans (mem_cubeFinset.mp hzu) (hUR u hu)
    have hwy : w ∈ cubeAt y (R + M + 1) := by
      intro i
      have h1 := abs_coord_sub_le_one_of_adj hzw i
      have h2 := hzy i
      have := abs_sub_le (w i) (z i) (y i)
      push_cast at h2 ⊢
      linarith
    have hVz := isGoodCluster_goodCluster (isGoodSubcube_of_nonempty hne)
    have hVw := isGoodCluster_goodCluster (hgood w hwy)
    have hmeet : ∃ x ∈ goodCluster ω z M, x ∈ goodCluster ω w M := by
      obtain ⟨i, rfl | rfl⟩ := Graph.Zd.adj_iff.mp hzw
      · exact exists_mem_inter_of_isGoodCluster hM i hVz hVw
      · have hVz' : IsGoodCluster ω ((z - unit i) + unit i) M (goodCluster ω z M) := by
          simpa using hVz
        obtain ⟨x, hx1, hx2⟩ := exists_mem_inter_of_isGoodCluster hM i hVw hVz'
        exact ⟨x, hx2, hx1⟩
    obtain ⟨x, hxz, hxw⟩ := hmeet
    obtain ⟨u', hu', hu'x⟩ := hsub hxz
    have hwZ : w ∈ Zp := Finset.mem_biUnion.mpr ⟨u', hu', mem_cubeFinset.mpr (by
      rw [hu'x]; exact mem_cubeAt_comm.mp (subset_of_isLargestClusterIn hVw.1 hxw))⟩
    exact Finset.mem_filter.mpr ⟨hwZ, ⟨x, hxw, hsub hxz⟩,
      fun hwsub => hwF (Finset.mem_filter.mpr ⟨hwZ, ⟨x, hxw⟩, hwsub⟩)⟩
  have hFcard : edgeBoundaryCard (nearestNeighborGraph d) F ≤ 2 * d * P.card := by
    have hE' : edgeBoundaryCard (nearestNeighborGraph d) F = ∑ z ∈ F,
        (((nearestNeighborGraph d).neighborFinset z).filter (fun w => w ∉ F)).card := by
      unfold edgeBoundaryCard
      exact Finset.sum_congr rfl fun z _ => by congr
    rw [hE']
    calc ∑ z ∈ F, (((nearestNeighborGraph d).neighborFinset z).filter (fun w => w ∉ F)).card
        ≤ ∑ z ∈ F, ∑ w ∈ P, if (nearestNeighborGraph d).Adj z w then 1 else 0 := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [← Finset.card_filter]
          refine Finset.card_le_card fun w hw => ?_
          obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
          rw [SimpleGraph.mem_neighborFinset] at hw1
          exact Finset.mem_filter.mpr ⟨hFP z hz w hw1 hw2, hw1⟩
      _ = ∑ w ∈ P, ∑ z ∈ F, if (nearestNeighborGraph d).Adj z w then 1 else 0 :=
          Finset.sum_comm
      _ ≤ ∑ _w ∈ P, 2 * d := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← Finset.card_filter, ← Graph.Zd.degree_eq w,
            ← SimpleGraph.card_neighborFinset_eq_degree]
          refine Finset.card_le_card fun z hz => ?_
          rw [SimpleGraph.mem_neighborFinset]
          exact (Finset.mem_filter.mp hz).2.symm
      _ = 2 * d * P.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- the real inequality
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set r : ℝ := ((d : ℝ) - 1) / d with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr1 : r ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  set K : ℝ := (2 * (M : ℝ) + 1) ^ d with hK
  have hK1 : 1 ≤ K := one_le_pow₀ (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
  set e : ℝ := (edgeBoundaryCard (componentGraph C) U : ℝ) with he
  have he0 : 0 ≤ e := Nat.cast_nonneg _
  have haq : (U.card : ℝ) ≤ F.card + P.card := by exact_mod_cast hcardU
  have hqe : (P.card : ℝ) ≤ K * e := by
    have : ((P.card : ℕ) : ℝ) ≤ (((2 * M + 1) ^ d * edgeBoundaryCard (componentGraph C) U : ℕ) : ℝ) :=
      by exact_mod_cast hPcard
    push_cast at this
    exact this
  have hfr : (F.card : ℝ) ^ r ≤ 2 * d * P.card := by
    refine (hLI F).trans ?_
    exact_mod_cast hFcard
  have hKe : 0 ≤ K * e := mul_nonneg (by linarith) he0
  have hgoal : (U.card : ℝ) ^ r ≤ e * (4 * d * K) := by
    rcases le_or_gt (F.card : ℝ) P.card with hfq | hqf
    · have h1 : (U.card : ℝ) ^ r ≤ U.card := by
        simpa using Real.rpow_le_rpow_of_exponent_le hs hr1
      nlinarith
    · have h2 : (U.card : ℝ) ^ r ≤ (2 * F.card) ^ r :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) hr0
      rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at h2
      have h22 : (2 : ℝ) ^ r ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr1
      have hfr0 : 0 ≤ (F.card : ℝ) ^ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
      calc (U.card : ℝ) ^ r ≤ 2 ^ r * (F.card : ℝ) ^ r := h2
        _ ≤ 2 * (F.card : ℝ) ^ r := mul_le_mul_of_nonneg_right h22 hfr0
        _ ≤ 2 * (2 * d * P.card) := by linarith
        _ ≤ 2 * (2 * d * (K * e)) := by gcongr
        _ = e * (4 * d * K) := by ring
  have hpos : (0 : ℝ) < 4 * d * K := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  exact hgoal

end Rigidity.Green

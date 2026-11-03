import Rigidity.Steps.Section5.StrongMaxPrinciple
import Rigidity.Proofs.Section5.FiniteMaxPrinciple
import LatticeProb.Network.Escape
import LatticeProb.Network.VoltageConnected

/-! # Section 5: the recurrence barrier on a planar open component

Step `step:5.16-barrier` of Lemma 5.16 (paper L1964-1978 of the corrected draft). On an infinite
open component `C` of a planar
configuration, fix a vertex `a`, a point `x` and `ε > 0`. For `n` large, let `B = C ∩ [-n, n]²`
and let `e` be the equilibrium potential of `a` killed outside `B` (one at `a`, zero off `B`,
harmonic on `B \ {a}`). The barrier is `φ = 1 - e`.

The energy of `e` is `2 / R`, where `R` is the effective resistance from `a` to the complement
of `B`. Each edge carries at most the full energy, so `|e u - e v| ≤ (2 / R)^{1/2}` on every
edge, and along a fixed path from `a` to `x` of length `ℓ`, `φ x ≤ ℓ (2 / R)^{1/2}`. The boxes
`C ∩ [-(r₀ + k), r₀ + k]²` form a nested chain whose boundary cuts have at most
`8 (r₀ + k) + 8` pairs, so the series law (Nash-Williams) bounds `R` from below by a harmonic
sum, which diverges. -/

open LatticeProb.Percolation LatticeProb.Network LatticeProb.Graph

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-! ### Boxes of the plane -/

/-- The box `[-r, r]²` of the planar lattice as a finset. -/
noncomputable def planeBox (r : ℕ) : Finset (Vertex 2) :=
  Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r

theorem mem_planeBox {r : ℕ} {v : Vertex 2} :
    v ∈ planeBox r ↔ -(r : ℤ) ≤ v 0 ∧ v 0 ≤ r ∧ -(r : ℤ) ≤ v 1 ∧ v 1 ≤ r := by
  simp only [planeBox, Fintype.mem_piFinset, Finset.mem_Icc, Fin.forall_fin_two, and_assoc]

theorem planeBox_mono {r s : ℕ} (h : r ≤ s) : planeBox r ⊆ planeBox s := by
  intro v hv
  rw [mem_planeBox] at hv ⊢
  omega

theorem card_planeBox (r : ℕ) : (planeBox r).card = (2 * r + 1) ^ 2 := by
  rw [planeBox, Fintype.card_piFinset, Fin.prod_univ_two, Int.card_Icc, sq]
  congr 1 <;> omega

/-- The shell `[-(r+1), r+1]² \ [-r, r]²` has `8 r + 8` points. -/
theorem card_planeShell (r : ℕ) : (planeBox (r + 1) \ planeBox r).card = 8 * r + 8 := by
  rw [Finset.card_sdiff_of_subset (planeBox_mono (Nat.le_succ r)), card_planeBox,
    card_planeBox]
  rw [show (2 * (r + 1) + 1) ^ 2 = (2 * r + 1) ^ 2 + (8 * r + 8) by ring,
    Nat.add_sub_cancel_left]

/-- Two lattice neighbours differ by one in exactly one coordinate. -/
theorem planeAdj_cases {u v : Vertex 2} (h : (nearestNeighborGraph 2).Adj u v) :
    (u 0 = v 0 ∧ (u 1 = v 1 + 1 ∨ u 1 = v 1 - 1)) ∨
      (u 1 = v 1 ∧ (u 0 = v 0 + 1 ∨ u 0 = v 0 - 1)) := by
  have h1 := lattice_adj_iff_l1Dist.mp h
  simp only [latticeL1Dist, Fin.sum_univ_two] at h1
  rcases abs_cases (u 0 - v 0) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases abs_cases (u 1 - v 1) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> omega

/-- A point outside a box has at most one lattice neighbour inside it. -/
theorem eq_of_adj_of_not_mem_planeBox {r : ℕ} {u u' v : Vertex 2} (hu : u ∈ planeBox r)
    (hu' : u' ∈ planeBox r) (hv : v ∉ planeBox r) (h : (nearestNeighborGraph 2).Adj u v)
    (h' : (nearestNeighborGraph 2).Adj u' v) : u = u' := by
  rw [mem_planeBox] at hu hu' hv
  have c := planeAdj_cases h
  have c' := planeAdj_cases h'
  funext i
  fin_cases i <;> simp <;> omega

/-! ### Boxes of a component -/

/-- The finite piece `C ∩ [-r, r]²` of an open component. -/
noncomputable def compBox {ω : Configuration 2} (C : OpenComponent ω) (r : ℕ) : Finset C :=
  (planeBox r).preimage Subtype.val Subtype.val_injective.injOn

theorem mem_compBox {ω : Configuration 2} {C : OpenComponent ω} {r : ℕ} {y : C} :
    y ∈ compBox C r ↔ y.1 ∈ planeBox r :=
  Finset.mem_preimage

theorem compBox_mono {ω : Configuration 2} (C : OpenComponent ω) {r s : ℕ} (h : r ≤ s) :
    compBox C r ⊆ compBox C s := fun _ hy =>
  mem_compBox.mpr (planeBox_mono h (mem_compBox.mp hy))

theorem adj_of_componentGraph_adj {ω : Configuration 2} {C : OpenComponent ω} {y z : C}
    (h : (componentGraph C).Adj y z) : (nearestNeighborGraph 2).Adj y.1 z.1 :=
  openGraph_le ω h

/-- A neighbour of a point of `C ∩ [-r, r]²` lies in `C ∩ [-(r+1), r+1]²`. -/
theorem neighborFinset_subset_compBox {ω : Configuration 2} (C : OpenComponent ω) {r : ℕ}
    {y : C} (hy : y ∈ compBox C r) : (componentGraph C).neighborFinset y ⊆ compBox C (r + 1) := by
  intro z hz
  have c := planeAdj_cases (adj_of_componentGraph_adj ((SimpleGraph.mem_neighborFinset _ _ _).mp hz))
  have hy' := mem_planeBox.mp (mem_compBox.mp hy)
  rw [mem_compBox, mem_planeBox]
  push_cast
  omega

/-- The boundary cut of `C ∩ [-r, r]²` has at most `8 r + 8` pairs: the outer endpoint of a cut
pair lies in the shell `[-(r+1), r+1]² \ [-r, r]²` and determines the pair. -/
theorem card_cutPairs_compBox_le {ω : Configuration 2} (C : OpenComponent ω) (r : ℕ) :
    (cutPairs (componentGraph C) (compBox C r)).card ≤ 8 * r + 8 := by
  classical
  rw [← card_planeShell r]
  refine Finset.card_le_card_of_injOn (fun p => p.2.1) (fun p hp => ?_) (fun p hp p' hp' hpp => ?_)
  · obtain ⟨h1, h2, h3⟩ := mem_cutPairs.mp hp
    refine Finset.mem_sdiff.mpr ⟨?_, fun h => h2 (mem_compBox.mpr h)⟩
    have c := planeAdj_cases (adj_of_componentGraph_adj h3)
    have hy' := mem_planeBox.mp (mem_compBox.mp h1)
    rw [mem_planeBox]
    push_cast
    omega
  · obtain ⟨h1, h2, h3⟩ := mem_cutPairs.mp (Finset.mem_coe.mp hp)
    obtain ⟨h1', -, h3'⟩ := mem_cutPairs.mp (Finset.mem_coe.mp hp')
    have hv : p.2.1 = p'.2.1 := hpp
    have hv2 : p.2 = p'.2 := Subtype.ext hv
    have hadj' := adj_of_componentGraph_adj h3'
    rw [← hv] at hadj'
    have hv1 : p.1 = p'.1 := Subtype.ext (eq_of_adj_of_not_mem_planeBox (mem_compBox.mp h1)
      (mem_compBox.mp h1') (fun h => h2 (mem_compBox.mpr h)) (adj_of_componentGraph_adj h3)
      hadj')
    exact Prod.ext hv1 hv2

/-! ### Networks -/

section Network

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The boundary cut of a set containing the source of the killed Green function and contained
in its domain carries the unit current, so it is nonempty. -/
theorem cutPairs_card_pos [DecidableEq V] (hG : G.Connected) (C U : Finset V) {o q : V}
    (ho : o ∈ C) (hq : q ∉ C) (hoU : o ∈ U) (hUC : U ⊆ C) : 0 < (cutPairs G U).card := by
  by_contra hc
  have hempty : cutPairs G U = ∅ := Finset.card_eq_zero.mp (by omega)
  have hflux : (1 : ℝ) ≤ ∑ p ∈ cutPairs G U,
      current G (unitCond G) (killedGreenReal G (C : Set V) o) p.1 p.2 := by
    rw [← flux_eq_sum_cutPairs]
    refine le_of_eq (flux_eq_one isCond_unitCond _ U hoU ?_).symm
    intro x hx
    rw [netLaplacian_unitCond]
    by_cases hxo : x = o
    · subst hxo
      rw [if_pos rfl]
      exact laplacian_killedGreenReal_source hG C ho hq
    · rw [if_neg hxo, neg_zero]
      exact harmonic_killedGreenReal hG C ho hq (by exact_mod_cast hUC hx) hxo
  rw [hempty, Finset.sum_empty] at hflux
  linarith

/-- One edge term is bounded by the energy, when the edge starts in the index set. -/
theorem sq_sub_le_energyOn {S : Finset V} (f : V → ℝ) {u v : V} (hu : u ∈ S)
    (huv : G.Adj u v) : (f u - f v) ^ 2 ≤ energyOn G (unitCond G) S f := by
  classical
  rw [energyOn_eq_sum]
  have hterm : ∀ x ∈ S, ∀ y ∈ G.neighborFinset x, 0 ≤ unitCond G x y * (f x - f y) ^ 2 :=
    fun x _ y _ => mul_nonneg (by unfold unitCond; split_ifs <;> norm_num) (sq_nonneg _)
  calc (f u - f v) ^ 2 = unitCond G u v * (f u - f v) ^ 2 := by rw [unitCond, if_pos huv, one_mul]
    _ ≤ ∑ y ∈ G.neighborFinset u, unitCond G u y * (f u - f y) ^ 2 :=
      Finset.single_le_sum (hterm u hu) ((G.mem_neighborFinset u v).mpr huv)
    _ ≤ _ := Finset.single_le_sum (f := fun x => ∑ y ∈ G.neighborFinset x,
        unitCond G x y * (f x - f y) ^ 2) (fun x hx => Finset.sum_nonneg (hterm x hx)) hu

omit [G.LocallyFinite] in
/-- A function whose increments along the edges are at most `M` changes by at most
`length * M` along a walk. -/
theorem abs_sub_le_length_mul (f : V → ℝ) (M : ℝ) (h : ∀ u v, G.Adj u v → |f u - f v| ≤ M) :
    ∀ {u v : V} (w : G.Walk u v), |f u - f v| ≤ w.length * M
  | _, _, .nil => by simp
  | _, _, .cons hadj w => by
    rw [SimpleGraph.Walk.length_cons, Nat.cast_succ]
    calc |f _ - f _| ≤ |f _ - f _| + |f _ - f _| := abs_sub_le _ _ _
      _ ≤ M + w.length * M := add_le_add (h _ _ hadj) (abs_sub_le_length_mul f M h w)
      _ = _ := by ring

end Network

/-! ### The barrier -/

/-- Step `step:5.16-barrier`: on an infinite open component of a planar configuration, the
barrier `1 - e`, with `e` the equilibrium potential of `a` killed outside `C ∩ [-n, n]²`, is
at most `ε` at `x` for `n` large. -/
theorem recurrenceBarrier : RecurrenceBarrierStep := by
  classical
  intro ω C hC a x ε hε
  have hG : (componentGraph C).Connected := C.connected_toSimpleGraph
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, a ∈ compBox C r₀ :=
    ⟨(a.1 0).natAbs + (a.1 1).natAbs, mem_compBox.mpr (mem_planeBox.mpr (by
      have h0 := le_abs_self (a.1 0); have h0' := neg_abs_le (a.1 0)
      have h1 := le_abs_self (a.1 1); have h1' := neg_abs_le (a.1 1)
      push_cast; omega))⟩
  obtain ⟨w⟩ := hG.preconnected a x
  set δ : ℝ := ε / (w.length + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨L, hL⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_ge_atTop
    (16 * ((r₀ : ℝ) + 1) * (2 / δ ^ 2))).exists
  set Cn := compBox C (r₀ + L) with hCn
  obtain ⟨q, hq⟩ : ∃ q, q ∉ Cn := by
    by_contra h
    exact hC (Cn.finite_toSet.subset fun y _ =>
      Finset.mem_coe.mpr (by_contra fun hy => h ⟨y, hy⟩))
  have ha : a ∈ Cn := compBox_mono C (Nat.le_add_right r₀ L) hr₀
  have hRpos : 0 < effRes (componentGraph C) Cn a := effRes_pos hG Cn ha hq
  -- the series law along the boxes `C ∩ [-(r₀ + k), r₀ + k]²`
  have hNW := nashWilliams_upto hG Cn ha hq L (fun k => compBox C (r₀ + k))
    (fun k _ => compBox_mono C (Nat.le_add_right r₀ k) hr₀)
    (fun k hk => compBox_mono C (by omega))
    (fun k _ y hy => neighborFinset_subset_compBox C hy)
    (fun i j hij _ => compBox_mono C (by omega))
  have hterm : ∀ k ∈ Finset.range L, 1 / (8 * ((r₀ : ℝ) + 1)) * (1 / ((k : ℝ) + 1)) ≤
      1 / ((cutPairs (componentGraph C) (compBox C (r₀ + k))).card : ℝ) := by
    intro k hk
    have hk' : k < L := Finset.mem_range.mp hk
    have hpos : (0 : ℝ) < (cutPairs (componentGraph C) (compBox C (r₀ + k))).card := by
      exact_mod_cast cutPairs_card_pos hG Cn (compBox C (r₀ + k)) ha hq
        (compBox_mono C (Nat.le_add_right r₀ k) hr₀) (compBox_mono C (by omega))
    have hle : ((cutPairs (componentGraph C) (compBox C (r₀ + k))).card : ℝ) ≤
        8 * ((r₀ : ℝ) + 1) * ((k : ℝ) + 1) := by
      have h2 : ((cutPairs (componentGraph C) (compBox C (r₀ + k))).card : ℝ) ≤
          8 * ((r₀ + k : ℕ) : ℝ) + 8 := by exact_mod_cast card_cutPairs_compBox_le C (r₀ + k)
      push_cast at h2
      have h3 : (0 : ℝ) ≤ (r₀ : ℝ) * k := by positivity
      linarith
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le hpos hle
  have hR : 2 / δ ^ 2 ≤ effRes (componentGraph C) Cn a := by
    have h1 := (Finset.sum_le_sum hterm).trans hNW
    rw [← Finset.mul_sum] at h1
    have hr : (0 : ℝ) < 8 * ((r₀ : ℝ) + 1) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hr.le
    rw [← mul_assoc, mul_one_div_cancel hr.ne', one_mul] at h3
    have h5 : 16 * ((r₀ : ℝ) + 1) * (2 / δ ^ 2) ≤
        16 * ((r₀ : ℝ) + 1) * effRes (componentGraph C) Cn a := by linarith
    exact le_of_mul_le_mul_left h5 (by positivity)
  -- the increments of the equilibrium potential along the edges
  have hedge : ∀ u v, (componentGraph C).Adj u v →
      |equilibrium (componentGraph C) Cn a u - equilibrium (componentGraph C) Cn a v| ≤ δ := by
    intro u v huv
    by_cases hu : u ∈ nbhd (componentGraph C) Cn
    · have hsq := sq_sub_le_energyOn (killedGreenReal (componentGraph C) (Cn : Set C) a) hu huv
      rw [energyOn_killedGreenReal hG Cn ha hq] at hsq
      have heq : equilibrium (componentGraph C) Cn a u - equilibrium (componentGraph C) Cn a v
          = (killedGreenReal (componentGraph C) (Cn : Set C) a u
            - killedGreenReal (componentGraph C) (Cn : Set C) a v)
            / effRes (componentGraph C) Cn a := (sub_div _ _ _).symm
      refine abs_le_of_sq_le_sq ?_ hδ0.le
      rw [heq, div_pow, div_le_iff₀ (pow_pos hRpos 2)]
      have h2 : 2 ≤ effRes (componentGraph C) Cn a * δ ^ 2 :=
        (div_le_iff₀ (pow_pos hδ0 2)).mp hR
      have h4 := mul_le_mul_of_nonneg_left h2 hRpos.le
      nlinarith
    · have hu' : u ∉ Cn := fun h => hu (subset_nbhd Cn h)
      have hv' : v ∉ Cn := fun h => hu (mem_nbhd_of_adj h huv.symm)
      rw [equilibrium_eq_zero hG Cn ha hq hu', equilibrium_eq_zero hG Cn ha hq hv', sub_zero,
        abs_zero]
      exact hδ0.le
  refine ⟨(Cn : Set C), Cn.finite_toSet, fun y => 1 - equilibrium (componentGraph C) Cn a y,
    fun y => ?_, fun y hy => ?_, fun y hy hya => ?_, ?_⟩
  · have h1 : equilibrium (componentGraph C) Cn a y ≤ 1 := by
      show killedGreenReal (componentGraph C) (Cn : Set C) a y / effRes (componentGraph C) Cn a
        ≤ 1
      rw [div_le_one hRpos]
      exact killedGreenReal_le_diag hG Cn ha hq y
    linarith
  · show 1 ≤ 1 - equilibrium (componentGraph C) Cn a y
    rw [equilibrium_eq_zero hG Cn ha hq (fun h => hy (Finset.mem_coe.mpr h)), sub_zero]
  · have h0 := laplacian_equilibrium hG Cn ha hq (Finset.mem_coe.mp hy) hya
    rw [laplacian] at h0
    rw [componentLaplacian, ← neg_eq_zero, ← h0, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  · have hxa := abs_sub_le_length_mul _ δ hedge w
    rw [equilibrium_self hG Cn ha hq] at hxa
    have hlen : (w.length : ℝ) * δ ≤ ε := by
      rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    show 1 - equilibrium (componentGraph C) Cn a x ≤ ε
    linarith [le_abs_self (1 - equilibrium (componentGraph C) Cn a x)]

/-- Lemma 5.16 (the strong maximum principle on the planar infinite cluster), given the almost
sure uniqueness of the infinite cluster. -/
theorem strongMaxPrinciple_of_uniqueClusterAe {p : unitInterval} (hU : UniqueClusterAe p) :
    StrongMaxPrincipleStmt p :=
  strongMaxPrinciple_of_steps hU finiteMaxPrinciple recurrenceBarrier

end Rigidity.Proofs.Section5

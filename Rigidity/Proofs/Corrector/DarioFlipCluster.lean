import Rigidity.Proofs.Corrector.DarioCaseThreeAe
import Rigidity.Proofs.Corrector.DarioBondResampling

/-!
# Opening and closing one bond: the open graph, the Laplacian and the infinite cluster

For an oriented lattice edge `a = (x, i)` from `x` to `y = x + e_i`, with bond `e = edgeBond a`, the
configurations `ω^{e,1}` and `ω^{e,0}` of Dario's Step 2 differ only at `e`:

* `edgeOpen_setBond_iff_of_ne`: the edges other than `a` are open in both or in neither;
* `edgeDiv_edgeGrad_setBond`: the Laplacians differ by the edge `e`,
  `∇·∇u` for `ω^{e,1}` is `∇·∇u` for `ω^{e,0}` plus `(u(y) - u(x))(δ_x - δ_y)`;
* `ae_setBond`: an almost sure property holds almost surely for every `ω^{e,b}` (Bernoulli law,
  `0 < p < 1`);
* `mem_supp_iff_of_mem_supp_setBond_false`: if `x` and `y` are in the infinite cluster of
  `ω^{e,0}`, then the infinite clusters of `ω^{e,1}` and `ω^{e,0}` have the same vertices (Case 3).
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped Classical ENNReal

theorem lattice_adj_edgeHead (a : LatticeEdge) : (nearestNeighborGraph 2).Adj a.1 (edgeHead a) :=
  LatticeProb.Graph.Zd.adj_iff.2 ⟨a.2, Or.inl rfl⟩

/-- The bond of the oriented lattice edge `a`. -/
noncomputable def edgeBond (a : LatticeEdge) : Bond 2 := bondOfAdjacent (lattice_adj_edgeHead a)

theorem edgeOpen_iff (ω : Configuration 2) (a : LatticeEdge) :
    EdgeOpen ω a ↔ ω (edgeBond a) = true := by
  unfold EdgeOpen edgeBond
  rw [openGraph_adj_iff]
  exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨_, hh⟩⟩

theorem edgeBond_injective : Function.Injective edgeBond := by
  intro a a' h
  have h' : s(a.1, edgeHead a) = s(a'.1, edgeHead a') := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨x, i⟩ := a
    obtain ⟨x', i'⟩ := a'
    simp only at h1
    subst h1
    simp only [edgeHead, add_right_inj] at h2
    by_contra hne
    have hii : i ≠ i' := fun e => hne (by rw [e])
    exact add_unit_ne_add_unit (x := x) hii (by rw [h2])
  · exfalso
    simp only [edgeHead] at h1 h2
    rw [h1] at h2
    exact add_unit_add_unit_ne a'.1 a'.2 a.2 h2

theorem setBond_apply_ne {e e' : Bond 2} (h : e' ≠ e) (b : Bool) (ω : Configuration 2) :
    setBond e b ω e' = ω e' := by
  unfold setBond
  exact Function.update_of_ne h b ω

theorem edgeOpen_setBond_iff_of_ne {a a' : LatticeEdge} (h : a' ≠ a) (b : Bool)
    (ω : Configuration 2) : EdgeOpen (setBond (edgeBond a) b ω) a' ↔ EdgeOpen ω a' := by
  rw [edgeOpen_iff, edgeOpen_iff,
    setBond_apply_ne (fun e => h (edgeBond_injective e)) b ω]

theorem edgeOpen_setBond_self (a : LatticeEdge) (b : Bool) (ω : Configuration 2) :
    EdgeOpen (setBond (edgeBond a) b ω) a ↔ b = true := by
  rw [edgeOpen_iff, setBond, Function.update_self]

theorem sum_indicator_edge (a : LatticeEdge) (z : Vertex 2) :
    ∑ i : Fin 2, ((if (z, i) = a then (1 : ℝ) else 0) -
      (if (z - LatticeProb.unit i, i) = a then 1 else 0)) =
      (if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0) := by
  obtain ⟨x, j⟩ := a
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · rw [Finset.sum_eq_single j]
    · simp only [Prod.mk.injEq, and_true, edgeHead]
      congr 1
      exact propext sub_eq_iff_eq_add
    · intro i _ hij
      simp [hij]
    · intro h
      exact absurd (Finset.mem_univ j) h

/-- **The Laplacians of `ω^{e,1}` and `ω^{e,0}` differ by the edge `e`.** -/
theorem edgeDiv_edgeGrad_setBond (a : LatticeEdge) (u : Vertex 2 → ℝ) (ω : Configuration 2)
    (z : Vertex 2) :
    edgeDiv (setBond (edgeBond a) true ω) (edgeGrad (setBond (edgeBond a) true ω) u) z =
      edgeDiv (setBond (edgeBond a) false ω) (edgeGrad (setBond (edgeBond a) false ω) u) z +
        (u (edgeHead a) - u a.1) *
          ((if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0)) := by
  set ω₁ := setBond (edgeBond a) true ω
  set ω₀ := setBond (edgeBond a) false ω
  have ha1 : EdgeOpen ω₁ a := (edgeOpen_setBond_self a true ω).2 rfl
  have ha0 : ¬ EdgeOpen ω₀ a := fun h => by simpa using (edgeOpen_setBond_self a false ω).1 h
  have hterm : ∀ b : LatticeEdge, (if EdgeOpen ω₁ b then edgeGrad ω₁ u b else 0) =
      (if EdgeOpen ω₀ b then edgeGrad ω₀ u b else 0) +
        (if b = a then u (edgeHead a) - u a.1 else 0) := by
    intro b
    by_cases hb : b = a
    · subst hb
      simp [ha1, ha0, edgeGrad]
    · rw [if_neg hb, add_zero]
      have h1 := edgeOpen_setBond_iff_of_ne hb true ω
      have h0 := edgeOpen_setBond_iff_of_ne hb false ω
      have hiff : EdgeOpen ω₁ b ↔ EdgeOpen ω₀ b := h1.trans h0.symm
      by_cases hob : EdgeOpen ω₁ b
      · rw [if_pos hob, if_pos (hiff.1 hob)]
        simp [edgeGrad, hob, hiff.1 hob]
      · rw [if_neg hob, if_neg (fun h => hob (hiff.2 h))]
  unfold edgeDiv
  rw [← sum_indicator_edge a z, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm, hterm]
  split_ifs <;> ring

/-- **Almost sure properties survive forcing one bond**: for the Bernoulli law with `0 < p < 1`,
an almost sure property holds almost surely for every `ω^{e,b}`. -/
theorem ae_setBond {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {P : Configuration 2 → Prop} (h : ∀ᵐ ω ∂latticeBondLaw 2 p, P ω) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (e : Bond 2) (b : Bool), P (setBond e b ω) := by
  set N := toMeasurable (latticeBondLaw 2 p) {ω | ¬ P ω} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : latticeBondLaw 2 p N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 h
  have hsub : {ω | ¬ P ω} ⊆ N := subset_toMeasurable _ _
  have key : ∀ (e : Bond 2) (b : Bool), ∀ᵐ ω ∂latticeBondLaw 2 p, setBond e b ω ∉ N := by
    intro e b
    have hq : 0 < bondWeight p b := by
      unfold bondWeight
      split_ifs
      · exact hp0
      · linarith
    have hle := ofReal_bondWeight_mul_lintegral_setBond_le p
      (f := N.indicator fun _ => (1 : ℝ≥0∞)) ((measurable_const.indicator hNm)) e b
    rw [lintegral_indicator_const hNm, hN0, mul_zero] at hle
    have hzero : ∫⁻ ω, N.indicator (fun _ => (1 : ℝ≥0∞)) (setBond e b ω)
        ∂latticeBondLaw 2 p = 0 := by
      have hq' : ENNReal.ofReal (bondWeight p b) ≠ 0 := by simp [hq]
      exact (mul_eq_zero.1 (le_antisymm hle bot_le)).resolve_left hq'
    have hpre : (fun ω => N.indicator (fun _ => (1 : ℝ≥0∞)) (setBond e b ω)) =
        (setBond e b ⁻¹' N).indicator fun _ => 1 := by
      funext ω
      simp [Set.indicator_apply]
    rw [hpre, lintegral_indicator_const (hNm.preimage (measurable_setBond e b)), one_mul]
      at hzero
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hzero] with ω hω
    exact hω
  have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (e : Bond 2) (b : Bool), setBond e b ω ∉ N := by
    rw [ae_all_iff]
    intro e
    rw [ae_all_iff]
    exact key e
  filter_upwards [hall] with ω hω e b
  by_contra hP
  exact hω e b (hsub hP)

/-- Reachability in `ω^{e,1}` gives reachability in `ω^{e,0}` when the endpoints of `e` are joined
in `ω^{e,0}`. -/
theorem reachable_setBond_false_of_true {a : LatticeEdge} {ω : Configuration 2}
    (hxy : (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a)) {u v : Vertex 2}
    (huv : (openGraph (setBond (edgeBond a) true ω)).Reachable u v) :
    (openGraph (setBond (edgeBond a) false ω)).Reachable u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u' v' w' hadj p ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    obtain ⟨hl, hopen⟩ := (openGraph_adj_iff _ _ _).1 hadj
    by_cases he : bondOfAdjacent hl = edgeBond a
    · have hs : s(u', v') = s(a.1, edgeHead a) := congrArg Subtype.val he
      rcases Sym2.eq_iff.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        exact hxy
      · rw [h1, h2]
        exact hxy.symm
    · refine SimpleGraph.Adj.reachable ?_
      refine (openGraph_adj_iff _ _ _).2 ⟨hl, ?_⟩
      rw [setBond_apply_ne he] at hopen
      rw [setBond_apply_ne he]
      exact hopen

theorem openGraph_setBond_le (e : Bond 2) (ω : Configuration 2) :
    openGraph (setBond e false ω) ≤ openGraph (setBond e true ω) := by
  intro u v h
  obtain ⟨hl, hopen⟩ := (openGraph_adj_iff _ _ _).1 h
  refine (openGraph_adj_iff _ _ _).2 ⟨hl, ?_⟩
  by_cases he : bondOfAdjacent hl = e
  · rw [he, setBond, Function.update_self]
  · rw [setBond_apply_ne he] at hopen
    rw [setBond_apply_ne he]
    exact hopen

/-- **Case 3**: if the endpoints of `e` lie in the infinite cluster of `ω^{e,0}`, the infinite
clusters of `ω^{e,1}` and `ω^{e,0}` have the same vertices. -/
theorem mem_supp_iff_of_mem_supp_setBond_false {a : LatticeEdge} {ω : Configuration 2}
    (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
    (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
    (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
    (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) (z : Vertex 2) :
    z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp := by
  have hxy : (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy).symm)
  have hmono := openGraph_setBond_le (edgeBond a) ω
  have hsupp : ∀ u : Vertex 2,
      ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk u).supp ⊆
        ((openGraph (setBond (edgeBond a) true ω)).connectedComponentMk u).supp := by
    intro u w hw
    refine (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
      (SimpleGraph.ConnectedComponent.sound ?_)
    exact SimpleGraph.Reachable.mono hmono (SimpleGraph.ConnectedComponent.exact
      ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hw))
  rw [mem_uniqueInfiniteComponent_iff, mem_uniqueInfiniteComponent_iff]
  constructor
  · intro hz
    have hx0 : setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 :=
      (mem_uniqueInfiniteComponent_iff h₀ a.1).1 hx
    have hx1 : setBond (edgeBond a) true ω ∈ infiniteComponentEvent a.1 :=
      Set.Infinite.mono (hsupp a.1) hx0
    have hz1 : z ∈ (uniqueInfiniteComponent h₁).supp := (mem_uniqueInfiniteComponent_iff h₁ z).2 hz
    have hx1' : a.1 ∈ (uniqueInfiniteComponent h₁).supp :=
      (mem_uniqueInfiniteComponent_iff h₁ a.1).2 hx1
    have hzx : (openGraph (setBond (edgeBond a) true ω)).Reachable z a.1 :=
      SimpleGraph.ConnectedComponent.exact
        (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hz1).trans
          ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx1').symm)
    have hzx0 := reachable_setBond_false_of_true hxy hzx
    change ((openGraph _).connectedComponentMk z).supp.Infinite
    rw [SimpleGraph.ConnectedComponent.sound hzx0]
    exact hx0
  · intro hz
    exact Set.Infinite.mono (hsupp z) hz

end Rigidity.Corrector

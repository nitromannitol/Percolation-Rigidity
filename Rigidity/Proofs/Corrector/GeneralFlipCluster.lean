import Rigidity.Proofs.Corrector.GeneralCaseField
import Rigidity.Proofs.Corrector.GeneralFlipTerms

/-!
# Opening and closing one bond of `ℤᵈ`: the open graph, the Laplacian and the infinite cluster

For an oriented lattice edge `a = (x, i)` from `x` to `y = x + e_i`, with bond `e = edgeBond a`, the
configurations `ω^{e,1}` and `ω^{e,0}` of Dario's Step 2 differ only at `e`, as in the planar file
`DarioFlipCluster`:

* `edgeOpen_setBond_iff_of_ne`: the edges other than `a` are open in both or in neither;
* `edgeDiv_edgeGrad_setBond`: the Laplacians differ by the edge `e`,
  `∇·∇u` for `ω^{e,1}` is `∇·∇u` for `ω^{e,0}` plus `(u(y) - u(x))(δ_x - δ_y)`;
* `mem_supp_iff_of_mem_supp_setBond_false`: if `x` and `y` are in the infinite cluster of
  `ω^{e,0}`, then the infinite clusters of `ω^{e,1}` and `ω^{e,0}` have the same vertices (Case 3);
* `ae_correctedPlane_sub_eq_smul_greenProj`: Dario's (3.22) for the corrected planes, from the
  Liouville theorem (`ae_edgeGrad_eq_smul_greenProj_of_div`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ}

theorem lattice_adj_edgeHead (a : LatticeEdge d) : (nearestNeighborGraph d).Adj a.1 (edgeHead a) :=
  LatticeProb.Graph.Zd.adj_iff.2 ⟨a.2, Or.inl rfl⟩

/-- The bond of the oriented lattice edge `a`. -/
noncomputable def edgeBond (a : LatticeEdge d) : Bond d := bondOfAdjacent (lattice_adj_edgeHead a)

theorem edgeOpen_iff (ω : Configuration d) (a : LatticeEdge d) :
    EdgeOpen ω a ↔ ω (edgeBond a) = true := by
  unfold EdgeOpen edgeBond
  rw [openGraph_adj_iff]
  exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨_, hh⟩⟩

theorem edgeBond_injective : Function.Injective (edgeBond (d := d)) := by
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

theorem edgeOpen_setBond_iff_of_ne {a a' : LatticeEdge d} (h : a' ≠ a) (b : Bool)
    (ω : Configuration d) : EdgeOpen (setBond (edgeBond a) b ω) a' ↔ EdgeOpen ω a' := by
  rw [edgeOpen_iff, edgeOpen_iff,
    setBond_apply_ne (fun e => h (edgeBond_injective e)) b ω]

theorem edgeOpen_setBond_self (a : LatticeEdge d) (b : Bool) (ω : Configuration d) :
    EdgeOpen (setBond (edgeBond a) b ω) a ↔ b = true := by
  rw [edgeOpen_iff, setBond, Function.update_self]

theorem sum_indicator_edge (a : LatticeEdge d) (z : Vertex d) :
    ∑ i : Fin d, ((if (z, i) = a then (1 : ℝ) else 0) -
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
theorem edgeDiv_edgeGrad_setBond (a : LatticeEdge d) (u : Vertex d → ℝ) (ω : Configuration d)
    (z : Vertex d) :
    edgeDiv (setBond (edgeBond a) true ω) (edgeGrad (setBond (edgeBond a) true ω) u) z =
      edgeDiv (setBond (edgeBond a) false ω) (edgeGrad (setBond (edgeBond a) false ω) u) z +
        (u (edgeHead a) - u a.1) *
          ((if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0)) := by
  set ω₁ := setBond (edgeBond a) true ω
  set ω₀ := setBond (edgeBond a) false ω
  have ha1 : EdgeOpen ω₁ a := (edgeOpen_setBond_self a true ω).2 rfl
  have ha0 : ¬ EdgeOpen ω₀ a := fun h => by simpa using (edgeOpen_setBond_self a false ω).1 h
  have hterm : ∀ b : LatticeEdge d, (if EdgeOpen ω₁ b then edgeGrad ω₁ u b else 0) =
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

/-- Reachability in `ω^{e,1}` gives reachability in `ω^{e,0}` when the endpoints of `e` are joined
in `ω^{e,0}`. -/
theorem reachable_setBond_false_of_true {a : LatticeEdge d} {ω : Configuration d}
    (hxy : (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a)) {u v : Vertex d}
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

/-- **Case 3**: if the endpoints of `e` lie in the infinite cluster of `ω^{e,0}`, the infinite
clusters of `ω^{e,1}` and `ω^{e,0}` have the same vertices. -/
theorem mem_supp_iff_of_mem_supp_setBond_false {a : LatticeEdge d} {ω : Configuration d}
    (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
    (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
    (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
    (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) (z : Vertex d) :
    z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp := by
  have hxy : (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy).symm)
  have hmono := openGraph_setBond_le (edgeBond a) ω
  have hsupp : ∀ u : Vertex d,
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

/-- **Dario, (3.22), for the corrected planes**: almost surely, for every oriented edge `a = (x, i)`
with bond `e`, if `x` and `y = x + e_i` are in the infinite cluster of `ω^{e,0}`, then for corrected
planes `ℓ₁` of `ω^{e,1}` and `ℓ₀` of `ω^{e,0}` of the same slope and every open edge `b` of the
cluster, `∇(ℓ₁ - ℓ₀)(b) = (ℓ₀(x) - ℓ₀(y)) (greenProj ω^{e,1} (1_a))(b)`. -/
theorem ae_correctedPlane_sub_eq_smul_greenProj [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ a : LatticeEdge d,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
        (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
        (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp)
        (q : Fin d → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
        (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
        IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
        IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
        ∀ b : LatticeEdge d, EdgeOpen (setBond (edgeBond a) true ω) b →
          b.1 ∈ (uniqueInfiniteComponent h₁).supp →
          (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₁ b.1) -
              (extendComp _ ℓ₀ (edgeHead b) - extendComp _ ℓ₀ b.1) =
            (ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) *
              greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1) b := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 (ae_edgeGrad_eq_smul_greenProj_of_div hd hpc hp1)] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ b hb hb1
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  have ha : EdgeOpen (setBond (edgeBond a) true ω) a := (edgeOpen_setBond_self a true ω).2 rfl
  have hdiv : ∀ z ∈ (uniqueInfiniteComponent h₁).supp,
      edgeDiv (setBond (edgeBond a) true ω) (edgeGrad (setBond (edgeBond a) true ω)
        (fun z => extendComp _ ℓ₁ z - 1 * extendComp _ ℓ₀ z)) z =
      (ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) *
        ((if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0)) := by
    intro z hz
    rw [edgeDiv_edgeGrad_sub_smul, edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₁.1.1 hz,
      edgeDiv_edgeGrad_setBond,
      edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₀.1.1 ((hC z).1 hz),
      extendComp_of_mem _ ℓ₀ hx, extendComp_of_mem _ ℓ₀ hy]
    ring
  have hsub : SublinearOn (uniqueInfiniteComponent h₁).supp
      (fun z => extendComp _ ℓ₁ z - 1 * extendComp _ ℓ₀ z) := by
    have h1 := sublinearOn_of_componentSlopeAsymptotics _ hℓ₁.2
    have h0 := sublinearOn_of_componentSlopeAsymptotics _ hℓ₀.2
    have h0' : SublinearOn (uniqueInfiniteComponent h₁).supp
        (fun z => extendComp _ ℓ₀ z - ∑ i, q i * (z i : ℝ)) := fun ε hε => by
      obtain ⟨R, hR⟩ := h0 ε hε
      exact ⟨R, fun z hz => hR z ((hC z).1 hz)⟩
    have h2 := h1.sub_smul h0' 1
    intro ε hε
    obtain ⟨R, hR⟩ := h2 ε hε
    refine ⟨R, fun z hz hRz => ?_⟩
    have h3 := hR z hz hRz
    convert h3 using 2
    ring
  have key := hω (edgeBond a) true h₁ _ a.1 (edgeHead a) (edgeDiv_single _ ha) _ _ hdiv hsub b hb hb1
  simp only [edgeGrad, if_pos hb] at key
  rw [← key]
  ring

end Rigidity.Corrector.GeneralDim

import Rigidity.Steps.Section5.GradientTrichotomy
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable
import Rigidity.Proofs.Section5.SublinearLiouville

/-!
# Proposition 5.7, Step 2: the deterministic flip steps

Proofs of the three deterministic steps of `step:5.7-flip` (corrected draft L1797-1812), carved in
`Rigidity/Steps/Section5/GradientTrichotomy.lean`.

* `flipShrinkStep`: closing an edge `ab` of `𝒞_∞` that changes the vertex set of the infinite
  cluster disconnects a finite open cluster `F ∋ a` (or `∋ b`); summing `-Δu = f` over `F`, only
  the closed edge contributes, so `Σ_F f = u(a) - u(b)` and the mass on the new cluster is
  `-(u(a) - u(b)) ≠ 0`.
* `flipIdentityStep`: if the vertex set is kept, `ℓ - ℓ' - ∇ℓ'(ab) (G(·, a) - G(·, b))` is harmonic
  and of sublinear growth on `𝒞_∞`, hence constant (Liouville at order zero); the identity
  follows from the symmetry of `H = G - κ` and `Σ f = 0`.
* `flipGradientStep`: if `ℓ'(a) = ℓ'(b)`, `ℓ'` is harmonic on `𝒞_∞`, so `ℓ - ℓ'` is constant.

The basic facts: closing the open edge `ab` removes exactly that edge
(`openGraph_flipAt_adj_iff`), which changes the Laplacian only at `a` and `b`
(`laplacian_eq_of_flip`); the Laplacian sums to zero over a finite set closed under adjacency
(`sum_laplacian_eq_zero`).
-/

open LatticeProb LatticeProb.Percolation Filter Topology

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

section Flip

variable {ω ω' : Configuration 2} {a b : Vertex 2}

/-- Closing the open edge `ab` removes exactly that edge from the open graph. -/
theorem openGraph_flipAt_adj_iff (hab : (openGraph ω).Adj a b) (x y : Vertex 2) :
    (openGraph (flipAt s(a, b) ω)).Adj x y ↔ (openGraph ω).Adj x y ∧ s(x, y) ≠ s(a, b) := by
  obtain ⟨hab', hω⟩ := hab
  constructor
  · rintro ⟨hxy, hω'⟩
    have hne : s(x, y) ≠ s(a, b) := by
      intro heq
      have hbond : bondOfAdjacent hxy = bondOfAdjacent hab' := Subtype.ext heq
      have h1 : flipAt s(a, b) ω (bondOfAdjacent hxy) = !ω (bondOfAdjacent hxy) := if_pos heq
      rw [h1, hbond, hω] at hω'
      exact Bool.false_ne_true hω'
    have h1 : flipAt s(a, b) ω (bondOfAdjacent hxy) = ω (bondOfAdjacent hxy) := if_neg hne
    exact ⟨⟨hxy, h1 ▸ hω'⟩, hne⟩
  · rintro ⟨⟨hxy, hω''⟩, hne⟩
    have h1 : flipAt s(a, b) ω (bondOfAdjacent hxy) = ω (bondOfAdjacent hxy) := if_neg hne
    exact ⟨hxy, h1 ▸ hω''⟩

/-- Removing one edge `ab` changes the Laplacian only at `a` and `b`. -/
theorem laplacian_eq_of_flip (hab : (openGraph ω).Adj a b)
    (hflip : ∀ x y, (openGraph ω').Adj x y ↔ (openGraph ω).Adj x y ∧ s(x, y) ≠ s(a, b))
    (U : Vertex 2 → ℝ) (x : Vertex 2) :
    Graph.laplacian (openGraph ω) U x = Graph.laplacian (openGraph ω') U x +
      ((if x = a then U b - U a else 0) + (if x = b then U a - U b else 0)) := by
  classical
  have hN : (openGraph ω').neighborFinset x =
      ((openGraph ω).neighborFinset x).filter (fun y => s(x, y) ≠ s(a, b)) := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, hflip]
  have hrest : ∑ y ∈ (openGraph ω).neighborFinset x,
      (if s(x, y) ≠ s(a, b) then 0 else U y - U x) =
      (if x = a then U b - U a else 0) + (if x = b then U a - U b else 0) := by
    by_cases hxa : x = a
    · subst hxa
      have hxb : x ≠ b := hab.ne
      have hc : ∀ y, (s(x, y) ≠ s(x, b)) ↔ ¬ (b = y) := fun y => by
        rw [Ne, Sym2.congr_right, eq_comm]
      simp only [hc, ite_not, if_true, hxb, if_false, add_zero]
      rw [Finset.sum_ite_eq, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).2 hab)]
    · by_cases hxb : x = b
      · subst hxb
        have hc : ∀ y, (s(x, y) ≠ s(a, x)) ↔ ¬ (a = y) := fun y => by
          rw [Ne, Sym2.eq_swap (a := a), Sym2.congr_right, eq_comm]
        simp only [hc, ite_not, if_true, hxa, if_false, zero_add]
        rw [Finset.sum_ite_eq, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).2 hab.symm)]
      · have hc : ∀ y, s(x, y) ≠ s(a, b) := fun y heq => by
          have hx : x ∈ s(a, b) := heq ▸ Sym2.mem_mk_left x y
          rcases Sym2.mem_iff.1 hx with h | h
          · exact hxa h
          · exact hxb h
        simp only [hc, ne_eq, not_false_eq_true, if_true, Finset.sum_const_zero, hxa, hxb,
          if_false, add_zero]
  unfold Graph.laplacian
  rw [hN, Finset.sum_filter, ← hrest, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- The Laplacian sums to zero over a finite set closed under adjacency. -/
theorem sum_laplacian_eq_zero {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (K : Finset V) (hK : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (U : V → ℝ) :
    ∑ x ∈ K, Graph.laplacian G U x = 0 := by
  classical
  have h1 : ∀ x ∈ K, Graph.laplacian G U x =
      ∑ y ∈ K, if G.Adj x y then U y - U x else 0 := by
    intro x hx
    unfold Graph.laplacian
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨hK x hx y h, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ x ∈ K, ∑ y ∈ K, (if G.Adj x y then U y - U x else 0) =
      -∑ x ∈ K, ∑ y ∈ K, (if G.Adj x y then U y - U x else 0) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [G.adj_comm]
    split_ifs <;> ring
  linarith

/-- A walk of `ω` from `x` to `t` gives a walk of `ω'` (the edge `ab` closed) from `x` to `t`, to
`a` or to `b`. -/
theorem reachable_of_flip
    (hflip : ∀ x y, (openGraph ω').Adj x y ↔ (openGraph ω).Adj x y ∧ s(x, y) ≠ s(a, b))
    {x t : Vertex 2} (hxt : (openGraph ω).Reachable x t) :
    (openGraph ω').Reachable x t ∨ (openGraph ω').Reachable x a ∨
      (openGraph ω').Reachable x b := by
  obtain ⟨w⟩ := hxt
  induction w with
  | nil => exact Or.inl SimpleGraph.Reachable.rfl
  | @cons x y t hxy w ih =>
    by_cases he : s(x, y) = s(a, b)
    · rcases Sym2.eq_iff.1 he with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inl (h ▸ SimpleGraph.Reachable.rfl))
      · exact Or.inr (Or.inr (h ▸ SimpleGraph.Reachable.rfl))
    · have hxy' : (openGraph ω').Adj x y := (hflip x y).2 ⟨hxy, he⟩
      rcases ih with h | h | h
      · exact Or.inl (hxy'.reachable.trans h)
      · exact Or.inr (Or.inl (hxy'.reachable.trans h))
      · exact Or.inr (Or.inr (hxy'.reachable.trans h))

/-- If the open graph of `ω'` is smaller, the infinite cluster of `ω'` lies in that of `ω`. -/
theorem uniqueInfiniteComponent_supp_subset (hle : openGraph ω' ≤ openGraph ω)
    (h : HasUniqueInfiniteOpenComponent ω) (h' : HasUniqueInfiniteOpenComponent ω') :
    (uniqueInfiniteComponent h').supp ⊆ (uniqueInfiniteComponent h).supp := by
  obtain ⟨v, hv⟩ := (uniqueInfiniteComponent_infinite h').nonempty
  have hreach : ∀ w ∈ (uniqueInfiniteComponent h').supp, (openGraph ω).Reachable w v := by
    intro w hw
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hw hv
    exact (SimpleGraph.ConnectedComponent.exact (hw.trans hv.symm)).mono hle
  have hD : (openGraph ω).connectedComponentMk v = uniqueInfiniteComponent h := by
    rw [eq_uniqueInfiniteComponent_iff]
    refine (uniqueInfiniteComponent_infinite h').mono fun w hw => ?_
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact hreach w hw
  intro w hw
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, ← hD, SimpleGraph.ConnectedComponent.eq]
  exact hreach w hw

open Classical in
/-- The mass of `f` on a cluster as a sum over the support of `f`. -/
theorem mass_eq_sum_ite {ω : Configuration 2} (D : OpenComponent ω) {f : Vertex 2 → ℤ}
    (hf : (Function.support f).Finite) :
    (mass D f : ℝ) = ∑ v ∈ hf.toFinset, if v ∈ D.supp then (f v : ℝ) else 0 := by
  classical
  have h1 : mass D f = ∑ y ∈ hf.toFinset.subtype (· ∈ D), f y.val := by
    rw [mass]
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simpa only [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset,
      Function.mem_support] using hy
  rw [h1, Finset.sum_subtype_eq_sum_filter (fun v => f v), Int.cast_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun v _ => if_congr Iff.rfl rfl rfl

/-- Closing `ab`: if `b` stays in the infinite cluster and `a` leaves it, the finite cluster of
`a` carries the mass `u(a) - u(b)`. -/
theorem mass_eq_of_flip {f : Vertex 2 → ℤ} (hf : (Function.support f).Finite)
    (hab : (openGraph ω).Adj a b)
    (hflip : ∀ x y, (openGraph ω').Adj x y ↔ (openGraph ω).Adj x y ∧ s(x, y) ≠ s(a, b))
    (C : OpenComponent ω) (ha : a ∈ C.supp) (h' : HasUniqueInfiniteOpenComponent ω')
    (hsub : (uniqueInfiniteComponent h').supp ⊆ C.supp)
    (ha' : a ∉ (uniqueInfiniteComponent h').supp) (hb' : b ∈ (uniqueInfiniteComponent h').supp)
    (U : Vertex 2 → ℝ) (hU : ∀ x ∈ C.supp, -Graph.laplacian (openGraph ω) U x = f x) :
    (mass (uniqueInfiniteComponent h') f : ℝ) = mass C f - (U a - U b) := by
  classical
  set C' := uniqueInfiniteComponent h'
  set K := (openGraph ω').connectedComponentMk a
  have hle : openGraph ω' ≤ openGraph ω := fun x y hxy => ((hflip x y).1 hxy).1
  have haK : a ∈ K.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl
  have hKC : ∀ v ∈ K.supp, v ∈ C.supp := by
    intro v hv
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv ha ⊢
    rw [← ha, SimpleGraph.ConnectedComponent.eq]
    exact (SimpleGraph.ConnectedComponent.exact hv).mono hle
  have hdisj : ∀ v ∈ C'.supp, v ∉ K.supp := by
    intro v hv hvK
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv hvK haK
    exact ha' ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 (haK.trans (hvK.symm.trans hv)))
  have hsplit : ∀ v ∈ C.supp, v ∈ C'.supp ∨ v ∈ K.supp := by
    intro v hv
    have hva : (openGraph ω).Reachable v a := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv ha
      exact SimpleGraph.ConnectedComponent.exact (hv.trans ha.symm)
    have hK : (openGraph ω').Reachable v a → v ∈ K.supp := fun h =>
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        (SimpleGraph.ConnectedComponent.sound h)
    rcases reachable_of_flip hflip hva with h | h | h
    · exact Or.inr (hK h)
    · exact Or.inr (hK h)
    · left
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hb' ⊢
      exact (SimpleGraph.ConnectedComponent.sound h).trans hb'
  have hKfin : K.supp.Finite := by
    by_contra hinf
    have hKC' : K = C' := (eq_uniqueInfiniteComponent_iff h' K).2 hinf
    exact ha' (hKC' ▸ haK)
  have hbK : b ∉ K.supp := hdisj b hb'
  have hclosed : ∀ x ∈ hKfin.toFinset, ∀ y, (openGraph ω').Adj x y → y ∈ hKfin.toFinset := by
    intro x hx y hxy
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact K.mem_supp_of_adj_mem_supp hx hxy
  -- the mass of `f` on `K`
  have hmassK : ∑ v ∈ hKfin.toFinset, (f v : ℝ) = U a - U b := by
    have h1 : ∀ v ∈ hKfin.toFinset, (f v : ℝ) = -(Graph.laplacian (openGraph ω') U v +
        ((if v = a then U b - U a else 0) + (if v = b then U a - U b else 0))) := by
      intro v hv
      rw [← laplacian_eq_of_flip hab hflip, hU v (hKC v ((Set.Finite.mem_toFinset _).1 hv))]
    rw [Finset.sum_congr rfl h1, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      sum_laplacian_eq_zero _ _ hclosed, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', if_pos ((Set.Finite.mem_toFinset _).2 haK),
      if_neg (fun h => hbK ((Set.Finite.mem_toFinset _).1 h))]
    ring
  have hK2 : ∑ v ∈ hKfin.toFinset, (f v : ℝ) =
      ∑ v ∈ hf.toFinset, if v ∈ K.supp then (f v : ℝ) else 0 := by
    have e1 : ∑ v ∈ hKfin.toFinset, (f v : ℝ) =
        ∑ v ∈ hKfin.toFinset ∪ hf.toFinset, if v ∈ K.supp then (f v : ℝ) else 0 := by
      rw [← Finset.sum_subset Finset.subset_union_left]
      · refine Finset.sum_congr rfl fun v hv => ?_
        rw [if_pos ((Set.Finite.mem_toFinset _).1 hv)]
      · intro v _ hv
        rw [if_neg fun h => hv ((Set.Finite.mem_toFinset _).2 h)]
    rw [e1, ← Finset.sum_subset Finset.subset_union_right]
    intro v _ hv
    have : f v = 0 := by simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hv
    simp only [this, Int.cast_zero, ite_self]
  rw [mass_eq_sum_ite C hf, mass_eq_sum_ite C' hf, ← hmassK, hK2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hvC : v ∈ C.supp
  · rcases hsplit v hvC with h | h
    · rw [if_pos hvC, if_pos h, if_neg (hdisj v h), sub_zero]
    · rw [if_pos hvC, if_neg (fun h' => hdisj v h' h), if_pos h, sub_self]
  · rw [if_neg hvC, if_neg (fun h => hvC (hsub h)), if_neg (fun h => hvC (hKC v h)), sub_zero]

end Flip

/-- Step 2, vertex sets (L1797-1799): if closing the edge `ab` of `𝒞_∞` with `u(a) ≠ u(b)`
changes the vertex set of the infinite cluster, the mass of `f` on the new cluster is
`-(u(a) - u(b))` or `-(u(b) - u(a))`, nonzero. -/
theorem flipShrinkStep (f : Vertex 2 → ℤ) : FlipShrinkStep f := by
  classical
  intro hf ω h u hu a b hab hne hm h' hsupp
  have hab0 : (openGraph ω).Adj a.val b.val := hab
  have hflip := openGraph_flipAt_adj_iff hab0
  have hflip' : ∀ x y, (openGraph (flipAt s(a.val, b.val) ω)).Adj x y ↔
      (openGraph ω).Adj x y ∧ s(x, y) ≠ s(b.val, a.val) := by
    intro x y
    rw [hflip, Sym2.eq_swap (a := b.val)]
  have hle : openGraph (flipAt s(a.val, b.val) ω) ≤ openGraph ω :=
    fun x y hxy => ((hflip x y).1 hxy).1
  have hsub := uniqueInfiniteComponent_supp_subset hle h h'
  let U : Vertex 2 → ℝ := fun v => if hv : v ∈ uniqueInfiniteComponent h then u ⟨v, hv⟩ else 0
  have hUy : ∀ y : uniqueInfiniteComponent h, U y.val = u y := fun y => by
    simp only [U, dif_pos y.prop]
  have hUa : U a.val = u a := hUy a
  have hUb : U b.val = u b := hUy b
  have hU : ∀ x ∈ (uniqueInfiniteComponent h).supp, -Graph.laplacian (openGraph ω) U x = f x := by
    intro x hx
    have h1 : u = fun y => U y.val := funext fun y => (hUy y).symm
    have h2 := hu ⟨x, hx⟩
    rw [h1, componentLaplacian_restrict_eq] at h2
    exact h2
  have hm0 : (mass (uniqueInfiniteComponent h) f : ℝ) = 0 := by exact_mod_cast hm
  have haC : a.val ∈ (uniqueInfiniteComponent h).supp := a.prop
  have hbC : b.val ∈ (uniqueInfiniteComponent h).supp := b.prop
  have hreach : ∀ v ∈ (uniqueInfiniteComponent h).supp, (openGraph ω).Reachable v a.val := by
    intro v hv
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv haC
    exact SimpleGraph.ConnectedComponent.exact (hv.trans haC.symm)
  have hmemC' : ∀ {v w : Vertex 2}, w ∈ (uniqueInfiniteComponent h').supp →
      (openGraph (flipAt s(a.val, b.val) ω)).Reachable v w → v ∈ (uniqueInfiniteComponent h').supp := by
    intro v w hw hvw
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hw ⊢
    exact (SimpleGraph.ConnectedComponent.sound hvw).trans hw
  rw [Ne, ← Int.cast_eq_zero (α := ℝ)]
  by_cases ha' : a.val ∈ (uniqueInfiniteComponent h').supp <;> by_cases hb' : b.val ∈ (uniqueInfiniteComponent h').supp
  · exfalso
    refine hsupp (hsub.antisymm fun v hv => ?_)
    rcases reachable_of_flip hflip (hreach v hv) with h | h | h
    · exact hmemC' ha' h
    · exact hmemC' ha' h
    · exact hmemC' hb' h
  · rw [mass_eq_of_flip hf hab0.symm hflip' _ hbC h' hsub hb' ha' U hU, hm0, hUa, hUb]
    exact fun h0 => hne (by linarith)
  · rw [mass_eq_of_flip hf hab0 hflip _ haC h' hsub ha' hb' U hU, hm0, hUa, hUb]
    exact fun h0 => hne (by linarith)
  · exfalso
    obtain ⟨v, hv⟩ := (uniqueInfiniteComponent_infinite h').nonempty
    rcases reachable_of_flip hflip (hreach v (hsub hv)) with h | h | h
    · exact ha' (hmemC' hv h.symm)
    · exact ha' (hmemC' hv h.symm)
    · exact hb' (hmemC' hv h.symm)


section Transport

variable {ω ω' : Configuration 2}

/-- Growth `o(|x|)` at infinity on a cluster (the growth hypothesis of
`HasSublinearLiouville`). -/
def IsSublinearOn (D : OpenComponent ω) (v : D → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : D, R ≤ eucl x.val → |v x| ≤ ε * eucl x.val

theorem IsSublinearOn.congr {D : OpenComponent ω} {v w : D → ℝ} (hv : IsSublinearOn D v)
    (h : ∀ x, v x = w x) : IsSublinearOn D w := by
  intro ε hε
  obtain ⟨R, hR⟩ := hv ε hε
  exact ⟨R, fun x hx => h x ▸ hR x hx⟩

theorem IsSublinearOn.add {D : OpenComponent ω} {v w : D → ℝ} (hv : IsSublinearOn D v)
    (hw : IsSublinearOn D w) : IsSublinearOn D fun x => v x + w x := by
  intro ε hε
  obtain ⟨R₁, h₁⟩ := hv (ε / 2) (by positivity)
  obtain ⟨R₂, h₂⟩ := hw (ε / 2) (by positivity)
  refine ⟨max R₁ R₂, fun x hx => ?_⟩
  have e1 := h₁ x (le_trans (le_max_left _ _) hx)
  have e2 := h₂ x (le_trans (le_max_right _ _) hx)
  calc |v x + w x| ≤ |v x| + |w x| := abs_add_le _ _
    _ ≤ ε / 2 * eucl x.val + ε / 2 * eucl x.val := add_le_add e1 e2
    _ = ε * eucl x.val := by ring

theorem IsSublinearOn.const_mul {D : OpenComponent ω} {v : D → ℝ} (hv : IsSublinearOn D v)
    (c : ℝ) : IsSublinearOn D fun x => c * v x := by
  intro ε hε
  obtain ⟨R, h⟩ := hv (ε / (|c| + 1)) (by positivity)
  refine ⟨R, fun x hx => ?_⟩
  have hc : |c| * (ε / (|c| + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg c]
  rw [abs_mul]
  calc |c| * |v x| ≤ |c| * (ε / (|c| + 1) * eucl x.val) :=
        mul_le_mul_of_nonneg_left (h x hx) (abs_nonneg c)
    _ = (|c| * (ε / (|c| + 1))) * eucl x.val := by ring
    _ ≤ ε * eucl x.val := mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem IsSublinearOn.sub {D : OpenComponent ω} {v w : D → ℝ} (hv : IsSublinearOn D v)
    (hw : IsSublinearOn D w) : IsSublinearOn D fun x => v x - w x :=
  (hv.add (hw.const_mul (-1))).congr fun x => by ring

/-- A function with the slope asymptotics of `q` is `ℓ_q` up to `o(|x|)`. -/
theorem isSublinearOn_of_slope {D : OpenComponent ω} {q : Fin 2 → ℝ} {u : D → ℝ}
    (hu : componentSlopeAsymptotics D q u) :
    IsSublinearOn D fun x => u x - componentSlope D q x := by
  intro ε hε
  obtain ⟨R₀, hR₀, h⟩ := hu (ε / 2) (by positivity)
  refine ⟨R₀, fun x hx => ?_⟩
  have hpos : 0 < eucl x.val := lt_of_lt_of_le hR₀ hx
  have hmem : x ∈ componentEuclideanBall D 0 (2 * eucl x.val) := by
    rw [mem_componentEuclideanBall, dist_latticeEuclideanEmbedding_zero]
    linarith
  calc _ ≤ ε / 2 * (2 * eucl x.val) := h (2 * eucl x.val) (by linarith) x hmem
    _ = ε * eucl x.val := by ring

/-- A Green column in `d = 2` grows sublinearly. -/
theorem isSublinearOn_column {D : OpenComponent ω} {y : D} {g : D → ℝ}
    (hg : IsGreenColumn 2 le_rfl D y g) : IsSublinearOn D g := by
  intro ε hε
  obtain ⟨R, -, hR⟩ := (hg.2.1 rfl).2 ε hε
  exact ⟨R, hR⟩

/-- Clusters with the same vertex set have the same vertices. -/
def equivOfSuppEq {C : OpenComponent ω} {C' : OpenComponent ω'} (hsupp : C'.supp = C.supp) :
    C ≃ C' :=
  Equiv.subtypeEquivRight fun v => by
    change v ∈ C.supp ↔ v ∈ C'.supp
    rw [hsupp]

theorem IsSublinearOn.comp_equiv {C : OpenComponent ω} {C' : OpenComponent ω'}
    (hsupp : C'.supp = C.supp) {v : C' → ℝ} (hv : IsSublinearOn C' v) :
    IsSublinearOn C fun x => v (equivOfSuppEq hsupp x) := by
  intro ε hε
  obtain ⟨R, hR⟩ := hv ε hε
  exact ⟨R, fun x hx => hR (equivOfSuppEq hsupp x) hx⟩

/-- If closing the open edge `ab` keeps the vertex set of a cluster, a harmonic function `ℓ'` on
the new cluster has, on the old cluster, Laplacian `∇ℓ'(ab) (δ_a - δ_b)`. -/
theorem componentLaplacian_transport {a b : Vertex 2} (hab : (openGraph ω).Adj a b)
    (hflip : ∀ x y, (openGraph ω').Adj x y ↔ (openGraph ω).Adj x y ∧ s(x, y) ≠ s(a, b))
    {C : OpenComponent ω} {C' : OpenComponent ω'} (hsupp : C'.supp = C.supp) (ℓ' : C' → ℝ)
    (hℓ' : ∀ x, componentLaplacian C' ℓ' x = 0) (a' b' : C') (ha' : a'.val = a)
    (hb' : b'.val = b) (x : C) :
    componentLaplacian C (fun y => ℓ' (equivOfSuppEq hsupp y)) x =
      (if x.val = a then ℓ' b' - ℓ' a' else 0) + (if x.val = b then ℓ' a' - ℓ' b' else 0) := by
  classical
  let U : Vertex 2 → ℝ := fun v => if hv : v ∈ C' then ℓ' ⟨v, hv⟩ else 0
  have hUy : ∀ y : C', U y.val = ℓ' y := fun y => by simp only [U, dif_pos y.prop]
  have h1 : (fun y => ℓ' (equivOfSuppEq hsupp y)) = fun y : C => U y.val :=
    funext fun y => (hUy (equivOfSuppEq hsupp y)).symm
  have h2 : (∀ y : C', U y.val = ℓ' y) → ℓ' = fun y : C' => U y.val :=
    fun h => funext fun y => (h y).symm
  have h0 := hℓ' (equivOfSuppEq hsupp x)
  rw [h2 hUy, componentLaplacian_restrict_eq] at h0
  rw [h1, componentLaplacian_restrict_eq, laplacian_eq_of_flip hab hflip]
  change Graph.laplacian (openGraph ω') U x.val = 0 at h0
  rw [h0, zero_add, ← ha', ← hb', hUy, hUy]

/-- The Laplacian of `u₁ - u₂ - D (g₁ - g₂)`. -/
theorem componentLaplacian_comb (C : OpenComponent ω) (u₁ u₂ g₁ g₂ : C → ℝ) (D : ℝ) (x : C) :
    componentLaplacian C (fun y => u₁ y - u₂ y - D * (g₁ y - g₂ y)) x =
      componentLaplacian C u₁ x - componentLaplacian C u₂ x -
        D * (componentLaplacian C g₁ x - componentLaplacian C g₂ x) := by
  simp only [componentLaplacian, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

end Transport

/-- Step 2, gradients (L1801-1803): if closing the edge `ab` keeps the vertex set of `𝒞_∞` and
`ℓ'(a) = ℓ'(b)`, then `ℓ'` is harmonic on `𝒞_∞`, `ℓ - ℓ'` is harmonic and sublinear, hence
constant, so `ℓ(a) = ℓ(b)`. -/
theorem flipGradientStep (q : Fin 2 → ℝ) : FlipGradientStep q := by
  intro ω h hL ℓ hℓ a b hab h' hsupp ℓ' hℓ' a' b' ha' hb' hne heq
  have hab0 : (openGraph ω).Adj a.val b.val := hab
  have hℓh := ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ.1).1
  have hℓ'h := ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ'.1).1
  let e := equivOfSuppEq hsupp
  have hT := componentLaplacian_transport hab0 (openGraph_flipAt_adj_iff hab0) hsupp ℓ' hℓ'h
    a' b' ha' hb'
  have hharm : ∀ x, componentLaplacian _ (fun y => ℓ y - ℓ' (e y) - 0 * (ℓ y - ℓ y)) x = 0 := by
    intro x
    rw [componentLaplacian_comb, hℓh, hT, heq, sub_self, sub_self, ite_self, ite_self]
    ring
  have hsub : IsSublinearOn (uniqueInfiniteComponent h)
      fun y => ℓ y - ℓ' (e y) - 0 * (ℓ y - ℓ y) :=
    ((isSublinearOn_of_slope hℓ.2).sub ((isSublinearOn_of_slope hℓ'.2).comp_equiv hsupp)).congr
      fun x => by
        change _ - (_ - componentSlope (uniqueInfiniteComponent h) q x) = _
        ring
  obtain ⟨c, hc⟩ := hL _ hharm hsub
  have hea : e a = a' := Subtype.ext ha'.symm
  have heb : e b = b' := Subtype.ext hb'.symm
  have h1 := hc a
  have h2 := hc b
  rw [hea] at h1
  rw [heb] at h2
  exact hne (by linarith)


open Classical in
/-- `Σ_y f(y) g(y)` over a cluster as a finite sum over the support of `f`. -/
theorem finsum_mul_eq_sum {ω : Configuration 2} {D : OpenComponent ω} {f : Vertex 2 → ℤ}
    (hf : (Function.support f).Finite) (g : D → ℝ) :
    ∑ᶠ y : D, (f y.val : ℝ) * g y = ∑ y ∈ hf.toFinset.subtype (· ∈ D), (f y.val : ℝ) * g y := by
  refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
  have h0 : f y.val ≠ 0 := fun h0 => hy (by simp only [h0, Int.cast_zero, zero_mul])
  simpa only [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset,
    Function.mem_support] using h0

open Classical in
/-- The mass of `f` on a cluster as a finite sum over the support of `f`. -/
theorem mass_eq_sum_subtype {ω : Configuration 2} {D : OpenComponent ω} {f : Vertex 2 → ℤ}
    (hf : (Function.support f).Finite) :
    (mass D f : ℝ) = ∑ y ∈ hf.toFinset.subtype (· ∈ D), (f y.val : ℝ) := by
  have h := finsum_mul_eq_sum (D := D) hf fun _ => 1
  simp only [mul_one] at h
  rw [← h, mass]
  have hs : (Function.support fun y : D => f y.val).Finite := by
    refine (hf.preimage Subtype.val_injective.injOn).subset fun y hy => hy
  exact (map_finsum (Int.castRingHom ℝ) hs).symm ▸ rfl

/-- Step 2, the identity of L1806-1812: if closing the edge `ab` keeps the vertex set of `𝒞_∞`,
`v = ℓ - ℓ' - ∇ℓ'(ab) (G(·, a) - G(·, b))` is harmonic (`Δℓ' = ∇ℓ'(ab) (δ_a - δ_b)` on `𝒞_∞`)
and sublinear, hence constant; then `G(y, a) - G(y, b) = G(a, y) - G(b, y) + κ(a) - κ(b)` and
`Σ f = 0` give the identity. -/
theorem flipIdentityStep (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) : FlipIdentityStep f q := by
  classical
  intro hf ω h hL G hG hκ hm ℓ hℓ a b hab h' hsupp ℓ' hℓ' a' b' ha' hb'
  obtain ⟨κ, hκ⟩ := hκ
  have hab0 : (openGraph ω).Adj a.val b.val := hab
  have hℓh := ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ.1).1
  have hℓ'h := ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ'.1).1
  let e := equivOfSuppEq hsupp
  have hT := componentLaplacian_transport hab0 (openGraph_flipAt_adj_iff hab0) hsupp ℓ' hℓ'h
    a' b' ha' hb'
  simp only [← Subtype.ext_iff] at hT
  have hharm : ∀ x, componentLaplacian _
      (fun y => ℓ y - ℓ' (e y) - (ℓ' b' - ℓ' a') * (G y a - G y b)) x = 0 := by
    intro x
    have hGa := (hG a).1 x
    have hGb := (hG b).1 x
    rw [componentLaplacian_comb, hℓh, hT,
      show componentLaplacian _ (fun y => G y a) x = -(if x = a then 1 else 0) by linarith,
      show componentLaplacian _ (fun y => G y b) x = -(if x = b then 1 else 0) by linarith]
    split_ifs <;> ring
  have hsub : IsSublinearOn (uniqueInfiniteComponent h)
      fun y => ℓ y - ℓ' (e y) - (ℓ' b' - ℓ' a') * (G y a - G y b) :=
    (((isSublinearOn_of_slope hℓ.2).sub ((isSublinearOn_of_slope hℓ'.2).comp_equiv hsupp)).sub
      (((isSublinearOn_column (hG a)).sub (isSublinearOn_column (hG b))).const_mul
        (ℓ' b' - ℓ' a'))).congr fun x => by
      change _ - (_ - componentSlope (uniqueInfiniteComponent h) q x) - _ = _
      ring
  obtain ⟨c, hc⟩ := hL _ hharm hsub
  have hc' : ∀ y, ℓ y - ℓ' (e y) - (ℓ' b' - ℓ' a') * (G y a - G y b) = c := hc
  set S := hf.toFinset.subtype (· ∈ uniqueInfiniteComponent h)
  have hpair' : pairing _ f ℓ' = ∑ y ∈ S, (f y.val : ℝ) * ℓ' (e y) := by
    rw [pairing, ← finsum_comp_equiv e]
    exact finsum_mul_eq_sum hf _
  have hm' : ∑ y ∈ S, (f y.val : ℝ) = 0 := by
    rw [← mass_eq_sum_subtype hf]
    exact_mod_cast hm
  rw [hpair', pairing, potential, potential, finsum_mul_eq_sum hf, finsum_mul_eq_sum hf,
    finsum_mul_eq_sum hf]
  calc ∑ y ∈ S, (f y.val : ℝ) * ℓ y - ∑ y ∈ S, (f y.val : ℝ) * ℓ' (e y)
      = ∑ y ∈ S, ((ℓ' b' - ℓ' a') * ((f y.val : ℝ) * G a y) -
          (ℓ' b' - ℓ' a') * ((f y.val : ℝ) * G b y) +
          ((ℓ' b' - ℓ' a') * (κ a - κ b) + c) * (f y.val : ℝ)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        linear_combination (f y.val : ℝ) * hc' y +
          ((ℓ' b' - ℓ' a') * (f y.val : ℝ)) * hκ y a -
          ((ℓ' b' - ℓ' a') * (f y.val : ℝ)) * hκ y b
    _ = (ℓ' b' - ℓ' a') * (∑ y ∈ S, (f y.val : ℝ) * G a y -
          ∑ y ∈ S, (f y.val : ℝ) * G b y) +
          ((ℓ' b' - ℓ' a') * (κ a - κ b) + c) * ∑ y ∈ S, (f y.val : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
        ring
    _ = _ := by rw [hm', mul_zero, add_zero]

end Rigidity.Proofs.Section5

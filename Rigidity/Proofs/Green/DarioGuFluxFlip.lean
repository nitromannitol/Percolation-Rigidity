import Rigidity.Proofs.Corrector.DarioCaseOneTwo
import Rigidity.Proofs.Corrector.DarioCaseThreeClosed

/-!
# The flux of the corrected planes under the flip of one bond

For a configuration `ω`, an open component `C` and a function `ℓ` on it, `clusterFlux C ℓ b` is the
flux `(ℓ(z + e_i) - ℓ(z)) 1{b ∈ E(C)}` of `ℓ` along the oriented edge `b = (z, i)`: the `i`-th
component of `a(Dχ + p)` at `z` for the corrected plane `ℓ = p · x + χ`. This is the flux `g_p` of
C. Gu (*An efficient algorithm for solving elliptic problems on percolation clusters*, (1.6),
§3.1) and of Dario and Gu (Appendix B). Its variance is estimated as in Gu's proof of his
Proposition 1.1 (Steps 2 to 4), in the flip form of the proof of Lemma 3.3 of Dario in this
repository: the configurations `ω^{e,1}` and `ω^{e,0}` with the bond `e` open and closed replace
the resampled environment.

* `ae_clusterFlux_setBond_eq` (Gu, Lemma 3.2, the pivot edge, and the case where the endpoints
  are outside the infinite cluster): if the endpoints of `e` are not both in the infinite cluster
  `𝒞⁰` of `ω^{e,0}`, the fluxes of the corrected planes of `ω^{e,1}` and `ω^{e,0}` agree on every
  edge. The corrected plane of `ω^{e,1}` is constant on the finite piece cut off by `e`
  (maximum principle, `le_of_finite_piece`), and equals the corrected plane of `ω^{e,0}` up to a
  constant on `𝒞⁰` (`ae_exists_correctedPlane_eq_add_const`).
* `ae_clusterFlux_setBond_sub_open` and `ae_clusterFlux_setBond_sub_closed` (Gu, Steps 3 and 4,
  the terms `A_e` and `B_e`): if both endpoints are in `𝒞⁰`, the difference of the fluxes is the
  increment `c` across `e` times the gradient of the Green function of the dipole of `e` (for
  `ω^{e,1}`) or of the field of an open path joining the endpoints (for `ω^{e,0}`), minus `c` on
  the edge `e` itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Corrector
open scoped Classical

/-- The flux of `ℓ` along the oriented edge `b`: `(ℓ(edgeHead b) - ℓ(b.1)) 1{b open, b.1 ∈ C}`. -/
noncomputable def clusterFlux {ω : Configuration 2} (C : OpenComponent ω) (ℓ : C → ℝ)
    (b : LatticeEdge) : ℝ :=
  if EdgeOpen ω b ∧ b.1 ∈ C.supp then extendComp C ℓ (edgeHead b) - extendComp C ℓ b.1 else 0

/-- **Paths in `ω^{e,1}`**: a reachability in `ω^{e,1}` is a reachability in `ω^{e,0}`, or it
crosses `e` from one endpoint to the other. -/
theorem reachable_setBond_true_cases {a : LatticeEdge} {ω : Configuration 2} {u v : Vertex 2}
    (huv : (openGraph (setBond (edgeBond a) true ω)).Reachable u v) :
    (openGraph (setBond (edgeBond a) false ω)).Reachable u v ∨
      ((openGraph (setBond (edgeBond a) false ω)).Reachable u a.1 ∧
        (openGraph (setBond (edgeBond a) false ω)).Reachable (edgeHead a) v) ∨
      ((openGraph (setBond (edgeBond a) false ω)).Reachable u (edgeHead a) ∧
        (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 v) := by
  obtain ⟨pw⟩ := huv
  induction pw with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons u' v' w' hadj pw ih =>
    obtain ⟨hl, hopen⟩ := (openGraph_adj_iff _ _ _).1 hadj
    by_cases he : bondOfAdjacent hl = edgeBond a
    · have hs : s(u', v') = s(a.1, edgeHead a) := congrArg Subtype.val he
      rcases Sym2.eq_iff.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h⟩)
        · exact Or.inl (h1.symm.trans h2)
        · exact Or.inl h2
      · subst h1 h2
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h⟩)
        · exact Or.inl h2
        · exact Or.inl (h1.symm.trans h2)
    · have hadj0 : (openGraph (setBond (edgeBond a) false ω)).Adj u' v' := by
        refine (openGraph_adj_iff _ _ _).2 ⟨hl, ?_⟩
        rw [setBond_apply_ne he] at hopen
        rw [setBond_apply_ne he]
        exact hopen
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (hadj0.reachable.trans h)
      · exact Or.inr (Or.inl ⟨hadj0.reachable.trans h1, h2⟩)
      · exact Or.inr (Or.inr ⟨hadj0.reachable.trans h1, h2⟩)

/-- **Gu, Lemma 3.2, in flip form**: almost surely, if the endpoints of the bond `e` of `a` are not
both in the infinite cluster of `ω^{e,0}`, the fluxes of the corrected planes of `ω^{e,1}` and
`ω^{e,0}` of the same slope agree on every oriented edge. -/
theorem ae_clusterFlux_setBond_eq {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ a : LatticeEdge,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω)),
        ¬ (a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
          edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) →
        ∀ (q : Fin 2 → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
          (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
          IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
          ∀ b : LatticeEdge, clusterFlux _ ℓ₁ b = clusterFlux _ ℓ₀ b := by
  filter_upwards [ae_exists_correctedPlane_eq_add_const hpc hp1] with ω hω
  intro a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀ b
  obtain ⟨k, hk⟩ := hω a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀
  set f : Vertex 2 → ℝ := extendComp (uniqueInfiniteComponent h₁) ℓ₁
  have hsub01 : ∀ z, z ∈ (uniqueInfiniteComponent h₀).supp → z ∈ (uniqueInfiniteComponent h₁).supp := fun z hz =>
    (mem_uniqueInfiniteComponent_iff h₁ z).2 (Set.Infinite.mono
      (supp_setBond_false_subset (edgeBond a) ω z) ((mem_uniqueInfiniteComponent_iff h₀ z).1 hz))
  have hharm1 : ∀ z ∈ (uniqueInfiniteComponent h₁).supp,
      LatticeProb.Graph.laplacian (openGraph (setBond (edgeBond a) true ω)) f z = 0 := by
    intro z hz
    rw [laplacian_openGraph_eq_edgeDiv]
    exact edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₁.1.1 hz
  -- `f` is constant on the finite piece cut off by the bond
  have hconst : ∀ u w : Vertex 2, s(u, w) = s(a.1, edgeHead a) → u ∈ (uniqueInfiniteComponent h₀).supp →
      w ∉ (uniqueInfiniteComponent h₀).supp → ∀ z ∈ ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp,
        f z = f u := by
    intro u w hpair hu hw
    set F := ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp
    have hfin : F.Finite := by
      by_contra hinf
      exact hw ((mem_uniqueInfiniteComponent_iff h₀ w).2 hinf)
    have huF : u ∉ F := by
      intro huF
      have heq := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 huF
      have hinf := (mem_uniqueInfiniteComponent_iff h₀ u).1 hu
      change ((openGraph _).connectedComponentMk u).supp.Infinite at hinf
      rw [heq] at hinf
      exact hinf hfin
    have hadj_uw : (openGraph (setBond (edgeBond a) true ω)).Adj u w := by
      have ha : (openGraph (setBond (edgeBond a) true ω)).Adj a.1 (edgeHead a) :=
        (edgeOpen_setBond_self a true ω).2 rfl
      rcases Sym2.eq_iff.1 hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact ha
      · rw [h1, h2]; exact ha.symm
    have hF1 : ∀ z ∈ F, z ∈ (uniqueInfiniteComponent h₁).supp := by
      intro z hz
      have hzw : (openGraph (setBond (edgeBond a) true ω)).Reachable z w :=
        SimpleGraph.Reachable.mono (openGraph_setBond_le (edgeBond a) ω)
          (SimpleGraph.ConnectedComponent.exact
            ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hz))
      have hzu := hzw.trans hadj_uw.symm.reachable
      have hu1 := (mem_uniqueInfiniteComponent_iff h₁ u).1 (hsub01 u hu)
      refine (mem_uniqueInfiniteComponent_iff h₁ z).2 ?_
      change ((openGraph _).connectedComponentMk z).supp.Infinite
      rw [SimpleGraph.ConnectedComponent.sound hzu]
      exact hu1
    intro z hz
    have hle := le_of_finite_piece hpair hfin huF f (fun z hz => hharm1 z (hF1 z hz)) z hz
    have hge := le_of_finite_piece hpair hfin huF (fun y => -f y)
      (fun z hz => by rw [laplacian_neg, hharm1 z (hF1 z hz), neg_zero]) z hz
    linarith
  -- a vertex of `𝒞¹` outside `𝒞⁰` lies in the finite piece of an endpoint
  have hpiece : ∀ z ∈ (uniqueInfiniteComponent h₁).supp, z ∉ (uniqueInfiniteComponent h₀).supp → ∃ u w : Vertex 2, s(u, w) = s(a.1, edgeHead a) ∧
      u ∈ (uniqueInfiniteComponent h₀).supp ∧ w ∉ (uniqueInfiniteComponent h₀).supp ∧
        z ∈ ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp := by
    intro z hz1 hz0
    obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h₀).nonempty
    have ho1 := hsub01 o ho
    have hzo : (openGraph (setBond (edgeBond a) true ω)).Reachable z o :=
      SimpleGraph.ConnectedComponent.exact (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1
        hz1).trans ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ho1).symm)
    have hmem0 : ∀ y, (openGraph (setBond (edgeBond a) false ω)).Reachable y o → y ∈ (uniqueInfiniteComponent h₀).supp :=
      fun y hy => (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        ((SimpleGraph.ConnectedComponent.sound hy).trans
          ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ho))
    have hpieceOf : ∀ w, (openGraph (setBond (edgeBond a) false ω)).Reachable z w →
        z ∈ ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp :=
      fun w hw => (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        (SimpleGraph.ConnectedComponent.sound hw)
    rcases reachable_setBond_true_cases hzo with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (hmem0 z h) hz0
    · have hy0 := hmem0 _ h2
      have hx0 : a.1 ∉ (uniqueInfiniteComponent h₀).supp := fun hx => hnot ⟨hx, hy0⟩
      exact ⟨edgeHead a, a.1, Sym2.eq_swap, hy0, hx0, hpieceOf _ h1⟩
    · have hx0 := hmem0 _ h2
      have hy0 : edgeHead a ∉ (uniqueInfiniteComponent h₀).supp := fun hy => hnot ⟨hx0, hy⟩
      exact ⟨a.1, edgeHead a, rfl, hx0, hy0, hpieceOf _ h1⟩
  -- the comparison
  have hopen : ∀ b' : LatticeEdge, b' ≠ a →
      (EdgeOpen (setBond (edgeBond a) true ω) b' ↔ EdgeOpen (setBond (edgeBond a) false ω) b') :=
    fun b' hb' => (edgeOpen_setBond_iff_of_ne hb' true ω).trans
      (edgeOpen_setBond_iff_of_ne hb' false ω).symm
  unfold clusterFlux
  by_cases hb1 : b.1 ∈ (uniqueInfiniteComponent h₁).supp
  · by_cases hb0 : b.1 ∈ (uniqueInfiniteComponent h₀).supp
    · by_cases hba : b = a
      · subst hba
        have hy0 : edgeHead b ∉ (uniqueInfiniteComponent h₀).supp := fun hy => hnot ⟨hb0, hy⟩
        have hcl : ¬ EdgeOpen (setBond (edgeBond b) false ω) b := by
          rw [edgeOpen_setBond_self]; simp
        rw [if_neg (show ¬ (EdgeOpen (setBond (edgeBond b) false ω) b ∧
          b.1 ∈ (uniqueInfiniteComponent h₀).supp) from fun h => hcl h.1)]
        split_ifs with h
        · have hfy := hconst b.1 (edgeHead b) rfl hb0 hy0 (edgeHead b)
            SimpleGraph.ConnectedComponent.connectedComponentMk_mem
          change f (edgeHead b) - f b.1 = 0
          rw [hfy, sub_self]
        · rfl
      · by_cases ho : EdgeOpen (setBond (edgeBond a) false ω) b
        · have hy0 : edgeHead b ∈ (uniqueInfiniteComponent h₀).supp := (uniqueInfiniteComponent h₀).mem_supp_of_adj_mem_supp hb0 ho
          rw [if_pos ⟨(hopen b hba).2 ho, hb1⟩, if_pos ⟨ho, hb0⟩]
          change f (edgeHead b) - f b.1 = _
          rw [hk _ hy0, hk _ hb0]
          ring
        · rw [if_neg (fun h => ho ((hopen b hba).1 h.1)), if_neg (fun h => ho h.1)]
    · rw [if_neg (show ¬ (EdgeOpen (setBond (edgeBond a) false ω) b ∧
        b.1 ∈ (uniqueInfiniteComponent h₀).supp) from fun h => hb0 h.2)]
      split_ifs with h
      · obtain ⟨u, w, hpair, hu, hw, hzF⟩ := hpiece b.1 hb1 hb0
        have hfb := hconst u w hpair hu hw b.1 hzF
        change f (edgeHead b) - f b.1 = 0
        by_cases hba : b = a
        · subst hba
          have hhu : edgeHead b = u := by
            rcases Sym2.eq_iff.1 hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd (h1 ▸ hu) hb0
            · exact h1.symm
          rw [hhu, hfb, sub_self]
        · have hadj0 : EdgeOpen (setBond (edgeBond a) false ω) b := (hopen b hba).1 h.1
          have hyF : edgeHead b ∈
              ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp :=
            SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ hzF hadj0
          rw [hconst u w hpair hu hw _ hyF, hfb, sub_self]
      · rfl
  · rw [if_neg (fun h => hb1 h.2), if_neg (fun h => hb1 (hsub01 _ h.2))]

/-- **The flux difference in Case 3, through the configuration with the bond open** (Gu, Steps 3
and 4, with Dario's (3.22)): almost surely, if both endpoints of the bond `e` of `a` are in the
infinite cluster of `ω^{e,0}`, then for every oriented edge `b`
`flux₁(b) - flux₀(b) = c 1{b ∈ E(𝒞¹)} (greenProj ω^{e,1} (1_a))(b) - c 1{b = a}` with
`c = ℓ₀(a.1) - ℓ₀(edgeHead a)`. -/
theorem ae_clusterFlux_setBond_sub_open {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ a : LatticeEdge,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
        (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
        (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp)
        (q : Fin 2 → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
        (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
        IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
        IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
        ∀ b : LatticeEdge, clusterFlux _ ℓ₁ b - clusterFlux _ ℓ₀ b =
          (if EdgeOpen (setBond (edgeBond a) true ω) b ∧
              b.1 ∈ (uniqueInfiniteComponent h₁).supp then
            (ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) *
              greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1) b else 0) -
            (if b = a then ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩ else 0) := by
  filter_upwards [ae_correctedPlane_sub_eq_smul_greenProj hpc hp1] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ b
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  unfold clusterFlux
  by_cases hba : b = a
  · subst hba
    have ho1 : EdgeOpen (setBond (edgeBond b) true ω) b := (edgeOpen_setBond_self b true ω).2 rfl
    have hcl : ¬ EdgeOpen (setBond (edgeBond b) false ω) b := by
      rw [edgeOpen_setBond_self]; simp
    have hb1 : b.1 ∈ (uniqueInfiniteComponent h₁).supp := (hC _).2 hx
    have key := hω b h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ b ho1 hb1
    rw [if_pos ⟨ho1, hb1⟩, if_neg (fun h => hcl h.1), if_pos ⟨ho1, hb1⟩, if_pos rfl,
      ← key, extendComp_of_mem _ _ hx, extendComp_of_mem _ _ hy]
    ring
  · rw [if_neg hba, sub_zero]
    have hopen : EdgeOpen (setBond (edgeBond a) true ω) b ↔
        EdgeOpen (setBond (edgeBond a) false ω) b :=
      (edgeOpen_setBond_iff_of_ne hba true ω).trans (edgeOpen_setBond_iff_of_ne hba false ω).symm
    by_cases h : EdgeOpen (setBond (edgeBond a) true ω) b ∧ b.1 ∈ (uniqueInfiniteComponent h₁).supp
    · rw [if_pos h, if_pos ⟨hopen.1 h.1, (hC _).1 h.2⟩, if_pos h]
      exact hω a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ b h.1 h.2
    · rw [if_neg h, if_neg (fun h' => h ⟨hopen.2 h'.1, (hC _).2 h'.2⟩), if_neg h, sub_zero]

/-- **The flux difference in Case 3, through the configuration with the bond closed**: almost
surely, if both endpoints of the bond `e` of `a` are in the infinite cluster of `ω^{e,0}`, then for
every open path `pw` of `ω^{e,0}` joining them and every oriented edge `b`
`flux₁(b) - flux₀(b) = c' 1{b ∈ E(𝒞⁰)} (greenProj ω^{e,0} (pathField pw))(b) - c' 1{b = a}` with
`c' = ℓ₁(a.1) - ℓ₁(edgeHead a)`. -/
theorem ae_clusterFlux_setBond_sub_closed {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ a : LatticeEdge,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
        (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
        (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp)
        (q : Fin 2 → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
        (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
        IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
        IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
        ∀ (pw : (openGraph (setBond (edgeBond a) false ω)).Walk a.1 (edgeHead a))
          (b : LatticeEdge), clusterFlux _ ℓ₁ b - clusterFlux _ ℓ₀ b =
          (if EdgeOpen (setBond (edgeBond a) false ω) b ∧
              b.1 ∈ (uniqueInfiniteComponent h₀).supp then
            (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)) *
              greenProj (setBond (edgeBond a) false ω)
                (pathField (setBond (edgeBond a) false ω) pw) b else 0) -
            (if b = a then extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a) else 0) := by
  filter_upwards [ae_correctedPlane_sub_eq_smul_greenProj_closed hpc hp1] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw b
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  unfold clusterFlux
  by_cases hba : b = a
  · subst hba
    have ho1 : EdgeOpen (setBond (edgeBond b) true ω) b := (edgeOpen_setBond_self b true ω).2 rfl
    have hcl : ¬ EdgeOpen (setBond (edgeBond b) false ω) b := by
      rw [edgeOpen_setBond_self]; simp
    have hb1 : b.1 ∈ (uniqueInfiniteComponent h₁).supp := (hC _).2 hx
    rw [if_pos ⟨ho1, hb1⟩, if_neg (fun h => hcl h.1), if_neg (fun h => hcl h.1), if_pos rfl]
    ring
  · rw [if_neg hba, sub_zero]
    have hopen : EdgeOpen (setBond (edgeBond a) true ω) b ↔
        EdgeOpen (setBond (edgeBond a) false ω) b :=
      (edgeOpen_setBond_iff_of_ne hba true ω).trans (edgeOpen_setBond_iff_of_ne hba false ω).symm
    by_cases h : EdgeOpen (setBond (edgeBond a) false ω) b ∧
        b.1 ∈ (uniqueInfiniteComponent h₀).supp
    · rw [if_pos ⟨hopen.2 h.1, (hC _).2 h.2⟩, if_pos h, if_pos h]
      exact hω a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw b h.1 h.2
    · rw [if_neg (fun h' => h ⟨hopen.1 h'.1, (hC _).1 h'.2⟩), if_neg h, if_neg h, sub_zero]

end Rigidity.Green

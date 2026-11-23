import Rigidity.Proofs.Corrector.DarioCaseThreePairing

/-!
# Case 3 of Step 2 with the bond closed in the base configuration

When the base configuration is `ω^{e,0}` (the bond `e` of `a = (x, i)` closed), Dario's (3.22) has
`(a - a^e)(e) = -1` and `∇∇G(e, ·)` is the solution of `-∇·∇u = δ_x - δ_y` on the cluster of
`ω^{e,0}`, in which `e` is not an edge: its source is the field of an open path from `x` to `y`
(`edgeDiv_pathField`), and `greenProj ω^{e,0} (pathField p)` does not depend on the path
(`eq_greenProj_of_edgeDiv_eq`). Here

* `ae_correctedPlane_sub_eq_smul_greenProj_closed`: almost surely, in Case 3,
  `∇(ℓ₁ - ℓ₀) = (ℓ₁(x) - ℓ₁(y)) greenProj ω^{e,0} (pathField p)` on the open edges of the cluster
  of `ω^{e,0}`;
* `ae_heatComp_coarse_sub_eq_walkSum_closed`: the heat average of the coarsened change for the
  partition of `ω^{e,0}` is `(ℓ₁(x) - ℓ₁(y))` times the sum of `Pγ` along `p`, Dario's
  `w_γ(x) - w_γ(y)` with the path of (3.29).
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped InnerProductSpace Classical

variable (ω : Configuration 2)

theorem edgeDiv_add (η ζ : LatticeEdge → ℝ) (z : Vertex 2) :
    edgeDiv ω (η + ζ) z = edgeDiv ω η z + edgeDiv ω ζ z := by
  unfold edgeDiv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  split_ifs <;> ring

theorem edgeDiv_neg (η : LatticeEdge → ℝ) (z : Vertex 2) :
    edgeDiv ω (-η) z = -edgeDiv ω η z := by
  unfold edgeDiv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.neg_apply]
  split_ifs <;> ring

theorem edgeDiv_zero (z : Vertex 2) : edgeDiv ω 0 z = 0 := by
  unfold edgeDiv
  simp

theorem edgeDiv_dartField {u v : Vertex 2} (h : (openGraph ω).Adj u v) (z : Vertex 2) :
    edgeDiv ω (dartField u v : LatticeEdge → ℝ) z =
      (if z = u then 1 else 0) - (if z = v then 1 else 0) := by
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω h)
  · subst hi
    rw [dartField_add_unit]
    exact edgeDiv_single ω (a := (u, i)) h z
  · have hx : u = v + LatticeProb.unit i := by rw [hi]; abel
    subst hx
    rw [dartField_unit_add, lp.coeFn_neg, edgeDiv_neg,
      edgeDiv_single ω (a := (v, i)) h.symm z]
    simp only [edgeHead]
    ring

/-- **The field of a walk from `x` to `y` has divergence `δ_x - δ_y`.** -/
theorem edgeDiv_pathField {x y : Vertex 2} (p : (openGraph ω).Walk x y) (z : Vertex 2) :
    edgeDiv ω (pathField ω p : LatticeEdge → ℝ) z =
      (if z = x then 1 else 0) - (if z = y then 1 else 0) := by
  induction p with
  | nil =>
    simp only [pathField, SimpleGraph.Walk.darts_nil, List.map_nil, List.sum_nil, lp.coeFn_zero,
      sub_self]
    exact edgeDiv_zero ω z
  | @cons u v w hadj p ih =>
    unfold pathField at ih ⊢
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, lp.coeFn_add]
    rw [edgeDiv_add, ih, edgeDiv_dartField ω hadj]
    ring

/-- **Dario, (3.22), with the bond closed in the base configuration**: almost surely, in Case 3,
for every open path `p` from `x` to `y` in `ω^{e,0}`,
`∇(ℓ₁ - ℓ₀) = (ℓ₁(x) - ℓ₁(y)) greenProj ω^{e,0} (pathField p)` on the open edges of the cluster of
`ω^{e,0}`. -/
theorem ae_correctedPlane_sub_eq_smul_greenProj_closed {p : unitInterval}
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
          (b : LatticeEdge), EdgeOpen (setBond (edgeBond a) false ω) b →
          b.1 ∈ (uniqueInfiniteComponent h₀).supp →
          (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₁ b.1) -
              (extendComp _ ℓ₀ (edgeHead b) - extendComp _ ℓ₀ b.1) =
            (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)) *
              greenProj (setBond (edgeBond a) false ω)
                (pathField (setBond (edgeBond a) false ω) pw) b := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 (ae_edgeGrad_eq_smul_greenProj_of_div hpc hp1)] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw b hb hb1
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  have hdiv : ∀ z ∈ (uniqueInfiniteComponent h₀).supp,
      edgeDiv (setBond (edgeBond a) false ω) (edgeGrad (setBond (edgeBond a) false ω)
        (fun z => extendComp _ ℓ₁ z - 1 * extendComp _ ℓ₀ z)) z =
      (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)) *
        ((if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0)) := by
    intro z hz
    have hflip := edgeDiv_edgeGrad_setBond a (extendComp _ ℓ₁) ω z
    rw [edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₁.1.1 ((hC z).2 hz)] at hflip
    rw [edgeDiv_edgeGrad_sub_smul, edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₀.1.1 hz]
    linarith
  have hsub : SublinearOn (uniqueInfiniteComponent h₀).supp
      (fun z => extendComp _ ℓ₁ z - 1 * extendComp _ ℓ₀ z) := by
    have h1 := sublinearOn_of_componentSlopeAsymptotics _ hℓ₁.2
    have h0 := sublinearOn_of_componentSlopeAsymptotics _ hℓ₀.2
    have h1' : SublinearOn (uniqueInfiniteComponent h₀).supp
        (fun z => extendComp _ ℓ₁ z - ∑ i, q i * (z i : ℝ)) := fun ε hε => by
      obtain ⟨R, hR⟩ := h1 ε hε
      exact ⟨R, fun z hz => hR z ((hC z).2 hz)⟩
    have h2 := h1'.sub_smul h0 1
    intro ε hε
    obtain ⟨R, hR⟩ := h2 ε hε
    refine ⟨R, fun z hz hRz => ?_⟩
    have h3 := hR z hz hRz
    convert h3 using 2
    ring
  have key := hω (edgeBond a) false h₀ _ a.1 (edgeHead a)
    (edgeDiv_pathField (setBond (edgeBond a) false ω) pw) _ _ hdiv hsub b hb hb1
  simp only [edgeGrad, if_pos hb] at key
  rw [← key]
  ring

/-- **Case 3 with the bond closed**: almost surely, the heat average of the coarsened change of the
corrected planes for the partition of `ω^{e,0}` is `(ℓ₁(x) - ℓ₁(y))` times the sum of `Pγ` along any
open path `p` from `x` to `y` in `ω^{e,0}`. -/
theorem ae_heatComp_coarse_sub_eq_walkSum_closed {p : unitInterval}
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
          (hP : PlanarPartitionEvent (setBond (edgeBond a) false ω)) (r : ℝ) (x : Vertex 2)
          (j : Fin 2), Summable (fun z => latticeHeat (r ^ 2) x z *
            (stepRegion (setBond (edgeBond a) false ω) z j).card) →
          heatComp (fun z =>
              extendComp _ ℓ₁ (planarCoarseAnchor (setBond (edgeBond a) false ω) z) -
              extendComp _ ℓ₀ (planarCoarseAnchor (setBond (edgeBond a) false ω) z)) r x j =
            (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)) *
              walkSum (setBond (edgeBond a) false ω)
                (greenProj (setBond (edgeBond a) false ω) (coarseHeatField hP r x j)) pw := by
  filter_upwards [ae_correctedPlane_sub_eq_smul_greenProj_closed hpc hp1] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw hP r x j hS
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  rw [heatComp_coarse_eq_smul_inner_greenProj (v := fun z => extendComp _ ℓ₁ z -
      extendComp _ ℓ₀ z) (c := extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a))
      (ξ := pathField (setBond (edgeBond a) false ω) pw) hP hS
      (fun b hb hinf => ?_) (fun b hb hinf => ?_), real_inner_comm, inner_pathField]
  · have hb1 : b.1 ∈ (uniqueInfiniteComponent h₀).supp :=
      (mem_uniqueInfiniteComponent_iff h₀ b.1).2 hinf
    have key := hω a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw b hb hb1
    simp only [edgeGrad, if_pos hb]
    rw [← key]
    ring
  · have hb1 : b.1 ∉ (uniqueInfiniteComponent h₀).supp := fun h =>
      hinf ((mem_uniqueInfiniteComponent_iff h₀ b.1).1 h)
    have hb2 : edgeHead b ∉ (uniqueInfiniteComponent h₀).supp := fun h =>
      hb1 ((uniqueInfiniteComponent h₀).mem_supp_of_adj_mem_supp h hb.symm)
    simp only [edgeGrad, if_pos hb]
    rw [extendComp_of_not_mem _ _ hb1, extendComp_of_not_mem _ _ hb2,
      extendComp_of_not_mem _ _ (fun h => hb1 ((hC _).1 h)),
      extendComp_of_not_mem _ _ (fun h => hb2 ((hC _).1 h))]
    ring

end Rigidity.Corrector

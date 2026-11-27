import Rigidity.Proofs.Corrector.GeneralFlipCluster

/-!
# Step 2 of Lemma 3.3 of Dario on `ℤᵈ`: the term `T₂(e)` in Cases 1, 2 and 3

For a bond `e` with endpoints `x, y` and the forced configurations `ω^{e,1}`, `ω^{e,0}`, the term
(3.15)-(ii) `T₂(e) = Φ_{r²} * ∇_j[χ₁ - χ₀]_{𝒫⁰}(x)` (`flipTermTwo`) is computed case by case, as in
the planar files `DarioCaseThreeClosed`, `DarioCaseOneTwo`, `DarioStepTwoCases` and
`DarioStepTwoSplit`:

* `ae_correctedPlane_sub_eq_smul_greenProj_closed`, `ae_heatComp_coarse_sub_eq_walkSum_closed`:
  Case 3 with the bond closed, through an open path from `x` to `y` in `ω^{e,0}`;
* `ae_exists_correctedPlane_eq_add_const`: Cases 1 and 2, where the infinite cluster does not
  change, so the corrected planes differ by a constant;
* `ae_heatComp_coarse_sub_eq_zero`, `ae_flipTermTwo_eq_zero`: then `T₂(e) = 0`;
* `ae_flipTermTwo_eq_walkSum`: in Case 3, `T₂(e) = (χ₁(x) - χ₁(y)) Σ_p P γ`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal InnerProductSpace

variable {d : ℕ}

/-- **Dario, (3.22), with the bond closed in the base configuration**: almost surely, in Case 3,
for every open path `p` from `x` to `y` in `ω^{e,0}`,
`∇(ℓ₁ - ℓ₀) = (ℓ₁(x) - ℓ₁(y)) greenProj ω^{e,0} (pathField p)` on the open edges of the cluster of
`ω^{e,0}`. -/
theorem ae_correctedPlane_sub_eq_smul_greenProj_closed [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
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
        ∀ (pw : (openGraph (setBond (edgeBond a) false ω)).Walk a.1 (edgeHead a))
          (b : LatticeEdge d), EdgeOpen (setBond (edgeBond a) false ω) b →
          b.1 ∈ (uniqueInfiniteComponent h₀).supp →
          (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₁ b.1) -
              (extendComp _ ℓ₀ (edgeHead b) - extendComp _ ℓ₀ b.1) =
            (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)) *
              greenProj (setBond (edgeBond a) false ω)
                (pathField (setBond (edgeBond a) false ω) pw) b := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 (ae_edgeGrad_eq_smul_greenProj_of_div hd hpc hp1)] with ω hω
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
theorem ae_heatComp_coarse_sub_eq_walkSum_closed [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
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
        ∀ (pw : (openGraph (setBond (edgeBond a) false ω)).Walk a.1 (edgeHead a))
          (hP : PartitionEvent (setBond (edgeBond a) false ω)) (r : ℝ) (x : Vertex d)
          (j : Fin d), Summable (fun z => zdHeat d (r ^ 2) x z *
            (stepRegion (setBond (edgeBond a) false ω) z j).card) →
          heatComp (fun z =>
              extendComp _ ℓ₁ (partitionAnchor (setBond (edgeBond a) false ω) z) -
              extendComp _ ℓ₀ (partitionAnchor (setBond (edgeBond a) false ω) z)) r x j =
            (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)) *
              walkSum (setBond (edgeBond a) false ω)
                (greenProj (setBond (edgeBond a) false ω) (coarseHeatField hP r x j)) pw := by
  filter_upwards [ae_correctedPlane_sub_eq_smul_greenProj_closed hd hpc hp1] with ω hω
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

/-- **The maximum principle on the finite piece**: if closing the bond `e` between `u` and `w`
leaves `w` in a finite component `F` not containing `u`, and `f` is harmonic in `ω^{e,1}` on `F`,
then `f ≤ f(u)` on `F`. -/
theorem le_of_finite_piece {a : LatticeEdge d} {ω : Configuration d} {u w : Vertex d}
    (hpair : s(u, w) = s(a.1, edgeHead a))
    (hfin : ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp.Finite)
    (hu : u ∉ ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp)
    (f : Vertex d → ℝ)
    (hf : ∀ z ∈ ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp,
      LatticeProb.Graph.laplacian (openGraph (setBond (edgeBond a) true ω)) f z = 0) :
    ∀ z ∈ ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp, f z ≤ f u := by
  set F := ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp with hF
  have hwF : w ∈ F := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hmono := openGraph_setBond_le (edgeBond a) ω
  have hadj_uw : (openGraph (setBond (edgeBond a) true ω)).Adj u w := by
    have ha : (openGraph (setBond (edgeBond a) true ω)).Adj a.1 (edgeHead a) :=
      (edgeOpen_setBond_self a true ω).2 rfl
    rcases Sym2.eq_iff.1 hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ha
    · rw [h1, h2]; exact ha.symm
  have hmemF : ∀ z n, z ∈ F → (openGraph (setBond (edgeBond a) false ω)).Adj z n → n ∈ F := by
    intro z n hz hzn
    rw [hF, SimpleGraph.ConnectedComponent.mem_supp_iff] at hz ⊢
    rw [← hz]
    exact (SimpleGraph.ConnectedComponent.sound hzn.reachable).symm
  -- the neighbours of a vertex of `F` in `ω^{e,1}` are in `F`, or are `u`
  have hnb : ∀ z n, z ∈ F → (openGraph (setBond (edgeBond a) true ω)).Adj z n →
      n ∈ F ∨ n = u := by
    intro z n hz hzn
    obtain ⟨hl, hopen⟩ := (openGraph_adj_iff _ _ _).1 hzn
    by_cases he : bondOfAdjacent hl = edgeBond a
    · right
      have hs : s(z, n) = s(u, w) := (congrArg Subtype.val he).trans hpair.symm
      rcases Sym2.eq_iff.1 hs with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (h1 ▸ hz) hu
      · exact h2
    · left
      refine hmemF z n hz ((openGraph_adj_iff _ _ _).2 ⟨hl, ?_⟩)
      rw [setBond_apply_ne he] at hopen
      rw [setBond_apply_ne he]
      exact hopen
  obtain ⟨z₀, hz₀, hmax⟩ := hfin.toFinset.exists_max_image f ⟨w, hfin.mem_toFinset.2 hwF⟩
  have hz₀F : z₀ ∈ F := hfin.mem_toFinset.1 hz₀
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hzF, hzu⟩ := hcon
  have hM : ∀ y ∈ F, f y ≤ f z₀ := fun y hy => hmax y (hfin.mem_toFinset.2 hy)
  have hu' : f u < f z₀ := hzu.trans_le (hM z hzF)
  have key : ∀ y ∈ F, f y = f z₀ → ∀ n, (openGraph (setBond (edgeBond a) true ω)).Adj y n →
      f n = f z₀ := by
    intro y hy hyM n hn
    have hlap := hf y hy
    unfold LatticeProb.Graph.laplacian at hlap
    have hle : ∀ m ∈ (openGraph (setBond (edgeBond a) true ω)).neighborFinset y,
        f m - f y ≤ 0 := by
      intro m hm
      rw [SimpleGraph.mem_neighborFinset] at hm
      rw [hyM]
      rcases hnb y m hy hm with hmF | rfl
      · linarith [hM m hmF]
      · linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonpos hle).1 hlap n
      ((SimpleGraph.mem_neighborFinset _ _ _).2 hn)
    linarith
  have hreach : (openGraph (setBond (edgeBond a) false ω)).Reachable z₀ w := by
    have h1 := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hz₀F
    exact SimpleGraph.ConnectedComponent.exact h1
  obtain ⟨pw⟩ := hreach
  have hprop : ∀ {y t : Vertex d} (p : (openGraph (setBond (edgeBond a) false ω)).Walk y t),
      y ∈ F → f y = f z₀ → f t = f z₀ := by
    intro y t p
    induction p with
    | nil => exact fun _ h => h
    | @cons y' v' w' hadj p ih =>
      intro hy hyM
      exact ih (hmemF y' v' hy hadj) (key y' hy hyM v' (hmono hadj))
  have hw := hprop pw hz₀F rfl
  have := key w hwF hw u hadj_uw.symm
  linarith

/-- **Dario, Cases 1 and 2 of Step 2**: almost surely, if the endpoints of the bond `e` of `a` are
not both in the infinite cluster `𝒞⁰` of `ω^{e,0}`, the corrected planes `ℓ₁` of `ω^{e,1}` and `ℓ₀`
of `ω^{e,0}` of the same slope satisfy `ℓ₁ = ℓ₀ + k` on `𝒞⁰` for a constant `k`. -/
theorem ae_exists_correctedPlane_eq_add_const [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ a : LatticeEdge d,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω)),
        ¬ (a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
          edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) →
        ∀ (q : Fin d → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
          (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
          IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
          ∃ k : ℝ, ∀ z ∈ (uniqueInfiniteComponent h₀).supp,
            extendComp _ ℓ₁ z = extendComp _ ℓ₀ z + k := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1
    (Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds p hpc hp1)] with ω hR2
  intro a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀
  set f : Vertex d → ℝ := extendComp (uniqueInfiniteComponent h₁) ℓ₁ with hfdef
  have hsub01 : ∀ z, z ∈ (uniqueInfiniteComponent h₀).supp →
      z ∈ (uniqueInfiniteComponent h₁).supp := fun z hz =>
    (mem_uniqueInfiniteComponent_iff h₁ z).2 (Set.Infinite.mono
      (supp_setBond_false_subset (edgeBond a) ω z) ((mem_uniqueInfiniteComponent_iff h₀ z).1 hz))
  have hharm1 : ∀ z ∈ (uniqueInfiniteComponent h₁).supp,
      LatticeProb.Graph.laplacian (openGraph (setBond (edgeBond a) true ω)) f z = 0 := by
    intro z hz
    rw [laplacian_openGraph_eq_edgeDiv]
    exact edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₁.1.1 hz
  have hconst : ∀ u w : Vertex d, s(u, w) = s(a.1, edgeHead a) →
      u ∈ (uniqueInfiniteComponent h₀).supp → w ∉ (uniqueInfiniteComponent h₀).supp →
      f w = f u := by
    intro u w hpair hu hw
    set F := ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp with hF
    have hwF : w ∈ F := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
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
    have hle := le_of_finite_piece hpair hfin huF f (fun z hz => hharm1 z (hF1 z hz)) w hwF
    have hge := le_of_finite_piece hpair hfin huF (fun y => -f y)
      (fun z hz => by rw [laplacian_neg, hharm1 z (hF1 z hz), neg_zero]) w hwF
    linarith
  have hharm0 : ∀ x : uniqueInfiniteComponent h₀,
      componentLaplacian _ (fun y : uniqueInfiniteComponent h₀ => f y.val) x = 0 := by
    intro x
    rw [componentLaplacian_restrict_eq, laplacian_openGraph_eq_edgeDiv]
    have h1 : edgeDiv (setBond (edgeBond a) true ω) (edgeGrad (setBond (edgeBond a) true ω) f)
        x.val = 0 := by
      rw [← laplacian_openGraph_eq_edgeDiv]
      exact hharm1 _ (hsub01 _ x.2)
    have hflip := edgeDiv_edgeGrad_setBond a f ω x.val
    have hterm : (f (edgeHead a) - f a.1) *
        ((if x.val = a.1 then 1 else 0) - (if x.val = edgeHead a then 1 else 0)) = 0 := by
      by_cases hxa : x.val = a.1
      · have ha1 : a.1 ∈ (uniqueInfiniteComponent h₀).supp := hxa ▸ x.2
        have hh : edgeHead a ∉ (uniqueInfiniteComponent h₀).supp := fun hh => hnot ⟨ha1, hh⟩
        rw [hconst a.1 (edgeHead a) rfl ha1 hh, sub_self, zero_mul]
      · by_cases hxh : x.val = edgeHead a
        · have hh : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp := hxh ▸ x.2
          have ha1 : a.1 ∉ (uniqueInfiniteComponent h₀).supp := fun ha1 => hnot ⟨ha1, hh⟩
          rw [← hconst (edgeHead a) a.1 Sym2.eq_swap hh ha1, sub_self, zero_mul]
        · rw [if_neg hxa, if_neg hxh, sub_zero, mul_zero]
    linarith
  have hslope : componentSlopeAsymptotics (uniqueInfiniteComponent h₀) q
      (fun y : uniqueInfiniteComponent h₀ => f y.val) := by
    intro ε hε
    obtain ⟨R₀, hR₀, ht⟩ := hℓ₁.2 ε hε
    refine ⟨R₀, hR₀, fun R hR x hx => ?_⟩
    have hx1 : (⟨x.val, hsub01 _ x.2⟩ : uniqueInfiniteComponent h₁) ∈
        componentEuclideanBall _ 0 R := by
      rw [mem_componentEuclideanBall] at hx ⊢
      exact hx
    have h := ht R hR _ hx1
    simp only [componentSlope] at h ⊢
    rw [hfdef, extendComp_of_mem _ _ (hsub01 _ x.2)]
    exact h
  have hcp := isCorrectedPlane_of_harmonic _ hharm0 hslope
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h₀).nonempty
  set o' : uniqueInfiniteComponent h₀ := ⟨o, ho⟩
  obtain ⟨u, -, huniq⟩ := ((hR2 (edgeBond a) false) h₀).1 q o'
  have hc1 : IsCorrectedPlane (uniqueInfiniteComponent h₀) q
      (fun y : uniqueInfiniteComponent h₀ => f y.val - f o'.val) := by
    have hc := isCorrectedPlane_sub _ hcp (isCorrectedPlane_const _ (f o'.val))
    rw [sub_zero] at hc
    exact hc
  have hc0 : IsCorrectedPlane (uniqueInfiniteComponent h₀) q
      (fun y : uniqueInfiniteComponent h₀ => ℓ₀ y - ℓ₀ o') := by
    have hc := isCorrectedPlane_sub _ hℓ₀ (isCorrectedPlane_const _ (ℓ₀ o'))
    rw [sub_zero] at hc
    exact hc
  have e1 := huniq _ ⟨hc1, by simp⟩
  have e2 := huniq _ ⟨hc0, by simp⟩
  refine ⟨f o'.val - ℓ₀ o', fun z hz => ?_⟩
  have h := congrFun (e1.trans e2.symm) ⟨z, hz⟩
  simp only at h
  rw [extendComp_of_mem _ ℓ₀ hz]
  linarith

/-- **Cases 1 and 2 of Step 2 for the term (3.15)-(ii)**: almost surely, if the endpoints of the
bond `e` of `a` are not both in the infinite cluster of `ω^{e,0}`, then
`Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_{𝒫⁰}(x) = 0` for the corrected planes `ℓ₁, ℓ₀` of the same slope. -/
theorem ae_heatComp_coarse_sub_eq_zero [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ a : LatticeEdge d,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω)),
        ¬ (a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
          edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) →
        ∀ (q : Fin d → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
          (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
          IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
          PartitionEvent (setBond (edgeBond a) false ω) → ∀ (r : ℝ) (x : Vertex d)
            (j : Fin d),
            heatComp (fun z =>
                extendComp _ ℓ₁ (partitionAnchor (setBond (edgeBond a) false ω) z) -
                extendComp _ ℓ₀ (partitionAnchor (setBond (edgeBond a) false ω) z)) r x j = 0 := by
  filter_upwards [ae_exists_correctedPlane_eq_add_const hd hpc hp1] with ω hω
  intro a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀ hP r x j
  obtain ⟨k, hk⟩ := hω a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀
  have e : (fun z => extendComp _ ℓ₁ (partitionAnchor (setBond (edgeBond a) false ω) z) -
      extendComp _ ℓ₀ (partitionAnchor (setBond (edgeBond a) false ω) z)) = fun _ => k := by
    funext z
    have hz : partitionAnchor (setBond (edgeBond a) false ω) z ∈
        (uniqueInfiniteComponent h₀).supp :=
      (mem_uniqueInfiniteComponent_iff h₀ _).2 (infinite_planarCoarseAnchor hP z)
    rw [hk _ hz]
    ring
  rw [e, heatComp_const]

section Planes

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The term (3.15)-(ii) per bond in Case 3.** -/
theorem ae_flipTermTwo_eq_walkSum [NeZero d] (hd : 2 ≤ d) {p : unitInterval} (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (a : LatticeEdge d) (hP₀ : PartitionEvent (setBond (edgeBond a) false ω))
      (pw : (openGraph (setBond (edgeBond a) false ω)).Walk a.1 (edgeHead a)),
      setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 →
      flipTermTwo hG hGv i j r x (edgeBond a) ω =
        (flipCorrector hG hGv i true (edgeBond a) ω a.1 -
            flipCorrector hG hGv i true (edgeBond a) ω (edgeHead a) +
            ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))) *
          walkSum (setBond (edgeBond a) false ω)
            (greenProj (setBond (edgeBond a) false ω) (coarseHeatField hP₀ r x j)) pw := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_heatComp_coarse_sub_eq_walkSum_closed hd hpc hp1,
    ae_summable_heat_stepRegion hd hpc hp1] with ω hG' hcase3 hS i j r hr x a hP₀ pw hinf
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single i 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single i 1)
  have hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp :=
    (mem_uniqueInfiniteComponent_iff h₀ a.1).2 hinf
  have hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (SimpleGraph.ConnectedComponent.eq.2 ⟨pw⟩).symm
  have hmem₀ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₀).supp :=
    fun v hv => (mem_uniqueInfiniteComponent_iff h₀ v).2 hv
  have hmem₁ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₁).supp := fun v hv =>
    (mem_uniqueInfiniteComponent_iff h₁ v).2 (infiniteComponentEvent_setBond_true hv true)
  have hA : ∀ z, (setBond (edgeBond a) false ω) ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) z) := fun z => by
    rw [guardAnchor_of_event hP₀]
    exact infinite_planarCoarseAnchor hP₀ z
  set L : Vertex d → ℝ := fun v => extendComp _ ℓ₁ v - extendComp _ ℓ₀ v with hL
  have hdiff : ∀ z,
      flipCorrector hG hGv i true (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) z) -
        flipCorrector hG hGv i false (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) z) =
      L (guardAnchor (setBond (edgeBond a) false ω) z) -
        L (guardAnchor (setBond (edgeBond a) false ω) 0) := fun z => by
    rw [flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ (hmem₁ _ (hA z))
        (hmem₁ _ (hA 0)),
      flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ (hmem₀ _ (hA z))
        (hmem₀ _ (hA 0))]
    simp only [hL]
    ring
  have key := hcase3 a h₁ h₀ hx hy (Pi.single i 1) ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw hP₀ r x j
    (hS (edgeBond a) false x j r hr)
  have hT : flipTermTwo hG hGv i j r x (edgeBond a) ω =
      heatComp (fun z => extendComp _ ℓ₁ (partitionAnchor (setBond (edgeBond a) false ω) z) -
        extendComp _ ℓ₀ (partitionAnchor (setBond (edgeBond a) false ω) z)) r x j := by
    unfold flipTermTwo heatComp
    refine tsum_congr fun y => ?_
    beta_reduce
    rw [hdiff, hdiff]
    simp only [guardAnchor_of_event hP₀, hL]
    ring
  rw [hT, key]
  congr 1
  have hC := mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  rw [flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ ((hC _).2 hx)
      (hmem₁ _ (hA 0)),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ ((hC _).2 hy)
      (hmem₁ _ (hA 0))]
  simp only [sum_single_mul_coord]
  ring

/-- **The term (3.15)-(ii) per bond in Cases 1 and 2**: almost surely, if the endpoints of the bond
of `a` are not both in the infinite cluster of `ω^{e,0}`, then `T₂(e) = 0`. -/
theorem ae_flipTermTwo_eq_zero [NeZero d] (hd : 2 ≤ d) {p : unitInterval} (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ) (x : Vertex d) (a : LatticeEdge d),
      PartitionEvent (setBond (edgeBond a) false ω) →
      ¬ (setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 ∧
        (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a)) →
      flipTermTwo hG hGv i j r x (edgeBond a) ω = 0 := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_exists_correctedPlane_eq_add_const hd hpc hp1] with
    ω hG' hcase12 i j r x a hP₀ hnot
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single i 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single i 1)
  have hcase : ¬ (a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
      edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) := by
    rintro ⟨hx, hy⟩
    refine hnot ⟨(mem_uniqueInfiniteComponent_iff h₀ a.1).1 hx, ?_⟩
    exact SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy).symm)
  obtain ⟨k, hk⟩ := hcase12 a h₁ h₀ hcase (Pi.single i 1) ℓ₁ ℓ₀ hℓ₁ hℓ₀
  have hmem₀ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₀).supp :=
    fun v hv => (mem_uniqueInfiniteComponent_iff h₀ v).2 hv
  have hmem₁ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₁).supp := fun v hv =>
    (mem_uniqueInfiniteComponent_iff h₁ v).2 (infiniteComponentEvent_setBond_true hv true)
  have hA : ∀ z, (setBond (edgeBond a) false ω) ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) z) := fun z => by
    rw [guardAnchor_of_event hP₀]
    exact infinite_planarCoarseAnchor hP₀ z
  have hconst : ∀ z,
      flipCorrector hG hGv i true (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) z) -
        flipCorrector hG hGv i false (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) z) =
      0 := fun z => by
    rw [flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ (hmem₁ _ (hA z))
        (hmem₁ _ (hA 0)),
      flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ (hmem₀ _ (hA z))
        (hmem₀ _ (hA 0)), hk _ (hmem₀ _ (hA z)), hk _ (hmem₀ _ (hA 0))]
    ring
  unfold flipTermTwo
  simp only [hconst]
  exact heatComp_const 0 r x j

end Planes

end Rigidity.Corrector.GeneralDim

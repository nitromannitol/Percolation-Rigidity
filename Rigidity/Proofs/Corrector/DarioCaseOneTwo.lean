import Rigidity.Proofs.Corrector.DarioCaseThreeClosed

/-!
# Cases 1 and 2 of Step 2: the corrected planes agree up to a constant

Cases 1 and 2 of Step 2 of Dario's proof of Lemma 3.3: if the endpoints `x, y` of the bond `e` are
not both in the infinite cluster `𝒞⁰` of `ω^{e,0}`, the corrected planes `ℓ₁` of `ω^{e,1}` and `ℓ₀`
of `ω^{e,0}` of the same slope differ by a constant on `𝒞⁰`, so the corrector change of (3.15)-(ii)
vanishes. (Case 1: `e` does not touch the cluster; Case 2: closing `e` cuts a finite piece `F` off
the cluster of `ω^{e,1}`, and Dario extends `χ_p^e` to `F` by (3.14).) Here, with `𝒞¹ ⊇ 𝒞⁰` the
infinite cluster of `ω^{e,1}`:

* `isCorrectedPlane_of_harmonic`: a harmonic function with slope asymptotics is a corrected plane
  (the growth condition follows from the slope asymptotics);
* `le_of_finite_piece`: the maximum principle on the finite piece `F`, by which `ℓ₁` is constant on
  `F` and equal to its value at the endpoint in `𝒞⁰` ((3.14): `χ_p = p·(z - x) + χ_p^e(x)` on `F`);
* `ae_exists_correctedPlane_eq_add_const`: almost surely, outside Case 3, `ℓ₁ = ℓ₀ + k` on `𝒞⁰`
  (Dario's Cases 1 and 2, by the uniqueness of corrected planes of `ω^{e,0}`).
-/

namespace Rigidity.Corrector

open Filter MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

/-- A harmonic function with slope asymptotics is a corrected plane. -/
theorem isCorrectedPlane_of_harmonic {ω : Configuration 2} (C : OpenComponent ω) {q : Fin 2 → ℝ}
    {u : C → ℝ} (hh : ∀ x, componentLaplacian C u x = 0) (hs : componentSlopeAsymptotics C q u) :
    IsCorrectedPlane C q u := by
  refine ⟨⟨hh, ?_⟩, hs⟩
  obtain ⟨R₀, hR₀, htail⟩ := hs 1 one_pos
  set K : ℝ := 1 + ∑ i, |q i| with hK
  have hK0 : 0 ≤ K := by positivity
  have hball : ∀ R : ℝ, R₀ ≤ R → componentBallL2 C 0 R u ≤ K * R := by
    intro R hR
    have hR0 : 0 < R := hR₀.trans_le hR
    refine componentBallL2_le_of_abs_le C 0 R u (by positivity) fun x hx => ?_
    have h1 := htail R hR x hx
    have hxR : Rigidity.Section5.eucl x.val < R := by
      rw [← Rigidity.Proofs.Section5.dist_latticeEuclideanEmbedding_zero]
      exact (mem_componentEuclideanBall C 0 R x).1 hx
    have hslope : |componentSlope C q x| ≤ (∑ i, |q i|) * R := by
      unfold componentSlope
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (abs_coord_le_norm x.val i).trans hxR.le
    have := abs_sub_abs_le_abs_sub (u x) (componentSlope C q x)
    rw [hK]
    nlinarith [abs_nonneg (componentSlope C q x)]
  change Tendsto (fun R : ℝ => (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u) atTop (nhds 0)
  have hlim : Tendsto (fun R : ℝ => K * R⁻¹) atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul K
  refine squeeze_zero' (eventually_atTop.2 ⟨max R₀ 1, fun R hR => ?_⟩)
    (eventually_atTop.2 ⟨max R₀ 1, fun R hR => ?_⟩) hlim
  · have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR)
    exact mul_nonneg (by positivity) (componentBallL2_nonneg C 0 R u)
  · have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    have hb := hball R ((le_max_left _ _).trans hR)
    calc (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u ≤ (R ^ (1 + 1))⁻¹ * (K * R) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = K * R⁻¹ := by field_simp; ring

theorem laplacian_neg {ω : Configuration 2} (f : Vertex 2 → ℝ) (z : Vertex 2) :
    LatticeProb.Graph.laplacian (openGraph ω) (fun y => -f y) z =
      -LatticeProb.Graph.laplacian (openGraph ω) f z := by
  unfold LatticeProb.Graph.laplacian
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The maximum principle on the finite piece**: if closing the bond `e` between `u` and `w`
leaves `w` in a finite component `F` not containing `u`, and `f` is harmonic in `ω^{e,1}` on `F`,
then `f ≤ f(u)` on `F`. -/
theorem le_of_finite_piece {a : LatticeEdge} {ω : Configuration 2} {u w : Vertex 2}
    (hpair : s(u, w) = s(a.1, edgeHead a))
    (hfin : ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp.Finite)
    (hu : u ∉ ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk w).supp)
    (f : Vertex 2 → ℝ)
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
  have hprop : ∀ {y t : Vertex 2} (p : (openGraph (setBond (edgeBond a) false ω)).Walk y t),
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

theorem supp_setBond_false_subset (e : Bond 2) (ω : Configuration 2) (u : Vertex 2) :
    ((openGraph (setBond e false ω)).connectedComponentMk u).supp ⊆
      ((openGraph (setBond e true ω)).connectedComponentMk u).supp := by
  intro w hw
  refine (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
    (SimpleGraph.ConnectedComponent.sound ?_)
  exact SimpleGraph.Reachable.mono (openGraph_setBond_le e ω) (SimpleGraph.ConnectedComponent.exact
    ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hw))

/-- **Dario, Cases 1 and 2 of Step 2**: almost surely, if the endpoints of the bond `e` of `a` are
not both in the infinite cluster `𝒞⁰` of `ω^{e,0}`, the corrected planes `ℓ₁` of `ω^{e,1}` and `ℓ₀`
of `ω^{e,0}` of the same slope satisfy `ℓ₁ = ℓ₀ + k` on `𝒞⁰` for a constant `k`. -/
theorem ae_exists_correctedPlane_eq_add_const {p : unitInterval}
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
          ∃ k : ℝ, ∀ z ∈ (uniqueInfiniteComponent h₀).supp,
            extendComp _ ℓ₁ z = extendComp _ ℓ₀ z + k := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1
    (Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds p hpc hp1)] with ω hR2
  intro a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀
  set f : Vertex 2 → ℝ := extendComp (uniqueInfiniteComponent h₁) ℓ₁ with hfdef
  have hsub01 : ∀ z, z ∈ (uniqueInfiniteComponent h₀).supp →
      z ∈ (uniqueInfiniteComponent h₁).supp := fun z hz =>
    (mem_uniqueInfiniteComponent_iff h₁ z).2 (Set.Infinite.mono
      (supp_setBond_false_subset (edgeBond a) ω z) ((mem_uniqueInfiniteComponent_iff h₀ z).1 hz))
  have hharm1 : ∀ z ∈ (uniqueInfiniteComponent h₁).supp,
      LatticeProb.Graph.laplacian (openGraph (setBond (edgeBond a) true ω)) f z = 0 := by
    intro z hz
    rw [laplacian_openGraph_eq_edgeDiv]
    exact edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₁.1.1 hz
  have hconst : ∀ u w : Vertex 2, s(u, w) = s(a.1, edgeHead a) →
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

end Rigidity.Corrector

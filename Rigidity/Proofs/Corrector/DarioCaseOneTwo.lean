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
* `eq_of_finite_piece`: the maximum principle on the finite piece `F`: `ℓ₁` is constant on `F` and
  equal to its value at the endpoint in `𝒞⁰` ((3.14): `χ_p = p·(z - x) + χ_p^e(x)` on `F`);
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

end Rigidity.Corrector

import Rigidity.Proofs.Corrector.DarioStepTwoSplit
import Rigidity.Proofs.Corrector.DarioStepOneLocal

/-!
# The term (3.15)-(ii) per bond in Case 3, through the configuration with the bond open

For a bond `e` of an oriented edge `a = (x, i)`, write `ω¹ = ω^{e,1}`, `ω⁰ = ω^{e,0}` and let
`g` be the potential of `∇∇G(e, ·) = greenProj ω¹ (1_a)` on the infinite cluster of `ω¹`, `0`
elsewhere (`dipolePot`); its gradient is at most `1` on every edge (`abs_edgeGrad_dipolePot_le`,
`abs_greenProj_single_le`). In Case 3 of Step 2 of the proof of Lemma 3.3 of Dario, `ℓ₁ - ℓ₀` and
`(ℓ₀(x) - ℓ₀(y)) g` differ by a constant on the cluster ((3.22) and `eq_of_walk_of_edge`), so that
almost surely (`ae_flipTermTwo_eq_open`)

`T₂(e) = (χ₀(x) - χ₀(y) + x_i - y_i) ((P_{ω¹} γ_{ω¹})(a) + Σ_y Φ_{r²}(x, y) Δ_y)`,

with `γ_{ω¹}` the field of the anchor paths of the partition of `ω¹` (`coarseHeatField`) and
`Δ_y = partitionChange ω¹ ω⁰ g j y` the change of the coarse gradient of `g` from the partition of
`ω¹` to that of `ω⁰`. The first term is Dario's `w_γ(x) - w_γ(y)` after (3.28)
(`heatComp_coarse_eq_smul_greenProj`). The second is the term (3.15)-(ii) evaluated with the
partition of `ω⁰` in place of that of `ω¹`: it is local by Lemma 3.5, as in Step 1. For a bond open
in `ω`, `ω¹ = ω`, so all these bonds share the source `γ_ω`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal InnerProductSpace

/-- The potential of `greenProj ω (1_a)` on the infinite components of `ω`, `0` elsewhere. -/
noncomputable def dipolePot (ω : Configuration 2) (a : LatticeEdge) (z : Vertex 2) : ℝ :=
  if ω ∈ infiniteComponentEvent z then
    (exists_isGradOf_greenProj ω (lp.single 2 a 1)).choose z else 0

theorem infiniteComponentEvent_iff_of_adj {ω : Configuration 2} {u v : Vertex 2}
    (h : (openGraph ω).Adj u v) :
    ω ∈ infiniteComponentEvent u ↔ ω ∈ infiniteComponentEvent v := by
  change ((openGraph ω).connectedComponentMk u).supp.Infinite ↔
    ((openGraph ω).connectedComponentMk v).supp.Infinite
  rw [SimpleGraph.ConnectedComponent.sound h.reachable]

theorem edgeGrad_dipolePot {ω : Configuration 2} (a : LatticeEdge) {b : LatticeEdge}
    (hb : EdgeOpen ω b) :
    edgeGrad ω (dipolePot ω a) b =
      if ω ∈ infiniteComponentEvent b.1 then greenProj ω (lp.single 2 a 1) b else 0 := by
  have hiff := infiniteComponentEvent_iff_of_adj (ω := ω) hb
  unfold edgeGrad dipolePot
  rw [if_pos hb]
  by_cases h : ω ∈ infiniteComponentEvent b.1
  · rw [if_pos (hiff.1 h), if_pos h, if_pos h]
    exact ((exists_isGradOf_greenProj ω (lp.single 2 a 1)).choose_spec b hb).symm
  · rw [if_neg (fun h' => h (hiff.2 h')), if_neg h, if_neg h, sub_zero]

/-- `|∇∇G(e, b)| ≤ 1`: the projection does not increase the norm of `1_a`. -/
theorem abs_greenProj_single_le (ω : Configuration 2) (a b : LatticeEdge) :
    |greenProj ω (lp.single 2 a 1) b| ≤ 1 := by
  have h1 := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (greenProj ω (lp.single 2 a 1)) b
  have h2 := norm_greenProj_le ω (lp.single 2 a 1)
  rw [lp.norm_single (by norm_num), norm_one] at h2
  rw [Real.norm_eq_abs] at h1
  linarith

theorem abs_edgeGrad_dipolePot_le (ω : Configuration 2) (a b : LatticeEdge) :
    |edgeGrad ω (dipolePot ω a) b| ≤ |greenProj ω (lp.single 2 a 1) b| := by
  by_cases hb : EdgeOpen ω b
  · rw [edgeGrad_dipolePot a hb]
    split_ifs
    · exact le_rfl
    · rw [abs_zero]
      exact abs_nonneg _
  · simp only [edgeGrad, if_neg hb, abs_zero]
    exact abs_nonneg _

theorem edgeOpen_setBond_true_of_false {a b : LatticeEdge} {ω : Configuration 2}
    (h : EdgeOpen (setBond (edgeBond a) false ω) b) :
    EdgeOpen (setBond (edgeBond a) true ω) b := by
  by_cases hba : b = a
  · subst hba
    exact absurd ((edgeOpen_setBond_self b false ω).1 h) (by simp)
  · exact (edgeOpen_setBond_iff_of_ne hba true ω).2 ((edgeOpen_setBond_iff_of_ne hba false ω).1 h)

/-- A function with no increment along the open edges based in a set closed under the open edges
is constant along the open walks starting in it. -/
theorem eq_of_walk_of_edge {ω : Configuration 2} {S : Set (Vertex 2)}
    (hS : ∀ z w, z ∈ S → (openGraph ω).Adj z w → w ∈ S) {F : Vertex 2 → ℝ}
    (hF : ∀ b : LatticeEdge, EdgeOpen ω b → b.1 ∈ S → F (edgeHead b) = F b.1)
    {u v : Vertex 2} (p : (openGraph ω).Walk u v) (hu : u ∈ S) : F u = F v := by
  induction p with
  | nil => rfl
  | @cons z w t hadj p ih =>
    have hw : w ∈ S := hS z w hu hadj
    refine Eq.trans ?_ (ih hw)
    obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω hadj)
    · have hy : w = z + LatticeProb.unit i := hi
      have hopen : EdgeOpen ω (z, i) := by
        unfold EdgeOpen edgeHead
        rw [← hy]
        exact hadj
      have h1 : F (edgeHead (z, i)) = F z := hF (z, i) hopen hu
      change F (z + LatticeProb.unit i) = F z at h1
      rw [← hy] at h1
      exact h1.symm
    · have hx : z = w + LatticeProb.unit i := by rw [hi]; abel
      have hopen : EdgeOpen ω (w, i) := by
        unfold EdgeOpen edgeHead
        rw [← hx]
        exact hadj.symm
      have h1 : F (edgeHead (w, i)) = F w := hF (w, i) hopen hw
      change F (w + LatticeProb.unit i) = F w at h1
      rw [← hx] at h1
      exact h1

theorem heatComp_smul (c : ℝ) (u : Vertex 2 → ℝ) (r : ℝ) (x : Vertex 2) (j : Fin 2) :
    heatComp (fun z => c * u z) r x j = c * heatComp u r x j := by
  unfold heatComp
  rw [← tsum_mul_left]
  exact tsum_congr fun y => by ring

section Planes

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The term (3.15)-(ii) per bond in Case 3, through `ω^{e,1}`.** -/
theorem ae_flipTermTwo_eq_open {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i j : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (a : LatticeEdge) (hP₁ : PlanarPartitionEvent (setBond (edgeBond a) true ω)),
      PlanarPartitionEvent (setBond (edgeBond a) false ω) →
      setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 →
      (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) →
      flipTermTwo hG hGv i j r x (edgeBond a) ω =
        (flipCorrector hG hGv i false (edgeBond a) ω a.1 -
            flipCorrector hG hGv i false (edgeBond a) ω (edgeHead a) +
            ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))) *
          (greenProj (setBond (edgeBond a) true ω) (coarseHeatField hP₁ r x j) a +
            ∑' y, latticeHeat (r ^ 2) x y *
              partitionChange (setBond (edgeBond a) true ω) (setBond (edgeBond a) false ω)
                (dipolePot (setBond (edgeBond a) true ω) a) j y) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_correctedPlane_sub_eq_smul_greenProj hpc hp1,
    ae_summable_heat_stepRegion hpc hp1] with ω hG' hpl hS i j r hr x a hP₁ hP₀ hinf hreach
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single i 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single i 1)
  have hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp :=
    (mem_uniqueInfiniteComponent_iff h₀ a.1).2 hinf
  have hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  have hC := mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
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
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩ := ⟨_, rfl⟩
  -- `ℓ₁ - ℓ₀ - c' g` has no increment on the open edges of the cluster of `ω¹`
  have hFedge : ∀ b : LatticeEdge, EdgeOpen (setBond (edgeBond a) true ω) b →
      b.1 ∈ (uniqueInfiniteComponent h₁).supp →
      (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₀ (edgeHead b)) -
          c' * dipolePot (setBond (edgeBond a) true ω) a (edgeHead b) =
        (extendComp _ ℓ₁ b.1 - extendComp _ ℓ₀ b.1) -
          c' * dipolePot (setBond (edgeBond a) true ω) a b.1 := by
    intro b hb hb1
    have key := hpl a h₁ h₀ hx hy (Pi.single i 1) ℓ₁ ℓ₀ hℓ₁ hℓ₀ b hb hb1
    rw [← hc'] at key
    have hgb := edgeGrad_dipolePot (ω := setBond (edgeBond a) true ω) a hb
    rw [if_pos ((mem_uniqueInfiniteComponent_iff h₁ b.1).1 hb1)] at hgb
    simp only [edgeGrad, if_pos hb] at hgb
    linear_combination key - c' * hgb
  have ha₁ : a.1 ∈ (uniqueInfiniteComponent h₁).supp := (hC _).2 hx
  have hconst : ∀ v ∈ (uniqueInfiniteComponent h₁).supp,
      (extendComp _ ℓ₁ v - extendComp _ ℓ₀ v) -
          c' * dipolePot (setBond (edgeBond a) true ω) a v =
        (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₀ a.1) -
          c' * dipolePot (setBond (edgeBond a) true ω) a a.1 := by
    intro v hv
    have hreach' : (openGraph (setBond (edgeBond a) true ω)).Reachable a.1 v :=
      SimpleGraph.ConnectedComponent.exact
        (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ha₁).trans
          ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hv).symm)
    exact (eq_of_walk_of_edge (S := (uniqueInfiniteComponent h₁).supp)
      (F := fun v => (extendComp _ ℓ₁ v - extendComp _ ℓ₀ v) -
        c' * dipolePot (setBond (edgeBond a) true ω) a v)
      (fun z w hz hzw => (uniqueInfiniteComponent h₁).mem_supp_of_adj_mem_supp hz hzw)
      hFedge hreach'.some ha₁).symm
  have hdiff : ∀ z,
      flipCorrector hG hGv i true (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) z) -
        flipCorrector hG hGv i false (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) z) =
      (extendComp _ ℓ₁ (guardAnchor (setBond (edgeBond a) false ω) z) -
          extendComp _ ℓ₀ (guardAnchor (setBond (edgeBond a) false ω) z)) -
        (extendComp _ ℓ₁ (guardAnchor (setBond (edgeBond a) false ω) 0) -
          extendComp _ ℓ₀ (guardAnchor (setBond (edgeBond a) false ω) 0)) := fun z => by
    rw [flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ (hmem₁ _ (hA z))
        (hmem₁ _ (hA 0)),
      flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ (hmem₀ _ (hA z))
        (hmem₀ _ (hA 0))]
    ring
  have hconstA : ∀ z, (extendComp _ ℓ₁ (guardAnchor (setBond (edgeBond a) false ω) z) -
        extendComp _ ℓ₀ (guardAnchor (setBond (edgeBond a) false ω) z)) -
          c' * dipolePot (setBond (edgeBond a) true ω) a
            (guardAnchor (setBond (edgeBond a) false ω) z) =
        (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₀ a.1) -
          c' * dipolePot (setBond (edgeBond a) true ω) a a.1 :=
    fun z => hconst _ (hmem₁ _ (hA z))
  -- `T₂(e) = c' Φ * ∇_j[g]_{𝒫⁰}(x)`
  have hT : flipTermTwo hG hGv i j r x (edgeBond a) ω =
      c' * heatComp (fun z => dipolePot (setBond (edgeBond a) true ω) a
        (planarCoarseAnchor (setBond (edgeBond a) false ω) z)) r x j := by
    unfold flipTermTwo heatComp
    rw [← tsum_mul_left]
    refine tsum_congr fun y => ?_
    beta_reduce
    have e1 := hdiff (y + LatticeProb.unit j)
    have e2 := hdiff y
    have e3 := hconstA (y + LatticeProb.unit j)
    have e4 := hconstA y
    simp only [guardAnchor_of_event hP₀] at e1 e2 e3 e4 ⊢
    linear_combination latticeHeat (r ^ 2) x y * (e1 - e2 + e3 - e4)
  -- the change of partition for `g`
  have hle₁ : ∀ b, |edgeGrad (setBond (edgeBond a) true ω)
      (dipolePot (setBond (edgeBond a) true ω) a) b| ≤
        |(1 : ℝ)| * |greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1) b| := fun b => by
    rw [abs_one, one_mul]
    exact abs_edgeGrad_dipolePot_le _ a b
  have hle₀ : ∀ b, |edgeGrad (setBond (edgeBond a) false ω)
      (dipolePot (setBond (edgeBond a) true ω) a) b| ≤
        |(1 : ℝ)| * |greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1) b| := fun b => by
    by_cases hb : EdgeOpen (setBond (edgeBond a) false ω) b
    · have e : edgeGrad (setBond (edgeBond a) false ω)
          (dipolePot (setBond (edgeBond a) true ω) a) b =
          edgeGrad (setBond (edgeBond a) true ω) (dipolePot (setBond (edgeBond a) true ω) a) b := by
        unfold edgeGrad
        rw [if_pos hb, if_pos (edgeOpen_setBond_true_of_false hb)]
      rw [e]
      exact hle₁ b
    · simp only [edgeGrad, if_neg hb, abs_zero]
      positivity
  have hs₁ := summable_heat_coarse_of_le hP₁ (hS (edgeBond a) true x j r hr) hle₁
  have hs₀ := summable_heat_coarse_of_le hP₀ (hS (edgeBond a) false x j r hr) hle₀
  have hsc : Summable fun y => latticeHeat (r ^ 2) x y *
      partitionChange (setBond (edgeBond a) true ω) (setBond (edgeBond a) false ω)
        (dipolePot (setBond (edgeBond a) true ω) a) j y := by
    refine (hs₀.sub hs₁).congr fun y => ?_
    unfold partitionChange
    ring
  have hpair : heatComp (fun z => dipolePot (setBond (edgeBond a) true ω) a
      (planarCoarseAnchor (setBond (edgeBond a) true ω) z)) r x j =
      greenProj (setBond (edgeBond a) true ω) (coarseHeatField hP₁ r x j) a := by
    have h := heatComp_coarse_eq_smul_greenProj hP₁ (hS (edgeBond a) true x j r hr)
      (v := dipolePot (setBond (edgeBond a) true ω) a) (c := 1) (a := a)
      (fun b hb hinf => by
        rw [edgeGrad_dipolePot a hb,
          if_pos (show setBond (edgeBond a) true ω ∈ infiniteComponentEvent b.1 from hinf), one_mul])
      (fun b hb hinf => by
        rw [edgeGrad_dipolePot a hb,
          if_neg (show setBond (edgeBond a) true ω ∉ infiniteComponentEvent b.1 from hinf)])
    rwa [one_mul] at h
  have hsplit : heatComp (fun z => dipolePot (setBond (edgeBond a) true ω) a
      (planarCoarseAnchor (setBond (edgeBond a) false ω) z)) r x j =
      greenProj (setBond (edgeBond a) true ω) (coarseHeatField hP₁ r x j) a +
        ∑' y, latticeHeat (r ^ 2) x y *
          partitionChange (setBond (edgeBond a) true ω) (setBond (edgeBond a) false ω)
            (dipolePot (setBond (edgeBond a) true ω) a) j y := by
    rw [← hpair]
    unfold heatComp
    rw [← hs₁.tsum_add hsc]
    refine tsum_congr fun y => ?_
    unfold partitionChange
    ring
  rw [hT, hsplit]
  congr 1
  rw [hc', flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ hx (hmem₀ _ (hA 0)),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ hy (hmem₀ _ (hA 0)),
    extendComp_of_mem _ _ hx, extendComp_of_mem _ _ hy]
  simp only [sum_single_mul_coord]
  ring

end Planes

end Rigidity.Corrector

import Rigidity.Proofs.Corrector.DarioFlipTermTwoSummable
import Rigidity.Proofs.Corrector.DarioStepTwoCases

/-!
# The term (3.15)-(ii) per bond as a path sum of the Green projection

For a bond `e` of an oriented edge `a = (x, i')` and `ω⁰ = ω^{e,0}`, almost surely
(`ae_flipTermTwo_eq_walkSum`): if `x` lies in the infinite cluster of `ω⁰`, then for every open walk
`pw` of `ω⁰` from `x` to `y = x + e_{i'}`

`T₂(e) = (χ₁(x) - χ₁(y) + x_i - y_i) Σ_{b ∈ pw} (P_{ω⁰} γ_{ω⁰})(b)`,

with `χ₁` the corrector of `ω^{e,1}` (`flipCorrector`), `γ_{ω⁰}` the field of the paths between the
anchors of neighbouring partition cubes of `ω⁰` weighted by the heat kernel (`coarseHeatField`) and
`P_{ω⁰}` the Green projection of `ω⁰`. This is Case 3 of Step 2 of the proof of Lemma 3.3 of Dario
in flip form (`ae_heatComp_coarse_sub_eq_walkSum_closed`), written for the term `T₂(e)` itself;
when there is no such walk, `T₂(e) = 0` (Cases 1 and 2, `ae_flipTermTwo_eq_zero`). For a bond closed
in `ω`, `ω⁰ = ω`, so that all these bonds share the source `γ_ω` (the single source of the bound of
the Step 2 sum).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal InnerProductSpace

section Planes

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

theorem sum_single_mul_coord (i : Fin 2) (v : Vertex 2) :
    ∑ k, (Pi.single i 1 : Fin 2 → ℝ) k * (v k : ℝ) = (v i : ℝ) := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- **The term (3.15)-(ii) per bond in Case 3.** -/
theorem ae_flipTermTwo_eq_walkSum {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i j : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (a : LatticeEdge) (hP₀ : PlanarPartitionEvent (setBond (edgeBond a) false ω))
      (pw : (openGraph (setBond (edgeBond a) false ω)).Walk a.1 (edgeHead a)),
      setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 →
      flipTermTwo hG hGv i j r x (edgeBond a) ω =
        (flipCorrector hG hGv i true (edgeBond a) ω a.1 -
            flipCorrector hG hGv i true (edgeBond a) ω (edgeHead a) +
            ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))) *
          walkSum (setBond (edgeBond a) false ω)
            (greenProj (setBond (edgeBond a) false ω) (coarseHeatField hP₀ r x j)) pw := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_heatComp_coarse_sub_eq_walkSum_closed hpc hp1,
    ae_summable_heat_stepRegion hpc hp1] with ω hG' hcase3 hS i j r hr x a hP₀ pw hinf
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
  set L : Vertex 2 → ℝ := fun v => extendComp _ ℓ₁ v - extendComp _ ℓ₀ v with hL
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
      heatComp (fun z => extendComp _ ℓ₁ (planarCoarseAnchor (setBond (edgeBond a) false ω) z) -
        extendComp _ ℓ₀ (planarCoarseAnchor (setBond (edgeBond a) false ω) z)) r x j := by
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
theorem ae_flipTermTwo_eq_zero {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i j : Fin 2) (r : ℝ) (x : Vertex 2) (a : LatticeEdge),
      PlanarPartitionEvent (setBond (edgeBond a) false ω) →
      ¬ (setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 ∧
        (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a)) →
      flipTermTwo hG hGv i j r x (edgeBond a) ω = 0 := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_exists_correctedPlane_eq_add_const hpc hp1] with
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

end Rigidity.Corrector

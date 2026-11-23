import Rigidity.Proofs.Corrector.DarioStepRegionSummable

/-!
# Convergence of the heat series of the term (3.15)-(ii)

The series of the term (3.15)-(ii) in flip form (`FlipTermTwoSummable`) is the heat series of the
coarse gradient of `χ₁ - χ₀` for the partition of `ω^{e,0}`. Its anchors lie in the infinite
cluster `𝒞⁰` of `ω^{e,0}`, where `χ₁ - χ₀ = ℓ₁ - ℓ₀` up to a constant for the corrected planes
`ℓ₁, ℓ₀` of the flips (`flipCorrector_eq_plane`). Then, almost surely
(`ae_flipTermTwoSummable`):

* in Cases 1 and 2 of Step 2, `ℓ₁ - ℓ₀` is constant on `𝒞⁰` and the series vanishes termwise;
* in Case 3, `∇(ℓ₁ - ℓ₀)` is a multiple of an `ℓ²` field on the open edges of `ω^{e,0}` (Dario's
  (3.22)), and the heat series of the coarse gradient of such a function converges as soon as
  `Σ_z Φ_{r²}(x, z) |stepRegion(z)|` does (`summable_heat_coarse_of_le`), which holds almost surely
  (`ae_summable_heat_stepRegion`).

With `darioFlipSumBound_of_sums`, Dario's (3.13) in flip form then follows from the two bounds
`Σ_e T₁(e)² ≤ O_s(C/r²)` (Step 1) and `Σ_e T₂(e)² ≤ O_s(C/r²)` (Step 2)
(`darioFlipSumBound_of_stepSums`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal InnerProductSpace

/-- Every bond is the bond of an oriented lattice edge. -/
theorem exists_edgeBond_eq (e : Bond 2) : ∃ a : LatticeEdge, edgeBond a = e := by
  obtain ⟨_, x, y, rfl, h⟩ := e
  have hadj : (nearestNeighborGraph 2).Adj x y := lattice_adj_iff_l1Dist.mpr h
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 hadj
  · exact ⟨(x, i), Subtype.ext (by simp [edgeBond, bondOfAdjacent, edgeHead, hi])⟩
  · exact ⟨(y, i), Subtype.ext (by simp [edgeBond, bondOfAdjacent, edgeHead, hi, Sym2.eq_swap])⟩

/-- **Convergence of the heat series of a coarse gradient with an `ℓ²` gradient**: on the
partition event, if `|∇u| ≤ |c| |g|` on the edges for a field `g ∈ ℓ²` and
`Σ_z Φ_{r²}(x, z) |stepRegion(z)| < ∞`, then `Σ_z Φ_{r²}(x, z) ∇_j[u]_𝒫(z)` converges. -/
theorem summable_heat_coarse_of_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {r : ℝ}
    {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card)
    {u : Vertex 2 → ℝ} {c : ℝ} {g : EdgeField} (hle : ∀ b, |edgeGrad ω u b| ≤ |c| * |g b|) :
    Summable fun z => latticeHeat (r ^ 2) x z *
      (u (planarCoarseAnchor ω (z + LatticeProb.unit j)) - u (planarCoarseAnchor ω z)) := by
  have hmem : Memℓp (edgeGrad ω u) 2 := by
    refine memℓp_gen' (C := c ^ 2 * ‖g‖ ^ 2) fun s => ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    calc ∑ b ∈ s, edgeGrad ω u b ^ 2 ≤ ∑ b ∈ s, c ^ 2 * g b ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h := hle b
          rw [← sq_abs (edgeGrad ω u b), ← sq_abs c, ← sq_abs (g b), ← mul_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = c ^ 2 * ∑ b ∈ s, g b ^ 2 := by rw [Finset.mul_sum]
      _ ≤ c ^ 2 * ‖g‖ ^ 2 := mul_le_mul_of_nonneg_left (sum_sq_le_norm_sq g s) (sq_nonneg c)
  set G' : EdgeField := ⟨edgeGrad ω u, hmem⟩ with hG'
  refine ((summable_heat_smul_pathField hP hS).mapL (innerSL ℝ G')).congr fun z => ?_
  simp only [innerSL_apply_apply]
  rw [real_inner_smul_right, inner_pathField]
  have hw := walkSum_eq_of_isGradOf ω (isGradOf_edgeGrad ω u) (coarseStepWalk hP z j)
  rw [show ((G' : LatticeEdge → ℝ)) = edgeGrad ω u from rfl, hw]

section Planes

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

include hGv in
/-- A corrected plane of every slope on the infinite cluster of a configuration of `G`. -/
theorem exists_isCorrectedPlane {ω : Configuration 2} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) (q : Fin 2 → ℝ) :
    ∃ ℓ : uniqueInfiniteComponent h → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ := by
  obtain ⟨v, hv⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  obtain ⟨u, hu, -⟩ := ((hGv hω).2 h).1 q ⟨v, hv⟩
  exact ⟨u, hu.1⟩

/-- On the infinite cluster of `ω^{e,b}`, `χ_b = ℓ - q · (·)` up to its value at the root. -/
theorem flipCorrector_eq_plane {e : Bond 2} {ω : Configuration 2} {b : Bool}
    (hω : setBond e b ω ∈ G) (h : HasUniqueInfiniteOpenComponent (setBond e b ω)) (i : Fin 2)
    {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ) {v : Vertex 2}
    (hv : v ∈ (uniqueInfiniteComponent h).supp)
    (ho : guardAnchor (setBond e false ω) 0 ∈ (uniqueInfiniteComponent h).supp) :
    flipCorrector hG hGv i b e ω v =
      (extendComp _ ℓ v - ∑ k, (Pi.single i 1 : Fin 2 → ℝ) k * (v k : ℝ)) -
        (extendComp _ ℓ (guardAnchor (setBond e false ω) 0) -
          ∑ k, (Pi.single i 1 : Fin 2 → ℝ) k * ((guardAnchor (setBond e false ω) 0) k : ℝ)) := by
  unfold flipCorrector
  rw [extendComp_of_mem _ _ hv, extendComp_of_mem _ _ ho]
  exact correctorDiff_eq hG hGv hω (uniqueInfiniteComponent_infinite h) hℓ ⟨v, hv⟩ ⟨_, ho⟩

/-- **Convergence of the series of the term (3.15)-(ii)**: almost surely, for all `i, j`, `r > 0`,
`x` and every bond. -/
theorem ae_flipTermTwoSummable {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i j : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2) (e : Bond 2),
      FlipTermTwoSummable hG hGv i j r x e ω := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_setBond hp0 hp1 (ae_planarPartitionEvent hpc),
    ae_exists_correctedPlane_eq_add_const hpc hp1,
    ae_correctedPlane_sub_eq_smul_greenProj_closed hpc hp1,
    ae_summable_heat_stepRegion hpc hp1] with ω hG' hP' hcase12 hcase3 hS i j r hr x e
  obtain ⟨a, rfl⟩ := exists_edgeBond_eq e
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single i 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single i 1)
  have hP₀ := hP' (edgeBond a) false
  -- the anchors of `ω⁰` lie in `𝒞⁰ ⊆ 𝒞¹`
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
  have hterm : ∀ y, latticeHeat (r ^ 2) x y *
      ((flipCorrector hG hGv i true (edgeBond a) ω
            (guardAnchor (setBond (edgeBond a) false ω) (y + LatticeProb.unit j)) -
          flipCorrector hG hGv i false (edgeBond a) ω
            (guardAnchor (setBond (edgeBond a) false ω) (y + LatticeProb.unit j))) -
        (flipCorrector hG hGv i true (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) y) -
          flipCorrector hG hGv i false (edgeBond a) ω
            (guardAnchor (setBond (edgeBond a) false ω) y))) =
      latticeHeat (r ^ 2) x y *
        (L (planarCoarseAnchor (setBond (edgeBond a) false ω) (y + LatticeProb.unit j)) -
          L (planarCoarseAnchor (setBond (edgeBond a) false ω) y)) :=
    fun y => by
      rw [hdiff, hdiff]
      simp only [guardAnchor_of_event hP₀]
      ring
  unfold FlipTermTwoSummable
  refine Summable.congr ?_ fun y => (hterm y).symm
  by_cases hcase : a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
      edgeHead a ∈ (uniqueInfiniteComponent h₀).supp
  · -- Case 3
    obtain ⟨hx, hy⟩ := hcase
    have hxy : (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) :=
      SimpleGraph.ConnectedComponent.exact
        (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx).trans
          ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy).symm)
    set pw := hxy.some
    have hC := mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
    refine summable_heat_coarse_of_le hP₀ (hS (edgeBond a) false x j r hr)
      (c := extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a))
      (g := greenProj (setBond (edgeBond a) false ω) (pathField (setBond (edgeBond a) false ω) pw))
      fun b => ?_
    by_cases hb : EdgeOpen (setBond (edgeBond a) false ω) b
    · by_cases hb1 : b.1 ∈ (uniqueInfiniteComponent h₀).supp
      · have key := hcase3 a h₁ h₀ hx hy (Pi.single i 1) ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw b hb hb1
        simp only [edgeGrad, if_pos hb, hL]
        rw [show extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₀ (edgeHead b) -
            (extendComp _ ℓ₁ b.1 - extendComp _ ℓ₀ b.1) =
            (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₁ b.1) -
              (extendComp _ ℓ₀ (edgeHead b) - extendComp _ ℓ₀ b.1) by ring, key, abs_mul]
      · have hb2 : edgeHead b ∉ (uniqueInfiniteComponent h₀).supp := fun h =>
          hb1 ((uniqueInfiniteComponent h₀).mem_supp_of_adj_mem_supp h hb.symm)
        simp only [edgeGrad, if_pos hb, hL]
        rw [extendComp_of_not_mem _ _ hb1, extendComp_of_not_mem _ _ hb2,
          extendComp_of_not_mem _ _ (fun h => hb1 ((hC _).1 h)),
          extendComp_of_not_mem _ _ (fun h => hb2 ((hC _).1 h))]
        simp only [sub_self, abs_zero]
        positivity
    · simp only [edgeGrad, if_neg hb, abs_zero]
      positivity
  · -- Cases 1 and 2
    obtain ⟨k, hk⟩ := hcase12 a h₁ h₀ hcase (Pi.single i 1) ℓ₁ ℓ₀ hℓ₁ hℓ₀
    refine summable_zero.congr fun y => ?_
    have hA' : ∀ z, planarCoarseAnchor (setBond (edgeBond a) false ω) z ∈
        (uniqueInfiniteComponent h₀).supp :=
      fun z =>
      hmem₀ _ (infinite_planarCoarseAnchor hP₀ z)
    simp only [hL, hk _ (hA' _)]
    ring

end Planes

/-- **(3.13) in flip form from the two square sums**: `DarioFlipSumBound` holds if, for the conull
sets `G` of the measurable corrector, there are `s, C > 0` such that for all `i, j`, `r ≥ 1` and
`x`, `Σ_e T₁(e)²` (Step 1) and `Σ_e T₂(e)²` (Step 2) are almost surely finite and `≤ O_s(C/r²)`. -/
theorem darioFlipSumBound_of_stepSums
    (h : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
        (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
          ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumOne hG hGv i j r x ω < ∞) ∧
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumTwo hG hGv i j r x ω < ∞) ∧
            IsOsBond 2 p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C / r ^ 2) ∧
            IsOsBond 2 p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ 2)) :
    DarioFlipSumBound := by
  refine darioFlipSumBound_of_sums fun p hpc hp1 G hG hGv hGae => ?_
  obtain ⟨s, C, hs, hC, hb⟩ := h p hpc hp1 G hG hGv hGae
  refine ⟨s, C, hs, hC, fun i j r hr x => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hb i j r hr x
  refine ⟨?_, h1, h2, h3, h4⟩
  filter_upwards [ae_flipTermTwoSummable hG hGv hpc hp1 hGae] with ω hω e
  exact hω i j r (by linarith) x e

end Rigidity.Corrector

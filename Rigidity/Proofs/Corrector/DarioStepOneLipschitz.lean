import Rigidity.Proofs.Corrector.DarioFlipTermTwoSummable

/-!
# Step 1 of Lemma 3.3 of Dario with the Lipschitz bounds of the corrector

The term `T₁(e)` of the split (3.15) in flip form (`flipTermOne`) is the heat average of
`partitionChange ω⁰ ω¹ χ₁`, which only sees the values of `χ₁` at anchors, all in the infinite
cluster of `ω¹ = ω^{e,1}`. Replacing `χ₁` by its restriction to that cluster, the total variations
of Step 1 over the open edges of `ω⁰ = ω^{e,0}` and of `ω¹` are both at most the one over the open
edges of `ω¹` (`edgeVariationIn_mono_config`), hence at most `4 Σ_{z ∈ box} Λ(z)` for Lipschitz
bounds `Λ` of the corrector of `ω¹` (`edgeVariationIn_correctorDiff_le`). Under the locality of
the change of partition (`ResampleLocal ρ M`, from Lemma 3.5):

`T₁(e)² ≤ |B| (Σ_{y ∈ B} Φ_{r²}(x, y)²) (8 Σ_{z ∈ B'} Λ(z))²` (`flipTermOne_sq_le`),

with `B` the box of radius `ρ` and `B'` the box of radius `(ρ + 1) + 5M` around the endpoint of
`e`; this is (3.16) of Dario with the Lipschitz bound (3.19) inserted.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare
open scoped Classical

/-- The total variation over the open edges grows with the set of open edges. -/
theorem edgeVariationIn_mono_config {ω ω' : Configuration 2}
    (h : ∀ x y, (openGraph ω).Adj x y → (openGraph ω').Adj x y) (S : Finset (Vertex 2))
    (w : Vertex 2 → ℝ) : edgeVariationIn ω S w ≤ edgeVariationIn ω' S w := by
  unfold edgeVariationIn
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  by_cases hxy : (openGraph ω).Adj x y
  · rw [if_pos hxy, if_pos (h x y hxy)]
  · rw [if_neg hxy]
    split_ifs <;> positivity

section Lipschitz

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **Step 1 with the Lipschitz bounds**: `T₁(e)² ≤ |B| (Σ_{y ∈ B} Φ²) (8 Σ_{z ∈ B'} Λ(z))²`. -/
theorem flipTermOne_sq_le {e : Bond 2} {ω : Configuration 2} (hω₁ : setBond e true ω ∈ G)
    (hP₁ : PlanarPartitionEvent (setBond e true ω)) (hP₀ : PlanarPartitionEvent (setBond e false ω))
    {ρ M : ℕ} {a : Vertex 2} (hloc : ResampleLocal ρ M (setBond e false ω) (setBond e true ω) a)
    {i : Fin 2} {Λ : Vertex 2 → ℝ} (hΛ0 : ∀ z, 0 ≤ Λ z)
    (hΛ : ∀ z, setBond e true ω ∈ infiniteComponentEvent z → ∀ y,
      (openGraph (setBond e true ω)).Adj z y →
        |correctorDiff hG hGv (Pi.single i 1) (setBond e true ω) z y| ≤ Λ z)
    (j : Fin 2) (r : ℝ) (x : Vertex 2) :
    flipTermOne hG hGv i j r x e ω ^ 2 ≤
      (supBox a ρ).card * (∑ y ∈ supBox a ρ, latticeHeat (r ^ 2) x y ^ 2) *
        (8 * ∑ z ∈ supBox a ((ρ + 1) + 5 * M), Λ z) ^ 2 := by
  set w : Vertex 2 → ℝ := fun v => if setBond e true ω ∈ infiniteComponentEvent v then
    correctorDiff hG hGv (Pi.single i 1) (setBond e true ω) v (guardAnchor (setBond e false ω) 0)
    else 0 with hw
  -- the anchors of both partitions lie in the infinite cluster of `ω¹`
  have hA₁ : ∀ z, setBond e true ω ∈
      infiniteComponentEvent (planarCoarseAnchor (setBond e true ω) z) :=
    fun z => infinite_planarCoarseAnchor hP₁ z
  have hA₀ : ∀ z, setBond e true ω ∈
      infiniteComponentEvent (planarCoarseAnchor (setBond e false ω) z) :=
    fun z => infiniteComponentEvent_setBond_true (infinite_planarCoarseAnchor hP₀ z) true
  have hpc : ∀ y, partitionChange (setBond e false ω) (setBond e true ω)
      (flipCorrector hG hGv i true e ω) j y =
      partitionChange (setBond e false ω) (setBond e true ω) w j y := fun y => by
    simp only [partitionChange, hw, if_pos (hA₁ _), if_pos (hA₀ _)]
    rfl
  rw [flipTermOne_eq_tsum_partitionChange hG hGv hP₁ hP₀]
  rw [tsum_congr fun y => by rw [hpc y]]
  refine (sq_tsum_partitionChange_le hloc hP₀ hP₁ (fun y => latticeHeat (r ^ 2) x y) w j).trans ?_
  have ho : setBond e true ω ∈ infiniteComponentEvent (guardAnchor (setBond e false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact hA₀ 0
  set S := supBox a ((ρ + 1) + 5 * M)
  have hV₁ : edgeVariationIn (setBond e true ω) S w ≤ 4 * ∑ z ∈ S, Λ z :=
    edgeVariationIn_correctorDiff_le hG hGv hω₁ ho S hΛ0 hΛ
  have hV₀ : edgeVariationIn (setBond e false ω) S w ≤ edgeVariationIn (setBond e true ω) S w :=
    edgeVariationIn_mono_config (fun u v huv => openGraph_setBond_le e ω huv) S w
  have h0 := edgeVariationIn_nonneg (setBond e false ω) S w
  have hsum : edgeVariationIn (setBond e false ω) S w + edgeVariationIn (setBond e true ω) S w ≤
      8 * ∑ z ∈ S, Λ z := by linarith
  have hB : (0 : ℝ) ≤ (supBox a ρ).card * ∑ y ∈ supBox a ρ, latticeHeat (r ^ 2) x y ^ 2 := by
    positivity
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (add_nonneg h0 (edgeVariationIn_nonneg _ _ _)) hsum 2) hB

end Lipschitz

end Rigidity.Corrector

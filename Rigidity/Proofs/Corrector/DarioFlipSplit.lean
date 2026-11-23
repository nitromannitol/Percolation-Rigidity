import Rigidity.Proofs.Corrector.DarioStepOneLocal
import Rigidity.Proofs.Corrector.DarioLemmaThreeThreeFlip
import Rigidity.Proofs.Corrector.DarioCaseThreeCorrector

/-!
# The split (3.15) of Dario in flip form

The variable of Lemma 3.3 is `X(ω) = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)`, built in `heatCoarseComp` from the
measurable corrector increments `correctorDiff` at the anchors `guardAnchor` of the planar
partition. On the partition event and on the set `G` of the measurable corrector, with a corrected
plane `ℓ` of slope `e_i` on the infinite cluster and `χ = ℓ - e_i · (·)` (`planeCorrector`),
`X(ω) = Φ_{r²} * ∇_j(χ ∘ z̄_ω)(x)` (`heatCoarseComp_eq_heatComp_planeCorrector`).

For the flips `ω¹ = ω^{e,1}`, `ω⁰ = ω^{e,0}` the flip difference `D_e X = X(ω¹) - X(ω⁰)` splits as
Dario's (3.15) with the corrector of `ω¹` coarsened by the partition of `ω⁰` as intermediate
(`bondFlipDiff_heatCoarseComp_eq`): the term (3.15)-(i) is the heat average of
`partitionChange ω⁰ ω¹ χ₁` (change of partition, same corrector) and the term (3.15)-(ii) is
`Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_{𝒫⁰}(x)` (change of corrector, same partition), the quantity of Cases 1-3
of Step 2. With Step 1 (`sq_tsum_partitionChange_le`) this gives
`sq_bondFlipDiff_heatCoarseComp_le`:
`(D_e X)² ≤ 2 |B| (Σ_{y ∈ B} Φ_{r²}(x, y)²) (V₀ + V₁)² + 2 (Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_{𝒫⁰}(x))²`.
The series are assumed summable.
-/

namespace Rigidity.Corrector

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Poincare
open scoped Classical

/-- The corrector `χ = ℓ - q · (·)` of a corrected plane `ℓ` of slope `q` on a component, with `ℓ`
extended by zero off the component. -/
noncomputable def planeCorrector {ω : Configuration 2} (K : OpenComponent ω) (ℓ : K → ℝ)
    (q : Fin 2 → ℝ) (z : Vertex 2) : ℝ :=
  extendComp K ℓ z - ∑ i, q i * (z i : ℝ)

/-- The heat average of a gradient does not see additive constants. -/
theorem heatComp_add_const (u : Vertex 2 → ℝ) (c r : ℝ) (x : Vertex 2) (j : Fin 2) :
    heatComp (fun z => u z + c) r x j = heatComp u r x j := by
  unfold heatComp
  exact tsum_congr fun y => by ring

section Plane

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The coarsened corrector through a corrected plane**: on the partition event and on `G`,
`[χ_{e_i}]_𝒫(z) - [χ_{e_i}]_𝒫(0) = χ(z̄(z)) - χ(z̄(0))` for `χ = ℓ - e_i · (·)` and every corrected
plane `ℓ` of slope `e_i` on the infinite cluster. -/
theorem coarseField_eq_planeCorrector {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) (h : HasUniqueInfiniteOpenComponent ω) (i : Fin 2)
    {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ) (z : Vertex 2) :
    coarseField hG hGv i 0 z ω =
      planeCorrector _ ℓ (Pi.single i 1) (planarCoarseAnchor ω z) -
        planeCorrector _ ℓ (Pi.single i 1) (planarCoarseAnchor ω 0) := by
  have ha : planarCoarseAnchor ω z ∈ (uniqueInfiniteComponent h).supp :=
    (mem_uniqueInfiniteComponent_iff h _).2 (infinite_planarCoarseAnchor hP z)
  have hb : planarCoarseAnchor ω 0 ∈ (uniqueInfiniteComponent h).supp :=
    (mem_uniqueInfiniteComponent_iff h _).2 (infinite_planarCoarseAnchor hP 0)
  unfold coarseField
  rw [shiftedAnchor_zero, shiftedAnchor_zero, guardAnchor_of_event hP, guardAnchor_of_event hP]
  refine (correctorDiff_eq hG hGv hω (uniqueInfiniteComponent_infinite h) hℓ ⟨_, ha⟩
    ⟨_, hb⟩).trans ?_
  rw [planeCorrector, planeCorrector, extendComp_of_mem _ _ ha, extendComp_of_mem _ _ hb]

/-- **The variable of Lemma 3.3 through a corrected plane**: `X(ω) = Φ_{r²} * ∇_j(χ ∘ z̄_ω)(x)`. -/
theorem heatCoarseComp_eq_heatComp_planeCorrector {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) (h : HasUniqueInfiniteOpenComponent ω) (i j : Fin 2)
    {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ) (r : ℝ) (x : Vertex 2) :
    heatCoarseComp hG hGv i j r x ω =
      heatComp (fun z => planeCorrector _ ℓ (Pi.single i 1) (planarCoarseAnchor ω z)) r x j := by
  unfold heatCoarseComp
  have e : (fun z => coarseField hG hGv i 0 z ω) = fun z =>
      planeCorrector _ ℓ (Pi.single i 1) (planarCoarseAnchor ω z) +
        -planeCorrector _ ℓ (Pi.single i 1) (planarCoarseAnchor ω 0) := by
    funext z
    rw [coarseField_eq_planeCorrector hG hGv hω hP h i hℓ z]
    ring
  rw [e, heatComp_add_const]

end Plane

/-- **The split (3.15), abstractly**: for functions `u₀, u₁` and anchor maps `A₀, A₁`,
`Φ * ∇_j(u₁ ∘ A₁) - Φ * ∇_j(u₀ ∘ A₀)` is the heat average of the change of anchors for `u₁`
plus `Φ * ∇_j((u₁ - u₀) ∘ A₀)`, when the three series converge. -/
theorem heatComp_sub_eq_split (A₀ A₁ : Vertex 2 → Vertex 2) (u₀ u₁ : Vertex 2 → ℝ) (r : ℝ)
    (x : Vertex 2) (j : Fin 2)
    (hS₁ : Summable fun y => latticeHeat (r ^ 2) x y *
      (u₁ (A₁ (y + LatticeProb.unit j)) - u₁ (A₁ y)))
    (hS₂ : Summable fun y => latticeHeat (r ^ 2) x y *
      (u₁ (A₀ (y + LatticeProb.unit j)) - u₁ (A₀ y)))
    (hS₃ : Summable fun y => latticeHeat (r ^ 2) x y *
      (u₀ (A₀ (y + LatticeProb.unit j)) - u₀ (A₀ y))) :
    heatComp (fun z => u₁ (A₁ z)) r x j - heatComp (fun z => u₀ (A₀ z)) r x j =
      (∑' y, latticeHeat (r ^ 2) x y *
        ((u₁ (A₁ (y + LatticeProb.unit j)) - u₁ (A₁ y)) -
          (u₁ (A₀ (y + LatticeProb.unit j)) - u₁ (A₀ y)))) +
        heatComp (fun z => u₁ (A₀ z) - u₀ (A₀ z)) r x j := by
  unfold heatComp
  calc (∑' y, latticeHeat (r ^ 2) x y * (u₁ (A₁ (y + LatticeProb.unit j)) - u₁ (A₁ y))) -
        ∑' y, latticeHeat (r ^ 2) x y * (u₀ (A₀ (y + LatticeProb.unit j)) - u₀ (A₀ y))
      = ((∑' y, latticeHeat (r ^ 2) x y * (u₁ (A₁ (y + LatticeProb.unit j)) - u₁ (A₁ y))) -
          ∑' y, latticeHeat (r ^ 2) x y * (u₁ (A₀ (y + LatticeProb.unit j)) - u₁ (A₀ y))) +
        ((∑' y, latticeHeat (r ^ 2) x y * (u₁ (A₀ (y + LatticeProb.unit j)) - u₁ (A₀ y))) -
          ∑' y, latticeHeat (r ^ 2) x y * (u₀ (A₀ (y + LatticeProb.unit j)) - u₀ (A₀ y))) := by
        ring
    _ = _ := by
        rw [← hS₁.tsum_sub hS₂, ← hS₂.tsum_sub hS₃]
        congr 1
        · exact tsum_congr fun y => by ring
        · exact tsum_congr fun y => by ring

section Flip

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **Dario's split (3.15) in flip form**: for the flips `ω¹ = ω^{e,1}`, `ω⁰ = ω^{e,0}` in `G` and
in the partition event, with corrected planes `ℓ₁, ℓ₀` of slope `e_i` and `χ₁ = ℓ₁ - e_i · (·)`,
`D_e X = Σ_y Φ_{r²}(x, y) partitionChange ω⁰ ω¹ χ₁ j y + Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_{𝒫⁰}(x)`. -/
theorem bondFlipDiff_heatCoarseComp_eq {e : Bond 2} {ω : Configuration 2}
    (hω₁ : setBond e true ω ∈ G) (hω₀ : setBond e false ω ∈ G)
    (hP₁ : PlanarPartitionEvent (setBond e true ω)) (hP₀ : PlanarPartitionEvent (setBond e false ω))
    (h₁ : HasUniqueInfiniteOpenComponent (setBond e true ω))
    (h₀ : HasUniqueInfiniteOpenComponent (setBond e false ω)) (i j : Fin 2)
    {ℓ₁ : uniqueInfiniteComponent h₁ → ℝ} {ℓ₀ : uniqueInfiniteComponent h₀ → ℝ}
    (hℓ₁ : IsCorrectedPlane (uniqueInfiniteComponent h₁) (Pi.single i 1) ℓ₁)
    (hℓ₀ : IsCorrectedPlane (uniqueInfiniteComponent h₀) (Pi.single i 1) ℓ₀) (r : ℝ) (x : Vertex 2)
    (hS₁ : Summable fun y => latticeHeat (r ^ 2) x y *
      (planeCorrector _ ℓ₁ (Pi.single i 1)
          (planarCoarseAnchor (setBond e true ω) (y + LatticeProb.unit j)) -
        planeCorrector _ ℓ₁ (Pi.single i 1) (planarCoarseAnchor (setBond e true ω) y)))
    (hS₂ : Summable fun y => latticeHeat (r ^ 2) x y *
      (planeCorrector _ ℓ₁ (Pi.single i 1)
          (planarCoarseAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        planeCorrector _ ℓ₁ (Pi.single i 1) (planarCoarseAnchor (setBond e false ω) y)))
    (hS₃ : Summable fun y => latticeHeat (r ^ 2) x y *
      (planeCorrector _ ℓ₀ (Pi.single i 1)
          (planarCoarseAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        planeCorrector _ ℓ₀ (Pi.single i 1) (planarCoarseAnchor (setBond e false ω) y))) :
    bondFlipDiff (heatCoarseComp hG hGv i j r x) e ω =
      (∑' y, latticeHeat (r ^ 2) x y * partitionChange (setBond e false ω) (setBond e true ω)
        (planeCorrector _ ℓ₁ (Pi.single i 1)) j y) +
        heatComp (fun z => extendComp _ ℓ₁ (planarCoarseAnchor (setBond e false ω) z) -
          extendComp _ ℓ₀ (planarCoarseAnchor (setBond e false ω) z)) r x j := by
  unfold bondFlipDiff
  rw [heatCoarseComp_eq_heatComp_planeCorrector hG hGv hω₁ hP₁ h₁ i j hℓ₁ r x,
    heatCoarseComp_eq_heatComp_planeCorrector hG hGv hω₀ hP₀ h₀ i j hℓ₀ r x,
    heatComp_sub_eq_split _ _ _ _ r x j hS₁ hS₂ hS₃]
  congr 1
  have e2 : (fun z => planeCorrector _ ℓ₁ (Pi.single i 1)
        (planarCoarseAnchor (setBond e false ω) z) -
      planeCorrector _ ℓ₀ (Pi.single i 1) (planarCoarseAnchor (setBond e false ω) z)) =
      fun z => extendComp _ ℓ₁ (planarCoarseAnchor (setBond e false ω) z) -
        extendComp _ ℓ₀ (planarCoarseAnchor (setBond e false ω) z) := by
    funext z
    simp only [planeCorrector]
    ring
  rw [e2]

/-- **(3.15) with Step 1, in flip form**: under the locality of the change of partition
(`ResampleLocal ρ M`, from Lemma 3.5),
`(D_e X)² ≤ 2 |B| (Σ_{y ∈ B} Φ_{r²}(x, y)²) (V₀ + V₁)² + 2 (Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_{𝒫⁰}(x))²`, with `B`
the box of radius `ρ` around the endpoint `a` and `V_b` the total variation of `χ₁` over the open
edges of `ω^{e,b}` in the box of radius `(ρ + 1) + 5M` around `a`. -/
theorem sq_bondFlipDiff_heatCoarseComp_le {e : Bond 2} {ω : Configuration 2}
    (hω₁ : setBond e true ω ∈ G) (hω₀ : setBond e false ω ∈ G)
    (hP₁ : PlanarPartitionEvent (setBond e true ω)) (hP₀ : PlanarPartitionEvent (setBond e false ω))
    (h₁ : HasUniqueInfiniteOpenComponent (setBond e true ω))
    (h₀ : HasUniqueInfiniteOpenComponent (setBond e false ω)) (i j : Fin 2)
    {ℓ₁ : uniqueInfiniteComponent h₁ → ℝ} {ℓ₀ : uniqueInfiniteComponent h₀ → ℝ}
    (hℓ₁ : IsCorrectedPlane (uniqueInfiniteComponent h₁) (Pi.single i 1) ℓ₁)
    (hℓ₀ : IsCorrectedPlane (uniqueInfiniteComponent h₀) (Pi.single i 1) ℓ₀) (r : ℝ) (x : Vertex 2)
    (hS₁ : Summable fun y => latticeHeat (r ^ 2) x y *
      (planeCorrector _ ℓ₁ (Pi.single i 1)
          (planarCoarseAnchor (setBond e true ω) (y + LatticeProb.unit j)) -
        planeCorrector _ ℓ₁ (Pi.single i 1) (planarCoarseAnchor (setBond e true ω) y)))
    (hS₂ : Summable fun y => latticeHeat (r ^ 2) x y *
      (planeCorrector _ ℓ₁ (Pi.single i 1)
          (planarCoarseAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        planeCorrector _ ℓ₁ (Pi.single i 1) (planarCoarseAnchor (setBond e false ω) y)))
    (hS₃ : Summable fun y => latticeHeat (r ^ 2) x y *
      (planeCorrector _ ℓ₀ (Pi.single i 1)
          (planarCoarseAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        planeCorrector _ ℓ₀ (Pi.single i 1) (planarCoarseAnchor (setBond e false ω) y)))
    {ρ M : ℕ} {a : Vertex 2}
    (hloc : ResampleLocal ρ M (setBond e false ω) (setBond e true ω) a) :
    bondFlipDiff (heatCoarseComp hG hGv i j r x) e ω ^ 2 ≤
      2 * ((supBox a ρ).card * (∑ y ∈ supBox a ρ, latticeHeat (r ^ 2) x y ^ 2) *
        (edgeVariationIn (setBond e false ω) (supBox a ((ρ + 1) + 5 * M))
            (planeCorrector _ ℓ₁ (Pi.single i 1)) +
          edgeVariationIn (setBond e true ω) (supBox a ((ρ + 1) + 5 * M))
            (planeCorrector _ ℓ₁ (Pi.single i 1))) ^ 2) +
      2 * heatComp (fun z => extendComp _ ℓ₁ (planarCoarseAnchor (setBond e false ω) z) -
          extendComp _ ℓ₀ (planarCoarseAnchor (setBond e false ω) z)) r x j ^ 2 := by
  rw [bondFlipDiff_heatCoarseComp_eq hG hGv hω₁ hω₀ hP₁ hP₀ h₁ h₀ i j hℓ₁ hℓ₀ r x hS₁ hS₂ hS₃]
  have h1 := sq_tsum_partitionChange_le hloc hP₀ hP₁ (fun y => latticeHeat (r ^ 2) x y)
    (planeCorrector _ ℓ₁ (Pi.single i 1)) j
  set A := ∑' y, latticeHeat (r ^ 2) x y * partitionChange (setBond e false ω) (setBond e true ω)
    (planeCorrector _ ℓ₁ (Pi.single i 1)) j y
  set B := heatComp (fun z => extendComp _ ℓ₁ (planarCoarseAnchor (setBond e false ω) z) -
    extendComp _ ℓ₀ (planarCoarseAnchor (setBond e false ω) z)) r x j
  nlinarith [sq_nonneg (A - B)]

end Flip

end Rigidity.Corrector

import Rigidity.Proofs.Green.DarioGuFluxPairing
import Rigidity.Proofs.Corrector.DarioCoarsenedFields
import Rigidity.Proofs.Corrector.DarioBondResampling

/-!
# The heat average of the flux as a random variable

On a measurable conull set `G` of configurations where the planar corrector input holds, the flux
of the corrected plane of slope `e_k` along the oriented edge `b` is the measurable function
`fluxVal k ω b` built from the measurable corrector increments `correctorDiff`
(`fluxVal_eq_planeFlux`), and its heat average `fluxObs k i r x = Σ_z Φ_{r²}(x, z) fluxVal(z, i)` is
measurable (`measurable_fluxObs`). This is the random variable `X = K_R ⋆ [g_p](x)` of Gu's proof of
Proposition 1.1 (Step 1), with `K_R = Φ_{r²}`, before centering. Its flip difference is the
difference of the heat averages of the fluxes of the corrected planes of `ω^{e,1}` and `ω^{e,0}`
(`bondFlipDiff_fluxObs_eq`), to which the formulas of `DarioGuFluxPairing` apply.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Corrector
open scoped Classical

section Observable

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The flux of the corrected plane of slope `e_k` along the oriented edge `b`, through the
measurable corrector increments. -/
noncomputable def fluxVal (k : Fin 2) (ω : Configuration 2) (b : LatticeEdge) : ℝ :=
  if EdgeOpen ω b ∧ ω ∈ infiniteComponentEvent b.1 then
    correctorDiff hG hGv (Pi.single k 1) ω (edgeHead b) b.1 + (if b.2 = k then 1 else 0)
  else 0

theorem measurableSet_edgeOpen (b : LatticeEdge) :
    MeasurableSet {ω : Configuration 2 | EdgeOpen ω b} := by
  have e : {ω : Configuration 2 | EdgeOpen ω b} = (fun ω : Configuration 2 => ω (edgeBond b)) ⁻¹'
      {true} := by
    ext ω
    simp [edgeOpen_iff]
  rw [e]
  exact (measurable_pi_apply (edgeBond b)) (measurableSet_singleton true)

theorem measurable_fluxVal (k : Fin 2) (b : LatticeEdge) :
    Measurable fun ω => fluxVal hG hGv k ω b := by
  unfold fluxVal
  exact Measurable.ite ((measurableSet_edgeOpen b).inter (measurableSet_infiniteComponentEvent b.1))
    ((measurable_correctorDiff hG hGv _ _ _).add_const _) measurable_const

theorem sum_single_mul_edgeHead_sub (k : Fin 2) (b : LatticeEdge) :
    ∑ j, (Pi.single k (1 : ℝ) : Fin 2 → ℝ) j * ((edgeHead b) j : ℝ) -
        ∑ j, (Pi.single k (1 : ℝ) : Fin 2 → ℝ) j * (b.1 j : ℝ) =
      if b.2 = k then 1 else 0 := by
  obtain ⟨z, j⟩ := b
  fin_cases k <;> fin_cases j <;> simp [edgeHead, LatticeProb.unit, Fin.sum_univ_two]

/-- **The measurable flux is the flux of the corrected plane.** -/
theorem fluxVal_eq_planeFlux {k : Fin 2} {ω : Configuration 2} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single k 1) ℓ) (b : LatticeEdge) :
    fluxVal hG hGv k ω b = planeFlux (uniqueInfiniteComponent h) ℓ b := by
  unfold fluxVal planeFlux
  have e : (EdgeOpen ω b ∧ ω ∈ infiniteComponentEvent b.1) ↔
      (EdgeOpen ω b ∧ b.1 ∈ (uniqueInfiniteComponent h).supp) :=
    and_congr_right fun _ => (mem_uniqueInfiniteComponent_iff h b.1).symm
  by_cases hc : EdgeOpen ω b ∧ b.1 ∈ (uniqueInfiniteComponent h).supp
  · rw [if_pos (e.2 hc), if_pos hc]
    have hy : edgeHead b ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hc.2 hc.1
    rw [correctorDiff_eq hG hGv hω (uniqueInfiniteComponent_infinite h) hℓ ⟨edgeHead b, hy⟩
      ⟨b.1, hc.2⟩, extendComp_of_mem _ _ hy, extendComp_of_mem _ _ hc.2]
    have hs := sum_single_mul_edgeHead_sub k b
    linarith
  · rw [if_neg (fun h' => hc (e.1 h')), if_neg hc]

/-- **The heat average of the flux**, `X = Σ_z Φ_{r²}(x, z) flux_{e_k}(z, i)`. -/
noncomputable def fluxObs (k i : Fin 2) (r : ℝ) (x : Vertex 2) (ω : Configuration 2) : ℝ :=
  ∑' z, latticeHeat (r ^ 2) x z * fluxVal hG hGv k ω (z, i)

theorem measurable_fluxObs (k i : Fin 2) (r : ℝ) (x : Vertex 2) :
    Measurable (fluxObs hG hGv k i r x) := by
  unfold fluxObs
  exact Measurable.tsum fun z => (measurable_fluxVal hG hGv k (z, i)).const_mul _

/-- The heat average of the flux through a corrected plane. -/
theorem fluxObs_eq {k : Fin 2} {ω : Configuration 2} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single k 1) ℓ) (i : Fin 2) (r : ℝ)
    (x : Vertex 2) :
    fluxObs hG hGv k i r x ω =
      ∑' z, latticeHeat (r ^ 2) x z * planeFlux (uniqueInfiniteComponent h) ℓ (z, i) := by
  unfold fluxObs
  exact tsum_congr fun z => by rw [fluxVal_eq_planeFlux hG hGv hω h hℓ]

/-- **The flip difference of the heat average of the flux**: if `ω^{e,1}, ω^{e,0} ∈ G`, it is the
difference of the heat averages of the fluxes of corrected planes of slope `e_k` of `ω^{e,1}` and
`ω^{e,0}`. -/
theorem bondFlipDiff_fluxObs_eq {k : Fin 2} {a : LatticeEdge} {ω : Configuration 2}
    (h1G : setBond (edgeBond a) true ω ∈ G) (h0G : setBond (edgeBond a) false ω ∈ G)
    (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
    (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
    {ℓ₁ : uniqueInfiniteComponent h₁ → ℝ} {ℓ₀ : uniqueInfiniteComponent h₀ → ℝ}
    (hℓ₁ : IsCorrectedPlane (uniqueInfiniteComponent h₁) (Pi.single k 1) ℓ₁)
    (hℓ₀ : IsCorrectedPlane (uniqueInfiniteComponent h₀) (Pi.single k 1) ℓ₀) (i : Fin 2) (r : ℝ)
    (x : Vertex 2) :
    bondFlipDiff (fluxObs hG hGv k i r x) (edgeBond a) ω =
      (∑' z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₁ (z, i)) -
        ∑' z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₀ (z, i) := by
  unfold bondFlipDiff
  rw [fluxObs_eq hG hGv h1G h₁ hℓ₁, fluxObs_eq hG hGv h0G h₀ hℓ₀]

end Observable

end Rigidity.Green

import Rigidity.Proofs.Green.DarioGuFluxOpenBound
import Rigidity.Proofs.Corrector.DarioStepTwoWeight

/-!
# The flip difference of the heat average of the flux for the bonds closed in the configuration

For a bond `e` of `a = (x₀, i')` closed in `ω`, `ω^{e,0} = ω` and, in Case 3, for an open path `π`
of `ω` joining the endpoints,

`D_e X = c' (v(y₀) - v(x₀) - 1{i' = i} Φ_{r²}(x, x₀))` (`ae_heat_planeFlux_sub_closed`)

with `v` the potential of `P_ω h_ω` (the sum of `P_ω h_ω` along `π`) and `c' = ℓ₁(x₀) - ℓ₁(y₀)`
for the corrected plane of `ω^{e,1}`. As in the proof of Lemma 3.3 of Dario for the bonds closed in
`ω` (`DarioStepTwoWeight.ae_flipTermTwo_sq_le_closed`), `|c'| ≤ 16 Σ_B G` and
`(v(y₀) - v(x₀))² ≤ 64 |B| Σ_B E_v` over the box `B` of the two partition cubes, so

`(D_e X)² ≤ 2¹⁵ (Σ_B G)² |B| (Σ_B E_v + Φ_{r²}(x, x₀)²)` (`ae_fluxFlip_sq_le_closed`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Corrector
  Rigidity.External Rigidity.Poincare
open scoped Classical ENNReal

section Bound

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The increment of a corrected plane of `ω^{e,1}` across the bond is the coefficient of
`ae_dipoleCoeff_eq` for `ω^{e,1}`. -/
theorem increment_eq_flipCorrector_true {k : Fin 2} {a : LatticeEdge} {ω : Configuration 2}
    (h1G : setBond (edgeBond a) true ω ∈ G)
    (hP₀ : PlanarPartitionEvent (setBond (edgeBond a) false ω))
    (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
    (hx : a.1 ∈ (uniqueInfiniteComponent h₁).supp)
    (hy : edgeHead a ∈ (uniqueInfiniteComponent h₁).supp) {ℓ₁ : uniqueInfiniteComponent h₁ → ℝ}
    (hℓ₁ : IsCorrectedPlane (uniqueInfiniteComponent h₁) (Pi.single k 1) ℓ₁) :
    extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a) =
      flipCorrector hG hGv k true (edgeBond a) ω a.1 -
        flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
        ((a.1 k : ℝ) - ((edgeHead a) k : ℝ)) := by
  have hA0 : setBond (edgeBond a) false ω ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact infinite_planarCoarseAnchor hP₀ 0
  have hA1 := infiniteComponentEvent_setBond_true hA0 true
  have hxi := (mem_uniqueInfiniteComponent_iff h₁ a.1).1 hx
  have hyi := (mem_uniqueInfiniteComponent_iff h₁ (edgeHead a)).1 hy
  unfold flipCorrector
  rw [correctorDiff_sub_eq hG hGv h1G hxi hyi hA1,
    correctorDiff_eq hG hGv h1G (uniqueInfiniteComponent_infinite h₁) hℓ₁ ⟨a.1, hx⟩
      ⟨edgeHead a, hy⟩, extendComp_of_mem _ _ hx, extendComp_of_mem _ _ hy]
  have hs : ∀ z : Vertex 2, ∑ j, (Pi.single k (1 : ℝ) : Fin 2 → ℝ) j * (z j : ℝ) = (z k : ℝ) := by
    intro z
    fin_cases k <;> simp [Fin.sum_univ_two]
  rw [hs, hs]
  ring

theorem closed_flux_arith {c Δv Δ SG BC SE Φ2 : ℝ} (hc2 : c ^ 2 ≤ (16 * SG) ^ 2)
    (hv : Δv ^ 2 ≤ 64 * BC * SE) (hΔ : Δ ^ 2 ≤ Φ2) (hBC : 1 ≤ BC) (hΦ : 0 ≤ Φ2) :
    (c * (Δv - Δ)) ^ 2 ≤ 2 ^ 15 * SG ^ 2 * BC * (SE + Φ2) := by
  have h1 : (Δv - Δ) ^ 2 ≤ 2 * Δv ^ 2 + 2 * Δ ^ 2 := by nlinarith [sq_nonneg (Δv + Δ)]
  have h2 : (Δv - Δ) ^ 2 ≤ 128 * BC * SE + 2 * Φ2 := by linarith
  calc (c * (Δv - Δ)) ^ 2 = c ^ 2 * (Δv - Δ) ^ 2 := by ring
    _ ≤ (16 * SG) ^ 2 * (128 * BC * SE + 2 * Φ2) :=
        mul_le_mul hc2 h2 (sq_nonneg _) (by positivity)
    _ ≤ 2 ^ 15 * SG ^ 2 * BC * (SE + Φ2) := by
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg SG) hΦ) (sub_nonneg.2 hBC)]

/-- **The flip difference for a bond closed in `ω`.** -/
theorem ae_fluxFlip_sq_le_closed {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (k i : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (a : LatticeEdge), ¬ EdgeOpen ω a → ∀ hP : PlanarPartitionEvent ω,
      bondFlipDiff (fluxObs hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
        2 ^ 15 * (∑ z ∈ supBox a.1 (1 + 5 * max (planarSide ω a.1) (planarSide ω (edgeHead a))),
            planeGrad hG hGv k ω z) ^ 2 *
          (supBox a.1 (1 + 5 * max (planarSide ω a.1) (planarSide ω (edgeHead a)))).card *
          (∑ u ∈ supBox a.1 (1 + 5 * max (planarSide ω a.1) (planarSide ω (edgeHead a))),
            openEnergy ω (clusterPot ω (heatEdge ω r x i)) u + latticeHeat (r ^ 2) x a.1 ^ 2) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_heat_planeFlux_sub_closed hpc hp1,
    ae_heat_planeFlux_sub_eq_zero hpc hp1, ae_dipoleCoeff_eq hG hGv hpc hp1 hGae] with
    ω hG' hwalk hzero hdip k i r hr x a hclosed hP
  have hωe : ω (edgeBond a) = false := by
    rw [edgeOpen_iff] at hclosed
    simpa using hclosed
  have heq : setBond (edgeBond a) false ω = ω := by
    have := setBond_self (edgeBond a) ω
    rwa [hωe] at this
  set B := supBox a.1 (1 + 5 * max (planarSide ω a.1) (planarSide ω (edgeHead a))) with hB
  set SE := ∑ u ∈ B, openEnergy ω (clusterPot ω (heatEdge ω r x i)) u with hSE
  have hE0 : 0 ≤ SE := Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u
  set SG := ∑ z ∈ B, planeGrad hG hGv k ω z with hSG
  have hSG0 : 0 ≤ SG := Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv k ω z
  have hP₀ : PlanarPartitionEvent (setBond (edgeBond a) false ω) := by rw [heq]; exact hP
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single k 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single k 1)
  rw [bondFlipDiff_fluxObs_eq hG hGv (hG' _ true) (hG' _ false) h₁ h₀ hℓ₁ hℓ₀]
  have hBc1 : (1 : ℝ) ≤ B.card := by
    have : a.1 ∈ B := by
      rw [hB, mem_supBox]
      intro i
      simp only [sub_self, abs_zero]
      positivity
    exact_mod_cast Finset.card_pos.2 ⟨a.1, this⟩
  have hRHS0 : 0 ≤ 2 ^ 15 * SG ^ 2 * (B.card : ℝ) * (SE + latticeHeat (r ^ 2) x a.1 ^ 2) := by
    positivity
  by_cases hcase : a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
      edgeHead a ∈ (uniqueInfiniteComponent h₀).supp
  swap
  · rw [hzero a h₁ h₀ hcase _ ℓ₁ ℓ₀ hℓ₁ hℓ₀ r x i]
    simpa using hRHS0
  obtain ⟨hx, hy⟩ := hcase
  have hinf₀ : setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 :=
    (mem_uniqueInfiniteComponent_iff h₀ a.1).1 hx
  have hreach₀ : (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy).symm)
  obtain ⟨pw₀⟩ := hreach₀
  have hinf : ω ∈ infiniteComponentEvent a.1 := by rw [← heq]; exact hinf₀
  have hreach : (openGraph ω).Reachable a.1 (edgeHead a) := by rw [← heq]; exact ⟨pw₀⟩
  have hT := hwalk a h₁ h₀ hx hy _ ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw₀ r hr x i
  have hpot : walkSum (setBond (edgeBond a) false ω)
      (greenProj (setBond (edgeBond a) false ω) (heatEdge (setBond (edgeBond a) false ω) r x i))
        pw₀ = clusterPot ω (heatEdge ω r x i) (edgeHead a) - clusterPot ω (heatEdge ω r x i) a.1 := by
    have key : ∀ (ω' : Configuration 2) (_ : ω' = ω)
        (pw' : (openGraph ω').Walk a.1 (edgeHead a)), ω' ∈ infiniteComponentEvent a.1 →
        walkSum ω' (greenProj ω' (heatEdge ω' r x i)) pw' =
          clusterPot ω (heatEdge ω r x i) (edgeHead a) - clusterPot ω (heatEdge ω r x i) a.1 := by
      intro ω' h pw' hinf'
      subst h
      exact walkSum_greenProj_eq_clusterPot _ pw' hinf'
    exact key _ heq pw₀ hinf₀
  rw [hpot] at hT
  -- the coefficient `c' = ℓ₁(x₀) - ℓ₁(y₀)`
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  rw [increment_eq_flipCorrector_true hG hGv (hG' _ true) hP₀ h₁ ((hC _).2 hx) ((hC _).2 hy) hℓ₁]
    at hT
  obtain ⟨R, hR0, -, hc⟩ := hdip k a hP₀ hinf₀ ⟨pw₀⟩
  have hoinf : ω ∈ infiniteComponentEvent (guardAnchor ω 0) := by
    rw [guardAnchor_of_event hP]
    exact infinite_planarCoarseAnchor hP 0
  have hGω : ω ∈ G := by have := hG' (edgeBond a) false; rwa [heq] at this
  obtain ⟨w, hw⟩ : ∃ w : Vertex 2 → ℝ, w = fun z => if ω ∈ infiniteComponentEvent z then
      correctorDiff hG hGv (Pi.single k 1) ω z (guardAnchor ω 0) + (z k : ℝ) else 0 :=
    ⟨_, rfl⟩
  have hyinf : ω ∈ infiniteComponentEvent (edgeHead a) := by
    change ((openGraph ω).connectedComponentMk (edgeHead a)).supp.Infinite
    rw [← SimpleGraph.ConnectedComponent.sound hreach]
    exact hinf
  have hc' : flipCorrector hG hGv k false (edgeBond a) ω a.1 -
      flipCorrector hG hGv k false (edgeBond a) ω (edgeHead a) +
      ((a.1 k : ℝ) - ((edgeHead a) k : ℝ)) = w a.1 - w (edgeHead a) := by
    rw [hw]
    beta_reduce
    rw [if_pos hinf, if_pos hyinf]
    unfold flipCorrector
    rw [heq]
    ring
  have hwev := abs_sub_le_two_mul_edgeVariation hP (abs_sub_edgeHead_le a) hinf hyinf w
  have hwl : ∀ u w', (openGraph ω).Adj u w' → |w u - w w'| ≤ planeGrad hG hGv k ω u :=
    fun u w' h => by rw [hw]; exact abs_sub_rootedPlane_le hG hGv hGω hoinf h
  have hgx := edgeVariationIn_le_four_mul_sum (cubeRegion ω a.1) (planeGrad_nonneg hG hGv k ω) hwl
  have hgy := edgeVariationIn_le_four_mul_sum (cubeRegion ω (edgeHead a))
    (planeGrad_nonneg hG hGv k ω) hwl
  have hRx : cubeRegion ω a.1 ⊆ B := by
    refine (cubeRegion_subset_supBox hP (L := 0) fun i => by simp).trans (supBox_mono ?_)
    omega
  have hRy : cubeRegion ω (edgeHead a) ⊆ B := by
    refine (cubeRegion_subset_supBox hP (L := 1) fun i => ?_).trans (supBox_mono ?_)
    · rw [abs_sub_comm]
      exact_mod_cast abs_sub_edgeHead_le a i
    · omega
  have hGs : ∀ S ⊆ B, ∑ z ∈ S, planeGrad hG hGv k ω z ≤ SG :=
    fun S hS => Finset.sum_le_sum_of_subset_of_nonneg hS fun z _ _ => planeGrad_nonneg hG hGv k ω z
  have hEs : ∀ S ⊆ B, ∑ u ∈ S, openEnergy ω (clusterPot ω (heatEdge ω r x i)) u ≤ SE :=
    fun S hS => Finset.sum_le_sum_of_subset_of_nonneg hS fun u _ _ => openEnergy_nonneg _ _ u
  have hcard : ∀ S ⊆ B, (S.card : ℝ) ≤ B.card := fun S hS => by
    exact_mod_cast Finset.card_le_card hS
  have hcb : |w a.1 - w (edgeHead a)| ≤ 16 * SG := by
    have := hGs _ hRx
    have := hGs _ hRy
    linarith
  have hvb : (clusterPot ω (heatEdge ω r x i) (edgeHead a) -
      clusterPot ω (heatEdge ω r x i) a.1) ^ 2 ≤ 64 * B.card * SE := by
    have hev := abs_sub_le_two_mul_edgeVariation hP (abs_sub_edgeHead_le a) hinf hyinf
      (clusterPot ω (heatEdge ω r x i))
    have h1 := sq_edgeVariationIn_le ω (cubeRegion ω a.1) (clusterPot ω (heatEdge ω r x i))
    have h2 := sq_edgeVariationIn_le ω (cubeRegion ω (edgeHead a)) (clusterPot ω (heatEdge ω r x i))
    have h1' := hEs _ hRx
    have h2' := hEs _ hRy
    have hc1 := hcard _ hRx
    have hc2 := hcard _ hRy
    have hB1 : edgeVariationIn ω (cubeRegion ω a.1) (clusterPot ω (heatEdge ω r x i)) ^ 2 ≤
        4 * B.card * SE := by
      have := mul_le_mul hc1 h1' (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u)
        (Nat.cast_nonneg _)
      linarith
    have hB2 : edgeVariationIn ω (cubeRegion ω (edgeHead a)) (clusterPot ω (heatEdge ω r x i)) ^ 2 ≤
        4 * B.card * SE := by
      have := mul_le_mul hc2 h2' (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u)
        (Nat.cast_nonneg _)
      linarith
    rw [abs_sub_comm] at hev
    have := sq_le_of_abs_le_two_mul_add hev hB1 hB2
    linarith
  have hcc : |flipCorrector hG hGv k true (edgeBond a) ω a.1 -
      flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
      ((a.1 k : ℝ) - ((edgeHead a) k : ℝ))| ≤ |w a.1 - w (edgeHead a)| := by
    rw [← hc', hc, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + R)]
    have := abs_nonneg (flipCorrector hG hGv k true (edgeBond a) ω a.1 -
      flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
      ((a.1 k : ℝ) - ((edgeHead a) k : ℝ)))
    nlinarith
  have hΔ : (if a.2 = i then latticeHeat (r ^ 2) x a.1 else 0) ^ 2 ≤
      latticeHeat (r ^ 2) x a.1 ^ 2 := by
    split_ifs
    · exact le_rfl
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  have hc2 : (flipCorrector hG hGv k true (edgeBond a) ω a.1 -
      flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
      ((a.1 k : ℝ) - ((edgeHead a) k : ℝ))) ^ 2 ≤ (16 * SG) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hcc.trans hcb) 2
  rw [hT]
  exact closed_flux_arith hc2 hvb hΔ hBc1 (sq_nonneg _)

end Bound

end Rigidity.Green

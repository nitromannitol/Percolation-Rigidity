import Rigidity.Proofs.Green.GeneralFluxPairing
import Rigidity.Proofs.Corrector.GeneralStepTwoClosedBound

/-!
# The flip difference of the flux on `ℤ^d` for the bonds closed in the configuration

The extension of `DarioGuFluxClosedBound.lean` from `ℤ²` to `ℤ^d`. For a bond `e` of
`a = (x₀, i')` closed in `ω`, `ω^{e,0} = ω` and, in Case 3, for an open path `π` of `ω` joining
the endpoints,

`D_e X = c' (v(y₀) - v(x₀) - 1{i' = i} Φ_{r²}(x, x₀))` (`fluxPairingClosedD_holds`)

with `v` the potential of `P_ω h_ω` on the infinite cluster (the sum of `P_ω h_ω` along `π`), `h_ω`
the heat field of the edges, and `c' = ℓ₁(x₀) - ℓ₁(y₀)` for the corrected plane of `ω^{e,1}`. As in
the proof of Lemma 3.3 of Dario (*Optimal corrector estimates on percolation clusters*) for the
bonds closed in `ω` (`Rigidity.Corrector.GeneralDim.ae_flipTermTwo_sq_le_closed`), both factors are
bounded through the total variations over the boxes `anchorBox` of the partition cubes at `x₀` and
`y₀`, which lie in the box `B` of radius `1 + 5 max(s(x₀), s(y₀))` around `x₀`:
`|c'| ≤ 8d Σ_B G` and `(v(y₀) - v(x₀))² ≤ 32d |B| Σ_B E_v`, so

`(D_e X)² ≤ 4096 d³ (Σ_B G)² |B| (Σ_B E_v + Φ_{r²}(x, x₀)²)` (`ae_fluxFlipD_sq_le_closed`).

The planar statement has the constant `2¹⁵` and the planar boxes of the partition cubes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Corrector.GeneralDim
open Rigidity.Corrector (correctorDiff correctorDiff_eq)
open Rigidity.Poincare.GeneralDim (zdHeat zdHeat_nonneg)
open scoped Classical ENNReal InnerProductSpace

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

theorem closed_flux_arithD {c Δv Δ SG BC SE Φ2 D : ℝ} (hD : 1 ≤ D) (hc2 : c ^ 2 ≤ (8 * D * SG) ^ 2)
    (hv : Δv ^ 2 ≤ 32 * D * BC * SE) (hΔ : Δ ^ 2 ≤ Φ2) (hBC : 1 ≤ BC) :
    (c * (Δv - Δ)) ^ 2 ≤ 4096 * D ^ 3 * SG ^ 2 * BC * (SE + Φ2) := by
  have h1 : (Δv - Δ) ^ 2 ≤ 2 * Δv ^ 2 + 2 * Δ ^ 2 := by nlinarith [sq_nonneg (Δv + Δ)]
  have h2 : (Δv - Δ) ^ 2 ≤ 64 * D * BC * SE + 2 * Φ2 := by linarith
  have hSG2 : 0 ≤ SG ^ 2 := sq_nonneg _
  have hD0 : 0 ≤ D := by linarith
  have hk : 2 * Φ2 ≤ 64 * D * BC * Φ2 := by
    have : (2 : ℝ) ≤ 64 * D * BC := by nlinarith
    nlinarith
  calc (c * (Δv - Δ)) ^ 2 = c ^ 2 * (Δv - Δ) ^ 2 := by ring
    _ ≤ (8 * D * SG) ^ 2 * (64 * D * BC * SE + 2 * Φ2) :=
        mul_le_mul hc2 h2 (sq_nonneg _) (by positivity)
    _ ≤ (8 * D * SG) ^ 2 * (64 * D * BC * SE + 64 * D * BC * Φ2) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ = 4096 * D ^ 3 * SG ^ 2 * BC * (SE + Φ2) := by ring

section Bound

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The increment of a corrected plane of `ω^{e,1}` across the bond is the increment of the
corrector of `ω^{e,1}` plus the increment of the plane (planar:
`increment_eq_flipCorrector_true`). -/
theorem increment_eq_flipCorrector_trueD [NeZero d] {k : Fin d} {a : LatticeEdge d}
    {ω : Configuration d} (h1G : setBond (edgeBond a) true ω ∈ G)
    (hP₀ : PartitionEvent (setBond (edgeBond a) false ω))
    (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
    (hx : a.1 ∈ (uniqueInfiniteComponent h₁).supp)
    (hy : edgeHead a ∈ (uniqueInfiniteComponent h₁).supp) {ℓ₁ : uniqueInfiniteComponent h₁ → ℝ}
    (hℓ₁ : IsCorrectedPlane (uniqueInfiniteComponent h₁) (Pi.single k 1) ℓ₁) :
    extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a) =
      flipCorrector hG hGv k true (edgeBond a) ω a.1 -
        flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
        ((a.1 k : ℝ) - ((edgeHead a) k : ℝ)) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hA0 : setBond (edgeBond a) false ω ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact infinite_partitionAnchor hd0 hP₀ 0
  have hA1 := infiniteComponentEvent_setBond_true hA0 true
  have hxi := (mem_uniqueInfiniteComponent_iff h₁ a.1).1 hx
  have hyi := (mem_uniqueInfiniteComponent_iff h₁ (edgeHead a)).1 hy
  unfold flipCorrector
  rw [correctorDiff_sub_eq hG hGv h1G hxi hyi hA1,
    correctorDiff_eq hG hGv h1G (uniqueInfiniteComponent_infinite h₁) hℓ₁ ⟨a.1, hx⟩
      ⟨edgeHead a, hy⟩, extendComp_of_mem _ _ hx, extendComp_of_mem _ _ hy]
  have hs : ∀ z : Vertex d, ∑ j, (Pi.single k (1 : ℝ) : Fin d → ℝ) j * (z j : ℝ) = (z k : ℝ) := by
    intro z
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp
  rw [hs, hs]
  ring

/-- **The flip difference for a bond closed in `ω`** (planar: `ae_fluxFlip_sq_le_closed`):
almost surely, `(D_e X)² ≤ 4096 d³ (Σ_B G)² |B| (Σ_B E_v + Φ_{r²}(x, x₀)²)` with `B` the box of
radius `1 + 5 max(s(x₀), s(y₀))` around `x₀` and `v` the potential of the Green projection of the
heat field of the edges on the infinite cluster. -/
theorem ae_fluxFlipD_sq_le_closed [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (k i : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (a : LatticeEdge d), ¬ EdgeOpen ω a → PartitionEvent ω →
      bondFlipDiff (fluxObsD hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
        4096 * (d : ℝ) ^ 3 *
          (∑ z ∈ LatticeProb.boxFinset a.1 (1 + 5 * max (partSide ω a.1) (partSide ω (edgeHead a))),
            planeGrad hG hGv k ω z) ^ 2 *
          (LatticeProb.boxFinset a.1
            (1 + 5 * max (partSide ω a.1) (partSide ω (edgeHead a)))).card *
          (∑ u ∈ LatticeProb.boxFinset a.1 (1 + 5 * max (partSide ω a.1) (partSide ω (edgeHead a))),
              Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u +
            zdHeat d (r ^ 2) x a.1 ^ 2) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  filter_upwards [ae_setBond hp0 hp1 hGae, fluxPairingClosedD_holds hd hpc hp1,
    fluxPairingZeroD_holds hd hpc hp1, ae_dipoleCoeff_eq hG hGv hd hpc hp1 hGae] with
    ω hG' hwalk hzero hdip k i r hr x a hclosed hP
  have hωe : ω (edgeBond a) = false := by
    rw [edgeOpen_iff] at hclosed
    simpa using hclosed
  have heq : setBond (edgeBond a) false ω = ω := by
    have := setBond_self (edgeBond a) ω
    rwa [hωe] at this
  set B := LatticeProb.boxFinset a.1 (1 + 5 * max (partSide ω a.1) (partSide ω (edgeHead a)))
    with hB
  set SE := ∑ u ∈ B, Rigidity.Corrector.GeneralDim.openEnergy ω
    (clusterPot ω (heatEdgeD ω r x i)) u with hSE
  have hE0 : 0 ≤ SE := Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u
  set SG := ∑ z ∈ B, planeGrad hG hGv k ω z with hSG
  have hSG0 : 0 ≤ SG := Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv k ω z
  have hP₀ : PartitionEvent (setBond (edgeBond a) false ω) := by rw [heq]; exact hP
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single k 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single k 1)
  rw [bondFlipDiff_fluxObsD_eq hG hGv (hG' _ true) (hG' _ false) h₁ h₀ hℓ₁ hℓ₀]
  have hxB : a.1 ∈ B :=
    Rigidity.Poincare.GeneralDim.self_mem_supBox a.1 _
  have hBc1 : (1 : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_pos.2 ⟨a.1, hxB⟩
  have hRHS0 : 0 ≤ 4096 * (d : ℝ) ^ 3 * SG ^ 2 * (B.card : ℝ) *
      (SE + zdHeat d (r ^ 2) x a.1 ^ 2) := by
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
      (greenProj (setBond (edgeBond a) false ω) (heatEdgeD (setBond (edgeBond a) false ω) r x i))
        pw₀ = clusterPot ω (heatEdgeD ω r x i) (edgeHead a) -
          clusterPot ω (heatEdgeD ω r x i) a.1 := by
    have key : ∀ (ω' : Configuration d) (_ : ω' = ω)
        (pw' : (openGraph ω').Walk a.1 (edgeHead a)), ω' ∈ infiniteComponentEvent a.1 →
        walkSum ω' (greenProj ω' (heatEdgeD ω' r x i)) pw' =
          clusterPot ω (heatEdgeD ω r x i) (edgeHead a) -
            clusterPot ω (heatEdgeD ω r x i) a.1 := by
      intro ω' h pw' hinf'
      subst h
      exact walkSum_greenProj_eq_clusterPot _ pw' hinf'
    exact key _ heq pw₀ hinf₀
  rw [hpot] at hT
  -- the coefficient `c' = ℓ₁(x₀) - ℓ₁(y₀)`
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  rw [increment_eq_flipCorrector_trueD hG hGv (hG' _ true) hP₀ h₁ ((hC _).2 hx) ((hC _).2 hy) hℓ₁]
    at hT
  obtain ⟨R, hR0, -, hc⟩ := hdip k a hP₀ hinf₀ ⟨pw₀⟩
  have hoinf : ω ∈ infiniteComponentEvent (guardAnchor ω 0) := by
    rw [guardAnchor_of_event hP]
    exact infinite_partitionAnchor hd0 hP 0
  have hGω : ω ∈ G := by have := hG' (edgeBond a) false; rwa [heq] at this
  obtain ⟨w, hw⟩ : ∃ w : Vertex d → ℝ, w = fun z => if ω ∈ infiniteComponentEvent z then
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
  have hwl : ∀ u w', (openGraph ω).Adj u w' → |w u - w w'| ≤ planeGrad hG hGv k ω u :=
    fun u w' h => by rw [hw]; exact abs_sub_rootedPlane_le hG hGv hGω hoinf h
  have hwev := abs_sub_le_two_mul_edgeVariation hP (lattice_adj_edgeHead a) hinf hyinf w
  have hgx := edgeVariationIn_le_mul_sum (anchorBox ω a.1) (planeGrad_nonneg hG hGv k ω) hwl
  have hgy := edgeVariationIn_le_mul_sum (anchorBox ω (edgeHead a))
    (planeGrad_nonneg hG hGv k ω) hwl
  -- the regions lie in `B`
  have hRx : anchorBox ω a.1 ⊆ B := by
    refine (anchorBox_subset_boxFinset hP (L := 0) fun i => by simp).trans
      (Rigidity.Corrector.GeneralDim.boxFinset_mono ?_)
    omega
  have hRy : anchorBox ω (edgeHead a) ⊆ B := by
    refine (anchorBox_subset_boxFinset hP (L := 1) fun i => ?_).trans
      (Rigidity.Corrector.GeneralDim.boxFinset_mono ?_)
    · rw [abs_sub_comm]
      exact_mod_cast abs_sub_edgeHead_le a i
    · omega
  have hGs : ∀ S ⊆ B, ∑ z ∈ S, planeGrad hG hGv k ω z ≤ SG :=
    fun S hS => Finset.sum_le_sum_of_subset_of_nonneg hS fun z _ _ => planeGrad_nonneg hG hGv k ω z
  have hEs : ∀ S ⊆ B, ∑ u ∈ S, Rigidity.Corrector.GeneralDim.openEnergy ω
      (clusterPot ω (heatEdgeD ω r x i)) u ≤ SE :=
    fun S hS => Finset.sum_le_sum_of_subset_of_nonneg hS fun u _ _ => openEnergy_nonneg _ _ u
  have hcard : ∀ S ⊆ B, (S.card : ℝ) ≤ B.card := fun S hS => by
    exact_mod_cast Finset.card_le_card hS
  -- `|c'| ≤ 8d Σ_B G`
  have hcb : |w a.1 - w (edgeHead a)| ≤ 8 * d * SG := by
    have h1 := mul_le_mul_of_nonneg_left (hGs _ hRx) (by positivity : (0 : ℝ) ≤ 2 * d)
    have h2 := mul_le_mul_of_nonneg_left (hGs _ hRy) (by positivity : (0 : ℝ) ≤ 2 * d)
    have e : 8 * (d : ℝ) * SG = 2 * (2 * d * SG + 2 * d * SG) := by ring
    rw [e]
    linarith
  -- `(v(y₀) - v(x₀))² ≤ 32d |B| Σ_B E_v`
  have hvb : (clusterPot ω (heatEdgeD ω r x i) (edgeHead a) -
      clusterPot ω (heatEdgeD ω r x i) a.1) ^ 2 ≤ 32 * d * B.card * SE := by
    have hev := abs_sub_le_two_mul_edgeVariation hP (lattice_adj_edgeHead a) hinf hyinf
      (clusterPot ω (heatEdgeD ω r x i))
    have hB' : ∀ S ⊆ B, edgeVariationIn ω S (clusterPot ω (heatEdgeD ω r x i)) ^ 2 ≤
        2 * d * B.card * SE := by
      intro S hS
      have h1 := sq_edgeVariationIn_le ω S (clusterPot ω (heatEdgeD ω r x i))
      have h2 := mul_le_mul (hcard _ hS) (hEs _ hS)
        (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u) (Nat.cast_nonneg _)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * d)
      calc _ ≤ 2 * d * S.card * ∑ u ∈ S, Rigidity.Corrector.GeneralDim.openEnergy ω
            (clusterPot ω (heatEdgeD ω r x i)) u := h1
        _ = 2 * d * (S.card * ∑ u ∈ S, Rigidity.Corrector.GeneralDim.openEnergy ω
            (clusterPot ω (heatEdgeD ω r x i)) u) := by ring
        _ ≤ 2 * d * (B.card * SE) := h3
        _ = 2 * d * B.card * SE := by ring
    rw [abs_sub_comm] at hev
    have := sq_le_of_abs_le_two_mul_add hev (hB' _ hRx) (hB' _ hRy)
    linarith
  -- `|c'|` through the coefficient of the dipole
  have hcc : |flipCorrector hG hGv k true (edgeBond a) ω a.1 -
      flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
      ((a.1 k : ℝ) - ((edgeHead a) k : ℝ))| ≤ |w a.1 - w (edgeHead a)| := by
    rw [← hc', hc, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + R)]
    have := abs_nonneg (flipCorrector hG hGv k true (edgeBond a) ω a.1 -
      flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
      ((a.1 k : ℝ) - ((edgeHead a) k : ℝ)))
    nlinarith
  have hΔ : (if a.2 = i then zdHeat d (r ^ 2) x a.1 else 0) ^ 2 ≤ zdHeat d (r ^ 2) x a.1 ^ 2 := by
    split_ifs
    · exact le_rfl
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  have hc2 : (flipCorrector hG hGv k true (edgeBond a) ω a.1 -
      flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
      ((a.1 k : ℝ) - ((edgeHead a) k : ℝ))) ^ 2 ≤ (8 * d * SG) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hcc.trans hcb) 2
  rw [hT]
  exact closed_flux_arithD hd1 hc2 hvb hΔ hBc1

end Bound

end Rigidity.Green.GeneralFlux

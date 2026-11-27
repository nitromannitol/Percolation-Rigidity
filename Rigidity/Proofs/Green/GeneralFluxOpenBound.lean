import Rigidity.Proofs.Green.GeneralFluxPairing
import Rigidity.Proofs.Green.GeneralFluxP2Input
import Rigidity.Proofs.Corrector.GeneralStepTwoOpenBound

/-!
# The flip difference of the heat average of the flux on `ℤ^d` for the bonds open in the configuration

The extension of `DarioGuFluxOpenBound.lean` from `ℤ²` to `ℤ^d`, proving `FluxOpenBoundD d p`
(`GeneralFluxP2Input.lean`). For a bond `e` of `a = (x₀, i')` open in `ω`, `ω^{e,1} = ω` and, in
Case 3,

`D_e X = c ((P_ω h_ω)(a) - 1{i' = i} Φ_{r²}(x, x₀))` (`fluxPairingOpenD_holds`)

with `c = ℓ₀(x₀) - ℓ₀(y₀) = (1 + R) (ℓ_ω(x₀) - ℓ_ω(y₀))` (`increment_eq_flipCorrectorD` and
`ae_dipoleCoeff_eq`, Dario's (3.24)), as in the proof of Lemma 3.3 of Dario on `ℤ^d` for the bonds
open in `ω` (`ae_flipTermTwo_sq_le_open`), with the heat field `h_ω` of the edges in place of the
field of the coarsened gradient and the term `-1{i' = i} Φ_{r²}(x, x₀)` (Gu's `A_e`) in place of the
change of partition. With

* `|ℓ_ω(x₀) - ℓ_ω(y₀)| ≤ G(x₀)`, since the bond is open in `ω`;
* `(P_ω h_ω)(a)² ≤ E_v(x₀)` for the potential `v` of `P_ω h_ω` on the cluster;
* Lemma 3.5 in its corrected form (`resamplePartition_max_bound`): with
  `S = max(s_ω(x₀), s_{ω^{e,0}}(x₀))`, the partition cubes of `ω^{e,0}` at `x₀` and `y₀` have side
  at most `243 S`, so their boxes `anchorBox` have at most `7^d 243^d S^d` points and
  `R ≤ (8d 7^d 243^d S^d)²`;

one gets `(D_e X)² ≤ 2 (1 + (8d 7^d 243^d S^d)²)² G(x₀)² (E_v(x₀) + Φ_{r²}(x, x₀)²)`
(`ae_fluxFlip_sq_le_openD`, `fluxOpenBoundD_holds`). The planar statement assumes Lemma 3.5 in its
printed form, with the side `s_ω(x₀)` alone in place of `S`; that form holds for the partition of
the meshed squares of `ℤ²` (`Rigidity.Corrector.darioResamplePartitionTwo_holds`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.Proofs.Cluster Rigidity.External Rigidity.Corrector.GeneralDim
open Rigidity.Corrector (correctorDiff correctorDiff_eq)
open Rigidity.Poincare.GeneralDim (zdHeat zdHeat_nonneg)
open scoped Classical ENNReal InnerProductSpace

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

section Bound

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The increment of a corrected plane of `ω^{e,0}` across the bond is the coefficient of
`ae_dipoleCoeff_eq` (planar: `Rigidity.Green.increment_eq_flipCorrector`). -/
theorem increment_eq_flipCorrectorD [NeZero d] {k : Fin d} {a : LatticeEdge d}
    {ω : Configuration d} (h0G : setBond (edgeBond a) false ω ∈ G)
    (hP₀ : PartitionEvent (setBond (edgeBond a) false ω))
    (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
    (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
    (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) {ℓ₀ : uniqueInfiniteComponent h₀ → ℝ}
    (hℓ₀ : IsCorrectedPlane (uniqueInfiniteComponent h₀) (Pi.single k 1) ℓ₀) :
    ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩ =
      flipCorrector hG hGv k false (edgeBond a) ω a.1 -
        flipCorrector hG hGv k false (edgeBond a) ω (edgeHead a) +
        ((a.1 k : ℝ) - ((edgeHead a) k : ℝ)) := by
  have hA0 : setBond (edgeBond a) false ω ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact infinite_partitionAnchor (Nat.pos_of_ne_zero (NeZero.ne d)) hP₀ 0
  have hxi := (mem_uniqueInfiniteComponent_iff h₀ a.1).1 hx
  have hyi := (mem_uniqueInfiniteComponent_iff h₀ (edgeHead a)).1 hy
  unfold flipCorrector
  rw [correctorDiff_sub_eq hG hGv h0G hxi hyi hA0,
    correctorDiff_eq hG hGv h0G (uniqueInfiniteComponent_infinite h₀) hℓ₀ ⟨a.1, hx⟩
      ⟨edgeHead a, hy⟩, sum_single_mulD, sum_single_mulD]
  ring

/-- **The flip difference for a bond open in `ω`** (planar:
`Rigidity.Green.ae_fluxFlip_sq_le_open`, with the scale `S = max(s_ω(x₀), s_{ω^{e,0}}(x₀))` of the
corrected Lemma 3.5 in place of `s_ω(x₀)`). -/
theorem ae_fluxFlip_sq_le_openD [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (k i : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (a : LatticeEdge d), EdgeOpen ω a → PartitionEvent ω →
      bondFlipDiff (fluxObsD hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
        2 * (1 + (8 * d * 7 ^ d * 243 ^ d *
            (((max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1) : ℕ) : ℝ)) ^ d) ^
              2) ^ 2 *
          planeGrad hG hGv k ω a.1 ^ 2 *
          (Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) a.1 +
            zdHeat d (r ^ 2) x a.1 ^ 2) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have hd0 : 0 < d := by omega
  have hOpen := fluxPairingOpenD_holds (p := p) hd hpc hp1
  have hZero := fluxPairingZeroD_holds (p := p) hd hpc hp1
  unfold FluxPairingOpenD at hOpen
  unfold FluxPairingZeroD at hZero
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_setBond hp0 hp1 (ae_partitionEvent hd hpc),
    hOpen, hZero, ae_dipoleCoeff_eq hG hGv hd hpc hp1 hGae] with
    ω hG' hPs hopen hzero hdip k i r hr x a haopen hP
  have hωe : ω (edgeBond a) = true := (edgeOpen_iff ω a).1 haopen
  have heq : setBond (edgeBond a) true ω = ω := by
    have := setBond_self (edgeBond a) ω
    rwa [hωe] at this
  have hP₀ := hPs (edgeBond a) false
  have hP₁ : PartitionEvent (setBond (edgeBond a) true ω) := by rw [heq]; exact hP
  set S := max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1) with hS
  set E := Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) a.1
    with hE
  have hE0 : 0 ≤ E := openEnergy_nonneg _ _ _
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single k 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single k 1)
  rw [bondFlipDiff_fluxObsD_eq hG hGv (hG' _ true) (hG' _ false) h₁ h₀ hℓ₁ hℓ₀]
  by_cases hcase : a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
      edgeHead a ∈ (uniqueInfiniteComponent h₀).supp
  swap
  · rw [hzero a h₁ h₀ hcase _ ℓ₁ ℓ₀ hℓ₁ hℓ₀ r x i]
    have : 0 ≤ 2 * (1 + (8 * d * 7 ^ d * 243 ^ d * (S : ℝ) ^ d) ^ 2) ^ 2 *
        planeGrad hG hGv k ω a.1 ^ 2 * (E + zdHeat d (r ^ 2) x a.1 ^ 2) := by positivity
    simpa using this
  obtain ⟨hx, hy⟩ := hcase
  have hinf₀ : setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 :=
    (mem_uniqueInfiniteComponent_iff h₀ a.1).1 hx
  have hreach₀ : (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy).symm)
  have hinf : ω ∈ infiniteComponentEvent a.1 := by
    rw [← heq]; exact infiniteComponentEvent_setBond_true hinf₀ true
  have hyinf : ω ∈ infiniteComponentEvent (edgeHead a) := mem_infiniteComponentEvent_of_adj
    (by unfold EdgeOpen at haopen; exact haopen) hinf
  have hT := hopen a h₁ h₀ hx hy _ ℓ₁ ℓ₀ hℓ₁ hℓ₀ r hr x i
  -- `(P_ω h_ω)(a)` through the potential on the cluster of `ω`
  have hpair : greenProj (setBond (edgeBond a) true ω)
      (heatEdgeD (setBond (edgeBond a) true ω) r x i) a =
      clusterPot ω (heatEdgeD ω r x i) (edgeHead a) - clusterPot ω (heatEdgeD ω r x i) a.1 := by
    have key : ∀ (ω' : Configuration d) (_ : ω' = ω), EdgeOpen ω' a →
        ω' ∈ infiniteComponentEvent a.1 →
        greenProj ω' (heatEdgeD ω' r x i) a =
          clusterPot ω (heatEdgeD ω r x i) (edgeHead a) -
            clusterPot ω (heatEdgeD ω r x i) a.1 := by
      intro ω' h ha' hinf'
      subst h
      have e := edgeGrad_clusterPot (heatEdgeD ω' r x i) ha'
      rw [if_pos hinf'] at e
      unfold edgeGrad at e
      rw [if_pos ha'] at e
      exact e.symm
    exact key _ heq (by rw [heq]; exact haopen) (by rw [heq]; exact hinf)
  rw [hpair] at hT
  -- the dipole coefficient
  obtain ⟨R, hR0, hRle, hc⟩ := hdip k a hP₀ hinf₀ hreach₀
  rw [increment_eq_flipCorrectorD hG hGv (hG' _ false) hP₀ h₀ hx hy hℓ₀, hc] at hT
  have hA0 : setBond (edgeBond a) false ω ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact infinite_partitionAnchor hd0 hP₀ 0
  have hoinf : ω ∈ infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    have := infiniteComponentEvent_setBond_true hA0 true
    rwa [heq] at this
  have hGω : ω ∈ G := by have := hG' (edgeBond a) true; rwa [heq] at this
  have hcG : |flipCorrector hG hGv k true (edgeBond a) ω a.1 -
      flipCorrector hG hGv k true (edgeBond a) ω (edgeHead a) +
      ((a.1 k : ℝ) - ((edgeHead a) k : ℝ))| ≤ planeGrad hG hGv k ω a.1 := by
    unfold flipCorrector
    rw [heq, correctorDiff_sub_eq hG hGv hGω hinf hyinf hoinf]
    have h1 := abs_correctorDiff_add_one_le hG hGv (i := k)
      (show (openGraph ω).Adj a.1 (edgeHead a) from haopen)
    have h2 := abs_sub_le_one_of_adj (show (openGraph ω).Adj a.1 (edgeHead a) from haopen) k
    calc _ ≤ |correctorDiff hG hGv (Pi.single k 1) ω a.1 (edgeHead a)| +
          |(a.1 k : ℝ) - ((edgeHead a) k : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
  -- Lemma 3.5 in its corrected form, at the scale `S`
  have hS1 : 1 ≤ S := by
    have : 1 ≤ partSide ω a.1 := by
      rw [partSide_eq hP]
      exact Nat.one_le_pow _ _ (by norm_num)
    exact this.trans (le_max_left _ _)
  have hmax : max (3 ^ (partitionCube (setBond (edgeBond a) true ω) a.1).scale)
      (3 ^ (partitionCube (setBond (edgeBond a) false ω) a.1).scale) = S := by
    rw [hS, partSide_eq hP, partSide_eq hP₀, heq]
  have hloc := resamplePartition_max_bound (setBond_agree_off (edgeBond a) true false ω) hP₁ hP₀
    (mem_edgeBond_fst a)
  rw [hmax] at hloc
  have hnear : ∀ z : Vertex d, (∀ j, |z j - a.1 j| ≤ 1) →
      3 ^ (partitionCube (setBond (edgeBond a) false ω) z).scale ≤ 243 * S := by
    intro z hz
    refine (hloc z).1 fun j => ?_
    have h81 : (1 : ℤ) < ((81 : ℕ) : ℤ) * ((S : ℕ) : ℤ) := by
      have : (1 : ℤ) ≤ ((S : ℕ) : ℤ) := by exact_mod_cast hS1
      push_cast
      linarith
    linarith [hz j]
  have hsx := hnear a.1 fun j => by simp
  have hsy := hnear (edgeHead a) fun j => by
    rw [abs_sub_comm]
    exact abs_sub_edgeHead_le a j
  have hcard : ∀ z, 3 ^ (partitionCube (setBond (edgeBond a) false ω) z).scale ≤ 243 * S →
      ((anchorBox (setBond (edgeBond a) false ω) z).card : ℝ) ≤
        7 ^ d * 243 ^ d * (S : ℝ) ^ d := by
    intro z hz
    have := card_anchorBox_le hz
    push_cast at this
    rw [mul_pow, ← mul_assoc] at this
    exact this
  have hR : R ≤ (8 * d * 7 ^ d * 243 ^ d * (S : ℝ) ^ d) ^ 2 := by
    have hd0' : (0 : ℝ) ≤ 4 * d := by positivity
    refine hRle.trans (pow_le_pow_left₀
      (mul_nonneg hd0' (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_ 2)
    have h1 := hcard _ hsx
    have h2 := hcard _ hsy
    calc 4 * (d : ℝ) * (((anchorBox (setBond (edgeBond a) false ω) a.1).card : ℝ) +
          (anchorBox (setBond (edgeBond a) false ω) (edgeHead a)).card)
        ≤ 4 * d * (7 ^ d * 243 ^ d * (S : ℝ) ^ d + 7 ^ d * 243 ^ d * (S : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hd0'
      _ = 8 * d * 7 ^ d * 243 ^ d * (S : ℝ) ^ d := by ring
  -- `(P_ω h_ω)(a)² ≤ E_v(x₀)` and the heat term
  have hΔv : (clusterPot ω (heatEdgeD ω r x i) (edgeHead a) -
      clusterPot ω (heatEdgeD ω r x i) a.1) ^ 2 ≤ E := by
    rw [hE, ← neg_sub, neg_sq]
    exact sq_sub_le_openEnergy _ (show (openGraph ω).Adj a.1 (edgeHead a) from haopen)
  have hΔc : (-(if a.2 = i then zdHeat d (r ^ 2) x a.1 else 0)) ^ 2 ≤
      zdHeat d (r ^ 2) x a.1 ^ 2 := by
    split_ifs
    · rw [neg_sq]
    · simp only [neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  -- assembly
  rw [hT, sub_eq_add_neg]
  exact sq_mul_add_le hR0 hR hcG hΔv hΔc

end Bound

/-- **Part 2a**: `FluxOpenBoundD d p` for every `d ≥ 2` and every supercritical `p < 1`. -/
theorem fluxOpenBoundD_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) : FluxOpenBoundD d p :=
  fun _ hG hGv hGae => ae_fluxFlip_sq_le_openD hG hGv hd hpc hp1 hGae

end Rigidity.Green.GeneralFlux

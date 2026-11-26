import Rigidity.Proofs.Green.DarioGuFluxObservable
import Rigidity.Proofs.Corrector.DarioStepTwoOpenBound
import Rigidity.Proofs.Corrector.DarioStepTwoElectric

/-!
# The flip difference of the heat average of the flux for the bonds open in the configuration

For a bond `e` of `a = (x₀, i')` open in `ω`, `ω^{e,1} = ω` and, in Case 3,

`D_e X = c ((P_ω h_ω)(a) - 1{i' = i} Φ_{r²}(x, x₀))` (`ae_heat_planeFlux_sub_open`)

with `c = ℓ₀(x₀) - ℓ₀(y₀) = (1 + R) (ℓ_ω(x₀) - ℓ_ω(y₀))` (`ae_dipoleCoeff_eq`, Dario's (3.24)), as
in the proof of Lemma 3.3 of Dario for the bonds open in `ω` (`DarioStepTwoOpenBound`), with the
heat field `h_ω` of the edges in place of the field of the coarsened gradient, and the term
`-1{i' = i} Φ_{r²}(x, x₀)` (Gu's `A_e`) in place of the change of partition. With
`|ℓ_ω(x₀) - ℓ_ω(y₀)| ≤ G(x₀)`, `R ≤ (1296 C² s²)²` from Lemma 3.5 in the form
`ResamplePartitionBound C₀ C`, and `(P_ω h_ω)(a)² ≤ E_v(x₀)` for the potential `v` of `P_ω h_ω`:

`(D_e X)² ≤ 2 (1 + (1296 C² s²)²)² G(x₀)² (E_v(x₀) + Φ_{r²}(x, x₀)²)`
(`ae_fluxFlip_sq_le_open`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Corrector
  Rigidity.External Rigidity.Poincare
open scoped Classical ENNReal

section Bound

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The increment of a corrected plane of `ω^{e,0}` across the bond is the coefficient of
`ae_dipoleCoeff_eq`. -/
theorem increment_eq_flipCorrector {k : Fin 2} {a : LatticeEdge} {ω : Configuration 2}
    (h0G : setBond (edgeBond a) false ω ∈ G) (hP₀ : PlanarPartitionEvent (setBond (edgeBond a) false ω))
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
    exact infinite_planarCoarseAnchor hP₀ 0
  have hxi := (mem_uniqueInfiniteComponent_iff h₀ a.1).1 hx
  have hyi := (mem_uniqueInfiniteComponent_iff h₀ (edgeHead a)).1 hy
  unfold flipCorrector
  rw [correctorDiff_sub_eq hG hGv h0G hxi hyi hA0,
    correctorDiff_eq hG hGv h0G (uniqueInfiniteComponent_infinite h₀) hℓ₀ ⟨a.1, hx⟩
      ⟨edgeHead a, hy⟩]
  have hs : ∀ z : Vertex 2, ∑ j, (Pi.single k (1 : ℝ) : Fin 2 → ℝ) j * (z j : ℝ) = (z k : ℝ) := by
    intro z
    fin_cases k <;> simp [Fin.sum_univ_two]
  rw [hs, hs]
  ring

/-- **The flip difference for a bond open in `ω`.** -/
theorem ae_fluxFlip_sq_le_open {C₀ C : ℕ} (hC₀ : 2 ≤ C₀) (hres : ResamplePartitionBound C₀ C)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (k i : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (a : LatticeEdge), EdgeOpen ω a → ∀ hP : PlanarPartitionEvent ω,
      bondFlipDiff (fluxObs hG hGv k i r x) (edgeBond a) ω ^ 2 ≤
        2 * (1 + (1296 * (C : ℝ) ^ 2 * (planarSide ω a.1 : ℝ) ^ 2) ^ 2) ^ 2 *
          planeGrad hG hGv k ω a.1 ^ 2 *
          (openEnergy ω (clusterPot ω (heatEdge ω r x i)) a.1 + latticeHeat (r ^ 2) x a.1 ^ 2) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_setBond hp0 hp1 (ae_planarPartitionEvent hpc),
    ae_heat_planeFlux_sub_open hpc hp1, ae_heat_planeFlux_sub_eq_zero hpc hp1,
    ae_dipoleCoeff_eq hG hGv hpc hp1 hGae] with
    ω hG' hPs hopen hzero hdip k i r hr x a haopen hP
  have hωe : ω (edgeBond a) = true := (edgeOpen_iff ω a).1 haopen
  have heq : setBond (edgeBond a) true ω = ω := by
    have := setBond_self (edgeBond a) ω
    rwa [hωe] at this
  have hP₀ := hPs (edgeBond a) false
  have hP₁ : PlanarPartitionEvent (setBond (edgeBond a) true ω) := by rw [heq]; exact hP
  set s := planarSide ω a.1 with hs
  have hs1 : 1 ≤ s := by
    rw [hs, planarSide_eq hP]
    exact Nat.one_le_pow _ _ (by norm_num)
  set E := openEnergy ω (clusterPot ω (heatEdge ω r x i)) a.1 with hE
  have hE0 : 0 ≤ E := openEnergy_nonneg _ _ _
  have hG0 := planeGrad_nonneg hG hGv k ω a.1
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single k 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single k 1)
  rw [bondFlipDiff_fluxObs_eq hG hGv (hG' _ true) (hG' _ false) h₁ h₀ hℓ₁ hℓ₀]
  by_cases hcase : a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
      edgeHead a ∈ (uniqueInfiniteComponent h₀).supp
  swap
  · rw [hzero a h₁ h₀ hcase _ ℓ₁ ℓ₀ hℓ₁ hℓ₀ r x i]
    have : 0 ≤ 2 * (1 + (1296 * (C : ℝ) ^ 2 * (s : ℝ) ^ 2) ^ 2) ^ 2 *
        planeGrad hG hGv k ω a.1 ^ 2 * (E + latticeHeat (r ^ 2) x a.1 ^ 2) := by positivity
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
  have hpair : greenProj (setBond (edgeBond a) true ω) (heatEdge (setBond (edgeBond a) true ω) r x i)
      a = clusterPot ω (heatEdge ω r x i) (edgeHead a) - clusterPot ω (heatEdge ω r x i) a.1 := by
    have key : ∀ (ω' : Configuration 2) (_ : ω' = ω), EdgeOpen ω' a →
        ω' ∈ infiniteComponentEvent a.1 →
        greenProj ω' (heatEdge ω' r x i) a =
          clusterPot ω (heatEdge ω r x i) (edgeHead a) - clusterPot ω (heatEdge ω r x i) a.1 := by
      intro ω' h ha' hinf'
      subst h
      have e := edgeGrad_clusterPot (heatEdge ω' r x i) ha'
      rw [if_pos hinf'] at e
      unfold edgeGrad at e
      rw [if_pos ha'] at e
      exact e.symm
    exact key _ heq (by rw [heq]; exact haopen) (by rw [heq]; exact hinf)
  rw [hpair] at hT
  -- the dipole coefficient
  obtain ⟨R, hR0, hRle, hc⟩ := hdip k a hP₀ hinf₀ hreach₀
  rw [increment_eq_flipCorrector hG hGv (hG' _ false) hP₀ h₀ hx hy hℓ₀, hc] at hT
  have hA0 : setBond (edgeBond a) false ω ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact infinite_planarCoarseAnchor hP₀ 0
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
  -- Lemma 3.5
  have hloc := resampleLocal_of_bound hres (setBond_agree_off (edgeBond a) true false ω) hP₁ hP₀
    (mem_edgeBond_fst a)
  have hside : 3 ^ (planarPartCube (setBond (edgeBond a) true ω) a.1).scale = s := by
    rw [heq, hs, planarSide_eq hP]
  rw [hside] at hloc
  have hρ : ∀ z : Vertex 2, (∀ i, |z i - a.1 i| ≤ 1) → ∀ i, |z i - a.1 i| < ((C₀ * s : ℕ) : ℤ) := by
    intro z hz i
    have : (2 : ℤ) ≤ ((C₀ * s : ℕ) : ℤ) := by
      have : 2 ≤ C₀ * s := le_trans hC₀ (Nat.le_mul_of_pos_right C₀ hs1)
      exact_mod_cast this
    linarith [hz i]
  have hsx := ((hloc a.1).1 (hρ a.1 fun i => by simp)).2
  have hsy := ((hloc (edgeHead a)).1 (hρ (edgeHead a) fun i => by
    rw [abs_sub_comm]; exact abs_sub_edgeHead_le a i)).2
  have hcard : ∀ z, 3 ^ (planarPartCube (setBond (edgeBond a) false ω) z).scale ≤ C * s →
      ((cubeRegion (setBond (edgeBond a) false ω) z).card : ℝ) ≤
        81 * (C : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
    intro z hz
    have := card_cubeRegion_le hz
    push_cast at this
    linarith [show ((C : ℝ) * s) ^ 2 = (C : ℝ) ^ 2 * (s : ℝ) ^ 2 by ring]
  have hR : R ≤ (1296 * (C : ℝ) ^ 2 * (s : ℝ) ^ 2) ^ 2 := by
    refine hRle.trans (pow_le_pow_left₀ (by positivity) ?_ 2)
    have := hcard _ hsx
    have := hcard _ hsy
    linarith
  -- `(P_ω h_ω)(a)² ≤ E_v(x₀)` and the heat term
  have hΔv : (clusterPot ω (heatEdge ω r x i) (edgeHead a) -
      clusterPot ω (heatEdge ω r x i) a.1) ^ 2 ≤ E := by
    rw [hE, ← neg_sub, neg_sq]
    exact sq_sub_le_openEnergy _ (show (openGraph ω).Adj a.1 (edgeHead a) from haopen)
  have hΔc : (-(if a.2 = i then latticeHeat (r ^ 2) x a.1 else 0)) ^ 2 ≤
      latticeHeat (r ^ 2) x a.1 ^ 2 := by
    split_ifs
    · rw [neg_sq]
    · simp only [neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  -- assembly
  rw [hT, sub_eq_add_neg]
  exact sq_mul_add_le hR0 hR hcG hΔv hΔc

end Bound

end Rigidity.Green

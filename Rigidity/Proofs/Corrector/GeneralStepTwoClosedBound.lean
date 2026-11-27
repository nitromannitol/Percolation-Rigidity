import Rigidity.Proofs.Corrector.GeneralStepTwoOpenBound

/-!
# Step 2 of Lemma 3.3 of Dario on `ℤᵈ` for the bonds closed in the configuration

For a bond `e` of `a = (x, i')` closed in `ω`, `ω^{e,0} = ω` and, in Case 3,
`T₂(e) = c' (v(y) - v(x))` with `v` the potential of `P_ω γ_ω` on the infinite cluster
(`ae_flipTermTwo_eq_walkSum`) and `|c'| ≤ |ℓ_ω(x) - ℓ_ω(y)|` (`ae_dipoleCoeff_eq`). As in the planar
`ae_flipTermTwo_sq_le_closed`, both factors are bounded through the total variations over the boxes
`anchorBox` of the partition cubes at `x` and `y`, which lie in the box `B` of radius
`1 + 5 max(s(x), s(y))` around `x`: `|c'| ≤ 8d Σ_B G` and `(v(y) - v(x))² ≤ 32d |B| Σ_B E_v`, so
`T₂(e)² ≤ 2048 d³ (Σ_B G)² |B| Σ_B E_v` (`ae_flipTermTwo_sq_le_closed`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal InnerProductSpace

variable {d : ℕ}

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **Step 2 for a bond closed in `ω`**: almost surely, `T₂(e)² ≤ 2048 d³ (Σ_B G)² |B| Σ_B E_v` with
`B` the box of radius `1 + 5 max(s(x), s(y))` around `x` and `v` the potential of `P_ω γ_ω` on the
infinite cluster. -/
theorem ae_flipTermTwo_sq_le_closed [NeZero d] (hd : 2 ≤ d) {p : unitInterval} (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (a : LatticeEdge d), ¬ EdgeOpen ω a → ∀ hP : PartitionEvent ω,
      flipTermTwo hG hGv i j r x (edgeBond a) ω ^ 2 ≤
        2048 * (d : ℝ) ^ 3 * (∑ z ∈ LatticeProb.boxFinset a.1 (1 + 5 * max (partSide ω a.1) (partSide ω (edgeHead a))),
            planeGrad hG hGv i ω z) ^ 2 *
          (LatticeProb.boxFinset a.1 (1 + 5 * max (partSide ω a.1) (partSide ω (edgeHead a)))).card *
          ∑ u ∈ LatticeProb.boxFinset a.1 (1 + 5 * max (partSide ω a.1) (partSide ω (edgeHead a))),
            openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have hd0 : 0 < d := by omega
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_flipTermTwo_eq_walkSum hG hGv hd hpc hp1 hGae,
    ae_flipTermTwo_eq_zero hG hGv hd hpc hp1 hGae, ae_dipoleCoeff_eq hG hGv hd hpc hp1 hGae] with
    ω hG' hwalk hzero hdip i j r hr x a hclosed hP
  have hωe : ω (edgeBond a) = false := by
    rw [edgeOpen_iff] at hclosed
    simpa using hclosed
  have heq : setBond (edgeBond a) false ω = ω := by
    have := setBond_self (edgeBond a) ω
    rwa [hωe] at this
  set B := LatticeProb.boxFinset a.1 (1 + 5 * max (partSide ω a.1) (partSide ω (edgeHead a))) with hB
  have hE0 : 0 ≤ ∑ u ∈ B, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
    Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u
  have hRHS0 : 0 ≤ 2048 * (d : ℝ) ^ 3 * (∑ z ∈ B, planeGrad hG hGv i ω z) ^ 2 * (B.card : ℝ) *
      ∑ u ∈ B, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
    mul_nonneg (by positivity) hE0
  have hP₀ : PartitionEvent (setBond (edgeBond a) false ω) := by rw [heq]; exact hP
  by_cases hcase : setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 ∧
      (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a)
  swap
  · rw [hzero i j r x a hP₀ hcase]
    simpa using hRHS0
  obtain ⟨hinf₀, hreach₀⟩ := hcase
  obtain ⟨pw₀⟩ := hreach₀
  have hinf : ω ∈ infiniteComponentEvent a.1 := by rw [← heq]; exact hinf₀
  have hreach : (openGraph ω).Reachable a.1 (edgeHead a) := by rw [← heq]; exact ⟨pw₀⟩
  -- the identity of Case 3, through `ω` itself
  have hT := hwalk i j r hr x a hP₀ pw₀ hinf₀
  have hpot : walkSum (setBond (edgeBond a) false ω)
      (greenProj (setBond (edgeBond a) false ω) (coarseHeatField hP₀ r x j)) pw₀ =
      clusterPot ω (coarseHeatField hP r x j) (edgeHead a) -
        clusterPot ω (coarseHeatField hP r x j) a.1 := by
    have key : ∀ (ω' : Configuration d) (_ : ω' = ω) (hP' : PartitionEvent ω')
        (pw' : (openGraph ω').Walk a.1 (edgeHead a)), ω' ∈ infiniteComponentEvent a.1 →
        walkSum ω' (greenProj ω' (coarseHeatField hP' r x j)) pw' =
          clusterPot ω (coarseHeatField hP r x j) (edgeHead a) -
            clusterPot ω (coarseHeatField hP r x j) a.1 := by
      intro ω' h hP' pw' hinf'
      subst h
      exact walkSum_greenProj_eq_clusterPot _ pw' hinf'
    exact key _ heq hP₀ pw₀ hinf₀
  rw [hpot] at hT
  obtain ⟨R, hR0, -, hc⟩ := hdip i a hP₀ hinf₀ ⟨pw₀⟩
  -- the factor `c' = ℓ₀(x) - ℓ₀(y)` through the plane of `ω`
  have hoinf : ω ∈ infiniteComponentEvent (guardAnchor ω 0) := by
    rw [guardAnchor_of_event hP]
    exact infinite_partitionAnchor hd0 hP 0
  have hGω : ω ∈ G := by have := hG' (edgeBond a) false; rwa [heq] at this
  obtain ⟨w, hw⟩ : ∃ w : Vertex d → ℝ, w = fun z => if ω ∈ infiniteComponentEvent z then
      correctorDiff hG hGv (Pi.single i 1) ω z (guardAnchor ω 0) + (z i : ℝ) else 0 :=
    ⟨_, rfl⟩
  have hyinf : ω ∈ infiniteComponentEvent (edgeHead a) := by
    change ((openGraph ω).connectedComponentMk (edgeHead a)).supp.Infinite
    rw [← SimpleGraph.ConnectedComponent.sound hreach]
    exact hinf
  have hc' : flipCorrector hG hGv i false (edgeBond a) ω a.1 -
      flipCorrector hG hGv i false (edgeBond a) ω (edgeHead a) +
      ((a.1 i : ℝ) - ((edgeHead a) i : ℝ)) = w a.1 - w (edgeHead a) := by
    rw [hw]
    beta_reduce
    rw [if_pos hinf, if_pos hyinf]
    unfold flipCorrector
    rw [heq]
    ring
  have hwev := abs_sub_le_two_mul_edgeVariation hP (lattice_adj_edgeHead a) hinf hyinf w
  have hwl : ∀ u w', (openGraph ω).Adj u w' → |w u - w w'| ≤ planeGrad hG hGv i ω u :=
    fun u w' h => by rw [hw]; exact abs_sub_rootedPlane_le hG hGv hGω hoinf h
  have hgx := edgeVariationIn_le_mul_sum (anchorBox ω a.1) (planeGrad_nonneg hG hGv i ω) hwl
  have hgy := edgeVariationIn_le_mul_sum (anchorBox ω (edgeHead a))
    (planeGrad_nonneg hG hGv i ω) hwl
  -- the regions lie in `B`
  have hsx : partSide ω a.1 ≤ max (partSide ω a.1) (partSide ω (edgeHead a)) :=
    le_max_left _ _
  have hsy : partSide ω (edgeHead a) ≤ max (partSide ω a.1) (partSide ω (edgeHead a)) :=
    le_max_right _ _
  have hRx : anchorBox ω a.1 ⊆ B := by
    refine (anchorBox_subset_boxFinset hP (L := 0) fun i => by simp).trans (boxFinset_mono ?_)
    omega
  have hRy : anchorBox ω (edgeHead a) ⊆ B := by
    refine (anchorBox_subset_boxFinset hP (L := 1) fun i => ?_).trans (boxFinset_mono ?_)
    · rw [abs_sub_comm]
      exact_mod_cast abs_sub_edgeHead_le a i
    · omega
  have hGs : ∀ S ⊆ B, ∑ z ∈ S, planeGrad hG hGv i ω z ≤ ∑ z ∈ B, planeGrad hG hGv i ω z :=
    fun S hS => Finset.sum_le_sum_of_subset_of_nonneg hS fun z _ _ => planeGrad_nonneg hG hGv i ω z
  have hEs : ∀ S ⊆ B, ∑ u ∈ S, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u ≤
      ∑ u ∈ B, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
    fun S hS => Finset.sum_le_sum_of_subset_of_nonneg hS fun u _ _ => openEnergy_nonneg _ _ u
  have hcard : ∀ S ⊆ B, (S.card : ℝ) ≤ B.card := fun S hS => by
    exact_mod_cast Finset.card_le_card hS
  set SG := ∑ z ∈ B, planeGrad hG hGv i ω z with hSG
  set SE := ∑ u ∈ B, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u with hSE
  have hSG0 : 0 ≤ SG := Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv i ω z
  -- `|c'| ≤ 8d Σ_B G`
  have hcb : |w a.1 - w (edgeHead a)| ≤ 8 * d * SG := by
    have h1 := mul_le_mul_of_nonneg_left (hGs _ hRx) (by positivity : (0 : ℝ) ≤ 2 * d)
    have h2 := mul_le_mul_of_nonneg_left (hGs _ hRy) (by positivity : (0 : ℝ) ≤ 2 * d)
    have e : 8 * (d : ℝ) * SG = 2 * (2 * d * SG + 2 * d * SG) := by ring
    rw [e]
    linarith
  -- `(v(y) - v(x))² ≤ 32d |B| Σ_B E`
  have hvb : (clusterPot ω (coarseHeatField hP r x j) (edgeHead a) -
      clusterPot ω (coarseHeatField hP r x j) a.1) ^ 2 ≤ 32 * d * B.card * SE := by
    have hev := abs_sub_le_two_mul_edgeVariation hP (lattice_adj_edgeHead a) hinf hyinf
      (clusterPot ω (coarseHeatField hP r x j))
    have hB : ∀ S ⊆ B, edgeVariationIn ω S (clusterPot ω (coarseHeatField hP r x j)) ^ 2 ≤
        2 * d * B.card * SE := by
      intro S hS
      have h1 := sq_edgeVariationIn_le ω S (clusterPot ω (coarseHeatField hP r x j))
      have h2 := mul_le_mul (hcard _ hS) (hEs _ hS)
        (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u) (Nat.cast_nonneg _)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * d)
      calc _ ≤ 2 * d * S.card *
            ∑ u ∈ S, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u := h1
        _ = 2 * d * (S.card *
            ∑ u ∈ S, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) := by ring
        _ ≤ 2 * d * (B.card * SE) := h3
        _ = 2 * d * B.card * SE := by ring
    rw [abs_sub_comm] at hev
    have := sq_le_of_abs_le_two_mul_add hev (hB _ hRx) (hB _ hRy)
    linarith
  -- assembly
  have hcc : |flipCorrector hG hGv i true (edgeBond a) ω a.1 -
      flipCorrector hG hGv i true (edgeBond a) ω (edgeHead a) +
      ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))| ≤ |w a.1 - w (edgeHead a)| := by
    rw [← hc', hc, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + R)]
    have := abs_nonneg (flipCorrector hG hGv i true (edgeBond a) ω a.1 -
      flipCorrector hG hGv i true (edgeBond a) ω (edgeHead a) +
      ((a.1 i : ℝ) - ((edgeHead a) i : ℝ)))
    nlinarith
  rw [hT, mul_pow]
  have hc2 : (flipCorrector hG hGv i true (edgeBond a) ω a.1 -
      flipCorrector hG hGv i true (edgeBond a) ω (edgeHead a) +
      ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))) ^ 2 ≤ (8 * d * SG) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hcc.trans hcb) 2
  calc _ ≤ (8 * d * SG) ^ 2 * (32 * d * B.card * SE) :=
        mul_le_mul hc2 hvb (sq_nonneg _) (by positivity)
    _ = 2048 * (d : ℝ) ^ 3 * SG ^ 2 * B.card * SE := by ring

end Grad

end Rigidity.Corrector.GeneralDim

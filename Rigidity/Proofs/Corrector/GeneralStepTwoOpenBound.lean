import Rigidity.Proofs.Corrector.GeneralStepTwoOpen
import Rigidity.Proofs.Corrector.GeneralStepTwoDefs

/-!
# Step 2 of Lemma 3.3 of Dario on `ℤᵈ` for the bonds open in the configuration

For a bond `e` of `a = (x, i')` open in `ω`, `ω^{e,1} = ω` and, in Case 3,
`T₂(e) = c' ((P_ω γ_ω)(a) + Σ_y Φ_{r²}(x, y) Δ_y)` (`ae_flipTermTwo_eq_open`), with
`c' = ℓ₀(x) - ℓ₀(y) = (1 + R) (ℓ_ω(x) - ℓ_ω(y))` (`ae_dipoleCoeff_eq`). As in the planar file
`DarioStepTwoOpenBound`, with `s = max(s(x), s⁰(x))` the scale of the corrected Lemma 3.5 at `x`
(the larger side of the partition cubes of `ω` and of `ω^{e,0}` at `x`) and Lemma 3.5 in the form
`ResamplePartitionBound C₀ C`:

* `|ℓ_ω(x) - ℓ_ω(y)| ≤ G(x)`, since the bond is open in `ω`;
* the partition cubes of `ω^{e,0}` at `x` and `y` have side at most `C s`, so their boxes
  `anchorBox` have at most `7^d (C s)^d` points (`card_anchorBox_le`) and
  `R ≤ (8 d 7^d C^d s^d)²`;
* `(P_ω γ_ω)(a)² ≤ E_v(x)`, `v` the potential of `P_ω γ_ω` on the cluster;
* `(Σ_y Φ(y) Δ_y)² ≤ |B₁| (Σ_{y ∈ B₁} Φ²) (4d |B₂|)²` with `B₁ = B(x, C₀ s)` and
  `B₂ = B(x, (C₀ s + 1) + 3 C s)` (`sq_tsum_partitionChange_le`), since the potential of
  `∇∇G(e, ·)` changes by at most `1` along every open edge.

Together (`ae_flipTermTwo_sq_le_open`):
`T₂(e)² ≤ 2 (1 + (8 d 7^d C^d s^d)²)² G(x)² (E_v(x) + |B₁| (Σ_{y ∈ B₁} Φ(y)²) (4d |B₂|)²)`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal InnerProductSpace

variable {d : ℕ}

theorem mem_edgeBond_fst (a : LatticeEdge d) : a.1 ∈ (edgeBond a).1 := by
  rw [show (edgeBond a).1 = s(a.1, edgeHead a) from rfl]
  exact Sym2.mem_mk_left _ _

/-- The potential of `∇∇G(e, ·)` changes by at most `1` along the open edges of `ω^{e,b}`. -/
theorem abs_sub_clusterPot_single_le {a : LatticeEdge d} {ω : Configuration d} (b : Bool)
    {u w : Vertex d} (h : (openGraph (setBond (edgeBond a) b ω)).Adj u w) :
    |clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1) u -
        clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1) w| ≤ 1 := by
  refine abs_sub_le_of_abs_edgeGrad_le (ω := setBond (edgeBond a) b ω) (fun c => ?_) h
  have h1 : |edgeGrad (setBond (edgeBond a) true ω)
      (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) c| ≤ 1 :=
    (abs_edgeGrad_clusterPot_le _ _ c).trans (abs_greenProj_single_le _ a c)
  cases b
  · by_cases hc : EdgeOpen (setBond (edgeBond a) false ω) c
    · have e : edgeGrad (setBond (edgeBond a) false ω)
          (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) c =
          edgeGrad (setBond (edgeBond a) true ω)
            (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) c := by
        unfold edgeGrad
        rw [if_pos hc, if_pos (edgeOpen_setBond_true_of_false hc)]
      rw [e]
      exact h1
    · simp only [edgeGrad, if_neg hc, abs_zero]
      norm_num
  · exact h1

theorem sq_mul_add_le {R K c g Δv Δc E X : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ K) (hc : |c| ≤ g)
    (hv : Δv ^ 2 ≤ E) (hd : Δc ^ 2 ≤ X) :
    ((1 + R) * c * (Δv + Δc)) ^ 2 ≤ 2 * (1 + K) ^ 2 * g ^ 2 * (E + X) := by
  have hg : 0 ≤ g := (abs_nonneg c).trans hc
  have h1 : ((1 + R) * c) ^ 2 ≤ (1 + K) ^ 2 * g ^ 2 := by
    rw [mul_pow]
    refine mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 2) ?_ (sq_nonneg _)
      (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have e : (Δv + Δc) ^ 2 + (Δv - Δc) ^ 2 = 2 * Δv ^ 2 + 2 * Δc ^ 2 := by ring
  have h2 : (Δv + Δc) ^ 2 ≤ 2 * (E + X) := by linarith [sq_nonneg (Δv - Δc)]
  calc ((1 + R) * c * (Δv + Δc)) ^ 2 = ((1 + R) * c) ^ 2 * (Δv + Δc) ^ 2 := by ring
    _ ≤ ((1 + K) ^ 2 * g ^ 2) * (2 * (E + X)) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    _ = 2 * (1 + K) ^ 2 * g ^ 2 * (E + X) := by ring

theorem card_anchorBox_le {ω : Configuration d} {z : Vertex d} {M : ℕ}
    (h : 3 ^ (partitionCube ω z).scale ≤ M) :
    ((anchorBox ω z).card : ℝ) ≤ 7 ^ d * (M : ℝ) ^ d := by
  have hc : (anchorBox ω z).card = (2 * 3 ^ ((partitionCube ω z).scale + 1) + 1) ^ d := by
    unfold anchorBox
    rw [← supBox_eq_boxFinset, card_supBox]
  rw [hc]
  push_cast
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ d
  have h' : ((3 : ℝ) ^ (partitionCube ω z).scale) ≤ M := by exact_mod_cast h
  have h1 : (1 : ℝ) ≤ 3 ^ (partitionCube ω z).scale := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  nlinarith

section Planes

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **Step 2 for a bond open in `ω`.** -/
theorem ae_flipTermTwo_sq_le_open [NeZero d] (hd : 2 ≤ d) {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound (d := d) C₀ C) {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (a : LatticeEdge d), EdgeOpen ω a → ∀ hP : PartitionEvent ω,
      flipTermTwo hG hGv i j r x (edgeBond a) ω ^ 2 ≤
        2 * (1 + (8 * d * 7 ^ d * (C : ℝ) ^ d *
          ((max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1) : ℕ) : ℝ) ^ d) ^ 2) ^ 2 *
          planeGrad hG hGv i ω a.1 ^ 2 *
          (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) a.1 +
            (supBox a.1 (C₀ * max (partSide ω a.1)
                (partSide (setBond (edgeBond a) false ω) a.1))).card *
              (∑ y ∈ supBox a.1 (C₀ * max (partSide ω a.1)
                  (partSide (setBond (edgeBond a) false ω) a.1)), zdHeat d (r ^ 2) x y ^ 2) *
              (4 * d * (supBox a.1 ((C₀ * max (partSide ω a.1)
                  (partSide (setBond (edgeBond a) false ω) a.1) + 1) +
                3 * (C * max (partSide ω a.1)
                  (partSide (setBond (edgeBond a) false ω) a.1)))).card) ^ 2) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have hd0 : 0 < d := by omega
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_setBond hp0 hp1 (ae_partitionEvent hd hpc),
    ae_flipTermTwo_eq_open hG hGv hd hpc hp1 hGae, ae_flipTermTwo_eq_zero hG hGv hd hpc hp1 hGae,
    ae_dipoleCoeff_eq hG hGv hd hpc hp1 hGae] with
    ω hG' hPs hopen hzero hdip i j r hr x a haopen hP
  have hωe : ω (edgeBond a) = true := (edgeOpen_iff ω a).1 haopen
  have heq : setBond (edgeBond a) true ω = ω := by
    have := setBond_self (edgeBond a) ω
    rwa [hωe] at this
  have hP₀ := hPs (edgeBond a) false
  have hP₁ : PartitionEvent (setBond (edgeBond a) true ω) := by rw [heq]; exact hP
  set s := max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1) with hs
  have hs1 : 1 ≤ s := by
    refine le_trans ?_ (le_max_left _ _)
    rw [partSide_eq hP]
    exact Nat.one_le_pow _ _ (by norm_num)
  set E := openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) a.1 with hE
  have hE0 : 0 ≤ E := openEnergy_nonneg _ _ _
  set B₁ := supBox a.1 (C₀ * s) with hB₁
  set B₂ := supBox a.1 ((C₀ * s + 1) + 3 * (C * s)) with hB₂
  set S := ∑ y ∈ B₁, zdHeat d (r ^ 2) x y ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG0 := planeGrad_nonneg hG hGv i ω a.1
  by_cases hcase : setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 ∧
      (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a)
  swap
  · rw [hzero i j r x a hP₀ hcase]
    have : 0 ≤ 2 * (1 + (8 * d * 7 ^ d * (C : ℝ) ^ d * (s : ℝ) ^ d) ^ 2) ^ 2 *
        planeGrad hG hGv i ω a.1 ^ 2 * (E + B₁.card * S * (4 * d * B₂.card) ^ 2) := by positivity
    simpa using this
  obtain ⟨hinf₀, hreach₀⟩ := hcase
  have hinf : ω ∈ infiniteComponentEvent a.1 := by
    rw [← heq]; exact infiniteComponentEvent_setBond_true hinf₀ true
  have hyinf : ω ∈ infiniteComponentEvent (edgeHead a) := mem_infiniteComponentEvent_of_adj
    (by unfold EdgeOpen at haopen; exact haopen) hinf
  have hT := hopen i j r hr x a hP₁ hP₀ hinf₀ hreach₀
  -- `(P_ω γ_ω)(a)` through the potential on the cluster of `ω`
  have hpair : greenProj (setBond (edgeBond a) true ω) (coarseHeatField hP₁ r x j) a =
      clusterPot ω (coarseHeatField hP r x j) (edgeHead a) -
        clusterPot ω (coarseHeatField hP r x j) a.1 := by
    have key : ∀ (ω' : Configuration d) (_ : ω' = ω) (hP' : PartitionEvent ω'),
        EdgeOpen ω' a → ω' ∈ infiniteComponentEvent a.1 →
        greenProj ω' (coarseHeatField hP' r x j) a =
          clusterPot ω (coarseHeatField hP r x j) (edgeHead a) -
            clusterPot ω (coarseHeatField hP r x j) a.1 := by
      intro ω' h hP' ha' hinf'
      subst h
      have e := edgeGrad_clusterPot (coarseHeatField hP' r x j) ha'
      rw [if_pos hinf'] at e
      unfold edgeGrad at e
      rw [if_pos ha'] at e
      exact e.symm
    exact key _ heq hP₁ (by rw [heq]; exact haopen) (by rw [heq]; exact hinf)
  rw [hpair] at hT
  -- the dipole coefficient
  obtain ⟨R, hR0, hRle, hc⟩ := hdip i a hP₀ hinf₀ hreach₀
  rw [hc] at hT
  have hA0 : setBond (edgeBond a) false ω ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact infinite_partitionAnchor hd0 hP₀ 0
  have hoinf : ω ∈ infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    have := infiniteComponentEvent_setBond_true hA0 true
    rwa [heq] at this
  have hGω : ω ∈ G := by have := hG' (edgeBond a) true; rwa [heq] at this
  have hcG : |flipCorrector hG hGv i true (edgeBond a) ω a.1 -
      flipCorrector hG hGv i true (edgeBond a) ω (edgeHead a) +
      ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))| ≤ planeGrad hG hGv i ω a.1 := by
    unfold flipCorrector
    rw [heq, correctorDiff_sub_eq hG hGv hGω hinf hyinf hoinf]
    have h1 := abs_correctorDiff_add_one_le hG hGv (i := i)
      (show (openGraph ω).Adj a.1 (edgeHead a) from haopen)
    have h2 := abs_sub_le_one_of_adj (show (openGraph ω).Adj a.1 (edgeHead a) from haopen) i
    calc _ ≤ |correctorDiff hG hGv (Pi.single i 1) ω a.1 (edgeHead a)| +
          |(a.1 i : ℝ) - ((edgeHead a) i : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
  -- Lemma 3.5
  have hloc := resampleLocal_of_bound hres (setBond_agree_off (edgeBond a) true false ω) hP₁ hP₀
    (mem_edgeBond_fst a)
  have hside : resampleScale (setBond (edgeBond a) true ω) (setBond (edgeBond a) false ω) a.1 =
      s := by
    rw [hs, partSide_eq hP, partSide_eq hP₀]
    unfold resampleScale
    rw [heq]
  rw [hside] at hloc
  have hρ : ∀ z : Vertex d, (∀ i, |z i - a.1 i| ≤ 1) → ∀ i, |z i - a.1 i| < ((C₀ * s : ℕ) : ℤ) := by
    intro z hz i
    have : (2 : ℤ) ≤ ((C₀ * s : ℕ) : ℤ) := by
      have hs3 : 3 ≤ s := by
        refine le_trans ?_ (le_max_left _ _)
        rw [partSide_eq hP]
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (partitionCube ω a.1).scale := Nat.pow_le_pow_right (by norm_num)
              (by have := three_le_scale_partitionCube hP a.1; omega)
      have : 2 ≤ C₀ * s := by nlinarith
      exact_mod_cast this
    linarith [hz i]
  have hsx := ((hloc a.1).1 (hρ a.1 fun i => by simp)).2
  have hsy := ((hloc (edgeHead a)).1 (hρ (edgeHead a) fun i => by
    rw [abs_sub_comm]; exact abs_sub_edgeHead_le a i)).2
  have hcard : ∀ z, 3 ^ (partitionCube (setBond (edgeBond a) false ω) z).scale ≤ C * s →
      ((anchorBox (setBond (edgeBond a) false ω) z).card : ℝ) ≤
        7 ^ d * (C : ℝ) ^ d * (s : ℝ) ^ d := by
    intro z hz
    have := card_anchorBox_le hz
    push_cast at this
    rw [mul_pow, ← mul_assoc] at this
    exact this
  have hR : R ≤ (8 * d * 7 ^ d * (C : ℝ) ^ d * (s : ℝ) ^ d) ^ 2 := by
    refine hRle.trans (pow_le_pow_left₀ (by positivity) ?_ 2)
    have h1 := hcard _ hsx
    have h2 := hcard _ hsy
    have hd0' : (0 : ℝ) ≤ 4 * d := by positivity
    calc 4 * (d : ℝ) * (((anchorBox (setBond (edgeBond a) false ω) a.1).card : ℝ) +
          (anchorBox (setBond (edgeBond a) false ω) (edgeHead a)).card)
        ≤ 4 * d * (7 ^ d * (C : ℝ) ^ d * (s : ℝ) ^ d + 7 ^ d * (C : ℝ) ^ d * (s : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hd0'
      _ = 8 * d * 7 ^ d * (C : ℝ) ^ d * (s : ℝ) ^ d := by ring
  -- the change of partition
  have hpc := sq_tsum_partitionChange_le hd0 hloc hP₁ hP₀ (fun y => zdHeat d (r ^ 2) x y)
    (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) j
  have hV₀ := edgeVariationIn_le_card_mul (ω := setBond (edgeBond a) true ω) B₂ zero_le_one
    (fun u w h => abs_sub_clusterPot_single_le true h)
  have hV₁ := edgeVariationIn_le_card_mul (ω := setBond (edgeBond a) false ω) B₂ zero_le_one
    (fun u w h => abs_sub_clusterPot_single_le false h)
  set Δc := ∑' y, zdHeat d (r ^ 2) x y *
    partitionChange (setBond (edgeBond a) true ω) (setBond (edgeBond a) false ω)
      (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) j y with hΔc
  have hΔc : Δc ^ 2 ≤ B₁.card * S * (4 * d * B₂.card) ^ 2 := by
    refine hpc.trans ?_
    have h0 := edgeVariationIn_nonneg (setBond (edgeBond a) true ω) B₂
      (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1))
    have h1 := edgeVariationIn_nonneg (setBond (edgeBond a) false ω) B₂
      (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1))
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg h0 h1) ?_ 2) (by positivity)
    linarith
  -- `(P_ω γ_ω)(a)² ≤ E_v(x)`
  have hΔv : (clusterPot ω (coarseHeatField hP r x j) (edgeHead a) -
      clusterPot ω (coarseHeatField hP r x j) a.1) ^ 2 ≤ E := by
    rw [hE, ← neg_sub, neg_sq]
    exact sq_sub_le_openEnergy _ (show (openGraph ω).Adj a.1 (edgeHead a) from haopen)
  -- assembly
  rw [hT]
  exact sq_mul_add_le hR0 hR hcG hΔv hΔc

end Planes

end Rigidity.Corrector.GeneralDim

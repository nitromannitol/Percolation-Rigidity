import Rigidity.Proofs.Corrector.DarioStepTwoOpen

/-!
# The two dipole coefficients of Case 3

In Case 3 of Step 2 of the proof of Lemma 3.3 of Dario, the coefficient of (3.22) is
`ℓ₀(x) - ℓ₀(y)` written through the configuration `ω^{e,1}` with the bond open
(`ae_flipTermTwo_eq_open`), and `ℓ₁(x) - ℓ₁(y)` written through `ω^{e,0}` with the bond closed
(`ae_flipTermTwo_eq_walkSum`). With `R = ‖P_{ω⁰} ξ‖²`, `ξ` the field of an open path from `x` to
`y` in `ω^{e,0}`, almost surely (`ae_dipoleCoeff_eq`)

`ℓ₀(x) - ℓ₀(y) = (1 + R) (ℓ₁(x) - ℓ₁(y))`,   `0 ≤ R ≤ (8 (|R⁰(x)| + |R⁰(y)|))²`,

with `R⁰(z)` the ninefold square of the partition cube of `ω^{e,0}` at `z` (`cubeRegion`). This is
the rule of a resistor network for the bond, of unit conductance, put in parallel with the rest of
the cluster, of effective resistance `R` between `x` and `y`: `ℓ₁ - ℓ₀` is `ℓ₁(x) - ℓ₁(y)` times the
potential of `P_{ω⁰} ξ` up to a constant ((3.22) with the bond closed), and that potential increases
by `⟨P_{ω⁰} ξ, ξ⟩ = R` from `x` to `y`. The bound on `R` comes from
`abs_sub_le_two_mul_edgeVariation` and `|P_{ω⁰} ξ| ≤ √R` on every edge. Both coefficients are then
bounded by the corrector of the configuration in which the bond has its actual state.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal InnerProductSpace

/-- A function whose gradient is at most `L` on every edge changes by at most `L` along every open
edge. -/
theorem abs_sub_le_of_abs_edgeGrad_le {ω : Configuration 2} {f : Vertex 2 → ℝ} {L : ℝ}
    (hf : ∀ b, |edgeGrad ω f b| ≤ L) {u w : Vertex 2} (h : (openGraph ω).Adj u w) :
    |f u - f w| ≤ L := by
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω h)
  · have hy : w = u + LatticeProb.unit i := hi
    have hopen : EdgeOpen ω (u, i) := by
      unfold EdgeOpen edgeHead
      rw [← hy]
      exact h
    have e := hf (u, i)
    simp only [edgeGrad, if_pos hopen] at e
    change |f (u + LatticeProb.unit i) - f u| ≤ L at e
    rw [← hy, abs_sub_comm] at e
    exact e
  · have hx : u = w + LatticeProb.unit i := by rw [hi]; abel
    have hopen : EdgeOpen ω (w, i) := by
      unfold EdgeOpen edgeHead
      rw [← hx]
      exact h.symm
    have e := hf (w, i)
    simp only [edgeGrad, if_pos hopen] at e
    change |f (w + LatticeProb.unit i) - f w| ≤ L at e
    rw [← hx] at e
    exact e

/-- The total variation over the open edges inside `S` of a function changing by at most `L`
along every open edge is at most `4 |S| L`. -/
theorem edgeVariationIn_le_card_mul {ω : Configuration 2} (S : Finset (Vertex 2))
    {f : Vertex 2 → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ u w, (openGraph ω).Adj u w → |f u - f w| ≤ L) :
    edgeVariationIn ω S f ≤ 4 * S.card * L := by
  unfold edgeVariationIn
  have h : ∀ u ∈ S, (∑ w ∈ S, if (openGraph ω).Adj u w then |f u - f w| else 0) ≤ 4 * L := by
    intro u _
    have hterm : ∀ w ∈ S, (if (openGraph ω).Adj u w then |f u - f w| else 0) ≤
        if (openGraph ω).Adj u w then L else 0 := by
      intro w _
      split_ifs with huw
      · exact hf u w huw
      · exact le_rfl
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h4 : ((S.filter fun w => (openGraph ω).Adj u w).card : ℝ) ≤ 4 := by
      exact_mod_cast card_filter_adj_le ω S u
    nlinarith
  calc _ ≤ ∑ _u ∈ S, 4 * L := Finset.sum_le_sum h
    _ = 4 * S.card * L := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `⟨P ξ, ξ⟩ = ‖P ξ‖²`. -/
theorem inner_greenProj_self (ω : Configuration 2) (ξ : EdgeField) :
    ⟪greenProj ω ξ, ξ⟫_ℝ = ‖greenProj ω ξ‖ ^ 2 := by
  have hidem : greenProj ω (greenProj ω ξ) = greenProj ω ξ :=
    Submodule.starProjection_eq_self_iff.2 (greenProj_mem ω ξ)
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [← hidem]
  exact inner_greenProj_comm ω _ _

theorem abs_sub_edgeHead_le (a : LatticeEdge) (i : Fin 2) : |a.1 i - edgeHead a i| ≤ 1 := by
  have h := (abs_sub_add_unit_le a.1 a.2 i).1
  exact h

section Planes

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The two dipole coefficients of Case 3**: `ℓ₀(x) - ℓ₀(y) = (1 + R) (ℓ₁(x) - ℓ₁(y))` with
`0 ≤ R ≤ (8 (|R⁰(x)| + |R⁰(y)|))²`. -/
theorem ae_dipoleCoeff_eq {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i : Fin 2) (a : LatticeEdge),
      PlanarPartitionEvent (setBond (edgeBond a) false ω) →
      setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 →
      (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) →
      ∃ R : ℝ, 0 ≤ R ∧
        R ≤ (8 * (((cubeRegion (setBond (edgeBond a) false ω) a.1).card : ℝ) +
          (cubeRegion (setBond (edgeBond a) false ω) (edgeHead a)).card)) ^ 2 ∧
        flipCorrector hG hGv i false (edgeBond a) ω a.1 -
            flipCorrector hG hGv i false (edgeBond a) ω (edgeHead a) +
            ((a.1 i : ℝ) - ((edgeHead a) i : ℝ)) =
          (1 + R) * (flipCorrector hG hGv i true (edgeBond a) ω a.1 -
            flipCorrector hG hGv i true (edgeBond a) ω (edgeHead a) +
            ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae,
    ae_correctedPlane_sub_eq_smul_greenProj_closed hpc hp1] with ω hG' hcl i a hP₀ hinf hreach
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single i 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single i 1)
  have hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp :=
    (mem_uniqueInfiniteComponent_iff h₀ a.1).2 hinf
  have hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  have hC := mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  have hmem₀ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₀).supp :=
    fun v hv => (mem_uniqueInfiniteComponent_iff h₀ v).2 hv
  have hmem₁ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₁).supp := fun v hv =>
    (mem_uniqueInfiniteComponent_iff h₁ v).2 (infiniteComponentEvent_setBond_true hv true)
  have hA : (setBond (edgeBond a) false ω) ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact infinite_planarCoarseAnchor hP₀ 0
  obtain ⟨pw⟩ := hreach
  have hspec := (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
    (pathField (setBond (edgeBond a) false ω) pw)).choose_spec
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a) := ⟨_, rfl⟩
  -- `ℓ₁ - ℓ₀ - c w₀` has no increment on the open edges of the cluster of `ω⁰`
  have hFedge : ∀ b : LatticeEdge, EdgeOpen (setBond (edgeBond a) false ω) b →
      b.1 ∈ (uniqueInfiniteComponent h₀).supp →
      (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₀ (edgeHead b)) -
          c * (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
            (pathField (setBond (edgeBond a) false ω) pw)).choose (edgeHead b) =
        (extendComp _ ℓ₁ b.1 - extendComp _ ℓ₀ b.1) -
          c * (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
            (pathField (setBond (edgeBond a) false ω) pw)).choose b.1 := by
    intro b hb hb1
    have key := hcl a h₁ h₀ hx hy (Pi.single i 1) ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw b hb hb1
    rw [← hc, hspec b hb] at key
    linear_combination key
  have hFxy := eq_of_walk_of_edge (S := (uniqueInfiniteComponent h₀).supp)
    (F := fun v => (extendComp _ ℓ₁ v - extendComp _ ℓ₀ v) -
      c * (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
        (pathField (setBond (edgeBond a) false ω) pw)).choose v)
    (fun z w hz hzw => (uniqueInfiniteComponent h₀).mem_supp_of_adj_mem_supp hz hzw) hFedge pw hx
  have hW := walkSum_eq_of_isGradOf _ hspec pw
  rw [← inner_pathField, inner_greenProj_self] at hW
  -- the bound on the effective resistance
  set ηn := ‖greenProj (setBond (edgeBond a) false ω)
    (pathField (setBond (edgeBond a) false ω) pw)‖ with hηn
  have hηn0 : 0 ≤ ηn := norm_nonneg _
  have hpot : ∀ b, |edgeGrad (setBond (edgeBond a) false ω)
      (clusterPot (setBond (edgeBond a) false ω)
        (pathField (setBond (edgeBond a) false ω) pw)) b| ≤ ηn := fun b => by
    refine (abs_edgeGrad_clusterPot_le _ _ b).trans ?_
    have := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (greenProj (setBond (edgeBond a) false ω) (pathField (setBond (edgeBond a) false ω) pw)) b
    rwa [Real.norm_eq_abs] at this
  have hreach' : ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk
      (edgeHead a)).supp.Infinite := by
    have : (openGraph (setBond (edgeBond a) false ω)).connectedComponentMk (edgeHead a) =
        (openGraph (setBond (edgeBond a) false ω)).connectedComponentMk a.1 :=
      (SimpleGraph.ConnectedComponent.sound pw.reachable).symm
    rw [this]
    exact hinf
  have hev := abs_sub_le_two_mul_edgeVariation hP₀ (abs_sub_edgeHead_le a) hinf hreach'
    (clusterPot (setBond (edgeBond a) false ω) (pathField (setBond (edgeBond a) false ω) pw))
  have hv1 := edgeVariationIn_le_card_mul (ω := setBond (edgeBond a) false ω)
    (cubeRegion (setBond (edgeBond a) false ω) a.1) hηn0
    (fun u w huw => abs_sub_le_of_abs_edgeGrad_le hpot huw)
  have hv2 := edgeVariationIn_le_card_mul (ω := setBond (edgeBond a) false ω)
    (cubeRegion (setBond (edgeBond a) false ω) (edgeHead a)) hηn0
    (fun u w huw => abs_sub_le_of_abs_edgeGrad_le hpot huw)
  have hcx : clusterPot (setBond (edgeBond a) false ω)
      (pathField (setBond (edgeBond a) false ω) pw) a.1 =
      (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
        (pathField (setBond (edgeBond a) false ω) pw)).choose a.1 := if_pos hinf
  have hcy : clusterPot (setBond (edgeBond a) false ω)
      (pathField (setBond (edgeBond a) false ω) pw) (edgeHead a) =
      (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
        (pathField (setBond (edgeBond a) false ω) pw)).choose (edgeHead a) := if_pos hreach'
  rw [hcx, hcy, abs_sub_comm, ← hW, abs_of_nonneg (sq_nonneg _)] at hev
  set N : ℝ := ((cubeRegion (setBond (edgeBond a) false ω) a.1).card : ℝ) +
    (cubeRegion (setBond (edgeBond a) false ω) (edgeHead a)).card with hN
  have hN0 : 0 ≤ N := by positivity
  have hsq : ηn ^ 2 ≤ 8 * N * ηn := by
    have e : 8 * N * ηn = 8 * ((cubeRegion (setBond (edgeBond a) false ω) a.1).card : ℝ) * ηn +
        8 * ((cubeRegion (setBond (edgeBond a) false ω) (edgeHead a)).card : ℝ) * ηn := by
      rw [hN]; ring
    rw [e]
    linarith
  have hle : ηn ≤ 8 * N := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [mul_pos (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 8 * N) hlt) (sub_pos.2 hlt)]
  refine ⟨ηn ^ 2, sq_nonneg _, pow_le_pow_left₀ hηn0 hle 2, ?_⟩
  -- the identity
  have hx₁ : a.1 ∈ (uniqueInfiniteComponent h₁).supp := (hC _).2 hx
  have hy₁ : edgeHead a ∈ (uniqueInfiniteComponent h₁).supp := (hC _).2 hy
  rw [flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ hx (hmem₀ _ hA),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ hy (hmem₀ _ hA),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ hx₁ (hmem₁ _ hA),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ hy₁ (hmem₁ _ hA)]
  simp only [sum_single_mul_coord]
  linear_combination -hFxy - c * hW + ηn ^ 2 * hc

end Planes

end Rigidity.Corrector

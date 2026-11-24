import Rigidity.Proofs.Corrector.DarioStepTwoElectric

/-!
# The weight of the Step 2 sum and the bonds closed in the configuration

The bound of the Step 2 sum of the proof of Lemma 3.3 of Dario is written with

* the side `s(z)` of the partition cube at `z`, through the stopping size (`planarSide`);
* a bound `G(z)` for the gradient of the corrected plane of slope `e_i` at `z`: one plus the
  corrector increments along the open edges at `z` (`planeGrad`), so that
  `|χ(z) - χ(w)| + 1 ≤ G(z)` along every open edge `{z, w}` (`abs_correctorDiff_add_one_le`);
* the open energy `E_f(u) = Σ_{w ~ u} (f(u) - f(w))²` of a function at a vertex (`openEnergy`).

The total variations of Step 1 are bounded by these: `V_S(f) ≤ 4 Σ_{u ∈ S} g(u)` when `f` changes
by at most `g(u)` along the open edges at `u` (`edgeVariationIn_le_four_mul_sum`), and
`V_S(f)² ≤ 4 |S| Σ_{u ∈ S} E_f(u)` (`sq_edgeVariationIn_le`, Cauchy–Schwarz).

For a bond `e` of `a = (x, i')` closed in `ω`, `ω^{e,0} = ω` and, in Case 3,
`T₂(e) = (ℓ₁(x) - ℓ₁(y)) (v(y) - v(x))` with `v` the potential of `P_ω γ_ω` on the infinite cluster
(`ae_flipTermTwo_eq_walkSum`, `walkSum_greenProj_eq_clusterPot`). With
`|ℓ₁(x) - ℓ₁(y)| ≤ |ℓ₀(x) - ℓ₀(y)|` (`ae_dipoleCoeff_eq`) and the variations over the partition
squares of `ω` at `x` and `y`, `ae_flipTermTwo_sq_le_closed` gives

`T₂(e)² ≤ 2¹⁴ (Σ_{z ∈ B} G(z))² |B| Σ_{u ∈ B} E_v(u)`,   `B = B(x, 1 + 5 max(s(x), s(y)))`,

the first part of (4) of the route through estimate (2).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare
open scoped Classical ENNReal InnerProductSpace

/-- The side of the partition cube at `z`, through the stopping size. -/
noncomputable def planarSide (ω : Configuration 2) (z : Vertex 2) : ℕ :=
  ⌊TriadicCube.stoppingSize (planarGoodCubes ω) z⌋₊

theorem measurable_planarSide (z : Vertex 2) : Measurable fun ω => planarSide ω z :=
  Nat.measurable_floor.comp (measurable_stoppingSize_planar z)

theorem planarSide_eq {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (z : Vertex 2) :
    planarSide ω z = 3 ^ (planarPartCube ω z).scale := by
  unfold planarSide
  rw [TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP _).1 (planarPartCube_spec hP _).2]
  rw [show (3 : ℝ) ^ (planarPartCube ω z).scale =
    ((3 ^ (planarPartCube ω z).scale : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]

/-- The open energy of `f` at `u`. -/
noncomputable def openEnergy (ω : Configuration 2) (f : Vertex 2 → ℝ) (u : Vertex 2) : ℝ :=
  ∑ w ∈ (openGraph ω).neighborFinset u, (f u - f w) ^ 2

theorem openEnergy_nonneg (ω : Configuration 2) (f : Vertex 2 → ℝ) (u : Vertex 2) :
    0 ≤ openEnergy ω f u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sq_sub_le_openEnergy {ω : Configuration 2} (f : Vertex 2 → ℝ) {u w : Vertex 2}
    (h : (openGraph ω).Adj u w) : (f u - f w) ^ 2 ≤ openEnergy ω f u :=
  Finset.single_le_sum (f := fun w => (f u - f w) ^ 2) (fun _ _ => sq_nonneg _)
    ((SimpleGraph.mem_neighborFinset _ _ _).2 h)

/-- **The total variation by a pointwise bound**: if `f` changes by at most `g(u)` along the open
edges at `u`, then `V_S(f) ≤ 4 Σ_{u ∈ S} g(u)`. -/
theorem edgeVariationIn_le_four_mul_sum {ω : Configuration 2} (S : Finset (Vertex 2))
    {f g : Vertex 2 → ℝ} (hg : ∀ u, 0 ≤ g u)
    (hf : ∀ u w, (openGraph ω).Adj u w → |f u - f w| ≤ g u) :
    edgeVariationIn ω S f ≤ 4 * ∑ u ∈ S, g u := by
  unfold edgeVariationIn
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  have hterm : ∀ w ∈ S, (if (openGraph ω).Adj u w then |f u - f w| else 0) ≤
      if (openGraph ω).Adj u w then g u else 0 := by
    intro w _
    split_ifs with huw
    · exact hf u w huw
    · exact le_rfl
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h4 : ((S.filter fun w => (openGraph ω).Adj u w).card : ℝ) ≤ 4 := by
    exact_mod_cast card_filter_adj_le ω S u
  nlinarith [hg u]

/-- **The total variation by the energy** (Cauchy–Schwarz): `V_S(f)² ≤ 4 |S| Σ_{u ∈ S} E_f(u)`. -/
theorem sq_edgeVariationIn_le (ω : Configuration 2) (S : Finset (Vertex 2)) (f : Vertex 2 → ℝ) :
    edgeVariationIn ω S f ^ 2 ≤ 4 * S.card * ∑ u ∈ S, openEnergy ω f u := by
  unfold edgeVariationIn
  have hu : ∀ u ∈ S, (∑ w ∈ S, if (openGraph ω).Adj u w then |f u - f w| else 0) ^ 2 ≤
      4 * openEnergy ω f u := by
    intro u _
    rw [← Finset.sum_filter]
    have hc : ((S.filter fun w => (openGraph ω).Adj u w).card : ℝ) ≤ 4 := by
      exact_mod_cast card_filter_adj_le ω S u
    have hsub : S.filter (fun w => (openGraph ω).Adj u w) ⊆ (openGraph ω).neighborFinset u :=
      fun w hw => (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hw).2
    have hs : ∑ w ∈ S.filter (fun w => (openGraph ω).Adj u w), |f u - f w| ^ 2 ≤
        openEnergy ω f u := by
      simp only [sq_abs]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    have h0 : 0 ≤ ∑ w ∈ S.filter (fun w => (openGraph ω).Adj u w), |f u - f w| ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hcs := sq_sum_le_card_mul_sum_sq (s := S.filter (fun w => (openGraph ω).Adj u w))
      (f := fun w => |f u - f w|)
    nlinarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := S)
    (f := fun u => ∑ w ∈ S, if (openGraph ω).Adj u w then |f u - f w| else 0)
  calc _ ≤ (S.card : ℝ) * ∑ u ∈ S,
        (∑ w ∈ S, if (openGraph ω).Adj u w then |f u - f w| else 0) ^ 2 := hcs
    _ ≤ S.card * ∑ u ∈ S, 4 * openEnergy ω f u :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hu) (Nat.cast_nonneg _)
    _ = 4 * S.card * ∑ u ∈ S, openEnergy ω f u := by rw [← Finset.mul_sum]; ring

/-- Along a walk of the cluster, the sum of `P ξ` is the increment of its potential on the
cluster. -/
theorem walkSum_greenProj_eq_clusterPot {ω : Configuration 2} (ξ : EdgeField) {u v : Vertex 2}
    (p : (openGraph ω).Walk u v) (hu : ω ∈ infiniteComponentEvent u) :
    walkSum ω (greenProj ω ξ) p = clusterPot ω ξ v - clusterPot ω ξ u := by
  have hv : ω ∈ infiniteComponentEvent v := by
    change ((openGraph ω).connectedComponentMk v).supp.Infinite
    rw [← SimpleGraph.ConnectedComponent.sound p.reachable]
    exact hu
  rw [walkSum_eq_of_isGradOf _ (exists_isGradOf_greenProj ω ξ).choose_spec p]
  unfold clusterPot
  rw [if_pos hu, if_pos hv]

theorem abs_sub_le_one_of_adj {ω : Configuration 2} {u w : Vertex 2} (h : (openGraph ω).Adj u w)
    (i : Fin 2) : |(u i : ℝ) - (w i : ℝ)| ≤ 1 := by
  obtain ⟨k, hk | hk⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω h)
  · have hw : w = u + LatticeProb.unit k := hk
    have := (abs_sub_add_unit_le u k i).1
    rw [← hw] at this
    exact_mod_cast this
  · have hu : u = w + LatticeProb.unit k := by rw [hk]; abel
    have := (abs_sub_add_unit_le w k i).2
    rw [← hu] at this
    exact_mod_cast this

/-- The ninefold square of the partition cube at `z` lies in the box of radius `L + 5 s(z)` around
any `x` with `|z - x|_∞ ≤ L`. -/
theorem cubeRegion_subset_supBox {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x z : Vertex 2} {L : ℕ} (hzx : ∀ i, |z i - x i| ≤ L) :
    cubeRegion ω z ⊆ supBox x (L + 5 * planarSide ω z) :=
  ninefold_subset_supBox (planarPartCube_spec hP z).1 hzx (planarSide_eq hP z).ge

theorem sq_le_of_abs_le_two_mul_add {Δ V₁ V₂ X : ℝ} (hΔ : |Δ| ≤ 2 * (V₁ + V₂))
    (h1 : V₁ ^ 2 ≤ X) (h2 : V₂ ^ 2 ≤ X) : Δ ^ 2 ≤ 16 * X := by
  have hsq : Δ ^ 2 ≤ (2 * (V₁ + V₂)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
  nlinarith [sq_nonneg (V₁ - V₂)]

theorem supBox_mono {x : Vertex 2} {r r' : ℕ} (h : r ≤ r') : supBox x r ⊆ supBox x r' := by
  intro z hz
  rw [mem_supBox] at hz ⊢
  intro i
  exact (hz i).trans (by exact_mod_cast h)

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- A bound for the gradient of the corrected plane of slope `e_i` at `z`. -/
noncomputable def planeGrad (i : Fin 2) (ω : Configuration 2) (z : Vertex 2) : ℝ :=
  1 + ∑ k : Fin 2,
    ((if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0))

theorem planeGrad_term_nonneg (i : Fin 2) (ω : Configuration 2) (z : Vertex 2) (k : Fin 2) :
    0 ≤ (if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0) := by
  refine add_nonneg ?_ ?_ <;> split_ifs <;> positivity

theorem one_le_planeGrad (i : Fin 2) (ω : Configuration 2) (z : Vertex 2) :
    1 ≤ planeGrad hG hGv i ω z := by
  unfold planeGrad
  have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => planeGrad_term_nonneg hG hGv i ω z k
  linarith

theorem planeGrad_nonneg (i : Fin 2) (ω : Configuration 2) (z : Vertex 2) :
    0 ≤ planeGrad hG hGv i ω z :=
  zero_le_one.trans (one_le_planeGrad hG hGv i ω z)

/-- `|χ(z) - χ(w)| + 1 ≤ G(z)` along every open edge `{z, w}`. -/
theorem abs_correctorDiff_add_one_le {i : Fin 2} {ω : Configuration 2} {z w : Vertex 2}
    (h : (openGraph ω).Adj z w) :
    |correctorDiff hG hGv (Pi.single i 1) ω z w| + 1 ≤ planeGrad hG hGv i ω z := by
  have hsum : ∀ k, (if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0) ≤
      ∑ k : Fin 2, ((if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0)) :=
    fun k => Finset.single_le_sum (f := fun k => (if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0))
      (fun k _ => planeGrad_term_nonneg hG hGv i ω z k) (Finset.mem_univ k)
  unfold planeGrad
  obtain ⟨k, hk | hk⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω h)
  · have hw : w = z + LatticeProb.unit k := hk
    have hopen : EdgeOpen ω (z, k) := by
      unfold EdgeOpen edgeHead
      rw [← hw]
      exact h
    have h2 := hsum k
    rw [if_pos hopen, ← hw] at h2
    have h3 : 0 ≤ (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0) := by
      split_ifs <;> positivity
    linarith
  · have hw : w = z - LatticeProb.unit k := hk
    have hopen : EdgeOpen ω (z - LatticeProb.unit k, k) := by
      unfold EdgeOpen edgeHead
      rw [sub_add_cancel, ← hw]
      exact h.symm
    have h2 := hsum k
    rw [if_pos hopen, ← hw] at h2
    have h3 : 0 ≤ (if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) := by
      split_ifs <;> positivity
    linarith

/-- The corrected plane of slope `e_i` rooted at `o`, extended by `0` off the infinite cluster,
changes by at most `G(u)` along the open edges at `u`. -/
theorem abs_sub_rootedPlane_le {i : Fin 2} {ω : Configuration 2} (hω : ω ∈ G) {o : Vertex 2}
    (ho : ω ∈ infiniteComponentEvent o) {u w : Vertex 2} (h : (openGraph ω).Adj u w) :
    |(if ω ∈ infiniteComponentEvent u then
          correctorDiff hG hGv (Pi.single i 1) ω u o + (u i : ℝ) else 0) -
        (if ω ∈ infiniteComponentEvent w then
          correctorDiff hG hGv (Pi.single i 1) ω w o + (w i : ℝ) else 0)| ≤
      planeGrad hG hGv i ω u := by
  by_cases hu : ω ∈ infiniteComponentEvent u
  · have hw := mem_infiniteComponentEvent_of_adj h hu
    rw [if_pos hu, if_pos hw]
    have e := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω hu hw ho
    have h1 := abs_correctorDiff_add_one_le hG hGv (i := i) h
    have h2 := abs_sub_le_one_of_adj h i
    calc |correctorDiff hG hGv (Pi.single i 1) ω u o + (u i : ℝ) -
          (correctorDiff hG hGv (Pi.single i 1) ω w o + (w i : ℝ))|
        = |correctorDiff hG hGv (Pi.single i 1) ω u w + ((u i : ℝ) - (w i : ℝ))| := by
          rw [← e]; ring_nf
      _ ≤ |correctorDiff hG hGv (Pi.single i 1) ω u w| + |(u i : ℝ) - (w i : ℝ)| := abs_add_le _ _
      _ ≤ planeGrad hG hGv i ω u := by linarith
  · have hw : ω ∉ infiniteComponentEvent w := fun hw =>
      hu (mem_infiniteComponentEvent_of_adj h.symm hw)
    rw [if_neg hu, if_neg hw, sub_zero, abs_zero]
    exact planeGrad_nonneg hG hGv i ω u

/-- **Step 2 for a bond closed in `ω`**: almost surely, `T₂(e)² ≤ 2¹⁴ (Σ_B G)² |B| Σ_B E_v` with
`B` the box of radius `1 + 5 max(s(x), s(y))` around `x` and `v` the potential of `P_ω γ_ω` on the
infinite cluster. -/
theorem ae_flipTermTwo_sq_le_closed {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i j : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (a : LatticeEdge), ¬ EdgeOpen ω a → ∀ hP : PlanarPartitionEvent ω,
      flipTermTwo hG hGv i j r x (edgeBond a) ω ^ 2 ≤
        2 ^ 14 * (∑ z ∈ supBox a.1 (1 + 5 * max (planarSide ω a.1) (planarSide ω (edgeHead a))),
            planeGrad hG hGv i ω z) ^ 2 *
          (supBox a.1 (1 + 5 * max (planarSide ω a.1) (planarSide ω (edgeHead a)))).card *
          ∑ u ∈ supBox a.1 (1 + 5 * max (planarSide ω a.1) (planarSide ω (edgeHead a))),
            openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_flipTermTwo_eq_walkSum hG hGv hpc hp1 hGae,
    ae_flipTermTwo_eq_zero hG hGv hpc hp1 hGae, ae_dipoleCoeff_eq hG hGv hpc hp1 hGae] with
    ω hG' hwalk hzero hdip i j r hr x a hclosed hP
  have hωe : ω (edgeBond a) = false := by
    rw [edgeOpen_iff] at hclosed
    simpa using hclosed
  have heq : setBond (edgeBond a) false ω = ω := by
    have := setBond_self (edgeBond a) ω
    rwa [hωe] at this
  set B := supBox a.1 (1 + 5 * max (planarSide ω a.1) (planarSide ω (edgeHead a))) with hB
  have hE0 : 0 ≤ ∑ u ∈ B, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
    Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u
  have hRHS0 : 0 ≤ 2 ^ 14 * (∑ z ∈ B, planeGrad hG hGv i ω z) ^ 2 * (B.card : ℝ) *
      ∑ u ∈ B, openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u :=
    mul_nonneg (by positivity) hE0
  have hP₀ : PlanarPartitionEvent (setBond (edgeBond a) false ω) := by rw [heq]; exact hP
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
    have key : ∀ (ω' : Configuration 2) (_ : ω' = ω) (hP' : PlanarPartitionEvent ω')
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
    exact infinite_planarCoarseAnchor hP 0
  have hGω : ω ∈ G := by have := hG' (edgeBond a) false; rwa [heq] at this
  obtain ⟨w, hw⟩ : ∃ w : Vertex 2 → ℝ, w = fun z => if ω ∈ infiniteComponentEvent z then
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
  have hwev := abs_sub_le_two_mul_edgeVariation hP (abs_sub_edgeHead_le a) hinf hyinf w
  have hwl : ∀ u w', (openGraph ω).Adj u w' → |w u - w w'| ≤ planeGrad hG hGv i ω u :=
    fun u w' h => by rw [hw]; exact abs_sub_rootedPlane_le hG hGv hGω hoinf h
  have hgx := edgeVariationIn_le_four_mul_sum (cubeRegion ω a.1) (planeGrad_nonneg hG hGv i ω) hwl
  have hgy := edgeVariationIn_le_four_mul_sum (cubeRegion ω (edgeHead a))
    (planeGrad_nonneg hG hGv i ω) hwl
  -- the regions lie in `B`
  have hsx : planarSide ω a.1 ≤ max (planarSide ω a.1) (planarSide ω (edgeHead a)) :=
    le_max_left _ _
  have hsy : planarSide ω (edgeHead a) ≤ max (planarSide ω a.1) (planarSide ω (edgeHead a)) :=
    le_max_right _ _
  have hRx : cubeRegion ω a.1 ⊆ B := by
    refine (cubeRegion_subset_supBox hP (L := 0) fun i => by simp).trans (supBox_mono ?_)
    omega
  have hRy : cubeRegion ω (edgeHead a) ⊆ B := by
    refine (cubeRegion_subset_supBox hP (L := 1) fun i => ?_).trans (supBox_mono ?_)
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
  -- `|c'| ≤ 16 Σ_B G`
  have hcb : |w a.1 - w (edgeHead a)| ≤ 16 * SG := by
    have := hGs _ hRx
    have := hGs _ hRy
    linarith
  -- `(v(y) - v(x))² ≤ 64 |B| Σ_B E`
  have hvb : (clusterPot ω (coarseHeatField hP r x j) (edgeHead a) -
      clusterPot ω (coarseHeatField hP r x j) a.1) ^ 2 ≤ 64 * B.card * SE := by
    have hev := abs_sub_le_two_mul_edgeVariation hP (abs_sub_edgeHead_le a) hinf hyinf
      (clusterPot ω (coarseHeatField hP r x j))
    have h1 := sq_edgeVariationIn_le ω (cubeRegion ω a.1) (clusterPot ω (coarseHeatField hP r x j))
    have h2 := sq_edgeVariationIn_le ω (cubeRegion ω (edgeHead a))
      (clusterPot ω (coarseHeatField hP r x j))
    have h1' := hEs _ hRx
    have h2' := hEs _ hRy
    have hc1 := hcard _ hRx
    have hc2 := hcard _ hRy
    have hB1 : edgeVariationIn ω (cubeRegion ω a.1) (clusterPot ω (coarseHeatField hP r x j)) ^ 2 ≤
        4 * B.card * SE := by
      have := mul_le_mul hc1 h1' (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u)
        (Nat.cast_nonneg _)
      linarith
    have hB2 : edgeVariationIn ω (cubeRegion ω (edgeHead a))
        (clusterPot ω (coarseHeatField hP r x j)) ^ 2 ≤ 4 * B.card * SE := by
      have := mul_le_mul hc2 h2' (Finset.sum_nonneg fun u _ => openEnergy_nonneg _ _ u)
        (Nat.cast_nonneg _)
      linarith
    rw [abs_sub_comm] at hev
    have := sq_le_of_abs_le_two_mul_add hev hB1 hB2
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
      ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))) ^ 2 ≤ (16 * SG) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hcc.trans hcb) 2
  calc _ ≤ (16 * SG) ^ 2 * (64 * B.card * SE) :=
        mul_le_mul hc2 hvb (sq_nonneg _) (by positivity)
    _ = 2 ^ 14 * SG ^ 2 * B.card * SE := by ring

end Grad

end Rigidity.Corrector

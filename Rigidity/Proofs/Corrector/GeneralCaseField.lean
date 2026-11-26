import Rigidity.Proofs.Corrector.GeneralCaseThreePairing
import Rigidity.Proofs.Corrector.GeneralCaseThreeAe

/-!
# Fields, potentials and extensions on the cluster of `ℤᵈ` for Step 2 of Lemma 3.3 of Dario

The parts of the planar files `DarioCaseThreeCorrector`, `DarioCaseThreeClosed`, `DarioCaseOneTwo`,
`DarioStepTwoCases`, `DarioStepTwoSplit`, `DarioStepTwoOpen` and `DarioStepTwoElectric` that do not
involve the forced configurations `ω^{e,b}`, on `ℤᵈ`:

* `extendComp`: a function on a component, extended by zero to the lattice, harmonic in the
  vertex form when it is harmonic on the component
  (`edgeDiv_edgeGrad_extendComp_of_harmonic`), of sublinear growth after subtracting its slope
  (`sublinearOn_of_componentSlopeAsymptotics`);
* `edgeDiv_pathField`: the field of a walk from `x` to `y` has divergence `δ_x - δ_y`;
* `isCorrectedPlane_of_harmonic`: a harmonic function with slope asymptotics is a corrected plane;
* `clusterPot`: the potential of `greenProj ω ξ` on the infinite components, with
  `|∇ clusterPot| ≤ |Pξ|` (`abs_edgeGrad_clusterPot_le`) and `|P 1_a| ≤ 1`
  (`abs_greenProj_single_le`);
* `edgeVariationIn_le_card_mul`: the total variation over `S` of a function changing by at most
  `L` along the open edges is at most `2d |S| L`;
* `inner_greenProj_self`: `⟨Pξ, ξ⟩ = ‖Pξ‖²`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal InnerProductSpace

variable {d : ℕ} (ω : Configuration d)

/-- A function on a component, extended by zero to the lattice. -/
noncomputable def extendComp {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    (z : Vertex d) : ℝ :=
  if h : z ∈ C.supp then u ⟨z, h⟩ else 0

theorem extendComp_of_mem {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    {z : Vertex d} (h : z ∈ C.supp) : extendComp C u z = u ⟨z, h⟩ := by
  simp [extendComp, h]

theorem edgeDiv_edgeGrad_extendComp_of_harmonic {ω : Configuration d} (C : OpenComponent ω)
    {u : C → ℝ} (hu : ∀ x, componentLaplacian C u x = 0) {z : Vertex d} (hz : z ∈ C.supp) :
    edgeDiv ω (edgeGrad ω (extendComp C u)) z = 0 := by
  rw [← laplacian_openGraph_eq_edgeDiv, ← componentLaplacian_restrict_eq C (extendComp C u)
    ⟨z, hz⟩]
  have hfun : (fun y : C => extendComp C u y.val) = u := by
    funext y
    rw [extendComp_of_mem C u y.2]
  rw [hfun]
  exact hu _

theorem sublinearOn_of_componentSlopeAsymptotics {ω : Configuration d} (C : OpenComponent ω)
    {q : Fin d → ℝ} {u : C → ℝ} (hu : componentSlopeAsymptotics C q u) :
    SublinearOn C.supp (fun z => extendComp C u z - ∑ i, q i * (z i : ℝ)) := by
  intro ε hε
  obtain ⟨R₀, hR₀, htail⟩ := hu (ε / 2) (by positivity)
  refine ⟨max R₀ 1, fun z hz hR => ?_⟩
  set e := ‖latticeEuclideanEmbedding z‖ with he
  have he1 : 1 ≤ e := (le_max_right _ _).trans hR
  have hball : (⟨z, hz⟩ : C) ∈ componentEuclideanBall C 0 (e + 1) := by
    rw [mem_componentEuclideanBall, latticeEuclideanEmbedding_zero, dist_zero_right]
    linarith
  have h := htail (e + 1) (by linarith [(le_max_left R₀ 1).trans hR]) ⟨z, hz⟩ hball
  simp only [componentSlope] at h
  beta_reduce
  rw [extendComp_of_mem C u hz]
  calc |u ⟨z, hz⟩ - ∑ i, q i * (z i : ℝ)| ≤ ε / 2 * (e + 1) := h
    _ ≤ ε * e := by nlinarith


theorem extendComp_of_not_mem {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    {z : Vertex d} (h : z ∉ C.supp) : extendComp C u z = 0 := by
  simp [extendComp, h]


theorem edgeDiv_add (η ζ : LatticeEdge d → ℝ) (z : Vertex d) :
    edgeDiv ω (η + ζ) z = edgeDiv ω η z + edgeDiv ω ζ z := by
  unfold edgeDiv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  split_ifs <;> ring

theorem edgeDiv_neg (η : LatticeEdge d → ℝ) (z : Vertex d) :
    edgeDiv ω (-η) z = -edgeDiv ω η z := by
  unfold edgeDiv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.neg_apply]
  split_ifs <;> ring

theorem edgeDiv_zero (z : Vertex d) : edgeDiv ω 0 z = 0 := by
  unfold edgeDiv
  simp

theorem edgeDiv_dartField {u v : Vertex d} (h : (openGraph ω).Adj u v) (z : Vertex d) :
    edgeDiv ω (dartField u v : LatticeEdge d → ℝ) z =
      (if z = u then 1 else 0) - (if z = v then 1 else 0) := by
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω h)
  · subst hi
    rw [dartField_add_unit]
    exact edgeDiv_single ω (a := (u, i)) h z
  · have hx : u = v + LatticeProb.unit i := by rw [hi]; abel
    subst hx
    rw [dartField_unit_add, lp.coeFn_neg, edgeDiv_neg,
      edgeDiv_single ω (a := (v, i)) h.symm z]
    simp only [edgeHead]
    ring_nf

/-- **The field of a walk from `x` to `y` has divergence `δ_x - δ_y`.** -/
theorem edgeDiv_pathField {x y : Vertex d} (p : (openGraph ω).Walk x y) (z : Vertex d) :
    edgeDiv ω (pathField ω p : LatticeEdge d → ℝ) z =
      (if z = x then 1 else 0) - (if z = y then 1 else 0) := by
  induction p with
  | nil =>
    simp only [pathField, SimpleGraph.Walk.darts_nil, List.map_nil, List.sum_nil, lp.coeFn_zero,
      sub_self]
    exact edgeDiv_zero ω z
  | @cons u v w hadj p ih =>
    unfold pathField at ih ⊢
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, lp.coeFn_add]
    rw [edgeDiv_add, ih, edgeDiv_dartField ω hadj]
    ring


/-- A harmonic function with slope asymptotics is a corrected plane. -/
theorem isCorrectedPlane_of_harmonic {ω : Configuration d} (C : OpenComponent ω) {q : Fin d → ℝ}
    {u : C → ℝ} (hh : ∀ x, componentLaplacian C u x = 0) (hs : componentSlopeAsymptotics C q u) :
    IsCorrectedPlane C q u := by
  refine ⟨⟨hh, ?_⟩, hs⟩
  obtain ⟨R₀, hR₀, htail⟩ := hs 1 one_pos
  set K : ℝ := 1 + ∑ i, |q i| with hK
  have hK0 : 0 ≤ K := by positivity
  have hball : ∀ R : ℝ, R₀ ≤ R → componentBallL2 C 0 R u ≤ K * R := by
    intro R hR
    have hR0 : 0 < R := hR₀.trans_le hR
    refine componentBallL2_le_of_abs_le C 0 R u (by positivity) fun x hx => ?_
    have h1 := htail R hR x hx
    have hxR : ‖latticeEuclideanEmbedding x.val‖ < R := by
      have := (mem_componentEuclideanBall C 0 R x).1 hx
      rwa [latticeEuclideanEmbedding_zero, dist_zero_right] at this
    have hslope : |componentSlope C q x| ≤ (∑ i, |q i|) * R := by
      unfold componentSlope
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (abs_coord_le_norm x.val i).trans hxR.le
    have := abs_sub_abs_le_abs_sub (u x) (componentSlope C q x)
    rw [hK]
    nlinarith [abs_nonneg (componentSlope C q x)]
  change Tendsto (fun R : ℝ => (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u) atTop (nhds 0)
  have hlim : Tendsto (fun R : ℝ => K * R⁻¹) atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul K
  refine squeeze_zero' (eventually_atTop.2 ⟨max R₀ 1, fun R hR => ?_⟩)
    (eventually_atTop.2 ⟨max R₀ 1, fun R hR => ?_⟩) hlim
  · have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR)
    exact mul_nonneg (by positivity) (componentBallL2_nonneg C 0 R u)
  · have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    have hb := hball R ((le_max_left _ _).trans hR)
    calc (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u ≤ (R ^ (1 + 1))⁻¹ * (K * R) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = K * R⁻¹ := by field_simp; ring

theorem laplacian_neg {ω : Configuration d} (f : Vertex d → ℝ) (z : Vertex d) :
    LatticeProb.Graph.laplacian (openGraph ω) (fun y => -f y) z =
      -LatticeProb.Graph.laplacian (openGraph ω) f z := by
  unfold LatticeProb.Graph.laplacian
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring


/-- The heat average of the gradient of a constant vanishes. -/
theorem heatComp_const (c r : ℝ) (x : Vertex d) (j : Fin d) :
    heatComp (fun _ => c) r x j = 0 := by
  unfold heatComp
  simp


theorem sum_single_mul_coord (i : Fin d) (v : Vertex d) :
    ∑ k, (Pi.single i 1 : Fin d → ℝ) k * (v k : ℝ) = (v i : ℝ) := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp


/-- The potential of `greenProj ω ξ` on the infinite components of `ω`, `0` elsewhere. -/
noncomputable def clusterPot (ω : Configuration d) (ξ : EdgeField d) (z : Vertex d) : ℝ :=
  if ω ∈ infiniteComponentEvent z then (exists_isGradOf_greenProj ω ξ).choose z else 0

theorem infiniteComponentEvent_iff_of_adj {ω : Configuration d} {u v : Vertex d}
    (h : (openGraph ω).Adj u v) :
    ω ∈ infiniteComponentEvent u ↔ ω ∈ infiniteComponentEvent v := by
  change ((openGraph ω).connectedComponentMk u).supp.Infinite ↔
    ((openGraph ω).connectedComponentMk v).supp.Infinite
  rw [SimpleGraph.ConnectedComponent.sound h.reachable]

theorem edgeGrad_clusterPot {ω : Configuration d} (ξ : EdgeField d) {b : LatticeEdge d}
    (hb : EdgeOpen ω b) :
    edgeGrad ω (clusterPot ω ξ) b =
      if ω ∈ infiniteComponentEvent b.1 then greenProj ω ξ b else 0 := by
  have hiff := infiniteComponentEvent_iff_of_adj (ω := ω) hb
  unfold edgeGrad clusterPot
  rw [if_pos hb]
  by_cases h : ω ∈ infiniteComponentEvent b.1
  · rw [if_pos (hiff.1 h), if_pos h, if_pos h]
    exact ((exists_isGradOf_greenProj ω ξ).choose_spec b hb).symm
  · rw [if_neg (fun h' => h (hiff.2 h')), if_neg h, if_neg h, sub_zero]

/-- `|∇∇G(e, b)| ≤ 1`: the projection does not increase the norm of `1_a`. -/
theorem abs_greenProj_single_le (ω : Configuration d) (a b : LatticeEdge d) :
    |greenProj ω (lp.single 2 a 1) b| ≤ 1 := by
  have h1 := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (greenProj ω (lp.single 2 a 1)) b
  have h2 := norm_greenProj_le ω (lp.single 2 a 1)
  rw [lp.norm_single (by norm_num), norm_one] at h2
  rw [Real.norm_eq_abs] at h1
  linarith

theorem abs_edgeGrad_clusterPot_le (ω : Configuration d) (ξ : EdgeField d) (b : LatticeEdge d) :
    |edgeGrad ω (clusterPot ω ξ) b| ≤ |greenProj ω ξ b| := by
  by_cases hb : EdgeOpen ω b
  · rw [edgeGrad_clusterPot ξ hb]
    split_ifs
    · exact le_rfl
    · rw [abs_zero]
      exact abs_nonneg _
  · simp only [edgeGrad, if_neg hb, abs_zero]
    exact abs_nonneg _


/-- A function with no increment along the open edges based in a set closed under the open edges
is constant along the open walks starting in it. -/
theorem eq_of_walk_of_edge {ω : Configuration d} {S : Set (Vertex d)}
    (hS : ∀ z w, z ∈ S → (openGraph ω).Adj z w → w ∈ S) {F : Vertex d → ℝ}
    (hF : ∀ b : LatticeEdge d, EdgeOpen ω b → b.1 ∈ S → F (edgeHead b) = F b.1)
    {u v : Vertex d} (p : (openGraph ω).Walk u v) (hu : u ∈ S) : F u = F v := by
  induction p with
  | nil => rfl
  | @cons z w t hadj p ih =>
    have hw : w ∈ S := hS z w hu hadj
    refine Eq.trans ?_ (ih hw)
    obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω hadj)
    · have hy : w = z + LatticeProb.unit i := hi
      have hopen : EdgeOpen ω (z, i) := by
        unfold EdgeOpen edgeHead
        rw [← hy]
        exact hadj
      have h1 : F (edgeHead (z, i)) = F z := hF (z, i) hopen hu
      change F (z + LatticeProb.unit i) = F z at h1
      rw [← hy] at h1
      exact h1.symm
    · have hx : z = w + LatticeProb.unit i := by rw [hi]; abel
      have hopen : EdgeOpen ω (w, i) := by
        unfold EdgeOpen edgeHead
        rw [← hx]
        exact hadj.symm
      have h1 : F (edgeHead (w, i)) = F w := hF (w, i) hopen hw
      change F (w + LatticeProb.unit i) = F w at h1
      rw [← hx] at h1
      exact h1

theorem heatComp_smul (c : ℝ) (u : Vertex d → ℝ) (r : ℝ) (x : Vertex d) (j : Fin d) :
    heatComp (fun z => c * u z) r x j = c * heatComp u r x j := by
  unfold heatComp
  rw [← tsum_mul_left]
  exact tsum_congr fun y => by ring


/-- A function whose gradient is at most `L` on every edge changes by at most `L` along every open
edge. -/
theorem abs_sub_le_of_abs_edgeGrad_le {ω : Configuration d} {f : Vertex d → ℝ} {L : ℝ}
    (hf : ∀ b, |edgeGrad ω f b| ≤ L) {u w : Vertex d} (h : (openGraph ω).Adj u w) :
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
along every open edge is at most `2d |S| L`. -/
theorem edgeVariationIn_le_card_mul {ω : Configuration d} (S : Finset (Vertex d))
    {f : Vertex d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ u w, (openGraph ω).Adj u w → |f u - f w| ≤ L) :
    edgeVariationIn ω S f ≤ 2 * d * S.card * L := by
  unfold edgeVariationIn
  have h : ∀ u ∈ S, (∑ w ∈ S, if (openGraph ω).Adj u w then |f u - f w| else 0) ≤
      2 * d * L := by
    intro u _
    have hterm : ∀ w ∈ S, (if (openGraph ω).Adj u w then |f u - f w| else 0) ≤
        if (openGraph ω).Adj u w then L else 0 := by
      intro w _
      split_ifs with huw
      · exact hf u w huw
      · exact le_rfl
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h4 : ((S.filter fun w => (openGraph ω).Adj u w).card : ℝ) ≤ 2 * d := by
      exact_mod_cast card_filter_adj_le ω S u
    nlinarith
  calc _ ≤ ∑ _u ∈ S, 2 * d * L := Finset.sum_le_sum h
    _ = 2 * d * S.card * L := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `⟨P ξ, ξ⟩ = ‖P ξ‖²`. -/
theorem inner_greenProj_self (ω : Configuration d) (ξ : EdgeField d) :
    ⟪greenProj ω ξ, ξ⟫_ℝ = ‖greenProj ω ξ‖ ^ 2 := by
  have hidem : greenProj ω (greenProj ω ξ) = greenProj ω ξ :=
    Submodule.starProjection_eq_self_iff.2 (greenProj_mem ω ξ)
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [← hidem]
  exact inner_greenProj_comm ω _ _

theorem abs_sub_edgeHead_le (a : LatticeEdge d) (i : Fin d) : |a.1 i - edgeHead a i| ≤ 1 := by
  simp only [edgeHead, Pi.add_apply, LatticeProb.unit, Pi.single_apply]
  split_ifs <;> simp


end Rigidity.Corrector.GeneralDim

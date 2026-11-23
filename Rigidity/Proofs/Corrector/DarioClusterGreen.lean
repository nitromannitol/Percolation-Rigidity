import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Rigidity.Proofs.Corrector.DarioPropThreeOne

/-!
# The gradient of the Green function on the open graph (Dario, Propositions 2.11 and 2.12)

Dario's Propositions 2.11 and 2.12 solve `-∇·a∇w_ξ = -∇·ξ` on the infinite cluster for a vector
field `ξ` with `⟨ξ, ξ⟩ < ∞`, by minimising `½⟨∇u, a∇u⟩ - ⟨ξ, ∇u⟩` over the functions of finite
energy ("standard techniques of the calculus of variations"), with the gradient of the Green
function `∇∇G(e, ·)` the solution for `ξ = 1_e`, the bound (2.14) `⟨∇∇G(e,·), ∇∇G(e,·)⟩ ≤ C`, the
symmetry (2.15) and the representation (2.17) `∇w_ξ = Σ_e ξ(e) ∇∇G(e, ·)` ("standard arguments").

For bond percolation the conductances are `0` and `1`, and the minimiser is an orthogonal
projection in the Hilbert space `ℓ²` of the fields on the oriented edges `(z, i)` (from `z` to
`z + e_i`) of `ℤ²`: the projection `greenProj ω` onto the closure `gradSpace ω` of the gradients
of the finitely supported functions on the open graph of `ω`. Here

* `inner_gradDelta`: `⟨η, ∇δ_z⟩ = -(∇·η)(z)`, with `edgeDiv` the net outflow on the open edges;
* `edgeDiv_greenProj`: `-∇·(Pξ) = -∇·ξ` at every vertex (the equation of Proposition 2.12);
* `eq_greenProj_of_edgeDiv_eq`: the solution in `gradSpace ω` is unique;
* `exists_isGradOf_of_mem_gradSpace`: every element of `gradSpace ω` is the gradient of a function
  on the open edges (the potential `w_ξ`), by summing along walks from a root of each component;
* `norm_greenProj_le`: `‖Pξ‖ ≤ ‖ξ‖` ((2.14) with `C = 1` for `ξ = 1_e`);
* `inner_greenProj_comm`: the symmetry (2.15);
* `greenProj_apply_eq_tsum`: the representation (2.17)
  `(Pξ)(e') = Σ_e ξ(e) (P1_e)(e')`.
-/

namespace Rigidity.Corrector

open Filter Topology LatticeProb.Percolation
open scoped InnerProductSpace Classical ENNReal

/-- The oriented edges `(z, i)` of `ℤ²`, from `z` to `z + e_i`. -/
abbrev LatticeEdge := Vertex 2 × Fin 2

/-- The Hilbert space `ℓ²` of the fields on the oriented edges of `ℤ²`. -/
abbrev EdgeField := lp (fun _ : LatticeEdge => ℝ) 2

/-- The head `z + e_i` of the edge `(z, i)`. -/
def edgeHead (a : LatticeEdge) : Vertex 2 := a.1 + LatticeProb.unit a.2

/-- The edge `(z, i)` is open in `ω`. -/
def EdgeOpen (ω : Configuration 2) (a : LatticeEdge) : Prop :=
  (openGraph ω).Adj a.1 (edgeHead a)

variable (ω : Configuration 2)

/-- The gradient `∇u(z, i) = u(z + e_i) - u(z)` on the open edges, `0` on the closed edges. -/
noncomputable def edgeGrad (u : Vertex 2 → ℝ) (a : LatticeEdge) : ℝ :=
  if EdgeOpen ω a then u (edgeHead a) - u a.1 else 0

/-- The divergence (net outflow) `Σ_i (η(z, i) - η(z - e_i, i))` of a field at `z`, over the open
edges. -/
noncomputable def edgeDiv (η : LatticeEdge → ℝ) (z : Vertex 2) : ℝ :=
  ∑ i : Fin 2, ((if EdgeOpen ω (z, i) then η (z, i) else 0) -
    (if EdgeOpen ω (z - LatticeProb.unit i, i) then η (z - LatticeProb.unit i, i) else 0))

/-- The gradient `∇δ_z` of the point mass at `z`, as an element of `ℓ²`. -/
noncomputable def gradDelta (z : Vertex 2) : EdgeField :=
  ∑ i : Fin 2, ((if EdgeOpen ω (z - LatticeProb.unit i, i) then
      lp.single 2 (z - LatticeProb.unit i, i) (1 : ℝ) else 0) -
    (if EdgeOpen ω (z, i) then lp.single 2 (z, i) (1 : ℝ) else 0))

/-- **`⟨η, ∇δ_z⟩ = -(∇·η)(z)`.** -/
theorem inner_gradDelta (η : EdgeField) (z : Vertex 2) :
    ⟪η, gradDelta ω z⟫_ℝ = -edgeDiv ω η z := by
  unfold gradDelta edgeDiv
  rw [inner_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sub_right]
  split_ifs <;> simp [lp.inner_single_right]

/-- The closure in `ℓ²` of the gradients of the finitely supported functions on the open graph. -/
noncomputable def gradSpace : Submodule ℝ EdgeField :=
  (Submodule.span ℝ (Set.range (gradDelta ω))).topologicalClosure

instance : (gradSpace ω).HasOrthogonalProjection := by
  haveI : CompleteSpace (gradSpace ω) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- **The gradient of the solution of `-∇·∇w = -∇·ξ` of finite energy** (Dario, Propositions 2.11
and 2.12): the orthogonal projection onto `gradSpace ω`. -/
noncomputable def greenProj : EdgeField →L[ℝ] EdgeField :=
  (gradSpace ω).starProjection

theorem gradDelta_mem_gradSpace (z : Vertex 2) : gradDelta ω z ∈ gradSpace ω :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨z, rfl⟩)

theorem greenProj_mem (ξ : EdgeField) : greenProj ω ξ ∈ gradSpace ω :=
  (gradSpace ω).starProjection_apply_mem ξ

/-- A field orthogonal to every `∇δ_z` is orthogonal to `gradSpace ω`. -/
theorem inner_eq_zero_of_forall_gradDelta {v : EdgeField} (hv : ∀ z, ⟪v, gradDelta ω z⟫_ℝ = 0)
    {g : EdgeField} (hg : g ∈ gradSpace ω) : ⟪v, g⟫_ℝ = 0 := by
  have hle : Submodule.span ℝ (Set.range (gradDelta ω)) ≤
      LinearMap.ker (innerSL ℝ v : EdgeField →ₗ[ℝ] ℝ) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply]
    exact hv z
  have hcl : gradSpace ω ≤ LinearMap.ker (innerSL ℝ v : EdgeField →ₗ[ℝ] ℝ) :=
    Submodule.topologicalClosure_minimal _ hle (ContinuousLinearMap.isClosed_ker _)
  have := hcl hg
  simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] using this

/-- **The equation of Proposition 2.12**: `-∇·(Pξ) = -∇·ξ` at every vertex. -/
theorem edgeDiv_greenProj (ξ : EdgeField) (z : Vertex 2) :
    edgeDiv ω (greenProj ω ξ) z = edgeDiv ω ξ z := by
  have h := (gradSpace ω).starProjection_inner_eq_zero ξ (gradDelta ω z)
    (gradDelta_mem_gradSpace ω z)
  rw [inner_sub_left, inner_gradDelta, inner_gradDelta] at h
  change -edgeDiv ω ξ z - -edgeDiv ω (greenProj ω ξ) z = 0 at h
  linarith

/-- **Uniqueness**: an element of `gradSpace ω` with the divergence of `ξ` is `Pξ`. -/
theorem eq_greenProj_of_edgeDiv_eq {ξ η : EdgeField} (hη : η ∈ gradSpace ω)
    (hdiv : ∀ z, edgeDiv ω η z = edgeDiv ω ξ z) : η = greenProj ω ξ := by
  set v := η - greenProj ω ξ with hv
  have hvmem : v ∈ gradSpace ω := (gradSpace ω).sub_mem hη (greenProj_mem ω ξ)
  have horth : ∀ z, ⟪v, gradDelta ω z⟫_ℝ = 0 := by
    intro z
    rw [hv, inner_sub_left, inner_gradDelta, inner_gradDelta, hdiv z, edgeDiv_greenProj]
    ring
  have h0 := inner_eq_zero_of_forall_gradDelta ω horth hvmem
  rw [inner_self_eq_zero] at h0
  exact sub_eq_zero.1 h0

/-- **The bound (2.14)**, with constant one: `‖Pξ‖ ≤ ‖ξ‖`. -/
theorem norm_greenProj_le (ξ : EdgeField) : ‖greenProj ω ξ‖ ≤ ‖ξ‖ :=
  (gradSpace ω).norm_starProjection_apply_le ξ

/-- **The symmetry (2.15)**: `⟨Pξ, η⟩ = ⟨ξ, Pη⟩`. -/
theorem inner_greenProj_comm (ξ η : EdgeField) :
    ⟪greenProj ω ξ, η⟫_ℝ = ⟪ξ, greenProj ω η⟫_ℝ :=
  (gradSpace ω).inner_starProjection_left_eq_right ξ η

theorem greenProj_apply_eq_inner (ξ : EdgeField) (a : LatticeEdge) :
    greenProj ω ξ a = ⟪greenProj ω ξ, lp.single 2 a (1 : ℝ)⟫_ℝ := by
  rw [lp.inner_single_right, Real.inner_apply, mul_one]

/-- **The representation formula (2.17)**: `(Pξ)(e') = Σ_e ξ(e) (P1_e)(e')`. -/
theorem greenProj_apply_eq_tsum (ξ : EdgeField) (a : LatticeEdge) :
    greenProj ω ξ a = ∑' b, ξ b * greenProj ω (lp.single 2 b (1 : ℝ)) a := by
  rw [greenProj_apply_eq_inner, inner_greenProj_comm, lp.inner_eq_tsum]
  refine tsum_congr fun b => ?_
  rw [Real.inner_apply, greenProj_apply_eq_inner ω (lp.single 2 a 1) b, inner_greenProj_comm,
    lp.inner_single_left, Real.inner_apply, one_mul]

/-! ### The potential of an element of `gradSpace ω` -/

/-- `η` is the gradient of `w` on the open edges. -/
def IsGradOf (η : LatticeEdge → ℝ) (w : Vertex 2 → ℝ) : Prop :=
  ∀ a, EdgeOpen ω a → η a = w (edgeHead a) - w a.1

/-- The value of an edge field along the step from `x` to a neighbour `y`: `η(x, i)` if
`y = x + e_i`, `-η(y, i)` if `x = y + e_i`. -/
noncomputable def signedVal (η : LatticeEdge → ℝ) (x y : Vertex 2) : ℝ :=
  ∑ i : Fin 2, ((if y = x + LatticeProb.unit i then η (x, i) else 0) -
    (if x = y + LatticeProb.unit i then η (y, i) else 0))

theorem coord_sum_add_unit (x : Vertex 2) (i : Fin 2) :
    ∑ j, (x + LatticeProb.unit i) j = ∑ j, x j + 1 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, LatticeProb.unit, Finset.sum_pi_single',
    Finset.mem_univ, if_true]

theorem add_unit_ne_add_unit {x : Vertex 2} {i j : Fin 2} (h : i ≠ j) :
    x + LatticeProb.unit i ≠ x + LatticeProb.unit j := by
  intro e
  have := congrFun e i
  simp [LatticeProb.unit, h] at this

theorem add_unit_add_unit_ne (x : Vertex 2) (i j : Fin 2) :
    x + LatticeProb.unit i + LatticeProb.unit j ≠ x := by
  intro e
  have := congrArg (fun y : Vertex 2 => ∑ k, y k) e
  simp only [coord_sum_add_unit] at this
  omega

/-- Along an open step the signed value of a gradient is the increment of the potential. -/
theorem signedVal_eq_of_isGradOf {η : LatticeEdge → ℝ} {w : Vertex 2 → ℝ} (h : IsGradOf ω η w)
    {x y : Vertex 2} (hxy : (openGraph ω).Adj x y) : signedVal η x y = w y - w x := by
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω hxy)
  · have hy : y = x + LatticeProb.unit i := hi
    have hopen : EdgeOpen ω (x, i) := by
      unfold EdgeOpen edgeHead
      rw [← hy]
      exact hxy
    have key : ∀ j, ((if y = x + LatticeProb.unit j then η (x, j) else 0) -
        (if x = y + LatticeProb.unit j then η (y, j) else 0)) =
        if j = i then w y - w x else 0 := by
      intro j
      have h2 : ¬ x = y + LatticeProb.unit j := by
        rw [hy]
        exact fun e => add_unit_add_unit_ne x i j e.symm
      rw [if_neg h2, sub_zero]
      by_cases hj : j = i
      · subst hj
        rw [if_pos hy, if_pos rfl, h (x, j) hopen, hy]
        rfl
      · rw [if_neg hj, if_neg]
        rw [hy]
        exact fun e => add_unit_ne_add_unit (Ne.symm hj) e
    unfold signedVal
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_ite_eq' Finset.univ i]
    simp
  · have hx : x = y + LatticeProb.unit i := by rw [hi]; abel
    have hopen : EdgeOpen ω (y, i) := by
      unfold EdgeOpen edgeHead
      rw [← hx]
      exact hxy.symm
    have key : ∀ j, ((if y = x + LatticeProb.unit j then η (x, j) else 0) -
        (if x = y + LatticeProb.unit j then η (y, j) else 0)) =
        if j = i then w y - w x else 0 := by
      intro j
      have h1 : ¬ y = x + LatticeProb.unit j := by
        rw [hx]
        exact fun e => add_unit_add_unit_ne y i j e.symm
      rw [if_neg h1, zero_sub]
      by_cases hj : j = i
      · subst hj
        rw [if_pos hx, if_pos rfl, h (y, j) hopen]
        change -(w (y + LatticeProb.unit j) - w y) = w y - w x
        rw [← hx]
        ring
      · rw [if_neg hj, if_neg, neg_zero]
        rw [hx]
        exact fun e => add_unit_ne_add_unit (Ne.symm hj) e
    unfold signedVal
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_ite_eq' Finset.univ i]
    simp

/-- The sum of an edge field along a walk of the open graph. -/
noncomputable def walkSum (η : LatticeEdge → ℝ) {x y : Vertex 2} (p : (openGraph ω).Walk x y) : ℝ :=
  (p.darts.map fun d => signedVal η d.fst d.snd).sum

/-- Along a walk the sum of a gradient is the increment of the potential. -/
theorem walkSum_eq_of_isGradOf {η : LatticeEdge → ℝ} {w : Vertex 2 → ℝ} (h : IsGradOf ω η w)
    {x y : Vertex 2} (p : (openGraph ω).Walk x y) : walkSum ω η p = w y - w x := by
  induction p with
  | nil => simp [walkSum]
  | cons hadj p ih =>
    unfold walkSum at ih ⊢
    rw [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    have e := signedVal_eq_of_isGradOf ω h hadj
    dsimp only
    rw [e]
    ring

theorem tendsto_signedVal {η : ℕ → LatticeEdge → ℝ} {η₀ : LatticeEdge → ℝ}
    (h : ∀ a, Tendsto (fun n => η n a) atTop (𝓝 (η₀ a))) (x y : Vertex 2) :
    Tendsto (fun n => signedVal (η n) x y) atTop (𝓝 (signedVal η₀ x y)) := by
  unfold signedVal
  refine tendsto_finsetSum _ fun i _ => ?_
  refine Tendsto.sub ?_ ?_
  · split_ifs
    · exact h _
    · exact tendsto_const_nhds
  · split_ifs
    · exact h _
    · exact tendsto_const_nhds

theorem tendsto_walkSum {η : ℕ → LatticeEdge → ℝ} {η₀ : LatticeEdge → ℝ}
    (h : ∀ a, Tendsto (fun n => η n a) atTop (𝓝 (η₀ a))) {x y : Vertex 2}
    (p : (openGraph ω).Walk x y) :
    Tendsto (fun n => walkSum ω (η n) p) atTop (𝓝 (walkSum ω η₀ p)) := by
  induction p with
  | nil => simp [walkSum]
  | cons hadj p ih =>
    unfold walkSum at ih ⊢
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
    exact (tendsto_signedVal h _ _).add ih

theorem gradDelta_apply_of_open (z : Vertex 2) {a : LatticeEdge} (ha : EdgeOpen ω a) :
    gradDelta ω z a = Pi.single (M := fun _ => ℝ) z 1 (edgeHead a) -
      Pi.single (M := fun _ => ℝ) z 1 a.1 := by
  obtain ⟨x, i⟩ := a
  unfold gradDelta
  rw [lp.coeFn_sum, Finset.sum_apply]
  have key : ∀ j : Fin 2, ((((if EdgeOpen ω (z - LatticeProb.unit j, j) then
      lp.single 2 (z - LatticeProb.unit j, j) (1 : ℝ) else 0) -
      (if EdgeOpen ω (z, j) then lp.single 2 (z, j) (1 : ℝ) else 0)) : EdgeField) (x, i)) =
      if j = i then (Pi.single (M := fun _ => ℝ) z 1 (edgeHead (x, i)) -
        Pi.single (M := fun _ => ℝ) z 1 x) else 0 := by
    intro j
    rw [lp.coeFn_sub, Pi.sub_apply]
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      have e1 : ((if EdgeOpen ω (z - LatticeProb.unit j, j) then
          lp.single 2 (z - LatticeProb.unit j, j) (1 : ℝ) else 0 : EdgeField) (x, j)) =
          Pi.single (M := fun _ => ℝ) z 1 (edgeHead (x, j)) := by
        by_cases hx : x = z - LatticeProb.unit j
        · subst hx
          have hh : edgeHead (z - LatticeProb.unit j, j) = z := by
            simp [edgeHead]
          rw [if_pos ha, lp.single_apply, Pi.single_eq_same, hh, Pi.single_eq_same]
        · have hh : edgeHead (x, j) ≠ z := by
            intro e
            apply hx
            rw [← e]
            simp [edgeHead]
          rw [Pi.single_eq_of_ne hh]
          split_ifs
          · rw [lp.single_apply, Pi.single_eq_of_ne]
            intro e
            exact hx (Prod.mk.inj e).1
          · rfl
      have e2 : ((if EdgeOpen ω (z, j) then lp.single 2 (z, j) (1 : ℝ) else 0 : EdgeField)
          (x, j)) = Pi.single (M := fun _ => ℝ) z 1 x := by
        by_cases hx : x = z
        · subst hx
          rw [if_pos ha, lp.single_apply, Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hx]
          split_ifs
          · rw [lp.single_apply, Pi.single_eq_of_ne]
            intro e
            exact hx (Prod.mk.inj e).1
          · rfl
      rw [e1, e2]
    · rw [if_neg hj]
      have e1 : ((if EdgeOpen ω (z - LatticeProb.unit j, j) then
          lp.single 2 (z - LatticeProb.unit j, j) (1 : ℝ) else 0 : EdgeField) (x, i)) = 0 := by
        split_ifs
        · rw [lp.single_apply, Pi.single_eq_of_ne]
          intro e
          exact hj (Prod.mk.inj e).2.symm
        · rfl
      have e2 : ((if EdgeOpen ω (z, j) then lp.single 2 (z, j) (1 : ℝ) else 0 : EdgeField)
          (x, i)) = 0 := by
        split_ifs
        · rw [lp.single_apply, Pi.single_eq_of_ne]
          intro e
          exact hj (Prod.mk.inj e).2.symm
        · rfl
      rw [e1, e2, sub_zero]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_ite_eq' Finset.univ i]
  simp

theorem isGradOf_gradDelta (z : Vertex 2) :
    IsGradOf ω (gradDelta ω z) (Pi.single (M := fun _ => ℝ) z 1) :=
  fun _ ha => gradDelta_apply_of_open ω z ha

theorem exists_isGradOf_of_mem_span {η : EdgeField}
    (hη : η ∈ Submodule.span ℝ (Set.range (gradDelta ω))) : ∃ w, IsGradOf ω η w := by
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    exact ⟨_, isGradOf_gradDelta ω z⟩
  | zero => exact ⟨0, fun a _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w₁, h₁⟩ := hx
    obtain ⟨w₂, h₂⟩ := hy
    refine ⟨w₁ + w₂, fun a ha => ?_⟩
    rw [lp.coeFn_add, Pi.add_apply, h₁ a ha, h₂ a ha, Pi.add_apply, Pi.add_apply]
    ring
  | smul c x _ hx =>
    obtain ⟨w, h⟩ := hx
    refine ⟨c • w, fun a ha => ?_⟩
    rw [lp.coeFn_smul, Pi.smul_apply, h a ha, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    ring

/-- A root of the component of `x` in the open graph. -/
noncomputable def componentRoot (x : Vertex 2) : Vertex 2 :=
  Quot.out ((openGraph ω).connectedComponentMk x)

theorem reachable_componentRoot (x : Vertex 2) :
    (openGraph ω).Reachable (componentRoot ω x) x :=
  SimpleGraph.ConnectedComponent.exact (Quot.out_eq ((openGraph ω).connectedComponentMk x))

theorem componentRoot_eq_of_adj {x y : Vertex 2} (h : (openGraph ω).Adj x y) :
    componentRoot ω y = componentRoot ω x := by
  unfold componentRoot
  rw [SimpleGraph.ConnectedComponent.eq.2 h.reachable]

/-- **The potential**: every element of `gradSpace ω` is the gradient of a function on the open
edges. -/
theorem exists_isGradOf_of_mem_gradSpace {η : EdgeField} (hη : η ∈ gradSpace ω) :
    ∃ w, IsGradOf ω η w := by
  have hcl : η ∈ closure (Submodule.span ℝ (Set.range (gradDelta ω)) : Set EdgeField) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hη
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  choose w hw using fun n => exists_isGradOf_of_mem_span ω (hu n)
  have hcoord : ∀ a, Tendsto (fun n => (u n : LatticeEdge → ℝ) a) atTop (𝓝 (η a)) := by
    intro a
    rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (u n - η) a
    simpa only [lp.coeFn_sub, Pi.sub_apply] using this
  let walk : ∀ x, (openGraph ω).Walk (componentRoot ω x) x := fun x =>
    (reachable_componentRoot ω x).some
  refine ⟨fun x => walkSum ω η (walk x), fun a ha => ?_⟩
  have hroot := componentRoot_eq_of_adj ω ha
  have happrox : ∀ n, (u n : LatticeEdge → ℝ) a =
      walkSum ω (u n) (walk (edgeHead a)) - walkSum ω (u n) (walk a.1) := by
    intro n
    rw [walkSum_eq_of_isGradOf ω (hw n), walkSum_eq_of_isGradOf ω (hw n), hroot, hw n a ha]
    ring
  have hlim2 : Tendsto (fun n => walkSum ω (u n) (walk (edgeHead a)) -
      walkSum ω (u n) (walk a.1)) atTop
      (𝓝 (walkSum ω η (walk (edgeHead a)) - walkSum ω η (walk a.1))) :=
    (tendsto_walkSum ω hcoord _).sub (tendsto_walkSum ω hcoord _)
  have hlim1 := hcoord a
  simp_rw [happrox] at hlim1
  exact tendsto_nhds_unique hlim1 hlim2

/-- **The potential `w_ξ` of Proposition 2.12**: `Pξ` is the gradient of a function on the open
edges. -/
theorem exists_isGradOf_greenProj (ξ : EdgeField) : ∃ w, IsGradOf ω (greenProj ω ξ) w :=
  exists_isGradOf_of_mem_gradSpace ω (greenProj_mem ω ξ)

end Rigidity.Corrector

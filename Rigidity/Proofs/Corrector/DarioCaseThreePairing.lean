import Rigidity.Proofs.Corrector.DarioCaseThreeCorrector

/-!
# The heat average of the coarsened change of the corrector (Dario, Step 2, after (3.28))

With `γ = coarseHeatField` of (3.26) and `∇∇G(e, ·) = greenProj ω (1_a)`, Dario writes
`Φ_{r²} * ∇[χ_p - χ_p^e]_𝒫(0) = ⟨γ_r, ∇(χ_p - χ_p^e)⟩ = c ⟨γ_r, ∇∇G(e, ·)⟩ = c (w_γ(x) - w_γ(y))`
by (3.26), (3.22) and Proposition 2.12 with the symmetry (2.15). Here `w_γ(x) - w_γ(y)` is the value
`(greenProj ω γ)(a)` of the projection of `γ` at the edge `a` from `x` to `y`:

* `pathField_apply_ne_zero`: the field of a walk lives on its open edges;
* `coarseHeatField_apply_ne_zero`: `γ` lives on the open edges of the infinite cluster;
* `heatComp_coarse_eq_smul_greenProj`: if `∇v = c P1_a` on the open edges of the cluster and
  `∇v = 0` on the other open edges, then `Φ_{r²} * ∇_j[v]_𝒫(x) = c (Pγ)(a)`;
* `ae_heatComp_coarse_sub_eq_smul_greenProj`: with (3.22) for the corrected planes
  (`ae_correctedPlane_sub_eq_smul_greenProj`), the Case 3 identity
  `Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_𝒫(x) = (ℓ₀(x) - ℓ₀(y)) (Pγ)(a)` for `ω^{e,1}`;
* `abs_sub_le_two_mul_edgeVariation`: the factor `ℓ₀(x) - ℓ₀(y)` is bounded by total variations
  over the partition squares at `x` and `y` (the form of (3.24) used here).
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped InnerProductSpace Classical

variable (ω : Configuration 2)

theorem dartField_apply_ne_zero {u v : Vertex 2} (h : (openGraph ω).Adj u v) {b : LatticeEdge}
    (hb : dartField u v b ≠ 0) : EdgeOpen ω b ∧ (b.1 = u ∨ b.1 = v) := by
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω h)
  · subst hi
    rw [dartField_add_unit, lp.single_apply] at hb
    by_cases hbe : b = (u, i)
    · subst hbe
      exact ⟨h, Or.inl rfl⟩
    · exact absurd (Pi.single_eq_of_ne hbe _) hb
  · have hx : u = v + LatticeProb.unit i := by rw [hi]; abel
    subst hx
    rw [dartField_unit_add, lp.coeFn_neg, Pi.neg_apply, lp.single_apply, neg_ne_zero] at hb
    by_cases hbe : b = (v, i)
    · subst hbe
      exact ⟨h.symm, Or.inr rfl⟩
    · exact absurd (Pi.single_eq_of_ne hbe _) hb

/-- The field of a walk lives on its open edges, with tails on the walk. -/
theorem pathField_apply_ne_zero {x y : Vertex 2} (p : (openGraph ω).Walk x y) {b : LatticeEdge}
    (hb : pathField ω p b ≠ 0) : EdgeOpen ω b ∧ b.1 ∈ p.support := by
  induction p with
  | nil => simp [pathField] at hb
  | @cons u v w hadj p ih =>
    unfold pathField at hb ih
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, lp.coeFn_add,
      Pi.add_apply] at hb
    rw [SimpleGraph.Walk.support_cons, List.mem_cons]
    by_cases h1 : dartField u v b = 0
    · rw [h1, zero_add] at hb
      obtain ⟨ho, hm⟩ := ih hb
      exact ⟨ho, Or.inr hm⟩
    · obtain ⟨ho, hm | hm⟩ := dartField_apply_ne_zero ω hadj h1
      · exact ⟨ho, Or.inl hm⟩
      · exact ⟨ho, Or.inr (hm ▸ p.start_mem_support)⟩

/-- **`γ` lives on the open edges of the infinite cluster.** -/
theorem coarseHeatField_apply_ne_zero {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {r : ℝ} {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card)
    {b : LatticeEdge} (hb : coarseHeatField hP r x j b ≠ 0) :
    EdgeOpen ω b ∧ ((openGraph ω).connectedComponentMk b.1).supp.Infinite := by
  rw [coarseHeatField_apply hP hS b] at hb
  obtain ⟨z, hz⟩ : ∃ z, latticeHeat (r ^ 2) x z *
      pathField ω (coarseStepWalk hP z j) b ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hb (by simp [hall])
  have hz' : pathField ω (coarseStepWalk hP z j) b ≠ 0 := right_ne_zero_of_mul hz
  obtain ⟨ho, hm⟩ := pathField_apply_ne_zero ω _ hz'
  refine ⟨ho, ?_⟩
  have hreach : (openGraph ω).Reachable (planarCoarseAnchor ω z) b.1 :=
    ⟨(coarseStepWalk hP z j).takeUntil b.1 hm⟩
  have hinf := infinite_planarCoarseAnchor hP z
  change ((openGraph ω).connectedComponentMk (planarCoarseAnchor ω z)).supp.Infinite at hinf
  rwa [SimpleGraph.ConnectedComponent.sound hreach] at hinf

/-- **The pairing of (3.26) with (3.22)**, for a source `ξ`: if `∇v = c Pξ` on the open edges of
the infinite cluster and `∇v = 0` on the other open edges, then
`Φ_{r²} * ∇_j[v]_𝒫(x) = c ⟨ξ, Pγ⟩`. -/
theorem heatComp_coarse_eq_smul_inner_greenProj {ω : Configuration 2}
    (hP : PlanarPartitionEvent ω) {r : ℝ} {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card)
    {v : Vertex 2 → ℝ} {c : ℝ} {ξ : EdgeField}
    (hv : ∀ b, EdgeOpen ω b → ((openGraph ω).connectedComponentMk b.1).supp.Infinite →
      edgeGrad ω v b = c * greenProj ω ξ b)
    (hv0 : ∀ b, EdgeOpen ω b → ¬ ((openGraph ω).connectedComponentMk b.1).supp.Infinite →
      edgeGrad ω v b = 0) :
    heatComp (fun z => v (planarCoarseAnchor ω z)) r x j =
      c * ⟪ξ, greenProj ω (coarseHeatField hP r x j)⟫_ℝ := by
  set g : EdgeField := greenProj ω ξ with hg
  have hle : ∀ b, |edgeGrad ω v b| ≤ |c| * |g b| := by
    intro b
    by_cases ho : EdgeOpen ω b
    · by_cases hinf : ((openGraph ω).connectedComponentMk b.1).supp.Infinite
      · rw [hv b ho hinf, abs_mul]
      · rw [hv0 b ho hinf, abs_zero]
        positivity
    · simp only [edgeGrad, if_neg ho, abs_zero]
      positivity
  have hmem : Memℓp (edgeGrad ω v) 2 := by
    refine memℓp_gen' (C := c ^ 2 * ‖g‖ ^ 2) fun s => ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    calc ∑ b ∈ s, edgeGrad ω v b ^ 2 ≤ ∑ b ∈ s, c ^ 2 * g b ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h := hle b
          rw [← sq_abs (edgeGrad ω v b), ← sq_abs c, ← sq_abs (g b), ← mul_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = c ^ 2 * ∑ b ∈ s, g b ^ 2 := by rw [Finset.mul_sum]
      _ ≤ c ^ 2 * ‖g‖ ^ 2 := mul_le_mul_of_nonneg_left (sum_sq_le_norm_sq g s) (sq_nonneg c)
  rw [heatComp_coarse_eq_inner hP hmem hS]
  have heq : ⟪(⟨edgeGrad ω v, hmem⟩ : EdgeField), coarseHeatField hP r x j⟫_ℝ =
      ⟪c • g, coarseHeatField hP r x j⟫_ℝ := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun b => ?_
    by_cases hb : coarseHeatField hP r x j b = 0
    · rw [hb, inner_zero_right, inner_zero_right]
    · obtain ⟨ho, hinf⟩ := coarseHeatField_apply_ne_zero hP hS hb
      congr 1
      change edgeGrad ω v b = (c • g) b
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hv b ho hinf]
  rw [heq, real_inner_smul_left, hg, inner_greenProj_comm]

/-- **The pairing of (3.26) with (3.22)**, for an open edge `a`:
`Φ_{r²} * ∇_j[v]_𝒫(x) = c (Pγ)(a)`. -/
theorem heatComp_coarse_eq_smul_greenProj {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {r : ℝ} {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card)
    {v : Vertex 2 → ℝ} {c : ℝ} {a : LatticeEdge}
    (hv : ∀ b, EdgeOpen ω b → ((openGraph ω).connectedComponentMk b.1).supp.Infinite →
      edgeGrad ω v b = c * greenProj ω (lp.single 2 a 1) b)
    (hv0 : ∀ b, EdgeOpen ω b → ¬ ((openGraph ω).connectedComponentMk b.1).supp.Infinite →
      edgeGrad ω v b = 0) :
    heatComp (fun z => v (planarCoarseAnchor ω z)) r x j =
      c * greenProj ω (coarseHeatField hP r x j) a := by
  rw [heatComp_coarse_eq_smul_inner_greenProj hP hS hv hv0, lp.inner_single_left,
    Real.inner_apply, one_mul]

theorem extendComp_of_not_mem {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ)
    {z : Vertex 2} (h : z ∉ C.supp) : extendComp C u z = 0 := by
  simp [extendComp, h]

/-- **Case 3 of Step 2**: almost surely, with the bond `e` of `a = (x, i)` opened and closed and
`x, y` in the infinite cluster of `ω^{e,0}`, the heat average of the coarsened change of the
corrected planes is `Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_𝒫(x) = (ℓ₀(x) - ℓ₀(y)) (Pγ)(a)` for `ω^{e,1}`. -/
theorem ae_heatComp_coarse_sub_eq_smul_greenProj {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ a : LatticeEdge,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
        (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
        (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp)
        (q : Fin 2 → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
        (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
        IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
        IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
        ∀ (hP : PlanarPartitionEvent (setBond (edgeBond a) true ω)) (r : ℝ) (x : Vertex 2)
          (j : Fin 2), Summable (fun z => latticeHeat (r ^ 2) x z *
            (stepRegion (setBond (edgeBond a) true ω) z j).card) →
          heatComp (fun z => extendComp _ ℓ₁ (planarCoarseAnchor (setBond (edgeBond a) true ω) z) -
              extendComp _ ℓ₀ (planarCoarseAnchor (setBond (edgeBond a) true ω) z)) r x j =
            (ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) *
              greenProj (setBond (edgeBond a) true ω) (coarseHeatField hP r x j) a := by
  filter_upwards [ae_correctedPlane_sub_eq_smul_greenProj hpc hp1] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ hP r x j hS
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  refine heatComp_coarse_eq_smul_greenProj (v := fun z => extendComp _ ℓ₁ z - extendComp _ ℓ₀ z)
    (c := ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) (a := a) hP hS (fun b hb hinf => ?_)
    (fun b hb hinf => ?_)
  · have hb1 : b.1 ∈ (uniqueInfiniteComponent h₁).supp :=
      (mem_uniqueInfiniteComponent_iff h₁ b.1).2 hinf
    have key := hω a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ b hb hb1
    simp only [edgeGrad, if_pos hb]
    rw [← key]
    ring
  · have hb1 : b.1 ∉ (uniqueInfiniteComponent h₁).supp := fun h =>
      hinf ((mem_uniqueInfiniteComponent_iff h₁ b.1).1 h)
    have hb2 : edgeHead b ∉ (uniqueInfiniteComponent h₁).supp := fun h =>
      hb1 ((uniqueInfiniteComponent h₁).mem_supp_of_adj_mem_supp h hb.symm)
    simp only [edgeGrad, if_pos hb]
    rw [extendComp_of_not_mem _ _ hb1, extendComp_of_not_mem _ _ hb2,
      extendComp_of_not_mem _ _ (fun h => hb1 ((hC _).2 h)),
      extendComp_of_not_mem _ _ (fun h => hb2 ((hC _).2 h))]
    ring

/-- **The increment across a bond, by coarsening** (the form of Dario's (3.24) used here): for
neighbours `x, y` of the infinite cluster, `|w(x) - w(y)|` is at most twice the total variations of
`w` over the squares of side `9s` around their partition cubes. With `ω = ω^{e,0}` and
`w = ℓ₀` this bounds the factor `ℓ₀(x) - ℓ₀(y)` of Case 3 by the partition of `ω^{e,0}` alone,
without Lemma 3.5. -/
theorem abs_sub_le_two_mul_edgeVariation {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x y : Vertex 2} (hnear : ∀ i, |x i - y i| ≤ 1)
    (hx : ((openGraph ω).connectedComponentMk x).supp.Infinite)
    (hy : ((openGraph ω).connectedComponentMk y).supp.Infinite) (w : Vertex 2 → ℝ) :
    |w x - w y| ≤
      2 * (edgeVariationIn ω (cubeRegion ω x) w + edgeVariationIn ω (cubeRegion ω y) w) := by
  have h1 := abs_sub_coarseAnchor_le hP hx w
  have h2 := abs_coarseAnchor_sub_le_add hP hnear w
  have h3 := abs_sub_coarseAnchor_le hP hy w
  have t1 := abs_sub_le (w x) (w (planarCoarseAnchor ω x)) (w y)
  have t2 := abs_sub_le (w (planarCoarseAnchor ω x)) (w (planarCoarseAnchor ω y)) (w y)
  have e3 := abs_sub_comm (w (planarCoarseAnchor ω y)) (w y)
  unfold cubeRegion at h2 ⊢
  linarith

end Rigidity.Corrector

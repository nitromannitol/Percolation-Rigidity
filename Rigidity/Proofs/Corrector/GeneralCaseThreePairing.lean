import Rigidity.Proofs.Corrector.GeneralCaseHeatField
import Rigidity.Proofs.Corrector.GeneralCaseFiniteEnergy
import Rigidity.Proofs.Corrector.GeneralCaseThree

/-!
# The heat average of the coarsened change of the corrector on `ℤᵈ` (Dario, Step 2, after (3.28))

With `γ = coarseHeatField` of (3.26) and `∇∇G(e, ·) = greenProj ω (1_a)`, Dario writes
`Φ_{r²} * ∇[χ_p - χ_p^e]_𝒫(0) = ⟨γ_r, ∇(χ_p - χ_p^e)⟩ = c ⟨γ_r, ∇∇G(e, ·)⟩ = c (w_γ(x) - w_γ(y))`
by (3.26), (3.22) and Proposition 2.12 with the symmetry (2.15). Here `w_γ(x) - w_γ(y)` is the value
`(greenProj ω γ)(a)` of the projection of `γ` at the edge `a` from `x` to `y` (the deterministic part
of the planar file `DarioCaseThreePairing`, for the partition into good cubes of `ℤᵈ`):

* `pathField_apply_ne_zero`: the field of a walk lives on its open edges;
* `coarseHeatField_apply_ne_zero`: `γ` lives on the open edges of the infinite cluster;
* `heatComp_coarse_eq_smul_greenProj`: if `∇v = c P1_a` on the open edges of the cluster and
  `∇v = 0` on the other open edges, then `Φ_{r²} * ∇_j[v]_𝒫(x) = c (Pγ)(a)`;
* `abs_sub_le_two_mul_edgeVariation`: for lattice neighbours `x, y` of the infinite cluster,
  `|w(x) - w(y)|` is at most twice the total variations of `w` over the boxes `anchorBox` around
  `x` and `y` (the form of (3.24) used here).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped InnerProductSpace Classical
open Rigidity.Poincare.GeneralDim (zdHeat zdHeat_nonneg)

variable {d : ℕ} (ω : Configuration d)

theorem dartField_apply_ne_zero {u v : Vertex d} (h : (openGraph ω).Adj u v) {b : LatticeEdge d}
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
theorem pathField_apply_ne_zero {x y : Vertex d} (p : (openGraph ω).Walk x y) {b : LatticeEdge d}
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
theorem coarseHeatField_apply_ne_zero [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    {r : ℝ} {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card)
    {b : LatticeEdge d} (hb : coarseHeatField hP r x j b ≠ 0) :
    EdgeOpen ω b ∧ ((openGraph ω).connectedComponentMk b.1).supp.Infinite := by
  rw [coarseHeatField_apply hP hS b] at hb
  obtain ⟨z, hz⟩ : ∃ z, zdHeat d (r ^ 2) x z *
      pathField ω (coarseStepWalk hP z j) b ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hb (by simp [hall])
  have hz' : pathField ω (coarseStepWalk hP z j) b ≠ 0 := right_ne_zero_of_mul hz
  obtain ⟨ho, hm⟩ := pathField_apply_ne_zero ω _ hz'
  refine ⟨ho, ?_⟩
  have hreach : (openGraph ω).Reachable (partitionAnchor ω z) b.1 :=
    ⟨(coarseStepWalk hP z j).takeUntil b.1 hm⟩
  have hinf := infinite_partitionAnchor (Nat.pos_of_ne_zero (NeZero.ne d)) hP z
  change ((openGraph ω).connectedComponentMk (partitionAnchor ω z)).supp.Infinite at hinf
  rwa [SimpleGraph.ConnectedComponent.sound hreach] at hinf

/-- **The pairing of (3.26) with (3.22)**, for a source `ξ`: if `∇v = c Pξ` on the open edges of
the infinite cluster and `∇v = 0` on the other open edges, then
`Φ_{r²} * ∇_j[v]_𝒫(x) = c ⟨ξ, Pγ⟩`. -/
theorem heatComp_coarse_eq_smul_inner_greenProj [NeZero d] {ω : Configuration d}
    (hP : PartitionEvent ω) {r : ℝ} {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card)
    {v : Vertex d → ℝ} {c : ℝ} {ξ : EdgeField d}
    (hv : ∀ b, EdgeOpen ω b → ((openGraph ω).connectedComponentMk b.1).supp.Infinite →
      edgeGrad ω v b = c * greenProj ω ξ b)
    (hv0 : ∀ b, EdgeOpen ω b → ¬ ((openGraph ω).connectedComponentMk b.1).supp.Infinite →
      edgeGrad ω v b = 0) :
    heatComp (fun z => v (partitionAnchor ω z)) r x j =
      c * ⟪ξ, greenProj ω (coarseHeatField hP r x j)⟫_ℝ := by
  set g : EdgeField d := greenProj ω ξ with hg
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
  have heq : ⟪(⟨edgeGrad ω v, hmem⟩ : EdgeField d), coarseHeatField hP r x j⟫_ℝ =
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
theorem heatComp_coarse_eq_smul_greenProj [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    {r : ℝ} {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card)
    {v : Vertex d → ℝ} {c : ℝ} {a : LatticeEdge d}
    (hv : ∀ b, EdgeOpen ω b → ((openGraph ω).connectedComponentMk b.1).supp.Infinite →
      edgeGrad ω v b = c * greenProj ω (lp.single 2 a 1) b)
    (hv0 : ∀ b, EdgeOpen ω b → ¬ ((openGraph ω).connectedComponentMk b.1).supp.Infinite →
      edgeGrad ω v b = 0) :
    heatComp (fun z => v (partitionAnchor ω z)) r x j =
      c * greenProj ω (coarseHeatField hP r x j) a := by
  rw [heatComp_coarse_eq_smul_inner_greenProj hP hS hv hv0, lp.inner_single_left,
    Real.inner_apply, one_mul]

/-- The partition cube of a lattice neighbour of `x` lies in the box `anchorBox ω x`. -/
theorem mem_anchorBox_of_mem_partitionCube_near {ω : Configuration d} (hP : PartitionEvent ω)
    {x y w : Vertex d} (hnear : ∀ i, |x i - y i| ≤ 1) (hw : w ∈ (partitionCube ω y).vertices) :
    w ∈ anchorBox ω x := by
  rw [mem_anchorBox]
  intro i
  have hsc := (partitionCube_scales_close hP hnear).2
  have h1 := abs_sub_le_of_mem_partitionCube hP hw (s := 3 ^ (partitionCube ω y).scale) le_rfl i
  have h3 : (3 : ℤ) ^ (partitionCube ω y).scale ≤ 3 ^ ((partitionCube ω x).scale + 1) :=
    pow_le_pow_right₀ (by norm_num) hsc
  have h4 := hnear i
  have h5 : |w i - x i| ≤ |w i - y i| + |x i - y i| := by
    rw [abs_sub_comm (x i)]
    exact abs_sub_le _ _ _
  push_cast at h1 ⊢
  linarith

/-- **The increment across a bond, by coarsening** (the form of Dario's (3.24) used here): for
lattice neighbours `x, y` of the infinite cluster, `|w(x) - w(y)|` is at most twice the total
variations of `w` over the boxes `anchorBox` around them. -/
theorem abs_sub_le_two_mul_edgeVariation [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    {x y : Vertex d} (hxy : (nearestNeighborGraph d).Adj x y)
    (hx : ω ∈ infiniteComponentEvent x) (hy : ω ∈ infiniteComponentEvent y) (w : Vertex d → ℝ) :
    |w x - w y| ≤
      2 * (edgeVariationIn ω (anchorBox ω x) w + edgeVariationIn ω (anchorBox ω y) w) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hnear := abs_sub_le_one_of_adj_lattice hxy
  have h1 := abs_sub_le_edgeVariationIn_of_reachable _ w (reachable_anchorBox hd hP hx)
  have h3 := abs_sub_le_edgeVariationIn_of_reachable _ w (reachable_anchorBox hd hP hy)
  have h2 : |w (partitionAnchor ω x) - w (partitionAnchor ω y)| ≤
      edgeVariationIn ω (anchorBox ω x) w := by
    refine abs_sub_le_edgeVariationIn_of_reachable _ w
      (Rigidity.Percolation.openIn_reachable_mono_region ?_
        (reachable_partitionAnchor_of_adj hd hP hxy))
    intro z hz
    rw [Finset.mem_coe]
    rcases hz with hz | hz
    · exact mem_anchorBox_of_mem_partitionCube_near hP (fun i => by simp) hz
    · exact mem_anchorBox_of_mem_partitionCube_near hP hnear hz
  have t1 := abs_sub_le (w x) (w (partitionAnchor ω x)) (w y)
  have t2 := abs_sub_le (w (partitionAnchor ω x)) (w (partitionAnchor ω y)) (w y)
  have e3 := abs_sub_comm (w (partitionAnchor ω y)) (w y)
  have h0y := edgeVariationIn_nonneg ω (anchorBox ω y) w
  linarith

end Rigidity.Corrector.GeneralDim

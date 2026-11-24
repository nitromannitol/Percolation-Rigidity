import Rigidity.Proofs.Corrector.DarioCellSum

/-!
# The potential of a projected field on the cluster

For an `ℓ²` field `ξ` on the edges and `v` the potential of `P_ω ξ` on the infinite cluster
(`clusterPot`):

* `openLaplacian_clusterPot`: `∇·∇v = ∇·ξ` at every vertex of the infinite cluster (the equation of
  Proposition 2.12 of Dario, `edgeDiv_greenProj`), the hypothesis of the Meyers estimate with a
  source;
* `tsum_clusterOpenEnergy_le`: `Σ_z E_v(z) ≤ 2 Σ_z Γ(z)`, `Γ(z) = Σ_i ξ(z, i)²`: the energy of `v`
  counts every edge twice and `‖P_ω ξ‖ ≤ ‖ξ‖`.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
open scoped Classical ENNReal InnerProductSpace

variable {ω : Configuration 2}

theorem edgeGrad_clusterPot_eq_of_mem (ξ : EdgeField) {b : LatticeEdge} (hb : EdgeOpen ω b)
    (hinf : ω ∈ infiniteComponentEvent b.1) :
    edgeGrad ω (clusterPot ω ξ) b = greenProj ω ξ b := by
  rw [edgeGrad_clusterPot ξ hb, if_pos hinf]

/-- **The equation for the potential of a projected field**: `∇·∇v = ∇·ξ` on the cluster. -/
theorem openLaplacian_clusterPot (ξ : EdgeField) {z : Vertex 2}
    (hz : ω ∈ infiniteComponentEvent z) : openLaplacian ω (clusterPot ω ξ) z = edgeDiv ω ξ z := by
  rw [openLaplacian_eq_edgeDiv, ← edgeDiv_greenProj ω ξ z]
  unfold edgeDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  · split_ifs with h
    · exact edgeGrad_clusterPot_eq_of_mem ξ h hz
    · rfl
  · split_ifs with h
    · refine edgeGrad_clusterPot_eq_of_mem ξ h ?_
      have hz' : ω ∈ infiniteComponentEvent (edgeHead (z - LatticeProb.unit i, i)) := by
        change ω ∈ infiniteComponentEvent (z - LatticeProb.unit i + LatticeProb.unit i)
        rw [sub_add_cancel]
        exact hz
      exact (infiniteComponentEvent_iff_of_adj h).2 hz'
    · rfl

/-- Off the infinite cluster the potential has no energy. -/
theorem openEnergy_clusterPot_eq (ξ : EdgeField) (z : Vertex 2) :
    openEnergy ω (clusterPot ω ξ) z = clusterOpenEnergy ω (clusterPot ω ξ) z := by
  unfold clusterOpenEnergy
  split_ifs with hz
  · rfl
  · unfold openEnergy
    refine Finset.sum_eq_zero fun w hw => ?_
    have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hw
    have hw' : ω ∉ infiniteComponentEvent w := fun h =>
      hz ((infiniteComponentEvent_iff_of_adj hadj).2 h)
    unfold clusterPot
    rw [if_neg hz, if_neg hw']
    ring

/-- The energy at a vertex through the gradients on the four lattice edges at it. -/
theorem openEnergy_le_sum_edgeGrad (f : Vertex 2 → ℝ) (z : Vertex 2) :
    openEnergy ω f z ≤ ∑ k : Fin 2, (edgeGrad ω f (z, k) ^ 2 +
      edgeGrad ω f (z - LatticeProb.unit k, k) ^ 2) := by
  set φ : Fin 2 × Bool → Vertex 2 := fun q =>
    if q.2 then z + LatticeProb.unit q.1 else z - LatticeProb.unit q.1 with hφ
  set h : Vertex 2 → ℝ := fun w => if (openGraph ω).Adj z w then (f z - f w) ^ 2 else 0 with hh
  have hh0 : ∀ w, 0 ≤ h w := fun w => by simp only [hh]; split_ifs <;> positivity
  have hsub : (openGraph ω).neighborFinset z ⊆ Finset.image φ Finset.univ := by
    intro w hw
    have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hw
    obtain ⟨k, hk | hk⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω hadj)
    · exact Finset.mem_image.2 ⟨(k, true), Finset.mem_univ _, by simp [hφ, hk]⟩
    · exact Finset.mem_image.2 ⟨(k, false), Finset.mem_univ _, by simp [hφ, hk]⟩
  have h1 : openEnergy ω f z = ∑ w ∈ (openGraph ω).neighborFinset z, h w := by
    unfold openEnergy
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hh]; beta_reduce
    rw [if_pos ((SimpleGraph.mem_neighborFinset _ _ _).1 hw)]
  rw [h1]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => hh0 w).trans ?_
  refine (Finset.sum_image_le_of_nonneg fun w _ => hh0 w).trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Fintype.sum_bool]
  simp only [hφ, if_true, Bool.false_eq_true, if_false]
  refine add_le_add ?_ ?_
  · simp only [hh]
    split_ifs with hadj
    · have hopen : EdgeOpen ω (z, k) := hadj
      simp only [edgeGrad, if_pos hopen, edgeHead]
      ring_nf
      exact le_rfl
    · exact sq_nonneg _
  · simp only [hh]
    split_ifs with hadj
    · have hopen : EdgeOpen ω (z - LatticeProb.unit k, k) := by
        unfold EdgeOpen edgeHead
        rw [sub_add_cancel]
        exact hadj.symm
      simp only [edgeGrad, if_pos hopen, edgeHead, sub_add_cancel]
      exact le_rfl
    · exact sq_nonneg _

/-- `Σ_b ξ(b)² = ‖ξ‖²` in `ℝ≥0∞`. -/
theorem tsum_ofReal_sq_eq (ξ : EdgeField) :
    ∑' b, ENNReal.ofReal (ξ b ^ 2) = ENNReal.ofReal (‖ξ‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum,
    ENNReal.ofReal_tsum_of_nonneg
      (fun b => by simp only [Real.inner_apply]; exact mul_self_nonneg _)
      (lp.summable_inner ξ ξ)]
  refine tsum_congr fun b => ?_
  simp only [Real.inner_apply, sq]

/-- **The energy of the potential of a projected field**: `Σ_z E_v(z) ≤ 2 Σ_z Γ(z)`. -/
theorem tsum_clusterOpenEnergy_le (ξ : EdgeField) :
    ∑' z, ENNReal.ofReal (clusterOpenEnergy ω (clusterPot ω ξ) z) ≤
      2 * ∑' z, ENNReal.ofReal (edgeSq ξ z) := by
  set v := clusterPot ω ξ with hv
  have hgrad : ∀ b, edgeGrad ω v b ^ 2 ≤ greenProj ω ξ b ^ 2 := fun b => by
    rw [← sq_abs, ← sq_abs (greenProj ω ξ b)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_edgeGrad_clusterPot_le ω ξ b) 2
  have hpt : ∀ z, ENNReal.ofReal (clusterOpenEnergy ω v z) ≤
      ∑ k : Fin 2, (ENNReal.ofReal (edgeGrad ω v (z, k) ^ 2) +
        ENNReal.ofReal (edgeGrad ω v (z - LatticeProb.unit k, k) ^ 2)) := by
    intro z
    rw [← openEnergy_clusterPot_eq]
    refine (ENNReal.ofReal_le_ofReal (openEnergy_le_sum_edgeGrad v z)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
    exact Finset.sum_congr rfl fun k _ => ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  simp only [ENNReal.tsum_add]
  have hshift : ∀ k : Fin 2, ∑' z, ENNReal.ofReal (edgeGrad ω v (z - LatticeProb.unit k, k) ^ 2) =
      ∑' z, ENNReal.ofReal (edgeGrad ω v (z, k) ^ 2) := fun k =>
    (Equiv.subRight (LatticeProb.unit k)).tsum_eq fun z => ENNReal.ofReal (edgeGrad ω v (z, k) ^ 2)
  simp only [hshift, ← two_mul]
  rw [← Finset.mul_sum]
  gcongr
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  have hb : ∑' z, ∑ k : Fin 2, ENNReal.ofReal (edgeGrad ω v (z, k) ^ 2) ≤
      ∑' b : LatticeEdge, ENNReal.ofReal (greenProj ω ξ b ^ 2) := by
    rw [ENNReal.tsum_prod']
    refine ENNReal.tsum_le_tsum fun z => ?_
    rw [tsum_fintype]
    exact Finset.sum_le_sum fun k _ => ENNReal.ofReal_le_ofReal (hgrad (z, k))
  refine hb.trans ?_
  rw [tsum_ofReal_sq_eq]
  have hn := norm_greenProj_le ω ξ
  have : ∑' z, ENNReal.ofReal (edgeSq ξ z) = ENNReal.ofReal (‖ξ‖ ^ 2) := by
    rw [← tsum_ofReal_sq_eq, ENNReal.tsum_prod']
    refine tsum_congr fun z => ?_
    rw [tsum_fintype, edgeSq, ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
  rw [this]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hn 2)

end Rigidity.Corrector

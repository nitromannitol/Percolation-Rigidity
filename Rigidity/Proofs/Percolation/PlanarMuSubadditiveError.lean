import Rigidity.Proofs.Percolation.PlanarMuSubadditive
import Rigidity.Proofs.Percolation.PlanarEdgeWeights

/-!
# The error in the subadditivity of `μ`

The error term in the subadditivity of `μ` is the coarse pairing of the minimizer `u` of
`μ(U, q)` over the exceptional lattice edges `F` (those leaving their subcube of scale `n` or lying
in an unresolved one). By the window bound, the Cauchy–Schwarz inequality and Young's inequality
with a parameter `t > 0`, it is at most

`|q|₁ (9 · 162000000 S_F / t + t · 2 · 18 |q|₁² · 162000000 S) / 2`,

where `S_F` and `S` are the sums of `s_x ^ 6 + s_{x + e_i} ^ 6` over the edges of `F` and over all
lattice edges of `U`; the energy of `u` is controlled by the upper bound for `-μ(U, q)`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The lattice edges of `U` leaving their subcube of scale `n` or lying in an unresolved one. -/
noncomputable def subcubeExceptionalEdges (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) :
    Finset (Vertex 2 × Fin 2) :=
  (latticeEdgesIn U).filter fun k => ¬ (PlanarResolved ω (scaleCube n k.1) ∧
    k.1 + unitVertex k.2 ∈ (scaleCube n k.1).toIntegerCube.vertices)

theorem subcubeExceptionalEdges_subset (U : TriadicCube 2) (n : ℕ) :
    subcubeExceptionalEdges ω U n ⊆ latticeEdgesIn U := Finset.filter_subset _ _

/-- The sum of sixth powers of the partition sides at the endpoints of a set of edges. -/
noncomputable def edgeSideSum (ω : Configuration 2) (F : Finset (Vertex 2 × Fin 2)) : ℝ :=
  ∑ k ∈ F, (partSide ω (k.1 + unitVertex k.2) ^ 6 + partSide ω k.1 ^ 6)

theorem edgeSideSum_nonneg (F : Finset (Vertex 2 × Fin 2)) : 0 ≤ edgeSideSum ω F :=
  Finset.sum_nonneg fun k _ => by
    have := one_le_partSide (ω := ω) k.1
    have := one_le_partSide (ω := ω) (k.1 + unitVertex k.2)
    positivity

/-- The coarse pairing over a set of edges is bounded by the weighted variation. -/
theorem sum_edges_coarsen_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {F : Finset (Vertex 2 × Fin 2)} (hF : F ⊆ latticeEdgesIn U)
    (q : Fin 2 → ℝ) (u : ClusterFun ω U) :
    ∑ k ∈ F, q k.2 * (coarsen ω U u (k.1 + unitVertex k.2) - coarsen ω U u k.1) ≤
      (|q 0| + |q 1|) * ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) * edgeSetWeight ω U F x.1 := by
  have hQ0 : 0 ≤ |q 0| + |q 1| := by positivity
  have hsum : ∑ k ∈ F, q k.2 * (coarsen ω U u (k.1 + unitVertex k.2) - coarsen ω U u k.1) ≤
      ∑ k ∈ F, (|q 0| + |q 1|) * edgeVariationIn ω
        (coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2)) (clusterExtend ω U u) := by
    refine Finset.sum_le_sum fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 (hF hk)
    have hx : k.1 ∈ U.vertices :=
      (U.mem_toIntegerCube_vertices _).1 (Finset.mem_product.1 hk1).1
    have hy : k.1 + unitVertex k.2 ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hk2
    have hbound := abs_coarseAnchor_sub_le_coarseEdgeWindow hP hU hx hy
      (abs_sub_unitVertex_le k.1 k.2) (clusterExtend ω U u)
    have hq : |q k.2| ≤ |q 0| + |q 1| := by
      rcases Fin.exists_fin_two.1 ⟨k.2, rfl⟩ with h | h <;> rw [h]
      · linarith [abs_nonneg (q 1)]
      · linarith [abs_nonneg (q 0)]
    unfold coarsen
    calc q k.2 * (clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2)) -
          clusterExtend ω U u (planarCoarseAnchor ω k.1))
        ≤ |q k.2| * |clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2)) -
          clusterExtend ω U u (planarCoarseAnchor ω k.1)| := by
          rw [← abs_mul]
          exact le_abs_self _
      _ ≤ (|q 0| + |q 1|) * edgeVariationIn ω (coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2))
          (clusterExtend ω U u) := by
          rw [abs_sub_comm]
          exact mul_le_mul hq hbound (abs_nonneg _) hQ0
  refine hsum.trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_edgeVariationIn_le u F _ fun k => coarseEdgeWindow_subset _ _) hQ0

/-- **Young's bound for edge-set pairings.** -/
theorem sum_edges_coarsen_le_young (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {F : Finset (Vertex 2 × Fin 2)} (hF : F ⊆ latticeEdgesIn U)
    (q : Fin 2 → ℝ) (u : ClusterFun ω U) {t : ℝ} (ht : 0 < t) :
    ∑ k ∈ F, q k.2 * (coarsen ω U u (k.1 + unitVertex k.2) - coarsen ω U u k.1) ≤
      (|q 0| + |q 1|) * ((9 * (162000000 * edgeSideSum ω F)) / t +
        t * (2 * clusterForm ω U u u)) / 2 := by
  set X := ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) * edgeSetWeight ω U F x.1
  set T := ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    (if (openGraph ω).Adj x.1 y.1 then edgeSetWeight ω U F x.1 ^ 2 else 0)
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (by split_ifs <;> positivity) (edgeSetWeight_nonneg U F x.1)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  have hB0 : 0 ≤ 2 * clusterForm ω U u u := by
    have := clusterForm_self_nonneg u
    linarith
  have hCS : X ^ 2 ≤ T * (2 * clusterForm ω U u u) :=
    sum_adj_abs_mul_sq_le u (fun x => edgeSetWeight ω U F x.1)
  have hT9 : T ≤ 9 * ∑ x : ↥(clusterVertices ω U), edgeSetWeight ω U F x.1 ^ 2 :=
    sum_adj_le_nine_mul (fun x => edgeSetWeight ω U F x.1 ^ 2) (fun _ => sq_nonneg _)
  have hW := sum_sq_edgeSetWeight_le hP hU hF
  have hXle := le_of_sq_le_mul hX0 hT0 hB0 ht hCS
  have hT' : T / t ≤ 9 * (162000000 * edgeSideSum ω F) / t := by
    apply div_le_div_of_nonneg_right _ ht.le
    unfold edgeSideSum
    linarith
  have h1 := sum_edges_coarsen_le hP hU hF q u
  have hQ0 : 0 ≤ |q 0| + |q 1| := by positivity
  calc ∑ k ∈ F, q k.2 * (coarsen ω U u (k.1 + unitVertex k.2) - coarsen ω U u k.1)
      ≤ (|q 0| + |q 1|) * X := h1
    _ ≤ (|q 0| + |q 1|) * ((T / t + t * (2 * clusterForm ω U u u)) / 2) :=
        mul_le_mul_of_nonneg_left hXle hQ0
    _ ≤ (|q 0| + |q 1|) * ((9 * (162000000 * edgeSideSum ω F) / t +
          t * (2 * clusterForm ω U u u)) / 2) := by gcongr
    _ = _ := by ring

/-- The energy of the minimizer of `μ(U, q)` is controlled by the sides of the partition cubes. -/
theorem clusterForm_minimizer_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) {u : ClusterFun ω U}
    (hu : u ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u = coarsePairing ω U q w)
    (hμ : planarMu ω U q = (clusterForm ω U u u / 2 - coarsePairing ω U q u) / U.volume) :
    clusterForm ω U u u ≤
      18 * (|q 0| + |q 1|) ^ 2 * (162000000 * edgeSideSum ω (latticeEdgesIn U)) := by
  have hneg := neg_planarMu_le hP hU q
  have hℓ : coarsePairing ω U q u = clusterForm ω U u u := (hvar u hu).symm
  have hvol := U.volume_pos
  have hB : clusterForm ω U u u = -2 * U.volume * planarMu ω U q := by
    rw [hμ, hℓ]
    field_simp
    ring
  have hW := sum_sq_edgeSetWeight_le hP hU (F := latticeEdgesIn U) le_rfl
  have hW' : ∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2 ≤
      162000000 * edgeSideSum ω (latticeEdgesIn U) := hW
  rw [le_div_iff₀ hvol] at hneg
  have hQ2 : 0 ≤ (|q 0| + |q 1|) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hW' (show (0 : ℝ) ≤ 9 * (|q 0| + |q 1|) ^ 2 by positivity)
  rw [hB]
  nlinarith

/-- **Subadditivity of `μ` with a quantified error.** -/
theorem sum_planarMu_subcubes_le_young (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin 2 → ℝ) {t : ℝ} (ht : 0 < t) :
    ∑ x ∈ U.toIntegerCube.vertices,
        (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) ≤
      planarMu ω U q * U.volume + (|q 0| + |q 1|) *
        ((9 * (162000000 * edgeSideSum ω (subcubeExceptionalEdges ω U n))) / t +
          t * (36 * (|q 0| + |q 1|) ^ 2 *
            (162000000 * edgeSideSum ω (latticeEdgesIn U)))) / 2 := by
  obtain ⟨u, hu, hvar, hsub⟩ := sum_planarMu_subcubes_le hP hU hn q
  obtain ⟨u', hu', hvar', hμ'⟩ := exists_planarMu_minimizer hP hU q
  -- the error term is the pairing over the exceptional edges
  have herr : ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
      (if x + unitVertex i ∈ U.toIntegerCube.vertices ∧
          ¬ (PlanarResolved ω (scaleCube n x) ∧
            x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices) then
        q i * (coarsen ω U u (x + unitVertex i) - coarsen ω U u x) else 0) =
      ∑ k ∈ subcubeExceptionalEdges ω U n,
        q k.2 * (coarsen ω U u (k.1 + unitVertex k.2) - coarsen ω U u k.1) := by
    rw [subcubeExceptionalEdges, latticeEdgesIn, Finset.filter_filter, Finset.sum_filter,
      Finset.sum_product]
  rw [herr] at hsub
  -- energies of two minimizers agree
  have hBeq : clusterForm ω U u u = clusterForm ω U u' u' := by
    have h1 := hvar u' hu'
    have h2 := hvar' u hu
    have h3 := hvar u hu
    have h4 := hvar' u' hu'
    rw [clusterForm_symm] at h1
    linarith
  have hBu := clusterForm_minimizer_le hP hU q hu' hvar' hμ'
  have hy := sum_edges_coarsen_le_young hP hU (subcubeExceptionalEdges_subset (ω := ω) U n) q u ht
  have hQ0 : 0 ≤ |q 0| + |q 1| := by positivity
  have hmono : (|q 0| + |q 1|) * ((9 * (162000000 * edgeSideSum ω (subcubeExceptionalEdges ω U n)))
      / t + t * (2 * clusterForm ω U u u)) / 2 ≤
      (|q 0| + |q 1|) * ((9 * (162000000 * edgeSideSum ω (subcubeExceptionalEdges ω U n))) / t +
        t * (36 * (|q 0| + |q 1|) ^ 2 *
          (162000000 * edgeSideSum ω (latticeEdgesIn U)))) / 2 := by
    rw [hBeq]
    have h2B : 2 * clusterForm ω U u' u' ≤ 36 * (|q 0| + |q 1|) ^ 2 *
        (162000000 * edgeSideSum ω (latticeEdgesIn U)) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2B ht.le
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl h3) hQ0)
      (by norm_num)
  linarith

end Rigidity.Percolation

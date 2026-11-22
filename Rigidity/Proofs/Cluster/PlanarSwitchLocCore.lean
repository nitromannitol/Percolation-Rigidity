import Rigidity.Proofs.Cluster.PlanarOneVarEstBound

/-!
# The deterministic comparison behind display (5.31) of Armstrong and Dario

For a resolved cube `U`, the pairing of the coarsened gradient of a function `w` on the cluster
with a field `h` is controlled by the Dirichlet form, with the weight of a vertex the sum of `|h|`
over the lattice edges whose coarsening window contains it (the argument of the upper bound for
`μ`, Lemma 4.4): `ℓ_h(w)² ≤ 9 N W ‖h‖² · 2 B(w, w)`, where `N` bounds the number of windows
containing a vertex and `W` the size of the windows (`fieldPairing_sq_le_of_bounds`).

If `u` and `u'` solve the first variations `B(·, u) = ℓ_q`, `B(·, u') = ℓ_{q'}` on the harmonic
functions, then by the second variation `B(u - u', u - u') = ℓ_{q - q'}(u - u')`, and
`(ℓ_g(u) - ℓ_{g'}(u'))² ≤ 8 K² (‖g‖² ‖q - q'‖² + ‖g - g'‖² ‖q'‖²)` whenever
`ℓ_h(w)² ≤ K ‖h‖² · 2 B(w, w)` for all `h, w` (`sq_fieldPairing_sub_le`). This is the comparison
of `u(·, □, q)` with its localized version in the proof of Proposition 4.10 (display (e.ulocloc))
and of Lemma 5.7, display (5.31).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- The squared norm `∑_{edges of U} h²` of a field over the lattice edges of `U`. -/
noncomputable def edgeNormSq (U : TriadicCube 2) (h : Vertex 2 → Fin 2 → ℝ) : ℝ :=
  ∑ k ∈ latticeEdgesIn U, h k.1 k.2 ^ 2

theorem edgeNormSq_nonneg (U : TriadicCube 2) (h : Vertex 2 → Fin 2 → ℝ) :
    0 ≤ edgeNormSq U h :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The weight of a vertex for a field: the sum of `|h|` over the lattice edges of `U` whose
coarsening window contains the vertex. -/
noncomputable def fieldWeight (ω : Configuration 2) (U : TriadicCube 2)
    (h : Vertex 2 → Fin 2 → ℝ) (a : Vertex 2) : ℝ :=
  ∑ k ∈ latticeEdgesIn U, |h k.1 k.2| *
    (if a ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2) then 1 else 0)

theorem fieldPairing_eq_sum_latticeEdgesIn {U : TriadicCube 2} (h : Vertex 2 → Fin 2 → ℝ)
    (u : ClusterFun ω U) :
    fieldPairing ω U h u = ∑ k ∈ latticeEdgesIn U,
      h k.1 k.2 * (clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2)) -
        clusterExtend ω U u (planarCoarseAnchor ω k.1)) := by
  rw [fieldPairing_apply, latticeEdgesIn, Finset.sum_filter, Finset.sum_product]

theorem fieldPairing_sub {U : TriadicCube 2} (g h : Vertex 2 → Fin 2 → ℝ) (u : ClusterFun ω U) :
    fieldPairing ω U (g - h) u = fieldPairing ω U g u - fieldPairing ω U h u := by
  simp only [fieldPairing_eq_sum_latticeEdgesIn, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.sub_apply]
  ring

/-- The field pairing is bounded by the increments over the open edges of the cluster weighted by
the field weight of the first vertex. -/
theorem abs_fieldPairing_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (h : Vertex 2 → Fin 2 → ℝ) (u : ClusterFun ω U) :
    |fieldPairing ω U h u| ≤ ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) * fieldWeight ω U h x.1 := by
  rw [fieldPairing_eq_sum_latticeEdgesIn]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hstep : ∀ k ∈ latticeEdgesIn U,
      |h k.1 k.2 * (clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2)) -
        clusterExtend ω U u (planarCoarseAnchor ω k.1))| ≤
      ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) *
          (|h k.1 k.2| *
            (if x.1 ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2) then 1 else 0)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    have hx : k.1 ∈ U.vertices :=
      (U.mem_toIntegerCube_vertices _).1 (Finset.mem_product.1 hk1).1
    have hy : k.1 + unitVertex k.2 ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hk2
    have hbound := abs_coarseAnchor_sub_le_coarseEdgeWindow hP hU hx hy
      (abs_sub_unitVertex_le k.1 k.2) (clusterExtend ω U u)
    have hev := edgeVariationIn_le_of_subset u
      (coarseEdgeWindow_subset (ω := ω) (U := U) k.1 (k.1 + unitVertex k.2))
    rw [abs_mul, abs_sub_comm]
    calc |h k.1 k.2| * |clusterExtend ω U u (planarCoarseAnchor ω k.1) -
          clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2))|
        ≤ |h k.1 k.2| * ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
            (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) *
              (if x.1 ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2) then 1 else 0) :=
          mul_le_mul_of_nonneg_left (hbound.trans hev) (abs_nonneg _)
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [fieldWeight, Finset.mul_sum]

/-- **Cauchy–Schwarz for the field pairing.** -/
theorem fieldPairing_sq_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (h : Vertex 2 → Fin 2 → ℝ) (u : ClusterFun ω U) :
    fieldPairing ω U h u ^ 2 ≤
      (9 * ∑ x : ↥(clusterVertices ω U), fieldWeight ω U h x.1 ^ 2) * (2 * clusterForm ω U u u) := by
  have h1 := abs_fieldPairing_le hP hU h u
  have hw0 : ∀ a, 0 ≤ fieldWeight ω U h a := fun a =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (by split_ifs <;> norm_num)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ Finset.univ)
    (fun p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U) =>
      if (openGraph ω).Adj p.1.1 p.2.1 then fieldWeight ω U h p.1.1 else 0)
    (fun p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U) =>
      if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0)
  have e1 : ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) * fieldWeight ω U h x.1 =
      ∑ p ∈ (Finset.univ : Finset ↥(clusterVertices ω U)) ×ˢ (Finset.univ : Finset ↥(clusterVertices ω U)),
        (if (openGraph ω).Adj p.1.1 p.2.1 then fieldWeight ω U h p.1.1 else 0) *
          (if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  have e2 : ∑ p ∈ (Finset.univ : Finset ↥(clusterVertices ω U)) ×ˢ (Finset.univ : Finset ↥(clusterVertices ω U)),
      (if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0) ^ 2 =
      2 * clusterForm ω U u u := by
    rw [two_mul_clusterForm_self, Finset.sum_product]
  have e3 : ∑ p ∈ (Finset.univ : Finset ↥(clusterVertices ω U)) ×ˢ (Finset.univ : Finset ↥(clusterVertices ω U)),
      (if (openGraph ω).Adj p.1.1 p.2.1 then fieldWeight ω U h p.1.1 else 0) ^ 2 ≤
      9 * ∑ x : ↥(clusterVertices ω U), fieldWeight ω U h x.1 ^ 2 := by
    rw [Finset.sum_product]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
      (sum_adj_le_nine_mul (fun x => fieldWeight ω U h x.1 ^ 2) fun _ => sq_nonneg _)
    split_ifs <;> simp
  have hB : 0 ≤ 2 * clusterForm ω U u u := by
    rw [← e2]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc fieldPairing ω U h u ^ 2 = |fieldPairing ω U h u| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
          (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) * fieldWeight ω U h x.1) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ _ := by
        rw [e1]
        refine hcs.trans ?_
        rw [e2]
        exact mul_le_mul_of_nonneg_right e3 hB

/-- The sum of the squared field weights over the cluster is at most `N W ‖h‖²`, where `N` bounds
the number of windows containing a vertex and `W` the size of the windows. -/
theorem sum_fieldWeight_sq_le {U : TriadicCube 2} (h : Vertex 2 → Fin 2 → ℝ) {N W : ℝ}
    (hN : ∀ a, coarseWeight ω U a ≤ N)
    (hW : ∀ k ∈ latticeEdgesIn U,
      ((coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2)).card : ℝ) ≤ W) :
    ∑ x : ↥(clusterVertices ω U), fieldWeight ω U h x.1 ^ 2 ≤ N * W * edgeNormSq U h := by
  set ind : (Vertex 2 × Fin 2) → Vertex 2 → ℝ := fun k a =>
    if a ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2) then 1 else 0 with hind
  have hind0 : ∀ k a, 0 ≤ ind k a := fun k a => by simp only [hind]; split_ifs <;> norm_num
  have hind2 : ∀ k a, ind k a ^ 2 = ind k a := fun k a => by
    simp only [hind]; split_ifs <;> norm_num
  have hpt : ∀ a, fieldWeight ω U h a ^ 2 ≤
      N * ∑ k ∈ latticeEdgesIn U, h k.1 k.2 ^ 2 * ind k a := by
    intro a
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (latticeEdgesIn U) (fun k => ind k a)
      (fun k => |h k.1 k.2| * ind k a)
    have e1 : fieldWeight ω U h a = ∑ k ∈ latticeEdgesIn U, ind k a * (|h k.1 k.2| * ind k a) := by
      unfold fieldWeight
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hind2 k a]
      simp only [hind]
      split_ifs <;> ring
    have e2 : ∑ k ∈ latticeEdgesIn U, ind k a ^ 2 = coarseWeight ω U a := by
      unfold coarseWeight
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hind2]
    have e3 : ∑ k ∈ latticeEdgesIn U, (|h k.1 k.2| * ind k a) ^ 2 =
        ∑ k ∈ latticeEdgesIn U, h k.1 k.2 ^ 2 * ind k a := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, sq_abs, hind2]
    rw [e1]
    refine hcs.trans ?_
    rw [e2, e3]
    exact mul_le_mul_of_nonneg_right (hN a)
      (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hind0 k a))
  have hN0 : 0 ≤ N := (coarseWeight_nonneg U 0).trans (hN 0)
  calc ∑ x : ↥(clusterVertices ω U), fieldWeight ω U h x.1 ^ 2
      ≤ ∑ x : ↥(clusterVertices ω U), N * ∑ k ∈ latticeEdgesIn U, h k.1 k.2 ^ 2 * ind k x.1 :=
        Finset.sum_le_sum fun x _ => hpt x.1
    _ = N * ∑ k ∈ latticeEdgesIn U, h k.1 k.2 ^ 2 *
          ∑ x : ↥(clusterVertices ω U), ind k x.1 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ N * ∑ k ∈ latticeEdgesIn U, h k.1 k.2 ^ 2 * W := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) hN0
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine le_trans (le_of_eq ?_) (hW k hk)
        rw [Finset.sum_coe_sort (clusterVertices ω U) (fun x => ind k x), Finset.sum_boole]
        have hsub : (clusterVertices ω U).filter
            (fun x => x ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2)) =
            coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2) := by
          ext x
          simp only [Finset.mem_filter, and_iff_right_iff_imp]
          exact fun hx => coarseEdgeWindow_subset _ _ hx
        rw [hsub]
    _ = N * W * edgeNormSq U h := by
        rw [edgeNormSq, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- **The weighted bound for the field pairing.** With `N` and `W` as above,
`ℓ_h(w)² ≤ 9 N W ‖h‖² · 2 B(w, w)`. -/
theorem fieldPairing_sq_le_of_bounds (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {N W : ℝ} (hN : ∀ a, coarseWeight ω U a ≤ N)
    (hW : ∀ k ∈ latticeEdgesIn U,
      ((coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2)).card : ℝ) ≤ W)
    (h : Vertex 2 → Fin 2 → ℝ) (u : ClusterFun ω U) :
    fieldPairing ω U h u ^ 2 ≤ 9 * N * W * edgeNormSq U h * (2 * clusterForm ω U u u) := by
  have hB : 0 ≤ 2 * clusterForm ω U u u := by
    rw [two_mul_clusterForm_self]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine (fieldPairing_sq_le hP hU h u).trans ?_
  have := sum_fieldWeight_sq_le h hN hW
  calc (9 * ∑ x : ↥(clusterVertices ω U), fieldWeight ω U h x.1 ^ 2) * (2 * clusterForm ω U u u)
      ≤ (9 * (N * W * edgeNormSq U h)) * (2 * clusterForm ω U u u) :=
        mul_le_mul_of_nonneg_right (by linarith) hB
    _ = _ := by ring

/-- `B ≤ |X|` and `X² ≤ K ‖h‖² · 2B` give `B ≤ 2 K ‖h‖²`. -/
theorem le_of_le_abs_of_sq_le {B X T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) (h1 : B ≤ |X|)
    (h2 : X ^ 2 ≤ T * (2 * B)) : B ≤ 2 * T := by
  have := le_of_le_mul_of_sq_le (Q := 1) (X := |X|) hB hT (by rw [one_mul]; exact h1)
    (by rw [sq_abs]; exact h2) zero_le_one
  linarith

/-- **The second variation comparison.** If `u, u'` are harmonic and solve
`B(·, u) = ℓ_q`, `B(·, u') = ℓ_{q'}` on the harmonic functions, and `ℓ_h(w)² ≤ K ‖h‖² · 2 B(w, w)`
for every field `h` and function `w`, then
`(ℓ_g(u) - ℓ_{g'}(u'))² ≤ 8 K² (‖g‖² ‖q - q'‖² + ‖g - g'‖² ‖q'‖²)`. -/
theorem sq_fieldPairing_sub_le {U : TriadicCube 2} {g g' q q' : Vertex 2 → Fin 2 → ℝ}
    {u u' : ClusterFun ω U} (hu : u ∈ clusterHarmonic ω U) (hu' : u' ∈ clusterHarmonic ω U)
    (hv : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u = fieldPairing ω U q w)
    (hv' : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u' = fieldPairing ω U q' w)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (h : Vertex 2 → Fin 2 → ℝ) (w : ClusterFun ω U),
      fieldPairing ω U h w ^ 2 ≤ K * edgeNormSq U h * (2 * clusterForm ω U w w)) :
    (fieldPairing ω U g u - fieldPairing ω U g' u') ^ 2 ≤
      8 * K ^ 2 * (edgeNormSq U g * edgeNormSq U (q - q') +
        edgeNormSq U (g - g') * edgeNormSq U q') := by
  have hδA : u - u' ∈ clusterHarmonic ω U := sub_mem hu hu'
  have hBnn : ∀ w : ClusterFun ω U, 0 ≤ clusterForm ω U w w := fun w => by
    have h2 := two_mul_clusterForm_self (ω := ω) (U := U) w
    have : 0 ≤ 2 * clusterForm ω U w w := by
      rw [h2]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hBδ : clusterForm ω U (u - u') (u - u') = fieldPairing ω U (q - q') (u - u') := by
    rw [fieldPairing_sub, ← hv _ hδA, ← hv' _ hδA, ← map_sub]
  have hBδle : clusterForm ω U (u - u') (u - u') ≤ 2 * (K * edgeNormSq U (q - q')) :=
    le_of_le_abs_of_sq_le (X := fieldPairing ω U (q - q') (u - u')) (hBnn _)
      (mul_nonneg hK0 (edgeNormSq_nonneg _ _)) (by rw [hBδ]; exact le_abs_self _) (hK _ _)
  have hBu' : clusterForm ω U u' u' = fieldPairing ω U q' u' := hv' u' hu'
  have hBu'le : clusterForm ω U u' u' ≤ 2 * (K * edgeNormSq U q') :=
    le_of_le_abs_of_sq_le (X := fieldPairing ω U q' u') (hBnn u')
      (mul_nonneg hK0 (edgeNormSq_nonneg _ _)) (by rw [hBu']; exact le_abs_self _) (hK _ u')
  have hsplit : fieldPairing ω U g u - fieldPairing ω U g' u' =
      fieldPairing ω U g (u - u') + fieldPairing ω U (g - g') u' := by
    rw [fieldPairing_sub, map_sub]
    ring
  have h1 := hK g (u - u')
  have h2 := hK (g - g') u'
  have hng := edgeNormSq_nonneg U g
  have hngg := edgeNormSq_nonneg U (g - g')
  have hnq := edgeNormSq_nonneg U (q - q')
  have hnq' := edgeNormSq_nonneg U q'
  rw [hsplit]
  generalize fieldPairing ω U g (u - u') = a at h1 ⊢
  generalize fieldPairing ω U (g - g') u' = b at h2 ⊢
  generalize clusterForm ω U (u - u') (u - u') = B₁ at h1 hBδle
  generalize clusterForm ω U u' u' = B₂ at h2 hBu'le
  generalize edgeNormSq U g = Ng at h1 hng ⊢
  generalize edgeNormSq U (g - g') = Ngg at h2 hngg ⊢
  generalize edgeNormSq U (q - q') = Nq at hBδle hnq ⊢
  generalize edgeNormSq U q' = Nq' at hBu'le hnq' ⊢
  have hsq : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h1' : a ^ 2 ≤ K * Ng * (2 * (2 * (K * Nq))) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK0 hng))
  have h2' : b ^ 2 ≤ K * Ngg * (2 * (2 * (K * Nq'))) :=
    h2.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK0 hngg))
  have e : 8 * K ^ 2 * (Ng * Nq + Ngg * Nq') =
      2 * (K * Ng * (2 * (2 * (K * Nq)))) + 2 * (K * Ngg * (2 * (2 * (K * Nq')))) := by ring
  rw [e]
  linarith

end Rigidity.Proofs.Cluster

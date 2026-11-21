import Rigidity.Proofs.Cluster.CoarseData

/-!
# Coarse-grained functional inequalities on a cluster

Armstrong and Dario, Lemmas 3.2 and 3.3, for coarse-graining data in every dimension and every
exponent `1 ≤ s < ∞`.

* `CoarseData.sum_abs_sub_coarsen_rpow_le_errorWeight` and
  `CoarseData.sum_gradNormIn_coarsen_rpow_le_gradWeight`: the two inequalities with exact weights,
  obtained by Hölder's inequality on the sums of the increments along the local open paths.
* `CoarseData.sum_abs_sub_coarsen_rpow_le` (Lemma 3.2) and
  `CoarseData.sum_gradNormIn_coarsen_rpow_le` (Lemma 3.3): the weights are bounded by
  `C^s size(□_𝒫(z))^{sd}`, respectively `C^s size(□_𝒫(z))^{sd-1}`, when the regions have volume
  comparable to the partition cube, meet only partition cubes of comparable size, and each vertex
  lies in the regions of boundedly many partition cubes. The right sides are written as sums over
  the vertices `z` of the cluster; grouping them by partition cubes gives the sums
  `∑_{□ ⊆ cl_𝒫(U)} size(□)^{sd} ∫_{□ ∩ C_*(U)}` of Armstrong and Dario.

The boundary count used for Lemma 3.3 is `TriadicCube.card_exitPairs_le`: at most
`2d · 3^{(d-1)n}` lattice edges leave a triadic cube of scale `n`.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

section Faces

/-- A lattice cube has its side length to the dimension many vertices. -/
theorem IntegerCube.card_vertices_eq (Q : IntegerCube d) : Q.vertices.card = Q.size ^ d := by
  simp only [IntegerCube.vertices, Fintype.card_piFinset, Int.card_Ico]
  have hcard : ∀ i : Fin d, (Q.corner i + (Q.size : ℤ) - Q.corner i).toNat = Q.size := by
    intro i
    simp only [add_sub_cancel_left, Int.toNat_natCast]
  simp only [hcard, Finset.prod_const, Finset.card_fin]

private theorem IntegerCube.card_slice (Q : IntegerCube d) (i : Fin d) (a : ℤ) :
    (Fintype.piFinset fun j => if j = i then ({a} : Finset ℤ)
      else Finset.Ico (Q.corner j) (Q.corner j + (Q.size : ℤ))).card = Q.size ^ (d - 1) := by
  rw [Fintype.card_piFinset]
  have h : ∀ j, (if j = i then ({a} : Finset ℤ)
      else Finset.Ico (Q.corner j) (Q.corner j + (Q.size : ℤ))).card =
      if j = i then 1 else Q.size := by
    intro j
    split_ifs
    · exact Finset.card_singleton a
    · rw [Int.card_Ico]
      simp
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]
  congr 1
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin d))) (fun j => j = i)
  rw [Finset.filter_eq' Finset.univ i, if_pos (Finset.mem_univ i), Finset.card_singleton,
    Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- The upper face of a lattice cube in a given direction has at most `size^(d-1)` vertices. -/
theorem IntegerCube.card_upperFace_le (Q : IntegerCube d) (i : Fin d) :
    (Q.upperFace i).card ≤ Q.size ^ (d - 1) := by
  rw [← IntegerCube.card_slice Q i (Q.corner i + Q.size - 1)]
  apply Finset.card_le_card
  intro x hx
  rw [IntegerCube.mem_upperFace, IntegerCube.mem_vertices] at hx
  rw [Fintype.mem_piFinset]
  intro j
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, Finset.mem_singleton]
    have := hx.2
    omega
  · rw [if_neg hj, Finset.mem_Ico]
    exact hx.1 j

/-- The lower face of a lattice cube in a given direction has at most `size^(d-1)` vertices. -/
theorem IntegerCube.card_lowerFace_le (Q : IntegerCube d) (i : Fin d) :
    (Q.lowerFace i).card ≤ Q.size ^ (d - 1) := by
  rw [← IntegerCube.card_slice Q i (Q.corner i)]
  apply Finset.card_le_card
  intro x hx
  rw [IntegerCube.mem_lowerFace, IntegerCube.mem_vertices] at hx
  rw [Fintype.mem_piFinset]
  intro j
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, Finset.mem_singleton]
    exact hx.2
  · rw [if_neg hj, Finset.mem_Ico]
    exact hx.1 j

/-- **Edges leaving a triadic cube.** At most `2d · 3^{(d-1)n}` ordered pairs `(x, y)` of lattice
neighbours have `x` in a triadic cube of scale `n` and `y` outside it. -/
theorem TriadicCube.card_exitPairs_le (Q : TriadicCube d) (S : Finset (Vertex d)) :
    ((Q.toIntegerCube.vertices ×ˢ S).filter fun q =>
      (nearestNeighborGraph d).Adj q.1 q.2 ∧ q.2 ∉ Q.vertices).card ≤
      2 * d * 3 ^ (Q.scale * (d - 1)) := by
  have hsub : ((Q.toIntegerCube.vertices ×ˢ S).filter fun q =>
      (nearestNeighborGraph d).Adj q.1 q.2 ∧ q.2 ∉ Q.vertices) ⊆
      Finset.univ.biUnion fun i : Fin d =>
        (Q.toIntegerCube.upperFace i).image (fun x => (x, x + LatticeProb.unit i)) ∪
          (Q.toIntegerCube.lowerFace i).image (fun x => (x, x - LatticeProb.unit i)) := by
    rintro ⟨x, y⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hx, -⟩, hadj, hy⟩ := hq
    rw [← Q.mem_toIntegerCube_vertices] at hy
    obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 hadj
    · subst hi
      refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_union_left _
        (Finset.mem_image.2 ⟨x, ?_, rfl⟩)⟩
      rw [IntegerCube.mem_upperFace]
      refine ⟨hx, ?_⟩
      by_contra hne
      apply hy
      rw [IntegerCube.mem_vertices] at hx ⊢
      intro j
      by_cases hj : j = i
      · subst hj
        have := hx j
        simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hj, add_zero]
        exact hx j
    · subst hi
      refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_union_right _
        (Finset.mem_image.2 ⟨x, ?_, rfl⟩)⟩
      rw [IntegerCube.mem_lowerFace]
      refine ⟨hx, ?_⟩
      by_contra hne
      apply hy
      rw [IntegerCube.mem_vertices] at hx ⊢
      intro j
      by_cases hj : j = i
      · subst hj
        have := hx j
        simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
        omega
      · simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne hj, sub_zero]
        exact hx j
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin d, ((Q.toIntegerCube.upperFace i).card +
          (Q.toIntegerCube.lowerFace i).card) := by
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
        exact (Finset.card_union_le _ _).trans
          (add_le_add Finset.card_image_le Finset.card_image_le)
    _ ≤ ∑ _i : Fin d, 2 * Q.toIntegerCube.size ^ (d - 1) := Finset.sum_le_sum fun i _ => by
        have h1 := Q.toIntegerCube.card_upperFace_le i
        have h2 := Q.toIntegerCube.card_lowerFace_le i
        omega
    _ = 2 * d * 3 ^ (Q.scale * (d - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pow_mul]
        simp only [TriadicCube.toIntegerCube]
        ring

end Faces

section Algebra

private theorem sum_mul_sum_inter_eq {ι : Type*} (C : Finset (Vertex d))
    (R : ι → Finset (Vertex d)) (A : Finset ι) (c : ι → ℝ) (f : Vertex d → ℝ) :
    ∑ x ∈ A, c x * ∑ z ∈ R x ∩ C, f z =
      ∑ z ∈ C, (∑ x ∈ A, if z ∈ R x then c x else 0) * f z := by
  have h : ∀ x, ∑ z ∈ R x ∩ C, f z = ∑ z ∈ C, if z ∈ R x then f z else 0 := by
    intro x
    rw [← Finset.sum_filter]
    congr 1
    ext z
    simp only [Finset.mem_inter, Finset.mem_filter, and_comm]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

private theorem sum_le_of_fibres {α β : Type*} [DecidableEq β] (F : Finset α) (g : α → β)
    (c : α → ℝ) {A M : ℝ} {N : ℕ} (hc : ∀ q ∈ F, c q ≤ A) (hA : 0 ≤ A)
    (hfib : ∀ Q ∈ F.image g, ((F.filter fun q => g q = Q).card : ℝ) ≤ M)
    (himage : (F.image g).card ≤ N) (hM : 0 ≤ M) : ∑ q ∈ F, c q ≤ N * M * A := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem g hq) c]
  calc ∑ Q ∈ F.image g, ∑ q ∈ F.filter (fun q => g q = Q), c q
      ≤ ∑ _Q ∈ F.image g, M * A := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        calc ∑ q ∈ F.filter (fun q => g q = Q), c q
            ≤ ∑ _q ∈ F.filter (fun q => g q = Q), A :=
              Finset.sum_le_sum fun q hq => hc q (Finset.mem_filter.1 hq).1
          _ = ((F.filter fun q => g q = Q).card : ℝ) * A := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ M * A := mul_le_mul_of_nonneg_right (hfib Q hQ) hA
    _ = ((F.image g).card : ℝ) * (M * A) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * (M * A) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast himage) (mul_nonneg hM hA)
    _ = N * M * A := by ring

private theorem mul_mul_rpow_sub_one {L K : ℝ} (hL : 0 < L) (hK : 0 ≤ K) (s : ℝ) :
    L * (K * L) ^ (s - 1) = K ^ (s - 1) * L ^ s := by
  rw [Real.mul_rpow hK hL.le, Real.rpow_sub_one hL.ne' s]
  calc L * (K ^ (s - 1) * (L ^ s / L)) = K ^ (s - 1) * (L ^ s / L * L) := by ring
    _ = K ^ (s - 1) * L ^ s := by rw [div_mul_cancel₀ _ hL.ne']

private theorem pow_mul_rpow_sub_one {b K : ℝ} (hb : 0 < b) (hK : 0 ≤ K) (hd : 1 ≤ d)
    (s : ℝ) : b ^ (d - 1) * (K * b ^ d) ^ (s - 1) = K ^ (s - 1) * b ^ (s * d - 1) := by
  rw [Real.mul_rpow hK (by positivity)]
  have hexp : b ^ (s * d - 1) = b ^ (d - 1) * (b ^ d) ^ (s - 1) := by
    rw [← Real.rpow_natCast b (d - 1), ← Real.rpow_natCast b d, ← Real.rpow_mul hb.le,
      ← Real.rpow_add hb]
    congr 1
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [hexp]
  ring

private theorem coarse_const_le {W V N K t A c g s : ℝ} (hs : 1 ≤ s) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (ht : 0 ≤ t) (hA : 0 ≤ A) (hc : 0 ≤ c) (hg : 0 ≤ g) (hW : W ≤ N * K ^ (s - 1) * (t * A) ^ s)
    (hV0 : 0 ≤ V) (hV : V ≤ (c * g) ^ s) :
    W * V ≤ (N * K * t * c) ^ s * (A ^ s * g ^ s) := by
  have hN0 : 0 ≤ N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hNs : N ≤ N ^ s := Real.self_le_rpow_of_one_le hN hs
  have hKs : K ^ (s - 1) ≤ K ^ s := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have htA : 0 ≤ (t * A) ^ s := Real.rpow_nonneg (mul_nonneg ht hA) s
  have hcg : 0 ≤ (c * g) ^ s := Real.rpow_nonneg (mul_nonneg hc hg) s
  calc W * V ≤ (N * K ^ (s - 1) * (t * A) ^ s) * (c * g) ^ s :=
        mul_le_mul hW hV hV0 (by positivity)
    _ ≤ (N ^ s * K ^ s * (t * A) ^ s) * (c * g) ^ s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul hNs hKs (by positivity) (by positivity)) htA) hcg
    _ = (N * K * t * c) ^ s * (A ^ s * g ^ s) := by
        rw [Real.mul_rpow ht hA, Real.mul_rpow hc hg,
          Real.mul_rpow (x := N * K * t) (y := c) (by positivity) hc,
          Real.mul_rpow (x := N * K) (y := t) (by positivity) ht, Real.mul_rpow hN0 hK0]
        ring

private theorem coarse_const_le' {W V N K t A c g D s : ℝ} (hs : 1 ≤ s) (hN : 1 ≤ N)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (hA : 0 ≤ A) (hc : 0 ≤ c) (hg : 0 ≤ g) (hD : 0 < D)
    (hW : W ≤ D * N * K ^ (s - 1) * (t ^ s * A)) (hV0 : 0 ≤ V) (hV : V ≤ (c * g) ^ s) :
    D ^ (s - 1) * (W * V) ≤ (D * N * K * t * c) ^ s * (A * g ^ s) := by
  have hN0 : 0 ≤ N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hNs : N ≤ N ^ s := Real.self_le_rpow_of_one_le hN hs
  have hKs : K ^ (s - 1) ≤ K ^ s := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have htA : 0 ≤ t ^ s * A := mul_nonneg (Real.rpow_nonneg ht s) hA
  have hcg : 0 ≤ (c * g) ^ s := Real.rpow_nonneg (mul_nonneg hc hg) s
  have hDs : 0 ≤ D ^ (s - 1) := Real.rpow_nonneg hD.le _
  calc D ^ (s - 1) * (W * V) ≤ D ^ (s - 1) * ((D * N * K ^ (s - 1) * (t ^ s * A)) * (c * g) ^ s) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hW hV hV0 (by positivity)) hDs
    _ ≤ D ^ (s - 1) * ((D * N ^ s * K ^ s * (t ^ s * A)) * (c * g) ^ s) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ?_ htA) hcg) hDs
        rw [mul_assoc D, mul_assoc D]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hNs hKs (by positivity) (by positivity))
          hD.le
    _ = (D ^ (s - 1) * D) * N ^ s * K ^ s * t ^ s * c ^ s * (A * g ^ s) := by
        rw [Real.mul_rpow hc hg]
        ring
    _ = (D * N * K * t * c) ^ s * (A * g ^ s) := by
        rw [Real.rpow_sub_one hD.ne' s, div_mul_cancel₀ _ hD.ne',
          Real.mul_rpow (x := D * N * K * t) (y := c) (by positivity) hc,
          Real.mul_rpow (x := D * N * K) (y := t) (by positivity) ht,
          Real.mul_rpow (x := D * N) (y := K) (by positivity) hK0,
          Real.mul_rpow hD.le hN0]

end Algebra

namespace CoarseData

variable {ω : Configuration d} (P : CoarseData d ω)

/-- The ordered pairs of lattice neighbours of the domain lying in different partition cubes. -/
noncomputable def edgesAcross : Finset (Vertex d × Vertex d) :=
  (P.domain ×ˢ P.domain).filter fun q =>
    (nearestNeighborGraph d).Adj q.1 q.2 ∧ P.part q.1 ≠ P.part q.2

/-- The weight of the coarsening error at `z`: the sum of `#(R(x) ∩ C_*(U))^{s-1}` over the
vertices `x` of the cluster whose region `R(x)` contains `z`. -/
noncomputable def errorWeight (s : ℝ) (z : Vertex d) : ℝ :=
  ∑ x ∈ P.cluster, if z ∈ P.region x then ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1) else 0

/-- The weight of the coarse gradient at `z`: the sum of `#(R(x, y) ∩ C_*(U))^{s-1}` over the
pairs of lattice neighbours `(x, y)` in different partition cubes whose region `R(x, y)` contains
`z`. -/
noncomputable def gradWeight (s : ℝ) (z : Vertex d) : ℝ :=
  ∑ q ∈ P.edgesAcross, if z ∈ P.pairRegion q.1 q.2 then
    ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1) else 0

theorem errorWeight_nonneg (s : ℝ) (z : Vertex d) : 0 ≤ P.errorWeight s z :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem gradWeight_nonneg (s : ℝ) (z : Vertex d) : 0 ≤ P.gradWeight s z :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- **Coarsening error at a vertex.** `|w(x) - [w]_𝒫(x)|^s` is at most `#R^{s-1}` times the sum
over `z ∈ R = R(x) ∩ C_*(U)` of the `s`-th power of the open increments of `w` at `z`. -/
theorem abs_sub_coarsen_rpow_le (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) {x : Vertex d}
    (hx : x ∈ P.cluster) :
    |w x - P.coarsen w x| ^ s ≤ ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1) *
      ∑ z ∈ P.region x ∩ P.cluster, vertexVariation ω P.cluster w z ^ s := by
  have h1 := abs_sub_le_sum_vertexVariation (P.region x ∩ P.cluster) w
    (P.joinedWithin_region x hx)
  have h2 : ∑ z ∈ P.region x ∩ P.cluster, vertexVariation ω (P.region x ∩ P.cluster) w z ≤
      ∑ z ∈ P.region x ∩ P.cluster, vertexVariation ω P.cluster w z :=
    Finset.sum_le_sum fun z _ => vertexVariation_mono ω Finset.inter_subset_right w z
  calc |w x - P.coarsen w x| ^ s
      ≤ (∑ z ∈ P.region x ∩ P.cluster, vertexVariation ω P.cluster w z) ^ s :=
        Real.rpow_le_rpow (abs_nonneg _) (h1.trans h2) (by linarith)
    _ ≤ _ := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := P.region x ∩ P.cluster) hs
        (fun z _ => vertexVariation_nonneg ω P.cluster w z)

/-- **Coarse gradient across an edge.** For lattice neighbours `x, y` of the domain in different
partition cubes, `|[w]_𝒫(x) - [w]_𝒫(y)|^s` is at most `#R^{s-1}` times the sum over
`z ∈ R = R(x, y) ∩ C_*(U)` of the `s`-th power of the open increments of `w` at `z`. -/
theorem abs_coarsen_sub_rpow_le (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) {x y : Vertex d}
    (hx : x ∈ P.domain) (hy : y ∈ P.domain) (hxy : (nearestNeighborGraph d).Adj x y)
    (hne : P.part x ≠ P.part y) :
    |P.coarsen w x - P.coarsen w y| ^ s ≤
      ((P.pairRegion x y ∩ P.cluster).card : ℝ) ^ (s - 1) *
        ∑ z ∈ P.pairRegion x y ∩ P.cluster, vertexVariation ω P.cluster w z ^ s := by
  have h1 := abs_sub_le_sum_vertexVariation (P.pairRegion x y ∩ P.cluster) w
    (P.joinedWithin_pairRegion x hx y hy hxy hne)
  have h2 : ∑ z ∈ P.pairRegion x y ∩ P.cluster,
      vertexVariation ω (P.pairRegion x y ∩ P.cluster) w z ≤
      ∑ z ∈ P.pairRegion x y ∩ P.cluster, vertexVariation ω P.cluster w z :=
    Finset.sum_le_sum fun z _ => vertexVariation_mono ω Finset.inter_subset_right w z
  calc |P.coarsen w x - P.coarsen w y| ^ s
      ≤ (∑ z ∈ P.pairRegion x y ∩ P.cluster, vertexVariation ω P.cluster w z) ^ s :=
        Real.rpow_le_rpow (abs_nonneg _) (h1.trans h2) (by linarith)
    _ ≤ _ := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := P.pairRegion x y ∩ P.cluster) hs
        (fun z _ => vertexVariation_nonneg ω P.cluster w z)

/-- **Coarsening error with exact weights** (Armstrong and Dario, Lemma 3.2, before bounding the
weights). -/
theorem sum_abs_sub_coarsen_rpow_le_errorWeight (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤
      ∑ z ∈ P.cluster, P.errorWeight s z * vertexVariation ω P.cluster w z ^ s := by
  calc ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s
      ≤ ∑ x ∈ P.cluster, ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1) *
          ∑ z ∈ P.region x ∩ P.cluster, vertexVariation ω P.cluster w z ^ s :=
        Finset.sum_le_sum fun x hx => P.abs_sub_coarsen_rpow_le w hs hx
    _ = _ := sum_mul_sum_inter_eq P.cluster P.region P.cluster
        (fun x => ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1))
        (fun z => vertexVariation ω P.cluster w z ^ s)

/-- **Coarse gradients with exact weights** (Armstrong and Dario, Lemma 3.3, before bounding the
weights). -/
theorem sum_gradNormIn_coarsen_rpow_le_gradWeight (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ s ≤
      (2 * d : ℝ) ^ (s - 1) *
        ∑ z ∈ P.cluster, P.gradWeight s z * vertexVariation ω P.cluster w z ^ s := by
  have hs0 : s ≠ 0 := (show (0 : ℝ) < s by linarith).ne'
  calc ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ s
      ≤ ∑ x ∈ P.domain, (2 * d : ℝ) ^ (s - 1) * ∑ y ∈ P.domain,
          (if (nearestNeighborGraph d).Adj x y then
            |P.coarsen w x - P.coarsen w y| ^ s else 0) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have h := gradNormIn_rpow_le (nearestNeighborGraph d) P.domain (P.coarsen w) x hs
          (D := 2 * d) (LatticeProb.Graph.Zd.degree_eq x).le
        push_cast at h
        exact h
    _ = (2 * d : ℝ) ^ (s - 1) * ∑ q ∈ P.domain ×ˢ P.domain,
          (if (nearestNeighborGraph d).Adj q.1 q.2 then
            |P.coarsen w q.1 - P.coarsen w q.2| ^ s else 0) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_product]
    _ ≤ (2 * d : ℝ) ^ (s - 1) * ∑ q ∈ P.edgesAcross,
          ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1) *
            ∑ z ∈ P.pairRegion q.1 q.2 ∩ P.cluster, vertexVariation ω P.cluster w z ^ s := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [edgesAcross, Finset.sum_filter]
        refine Finset.sum_le_sum fun q hq => ?_
        rw [Finset.mem_product] at hq
        by_cases hadj : (nearestNeighborGraph d).Adj q.1 q.2
        · by_cases hpart : P.part q.1 = P.part q.2
          · rw [if_pos hadj, if_neg (fun h => h.2 hpart), P.coarsen_congr w hpart, sub_self,
              abs_zero, Real.zero_rpow hs0]
          · rw [if_pos hadj, if_pos ⟨hadj, hpart⟩]
            exact P.abs_coarsen_sub_rpow_le w hs hq.1 hq.2 hadj hpart
        · rw [if_neg hadj, if_neg (fun h => hadj h.1)]
    _ = _ := by
        congr 1
        exact sum_mul_sum_inter_eq P.cluster (fun q => P.pairRegion q.1 q.2) P.edgesAcross
          (fun q => ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1))
          (fun z => vertexVariation ω P.cluster w z ^ s)

/-- **Bounded overlap of the regions of Lemma 3.2**, with constants `K`, `N`, `m`: the region of
`x` has at most `K |□_𝒫(x)|` vertices of the cluster, the partition cube of each of them has scale
at least that of `□_𝒫(x)` minus `m`, and the vertices of the cluster whose region contains a given
vertex lie in at most `N` partition cubes. -/
structure RegionOverlap (K N m : ℕ) : Prop where
  card_region_le : ∀ x ∈ P.cluster,
    (P.region x ∩ P.cluster).card ≤ K * 3 ^ ((P.part x).scale * d)
  scale_le : ∀ x ∈ P.cluster, ∀ z ∈ P.region x ∩ P.cluster,
    (P.part x).scale ≤ (P.part z).scale + m
  card_image_le : ∀ z ∈ P.cluster,
    ((P.cluster.filter fun x => z ∈ P.region x).image P.part).card ≤ N

/-- **Bounded overlap of the regions of Lemma 3.3**, with constants `K`, `N`, `m`: for lattice
neighbours `(x, y)` in different partition cubes, the region has at most `K |□_𝒫(x)|` vertices of
the cluster, the partition cube of each of them has scale at least that of `□_𝒫(x)` minus `m`, and
the pairs whose region contains a given vertex start in at most `N` partition cubes. -/
structure PairOverlap (K N m : ℕ) : Prop where
  card_pairRegion_le : ∀ q ∈ P.edgesAcross,
    (P.pairRegion q.1 q.2 ∩ P.cluster).card ≤ K * 3 ^ ((P.part q.1).scale * d)
  scale_le : ∀ q ∈ P.edgesAcross, ∀ z ∈ P.pairRegion q.1 q.2 ∩ P.cluster,
    (P.part q.1).scale ≤ (P.part z).scale + m
  card_image_le : ∀ z ∈ P.cluster,
    ((P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).image fun q => P.part q.1).card ≤ N

/-- The weight of Lemma 3.2 is at most `N K^{s-1} (3^{n + m})^{ds}`, where `n` is the scale of the
partition cube of `z`. -/
theorem errorWeight_le {K N m : ℕ} (h : P.RegionOverlap K N m) {s : ℝ} (hs : 1 ≤ s)
    {z : Vertex d} (hz : z ∈ P.cluster) :
    P.errorWeight s z ≤
      N * (K : ℝ) ^ (s - 1) * (((3 : ℝ) ^ ((P.part z).scale + m)) ^ d) ^ s := by
  have hs1 : 0 ≤ s - 1 := by linarith
  have hL : (0 : ℝ) < ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d := by positivity
  have hW : P.errorWeight s z = ∑ x ∈ P.cluster.filter (fun x => z ∈ P.region x),
      ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1) := by
    rw [errorWeight, Finset.sum_filter]
  have hsc : ∀ x ∈ P.cluster.filter (fun x => z ∈ P.region x),
      (P.part x).scale ≤ (P.part z).scale + m := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact h.scale_le x hx.1 z (Finset.mem_inter.2 ⟨hx.2, hz⟩)
  have hpow : ∀ x ∈ P.cluster.filter (fun x => z ∈ P.region x),
      ((3 : ℝ) ^ (P.part x).scale) ^ d ≤ ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d := fun x hx =>
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (hsc x hx)) d
  have hc : ∀ x ∈ P.cluster.filter (fun x => z ∈ P.region x),
      ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1) ≤
        ((K : ℝ) * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d) ^ (s - 1) := by
    intro x hx
    have h1 := h.card_region_le x (Finset.mem_filter.1 hx).1
    have h2 : ((P.region x ∩ P.cluster).card : ℝ) ≤
        K * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d := by
      calc ((P.region x ∩ P.cluster).card : ℝ)
          ≤ ((K * 3 ^ ((P.part x).scale * d) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = K * ((3 : ℝ) ^ (P.part x).scale) ^ d := by push_cast; ring
        _ ≤ K * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d :=
            mul_le_mul_of_nonneg_left (hpow x hx) (Nat.cast_nonneg K)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) h2 hs1
  have hfib : ∀ Q ∈ (P.cluster.filter fun x => z ∈ P.region x).image P.part,
      (((P.cluster.filter fun x => z ∈ P.region x).filter fun x => P.part x = Q).card : ℝ) ≤
        ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d := by
    intro Q hQ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hQ
    have hsub : ((P.cluster.filter fun x => z ∈ P.region x).filter
        fun y => P.part y = P.part x) ⊆ (P.part x).toIntegerCube.vertices := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [TriadicCube.mem_toIntegerCube_vertices, ← hy.2]
      exact P.mem_part y (P.cluster_subset (Finset.mem_filter.1 hy.1).1)
    have h1 := Finset.card_le_card hsub
    rw [IntegerCube.card_vertices_eq] at h1
    calc (((P.cluster.filter fun x => z ∈ P.region x).filter
          fun y => P.part y = P.part x).card : ℝ)
        ≤ (((P.part x).toIntegerCube.size ^ d : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((3 : ℝ) ^ (P.part x).scale) ^ d := by
          simp only [TriadicCube.toIntegerCube, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ _ := hpow x hx
  rw [hW]
  refine (sum_le_of_fibres _ P.part _ hc (by positivity) hfib (h.card_image_le z hz)
    hL.le).trans (le_of_eq ?_)
  rw [mul_assoc (N : ℝ), mul_mul_rpow_sub_one hL (Nat.cast_nonneg K) s]
  ring

/-- The weight of Lemma 3.3 is at most `2d N K^{s-1} (3^{n + m})^{sd - 1}`, where `n` is the scale
of the partition cube of `z`. -/
theorem gradWeight_le {K N m : ℕ} (h : P.PairOverlap K N m) (hd : 1 ≤ d) {s : ℝ} (hs : 1 ≤ s)
    {z : Vertex d} (hz : z ∈ P.cluster) :
    P.gradWeight s z ≤
      2 * d * N * (K : ℝ) ^ (s - 1) * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ (s * d - 1) := by
  have hs1 : 0 ≤ s - 1 := by linarith
  have hb : (0 : ℝ) < (3 : ℝ) ^ ((P.part z).scale + m) := by positivity
  have hW : P.gradWeight s z = ∑ q ∈ P.edgesAcross.filter (fun q => z ∈ P.pairRegion q.1 q.2),
      ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1) := by
    rw [gradWeight, Finset.sum_filter]
  have hsc : ∀ q ∈ P.edgesAcross.filter (fun q => z ∈ P.pairRegion q.1 q.2),
      (P.part q.1).scale ≤ (P.part z).scale + m := fun q hq =>
    h.scale_le q (Finset.mem_filter.1 hq).1 z
      (Finset.mem_inter.2 ⟨(Finset.mem_filter.1 hq).2, hz⟩)
  have hc : ∀ q ∈ P.edgesAcross.filter (fun q => z ∈ P.pairRegion q.1 q.2),
      ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1) ≤
        ((K : ℝ) * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d) ^ (s - 1) := by
    intro q hq
    have h1 := h.card_pairRegion_le q (Finset.mem_filter.1 hq).1
    have h2 : ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ≤
        K * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d := by
      calc ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ)
          ≤ ((K * 3 ^ ((P.part q.1).scale * d) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = K * ((3 : ℝ) ^ (P.part q.1).scale) ^ d := by push_cast; ring
        _ ≤ K * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
              (pow_le_pow_right₀ (by norm_num) (hsc q hq)) d) (Nat.cast_nonneg K)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) h2 hs1
  have hfib : ∀ Q ∈ (P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).image
      (fun q => P.part q.1),
      (((P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).filter
        fun q => P.part q.1 = Q).card : ℝ) ≤
        2 * d * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ (d - 1) := by
    intro Q hQ
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.1 hQ
    have hsub : ((P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).filter
        fun q => P.part q.1 = P.part q₀.1) ⊆
        ((P.part q₀.1).toIntegerCube.vertices ×ˢ P.domain).filter fun q =>
          (nearestNeighborGraph d).Adj q.1 q.2 ∧ q.2 ∉ (P.part q₀.1).vertices := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqF, hpart⟩ := hq
      have hqE := (Finset.mem_filter.1 hqF).1
      rw [edgesAcross, Finset.mem_filter, Finset.mem_product] at hqE
      obtain ⟨⟨hx, hy⟩, hadj, hne⟩ := hqE
      rw [Finset.mem_filter, Finset.mem_product, TriadicCube.mem_toIntegerCube_vertices,
        ← hpart]
      exact ⟨⟨P.mem_part _ hx, hy⟩, hadj, fun hmem => hne (P.part_eq_of_mem _ hx _ hmem).symm⟩
    have h1 := (Finset.card_le_card hsub).trans ((P.part q₀.1).card_exitPairs_le P.domain)
    calc (((P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).filter
          fun q => P.part q.1 = P.part q₀.1).card : ℝ)
        ≤ ((2 * d * 3 ^ ((P.part q₀.1).scale * (d - 1)) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = 2 * d * ((3 : ℝ) ^ (P.part q₀.1).scale) ^ (d - 1) := by push_cast; ring
      _ ≤ 2 * d * ((3 : ℝ) ^ ((P.part z).scale + m)) ^ (d - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
            (pow_le_pow_right₀ (by norm_num) (hsc q₀ hq₀)) _) (by positivity)
  rw [hW]
  refine (sum_le_of_fibres _ (fun q => P.part q.1) _ hc (by positivity) hfib
    (h.card_image_le z hz) (by positivity)).trans (le_of_eq ?_)
  rw [mul_assoc (N : ℝ), mul_assoc (2 * (d : ℝ)), pow_mul_rpow_sub_one hb (Nat.cast_nonneg K) hd s]
  ring

/-- **Armstrong and Dario, Lemma 3.2** (coarsening error), for `1 ≤ s < ∞`:
`∑_{x ∈ C_*(U)} |w(x) - [w]_𝒫(x)|^s ≤ C^s ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{sd} |∇w 1_{a≠0}|^s(z)`
with `C = N K 3^{md} 2√d`, under bounded overlap of the regions. -/
theorem sum_abs_sub_coarsen_rpow_le {K N m : ℕ} (h : P.RegionOverlap K N m) (hK : 1 ≤ K)
    (hN : 1 ≤ N) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤
      ((N : ℝ) * K * 3 ^ (m * d) * (2 * √(d : ℝ))) ^ s *
        ∑ z ∈ P.cluster, ((3 : ℝ) ^ (P.part z).scale) ^ (s * d) *
          gradNormIn (openGraph ω) P.cluster w z ^ s := by
  refine (P.sum_abs_sub_coarsen_rpow_le_errorWeight w hs).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have hg := gradNormIn_nonneg (openGraph ω) P.cluster w z
  have hV : vertexVariation ω P.cluster w z ^ s ≤
      (2 * √(d : ℝ) * gradNormIn (openGraph ω) P.cluster w z) ^ s :=
    Real.rpow_le_rpow (vertexVariation_nonneg _ _ _ _)
      (vertexVariation_le_gradNormIn ω P.cluster w z) (by linarith)
  have hW := P.errorWeight_le h hs hz
  have hsplit : ((3 : ℝ) ^ ((P.part z).scale + m)) ^ d =
      (3 : ℝ) ^ (m * d) * ((3 : ℝ) ^ (P.part z).scale) ^ d := by
    ring
  rw [hsplit] at hW
  have hA : ((3 : ℝ) ^ (P.part z).scale) ^ (s * d) =
      (((3 : ℝ) ^ (P.part z).scale) ^ d) ^ s := by
    rw [mul_comm s, Real.rpow_mul (x := (3 : ℝ) ^ (P.part z).scale) (by positivity),
      Real.rpow_natCast]
  rw [hA]
  exact coarse_const_le hs (by exact_mod_cast hN) (by exact_mod_cast hK) (by positivity)
    (by positivity) (by positivity) hg hW (Real.rpow_nonneg (vertexVariation_nonneg _ _ _ _) _)
    hV

/-- **Armstrong and Dario, Lemma 3.3** (coarse gradients), for `1 ≤ s < ∞`:
`∑_{x ∈ cl_𝒫(U)} |∇[w]_𝒫|^s(x) ≤ C^s ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{sd-1} |∇w 1_{a≠0}|^s(z)`
with `C = 2d N K 3^{md} 2√d`, under bounded overlap of the pair regions. -/
theorem sum_gradNormIn_coarsen_rpow_le {K N m : ℕ} (h : P.PairOverlap K N m) (hK : 1 ≤ K)
    (hN : 1 ≤ N) (hd : 1 ≤ d) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ s ≤
      (2 * (d : ℝ) * N * K * 3 ^ (m * d) * (2 * √(d : ℝ))) ^ s *
        ∑ z ∈ P.cluster, ((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1) *
          gradNormIn (openGraph ω) P.cluster w z ^ s := by
  refine (P.sum_gradNormIn_coarsen_rpow_le_gradWeight w hs).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have hg := gradNormIn_nonneg (openGraph ω) P.cluster w z
  have hV : vertexVariation ω P.cluster w z ^ s ≤
      (2 * √(d : ℝ) * gradNormIn (openGraph ω) P.cluster w z) ^ s :=
    Real.rpow_le_rpow (vertexVariation_nonneg _ _ _ _)
      (vertexVariation_le_gradNormIn ω P.cluster w z) (by linarith)
  have hW := P.gradWeight_le h hd hs hz
  have h3m : ((3 : ℝ) ^ m) ^ (s * d - 1) ≤ ((3 : ℝ) ^ (m * d)) ^ s := by
    calc ((3 : ℝ) ^ m) ^ (s * d - 1) ≤ ((3 : ℝ) ^ m) ^ (s * d) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
      _ = ((3 : ℝ) ^ (m * d)) ^ s := by
          rw [mul_comm s, Real.rpow_mul (x := (3 : ℝ) ^ m) (by positivity), Real.rpow_natCast,
            ← pow_mul]
  have hsplit : ((3 : ℝ) ^ ((P.part z).scale + m)) ^ (s * d - 1) ≤
      ((3 : ℝ) ^ (m * d)) ^ s * ((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1) := by
    rw [pow_add, Real.mul_rpow (x := (3 : ℝ) ^ (P.part z).scale) (y := (3 : ℝ) ^ m)
      (by positivity) (by positivity)]
    calc ((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1) * ((3 : ℝ) ^ m) ^ (s * d - 1)
        ≤ ((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1) * ((3 : ℝ) ^ (m * d)) ^ s :=
          mul_le_mul_of_nonneg_left h3m (by positivity)
      _ = _ := mul_comm _ _
  have hW' : P.gradWeight s z ≤ 2 * d * N * (K : ℝ) ^ (s - 1) *
      (((3 : ℝ) ^ (m * d)) ^ s * ((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1)) :=
    hW.trans (mul_le_mul_of_nonneg_left hsplit (by positivity))
  have hd0 : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact coarse_const_le' (D := 2 * d) hs (by exact_mod_cast hN) (by exact_mod_cast hK)
    (by positivity) (by positivity) (by positivity) hg hd0 hW'
    (Real.rpow_nonneg (vertexVariation_nonneg _ _ _ _) _) hV

end CoarseData

end Rigidity.Percolation

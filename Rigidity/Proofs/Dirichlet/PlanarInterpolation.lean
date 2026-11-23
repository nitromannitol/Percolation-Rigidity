import Rigidity.Proofs.Dirichlet.PlanarStatements
import Rigidity.Proofs.Cluster.PlanarCoarseReach
import Rigidity.Proofs.Dirichlet.Interpolation

/-!
# Lemma 6.4 (iii) for the planar partition

For the coarse-graining data of a resolved planar cube `U` (`planarCoarseData`), the regions of
Lemmas 3.2 and 3.3 are windows inside the squares of side `9s` around the partition cubes, so
Lemmas 3.2 and 3.3 hold with the reach scales `ρ`, `ρ'` in place of the sizes of the partition
cubes (`planar_sum_abs_sub_coarseAnchor_rpow_le`, `planar_sum_gradNormIn_coarseAnchor_rpow_le`).
With the weighted Hölder inequality, the normalized `L^s` norm of the gradient of the boundary
interpolation `w̃` is at most
`3^{s-1} (2 · 2^{s/2} C₃^s 𝔐'_{2s-1} + 4 C₂^s 𝔐_{2s}) (V⁻¹ Σ_{C_*(U)} |∇u 1_{a≠0}|^p)^{s/p}`,
with `𝔐_a = (V⁻¹ Σ_z (3^{ρ(z)})^{a p/(p-s)})^{1-s/p}` and `𝔐'` the same with `ρ'`
(`planar_sum_abs_grad_boundaryInterpolation_rpow_div_le`), the planar form of Armstrong and Dario,
Lemma 6.4 (iii). The moments of the reach scales are bounded by those of the partition sizes:
`Σ_z (3^{ρ(z)})^t ≤ 81 Σ_{x ∈ C_*(U)} (3^{s(x)})^{t + 2}`, since the reach scale at `z` is the
largest scale of a partition cube whose window contains `z`, and the window of the partition cube
of `x` has at most `81 · 9^{s(x)}` vertices (`sum_three_pow_reachScale_rpow_le`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- The constant of the planar Lemma 3.2 with exponent `s`. -/
noncomputable def planarConstTwo : ℝ :=
  3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))

/-- The constant of the planar Lemma 3.3 with exponent `s`. -/
noncomputable def planarConstThree : ℝ :=
  2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
    (2 * √((2 : ℕ) : ℝ))

theorem planarConstTwo_nonneg : 0 ≤ planarConstTwo := by unfold planarConstTwo; positivity

theorem planarConstThree_nonneg : 0 ≤ planarConstThree := by unfold planarConstThree; positivity

/-- The right side of the planar Lemma 6.4 (iii): the moments of the reach scales times the
normalized `L^p` norm of the open gradient of `u` to the power `s/p`. -/
noncomputable def planarInterpolationBound (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (hU : PlanarResolved ω U) (s p V : ℝ) (u : Vertex 2 → ℝ) : ℝ :=
  (3 : ℝ) ^ (s - 1) * (((2 : ℕ) : ℝ) * (2 : ℝ) ^ (s / 2) * planarConstThree ^ s *
      ((∑ z ∈ clusterVertices ω U,
        (((3 : ℝ) ^ (planarCoarseData hP U hU).pairReachScale z) ^ (s * ((2 : ℕ) : ℝ) - 1)) ^
          (p / (p - s))) / V) ^ (1 - s / p) +
    2 * ((2 : ℕ) : ℝ) * planarConstTwo ^ s *
      ((∑ z ∈ clusterVertices ω U,
        (((3 : ℝ) ^ (planarCoarseData hP U hU).reachScale z) ^ (s * ((2 : ℕ) : ℝ))) ^
          (p / (p - s))) / V) ^ (1 - s / p)) *
    ((∑ z ∈ clusterVertices ω U,
      gradNormIn (openGraph ω) (clusterVertices ω U) u z ^ p) / V) ^ (s / p)

/-- **Armstrong and Dario, Lemma 6.4 (iii), for the planar partition.** -/
theorem planar_sum_abs_grad_boundaryInterpolation_rpow_div_le (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) {B : Finset (Vertex 2)}
    (hB : B ⊆ clusterVertices ω U) (u : Vertex 2 → ℝ) {s p : ℝ} (hs : 1 ≤ s) (hsp : s < p)
    {V : ℝ} (hV : 0 < V) :
    (∑ x ∈ U.toIntegerCube.vertices, ∑ j : Fin 2, (if x + unit j ∈ U.toIntegerCube.vertices then
        |boundaryInterpolation (planarCoarseData hP U hU) B u (x + unit j) -
          boundaryInterpolation (planarCoarseData hP U hU) B u x| ^ s else 0)) / V ≤
      planarInterpolationBound hP U hU s p V u := by
  set P := planarCoarseData hP U hU with hPdef
  have hs0 : 0 < s := by linarith
  set G : Vertex 2 → ℝ := fun z => gradNormIn (openGraph ω) (clusterVertices ω U) u z
  have hG : ∀ z, 0 ≤ G z := fun z => gradNormIn_nonneg _ _ _ _
  have hGabs : ∀ z (t : ℝ), |G z| ^ t = G z ^ t := fun z t => by rw [abs_of_nonneg (hG z)]
  have hstep := sum_abs_grad_boundaryInterpolation_rpow_le P hB u hs
  have hL3 := planar_sum_gradNormIn_coarseAnchor_rpow_le hP hU u hs
  have hL2 := planar_sum_abs_sub_coarseAnchor_rpow_le hP hU u hs
  have hW3 := sum_mul_rpow_div_le (clusterVertices ω U)
    (fun z => ((3 : ℝ) ^ P.pairReachScale z) ^ (s * ((2 : ℕ) : ℝ) - 1))
    G (fun z _ => by positivity) hs0 hsp hV
  have hW2 := sum_mul_rpow_div_le (clusterVertices ω U)
    (fun z => ((3 : ℝ) ^ P.reachScale z) ^ (s * ((2 : ℕ) : ℝ)))
    G (fun z _ => by positivity) hs0 hsp hV
  simp only [hGabs] at hW3 hW2
  set C₃ : ℝ := planarConstThree ^ s
  set C₂ : ℝ := planarConstTwo ^ s
  set S₃ : ℝ := ∑ z ∈ clusterVertices ω U,
    ((3 : ℝ) ^ P.pairReachScale z) ^ (s * ((2 : ℕ) : ℝ) - 1) * G z ^ s
  set S₂ : ℝ := ∑ z ∈ clusterVertices ω U,
    ((3 : ℝ) ^ P.reachScale z) ^ (s * ((2 : ℕ) : ℝ)) * G z ^ s
  have hC₃ : 0 ≤ C₃ := Real.rpow_nonneg planarConstThree_nonneg _
  have hC₂ : 0 ≤ C₂ := Real.rpow_nonneg planarConstTwo_nonneg _
  have h3s : 0 ≤ (3 : ℝ) ^ (s - 1) := by positivity
  have hA : 0 ≤ ((2 : ℕ) : ℝ) * (2 : ℝ) ^ (s / 2) := by positivity
  have hL3' : ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph 2) P.domain (P.coarsen u) x ^ s ≤
      C₃ * S₃ := hL3
  have hL2' : ∑ z ∈ P.cluster, |u z - P.coarsen u z| ^ s ≤ C₂ * S₂ := hL2
  unfold planarInterpolationBound
  calc (∑ x ∈ U.toIntegerCube.vertices, ∑ j : Fin 2, (if x + unit j ∈ U.toIntegerCube.vertices then
        |boundaryInterpolation P B u (x + unit j) - boundaryInterpolation P B u x| ^ s else 0)) / V
      ≤ (3 : ℝ) ^ (s - 1) * (((2 : ℕ) : ℝ) * (2 : ℝ) ^ (s / 2) * (C₃ * S₃) +
          2 * ((2 : ℕ) : ℝ) * (C₂ * S₂)) / V := by
        refine div_le_div_of_nonneg_right (hstep.trans ?_) hV.le
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) h3s
        · exact mul_le_mul_of_nonneg_left hL3' hA
        · exact mul_le_mul_of_nonneg_left hL2' (by positivity)
    _ = (3 : ℝ) ^ (s - 1) * (((2 : ℕ) : ℝ) * (2 : ℝ) ^ (s / 2) * C₃ * (S₃ / V) +
          2 * ((2 : ℕ) : ℝ) * C₂ * (S₂ / V)) := by
        field_simp
    _ ≤ _ := by
        rw [mul_assoc ((3 : ℝ) ^ (s - 1))]
        refine mul_le_mul_of_nonneg_left ?_ h3s
        rw [add_mul]
        refine add_le_add ?_ ?_
        · rw [mul_assoc (((2 : ℕ) : ℝ) * (2 : ℝ) ^ (s / 2) * C₃)]
          exact mul_le_mul_of_nonneg_left hW3 (by positivity)
        · rw [mul_assoc (2 * ((2 : ℕ) : ℝ) * C₂)]
          exact mul_le_mul_of_nonneg_left hW2 (by positivity)

/-- **Moments of the reach scale** by the moments of the partition sizes:
`Σ_{z ∈ C_*(U)} (3^{ρ(z)})^t ≤ 81 Σ_{x ∈ U} (3^{s(x)})^{t+2}`. -/
theorem sum_three_pow_reachScale_rpow_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (t : ℝ) :
    ∑ z ∈ clusterVertices ω U, ((3 : ℝ) ^ (planarCoarseData hP U hU).reachScale z) ^ t ≤
      81 * ∑ x ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (t + 2) := by
  set P := planarCoarseData hP U hU
  set C := clusterVertices ω U
  set g : Vertex 2 → ℝ := fun x => ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ t with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hpt : ∀ z ∈ C, ((3 : ℝ) ^ P.reachScale z) ^ t ≤
      ∑ x ∈ C, (if z ∈ P.region x then g x else 0) := by
    intro z hz
    have hne : (C.filter fun x => z ∈ P.region x).Nonempty :=
      ⟨z, Finset.mem_filter.2 ⟨hz, P.mem_region_self hz⟩⟩
    obtain ⟨x, hx, hxmax⟩ := Finset.exists_mem_eq_sup _ hne (fun x => (P.part x).scale)
    have e : P.reachScale z = (planarPartCube ω x).scale := hxmax
    rw [e, ← Finset.sum_filter]
    exact Finset.single_le_sum (f := g) (fun y _ => hg0 y) hx
  have hcard : ∀ x ∈ C, ((C.filter fun z => z ∈ P.region x).card : ℝ) ≤
      81 * (3 : ℝ) ^ ((planarPartCube ω x).scale * 2) := by
    intro x hx
    have hsub : C.filter (fun z => z ∈ P.region x) ⊆ ((planarPartCube ω x).thicken 4).vertices :=
      fun z hz => planarClusterWindow_subset_thicken hP hU (mem_clusterVertices.1 hx).1
        (Finset.mem_filter.1 hz).2
    have h := Finset.card_le_card hsub
    rw [TriadicCube.card_thicken] at h
    have h' : ((C.filter fun z => z ∈ P.region x).card : ℝ) ≤
        ((2 * 4 + 1) ^ 2 * 3 ^ ((planarPartCube ω x).scale * 2) : ℕ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hCU : C ⊆ U.toIntegerCube.vertices := Finset.filter_subset _ _
  calc ∑ z ∈ C, ((3 : ℝ) ^ P.reachScale z) ^ t
      ≤ ∑ z ∈ C, ∑ x ∈ C, (if z ∈ P.region x then g x else 0) := Finset.sum_le_sum hpt
    _ = ∑ x ∈ C, g x * ((C.filter fun z => z ∈ P.region x).card : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ C, g x * (81 * (3 : ℝ) ^ ((planarPartCube ω x).scale * 2)) :=
        Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hcard x hx) (hg0 x)
    _ = 81 * ∑ x ∈ C, ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (t + 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hg, Real.rpow_add (by positivity), Real.rpow_two, ← pow_mul]
        ring
    _ ≤ 81 * ∑ x ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (t + 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hCU
          fun _ _ _ => by positivity) (by norm_num)

/-- **Moments of the pair reach scale** by the moments of the partition sizes:
`Σ_{z ∈ C_*(U)} (3^{ρ'(z)})^t ≤ |C_*(U)| + 324 Σ_{x ∈ U} (3^{s(x)})^{t+2}`. -/
theorem sum_three_pow_pairReachScale_rpow_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (t : ℝ) :
    ∑ z ∈ clusterVertices ω U, ((3 : ℝ) ^ (planarCoarseData hP U hU).pairReachScale z) ^ t ≤
      (clusterVertices ω U).card + 324 * ∑ x ∈ U.toIntegerCube.vertices,
        ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (t + 2) := by
  set P := planarCoarseData hP U hU
  set C := clusterVertices ω U
  set g : Vertex 2 → ℝ := fun x => ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ t with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hpt : ∀ z ∈ C, ((3 : ℝ) ^ P.pairReachScale z) ^ t ≤
      1 + ∑ q ∈ P.edgesAcross, (if z ∈ P.pairRegion q.1 q.2 then g q.1 else 0) := by
    intro z _
    by_cases hne : (P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).Nonempty
    · obtain ⟨q, hq, hqmax⟩ := Finset.exists_mem_eq_sup _ hne (fun q => (P.part q.1).scale)
      have e : P.pairReachScale z = (planarPartCube ω q.1).scale := hqmax
      rw [e, ← Finset.sum_filter]
      have h1 : ((3 : ℝ) ^ (planarPartCube ω q.1).scale) ^ t ≤
          ∑ q' ∈ P.edgesAcross.filter (fun q => z ∈ P.pairRegion q.1 q.2), g q'.1 :=
        Finset.single_le_sum (f := fun q' : Vertex 2 × Vertex 2 => g q'.1)
          (fun y _ => hg0 y.1) hq
      linarith
    · have e : P.pairReachScale z = 0 := by
        unfold CoarseData.pairReachScale
        rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sup_empty]
        rfl
      rw [e, pow_zero, Real.one_rpow]
      have : 0 ≤ ∑ q ∈ P.edgesAcross, (if z ∈ P.pairRegion q.1 q.2 then g q.1 else 0) :=
        Finset.sum_nonneg fun q _ => by split_ifs <;> [exact hg0 _; exact le_rfl]
      linarith
  have hcard : ∀ q ∈ P.edgesAcross, ((C.filter fun z => z ∈ P.pairRegion q.1 q.2).card : ℝ) ≤
      81 * (3 : ℝ) ^ ((planarPartCube ω q.1).scale * 2) := by
    intro q hq
    have hq' : q ∈ (planarCoarseData hP U hU).edgesAcross := hq
    simp only [CoarseData.edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
    obtain ⟨⟨hx, hy⟩, hadj, -⟩ := hq'
    have hsub : C.filter (fun z => z ∈ P.pairRegion q.1 q.2) ⊆
        ((planarPartCube ω q.1).thicken 4).vertices :=
      fun z hz => planarClusterPairRegion_subset_thicken hP hU
        ((U.mem_toIntegerCube_vertices _).1 hx) ((U.mem_toIntegerCube_vertices _).1 hy) hadj
        (Finset.mem_filter.1 hz).2
    have h := Finset.card_le_card hsub
    rw [TriadicCube.card_thicken] at h
    have h' : ((C.filter fun z => z ∈ P.pairRegion q.1 q.2).card : ℝ) ≤
        ((2 * 4 + 1) ^ 2 * 3 ^ ((planarPartCube ω q.1).scale * 2) : ℕ) := by exact_mod_cast h
    push_cast at h'
    linarith
  -- each vertex starts at most four edges
  have hE : ∀ h : Vertex 2 → ℝ, (∀ x, 0 ≤ h x) → ∑ q ∈ P.edgesAcross, h q.1 ≤ 4 * ∑ x ∈ U.toIntegerCube.vertices, h x := by
    intro h hh
    have hsub : P.edgesAcross ⊆ (U.toIntegerCube.vertices ×ˢ U.toIntegerCube.vertices).filter fun q => (nearestNeighborGraph 2).Adj q.1 q.2 :=
      fun q hq => by
        have hq' : q ∈ (planarCoarseData hP U hU).edgesAcross := hq
        simp only [CoarseData.edgesAcross, Finset.mem_filter] at hq'
        exact Finset.mem_filter.2 ⟨hq'.1, hq'.2.1⟩
    have hdeg : ∀ x, ((U.toIntegerCube.vertices.filter fun y => (nearestNeighborGraph 2).Adj x y).card : ℝ) ≤ 4 := by
      intro x
      have hnb : U.toIntegerCube.vertices.filter (fun y => (nearestNeighborGraph 2).Adj x y) ⊆
          (nearestNeighborGraph 2).neighborFinset x :=
        fun y hy => (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hy).2
      have h1 := (Finset.card_le_card hnb).trans
        ((SimpleGraph.card_neighborFinset_eq_degree _ _).le.trans
          (Graph.Zd.degree_eq (d := 2) x).le)
      have : ((U.toIntegerCube.vertices.filter fun y => (nearestNeighborGraph 2).Adj x y).card : ℝ) ≤ ((2 * 2 : ℕ) : ℝ) :=
        by exact_mod_cast h1
      norm_num at this
      exact_mod_cast this
    calc ∑ q ∈ P.edgesAcross, h q.1
        ≤ ∑ q ∈ (U.toIntegerCube.vertices ×ˢ U.toIntegerCube.vertices).filter (fun q => (nearestNeighborGraph 2).Adj q.1 q.2), h q.1 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hh q.1
      _ = ∑ x ∈ U.toIntegerCube.vertices, ((U.toIntegerCube.vertices.filter fun y => (nearestNeighborGraph 2).Adj x y).card : ℝ) * h x := by
          rw [Finset.sum_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          dsimp only
          split_ifs <;> simp
      _ ≤ ∑ x ∈ U.toIntegerCube.vertices, 4 * h x :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hdeg x) (hh x)
      _ = 4 * ∑ x ∈ U.toIntegerCube.vertices, h x := (Finset.mul_sum _ _ _).symm
  calc ∑ z ∈ C, ((3 : ℝ) ^ P.pairReachScale z) ^ t
      ≤ ∑ z ∈ C, (1 + ∑ q ∈ P.edgesAcross, (if z ∈ P.pairRegion q.1 q.2 then g q.1 else 0)) :=
        Finset.sum_le_sum hpt
    _ = C.card + ∑ q ∈ P.edgesAcross, g q.1 * ((C.filter fun z => z ∈ P.pairRegion q.1 q.2).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ C.card + ∑ q ∈ P.edgesAcross, 81 * ((3 : ℝ) ^ (planarPartCube ω q.1).scale) ^ (t + 2) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun q hq => ?_)
        calc g q.1 * ((C.filter fun z => z ∈ P.pairRegion q.1 q.2).card : ℝ)
            ≤ g q.1 * (81 * (3 : ℝ) ^ ((planarPartCube ω q.1).scale * 2)) :=
              mul_le_mul_of_nonneg_left (hcard q hq) (hg0 _)
          _ = 81 * ((3 : ℝ) ^ (planarPartCube ω q.1).scale) ^ (t + 2) := by
              rw [hg, Real.rpow_add (by positivity), Real.rpow_two, ← pow_mul]
              ring
    _ ≤ C.card + 4 * ∑ x ∈ U.toIntegerCube.vertices, 81 * ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (t + 2) :=
        add_le_add le_rfl (hE (fun x => 81 * ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (t + 2))
          fun x => mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
    _ = C.card + 324 * ∑ x ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (t + 2) := by
        rw [← Finset.mul_sum]
        ring

end Rigidity.Dirichlet

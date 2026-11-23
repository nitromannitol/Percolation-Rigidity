import Rigidity.Proofs.Regularity.PlanarCoarseComparisonTwo
import Rigidity.Proofs.Cluster.SobolevMeanZero

/-!
# The bound of the coarsened function on a planar square (Step 2 of Lemma 7.1)

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, Step 2, with `w = a` a constant, on
the squares `□_j` of the plane: for `u` harmonic on the cluster,
`‖[u]_𝒫 - a‖_{L̲²(□_j)} ≤ K ‖u - a‖_{L̲²(C_*(□_{j+3}))}`.
In place of the Sobolev step in `L^{p'}` of the paper the proof splits `[u]_𝒫 - a` into
`[u]_𝒫 - m`, with `m` the mean of `[u]_𝒫` on `□_j`, and `m - a`:

* `sum_sq_coarse_sub_mean_le`: the Poincaré inequality on `□_j`
  (`IntegerCube.sum_abs_sub_mean_rpow_le`), Lemma 3.3 with the pair reach scales
  (`planar_sum_gradNormIn_coarseAnchor_rpow_le`), the Hölder inequality with the Meyers estimate
  and the moments of the pair reach scales, and the Caccioppoli inequality bound `[u]_𝒫 - m`;
* `squareL2_coarse_sub_le`: averaging `m - a = (m - [u]_𝒫) + ([u]_𝒫 - u) + (u - a)` over the
  cluster `C_*(□_j)`, which carries a fixed proportion of `□_j`, bounds `m - a` by the first part,
  the comparison (7.8) and `u - a`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical ENNReal

variable {ω : Configuration 2}

theorem toIntegerCube_vertices_zero (j : ℕ) :
    (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices = triadicCubeFinset 2 j 0 := by
  ext x
  rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_zero_iff, mem_square_iff_int]

theorem card_square_eq (j : ℕ) : ((triadicCubeFinset 2 j 0).card : ℝ) = 9 ^ j := by
  rw [card_triadicCubeFinset]
  push_cast
  rw [pow_mul]
  norm_num

/-- The scale of the partition cube of a vertex is bounded by the reach. -/
theorem three_pow_planarPartCube_scale_le_planarReach (hP : PlanarPartitionEvent ω)
    (z : Vertex 2) : (3 : ℝ≥0∞) ^ (planarPartCube ω z).scale ≤ planarReach ω z := by
  unfold planarReach
  refine le_iSup₂ (f := fun (Q : TriadicCube 2) (_ : Q.IsMaximalStopping (planarGoodCubes ω) ∧
    z ∈ (↑Q.ninefold.vertices : Set (Vertex 2))) => (3 : ℝ≥0∞) ^ Q.scale) (planarPartCube ω z)
    ⟨(planarPartCube_spec hP z).2, ?_⟩
  rw [TriadicCube.mem_ninefold]
  intro i
  have h1 := (planarPartCube ω z).abs_sub_center_le (planarPartCube_spec hP z).1 i
  have h2 := (planarPartCube ω z).two_mul_ninefoldRadius
  have hpos : (1 : ℤ) ≤ 3 ^ (planarPartCube ω z).scale := one_le_pow₀ (by norm_num)
  omega

/-- The pair reach scale of the planar coarse-graining data is bounded by the reach of the
partition. -/
theorem three_pow_pairReachScale_le_planarReach (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (z : Vertex 2) :
    (3 : ℝ≥0∞) ^ (planarCoarseData hP U hU).pairReachScale z ≤ planarReach ω z := by
  unfold CoarseData.pairReachScale
  rcases Finset.eq_empty_or_nonempty ((planarCoarseData hP U hU).edgesAcross.filter
      fun q => z ∈ (planarCoarseData hP U hU).pairRegion q.1 q.2) with h | h
  · rw [h, Finset.sup_empty]
    exact (one_le_pow₀ (by norm_num)).trans (three_pow_planarPartCube_scale_le_planarReach hP z)
  · obtain ⟨q, hq, hqsup⟩ := Finset.exists_mem_eq_sup _ h
      (fun q => ((planarCoarseData hP U hU).part q.1).scale)
    rw [hqsup]
    obtain ⟨hqe, hzq⟩ := Finset.mem_filter.1 hq
    have hq' := hqe
    rw [CoarseData.edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
    obtain ⟨⟨hx, hy⟩, hadj, -⟩ := hq'
    change q.1 ∈ U.toIntegerCube.vertices at hx
    change q.2 ∈ U.toIntegerCube.vertices at hy
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx hy
    have hzw : z ∈ ((planarPartCube ω q.1).thicken 4).vertices :=
      planarClusterPairRegion_subset_thicken hP hU hx hy hadj hzq
    rw [← TriadicCube.ninefold_vertices_eq_thicken] at hzw
    unfold planarReach
    exact le_iSup₂ (f := fun (Q : TriadicCube 2) (_ : Q.IsMaximalStopping (planarGoodCubes ω) ∧
      z ∈ (↑Q.ninefold.vertices : Set (Vertex 2))) => (3 : ℝ≥0∞) ^ Q.scale) (planarPartCube ω q.1)
      ⟨(planarPartCube_spec hP q.1).2, Finset.mem_coe.2 hzw⟩

/-- **Moments of scales bounded by the reach** on the cluster of `□_j`, from the moments of the
reach on the triadic cube of scale `j`. -/
theorem sum_rpow_le_of_le_planarReach {j : ℕ} (ρ : Vertex 2 → ℕ)
    (hρ : ∀ z, (3 : ℝ≥0∞) ^ ρ z ≤ planarReach ω z) {τ K : ℝ} (hτ : 0 < τ) (hK : 0 ≤ K)
    (hfin : ∀ x ∈ cube j (0 : Vertex 2), planarReach ω x ≠ ⊤)
    (hsum : ∑ x ∈ cube j (0 : Vertex 2), planarReach ω x ^ ⌈τ⌉₊ ≤
      ENNReal.ofReal (K * (cube j (0 : Vertex 2)).card)) :
    ∑ z ∈ clusterVertices ω ⟨j, 0⟩, ((3 : ℝ) ^ ρ z) ^ τ ≤ K * 9 ^ j := by
  have hcube : ((cube j (0 : Vertex 2)).card : ℝ) = 9 ^ j := by
    rw [card_cube, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have hpt : ∀ z ∈ clusterVertices ω ⟨j, 0⟩,
      ((3 : ℝ) ^ ρ z) ^ τ ≤ (planarReach ω z).toReal ^ ⌈τ⌉₊ := by
    intro z hz
    have hzc : z ∈ cube j (0 : Vertex 2) :=
      mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz)
    have hle' : (3 : ℝ) ^ ρ z ≤ (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono (hfin z hzc) (hρ z)
      simpa using this
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ ρ z := one_le_pow₀ (by norm_num)
    calc ((3 : ℝ) ^ ρ z) ^ τ
        ≤ (planarReach ω z).toReal ^ τ := Real.rpow_le_rpow (by positivity) hle' hτ.le
      _ ≤ (planarReach ω z).toReal ^ (⌈τ⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (h1.trans hle') (Nat.le_ceil τ)
      _ = (planarReach ω z).toReal ^ ⌈τ⌉₊ := Real.rpow_natCast _ _
  have hsub : clusterVertices ω ⟨j, 0⟩ ⊆ cube j (0 : Vertex 2) :=
    fun z hz => mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz)
  calc ∑ z ∈ clusterVertices ω ⟨j, 0⟩, ((3 : ℝ) ^ ρ z) ^ τ
      ≤ ∑ z ∈ clusterVertices ω ⟨j, 0⟩, (planarReach ω z).toReal ^ ⌈τ⌉₊ :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ z ∈ cube j (0 : Vertex 2), (planarReach ω z).toReal ^ ⌈τ⌉₊ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (∑ z ∈ cube j (0 : Vertex 2), planarReach ω z ^ ⌈τ⌉₊).toReal := by
        rw [ENNReal.toReal_sum fun z hz => ENNReal.pow_ne_top (hfin z hz)]
        exact Finset.sum_congr rfl fun z _ => (ENNReal.toReal_pow _ _).symm
    _ ≤ (ENNReal.ofReal (K * (cube j (0 : Vertex 2)).card)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    _ = K * 9 ^ j := by
        rw [ENNReal.toReal_ofReal (by positivity), hcube]

/-- **The Poincaré inequality on `□_j`**. -/
theorem sum_sq_sub_mean_square_le (j : ℕ) (f : Vertex 2 → ℝ) :
    ∑ x ∈ triadicCubeFinset 2 j 0, (f x - (∑ y ∈ triadicCubeFinset 2 j 0, f y) / 9 ^ j) ^ 2 ≤
      8 * 9 ^ j * ∑ x ∈ triadicCubeFinset 2 j 0,
        gradNormIn (nearestNeighborGraph 2) (triadicCubeFinset 2 j 0) f x ^ 2 := by
  have hB : 0 < (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.size := by
    change 0 < 3 ^ j
    positivity
  have h := IntegerCube.sum_abs_sub_mean_rpow_le _ hB f (p := 2) (by norm_num)
  have hsize : (((⟨j, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) = 3 ^ j := by
    change ((3 ^ j : ℕ) : ℝ) = _
    push_cast
    rfl
  have hc : ((2 : ℕ) : ℝ) ^ ((2 : ℝ) - 1) * (((2 : ℕ) : ℝ) * √2 ^ (2 : ℝ)) *
      (((⟨j, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ (2 : ℝ) = 8 * 9 ^ j := by
    rw [hsize, Real.rpow_two, Real.rpow_two, Real.sq_sqrt (by norm_num),
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [hc, toIntegerCube_vertices_zero, card_square_eq] at h
  simp only [Real.rpow_two, sq_abs] at h
  exact h

/-- **The Hölder step with the Meyers estimate** for a weight `a` on the cluster of `□_j`:
`∑ |∇u|² a ≤ C_M^{1/q} K_a^{1/q'} A / 9`, with `A` the energy on `□_{j+1}` of the restriction of
`u` to the cluster of `□_{j+2}`. -/
theorem sum_gradNormIn_mul_le_of_meyers (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h02 : clusterVertices ω ⟨j, 0⟩ ⊆ clusterVertices ω ⟨j + 2, 0⟩)
    {q CM Ka : ℝ} (hq : 1 < q) (hCM : 0 ≤ CM) (hKa : 0 ≤ Ka)
    (hM : avg (cube j (0 : Vertex 2)) (fun x => clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) x ^ q) ≤
      CM * avg (enl 1 j (0 : Vertex 2)) (clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩))) ^ q)
    (a : Vertex 2 → ℝ) (ha : ∀ z, 0 ≤ a z)
    (hmom : ∑ z ∈ clusterVertices ω ⟨j, 0⟩, a z ^ Real.conjExponent q ≤ Ka * 9 ^ j) :
    ∑ z ∈ clusterVertices ω ⟨j, 0⟩, gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
        (Rigidity.Section3.extend C u) z ^ 2 * a z ≤
      CM ^ (1 / q) * Ka ^ (1 / Real.conjExponent q) *
        ((∑ z ∈ enl 1 j (0 : Vertex 2), clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
          (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) z) / 9) := by
  obtain ⟨E, hEdef⟩ : ∃ E : Vertex 2 → ℝ, E = clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
      (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) := ⟨_, rfl⟩
  rw [← hEdef] at hM ⊢
  have hE0 : ∀ z, 0 ≤ E z := fun z => by rw [hEdef]; exact clusterEnergy_nonneg _ _ _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ z ∈ enl 1 j (0 : Vertex 2), E z := ⟨_, rfl⟩
  rw [← hAdef]
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Finset.sum_nonneg fun z _ => hE0 z
  have hN : (0 : ℝ) < 9 ^ j := by positivity
  have hcube : ((cube j (0 : Vertex 2)).card : ℝ) = 9 ^ j := by
    rw [card_cube, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have henl : ((enl 1 j (0 : Vertex 2)).card : ℝ) = 9 * 9 ^ j := by
    rw [card_enl, ← pow_mul, mul_comm (j + 1) 2, pow_mul]; norm_num; ring
  have hgE : ∀ z ∈ clusterVertices ω ⟨j, 0⟩, gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
      (Rigidity.Section3.extend C u) z ^ 2 ≤ E z := by
    intro z hz
    have hz2 := h02 hz
    rw [gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => by
      split_ifs <;> positivity)), hEdef, clusterEnergy, if_pos hz2, clusterGradSq,
      ← Finset.sum_filter]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc ∑ y ∈ (clusterVertices ω ⟨j, 0⟩).filter (fun y => (openGraph ω).Adj z y),
          (Rigidity.Section3.extend C u z - Rigidity.Section3.extend C u y) ^ 2
        ≤ ∑ y ∈ ((openGraph ω).neighborFinset z).filter (· ∈ clusterVertices ω ⟨j + 2, 0⟩),
            (Rigidity.Section3.extend C u z - Rigidity.Section3.extend C u y) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => by
            obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
            exact Finset.mem_filter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hy2, h02 hy1⟩)
            fun _ _ _ => sq_nonneg _
      _ = ∑ y ∈ ((openGraph ω).neighborFinset z).filter (· ∈ clusterVertices ω ⟨j + 2, 0⟩),
            (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩) z -
              clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩) y) ^ 2 :=
          Finset.sum_congr rfl fun y hy => by
            rw [clusterExtend_clusterRestrictTo C u hz2,
              clusterExtend_clusterRestrictTo C u (Finset.mem_filter.1 hy).2]
  have hbq : ∑ z ∈ clusterVertices ω ⟨j, 0⟩, (gradNormIn (openGraph ω)
      (clusterVertices ω ⟨j, 0⟩) (Rigidity.Section3.extend C u) z ^ 2) ^ q ≤
      CM * 9 ^ j * (A / (9 * 9 ^ j)) ^ q := by
    have hq0 : 0 ≤ q := by linarith
    calc ∑ z ∈ clusterVertices ω ⟨j, 0⟩, (gradNormIn (openGraph ω)
          (clusterVertices ω ⟨j, 0⟩) (Rigidity.Section3.extend C u) z ^ 2) ^ q
        ≤ ∑ z ∈ clusterVertices ω ⟨j, 0⟩, E z ^ q :=
          Finset.sum_le_sum fun z hz => Real.rpow_le_rpow (sq_nonneg _) (hgE z hz) hq0
      _ ≤ ∑ z ∈ cube j (0 : Vertex 2), E z ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz))
            fun z _ _ => Real.rpow_nonneg (hE0 z) _
      _ = 9 ^ j * avg (cube j (0 : Vertex 2)) (fun x => E x ^ q) := by
          rw [avg, hcube]; field_simp
      _ ≤ 9 ^ j * (CM * avg (enl 1 j (0 : Vertex 2)) E ^ q) :=
          mul_le_mul_of_nonneg_left hM hN.le
      _ = CM * 9 ^ j * (A / (9 * 9 ^ j)) ^ q := by
          rw [avg, henl, ← hAdef]; ring
  exact holder_meyers_bound (clusterVertices ω ⟨j, 0⟩) (a := a)
    (b := fun z => gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
      (Rigidity.Section3.extend C u) z ^ 2)
    (fun z _ => ha z) (fun z _ => sq_nonneg _) hq hKa hCM hN hA0 hbq hmom

/-- **The bound of `[u]_𝒫` minus its mean on one square**: from the Poincaré inequality on `□_j`,
Lemma 3.3 with the pair reach scales, the Hölder inequality with the Meyers estimate `hM` and the
moments `hmom` of the pair reach scales, and the Caccioppoli inequality on `𝒞 ∩ □_{j+2}`. -/
theorem sum_sq_coarse_sub_mean_le (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (u : C → ℝ) {j : ℕ} (hres0 : PlanarResolved ω ⟨j, 0⟩)
    (h02 : clusterVertices ω ⟨j, 0⟩ ⊆ clusterVertices ω ⟨j + 2, 0⟩)
    (h2C : ∀ x ∈ clusterVertices ω ⟨j + 2, 0⟩, x ∈ C.supp)
    (hU3 : ∀ x ∈ triadicCubeFinset 2 (j + 2) 0, x ∈ C.supp → x ∈ clusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ triadicCubeFinset 2 (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0)
    {q CM Kρ : ℝ} (hq : 1 < q) (hCM : 0 ≤ CM) (hKρ : 0 ≤ Kρ)
    (hM : avg (cube j (0 : Vertex 2)) (fun x => clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) x ^ q) ≤
      CM * avg (enl 1 j (0 : Vertex 2)) (clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩))) ^ q)
    (hmom : ∑ z ∈ clusterVertices ω ⟨j, 0⟩,
        (((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).pairReachScale z) ^ (3 : ℝ)) ^
          Real.conjExponent q ≤ Kρ * 9 ^ j) (c : ℝ) :
    ∑ x ∈ triadicCubeFinset 2 j 0,
        (planarCoarse C u x - (∑ y ∈ triadicCubeFinset 2 j 0, planarCoarse C u y) / 9 ^ j) ^ 2 ≤
      128 / 81 * (4 * planarCoarseConst) ^ 2 * (CM ^ (1 / q) * Kρ ^ (1 / Real.conjExponent q)) *
        ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩, (Rigidity.Section3.extend C u x - c) ^ 2 := by
  have hPo := sum_sq_sub_mean_square_le j (planarCoarse C u)
  have hL3 := planar_sum_gradNormIn_coarseAnchor_rpow_le hP hres0 (Rigidity.Section3.extend C u)
    (s := 2) (by norm_num)
  rw [toIntegerCube_vertices_zero] at hL3
  have hconst : 2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
      (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ)) = 4 * planarCoarseConst := by
    unfold planarCoarseConst; push_cast; ring
  have e1 : ∀ x ∈ triadicCubeFinset 2 j 0, gradNormIn (nearestNeighborGraph 2)
      (triadicCubeFinset 2 j 0) (fun x => Rigidity.Section3.extend C u (planarCoarseAnchor ω x))
        x ^ (2 : ℝ) =
      gradNormIn (nearestNeighborGraph 2) (triadicCubeFinset 2 j 0) (planarCoarse C u) x ^ 2 :=
    fun x _ => by rw [Real.rpow_two]; rfl
  have e2 : ∀ z ∈ clusterVertices ω ⟨j, 0⟩,
      ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).pairReachScale z) ^
          ((2 : ℝ) * ((2 : ℕ) : ℝ) - 1) *
        gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩) (Rigidity.Section3.extend C u) z ^
          (2 : ℝ) =
      gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩) (Rigidity.Section3.extend C u) z ^ 2 *
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).pairReachScale z) ^ (3 : ℝ) :=
    fun z _ => by
      rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) - 1 = 3 by norm_num, Real.rpow_two, mul_comm]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, hconst, Real.rpow_two] at hL3
  have hW := sum_gradNormIn_mul_le_of_meyers C u h02 hq hCM hKρ hM
    (fun z => ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).pairReachScale z) ^ (3 : ℝ))
    (fun z => by positivity) hmom
  have hcac := energy_enl_le_caccioppoli C u h2C
    (fun x hx => mem_square_of_mem_clusterVertices hx) hU3 hharm c
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ z ∈ enl 1 j (0 : Vertex 2),
      clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) z := ⟨_, rfl⟩
  rw [← hAdef] at hW hcac
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = CM ^ (1 / q) * Kρ ^ (1 / Real.conjExponent q) := ⟨_, rfl⟩
  rw [← hPdef] at hW ⊢
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hK0 : 0 ≤ (4 * planarCoarseConst) ^ 2 := sq_nonneg _
  obtain ⟨Ssum, hSdef⟩ : ∃ S : ℝ, S = ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩,
      (Rigidity.Section3.extend C u x - c) ^ 2 := ⟨_, rfl⟩
  rw [← hSdef] at hcac ⊢
  have hN : (0 : ℝ) < 9 ^ j := by positivity
  calc _ ≤ _ := hPo
    _ ≤ 8 * 9 ^ j * ((4 * planarCoarseConst) ^ 2 * (P * (A / 9))) :=
        mul_le_mul_of_nonneg_left (hL3.trans (mul_le_mul_of_nonneg_left hW hK0)) (by positivity)
    _ = 8 * 9 ^ j * (4 * planarCoarseConst) ^ 2 * P / 9 * A := by ring
    _ ≤ 8 * 9 ^ j * (4 * planarCoarseConst) ^ 2 * P / 9 * (16 / 9 ^ (j + 1) * Ssum) :=
        mul_le_mul_of_nonneg_left hcac (by positivity)
    _ = 128 / 81 * (4 * planarCoarseConst) ^ 2 * P * Ssum := by
        rw [pow_succ]; field_simp; ring

/-- `(x + y + z)² ≤ 3 (x² + y² + z²)`. -/
theorem sq_add_add_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

/-- **Step 2 on one square from its two parts.** If `[u]_𝒫 - m` is bounded on `□_j`, `u - [u]_𝒫`
on `C_*(□_j)`, and `C_*(□_j)` carries at least `κ 9^j` vertices, then
`‖[u]_𝒫 - a‖_{L̲²(□_j)} ≤ 27 (2 K₁ + 6 (K₁ + K₂ + 1) / κ)^{1/2} ‖u - a‖_{L̲²(C_*(□_{j+3}))}`. -/
theorem squareL2_coarse_sub_le (C : OpenComponent ω) (u : C → ℝ) {j : ℕ} (a m : ℝ)
    {K₁ K₂ κ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hκ : 0 < κ)
    (hPo : ∑ x ∈ triadicCubeFinset 2 j 0, (planarCoarse C u x - m) ^ 2 ≤
      K₁ * ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩, (Rigidity.Section3.extend C u x - a) ^ 2)
    (hL : ∑ x ∈ clusterVertices ω ⟨j, 0⟩,
        (Rigidity.Section3.extend C u x - planarCoarse C u x) ^ 2 ≤
      K₂ * ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩, (Rigidity.Section3.extend C u x - a) ^ 2)
    (hST : clusterVertices ω ⟨j, 0⟩ ⊆ clusterVertices ω ⟨j + 3, 0⟩)
    (hcard : κ * 9 ^ j ≤ (clusterVertices ω ⟨j, 0⟩).card) :
    squareL2 j (fun y => planarCoarse C u y - a) ≤
      27 * Real.sqrt (2 * K₁ + 6 * (K₁ + K₂ + 1) / κ) *
        clusterSquareL2 ω (j + 3) (fun x => Rigidity.Section3.extend C u x - a) := by
  set f := Rigidity.Section3.extend C u with hfdef
  set g := planarCoarse C u with hgdef
  set T := ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩, (f x - a) ^ 2 with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN : (0 : ℝ) < 9 ^ j := by positivity
  have hSB : clusterVertices ω ⟨j, 0⟩ ⊆ triadicCubeFinset 2 j 0 :=
    fun x hx => mem_square_of_mem_clusterVertices hx
  -- the mean against `a`
  have hpt : ∀ x ∈ clusterVertices ω ⟨j, 0⟩,
      (m - a) ^ 2 ≤ 3 * ((g x - m) ^ 2 + (f x - g x) ^ 2 + (f x - a) ^ 2) := by
    intro x _
    have h := sq_add_add_le (m - g x) (g x - f x) (f x - a)
    have e : m - g x + (g x - f x) + (f x - a) = m - a := by ring
    rw [e] at h
    calc (m - a) ^ 2 ≤ _ := h
      _ = 3 * ((g x - m) ^ 2 + (f x - g x) ^ 2 + (f x - a) ^ 2) := by ring
  have hS : ((clusterVertices ω ⟨j, 0⟩).card : ℝ) * (m - a) ^ 2 ≤ 3 * (K₁ + K₂ + 1) * T := by
    have h1 : ∑ _x ∈ clusterVertices ω ⟨j, 0⟩, (m - a) ^ 2 ≤
        ∑ x ∈ clusterVertices ω ⟨j, 0⟩, 3 * ((g x - m) ^ 2 + (f x - g x) ^ 2 + (f x - a) ^ 2) :=
      Finset.sum_le_sum hpt
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib] at h1
    have h2 : ∑ x ∈ clusterVertices ω ⟨j, 0⟩, (g x - m) ^ 2 ≤
        ∑ x ∈ triadicCubeFinset 2 j 0, (g x - m) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hSB fun _ _ _ => sq_nonneg _
    have h3 : ∑ x ∈ clusterVertices ω ⟨j, 0⟩, (f x - a) ^ 2 ≤ T :=
      Finset.sum_le_sum_of_subset_of_nonneg hST fun _ _ _ => sq_nonneg _
    linarith
  have hm : 9 ^ j * (m - a) ^ 2 ≤ 3 * (K₁ + K₂ + 1) / κ * T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    calc 9 ^ j * (m - a) ^ 2 * κ = κ * 9 ^ j * (m - a) ^ 2 := by ring
      _ ≤ ((clusterVertices ω ⟨j, 0⟩).card : ℝ) * (m - a) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ ≤ _ := hS
  -- the square
  have hB : ∑ x ∈ triadicCubeFinset 2 j 0, (g x - a) ^ 2 ≤
      (2 * K₁ + 6 * (K₁ + K₂ + 1) / κ) * T := by
    have h1 : ∀ x ∈ triadicCubeFinset 2 j 0, (g x - a) ^ 2 ≤ 2 * (g x - m) ^ 2 + 2 * (m - a) ^ 2 :=
      fun x _ => by nlinarith [sq_nonneg (g x - m - (m - a))]
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      card_square_eq] at h2
    have e : 6 * (K₁ + K₂ + 1) / κ * T = 2 * (3 * (K₁ + K₂ + 1) / κ * T) := by ring
    nlinarith
  unfold squareL2 clusterSquareL2
  rw [three_pow_two_mul, show 2 * (j + 3) = 2 * j + 6 by ring, pow_add, three_pow_two_mul]
  have hK0 : 0 ≤ 2 * K₁ + 6 * (K₁ + K₂ + 1) / κ := by positivity
  have hrhs : 27 * Real.sqrt (2 * K₁ + 6 * (K₁ + K₂ + 1) / κ) * Real.sqrt (T / (9 ^ j * 3 ^ 6)) =
      Real.sqrt ((2 * K₁ + 6 * (K₁ + K₂ + 1) / κ) * T / 9 ^ j) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 27), ← Real.sqrt_mul (by norm_num),
      ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
    norm_num
    ring
  rw [hrhs]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hB hN.le)

/-- The sums of squares from the comparison (7.8) in the normalized form. -/
theorem sum_sq_le_of_clusterSquareL2_le {j : ℕ} {g f : Vertex 2 → ℝ} {K : ℝ}
    (h : clusterSquareL2 ω j g ≤ K / 3 ^ j * clusterSquareL2 ω (j + 3) f) :
    ∑ x ∈ clusterVertices ω ⟨j, 0⟩, g x ^ 2 ≤
      K ^ 2 * ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩, f x ^ 2 := by
  unfold clusterSquareL2 at h
  set A := ∑ x ∈ clusterVertices ω ⟨j, 0⟩, g x ^ 2 with hA
  set B := ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩, f x ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), div_pow,
    ← pow_mul] at hsq
  have h9 : (1 : ℝ) ≤ 3 ^ (2 * (j + 3)) := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 3 ^ (j * 2) := by positivity
  have e : (3 : ℝ) ^ (j * 2) = 3 ^ (2 * j) := by rw [mul_comm]
  rw [e] at hsq hpos
  have h1 : A ≤ K ^ 2 * (B / 3 ^ (2 * (j + 3))) := by
    have h2 := mul_le_mul_of_nonneg_right hsq hpos.le
    have e2 : K ^ 2 / 3 ^ (2 * j) * (B / 3 ^ (2 * (j + 3))) * 3 ^ (2 * j) =
        K ^ 2 * (B / 3 ^ (2 * (j + 3))) := by
      field_simp
    rwa [div_mul_cancel₀ _ hpos.ne', e2] at h2
  calc A ≤ K ^ 2 * (B / 3 ^ (2 * (j + 3))) := h1
    _ ≤ K ^ 2 * B := mul_le_mul_of_nonneg_left (div_le_self hB0 h9) (sq_nonneg _)

/-- **The cluster of `□_{i+1}` carries a fixed proportion of the square**, from the density of
the infinite cluster in `□_i` and the inclusion of `𝒞 ∩ □_i` in `C_*(□_{i+1})`. -/
theorem card_clusterVertices_succ_ge (C : OpenComponent ω) {ℓ κ : ℝ}
    (hcube : ClusterCubeDensity C 0 1 ℓ κ) {i : ℕ} (hi : ℓ ≤ 3 ^ i)
    (hsucc : ∀ x ∈ triadicCubeFinset 2 i 0, x ∈ C.supp → x ∈ clusterVertices ω ⟨i + 1, 0⟩) :
    κ / 9 * 9 ^ (i + 1) ≤ (clusterVertices ω ⟨i + 1, 0⟩).card := by
  have hin : ∀ y ∈ triadicCube 2 i 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) <
        1 * 3 ^ i := by
    intro y hy
    rw [one_mul]
    rw [← coe_triadicCubeFinset] at hy
    exact dist_lt_of_mem_square hy
  have h := hcube i 0 hi hin
  have hle : (clusterCubePoints C 0 (1 * 3 ^ i) i 0).card ≤
      (clusterVertices ω ⟨i + 1, 0⟩).card := by
    refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
    · intro x hx
      have hx' : x ∈ clusterCubePoints C 0 (1 * 3 ^ i) i 0 := hx
      simp only [clusterCubePoints, mem_filter] at hx'
      refine hsucc x.val ?_ x.2
      rw [mem_square_iff]
      intro k
      simpa using hx'.2 k
    · intro x _ y _ hxy
      exact Subtype.val_injective hxy
  calc κ / 9 * 9 ^ (i + 1) = κ * 3 ^ (2 * i) := by
        rw [pow_succ, pow_mul]; norm_num; ring
    _ ≤ _ := h
    _ ≤ _ := by exact_mod_cast hle

end Rigidity.Proofs.Regularity

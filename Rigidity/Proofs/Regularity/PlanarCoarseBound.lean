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
  the comparison (7.4) and `u - a`.
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

end Rigidity.Proofs.Regularity

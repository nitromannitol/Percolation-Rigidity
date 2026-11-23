import Rigidity.Proofs.Regularity.PlanarCoarseComparison

/-!
# The comparison (7.4) on planar squares, almost surely above a minimal scale

`planarCoarseComparisonTwo_of_minimalScales` proves the comparison (7.4) of the proof of
Armstrong–Dario, Lemma 7.1 (arXiv:1609.09431v2), in `L²` on the squares of the plane, almost surely
above a minimal scale `𝒳 ≤ O_s(θ)`, from the minimal scales of Proposition 2.4
(`PlanarMinimalScalesTwo p`), the density of the infinite cluster (proved) and the planar Meyers
estimate on the reverse Hölder cells (`planar_meyers_rh_uniform`, proved). The ingredients at one
scale are `coarseComparison_on_square`; here they are checked above the minimal scale:

* the cells of the reverse Hölder partition inside `□_{j+1}` have scale at most `j + 1`
  (the bound `3^{s(x)} ≤ 3^{m/2}` of Proposition 2.4) and satisfy the moment bound used by the
  Meyers estimate (`meyers_on_square`);
* the reach scales of the planar partition are bounded by its reach
  (`three_pow_reachScale_le_planarReach`), whose moments are bounded by Proposition 2.4
  (`sum_reachScale_rpow_le`);
* the squares are resolved and their clusters lie in the infinite cluster
  (`PlanarClusterInclusions`).
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical ENNReal

variable {ω : Configuration 2}

/-- The reach scale of the planar coarse-graining data is bounded by the reach of the partition. -/
theorem three_pow_reachScale_le_planarReach (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (z : Vertex 2) :
    (3 : ℝ≥0∞) ^ (planarCoarseData hP U hU).reachScale z ≤ planarReach ω z := by
  have hown : (3 : ℝ≥0∞) ^ (planarPartCube ω z).scale ≤ planarReach ω z := by
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
  unfold CoarseData.reachScale
  rcases Finset.eq_empty_or_nonempty ((planarCoarseData hP U hU).cluster.filter
      fun x => z ∈ (planarCoarseData hP U hU).region x) with h | h
  · rw [h, Finset.sup_empty]
    exact (one_le_pow₀ (by norm_num)).trans hown
  · obtain ⟨x, hx, hxsup⟩ := Finset.exists_mem_eq_sup _ h
      (fun x => ((planarCoarseData hP U hU).part x).scale)
    rw [hxsup]
    obtain ⟨hxc, hzx⟩ := Finset.mem_filter.1 hx
    have hxU : x ∈ U.vertices := (mem_clusterVertices.1 hxc).1
    have hzw : z ∈ ((planarPartCube ω x).thicken 4).vertices :=
      planarClusterWindow_subset_thicken hP hU hxU hzx
    rw [← TriadicCube.ninefold_vertices_eq_thicken] at hzw
    unfold planarReach
    exact le_iSup₂ (f := fun (Q : TriadicCube 2) (_ : Q.IsMaximalStopping (planarGoodCubes ω) ∧
      z ∈ (↑Q.ninefold.vertices : Set (Vertex 2))) => (3 : ℝ≥0∞) ^ Q.scale) (planarPartCube ω x)
      ⟨(planarPartCube_spec hP x).2, Finset.mem_coe.2 hzw⟩

/-- **Moments of the reach scales** on the cluster of `□_j` from the moments of the reach on the
triadic cube of scale `j`. -/
theorem sum_reachScale_rpow_le (hP : PlanarPartitionEvent ω) {j : ℕ}
    (hres : PlanarResolved ω ⟨j, 0⟩) {τ K : ℝ} (hτ : 0 < τ)
    (hfin : ∀ x ∈ cube j (0 : Vertex 2), planarReach ω x ≠ ⊤)
    (hsum : ∑ x ∈ cube j (0 : Vertex 2), planarReach ω x ^ ⌈τ⌉₊ ≤
      ENNReal.ofReal (K * (cube j (0 : Vertex 2)).card)) (hK : 0 ≤ K) :
    ∑ z ∈ clusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z) ^ τ ≤ K * 9 ^ j := by
  have hcube : ((cube j (0 : Vertex 2)).card : ℝ) = 9 ^ j := by
    rw [card_cube, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have hpt : ∀ z ∈ clusterVertices ω ⟨j, 0⟩,
      ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z) ^ τ ≤
        (planarReach ω z).toReal ^ ⌈τ⌉₊ := by
    intro z hz
    have hzc : z ∈ cube j (0 : Vertex 2) :=
      mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz)
    have hle := three_pow_reachScale_le_planarReach hP hres z
    have hle' : (3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z ≤
        (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono (hfin z hzc) hle
      simpa using this
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z :=
      one_le_pow₀ (by norm_num)
    calc ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z) ^ τ
        ≤ (planarReach ω z).toReal ^ τ := Real.rpow_le_rpow (by positivity) hle' hτ.le
      _ ≤ (planarReach ω z).toReal ^ (⌈τ⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (h1.trans hle') (Nat.le_ceil τ)
      _ = (planarReach ω z).toReal ^ ⌈τ⌉₊ := Real.rpow_natCast _ _
  have hsub : clusterVertices ω ⟨j, 0⟩ ⊆ cube j (0 : Vertex 2) :=
    fun z hz => mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz)
  calc ∑ z ∈ clusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z) ^ τ
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

theorem enl_one_zero_eq_cube (j : ℕ) : enl 1 j (0 : Vertex 2) = cube (j + 1) (0 : Vertex 2) := by
  rw [enl, cube, center_zero, center_zero]

/-- **The Meyers estimate on `□_j`** for the restriction of `u` to the cluster of `□_{j+2}`, from the
cells of the reverse Hölder partition. -/
theorem meyers_on_square {A₀ ε t K CM : ℝ}
    (hMey : ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2)
        (_ : PlanarResolved ω V) (w : ClusterFun ω V) (_ : w ∈ clusterHarmonic ω V) (n : ℕ)
        (x₀ : Vertex 2) (s : Vertex 2 → ℕ),
        (∀ x ∈ enl 1 n x₀, V.IsInterior x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube 2) ∈ planarRHGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀)
            (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ (1 + ε / 2))
    (hP : PlanarPartitionEvent ω) (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (hres2 : PlanarResolved ω ⟨j + 2, 0⟩)
    (h2C : ∀ x ∈ clusterVertices ω ⟨j + 2, 0⟩, x ∈ C.supp)
    (hharm : ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ triadicCubeFinset 2 (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0)
    (s : Vertex 2 → ℕ) (hcell : ∀ x, ∀ z ∈ cube (s x) x, s z = s x)
    (hnb : ∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1)
    (hrh : ∀ (k : ℕ) (y : Vertex 2), s y ≤ k → (⟨k, idx k y⟩ : TriadicCube 2) ∈ planarRHGood A₀ ω)
    (hsize : ∀ z ∈ cube (j + 1) (0 : Vertex 2), s z ≤ j + 1)
    (hmom : ∑ x ∈ cube j (0 : Vertex 2), ((3 : ℝ) ^ s x) ^ t ≤ K * (cube j (0 : Vertex 2)).card) :
    avg (cube j (0 : Vertex 2)) (fun x => clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 j (0 : Vertex 2)) (clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩))) ^ (1 + ε / 2) := by
  have hw := clusterRestrictTo_mem_clusterHarmonic hP hres2 C h2C fun x hx hxV _ => by
    refine hharm x hx ?_
    have h1 := mem_square_of_mem_clusterVertices hxV
    rw [mem_square_iff_int] at h1 ⊢
    intro i
    have := h1 i
    have h3 : (3 : ℤ) ^ (j + 2) ≤ 3 ^ (j + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  refine hMey ω hP ⟨j + 2, 0⟩ hres2 _ hw j 0 s ?_ hcell hnb ?_ (fun k y hk _ => hrh k y hk) hmom
  · intro x hx y hy
    have hx1 := mem_square_of_mem_enl hx
    rw [mem_triadicCube_zero_iff]
    intro i
    have h1 := (mem_square_iff_int.1 hx1) i
    have h2 := hy i
    have h3 : (3 : ℤ) ^ (j + 2) = 3 * 3 ^ (j + 1) := by ring
    have hpos : (1 : ℤ) ≤ 3 ^ (j + 1) := one_le_pow₀ (by norm_num)
    have ha := abs_sub_abs_le_abs_sub (y i) (x i)
    rw [abs_sub_comm (y i) (x i)] at ha
    omega
  · intro z hz
    rw [enl_one_zero_eq_cube] at hz ⊢
    intro w hw'
    have hle := hsize z hz
    have h1 : w ∈ cube (j + 1) z := cube_mono hle z hw'
    rw [cube_eq_of_mem hz] at h1
    exact h1

end Rigidity.Proofs.Regularity

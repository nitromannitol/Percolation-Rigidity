import Rigidity.Proofs.Regularity.PlanarCoarseBound

/-!
# The `L^{p'}` gradient norm on the cluster of a planar square

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, (7.4): for `u` harmonic on
the cluster, the normalized `L^{p'}` norm `M` of the open gradient of `u` on `C_*(□_{j+1})`
(`planarGradNormTwo`, the quantity of Theorem 1) is at most `4 C_M^{1/p'} 3^{-j}` times
`‖u - c‖_{L̲²(C_*(□_{j+3}))}`, for `p' = 2q` with the Meyers exponent `q`:

* the Meyers estimate on `□_{j+1}` for the restriction of `u` to the cluster of `□_{j+3}` bounds
  `M` by the energy on `□_{j+2}`;
* the Caccioppoli inequality on `C_*(□_{j+3})` itself (`energy_enl_succ_le_caccioppoli`), which
  contains the vertices of the infinite cluster in the square of half-side `17 · 3^j / 2`, bounds
  that energy by `16 · 9^{-(j+1)} Σ_{C_*(□_{j+3})} (u - c)²`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical

variable {ω : Configuration 2}

/-- The normalized `L^{p'}` norm `M = (|□_m|⁻¹ Σ_{x ∈ C_*(□_m)} |∇u 1_{a≠0}|^{p'}(x))^{1/p'}` of the
open gradient of `u` on the cluster of `□_m` (the quantity `planarGradNorm` of the statement of
Theorem 1 in dimension two). -/
noncomputable def planarGradNormTwo (ω : Configuration 2) (m : ℕ) (p' : ℝ) (u : Vertex 2 → ℝ) :
    ℝ :=
  ((∑ x ∈ clusterVertices ω ⟨m, 0⟩,
      gradNormIn (openGraph ω) (clusterVertices ω ⟨m, 0⟩) u x ^ p') / 9 ^ m) ^ (1 / p')

/-- **A vertex of an infinite cluster whose partition cube has its ninefold inside `U` lies in
the cluster of `U`.** -/
theorem mem_clusterVertices_of_ninefold_subset (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (hinf : C.supp.Infinite) {U : TriadicCube 2} {x : Vertex 2} (hxU : x ∈ U.vertices)
    (hxC : x ∈ C.supp)
    (hsub : (↑(planarPartCube ω x).ninefold.vertices : Set (Vertex 2)) ⊆ U.vertices) :
    x ∈ clusterVertices ω U := by
  have hC : (openGraph ω).connectedComponentMk x = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hxC
  have hxinf : ((openGraph ω).connectedComponentMk x).supp.Infinite := by rw [hC]; exact hinf
  obtain ⟨-, -, hB⟩ := (planarPartCube ω x).planarAnchor_spec (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x)
  have h1 := (planarPartCube ω x).reachIn_anchor_of_infinite hB (planarPartCube_spec hP x).1 hxinf
  exact mem_clusterVertices.2 ⟨hxU, h1.symm.mono hsub⟩

/-- **The infinite cluster in the inner part of `□_{j+3}`** lies in `C_*(□_{j+3})` when the
partition cubes of `□_{j+3}` have scale at most `j`. -/
theorem mem_clusterVertices_inner (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (hinf : C.supp.Infinite) {j : ℕ}
    (hsc : ∀ x ∈ triadicCubeFinset 2 (j + 3) 0, (planarPartCube ω x).scale ≤ j) {x : Vertex 2}
    (hxC : x ∈ C.supp) (hx : ∀ k, 2 * |x k| < 17 * 3 ^ j) :
    x ∈ clusterVertices ω ⟨j + 3, 0⟩ := by
  have h27 : (3 : ℤ) ^ (j + 3) = 27 * 3 ^ j := by ring
  have hxsq : x ∈ triadicCubeFinset 2 (j + 3) 0 := by
    rw [mem_square_iff_int]
    intro k
    have := hx k
    have h0 : (0 : ℤ) < 3 ^ j := by positivity
    rw [h27]; linarith
  have hxU : x ∈ (⟨j + 3, 0⟩ : TriadicCube 2).vertices :=
    mem_triadicCube_zero_iff.2 (mem_square_iff_int.1 hxsq)
  have hxQ : x ∈ (planarPartCube ω x).vertices := (planarPartCube_spec hP x).1
  have hs : (3 : ℤ) ^ (planarPartCube ω x).scale ≤ 3 ^ j := pow_le_pow_right₀ (by norm_num) (hsc x hxsq)
  refine mem_clusterVertices_of_ninefold_subset hP C hinf hxU hxC fun y hy => ?_
  rw [TriadicCube.mem_ninefold] at hy
  rw [mem_triadicCube_zero_iff]
  intro i
  have h9 := (planarPartCube ω x).two_mul_ninefoldRadius
  have hxc := (planarPartCube ω x).abs_sub_center_le hxQ i
  have hyc := hy i
  have hxi := hx i
  have a1 := abs_sub_le (y i) ((planarPartCube ω x).center i) (x i)
  have a2 := abs_sub_abs_le_abs_sub (y i) (x i)
  have a3 : |y i| ≤ |y i - x i| + |x i| := by linarith
  rw [abs_sub_comm ((planarPartCube ω x).center i) (x i)] at a1
  rw [h27]
  omega

/-- **The Caccioppoli step on `C_*(□_{j+3})`**: the energy of `u` on `□_{j+2}`, counted with the
edges inside the cluster of `□_{j+3}`, is at most `16 · 9^{-(j+1)} Σ_{C_*(□_{j+3})} (u - c)²`. -/
theorem energy_enl_succ_le_caccioppoli (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h3C : ∀ x ∈ clusterVertices ω ⟨j + 3, 0⟩, x ∈ C.supp)
    (hin : ∀ x, x ∈ C.supp → (∀ k, 2 * |x k| < 17 * 3 ^ j) → x ∈ clusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ triadicCubeFinset 2 (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0) (c : ℝ) :
    ∑ z ∈ enl 1 (j + 1) (0 : Vertex 2), clusterEnergy ω (clusterVertices ω ⟨j + 3, 0⟩)
        (clusterExtend ω ⟨j + 3, 0⟩ (clusterRestrictTo C u ⟨j + 3, 0⟩)) z ≤
      16 / 9 ^ (j + 1) * ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩,
        (Rigidity.Section3.extend C u x - c) ^ 2 := by
  set f := Rigidity.Section3.extend C u with hfdef
  set U := clusterVertices ω ⟨j + 3, 0⟩ with hUdef
  set V' := (triadicCubeFinset 2 (j + 2) 0).filter (· ∈ C.supp) with hV'def
  have h9 : (3 : ℤ) ^ (j + 2) = 9 * 3 ^ j := by ring
  have hV'U : V' ⊆ U := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    refine hin x hx2 fun k => ?_
    have := (mem_square_iff_int.1 hx1) k
    have h0 : (0 : ℤ) < 3 ^ j := by positivity
    rw [h9] at this; linarith
  have hE : ∑ z ∈ enl 1 (j + 1) (0 : Vertex 2), clusterEnergy ω U
      (clusterExtend ω ⟨j + 3, 0⟩ (clusterRestrictTo C u ⟨j + 3, 0⟩)) z ≤
      ∑ z ∈ V', clusterGradSq ω U f z := by
    calc ∑ z ∈ enl 1 (j + 1) (0 : Vertex 2), clusterEnergy ω U
          (clusterExtend ω ⟨j + 3, 0⟩ (clusterRestrictTo C u ⟨j + 3, 0⟩)) z
        = ∑ z ∈ (enl 1 (j + 1) (0 : Vertex 2)).filter (· ∈ U), clusterGradSq ω U
            (clusterExtend ω ⟨j + 3, 0⟩ (clusterRestrictTo C u ⟨j + 3, 0⟩)) z := by
          rw [Finset.sum_filter]; rfl
      _ ≤ ∑ z ∈ (enl 1 (j + 1) (0 : Vertex 2)).filter (· ∈ U), clusterGradSq ω U f z :=
          Finset.sum_le_sum fun z hz => clusterGradSq_le_of_eqOn le_rfl
            (clusterExtend_clusterRestrictTo C u (Finset.mem_filter.1 hz).2)
            fun y hy => clusterExtend_clusterRestrictTo C u hy
      _ ≤ ∑ z ∈ V', clusterGradSq ω U f z := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
            fun _ _ _ => clusterGradSq_nonneg _ _ _ _
          obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
          exact Finset.mem_filter.2 ⟨mem_square_of_mem_enl hz1, h3C z hz2⟩
  have hr : (0 : ℝ) < 3 ^ (j + 1) := by positivity
  have hdist : ∀ x ∈ V', ∀ z ∈ U, (∃ y, (openGraph ω).Adj z y ∧ y ∉ U) →
      (3 : ℝ) ^ (j + 1) ≤ (supDist x z : ℝ) := by
    rintro x hx z hz ⟨y, hzy, hyU⟩
    obtain ⟨hx1, -⟩ := Finset.mem_filter.1 hx
    have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp (h3C z hz) hzy
    have hy2 : ¬ ∀ k, 2 * |y k| < 17 * 3 ^ j := fun h => hyU (hin y hyC h)
    push Not at hy2
    obtain ⟨k, hk⟩ := hy2
    have hzk := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hzy) k
    have hxk := (mem_square_iff_int.1 hx1) k
    have hle : (x k - z k).natAbs ≤ supDist x z :=
      Finset.le_sup (f := fun i => (x i - z i).natAbs) (Finset.mem_univ k)
    have hcast : ((3 : ℤ) ^ (j + 1) : ℤ) ≤ ((x k - z k).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      have h3 : (3 : ℤ) ^ (j + 1) = 3 * 3 ^ j := by ring
      have hab := abs_sub_abs_le_abs_sub (z k) (x k)
      have hyz := abs_sub_abs_le_abs_sub (y k) (z k)
      rw [abs_sub_comm (z k) (x k)] at hab
      rw [h9] at hxk
      have h1 : (1 : ℤ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
      generalize |x k| = a at hxk hab
      generalize |z k| = b at hab hyz
      generalize |y k| = c at hk hyz
      generalize |x k - z k| = e at hab ⊢
      generalize |y k - z k| = g at hzk hyz
      generalize (3 : ℤ) ^ (j + 1) = t at h3 ⊢
      generalize (3 : ℤ) ^ j = t' at h3 hxk hk h1
      omega
    have : ((3 : ℤ) ^ (j + 1) : ℤ) ≤ (supDist x z : ℤ) := hcast.trans (by exact_mod_cast hle)
    exact_mod_cast this
  have hu : ∀ x ∈ U, (∀ y, (openGraph ω).Adj x y → y ∈ U) →
      openLaplacian ω (fun y => f y - c) x = 0 := by
    intro x hx _
    have hx2 := h3C x hx
    rw [Rigidity.Proofs.Cluster.openLaplacian_sub_const, hfdef, openLaplacian_extend_eq C u hx2]
    exact hharm x hx2 (mem_square_of_mem_clusterVertices hx)
  have hcac := caccioppoli_cluster ω U V' hV'U hr hdist (fun y => f y - c) hu
  have e1 : ∑ x ∈ V', clusterGradSq ω U (fun y => f y - c) x = ∑ x ∈ V', clusterGradSq ω U f x :=
    Finset.sum_congr rfl fun x _ => clusterGradSq_sub_const U f c x
  rw [e1] at hcac
  have hsumU : ∑ x ∈ U.filter (fun x => ¬ (x ∈ V' ∧
      ∀ y, (nearestNeighborGraph 2).Adj x y → y ∈ V')), (f x - c) ^ 2 ≤
      ∑ x ∈ U, (f x - c) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  have h16 : 8 * ((2 : ℕ) : ℝ) / ((3 : ℝ) ^ (j + 1)) ^ 2 = 16 / 9 ^ (j + 1) := by
    rw [← pow_mul, mul_comm (j + 1) 2, pow_mul]; norm_num
  rw [h16] at hcac
  calc _ ≤ ∑ z ∈ V', clusterGradSq ω U f z := hE
    _ ≤ _ := hcac
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumU (by positivity)

/-- The open gradient on the cluster of a cube against the energy of the restriction to the
cluster of a larger cube. -/
theorem gradNormIn_sq_le_clusterEnergy (C : OpenComponent ω) (u : C → ℝ) {V V' : TriadicCube 2}
    (hVV' : clusterVertices ω V ⊆ clusterVertices ω V') {z : Vertex 2}
    (hz : z ∈ clusterVertices ω V) :
    gradNormIn (openGraph ω) (clusterVertices ω V) (Rigidity.Section3.extend C u) z ^ 2 ≤
      clusterEnergy ω (clusterVertices ω V') (clusterExtend ω V' (clusterRestrictTo C u V')) z := by
  have hz2 := hVV' hz
  rw [gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => by
    split_ifs <;> positivity)), clusterEnergy, if_pos hz2, clusterGradSq,
    ← Finset.sum_filter]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc ∑ y ∈ (clusterVertices ω V).filter (fun y => (openGraph ω).Adj z y),
        (Rigidity.Section3.extend C u z - Rigidity.Section3.extend C u y) ^ 2
      ≤ ∑ y ∈ ((openGraph ω).neighborFinset z).filter (· ∈ clusterVertices ω V'),
          (Rigidity.Section3.extend C u z - Rigidity.Section3.extend C u y) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => by
          obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
          exact Finset.mem_filter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hy2, hVV' hy1⟩)
          fun _ _ _ => sq_nonneg _
    _ = ∑ y ∈ ((openGraph ω).neighborFinset z).filter (· ∈ clusterVertices ω V'),
          (clusterExtend ω V' (clusterRestrictTo C u V') z -
            clusterExtend ω V' (clusterRestrictTo C u V') y) ^ 2 :=
        Finset.sum_congr rfl fun y hy => by
          rw [clusterExtend_clusterRestrictTo C u hz2,
            clusterExtend_clusterRestrictTo C u (Finset.mem_filter.1 hy).2]

/-- **The gradient norm of Theorem 1 on `C_*(□_{j+1})`** from the Meyers estimate `hM` on
`□_{j+1}` and the Caccioppoli inequality on `C_*(□_{j+3})`:
`M ≤ 4 C_M^{1/(2q)} 3^{-j} ‖u - c‖_{L̲²(C_*(□_{j+3}))}`. -/
theorem planarGradNormTwo_le (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h13 : clusterVertices ω ⟨j + 1, 0⟩ ⊆ clusterVertices ω ⟨j + 3, 0⟩)
    (h3C : ∀ x ∈ clusterVertices ω ⟨j + 3, 0⟩, x ∈ C.supp)
    (hin : ∀ x, x ∈ C.supp → (∀ k, 2 * |x k| < 17 * 3 ^ j) → x ∈ clusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ triadicCubeFinset 2 (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0)
    {q CM : ℝ} (hq : 1 < q) (hCM : 0 ≤ CM)
    (hM : avg (cube (j + 1) (0 : Vertex 2)) (fun x =>
        clusterEnergy ω (clusterVertices ω ⟨j + 1 + 2, 0⟩)
          (clusterExtend ω ⟨j + 1 + 2, 0⟩ (clusterRestrictTo C u ⟨j + 1 + 2, 0⟩)) x ^ q) ≤
      CM * avg (enl 1 (j + 1) (0 : Vertex 2)) (clusterEnergy ω (clusterVertices ω ⟨j + 1 + 2, 0⟩)
        (clusterExtend ω ⟨j + 1 + 2, 0⟩ (clusterRestrictTo C u ⟨j + 1 + 2, 0⟩))) ^ q)
    (c : ℝ) :
    planarGradNormTwo ω (j + 1) (2 * q) (Rigidity.Section3.extend C u) ≤
      4 * CM ^ (1 / (2 * q)) / 3 ^ j *
        clusterSquareL2 ω (j + 3) (fun x => Rigidity.Section3.extend C u x - c) := by
  obtain ⟨E, hEdef⟩ : ∃ E : Vertex 2 → ℝ, E = clusterEnergy ω (clusterVertices ω ⟨j + 3, 0⟩)
      (clusterExtend ω ⟨j + 3, 0⟩ (clusterRestrictTo C u ⟨j + 3, 0⟩)) := ⟨_, rfl⟩
  have hM' : avg (cube (j + 1) (0 : Vertex 2)) (fun x => E x ^ q) ≤
      CM * avg (enl 1 (j + 1) (0 : Vertex 2)) E ^ q := by rw [hEdef]; exact hM
  have hE0 : ∀ z, 0 ≤ E z := fun z => by rw [hEdef]; exact clusterEnergy_nonneg _ _ _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ z ∈ enl 1 (j + 1) (0 : Vertex 2), E z := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Finset.sum_nonneg fun z _ => hE0 z
  have hq0 : 0 < q := by linarith
  have hN : (0 : ℝ) < 9 ^ (j + 1) := by positivity
  have hcube : ((cube (j + 1) (0 : Vertex 2)).card : ℝ) = 9 ^ (j + 1) := by
    rw [card_cube, ← pow_mul, mul_comm (j + 1) 2, pow_mul]; norm_num
  have henl : ((enl 1 (j + 1) (0 : Vertex 2)).card : ℝ) = 9 * 9 ^ (j + 1) := by
    rw [card_enl, ← pow_mul, mul_comm (j + 1 + 1) 2, pow_mul]; norm_num; ring
  -- the `L^{2q}` sum against the energy
  have hS : ∑ x ∈ clusterVertices ω ⟨j + 1, 0⟩, gradNormIn (openGraph ω)
      (clusterVertices ω ⟨j + 1, 0⟩) (Rigidity.Section3.extend C u) x ^ (2 * q) ≤
      9 ^ (j + 1) * (CM * (A / (9 * 9 ^ (j + 1))) ^ q) := by
    calc ∑ x ∈ clusterVertices ω ⟨j + 1, 0⟩, gradNormIn (openGraph ω)
          (clusterVertices ω ⟨j + 1, 0⟩) (Rigidity.Section3.extend C u) x ^ (2 * q)
        ≤ ∑ x ∈ clusterVertices ω ⟨j + 1, 0⟩, E x ^ q := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Real.rpow_mul (gradNormIn_nonneg _ _ _ _), Real.rpow_two]
          refine Real.rpow_le_rpow (sq_nonneg _) ?_ hq0.le
          rw [hEdef]
          exact gradNormIn_sq_le_clusterEnergy C u h13 hx
      _ ≤ ∑ x ∈ cube (j + 1) (0 : Vertex 2), E x ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz))
            fun z _ _ => Real.rpow_nonneg (hE0 z) _
      _ = 9 ^ (j + 1) * avg (cube (j + 1) (0 : Vertex 2)) (fun x => E x ^ q) := by
          rw [avg, hcube]; field_simp
      _ ≤ 9 ^ (j + 1) * (CM * avg (enl 1 (j + 1) (0 : Vertex 2)) E ^ q) :=
          mul_le_mul_of_nonneg_left hM' hN.le
      _ = 9 ^ (j + 1) * (CM * (A / (9 * 9 ^ (j + 1))) ^ q) := by
          rw [avg, henl, ← hAdef]
  -- the Caccioppoli step
  have hcac := energy_enl_succ_le_caccioppoli C u h3C hin hharm c
  rw [← hEdef, ← hAdef] at hcac
  obtain ⟨Ssum, hSdef⟩ : ∃ S : ℝ, S = ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩,
      (Rigidity.Section3.extend C u x - c) ^ 2 := ⟨_, rfl⟩
  rw [← hSdef] at hcac
  have hS0 : 0 ≤ Ssum := by rw [hSdef]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hAq : A / (9 * 9 ^ (j + 1)) ≤ 16 * Ssum / (9 ^ (j + 3) * 9 ^ j) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (9 : ℝ) ^ (j + 3) * 9 ^ j = 9 * 9 ^ (j + 1) * 9 ^ (j + 1) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hcac (by positivity : (0 : ℝ) ≤ 9 * 9 ^ (j + 1) * 9 ^ (j + 1))
    calc A * (9 * 9 ^ (j + 1) * 9 ^ (j + 1)) = 9 * 9 ^ (j + 1) * 9 ^ (j + 1) * A := by ring
      _ ≤ 9 * 9 ^ (j + 1) * 9 ^ (j + 1) * (16 / 9 ^ (j + 1) * Ssum) := this
      _ = 16 * Ssum * (9 * 9 ^ (j + 1)) := by field_simp
  -- the norm
  have hB0 : 0 ≤ 16 * Ssum / (9 ^ (j + 3) * 9 ^ j) := by positivity
  unfold planarGradNormTwo
  have hsum0 : 0 ≤ ∑ x ∈ clusterVertices ω ⟨j + 1, 0⟩, gradNormIn (openGraph ω)
      (clusterVertices ω ⟨j + 1, 0⟩) (Rigidity.Section3.extend C u) x ^ (2 * q) :=
    Finset.sum_nonneg fun x _ => Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _
  have h1 : (∑ x ∈ clusterVertices ω ⟨j + 1, 0⟩, gradNormIn (openGraph ω)
      (clusterVertices ω ⟨j + 1, 0⟩) (Rigidity.Section3.extend C u) x ^ (2 * q)) / 9 ^ (j + 1) ≤
      CM * (16 * Ssum / (9 ^ (j + 3) * 9 ^ j)) ^ q := by
    rw [div_le_iff₀ hN]
    calc _ ≤ 9 ^ (j + 1) * (CM * (A / (9 * 9 ^ (j + 1))) ^ q) := hS
      _ ≤ 9 ^ (j + 1) * (CM * (16 * Ssum / (9 ^ (j + 3) * 9 ^ j)) ^ q) := by
          gcongr
      _ = _ := by ring
  have h2 := Real.rpow_le_rpow (div_nonneg hsum0 hN.le) h1 (by positivity : (0 : ℝ) ≤ 1 / (2 * q))
  refine h2.trans (le_of_eq ?_)
  rw [Real.mul_rpow hCM (Real.rpow_nonneg hB0 _), ← Real.rpow_mul hB0,
    show q * (1 / (2 * q)) = 1 / 2 by field_simp, ← Real.sqrt_eq_rpow]
  unfold clusterSquareL2
  rw [← hSdef, three_pow_two_mul]
  have e : 16 * Ssum / (9 ^ (j + 3) * 9 ^ j) = (4 / 3 ^ j) ^ 2 * (Ssum / 9 ^ (j + 3)) := by
    rw [div_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num; ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

end Rigidity.Proofs.Regularity

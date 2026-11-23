import Rigidity.Proofs.Regularity.PlanarClusterRestriction
import Rigidity.Proofs.Regularity.PlanarPartitionSizeScale
import Rigidity.Proofs.Cluster.PlanarCoarseReach
import Rigidity.Proofs.Cluster.PlanarRHMeyers

/-!
# The comparison (7.8) of a harmonic function with its coarsening on planar squares

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, Step 3: for `3^j` above the minimal
scale and `u` harmonic on the cluster,
`3^{-j} ‖u - [u]_𝒫‖_{L²(C_*(□_j))} ≤ K 3^{-j} inf_a 3^{-j-3} ‖u - a‖_{L²(C_*(□_{j+3}))}`.
The proof combines

* Lemma 3.2 for the planar partition, with the reach scales `ρ`
  (`planar_sum_abs_sub_coarseAnchor_rpow_le`):
  `∑_{C_*(□_j)} |u - [u]_𝒫|² ≤ C₃² ∑_{C_*(□_j)} 3^{4ρ} |∇u|²`;
* the Hölder inequality with the exponent `q > 1` of the Meyers estimate and a bound
  `∑ 3^{4 ρ q'} ≤ K_ρ 9^j` on the moments of the reach scales (`holder_meyers_bound`);
* the Meyers estimate on `□_j` for the restriction of `u` to the cluster of `□_{j+2}`
  (hypothesis `hM`, the conclusion of `planar_meyers_rh_uniform`), whose right side is an average
  over `□_{j+1}`;
* the Caccioppoli inequality on `𝒞 ∩ □_{j+2}` (`caccioppoli_cluster`), from `□_{j+1}`, with the
  boundary of the cluster at distance `3^{j+1}` (`energy_enl_le_caccioppoli`).

`coarseComparison_on_square` is the outcome at one scale, under the inclusions
`C_*(□_j) ⊆ C_*(□_{j+2}) ⊆ 𝒞`, `𝒞 ∩ □_{j+2} ⊆ C_*(□_{j+3})` and harmonicity on `𝒞 ∩ □_{j+3}`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical

variable {ω : Configuration 2}

/-- The constant of the planar Lemma 3.2 with reach scales. -/
noncomputable def planarCoarseConst : ℝ :=
  3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))

theorem planarCoarseConst_nonneg : 0 ≤ planarCoarseConst := by
  unfold planarCoarseConst; positivity

/-- The open Laplacian of the extension of a function on a component, at a vertex of the
component, is its Laplacian on the component. -/
theorem openLaplacian_extend_eq (C : OpenComponent ω) (u : C → ℝ) {x : Vertex 2}
    (hx : x ∈ C.supp) :
    openLaplacian ω (Rigidity.Section3.extend C u) x = componentLaplacian C u ⟨x, hx⟩ := by
  rw [Rigidity.Proofs.S3.componentLaplacian_eq_sum_lattice C u x hx, ← Finset.sum_filter,
    openLaplacian]
  congr 1
  ext z
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => ⟨openGraph_le ω h, h⟩, fun h => h.2⟩

theorem clusterGradSq_sub_const (U : Finset (Vertex 2)) (f : Vertex 2 → ℝ) (c : ℝ)
    (x : Vertex 2) : clusterGradSq ω U (fun y => f y - c) x = clusterGradSq ω U f x := by
  unfold clusterGradSq
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem clusterGradSq_le_of_eqOn {U U' : Finset (Vertex 2)} (hUU' : U ⊆ U') {F f : Vertex 2 → ℝ}
    {x : Vertex 2} (hx : F x = f x) (hF : ∀ y ∈ U, F y = f y) :
    clusterGradSq ω U F x ≤ clusterGradSq ω U' f x := by
  unfold clusterGradSq
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc ∑ y ∈ ((openGraph ω).neighborFinset x).filter (· ∈ U), (F x - F y) ^ 2
      = ∑ y ∈ ((openGraph ω).neighborFinset x).filter (· ∈ U), (f x - f y) ^ 2 :=
        Finset.sum_congr rfl fun y hy => by rw [hx, hF y (Finset.mem_filter.1 hy).2]
    _ ≤ ∑ y ∈ ((openGraph ω).neighborFinset x).filter (· ∈ U'), (f x - f y) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun y hy => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1,
            hUU' (Finset.mem_filter.1 hy).2⟩) fun _ _ _ => sq_nonneg _

theorem center_zero (k : ℕ) : center k (0 : Vertex 2) = 0 := by
  funext i
  have h3 := two_mul_halfSide_add_one k
  have h0 := halfSide_nonneg k
  simp only [center, idx, Pi.zero_apply, zero_add]
  rw [Int.ediv_eq_zero_of_lt h0 (by omega), mul_zero]

theorem mem_square_of_mem_enl {j : ℕ} {z : Vertex 2} (hz : z ∈ enl 1 j (0 : Vertex 2)) :
    z ∈ triadicCubeFinset 2 (j + 1) 0 := by
  rw [enl, mem_box, center_zero] at hz
  rw [mem_square_iff_int]
  intro i
  have h := hz i
  rw [Pi.zero_apply, sub_zero] at h
  have h3 := two_mul_halfSide_add_one (j + 1)
  generalize |z i| = a at h ⊢
  generalize (3 : ℤ) ^ (j + 1) = b at h3 ⊢
  omega

theorem mem_cube_of_mem_square {j : ℕ} {z : Vertex 2} (hz : z ∈ triadicCubeFinset 2 j 0) :
    z ∈ cube j (0 : Vertex 2) := mem_cube_zero_of_mem_square hz

/-- **The Hölder step.** For `a, b ≥ 0` on `S`, `q > 1` and the conjugate exponent `q'`, the bounds
`∑ b^q ≤ K_B N (A / (9 N))^q` and `∑ a^{q'} ≤ K_A N` give `∑ b a ≤ K_B^{1/q} K_A^{1/q'} A / 9`. -/
theorem holder_meyers_bound {ι : Type*} (S : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i) {q KA KB N A : ℝ} (hq : 1 < q)
    (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hN : 0 < N) (hA : 0 ≤ A)
    (hbq : ∑ i ∈ S, b i ^ q ≤ KB * N * (A / (9 * N)) ^ q)
    (haq : ∑ i ∈ S, a i ^ Real.conjExponent q ≤ KA * N) :
    ∑ i ∈ S, b i * a i ≤ KB ^ (1 / q) * KA ^ (1 / Real.conjExponent q) * (A / 9) := by
  have hpq := Real.HolderConjugate.conjExponent hq
  have hq0 : 0 < q := by linarith
  have hq'0 : 0 < Real.conjExponent q := hpq.symm.pos
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg S hpq hb ha
  have hB0 : 0 ≤ ∑ i ∈ S, b i ^ q := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hb i hi) _
  have hA0 : 0 ≤ ∑ i ∈ S, a i ^ Real.conjExponent q :=
    Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) _
  have hAN : 0 ≤ A / (9 * N) := by positivity
  have h1 : (∑ i ∈ S, b i ^ q) ^ (1 / q) ≤ KB ^ (1 / q) * N ^ (1 / q) * (A / (9 * N)) := by
    calc (∑ i ∈ S, b i ^ q) ^ (1 / q) ≤ (KB * N * (A / (9 * N)) ^ q) ^ (1 / q) :=
          Real.rpow_le_rpow hB0 hbq (by positivity)
      _ = KB ^ (1 / q) * N ^ (1 / q) * (A / (9 * N)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hKB hN.le,
            ← Real.rpow_mul hAN, mul_one_div_cancel hq0.ne', Real.rpow_one]
  have h2 : (∑ i ∈ S, a i ^ Real.conjExponent q) ^ (1 / Real.conjExponent q) ≤
      KA ^ (1 / Real.conjExponent q) * N ^ (1 / Real.conjExponent q) := by
    calc (∑ i ∈ S, a i ^ Real.conjExponent q) ^ (1 / Real.conjExponent q)
        ≤ (KA * N) ^ (1 / Real.conjExponent q) := Real.rpow_le_rpow hA0 haq (by positivity)
      _ = KA ^ (1 / Real.conjExponent q) * N ^ (1 / Real.conjExponent q) :=
          Real.mul_rpow hKA hN.le
  have hNN : N ^ (1 / q) * N ^ (1 / Real.conjExponent q) = N := by
    rw [← Real.rpow_add hN, one_div, one_div, hpq.inv_add_inv_eq_one, Real.rpow_one]
  have hprod := mul_le_mul h1 h2 (Real.rpow_nonneg hA0 _)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hKB _) (Real.rpow_nonneg hN.le _)) hAN)
  calc ∑ i ∈ S, b i * a i ≤ _ := h
    _ ≤ _ := hprod
    _ = KB ^ (1 / q) * KA ^ (1 / Real.conjExponent q) *
          (N ^ (1 / q) * N ^ (1 / Real.conjExponent q)) * (A / (9 * N)) := by ring
    _ = KB ^ (1 / q) * KA ^ (1 / Real.conjExponent q) * (A / 9) := by
        rw [hNN, mul_assoc _ N, show N * (A / (9 * N)) = A / 9 * (N / N) by ring,
          div_self hN.ne', mul_one]

/-- **The Caccioppoli step**: the energy of `u` on `□_{j+1}`, counted with the edges inside the
cluster of `□_{j+2}`, is at most `16 · 9^{-(j+1)} ∑_{C_*(□_{j+3})} (u - c)²`. -/
theorem energy_enl_le_caccioppoli (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h2C : ∀ x ∈ clusterVertices ω ⟨j + 2, 0⟩, x ∈ C.supp)
    (h2sq : ∀ x ∈ clusterVertices ω ⟨j + 2, 0⟩, x ∈ triadicCubeFinset 2 (j + 2) 0)
    (hU3 : ∀ x ∈ triadicCubeFinset 2 (j + 2) 0, x ∈ C.supp → x ∈ clusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ triadicCubeFinset 2 (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0) (c : ℝ) :
    ∑ z ∈ enl 1 j (0 : Vertex 2), clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) z ≤
      16 / 9 ^ (j + 1) * ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩,
        (Rigidity.Section3.extend C u x - c) ^ 2 := by
  set f := Rigidity.Section3.extend C u with hfdef
  set S₂ := clusterVertices ω ⟨j + 2, 0⟩ with hS₂
  set U := (triadicCubeFinset 2 (j + 2) 0).filter (· ∈ C.supp) with hUdef
  set V' := (triadicCubeFinset 2 (j + 1) 0).filter (· ∈ C.supp) with hV'def
  have hS₂U : S₂ ⊆ U := fun x hx => Finset.mem_filter.2 ⟨h2sq x hx, h2C x hx⟩
  have hV'U : V' ⊆ U := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨?_, hx2⟩
    rw [mem_square_iff_int] at hx1 ⊢
    intro i
    have := hx1 i
    have h3 : (3 : ℤ) ^ (j + 1) ≤ 3 ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  -- the energy on `□_{j+1}` against the energy in `U`
  have hE : ∑ z ∈ enl 1 j (0 : Vertex 2), clusterEnergy ω S₂
      (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) z ≤
      ∑ z ∈ V', clusterGradSq ω U f z := by
    calc ∑ z ∈ enl 1 j (0 : Vertex 2), clusterEnergy ω S₂
          (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) z
        = ∑ z ∈ (enl 1 j (0 : Vertex 2)).filter (· ∈ S₂), clusterGradSq ω S₂
            (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) z := by
          rw [Finset.sum_filter]; rfl
      _ ≤ ∑ z ∈ (enl 1 j (0 : Vertex 2)).filter (· ∈ S₂), clusterGradSq ω U f z :=
          Finset.sum_le_sum fun z hz => clusterGradSq_le_of_eqOn hS₂U
            (clusterExtend_clusterRestrictTo C u (Finset.mem_filter.1 hz).2)
            fun y hy => clusterExtend_clusterRestrictTo C u hy
      _ ≤ ∑ z ∈ V', clusterGradSq ω U f z := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
            fun _ _ _ => clusterGradSq_nonneg _ _ _ _
          obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
          exact Finset.mem_filter.2 ⟨mem_square_of_mem_enl hz1, h2C z hz2⟩
  -- the Caccioppoli inequality on `U` from `V'`
  have hr : (0 : ℝ) < 3 ^ (j + 1) := by positivity
  have hdist : ∀ x ∈ V', ∀ z ∈ U, (∃ y, (openGraph ω).Adj z y ∧ y ∉ U) →
      (3 : ℝ) ^ (j + 1) ≤ (supDist x z : ℝ) := by
    rintro x hx z hz ⟨y, hzy, hyU⟩
    obtain ⟨hx1, -⟩ := Finset.mem_filter.1 hx
    obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
    have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hz2 hzy
    have hy2 : y ∉ triadicCubeFinset 2 (j + 2) 0 := fun h => hyU (Finset.mem_filter.2 ⟨h, hyC⟩)
    rw [mem_square_iff_int] at hy2
    push Not at hy2
    obtain ⟨k, hk⟩ := hy2
    have hzk := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hzy) k
    have hxk := (mem_square_iff_int.1 hx1) k
    have hzk2 := (mem_square_iff_int.1 hz1) k
    have hle : (x k - z k).natAbs ≤ supDist x z :=
      Finset.le_sup (f := fun i => (x i - z i).natAbs) (Finset.mem_univ k)
    have hcast : ((3 : ℤ) ^ (j + 1) : ℤ) ≤ ((x k - z k).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      have h3 : (3 : ℤ) ^ (j + 2) = 3 * 3 ^ (j + 1) := by ring
      have hab := abs_sub_abs_le_abs_sub (z k) (x k)
      have hyz := abs_sub_abs_le_abs_sub (y k) (z k)
      rw [abs_sub_comm (z k) (x k)] at hab
      have hodd := Rigidity.Proofs.Cluster.two_mul_halfSide_add_one (j + 2)
      generalize |x k| = a at hxk hab
      generalize |z k| = b at hzk2 hab hyz
      generalize |y k| = c at hk hyz
      generalize |x k - z k| = e at hab ⊢
      generalize |y k - z k| = g at hzk hyz
      generalize (3 : ℤ) ^ (j + 1) = t at h3 hxk ⊢
      generalize (3 : ℤ) ^ (j + 2) = t2 at h3 hk hzk2 hodd
      omega
    have : ((3 : ℤ) ^ (j + 1) : ℤ) ≤ (supDist x z : ℤ) := hcast.trans (by exact_mod_cast hle)
    exact_mod_cast this
  have hu : ∀ x ∈ U, (∀ y, (openGraph ω).Adj x y → y ∈ U) →
      openLaplacian ω (fun y => f y - c) x = 0 := by
    intro x hx _
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    rw [Rigidity.Proofs.Cluster.openLaplacian_sub_const, hfdef, openLaplacian_extend_eq C u hx2]
    refine hharm x hx2 ?_
    rw [mem_square_iff_int] at hx1 ⊢
    intro i
    have := hx1 i
    have h3 : (3 : ℤ) ^ (j + 2) ≤ 3 ^ (j + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hcac := caccioppoli_cluster ω U V' hV'U hr hdist (fun y => f y - c) hu
  have e1 : ∑ x ∈ V', clusterGradSq ω U (fun y => f y - c) x = ∑ x ∈ V', clusterGradSq ω U f x :=
    Finset.sum_congr rfl fun x _ => clusterGradSq_sub_const U f c x
  rw [e1] at hcac
  have hsumU : ∑ x ∈ U.filter (fun x => ¬ (x ∈ V' ∧
      ∀ y, (nearestNeighborGraph 2).Adj x y → y ∈ V')), (f x - c) ^ 2 ≤
      ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩, (f x - c) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun _ _ _ => sq_nonneg _
    obtain ⟨hxU, -⟩ := Finset.mem_filter.1 hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hxU
    exact hU3 x hx1 hx2
  have h16 : 8 * ((2 : ℕ) : ℝ) / ((3 : ℝ) ^ (j + 1)) ^ 2 = 16 / 9 ^ (j + 1) := by
    rw [← pow_mul, mul_comm (j + 1) 2, pow_mul]; norm_num
  rw [h16] at hcac
  calc _ ≤ ∑ z ∈ V', clusterGradSq ω U f z := hE
    _ ≤ _ := hcac
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumU (by positivity)

theorem three_pow_two_mul (j : ℕ) : (3 : ℝ) ^ (2 * j) = 9 ^ j := by
  rw [pow_mul]; norm_num

/-- **The comparison (7.8) in `L²` on one square** (Armstrong–Dario, proof of Lemma 7.1, Step 3,
in dimension two): from Lemma 3.2 with the reach scales, the Hölder inequality with the moments of
the reach scales, the Meyers estimate `hM` on `□_j` for the restriction of `u` to the cluster of
`□_{j+2}`, and the Caccioppoli inequality on `𝒞 ∩ □_{j+2}`. -/
theorem coarseComparison_on_square (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
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
        (((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).reachScale z) ^ (4 : ℕ)) ^
          Real.conjExponent q ≤ Kρ * 9 ^ j) :
    clusterSquareL2 ω j (fun x => Rigidity.Section3.extend C u x - planarCoarse C u x) ≤
      12 * planarCoarseConst * Real.sqrt (CM ^ (1 / q) * Kρ ^ (1 / Real.conjExponent q)) /
        3 ^ j * clusterSquareOsc C u (j + 3) := by
  obtain ⟨E, hEdef⟩ : ∃ E : Vertex 2 → ℝ, E = clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
      (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) := ⟨_, rfl⟩
  rw [← hEdef] at hM
  have hE0 : ∀ z, 0 ≤ E z := fun z => by rw [hEdef]; exact clusterEnergy_nonneg _ _ _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ z ∈ enl 1 j (0 : Vertex 2), E z := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Finset.sum_nonneg fun z _ => hE0 z
  have hN : (0 : ℝ) < 9 ^ j := by positivity
  have hcube : ((cube j (0 : Vertex 2)).card : ℝ) = 9 ^ j := by
    rw [card_cube, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have henl : ((enl 1 j (0 : Vertex 2)).card : ℝ) = 9 * 9 ^ j := by
    rw [card_enl, ← pow_mul, mul_comm (j + 1) 2, pow_mul]; norm_num; ring
  -- Lemma 3.2
  have hL : ∑ x ∈ clusterVertices ω ⟨j, 0⟩,
      (Rigidity.Section3.extend C u x - planarCoarse C u x) ^ 2 ≤
      planarCoarseConst ^ 2 * ∑ z ∈ clusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).reachScale z) ^ (4 : ℕ) *
          gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
            (Rigidity.Section3.extend C u) z ^ 2 := by
    have h := planar_sum_abs_sub_coarseAnchor_rpow_le hP hres0 (Rigidity.Section3.extend C u)
      (s := 2) (by norm_num)
    have e1 : ∀ x ∈ clusterVertices ω ⟨j, 0⟩,
        |Rigidity.Section3.extend C u x -
          Rigidity.Section3.extend C u (planarCoarseAnchor ω x)| ^ (2 : ℝ) =
        (Rigidity.Section3.extend C u x - planarCoarse C u x) ^ 2 := fun x _ => by
      rw [Real.rpow_two, sq_abs]; rfl
    have e2 : ∀ z ∈ clusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).reachScale z) ^ ((2 : ℝ) * ((2 : ℕ) : ℝ)) *
          gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
            (Rigidity.Section3.extend C u) z ^ (2 : ℝ) =
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).reachScale z) ^ (4 : ℕ) *
          gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
            (Rigidity.Section3.extend C u) z ^ 2 := fun z _ => by
      rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.rpow_two]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Real.rpow_two] at h
    exact h
  -- the energy bound for the gradients on `C_*(□_j)`
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
  -- the Hölder step with the Meyers estimate
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
  have hHold := holder_meyers_bound (clusterVertices ω ⟨j, 0⟩)
    (a := fun z => ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).reachScale z) ^ (4 : ℕ))
    (b := fun z => gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
      (Rigidity.Section3.extend C u) z ^ 2)
    (fun z _ => by positivity) (fun z _ => sq_nonneg _) hq hKρ hCM hN hA0 hbq hmom
  set P := CM ^ (1 / q) * Kρ ^ (1 / Real.conjExponent q) with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hsum : ∑ x ∈ clusterVertices ω ⟨j, 0⟩,
      (Rigidity.Section3.extend C u x - planarCoarse C u x) ^ 2 ≤
      planarCoarseConst ^ 2 * P * (A / 9) := by
    have e : ∑ z ∈ clusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).reachScale z) ^ (4 : ℕ) *
          gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
            (Rigidity.Section3.extend C u) z ^ 2 =
        ∑ z ∈ clusterVertices ω ⟨j, 0⟩, gradNormIn (openGraph ω) (clusterVertices ω ⟨j, 0⟩)
            (Rigidity.Section3.extend C u) z ^ 2 *
          ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres0).reachScale z) ^ (4 : ℕ) :=
      Finset.sum_congr rfl fun z _ => mul_comm _ _
    rw [e] at hL
    calc _ ≤ _ := hL
      _ ≤ planarCoarseConst ^ 2 * (P * (A / 9)) :=
          mul_le_mul_of_nonneg_left hHold (sq_nonneg _)
      _ = planarCoarseConst ^ 2 * P * (A / 9) := by ring
  -- the bound for every constant
  have hK0 : 0 ≤ 12 * planarCoarseConst * Real.sqrt P / 3 ^ j := by
    have := planarCoarseConst_nonneg; positivity
  rw [clusterSquareOsc, Real.mul_iInf_of_nonneg hK0]
  refine le_ciInf fun c => ?_
  have hcac := energy_enl_le_caccioppoli C u h2C
    (fun x hx => mem_square_of_mem_clusterVertices hx) hU3 hharm c
  rw [← hEdef, ← hAdef] at hcac
  set Ssum := ∑ x ∈ clusterVertices ω ⟨j + 3, 0⟩, (Rigidity.Section3.extend C u x - c) ^ 2
    with hSsum
  have hSsum0 : 0 ≤ Ssum := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3j : (0 : ℝ) < 3 ^ j := by positivity
  have hfin : ∑ x ∈ clusterVertices ω ⟨j, 0⟩,
      (Rigidity.Section3.extend C u x - planarCoarse C u x) ^ 2 ≤
      planarCoarseConst ^ 2 * P * (16 / 81) * Ssum / 9 ^ j := by
    have h1 := mul_le_mul_of_nonneg_left hcac (by positivity : (0 : ℝ) ≤ planarCoarseConst ^ 2 * P / 9)
    have e : planarCoarseConst ^ 2 * P / 9 * (16 / 9 ^ (j + 1) * Ssum) =
        planarCoarseConst ^ 2 * P * (16 / 81) * Ssum / 9 ^ j := by
      rw [pow_succ]; field_simp; ring
    calc _ ≤ planarCoarseConst ^ 2 * P * (A / 9) := hsum
      _ = planarCoarseConst ^ 2 * P / 9 * A := by ring
      _ ≤ _ := h1
      _ = _ := e
  unfold clusterSquareL2
  rw [three_pow_two_mul, show 2 * (j + 3) = 2 * j + 6 by ring, pow_add, three_pow_two_mul]
  have hrhs : 12 * planarCoarseConst * Real.sqrt P / 3 ^ j *
      Real.sqrt (Ssum / (9 ^ j * 3 ^ 6)) =
      Real.sqrt (planarCoarseConst ^ 2 * P * (16 / 81) * Ssum / 9 ^ j / 9 ^ j) := by
    have hC0 := planarCoarseConst_nonneg
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 12 * planarCoarseConst * Real.sqrt P / 3 ^ j),
      ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hP0, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
    field_simp
    ring
  rw [hrhs]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hfin hN.le)

end Rigidity.Proofs.Regularity

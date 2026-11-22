import Rigidity.Proofs.Percolation.PlanarOmegaPointwise

/-!
# The pointwise bound of the proof of Lemma 5.9 of Armstrong and Dario

On the partition event, for `n ≥ 1` with `V = □_n` and `U = □_{n+1}` resolved, every slope `ξ`,

`ν(V, p) - μ(V, q) - q · p ≤ |q · p| / L + |q|₁ E_p(v_V) / |V| + 3 (D^ν_n + D^μ_n) / |V|
  + 24 ((3^n - 1)² |V|)⁻¹ (2 ∑_{C_*(U)} |w - [w]_P|² + 4 |U| (F_u + F_v))`,

`w = v_U - u_U`, `D^μ_n, D^ν_n` the energies of the differences of Lemma 5.4 at scale `n` in `U`
and `F_u, F_v` the flatness errors of Lemma 5.8 of the coarsenings of `u_U` and `v_U` with respect
to the affine function of slope `ξ` (displays (5.38)-(5.41) of Armstrong and Dario, in dimension
two).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

open Rigidity.Proofs.Multiscale (finsetMean affineFun)

variable {ω : Configuration 2}

theorem central_mem_subcubesAt (n : ℕ) :
    (⟨n, 0⟩ : TriadicCube 2) ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n := by
  rw [subcubesAt_eq_image (Nat.le_succ n) 0, Finset.mem_image]
  refine ⟨0, ?_, rfl⟩
  rw [Rigidity.Proofs.Multiscale.mem_cube_iff]
  intro i
  simp

theorem clusterForm_restrict_sub_le_planarMuDefect {n : ℕ} (hV : PlanarResolved ω ⟨n, 0⟩)
    (q : Fin 2 → ℝ) :
    clusterForm ω ⟨n, 0⟩
        (clusterRestrictExt ⟨n, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q) -
          planarMuMinimizer ω ⟨n, 0⟩ q)
        (clusterRestrictExt ⟨n, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q) -
          planarMuMinimizer ω ⟨n, 0⟩ q) ≤
      2 * planarMuDefect ω ⟨n + 1, 0⟩ n q := by
  have hmem : (⟨n, 0⟩ : TriadicCube 2) ∈ (subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n).filter
      (fun V => PlanarResolved ω V) := Finset.mem_filter.2 ⟨central_mem_subcubesAt n, hV⟩
  have h := Finset.single_le_sum (f := fun V : TriadicCube 2 =>
    clusterForm ω V (clusterRestrictExt V (planarMuMinimizer ω ⟨n + 1, 0⟩ q) -
      planarMuMinimizer ω V q) (clusterRestrictExt V (planarMuMinimizer ω ⟨n + 1, 0⟩ q) -
      planarMuMinimizer ω V q) / 2) (fun V _ => div_nonneg (clusterForm_self_nonneg _)
      (by norm_num)) hmem
  rw [planarMuDefect]
  linarith

theorem clusterForm_restrict_sub_le_planarNuDefect {n : ℕ} (hV : PlanarResolved ω ⟨n, 0⟩)
    (p : Fin 2 → ℝ) :
    clusterForm ω ⟨n, 0⟩
        (clusterRestrictExt ⟨n, 0⟩ (planarNuMaximizer ω ⟨n + 1, 0⟩ p) -
          planarNuMaximizer ω ⟨n, 0⟩ p)
        (clusterRestrictExt ⟨n, 0⟩ (planarNuMaximizer ω ⟨n + 1, 0⟩ p) -
          planarNuMaximizer ω ⟨n, 0⟩ p) ≤
      2 * planarNuDefect ω ⟨n + 1, 0⟩ n p := by
  have hmem : (⟨n, 0⟩ : TriadicCube 2) ∈ (subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n).filter
      (fun V => PlanarResolved ω V) := Finset.mem_filter.2 ⟨central_mem_subcubesAt n, hV⟩
  have h := Finset.single_le_sum (f := fun V : TriadicCube 2 =>
    clusterForm ω V (clusterRestrictExt V (planarNuMaximizer ω ⟨n + 1, 0⟩ p) -
      planarNuMaximizer ω V p) (clusterRestrictExt V (planarNuMaximizer ω ⟨n + 1, 0⟩ p) -
      planarNuMaximizer ω V p) / 2) (fun V _ => div_nonneg (clusterForm_self_nonneg _)
      (by norm_num)) hmem
  rw [planarNuDefect]
  linarith

/-- The squared deviation of the coarsened difference from a constant, by the flatness errors. -/
theorem sum_sq_coarsen_sub_le_flatness (U : TriadicCube 2) (a b : ClusterFun ω U)
    (ξ : Fin 2 → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices, (coarsen ω U (a - b) x -
        (finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U a y - affineFun ξ y) -
          finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U b y - affineFun ξ y))) ^ 2 ≤
      2 * U.volume * (planarFlatnessError U (coarsen ω U a) ξ +
        planarFlatnessError U (coarsen ω U b) ξ) := by
  have hvol := U.volume_pos
  have hpt : ∀ x, (coarsen ω U (a - b) x -
      (finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U a y - affineFun ξ y) -
        finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U b y - affineFun ξ y))) ^ 2 ≤
      2 * (coarsen ω U a x - affineFun ξ x -
        finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U a y - affineFun ξ y)) ^ 2 +
      2 * (coarsen ω U b x - affineFun ξ x -
        finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U b y - affineFun ξ y)) ^ 2 := by
    intro x
    have e : coarsen ω U (a - b) x = coarsen ω U a x - coarsen ω U b x := by
      simp [coarsen, map_sub]
    rw [e]
    have := add_sq_le_two_mul
      (coarsen ω U a x - affineFun ξ x -
        finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U a y - affineFun ξ y))
      (-(coarsen ω U b x - affineFun ξ x -
        finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U b y - affineFun ξ y)))
    rw [neg_sq] at this
    convert this using 2
    ring
  refine (Finset.sum_le_sum fun x _ => hpt x).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, planarFlatnessError,
    planarFlatnessError]
  field_simp

/-- **The pointwise bound of the proof of Lemma 5.9** (Armstrong and Dario, displays
(5.38)-(5.41), in dimension two). -/
theorem planarOmega_chain (hP : PlanarPartitionEvent ω) {n : ℕ} (hn : 1 ≤ n)
    (hV : PlanarResolved ω ⟨n, 0⟩) (hU : PlanarResolved ω ⟨n + 1, 0⟩) (p q ξ : Fin 2 → ℝ) :
    planarNu ω ⟨n, 0⟩ p - planarMu ω ⟨n, 0⟩ q - ∑ i, q i * p i ≤
      |∑ i, q i * p i| / ((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℝ) +
      (|q 0| + |q 1|) * boundaryError ω ⟨n, 0⟩ p (planarNuMaximizer ω ⟨n, 0⟩ p) /
        (⟨n, 0⟩ : TriadicCube 2).volume +
      3 / (⟨n, 0⟩ : TriadicCube 2).volume *
        (planarNuDefect ω ⟨n + 1, 0⟩ n p + planarMuDefect ω ⟨n + 1, 0⟩ n q) +
      24 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) *
        (2 * ∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
            (clusterExtend ω ⟨n + 1, 0⟩
                (planarNuMaximizer ω ⟨n + 1, 0⟩ p - planarMuMinimizer ω ⟨n + 1, 0⟩ q) x -
              clusterExtend ω ⟨n + 1, 0⟩
                (planarNuMaximizer ω ⟨n + 1, 0⟩ p - planarMuMinimizer ω ⟨n + 1, 0⟩ q)
                (planarCoarseAnchor ω x)) ^ 2 +
          4 * (⟨n + 1, 0⟩ : TriadicCube 2).volume *
            (planarFlatnessError ⟨n + 1, 0⟩
                (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q)) ξ +
              planarFlatnessError ⟨n + 1, 0⟩
                (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ p)) ξ)) := by
  set V : TriadicCube 2 := ⟨n, 0⟩ with hVdef
  set U : TriadicCube 2 := ⟨n + 1, 0⟩ with hUdef
  set uV := planarMuMinimizer ω V q
  set uU := planarMuMinimizer ω U q
  set vV := planarNuMaximizer ω V p
  set vU := planarNuMaximizer ω U p
  have hsol : planarNuSolution ω U p = vU := by rw [planarNuSolution, if_pos ⟨hP, hU⟩]
  rw [hsol]
  have hvol := V.volume_pos
  have hUvol := U.volume_pos
  have h3n : (1 : ℝ) < 3 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have h3n1 : (0 : ℝ) < 3 ^ n - 1 := by linarith
  have hr : (0 : ℝ) < ((3 : ℝ) ^ n - 1) ^ 2 := by positivity
  -- quadratic response on `V`
  have hqr := planarNu_sub_planarMu_sub_le hP hV p q
  -- the decomposition of `v_V - u_V`
  set R : ClusterFun ω U → ClusterFun ω V := fun f => clusterRestrictExt V f with hR
  have hRsub : R (vU - uU) = R vU - R uU := by
    funext y
    simp [hR, clusterRestrictExt, map_sub]
  have hdec : vV - uV = -(R vU - vV) + R (vU - uU) + (R uU - uV) := by
    rw [hRsub]
    abel
  have hB := clusterForm_add_add_le (-(R vU - vV)) (R (vU - uU)) (R uU - uV)
  rw [← hdec] at hB
  have hneg : clusterForm ω V (-(R vU - vV)) (-(R vU - vV)) =
      clusterForm ω V (R vU - vV) (R vU - vV) := by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [hneg] at hB
  have hdν := clusterForm_restrict_sub_le_planarNuDefect (ω := ω) hV p
  have hdμ := clusterForm_restrict_sub_le_planarMuDefect (ω := ω) hV q
  -- Caccioppoli for `w = v_U - u_U`
  obtain ⟨huA, -⟩ := planarMuMinimizer_spec hP hU q
  obtain ⟨hvA, -⟩ := planarNuMaximizer_spec (ω := ω) U p
  have hwA : vU - uU ∈ clusterHarmonic ω U := (clusterHarmonic ω U).sub_mem hvA huA
  set cv := finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U vU y - affineFun ξ y)
  set cu := finsetMean U.toIntegerCube.vertices (fun y => coarsen ω U uU y - affineFun ξ y)
  have hcac := clusterForm_restrict_le_caccioppoli hP hn hU hwA (cv - cu)
  -- coarsening
  set w := vU - uU with hw
  have hcoarse : ∑ x ∈ clusterVertices ω U, (clusterExtend ω U w x - (cv - cu)) ^ 2 ≤
      2 * ∑ x ∈ clusterVertices ω U,
          (clusterExtend ω U w x - clusterExtend ω U w (planarCoarseAnchor ω x)) ^ 2 +
        2 * ∑ x ∈ U.toIntegerCube.vertices, (coarsen ω U w x - (cv - cu)) ^ 2 := by
    have h1 : ∑ x ∈ clusterVertices ω U, (clusterExtend ω U w x - (cv - cu)) ^ 2 ≤
        ∑ x ∈ clusterVertices ω U, (2 * (clusterExtend ω U w x -
          clusterExtend ω U w (planarCoarseAnchor ω x)) ^ 2 +
          2 * (coarsen ω U w x - (cv - cu)) ^ 2) := by
      refine Finset.sum_le_sum fun x _ => ?_
      have e : clusterExtend ω U w x - (cv - cu) = (clusterExtend ω U w x -
          clusterExtend ω U w (planarCoarseAnchor ω x)) + (coarsen ω U w x - (cv - cu)) := by
        rw [coarsen]
        ring
      rw [e]
      exact add_sq_le_two_mul _ _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 : ∑ x ∈ clusterVertices ω U, (coarsen ω U w x - (cv - cu)) ^ 2 ≤
        ∑ x ∈ U.toIntegerCube.vertices, (coarsen ω U w x - (cv - cu)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => sq_nonneg _
    linarith
  have hflat := sum_sq_coarsen_sub_le_flatness U vU uU ξ
  -- assembling
  set Co := ∑ x ∈ clusterVertices ω U,
    (clusterExtend ω U w x - clusterExtend ω U w (planarCoarseAnchor ω x)) ^ 2
  set Fu := planarFlatnessError U (coarsen ω U uU) ξ
  set Fv := planarFlatnessError U (coarsen ω U vU) ξ
  set S := ∑ x ∈ clusterVertices ω U, (clusterExtend ω U w x - (cv - cu)) ^ 2
  have hS : S ≤ 2 * Co + 4 * U.volume * (Fu + Fv) := by
    have : ∑ x ∈ U.toIntegerCube.vertices, (coarsen ω U w x - (cv - cu)) ^ 2 ≤
        2 * U.volume * (Fv + Fu) := hflat
    linarith
  have hRw : clusterRestrictExt V w = R vU - R uU := hRsub
  have hBw : clusterForm ω V (R (vU - uU)) (R (vU - uU)) ≤ 16 / ((3 : ℝ) ^ n - 1) ^ 2 * S :=
    hcac
  have hBV : clusterForm ω V (vV - uV) (vV - uV) ≤
      3 * (2 * planarNuDefect ω U n p + 2 * planarMuDefect ω U n q) +
        3 * (16 / ((3 : ℝ) ^ n - 1) ^ 2 * (2 * Co + 4 * U.volume * (Fu + Fv))) := by
    have k1 : 16 / ((3 : ℝ) ^ n - 1) ^ 2 * S ≤
        16 / ((3 : ℝ) ^ n - 1) ^ 2 * (2 * Co + 4 * U.volume * (Fu + Fv)) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    linarith
  have hfin : clusterForm ω V (vV - uV) (vV - uV) / 2 / V.volume ≤
      3 / V.volume * (planarNuDefect ω U n p + planarMuDefect ω U n q) +
      24 / (((3 : ℝ) ^ n - 1) ^ 2 * V.volume) * (2 * Co + 4 * U.volume * (Fu + Fv)) := by
    have e : 3 / V.volume * (planarNuDefect ω U n p + planarMuDefect ω U n q) +
        24 / (((3 : ℝ) ^ n - 1) ^ 2 * V.volume) * (2 * Co + 4 * U.volume * (Fu + Fv)) =
        (3 * (2 * planarNuDefect ω U n p + 2 * planarMuDefect ω U n q) +
          3 * (16 / ((3 : ℝ) ^ n - 1) ^ 2 * (2 * Co + 4 * U.volume * (Fu + Fv)))) / 2 /
            V.volume := by
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hBV (by norm_num)) hvol.le
  have hFuFv : Fu + Fv = planarFlatnessError U (coarsen ω U uU) ξ +
      planarFlatnessError U (coarsen ω U vU) ξ := rfl
  linarith

end Rigidity.Percolation

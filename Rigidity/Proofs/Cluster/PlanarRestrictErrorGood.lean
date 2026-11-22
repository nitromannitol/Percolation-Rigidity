import Rigidity.Proofs.Cluster.PlanarMidCells
import Rigidity.Proofs.Percolation.PlanarRestrictErrorMeasurable

/-!
# The quantity of Lemma 5.5 of Armstrong and Dario on the good event

The deterministic part of the proof of Lemma 5.5 of Armstrong and Dario (Steps 2 and 3, with the
repaired Step 3), in dimension two, in the form of display (5.12). Let `U` be a triadic cube,
`1 ≤ j < n ≤ scale U`, and suppose that the planar partition cubes of the vertices of `U` have
scale at most `j`. Then every subcube `V` of scale `n` is resolved, and for functions `u_U` and
`u_V` of `A_*(U)` and `A_*(V)` the difference of the spatial sum of `∇[u_U]_𝒫` over the edges of
`V` and the coarse pairing of `u_V` is the pairing of `e_i` with `∇[w_V]_𝒫`,
`w_V = u_U|_V - u_V ∈ A_*(V)` (`cubeGradSum_coarsen_sub_coarsePairing`). Suppose moreover that
on the cells `□'` of scale `j - 1` of the inner squares of the subcubes (`midCells`):
* a Gehring partition `s` has cells of scale at most `j - 1` on `3□'` and
  `∑_{□'} (3^s)^t ≤ K |□'|`, and the Meyers estimate with exponent `1 + ε/2` and constant `C_M`
  holds for the functions of `A_*(V)` on every such cube (hypothesis `hMey`, which is
  `planar_meyers_clusterHarmonic_uniform` once the Gehring partition is fixed);
* the weight `Wt ≥ 3 planarReach` has `(avg_{□'} Wt^{3r})^{1/r} ≤ A`, `r` the conjugate exponent
  of `1 + ε/2`;
and `3 planarReach ≤ W` on `U`. Then, with
`Λ = 8 · 9^n C² A C_M^{1/p} 9 + 64 · 3^{n+j} C² W³` (`C` the constant of the coarse gradients),
the quantity of display (5.12) is at most `4 (Λ / 9^n) |U|⁻¹ ∑_V B(w_V, w_V)/2`
(`restrictError_le_of_good`), that is, `4 Λ / 9^n` times the normalized energy of the
differences of Lemma 5.4. Applied to the minimizers of `μ` and the maximizers of `ν` this is
`planarMuRestrictError_le_of_good` and `planarNuRestrictError_le_of_good`.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- The constant of the bound of the coarse gradients by the energy. -/
noncomputable def coarseGradConst : ℝ :=
  2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
    (2 * √((2 : ℕ) : ℝ))

/-- The constant `Λ = 8 · 9^n C² A C_M^{1/p} 9 + 64 · 3^{n+j} C² W³` of the per-subcube bound. -/
noncomputable def restrictLambda (n j : ℕ) (A CM p W : ℝ) : ℝ :=
  8 * 1 ^ 2 * 9 ^ n * (coarseGradConst ^ 2 * (A * (CM ^ (1 / p) * ((9 : ℕ) : ℝ)))) +
    64 * 1 ^ 2 * 3 ^ (n + j) * (coarseGradConst ^ 2 * W ^ 3)

/-- The spatial sum over the edges of a resolved cube `V` of the gradient of the coarsening of a
function on the cluster of `U`, minus the coarse pairing of a function on the cluster of `V`, is
the pairing of `e_i` with the gradient of the coarsening of the difference of the restriction and
the function on `V`. -/
theorem cubeGradSum_coarsen_sub_coarsePairing (hP : PlanarPartitionEvent ω) {U V : TriadicCube 2}
    (hVr : PlanarResolved ω V) (uU : ClusterFun ω U) (v : ClusterFun ω V) (i : Fin 2) :
    cubeGradSum V (coarsen ω U uU) i - coarsePairing ω V (Pi.single i 1) v =
      edgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
        (fun x => clusterExtend ω V (clusterRestrictExt V uU - v) (planarCoarseAnchor ω x)) := by
  have hco : ∀ y ∈ V.toIntegerCube.vertices,
      coarsen ω U uU y = coarsen ω V (clusterRestrictExt V uU) y := by
    intro y hy
    have hyV := (V.mem_toIntegerCube_vertices y).1 hy
    have hmem : planarCoarseAnchor ω y ∈ clusterVertices ω V := by
      unfold planarCoarseAnchor
      exact mem_clusterVertices.2 (planarAnchor_mem_planarCubeCluster hP hVr hyV)
    unfold coarsen
    rw [clusterExtend_apply_of_mem _ hmem]
    rfl
  have h1 : cubeGradSum V (coarsen ω U uU) i =
      coarsePairing ω V (Pi.single i 1) (clusterRestrictExt V uU) := by
    rw [coarsePairing_single_eq_cubeGradSum]
    simp only [cubeGradSum, Rigidity.Proofs.Multiscale.gradSum]
    refine Finset.sum_congr rfl fun x hx => ?_
    split_ifs with hxi
    · rw [hco x hx, hco _ hxi]
    · rfl
  rw [h1, ← map_sub, coarsePairing_eq_edgePairing]

/-- **The per-subcube bound** (Armstrong and Dario, proof of Lemma 5.5, Steps 2 and 3, repaired,
deterministic part, in dimension two), with the cells of scale `j - 1` of the inner square and
the Meyers estimate supplied by a Gehring partition. -/
theorem edgePairing_sq_le_restrictLambda (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j < V.scale)
    (hres : ∀ x ∈ V.vertices, (planarPartCube ω x).scale ≤ j) {w : ClusterFun ω V}
    (i : Fin 2) {ε r CM A W t K : ℝ} (s : Vertex 2 → ℕ)
    (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A) (Wt : Vertex 2 → ℝ)
    (hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z))
    (hW : ∀ z ∈ clusterVertices ω V, 3 * planarReach ω z ≤ ENNReal.ofReal W)
    (hA : ∀ c ∈ midCells V j, avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r) ≤ A)
    (hGeh : ∀ c ∈ midCells V j, (∀ z ∈ enl 1 c.1 c.2, s z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube c.1 c.2).card)
    (hMey : ∀ (k : ℕ) (x₀ : Vertex 2), (∀ x ∈ enl 1 k x₀, V.IsInterior x) →
      (∀ z ∈ enl 1 k x₀, s z ≤ k) → ∑ x ∈ cube k x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube k x₀).card →
      avg (cube k x₀) (fun x =>
          clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
        CM * avg (enl 1 k x₀) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^
          (1 + ε / 2)) :
    edgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
        (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) ^ 2 ≤
      restrictLambda V.scale j A CM (1 + ε / 2) W * clusterForm ω V w w := by
  have hVr : PlanarResolved ω V := fun z hz => (hres z hz).trans hj.le
  have hg : ∀ (x : Vertex 2) (i' : Fin 2), |(fun _ => (Pi.single i 1 : Fin 2 → ℝ)) x i'| ≤ 1 := by
    intro x i'
    by_cases h : i' = i
    · subst h
      simp
    · simp [h]
  have hcov : ∀ z ∈ boxClusterVertices ω (innerSquare V j), ∃ c ∈ midCells V j,
      z ∈ cube c.1 c.2 := fun z hz => midCells_cover V j (Finset.filter_subset _ _ hz)
  have hM : ∀ c ∈ midCells V j, avg (cube c.1 c.2) (fun x =>
      clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^
        (1 + ε / 2) := fun c hc =>
    hMey c.1 c.2 (fun x hx => midCells_isInterior hj1 hj hc hx) (hGeh c hc).1 (hGeh c hc).2
  have h := edgePairing_clusterExtend_sq_le_clusterForm hP hVr hj hres w hg Wt hWt hW hpq hCM hA0
    (midCells V j) (N := 9) hcov (fun c hc => midCells_enl_subset hj1 hj hc)
    (fun x => card_midCells_filter_le V j x) hA hM
  refine h.trans (le_of_eq ?_)
  rw [restrictLambda, coarseGradConst]

/-- **The quantity of display (5.12) on the good event** (Armstrong and Dario, Lemma 5.5,
deterministic part, with the repaired Step 3, in dimension two), for functions `u_U ∈ A_*(U)` and
`u_V ∈ A_*(V)`. -/
theorem restrictError_le_of_good (hP : PlanarPartitionEvent ω) {U : TriadicCube 2} {n j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j) (uU : ClusterFun ω U)
    (huU : uU ∈ clusterHarmonic ω U) (uV : ∀ V : TriadicCube 2, ClusterFun ω V)
    (huV : ∀ V ∈ subcubesAt U n, uV V ∈ clusterHarmonic ω V) {ε r CM A W t K : ℝ}
    (s : Vertex 2 → ℕ) (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (Wt : Vertex 2 → ℝ) (hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z))
    (hW : ∀ z ∈ U.vertices, 3 * planarReach ω z ≤ ENNReal.ofReal W)
    (hA : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r) ≤ A)
    (hGeh : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j, (∀ z ∈ enl 1 c.1 c.2, s z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube c.1 c.2).card)
    (hMey : ∀ (V : TriadicCube 2), PlanarResolved ω V → ∀ (w : ClusterFun ω V),
      w ∈ clusterHarmonic ω V → ∀ (k : ℕ) (x₀ : Vertex 2), (∀ x ∈ enl 1 k x₀, V.IsInterior x) →
      (∀ z ∈ enl 1 k x₀, s z ≤ k) → ∑ x ∈ cube k x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube k x₀).card →
      avg (cube k x₀) (fun x =>
          clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
        CM * avg (enl 1 k x₀) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^
          (1 + ε / 2)) :
    ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n, ∑ i : Fin 2,
        ((cubeGradSum V (coarsen ω U uU) i - coarsePairing ω V (Pi.single i 1) (uV V)) /
          V.volume) ^ 2 ≤
      4 * (restrictLambda n j A CM (1 + ε / 2) W / 9 ^ n) *
        ((∑ V ∈ subcubesAt U n, clusterForm ω V (clusterRestrictExt V uU - uV V)
          (clusterRestrictExt V uU - uV V) / 2) / U.volume) := by
  set Λ := restrictLambda n j A CM (1 + ε / 2) W with hΛ
  have hN := card_subcubesAt_mul hn
  have hNpos : (0 : ℝ) < (subcubesAt U n).card := by
    rcases (Nat.cast_nonneg (α := ℝ) (subcubesAt U n).card).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hN
      exact U.volume_pos.ne' hN.symm
  have hvolU := U.volume_pos
  have hterm : ∀ V ∈ subcubesAt U n, ∑ i : Fin 2,
      ((cubeGradSum V (coarsen ω U uU) i - coarsePairing ω V (Pi.single i 1) (uV V)) /
        V.volume) ^ 2 ≤
      (2 * Λ / ((9 : ℝ) ^ n) ^ 2) * clusterForm ω V (clusterRestrictExt V uU - uV V)
        (clusterRestrictExt V uU - uV V) := by
    intro V hV
    have hVs : V.scale = n := scale_of_mem_subcubesAt hV
    have hVU : V.vertices ⊆ U.vertices := subset_of_mem_subcubesAt hn hV
    have hresV : ∀ x ∈ V.vertices, (planarPartCube ω x).scale ≤ j := fun x hx => hres x (hVU hx)
    have hVr : PlanarResolved ω V := fun z hz => (hresV z hz).trans (by omega)
    have hw : clusterRestrictExt V uU - uV V ∈ clusterHarmonic ω V := by
      rw [clusterRestrictExt_eq hVU]
      exact sub_mem (clusterRestrict_mem_clusterHarmonic hP hVr hVU huU) (huV V hV)
    have hWV : ∀ z ∈ clusterVertices ω V, 3 * planarReach ω z ≤ ENNReal.ofReal W :=
      fun z hz => hW z (hVU (mem_clusterVertices.1 hz).1)
    have hvol : V.volume = (9 : ℝ) ^ n := by rw [TriadicCube.volume, hVs]
    have hi : ∀ i : Fin 2,
        ((cubeGradSum V (coarsen ω U uU) i - coarsePairing ω V (Pi.single i 1) (uV V)) /
          V.volume) ^ 2 ≤ (Λ / ((9 : ℝ) ^ n) ^ 2) * clusterForm ω V
            (clusterRestrictExt V uU - uV V) (clusterRestrictExt V uU - uV V) := by
      intro i
      rw [cubeGradSum_coarsen_sub_coarsePairing hP hVr uU (uV V) i, div_pow, hvol]
      have hb := edgePairing_sq_le_restrictLambda hP hj1 (by omega : j < V.scale) hresV i s hpq
        hCM hA0 Wt hWt hWV (hA V hV) (hGeh V hV) (hMey V hVr _ hw)
      rw [hVs] at hb
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      exact hb
    calc ∑ i : Fin 2,
        ((cubeGradSum V (coarsen ω U uU) i - coarsePairing ω V (Pi.single i 1) (uV V)) /
          V.volume) ^ 2
        ≤ ∑ _i : Fin 2, (Λ / ((9 : ℝ) ^ n) ^ 2) * clusterForm ω V
            (clusterRestrictExt V uU - uV V) (clusterRestrictExt V uU - uV V) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = (2 * Λ / ((9 : ℝ) ^ n) ^ 2) * clusterForm ω V (clusterRestrictExt V uU - uV V)
            (clusterRestrictExt V uU - uV V) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hfinal : ((subcubesAt U n).card : ℝ)⁻¹ * ((2 * Λ / ((9 : ℝ) ^ n) ^ 2) *
      ∑ V ∈ subcubesAt U n, clusterForm ω V (clusterRestrictExt V uU - uV V)
        (clusterRestrictExt V uU - uV V)) =
      4 * (Λ / 9 ^ n) * ((∑ V ∈ subcubesAt U n, clusterForm ω V (clusterRestrictExt V uU - uV V)
          (clusterRestrictExt V uU - uV V) / 2) / U.volume) := by
    rw [← Finset.sum_div, ← hN]
    field_simp
    ring
  calc ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n, ∑ i : Fin 2,
        ((cubeGradSum V (coarsen ω U uU) i - coarsePairing ω V (Pi.single i 1) (uV V)) /
          V.volume) ^ 2
      ≤ ((subcubesAt U n).card : ℝ)⁻¹ * ((2 * Λ / ((9 : ℝ) ^ n) ^ 2) *
          ∑ V ∈ subcubesAt U n, clusterForm ω V (clusterRestrictExt V uU - uV V)
            (clusterRestrictExt V uU - uV V)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNpos.le)
    _ = _ := hfinal

/-- If the planar partition cubes of the vertices of `U` have scale less than `n`, every subcube
of scale `n` is resolved, and the energies of the differences of Lemma 5.4 are summed over all the
subcubes. -/
theorem filter_planarResolved_eq {U : TriadicCube 2} {n j : ℕ} (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j) :
    (subcubesAt U n).filter (fun V => PlanarResolved ω V) = subcubesAt U n := by
  refine Finset.filter_true_of_mem fun V hV z hz => ?_
  rw [scale_of_mem_subcubesAt hV]
  exact (hres z (subset_of_mem_subcubesAt hn hV hz)).trans hjn.le

/-- **The quantity of display (5.12) for `μ` on the good event** (Armstrong and Dario, Lemma 5.5,
deterministic part, with the repaired Step 3, in dimension two): it is at most `4 Λ / 9^n` times
the normalized energy `D_n(U, q) / |U|` of the differences of Lemma 5.4. -/
theorem planarMuRestrictError_le_of_good (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j) (q : Fin 2 → ℝ)
    {ε r CM A W t K : ℝ} (s : Vertex 2 → ℕ) (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM)
    (hA0 : 0 ≤ A) (Wt : Vertex 2 → ℝ) (hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z))
    (hW : ∀ z ∈ U.vertices, 3 * planarReach ω z ≤ ENNReal.ofReal W)
    (hA : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r) ≤ A)
    (hGeh : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j, (∀ z ∈ enl 1 c.1 c.2, s z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube c.1 c.2).card)
    (hMey : ∀ (V : TriadicCube 2), PlanarResolved ω V → ∀ (w : ClusterFun ω V),
      w ∈ clusterHarmonic ω V → ∀ (k : ℕ) (x₀ : Vertex 2), (∀ x ∈ enl 1 k x₀, V.IsInterior x) →
      (∀ z ∈ enl 1 k x₀, s z ≤ k) → ∑ x ∈ cube k x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube k x₀).card →
      avg (cube k x₀) (fun x =>
          clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
        CM * avg (enl 1 k x₀) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^
          (1 + ε / 2)) :
    planarMuRestrictError ω U n q ≤
      4 * (restrictLambda n j A CM (1 + ε / 2) W / 9 ^ n) *
        (planarMuDefect ω U n q / U.volume) := by
  have hU : PlanarResolved ω U := fun z hz => (hres z hz).trans (by omega)
  have h := restrictError_le_of_good hP hj1 hjn hn hres (planarMuMinimizer ω U q)
    (planarMuMinimizer_spec hP hU q).1 (fun V => planarMuMinimizer ω V q)
    (fun V hV => (planarMuMinimizer_spec hP (fun z hz => by
      rw [scale_of_mem_subcubesAt hV]
      exact (hres z (subset_of_mem_subcubesAt hn hV hz)).trans hjn.le) q).1)
    s hpq hCM hA0 Wt hWt hW hA hGeh hMey
  rw [planarMuRestrictError, planarMuDefect, filter_planarResolved_eq hjn hn hres]
  exact h

/-- **The quantity of display (5.12) for `ν` on the good event** (Armstrong and Dario, Lemma 5.5,
second term, deterministic part, with the repaired Step 3, in dimension two). -/
theorem planarNuRestrictError_le_of_good (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j) (ξ : Fin 2 → ℝ)
    {ε r CM A W t K : ℝ} (s : Vertex 2 → ℕ) (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM)
    (hA0 : 0 ≤ A) (Wt : Vertex 2 → ℝ) (hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z))
    (hW : ∀ z ∈ U.vertices, 3 * planarReach ω z ≤ ENNReal.ofReal W)
    (hA : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r) ≤ A)
    (hGeh : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j, (∀ z ∈ enl 1 c.1 c.2, s z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube c.1 c.2).card)
    (hMey : ∀ (V : TriadicCube 2), PlanarResolved ω V → ∀ (w : ClusterFun ω V),
      w ∈ clusterHarmonic ω V → ∀ (k : ℕ) (x₀ : Vertex 2), (∀ x ∈ enl 1 k x₀, V.IsInterior x) →
      (∀ z ∈ enl 1 k x₀, s z ≤ k) → ∑ x ∈ cube k x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube k x₀).card →
      avg (cube k x₀) (fun x =>
          clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
        CM * avg (enl 1 k x₀) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^
          (1 + ε / 2)) :
    planarNuRestrictError ω U n ξ ≤
      4 * (restrictLambda n j A CM (1 + ε / 2) W / 9 ^ n) *
        (planarNuDefect ω U n ξ / U.volume) := by
  have hU : PlanarResolved ω U := fun z hz => (hres z hz).trans (by omega)
  have hsol : ∀ V : TriadicCube 2, PlanarResolved ω V →
      planarNuSolution ω V ξ = planarNuMaximizer ω V ξ := fun V hV => by
    rw [planarNuSolution, if_pos ⟨hP, hV⟩]
  have hVres : ∀ V ∈ subcubesAt U n, PlanarResolved ω V := fun V hV z hz => by
    rw [scale_of_mem_subcubesAt hV]
    exact (hres z (subset_of_mem_subcubesAt hn hV hz)).trans hjn.le
  have h := restrictError_le_of_good hP hj1 hjn hn hres (planarNuMaximizer ω U ξ)
    (planarNuMaximizer_spec U ξ).1 (fun V => planarNuMaximizer ω V ξ)
    (fun V _ => (planarNuMaximizer_spec V ξ).1) s hpq hCM hA0 Wt hWt hW hA hGeh hMey
  have hsum : ∑ V ∈ subcubesAt U n, ∑ i : Fin 2,
      ((cubeGradSum V (coarsen ω U (planarNuMaximizer ω U ξ)) i -
        coarsePairing ω V (Pi.single i 1) (planarNuSolution ω V ξ)) / V.volume) ^ 2 =
      ∑ V ∈ subcubesAt U n, ∑ i : Fin 2,
      ((cubeGradSum V (coarsen ω U (planarNuMaximizer ω U ξ)) i -
        coarsePairing ω V (Pi.single i 1) (planarNuMaximizer ω V ξ)) / V.volume) ^ 2 :=
    Finset.sum_congr rfl fun V hV => by rw [hsol V (hVres V hV)]
  rw [planarNuRestrictError, planarNuDefect, filter_planarResolved_eq hjn hn hres, hsol U hU,
    hsum]
  exact h

end Rigidity.Proofs.Cluster

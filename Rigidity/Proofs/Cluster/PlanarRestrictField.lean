import Rigidity.Proofs.Cluster.PlanarRestrictQuadGood

/-!
# The coarsened gradients of the differences of the minimizers paired with a field

The form of Lemma 5.5 of Armstrong and Dario used in Step 3 of the proof of Lemma 5.7: the pairing
of the coarsened gradients with a bounded lattice field `g` instead of a constant direction. For a
triadic cube `U` and the subcubes `V` of scale `n`, the quantity
`N⁻¹ ∑_V (⟨∇[u(·, U, q)]_𝒫, g⟩_V - ⟨∇[u(·, V, q)]_𝒫, g⟩_V)² / |V|²` (`planarMuRestrictFieldError`)
is, on the scale event, the mean of the squared pairings of `g` with the coarsened gradients of the
differences `w_V = u(·, U, q)|_V - u(·, V, q)` (`edgePairing_coarsen_sub`). The per-subcube bound of
the repaired Step 3 holds for every field with `|g| ≤ G`, with the factor `G²`
(`restrictFieldError_le_of_good`); off the bad event the quantity is at most
`G² Λ₀ D_n(U, q)/|U|` (`planarMuRestrictFieldError_le_of_not_mem_restrictBad`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

theorem edgePairing_sub_fun (D : Finset (Vertex 2)) (g : Vertex 2 → Fin 2 → ℝ)
    (f₁ f₂ : Vertex 2 → ℝ) :
    edgePairing D g (fun x => f₁ x - f₂ x) = edgePairing D g f₁ - edgePairing D g f₂ := by
  simp only [edgePairing, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · ring
  · ring

theorem edgePairing_congr (D : Finset (Vertex 2)) (g : Vertex 2 → Fin 2 → ℝ)
    {f₁ f₂ : Vertex 2 → ℝ} (h : ∀ x ∈ D, f₁ x = f₂ x) :
    edgePairing D g f₁ = edgePairing D g f₂ := by
  simp only [edgePairing]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hxi
  · rw [h x hx, h _ hxi]
  · rfl

/-- The pairing of a field with the coarsened gradient of a function on the cluster of `U` over
a resolved cube `V`, minus the pairing with the coarsened gradient of a function on the cluster of
`V`, is the pairing with the coarsened gradient of the difference of the restriction and the
function on `V`. -/
theorem edgePairing_coarsen_sub (hP : PlanarPartitionEvent ω) {U V : TriadicCube 2}
    (hVr : PlanarResolved ω V) (uU : ClusterFun ω U) (v : ClusterFun ω V)
    (g : Vertex 2 → Fin 2 → ℝ) :
    edgePairing V.toIntegerCube.vertices g (coarsen ω U uU) -
        edgePairing V.toIntegerCube.vertices g (coarsen ω V v) =
      edgePairing V.toIntegerCube.vertices g
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
  rw [edgePairing_congr _ g hco]
  have e : (fun x => clusterExtend ω V (clusterRestrictExt V uU - v) (planarCoarseAnchor ω x)) =
      fun x => coarsen ω V (clusterRestrictExt V uU) x - coarsen ω V v x := by
    funext x
    simp only [coarsen, map_sub, Pi.sub_apply]
  rw [e, edgePairing_sub_fun]

/-- The quantity `N⁻¹ ∑_V (⟨∇[u_U]_𝒫, g⟩_V - ⟨∇[u_V]_𝒫, g⟩_V)² / |V|²` for a lattice field `g`. -/
noncomputable def restrictFieldError (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ)
    (uU : ClusterFun ω U) (uV : ∀ V : TriadicCube 2, ClusterFun ω V)
    (g : Vertex 2 → Fin 2 → ℝ) : ℝ :=
  ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n,
    ((edgePairing V.toIntegerCube.vertices g (coarsen ω U uU) -
      edgePairing V.toIntegerCube.vertices g (coarsen ω V (uV V))) / V.volume) ^ 2

/-- The quantity of display (5.12) for the minimizers of `μ`, paired with a lattice field `g`. -/
noncomputable def planarMuRestrictFieldError (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ)
    (q : Fin 2 → ℝ) (g : Vertex 2 → Fin 2 → ℝ) : ℝ :=
  restrictFieldError ω U n (planarMuMinimizer ω U q) (fun V => planarMuMinimizer ω V q) g

set_option maxHeartbeats 400000 in
/-- **The quantity with a field on the good event** (deterministic part of Lemma 5.5 of
Armstrong and Dario with the repaired Step 3, for a bounded field `g`). -/
theorem restrictFieldError_le_of_good (hP : PlanarPartitionEvent ω) {U : TriadicCube 2} {n j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j) (uU : ClusterFun ω U)
    (huU : uU ∈ clusterHarmonic ω U) (uV : ∀ V : TriadicCube 2, ClusterFun ω V)
    (huV : ∀ V ∈ subcubesAt U n, uV V ∈ clusterHarmonic ω V) {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ}
    (hg : ∀ x i, |g x i| ≤ G) {ε r CM A W t K : ℝ}
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
    restrictFieldError ω U n uU uV g ≤
      2 * G ^ 2 * (restrictLambda n j A CM (1 + ε / 2) W / 9 ^ n) *
        ((∑ V ∈ subcubesAt U n, clusterForm ω V (clusterRestrictExt V uU - uV V)
          (clusterRestrictExt V uU - uV V) / 2) / U.volume) := by
  set Λ := restrictLambda n j A CM (1 + ε / 2) W with hΛ
  have hN := card_subcubesAt_mul hn
  have hvolU := U.volume_pos
  have hNpos : (0 : ℝ) < (subcubesAt U n).card := by
    rcases (Nat.cast_nonneg (α := ℝ) (subcubesAt U n).card).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hN
      exact hvolU.ne' hN.symm
  have hterm : ∀ V ∈ subcubesAt U n,
      ((edgePairing V.toIntegerCube.vertices g (coarsen ω U uU) -
        edgePairing V.toIntegerCube.vertices g (coarsen ω V (uV V))) / V.volume) ^ 2 ≤
      (G ^ 2 * Λ / ((9 : ℝ) ^ n) ^ 2) * clusterForm ω V (clusterRestrictExt V uU - uV V)
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
    have hcov : ∀ z ∈ boxClusterVertices ω (innerSquare V j), ∃ c ∈ midCells V j,
        z ∈ cube c.1 c.2 := fun z hz => midCells_cover V j (Finset.filter_subset _ _ hz)
    have hM : ∀ c ∈ midCells V j, avg (cube c.1 c.2) (fun x => clusterEnergy ω
        (clusterVertices ω V) (clusterExtend ω V (clusterRestrictExt V uU - uV V)) x ^
          (1 + ε / 2)) ≤ CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (clusterVertices ω V)
            (clusterExtend ω V (clusterRestrictExt V uU - uV V))) ^ (1 + ε / 2) := fun c hc =>
      hMey V hVr _ hw c.1 c.2 (fun x hx => midCells_isInterior hj1 (by omega) hc hx)
        ((hGeh V hV) c hc).1 ((hGeh V hV) c hc).2
    have hb := edgePairing_clusterExtend_sq_le_clusterForm hP hVr (by omega : j < V.scale) hresV
      (clusterRestrictExt V uU - uV V) hg Wt hWt hWV hpq hCM hA0 (midCells V j) (N := 9) hcov
      (fun c hc => midCells_enl_subset hj1 (by omega) hc) (fun x => card_midCells_filter_le V j x)
      (hA V hV) hM
    rw [edgePairing_coarsen_sub hP hVr uU (uV V) g, div_pow, hvol, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right (by positivity)]
    refine hb.trans (le_of_eq ?_)
    rw [hVs, hΛ, restrictLambda, coarseGradConst]
    ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hfinal : ((subcubesAt U n).card : ℝ)⁻¹ * ((G ^ 2 * Λ / ((9 : ℝ) ^ n) ^ 2) *
      ∑ V ∈ subcubesAt U n, clusterForm ω V (clusterRestrictExt V uU - uV V)
        (clusterRestrictExt V uU - uV V)) =
      2 * G ^ 2 * (Λ / 9 ^ n) * ((∑ V ∈ subcubesAt U n, clusterForm ω V
        (clusterRestrictExt V uU - uV V) (clusterRestrictExt V uU - uV V) / 2) / U.volume) := by
    rw [← Finset.sum_div, ← hN]
    generalize (∑ V ∈ subcubesAt U n, clusterForm ω V (clusterRestrictExt V uU - uV V)
      (clusterRestrictExt V uU - uV V)) = S
    have h9 : (9 : ℝ) ^ n ≠ 0 := by positivity
    have hN0 : ((subcubesAt U n).card : ℝ) ≠ 0 := hNpos.ne'
    field_simp
  unfold restrictFieldError
  calc ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n,
        ((edgePairing V.toIntegerCube.vertices g (coarsen ω U uU) -
          edgePairing V.toIntegerCube.vertices g (coarsen ω V (uV V))) / V.volume) ^ 2
      ≤ ((subcubesAt U n).card : ℝ)⁻¹ * ((G ^ 2 * Λ / ((9 : ℝ) ^ n) ^ 2) *
          ∑ V ∈ subcubesAt U n, clusterForm ω V (clusterRestrictExt V uU - uV V)
            (clusterRestrictExt V uU - uV V)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNpos.le)
    _ = _ := hfinal

theorem planarMuRestrictFieldError_le_of_good (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j) (q : Fin 2 → ℝ)
    {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G)
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
    planarMuRestrictFieldError ω U n q g ≤
      2 * G ^ 2 * (restrictLambda n j A CM (1 + ε / 2) W / 9 ^ n) *
        (planarMuDefect ω U n q / U.volume) := by
  have hU : PlanarResolved ω U := fun z hz => (hres z hz).trans (by omega)
  have h := restrictFieldError_le_of_good hP hj1 hjn hn hres (planarMuMinimizer ω U q)
    (planarMuMinimizer_spec hP hU q).1 (fun V => planarMuMinimizer ω V q)
    (fun V hV => (planarMuMinimizer_spec hP (fun z hz => by
      rw [scale_of_mem_subcubesAt hV]
      exact (hres z (subset_of_mem_subcubesAt hn hV hz)).trans hjn.le) q).1)
    hg s hpq hCM hA0 Wt hWt hW hA hGeh hMey
  rw [planarMuRestrictFieldError, planarMuDefect, filter_planarResolved_eq hjn hn hres]
  exact h

/-- **The quantity with a field off the bad event** (Armstrong and Dario, proof of Lemma 5.5,
deterministic part, for a bounded field). -/
theorem planarMuRestrictFieldError_le_of_not_mem_restrictBad {CG : ℝ}
    {s : Configuration 2 → Vertex 2 → ℕ} {ε t K CM r : ℝ} {τ : ℕ} {Aτ A₂ : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hτr : 3 * r ≤ τ) (hCM : 0 ≤ CM) (hAτ : 0 ≤ Aτ)
    (hA₂ : 0 ≤ A₂)
    (hMey : ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2)
        (_ : PlanarResolved ω V) (w : ClusterFun ω V) (_ : w ∈ clusterHarmonic ω V) (n : ℕ)
        (x₀ : Vertex 2) (s : Vertex 2 → ℕ),
        (∀ x ∈ enl 1 n x₀, V.IsInterior x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
            ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀)
            (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ (1 + ε / 2))
    (hP : PlanarPartitionEvent ω)
    (hs : (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex 2), s ω y ≤ k →
        (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
          ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2))
    (hfin : ∀ z, planarReach ω z ≠ ∞) {U : TriadicCube 2} {n : ℕ}
    (hmn : 9 * U.scale ≤ 10 * n) (hnm : n < U.scale)
    (hgood : ω ∉ restrictBad s t K τ Aτ A₂ U n) (q : Fin 2 → ℝ) {g : Vertex 2 → Fin 2 → ℝ}
    {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) :
    planarMuRestrictFieldError ω U n q g ≤
      G ^ 2 * restrictConst Aτ r CM (1 + ε / 2) A₂ * (planarMuDefect ω U n q / U.volume) := by
  obtain ⟨hcell, hnb, hRH⟩ := hs
  set j := n / 2 with hj
  set k := (n - n / 2) / 3 with hk
  have hn9 : 9 ≤ n := by omega
  have hj1 : 1 ≤ j := by omega
  have hjn : j < n := by omega
  have hjk : j + 3 * k ≤ n := by omega
  simp only [restrictBad, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or,
    not_exists, not_and, not_lt] at hgood
  obtain ⟨⟨hE2, hE5⟩, hE67⟩ := hgood
  have hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j := fun x hx =>
    hE2 hP x ((U.mem_toIntegerCube_vertices x).2 hx)
  -- the weights
  set Wt : Vertex 2 → ℝ := fun z => 3 * (planarReach ω z).toReal with hWtdef
  have hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z) := fun z => by
    show 3 * planarReach ω z ≤ ENNReal.ofReal (3 * (planarReach ω z).toReal)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (hfin z)]
    simp
  have hR1 : ∀ z, 1 ≤ (planarReach ω z).toReal := fun z => by
    have := ENNReal.toReal_mono (hfin z) (one_le_planarReach hP z)
    simpa using this
  have hW : ∀ z ∈ U.vertices, 3 * planarReach ω z ≤ ENNReal.ofReal (3 * √A₂ * 3 ^ k) := by
    intro z hz
    have h5 := hE5 z ((U.mem_toIntegerCube_vertices z).2 hz)
    have hfin2 : ∑ x ∈ cube k z, planarReach ω x ^ 2 ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun x _ => ENNReal.pow_ne_top (hfin x)
    have h1 : planarReach ω z ^ 2 ≤ ∑ x ∈ cube k z, planarReach ω x ^ 2 :=
      Finset.single_le_sum (f := fun x => planarReach ω x ^ 2) (fun _ _ => zero_le)
        (mem_cube_self k z)
    have h2 : (planarReach ω z).toReal ^ 2 ≤ A₂ * ((3 : ℝ) ^ k) ^ 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h1.trans h5)
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg hA₂ (Nat.cast_nonneg _)),
        card_cube] at this
      exact this
    have h3 : (planarReach ω z).toReal ≤ √A₂ * 3 ^ k := by
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_mul hA₂,
        Real.sqrt_sq (by positivity)] at this
    calc 3 * planarReach ω z = ENNReal.ofReal (3 * (planarReach ω z).toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (hfin z)]
          simp
      _ ≤ ENNReal.ofReal (3 * √A₂ * 3 ^ k) := ENNReal.ofReal_le_ofReal (by nlinarith)
  have hr0 : 0 < r := hpq.symm.pos
  have hA : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r) ≤ 27 * Aτ ^ (1 / r) := by
    intro V hV c hc
    have h6 := (hE67 V hV c hc).1
    have hfinτ : ∑ x ∈ cube c.1 c.2, planarReach ω x ^ τ ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun x _ => ENNReal.pow_ne_top (hfin x)
    have hsum : ∑ x ∈ cube c.1 c.2, (planarReach ω x).toReal ^ τ ≤ Aτ * (cube c.1 c.2).card := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h6
      rw [ENNReal.toReal_sum fun x _ => ENNReal.pow_ne_top (hfin x),
        ENNReal.toReal_ofReal (mul_nonneg hAτ (Nat.cast_nonneg _))] at this
      simpa only [ENNReal.toReal_pow] using this
    have hpt : ∀ x, (Wt x ^ 3) ^ r ≤ (27 : ℝ) ^ r * (planarReach ω x).toReal ^ τ := by
      intro x
      have hR0 : 0 ≤ (planarReach ω x).toReal := ENNReal.toReal_nonneg
      have e : Wt x ^ 3 = 27 * (planarReach ω x).toReal ^ 3 := by
        show (3 * (planarReach ω x).toReal) ^ 3 = _
        ring
      rw [e, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast _ 3,
        ← Real.rpow_mul hR0, ← Real.rpow_natCast _ τ]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hR1 x)
        (by exact_mod_cast hτr)) (by positivity)
    have hcpos := card_cube_pos c.1 c.2
    have havg : avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ≤ (27 : ℝ) ^ r * Aτ := by
      rw [avg, div_le_iff₀ hcpos]
      calc ∑ x ∈ cube c.1 c.2, (Wt x ^ 3) ^ r
          ≤ ∑ x ∈ cube c.1 c.2, (27 : ℝ) ^ r * (planarReach ω x).toReal ^ τ :=
            Finset.sum_le_sum fun x _ => hpt x
        _ = (27 : ℝ) ^ r * ∑ x ∈ cube c.1 c.2, (planarReach ω x).toReal ^ τ := by
            rw [Finset.mul_sum]
        _ ≤ (27 : ℝ) ^ r * (Aτ * (cube c.1 c.2).card) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (27 : ℝ) ^ r * Aτ * (cube c.1 c.2).card := by ring
    have havg0 : 0 ≤ avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) :=
      div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (by positivity) _)
        (Nat.cast_nonneg _)
    calc avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r)
        ≤ ((27 : ℝ) ^ r * Aτ) ^ (1 / r) :=
          Real.rpow_le_rpow havg0 havg (by positivity)
      _ = 27 * Aτ ^ (1 / r) := by
          rw [Real.mul_rpow (by positivity) hAτ, ← Real.rpow_mul (by norm_num),
            mul_one_div_cancel hr0.ne', Real.rpow_one]
  have hGeh : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j, (∀ z ∈ enl 1 c.1 c.2, s ω z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube c.1 c.2).card := by
    intro V hV c hc
    obtain ⟨-, h7, h8⟩ := hE67 V hV c hc
    exact ⟨h7, h8⟩
  have hMey' : ∀ (V : TriadicCube 2), PlanarResolved ω V → ∀ (w : ClusterFun ω V),
      w ∈ clusterHarmonic ω V → ∀ (k' : ℕ) (x₀ : Vertex 2), (∀ x ∈ enl 1 k' x₀, V.IsInterior x) →
      (∀ z ∈ enl 1 k' x₀, s ω z ≤ k') →
      ∑ x ∈ cube k' x₀, ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube k' x₀).card →
      avg (cube k' x₀) (fun x =>
          clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
        CM * avg (enl 1 k' x₀) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^
          (1 + ε / 2) := by
    intro V hV w hw k' x₀ hint hsk hmom
    refine hMey ω hP V hV w hw k' x₀ (s ω) hint hcell hnb (fun z hz => ?_)
      (fun k'' y hy _ => hRH k'' y hy) hmom
    exact (cube_mono (hsk z hz) z).trans (cube_subset_enl_of_mem hz)
  have h := planarMuRestrictFieldError_le_of_good hP hj1 hjn hnm.le hres q hg (s ω) hpq hCM
    (by positivity : (0 : ℝ) ≤ 27 * Aτ ^ (1 / r)) Wt hWt hW hA hGeh hMey'
  have hD0 : 0 ≤ planarMuDefect ω U n q / U.volume :=
    div_nonneg (planarMuDefect_nonneg U n q) U.volume_pos.le
  have hL := four_mul_restrictLambda_div_le (Aτ := Aτ) (r := r) (CM := CM) (p := 1 + ε / 2)
    (A₂ := A₂) hjk
  have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
  have hΛ0 : 0 ≤ restrictLambda n j (27 * Aτ ^ (1 / r)) CM (1 + ε / 2) (3 * √A₂ * 3 ^ k) / 9 ^ n := by
    unfold restrictLambda coarseGradConst
    have h1 : 0 ≤ Aτ ^ (1 / r) := Real.rpow_nonneg hAτ _
    have h2 : 0 ≤ CM ^ (1 / (1 + ε / 2)) := Real.rpow_nonneg hCM _
    positivity
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hD0)
  calc 2 * G ^ 2 * (restrictLambda n j (27 * Aτ ^ (1 / r)) CM (1 + ε / 2) (3 * √A₂ * 3 ^ k) / 9 ^ n)
      ≤ 4 * G ^ 2 * (restrictLambda n j (27 * Aτ ^ (1 / r)) CM (1 + ε / 2) (3 * √A₂ * 3 ^ k) /
          9 ^ n) := by nlinarith
    _ = G ^ 2 * (4 * (restrictLambda n j (27 * Aτ ^ (1 / r)) CM (1 + ε / 2) (3 * √A₂ * 3 ^ k) /
          9 ^ n)) := by ring
    _ ≤ G ^ 2 * restrictConst Aτ r CM (1 + ε / 2) A₂ := mul_le_mul_of_nonneg_left hL hG2

end Rigidity.Proofs.Cluster

import Rigidity.Proofs.Percolation.PlanarOmegaBad

/-!
# The pointwise inequality of the proof of Lemma 5.9 in integrable form

With `V = □_n`, `U = □_{n+1}`, `c = 3/|V|`, the energies of the differences of Lemma 5.4 are
written through the subadditivity gaps `G^μ = D^μ_n + ∑_x μ(V_x) - |U| μ(U)` and
`G^ν = D^ν_n + |U| ν(U) - ∑_x ν(V_x)` (`V_x` the subcube of scale `n` containing `x`), whose
expectations are controlled by the subadditivity error bounds, and the sums of `-μ(V_x)`, `ν(V_x)`.
On every configuration,

`ν(V) + (-μ(V)) + c |U| (-μ(U)) + c |U| ν(U) ≤ s + s/L + M_b + c₄₈ H + c₉₆ (Φ_u + Φ_v) + c M_μ
  + c ∑_x (-μ(V_x)) + c ∑_x ν(V_x) + M_bad + c (G^ν)⁺`,

the terms on the left being restricted to the resolution of `V`, `U`, where `M_b, H, Φ_u, Φ_v,
M_μ, M_bad` are majorants of the boundary term, the coarsening error, the flatness errors, the gap of
`μ` and the values on the exceptional event.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- `∑_{x ∈ U} -μ(V_x, q)` over the resolved subcubes of scale `n`. -/
noncomputable def subMuSum (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) (q : Fin 2 → ℝ) :
    ℝ :=
  ∑ x ∈ U.toIntegerCube.vertices, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube n x)
    then -planarMu ω (scaleCube n x) q else 0)

/-- `∑_{x ∈ U} ν(V_x, ξ)` over the resolved subcubes of scale `n`. -/
noncomputable def subNuSum (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) (ξ : Fin 2 → ℝ) :
    ℝ :=
  ∑ x ∈ U.toIntegerCube.vertices, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube n x)
    then planarNu ω (scaleCube n x) ξ else 0)

/-- The subadditivity gap of `μ`. -/
noncomputable def muSubGap (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) (q : Fin 2 → ℝ) : ℝ :=
  planarMuDefect ω U n q + ∑ x ∈ U.toIntegerCube.vertices,
    (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) -
    planarMu ω U q * U.volume

/-- The subadditivity gap of `ν`. -/
noncomputable def nuSubGap (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) (ξ : Fin 2 → ℝ) : ℝ :=
  planarNuDefect ω U n ξ + planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
    (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0)

theorem subMuSum_nonneg (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) (q : Fin 2 → ℝ) :
    0 ≤ subMuSum ω U n q :=
  Finset.sum_nonneg fun x _ => by
    split_ifs with h
    · linarith [planarMu_nonpos h.1 h.2 q]
    · exact le_rfl

theorem subNuSum_nonneg (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) (ξ : Fin 2 → ℝ) :
    0 ≤ subNuSum ω U n ξ :=
  Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact planarNu_nonneg ξ
    · exact le_rfl

theorem planarMuDefect_eq_gap (hP : PlanarPartitionEvent ω) (U : TriadicCube 2) (n : ℕ)
    (q : Fin 2 → ℝ) :
    planarMuDefect ω U n q = muSubGap ω U n q + subMuSum ω U n q -
      U.volume * (-planarMu ω U q) := by
  have e : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) =
      -subMuSum ω U n q := by
    rw [subMuSum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : PlanarResolved ω (scaleCube n x)
    · rw [if_pos h, if_pos ⟨hP, h⟩, neg_neg]
    · rw [if_neg h, if_neg (fun h' => h h'.2), neg_zero]
  rw [muSubGap, e]
  ring

theorem planarNuDefect_eq_gap (hP : PlanarPartitionEvent ω) (U : TriadicCube 2) (n : ℕ)
    (ξ : Fin 2 → ℝ) :
    planarNuDefect ω U n ξ = nuSubGap ω U n ξ + subNuSum ω U n ξ - U.volume * planarNu ω U ξ := by
  have e : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) =
      subNuSum ω U n ξ := by
    rw [subNuSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : PlanarResolved ω (scaleCube n x)
    · rw [if_pos h, if_pos ⟨hP, h⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.2)]
  rw [nuSubGap, e]
  ring

/-- The real inequality on the event that both `□_n` and `□_{n+1}` are resolved. -/
theorem planarOmega_real_le (hP : PlanarPartitionEvent ω) {n : ℕ} (hn : 1 ≤ n)
    (hV : PlanarResolved ω ⟨n, 0⟩) (hU : PlanarResolved ω ⟨n + 1, 0⟩) (ξ q : Fin 2 → ℝ)
    (hs : 0 ≤ ∑ i, q i * ξ i) :
    planarNu ω ⟨n, 0⟩ ξ + -planarMu ω ⟨n, 0⟩ q +
        3 / (⟨n, 0⟩ : TriadicCube 2).volume *
          ((⟨n + 1, 0⟩ : TriadicCube 2).volume * -planarMu ω ⟨n + 1, 0⟩ q) +
        3 / (⟨n, 0⟩ : TriadicCube 2).volume *
          ((⟨n + 1, 0⟩ : TriadicCube 2).volume * planarNu ω ⟨n + 1, 0⟩ ξ) ≤
      (∑ i, q i * ξ i + (∑ i, q i * ξ i) / ((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℝ)) +
      (|q 0| + |q 1|) * boundaryError ω ⟨n, 0⟩ ξ (planarNuMaximizer ω ⟨n, 0⟩ ξ) /
        (⟨n, 0⟩ : TriadicCube 2).volume +
      48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) *
        ∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
          (clusterExtend ω ⟨n + 1, 0⟩
              (planarNuMaximizer ω ⟨n + 1, 0⟩ ξ - planarMuMinimizer ω ⟨n + 1, 0⟩ q) x -
            clusterExtend ω ⟨n + 1, 0⟩
              (planarNuMaximizer ω ⟨n + 1, 0⟩ ξ - planarMuMinimizer ω ⟨n + 1, 0⟩ q)
              (planarCoarseAnchor ω x)) ^ 2 +
      96 * (⟨n + 1, 0⟩ : TriadicCube 2).volume /
          (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) *
        (planarFlatnessError ⟨n + 1, 0⟩
            (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q)) ξ +
          planarFlatnessError ⟨n + 1, 0⟩
            (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ) +
      3 / (⟨n, 0⟩ : TriadicCube 2).volume * muSubGap ω ⟨n + 1, 0⟩ n q +
      3 / (⟨n, 0⟩ : TriadicCube 2).volume * subMuSum ω ⟨n + 1, 0⟩ n q +
      3 / (⟨n, 0⟩ : TriadicCube 2).volume * subNuSum ω ⟨n + 1, 0⟩ n ξ +
      3 / (⟨n, 0⟩ : TriadicCube 2).volume * nuSubGap ω ⟨n + 1, 0⟩ n ξ := by
  have hch := planarOmega_chain hP hn hV hU ξ q ξ
  rw [abs_of_nonneg hs] at hch
  have hdμ := planarMuDefect_eq_gap hP ⟨n + 1, 0⟩ n q
  have hdν := planarNuDefect_eq_gap hP ⟨n + 1, 0⟩ n ξ
  rw [hdμ, hdν] at hch
  have hvol := (⟨n, 0⟩ : TriadicCube 2).volume_pos
  have e1 : 48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) =
      2 * (24 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume)) := by ring
  have e2 : 96 * (⟨n + 1, 0⟩ : TriadicCube 2).volume /
      (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) =
      24 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) *
        (4 * (⟨n + 1, 0⟩ : TriadicCube 2).volume) := by ring
  rw [e1, e2]
  linarith

theorem ofReal_add8_le (a b c d e f g h : ℝ) :
    ENNReal.ofReal (a + b + c + d + e + f + g + h) ≤
      ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d +
        ENNReal.ofReal e + ENNReal.ofReal f + ENNReal.ofReal g + ENNReal.ofReal h := by
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
  exact ENNReal.ofReal_add_le

/-- **The pointwise inequality of the proof of Lemma 5.9, with majorants**, on every
configuration. -/
theorem planarOmega_ennreal_le {n : ℕ} (hn : 1 ≤ n) (ξ q : Fin 2 → ℝ)
    (hs : 0 ≤ ∑ i, q i * ξ i) (ω : Configuration 2) {Mb Φu Φv : ℝ} {H Mμ Bad : ℝ≥0∞}
    (hMb : PlanarPartitionEvent ω → PlanarResolved ω ⟨n, 0⟩ →
      (|q 0| + |q 1|) * boundaryError ω ⟨n, 0⟩ ξ (planarNuMaximizer ω ⟨n, 0⟩ ξ) /
        (⟨n, 0⟩ : TriadicCube 2).volume ≤ Mb)
    (hH : PlanarPartitionEvent ω → PlanarResolved ω ⟨n + 1, 0⟩ →
      ENNReal.ofReal (∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
        (clusterExtend ω ⟨n + 1, 0⟩
            (planarNuMaximizer ω ⟨n + 1, 0⟩ ξ - planarMuMinimizer ω ⟨n + 1, 0⟩ q) x -
          clusterExtend ω ⟨n + 1, 0⟩
            (planarNuMaximizer ω ⟨n + 1, 0⟩ ξ - planarMuMinimizer ω ⟨n + 1, 0⟩ q)
            (planarCoarseAnchor ω x)) ^ 2) ≤ H)
    (hΦu : planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q)) ξ ≤ Φu)
    (hΦv : planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ ≤ Φv)
    (hMμ : PlanarPartitionEvent ω → PlanarResolved ω ⟨n + 1, 0⟩ →
      ENNReal.ofReal (muSubGap ω ⟨n + 1, 0⟩ n q) ≤ Mμ)
    (hBad : PlanarPartitionEvent ω → PlanarResolved ω ⟨n, 0⟩ → ¬ PlanarResolved ω ⟨n + 1, 0⟩ →
      ENNReal.ofReal (planarNu ω ⟨n, 0⟩ ξ) + ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) ≤ Bad) :
    (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
        ENNReal.ofReal (planarNu ω ⟨n, 0⟩ ξ) else 0) +
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
        ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) else 0) +
      ENNReal.ofReal (3 / (⟨n, 0⟩ : TriadicCube 2).volume) *
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n + 1, 0⟩ then
          ENNReal.ofReal ((⟨n + 1, 0⟩ : TriadicCube 2).volume * -planarMu ω ⟨n + 1, 0⟩ q)
          else 0) +
      ENNReal.ofReal (3 / (⟨n, 0⟩ : TriadicCube 2).volume) *
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n + 1, 0⟩ then
          ENNReal.ofReal ((⟨n + 1, 0⟩ : TriadicCube 2).volume * planarNu ω ⟨n + 1, 0⟩ ξ)
          else 0) ≤
      ENNReal.ofReal (∑ i, q i * ξ i +
          (∑ i, q i * ξ i) / ((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℝ)) +
        ENNReal.ofReal Mb +
        ENNReal.ofReal (48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume)) * H +
        ENNReal.ofReal (96 * (⟨n + 1, 0⟩ : TriadicCube 2).volume /
          (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) * (Φu + Φv)) +
        ENNReal.ofReal (3 / (⟨n, 0⟩ : TriadicCube 2).volume) * Mμ +
        ENNReal.ofReal (3 / (⟨n, 0⟩ : TriadicCube 2).volume) *
          ENNReal.ofReal (subMuSum ω ⟨n + 1, 0⟩ n q) +
        ENNReal.ofReal (3 / (⟨n, 0⟩ : TriadicCube 2).volume) *
          ENNReal.ofReal (subNuSum ω ⟨n + 1, 0⟩ n ξ) +
        Bad +
        ENNReal.ofReal (3 / (⟨n, 0⟩ : TriadicCube 2).volume) *
          (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n + 1, 0⟩ then
            ENNReal.ofReal (nuSubGap ω ⟨n + 1, 0⟩ n ξ) else 0) := by
  set c : ℝ := 3 / (⟨n, 0⟩ : TriadicCube 2).volume with hc
  have hc0 : 0 ≤ c := div_nonneg (by norm_num) (⟨n, 0⟩ : TriadicCube 2).volume_pos.le
  have hUv := (⟨n + 1, 0⟩ : TriadicCube 2).volume_pos
  by_cases hP : PlanarPartitionEvent ω
  swap
  · simp only [hP, false_and, if_false, mul_zero, add_zero]
    exact zero_le
  by_cases hU : PlanarResolved ω ⟨n + 1, 0⟩
  · by_cases hV : PlanarResolved ω ⟨n, 0⟩
    · simp only [hP, hV, hU, and_self, if_true]
      have hreal := planarOmega_real_le hP hn hV hU ξ q hs
      have hν0 := planarNu_nonneg (ω := ω) (U := ⟨n, 0⟩) ξ
      have hμ0 : 0 ≤ -planarMu ω ⟨n, 0⟩ q := by linarith [planarMu_nonpos hP hV q]
      have hνU := planarNu_nonneg (ω := ω) (U := ⟨n + 1, 0⟩) ξ
      have hμU : 0 ≤ -planarMu ω ⟨n + 1, 0⟩ q := by linarith [planarMu_nonpos hP hU q]
      have hX2 : 0 ≤ (⟨n + 1, 0⟩ : TriadicCube 2).volume * -planarMu ω ⟨n + 1, 0⟩ q :=
        mul_nonneg hUv.le hμU
      have hX4 : 0 ≤ (⟨n + 1, 0⟩ : TriadicCube 2).volume * planarNu ω ⟨n + 1, 0⟩ ξ :=
        mul_nonneg hUv.le hνU
      rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add hν0 hμ0,
        ← ENNReal.ofReal_add (add_nonneg hν0 hμ0) (mul_nonneg hc0 hX2),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hc0 hX4)]
      refine (ENNReal.ofReal_le_ofReal hreal).trans ((ofReal_add8_le _ _ _ _ _ _ _ _).trans ?_)
      have hc48 : 0 ≤ 48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) :=
        div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (⟨n, 0⟩ : TriadicCube 2).volume_pos.le)
      have hc96 : 0 ≤ 96 * (⟨n + 1, 0⟩ : TriadicCube 2).volume /
          (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) :=
        div_nonneg (mul_nonneg (by norm_num) hUv.le)
          (mul_nonneg (sq_nonneg _) (⟨n, 0⟩ : TriadicCube 2).volume_pos.le)
      have k2 := ENNReal.ofReal_le_ofReal (hMb hP hV)
      have k3 : ENNReal.ofReal (48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) *
          ∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
            (clusterExtend ω ⟨n + 1, 0⟩
                (planarNuMaximizer ω ⟨n + 1, 0⟩ ξ - planarMuMinimizer ω ⟨n + 1, 0⟩ q) x -
              clusterExtend ω ⟨n + 1, 0⟩
                (planarNuMaximizer ω ⟨n + 1, 0⟩ ξ - planarMuMinimizer ω ⟨n + 1, 0⟩ q)
                (planarCoarseAnchor ω x)) ^ 2) ≤
          ENNReal.ofReal (48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume)) * H := by
        rw [ENNReal.ofReal_mul hc48]
        exact mul_le_mul_of_nonneg_left (hH hP hU) zero_le
      have k4 := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (add_le_add hΦu hΦv) hc96)
      have k5 : ENNReal.ofReal (c * muSubGap ω ⟨n + 1, 0⟩ n q) ≤ ENNReal.ofReal c * Mμ := by
        rw [ENNReal.ofReal_mul hc0]
        exact mul_le_mul_of_nonneg_left (hMμ hP hU) zero_le
      have k6 : ENNReal.ofReal (c * subMuSum ω ⟨n + 1, 0⟩ n q) =
          ENNReal.ofReal c * ENNReal.ofReal (subMuSum ω ⟨n + 1, 0⟩ n q) := ENNReal.ofReal_mul hc0
      have k7 : ENNReal.ofReal (c * subNuSum ω ⟨n + 1, 0⟩ n ξ) =
          ENNReal.ofReal c * ENNReal.ofReal (subNuSum ω ⟨n + 1, 0⟩ n ξ) := ENNReal.ofReal_mul hc0
      have k8 : ENNReal.ofReal (c * nuSubGap ω ⟨n + 1, 0⟩ n ξ) =
          ENNReal.ofReal c * ENNReal.ofReal (nuSubGap ω ⟨n + 1, 0⟩ n ξ) := ENNReal.ofReal_mul hc0
      refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add le_rfl k2) k3) k4) k5) k6.le) k7.le) k8.le).trans ?_
      exact add_le_add (le_self_add) le_rfl
    · simp only [hP, hV, hU, and_self, and_false, if_true, if_false, zero_add]
      -- `□_n` not resolved, `□_{n+1}` resolved
      have hdμ := planarMuDefect_eq_gap hP ⟨n + 1, 0⟩ n q
      have hdν := planarNuDefect_eq_gap hP ⟨n + 1, 0⟩ n ξ
      have h1 : (⟨n + 1, 0⟩ : TriadicCube 2).volume * -planarMu ω ⟨n + 1, 0⟩ q ≤
          muSubGap ω ⟨n + 1, 0⟩ n q + subMuSum ω ⟨n + 1, 0⟩ n q := by
        have := planarMuDefect_nonneg (ω := ω) ⟨n + 1, 0⟩ n q
        linarith
      have h2 : (⟨n + 1, 0⟩ : TriadicCube 2).volume * planarNu ω ⟨n + 1, 0⟩ ξ ≤
          nuSubGap ω ⟨n + 1, 0⟩ n ξ + subNuSum ω ⟨n + 1, 0⟩ n ξ := by
        have := planarNuDefect_nonneg (ω := ω) ⟨n + 1, 0⟩ n ξ
        linarith
      have k1 : ENNReal.ofReal ((⟨n + 1, 0⟩ : TriadicCube 2).volume * -planarMu ω ⟨n + 1, 0⟩ q) ≤
          Mμ + ENNReal.ofReal (subMuSum ω ⟨n + 1, 0⟩ n q) :=
        (ENNReal.ofReal_le_ofReal h1).trans (ENNReal.ofReal_add_le.trans
          (add_le_add (hMμ hP hU) le_rfl))
      have k2 : ENNReal.ofReal ((⟨n + 1, 0⟩ : TriadicCube 2).volume * planarNu ω ⟨n + 1, 0⟩ ξ) ≤
          ENNReal.ofReal (nuSubGap ω ⟨n + 1, 0⟩ n ξ) +
            ENNReal.ofReal (subNuSum ω ⟨n + 1, 0⟩ n ξ) :=
        (ENNReal.ofReal_le_ofReal h2).trans ENNReal.ofReal_add_le
      calc ENNReal.ofReal c * ENNReal.ofReal
            ((⟨n + 1, 0⟩ : TriadicCube 2).volume * -planarMu ω ⟨n + 1, 0⟩ q) +
          ENNReal.ofReal c * ENNReal.ofReal
            ((⟨n + 1, 0⟩ : TriadicCube 2).volume * planarNu ω ⟨n + 1, 0⟩ ξ)
          ≤ ENNReal.ofReal c * (Mμ + ENNReal.ofReal (subMuSum ω ⟨n + 1, 0⟩ n q)) +
            ENNReal.ofReal c * (ENNReal.ofReal (nuSubGap ω ⟨n + 1, 0⟩ n ξ) +
              ENNReal.ofReal (subNuSum ω ⟨n + 1, 0⟩ n ξ)) := by
            gcongr
        _ = ENNReal.ofReal c * Mμ + ENNReal.ofReal c * ENNReal.ofReal (subMuSum ω ⟨n + 1, 0⟩ n q) +
            ENNReal.ofReal c * ENNReal.ofReal (subNuSum ω ⟨n + 1, 0⟩ n ξ) +
            ENNReal.ofReal c * ENNReal.ofReal (nuSubGap ω ⟨n + 1, 0⟩ n ξ) := by ring
        _ ≤ _ := by
            refine add_le_add ?_ le_rfl
            calc _ ≤ ENNReal.ofReal c * Mμ +
                  ENNReal.ofReal c * ENNReal.ofReal (subMuSum ω ⟨n + 1, 0⟩ n q) +
                  ENNReal.ofReal c * ENNReal.ofReal (subNuSum ω ⟨n + 1, 0⟩ n ξ) := le_rfl
              _ ≤ _ := by
                  refine le_trans ?_ le_self_add
                  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
                  exact le_add_self
  · by_cases hV : PlanarResolved ω ⟨n, 0⟩
    · simp only [hP, hV, hU, and_self, and_false, if_true, if_false, mul_zero, add_zero]
      exact (hBad hP hV hU).trans le_add_self
    · simp only [hP, hV, hU, and_false, if_false, mul_zero, add_zero]
      exact zero_le

theorem ofReal_subMuSum_eq (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) (q : Fin 2 → ℝ) :
    ENNReal.ofReal (subMuSum ω U n q) = ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube n x) then
        ENNReal.ofReal (-planarMu ω (scaleCube n x) q) else 0) := by
  rw [subMuSum, ENNReal.ofReal_sum_of_nonneg fun x _ => by
    split_ifs with h
    · linarith [planarMu_nonpos h.1 h.2 q]
    · exact le_rfl]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem ofReal_subNuSum_eq (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) (ξ : Fin 2 → ℝ) :
    ENNReal.ofReal (subNuSum ω U n ξ) = ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube n x) then
        ENNReal.ofReal (planarNu ω (scaleCube n x) ξ) else 0) := by
  rw [subNuSum, ENNReal.ofReal_sum_of_nonneg fun x _ => by
    split_ifs
    · exact planarNu_nonneg ξ
    · exact le_rfl]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem measurable_ofReal_subMuSum (U : TriadicCube 2) (n : ℕ) (q : Fin 2 → ℝ) :
    Measurable fun ω => ENNReal.ofReal (subMuSum ω U n q) := by
  simp_rw [ofReal_subMuSum_eq]
  exact Finset.measurable_fun_sum _ fun x _ => measurable_planarMu_indicator _ q

theorem measurable_ofReal_subNuSum (U : TriadicCube 2) (n : ℕ) (ξ : Fin 2 → ℝ) :
    Measurable fun ω => ENNReal.ofReal (subNuSum ω U n ξ) := by
  simp_rw [ofReal_subNuSum_eq]
  exact Finset.measurable_fun_sum _ fun x _ => measurable_planarNu_indicator _ ξ

/-- The integral of the right side of the pointwise inequality. -/
theorem lintegral_rhs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s0 c c48 c96 : ℝ} (hs0 : 0 ≤ s0) (hc0 : 0 ≤ c) (hc48 : 0 ≤ c48) (hc96 : 0 ≤ c96)
    {Mb Φu Φv : Ω → ℝ} {H Mμ A B Bad Gt : Ω → ℝ≥0∞}
    (mMb : AEMeasurable Mb μ) (mH : AEMeasurable H μ) (mΦu : AEMeasurable Φu μ)
    (mΦv : AEMeasurable Φv μ) (mMμ : AEMeasurable Mμ μ) (mA : AEMeasurable A μ)
    (mB : AEMeasurable B μ) (mBad : AEMeasurable Bad μ) (hΦu0 : ∀ ω, 0 ≤ Φu ω)
    (hΦv0 : ∀ ω, 0 ≤ Φv ω) {bMb bH bΦu bΦv bMμ bA bB bBad bG : ℝ}
    (IMb : ∫⁻ ω, ENNReal.ofReal (Mb ω) ∂μ ≤ ENNReal.ofReal bMb)
    (IH : ∫⁻ ω, H ω ∂μ ≤ ENNReal.ofReal bH)
    (IΦu : ∫⁻ ω, ENNReal.ofReal (Φu ω) ∂μ ≤ ENNReal.ofReal bΦu)
    (IΦv : ∫⁻ ω, ENNReal.ofReal (Φv ω) ∂μ ≤ ENNReal.ofReal bΦv)
    (IMμ : ∫⁻ ω, Mμ ω ∂μ ≤ ENNReal.ofReal bMμ) (IA : ∫⁻ ω, A ω ∂μ ≤ ENNReal.ofReal bA)
    (IB : ∫⁻ ω, B ω ∂μ ≤ ENNReal.ofReal bB) (IBad : ∫⁻ ω, Bad ω ∂μ ≤ ENNReal.ofReal bBad)
    (IG : ∫⁻ ω, Gt ω ∂μ ≤ ENNReal.ofReal bG)
    (hb : 0 ≤ bMb ∧ 0 ≤ bH ∧ 0 ≤ bΦu ∧ 0 ≤ bΦv ∧ 0 ≤ bMμ ∧ 0 ≤ bA ∧ 0 ≤ bB ∧ 0 ≤ bBad ∧
      0 ≤ bG) :
    ∫⁻ ω, (ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω) + ENNReal.ofReal c48 * H ω +
        ENNReal.ofReal (c96 * (Φu ω + Φv ω)) + ENNReal.ofReal c * Mμ ω + ENNReal.ofReal c * A ω +
        ENNReal.ofReal c * B ω + Bad ω + ENNReal.ofReal c * Gt ω) ∂μ ≤
      ENNReal.ofReal (s0 + bMb + c48 * bH + c96 * (bΦu + bΦv) + c * bMμ + c * bA + c * bB +
        bBad + c * bG) := by
  obtain ⟨hbMb, hbH, hbΦu, hbΦv, hbMμ, hbA, hbB, hbBad, hbG⟩ := hb
  have m1 : AEMeasurable (fun ω => ENNReal.ofReal (Mb ω)) μ := mMb.ennreal_ofReal
  have m2 : AEMeasurable (fun ω => ENNReal.ofReal c48 * H ω) μ := mH.const_mul _
  have m3 : AEMeasurable (fun ω => ENNReal.ofReal (c96 * (Φu ω + Φv ω))) μ :=
    ((mΦu.add mΦv).const_mul _).ennreal_ofReal
  have m4 : AEMeasurable (fun ω => ENNReal.ofReal c * Mμ ω) μ := mMμ.const_mul _
  have m5 : AEMeasurable (fun ω => ENNReal.ofReal c * A ω) μ := mA.const_mul _
  have m6 : AEMeasurable (fun ω => ENNReal.ofReal c * B ω) μ := mB.const_mul _
  have a1 := aemeasurable_const (b := ENNReal.ofReal s0) (μ := μ)
  have n1 : AEMeasurable (fun ω => ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω)) μ := a1.add m1
  have n2 : AEMeasurable (fun ω => ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω) +
      ENNReal.ofReal c48 * H ω) μ := n1.add m2
  have n3 : AEMeasurable (fun ω => ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω) +
      ENNReal.ofReal c48 * H ω + ENNReal.ofReal (c96 * (Φu ω + Φv ω))) μ := n2.add m3
  have n4 : AEMeasurable (fun ω => ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω) +
      ENNReal.ofReal c48 * H ω + ENNReal.ofReal (c96 * (Φu ω + Φv ω)) +
      ENNReal.ofReal c * Mμ ω) μ := n3.add m4
  have n5 : AEMeasurable (fun ω => ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω) +
      ENNReal.ofReal c48 * H ω + ENNReal.ofReal (c96 * (Φu ω + Φv ω)) +
      ENNReal.ofReal c * Mμ ω + ENNReal.ofReal c * A ω) μ := n4.add m5
  have n6 : AEMeasurable (fun ω => ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω) +
      ENNReal.ofReal c48 * H ω + ENNReal.ofReal (c96 * (Φu ω + Φv ω)) +
      ENNReal.ofReal c * Mμ ω + ENNReal.ofReal c * A ω + ENNReal.ofReal c * B ω) μ := n5.add m6
  have n7 : AEMeasurable (fun ω => ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω) +
      ENNReal.ofReal c48 * H ω + ENNReal.ofReal (c96 * (Φu ω + Φv ω)) +
      ENNReal.ofReal c * Mμ ω + ENNReal.ofReal c * A ω + ENNReal.ofReal c * B ω + Bad ω) μ :=
    n6.add mBad
  rw [lintegral_add_left' n7, lintegral_add_left' n6, lintegral_add_left' n5,
    lintegral_add_left' n4, lintegral_add_left' n3, lintegral_add_left' n2,
    lintegral_add_left' n1, lintegral_add_left' a1, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have k3 : ∫⁻ ω, ENNReal.ofReal (c96 * (Φu ω + Φv ω)) ∂μ ≤ ENNReal.ofReal (c96 * (bΦu + bΦv)) := by
    have e : ∀ ω, ENNReal.ofReal (c96 * (Φu ω + Φv ω)) =
        ENNReal.ofReal c96 * (ENNReal.ofReal (Φu ω) + ENNReal.ofReal (Φv ω)) := fun ω => by
      rw [ENNReal.ofReal_mul hc96, ENNReal.ofReal_add (hΦu0 ω) (hΦv0 ω)]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' mΦu.ennreal_ofReal,
      ENNReal.ofReal_mul hc96, ENNReal.ofReal_add hbΦu hbΦv]
    gcongr
  calc _ ≤ ENNReal.ofReal s0 + ENNReal.ofReal bMb + ENNReal.ofReal c48 * ENNReal.ofReal bH +
        ENNReal.ofReal (c96 * (bΦu + bΦv)) + ENNReal.ofReal c * ENNReal.ofReal bMμ +
        ENNReal.ofReal c * ENNReal.ofReal bA + ENNReal.ofReal c * ENNReal.ofReal bB +
        ENNReal.ofReal bBad + ENNReal.ofReal c * ENNReal.ofReal bG := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul hc48, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hc0,
          ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hc0]
        rw [← ENNReal.ofReal_add hs0 hbMb, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The left side of the integrated inequality, by superadditivity. -/
theorem lintegral_lhs_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {c W : ℝ}
    (f g h k : Ω → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂μ + ∫⁻ ω, g ω ∂μ + ENNReal.ofReal c * (ENNReal.ofReal W * ∫⁻ ω, h ω ∂μ) +
        ENNReal.ofReal c * (ENNReal.ofReal W * ∫⁻ ω, k ω ∂μ) ≤
      ∫⁻ ω, (f ω + g ω + ENNReal.ofReal c * (ENNReal.ofReal W * h ω) +
        ENNReal.ofReal c * (ENNReal.ofReal W * k ω)) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact (add_le_add (add_le_add (le_lintegral_add _ _) le_rfl) le_rfl).trans
    ((add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _))

/-- Back to real numbers. -/
theorem toReal_add_four_le {x y z w : ℝ≥0∞} {c W R : ℝ} (hc : 0 ≤ c) (hW : 0 ≤ W) (hR : 0 ≤ R)
    (h : x + y + ENNReal.ofReal c * (ENNReal.ofReal W * z) +
      ENNReal.ofReal c * (ENNReal.ofReal W * w) ≤ ENNReal.ofReal R) :
    x.toReal + y.toReal + c * W * (z.toReal + w.toReal) ≤ R := by
  have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have h1 : x ≠ ∞ := by intro h'; apply hne; rw [h']; simp
  have h2 : y ≠ ∞ := by intro h'; apply hne; rw [h']; simp
  have h3 : ENNReal.ofReal c * (ENNReal.ofReal W * z) ≠ ∞ := by intro h'; apply hne; rw [h']; simp
  have h4 : ENNReal.ofReal c * (ENNReal.ofReal W * w) ≠ ∞ := by intro h'; apply hne; rw [h']; simp
  have hreal := ENNReal.toReal_le_of_le_ofReal hR h
  rw [ENNReal.toReal_add (by finiteness) h4, ENNReal.toReal_add (by finiteness) h3,
    ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hW] at hreal
  linarith

/-- **The pointwise inequality of the proof of Lemma 5.9, integrated.** -/
theorem planarOmega_integral_le {p : unitInterval} {n : ℕ} (hn : 1 ≤ n) (ξ q : Fin 2 → ℝ)
    (hs : 0 ≤ ∑ i, q i * ξ i) {Mb Φu Φv : Configuration 2 → ℝ}
    {H Mμ Bad : Configuration 2 → ℝ≥0∞}
    (mMb : AEMeasurable Mb (latticeBondLaw 2 p)) (mH : AEMeasurable H (latticeBondLaw 2 p))
    (mΦu : AEMeasurable Φu (latticeBondLaw 2 p)) (mΦv : AEMeasurable Φv (latticeBondLaw 2 p))
    (mMμ : AEMeasurable Mμ (latticeBondLaw 2 p)) (mBad : AEMeasurable Bad (latticeBondLaw 2 p))
    (hΦu0 : ∀ ω, 0 ≤ Φu ω) (hΦv0 : ∀ ω, 0 ≤ Φv ω)
    (hMb : ∀ ω, PlanarPartitionEvent ω → PlanarResolved ω ⟨n, 0⟩ →
      (|q 0| + |q 1|) * boundaryError ω ⟨n, 0⟩ ξ (planarNuMaximizer ω ⟨n, 0⟩ ξ) /
        (⟨n, 0⟩ : TriadicCube 2).volume ≤ Mb ω)
    (hH : ∀ ω, PlanarPartitionEvent ω → PlanarResolved ω ⟨n + 1, 0⟩ →
      ENNReal.ofReal (∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
        (clusterExtend ω ⟨n + 1, 0⟩
            (planarNuMaximizer ω ⟨n + 1, 0⟩ ξ - planarMuMinimizer ω ⟨n + 1, 0⟩ q) x -
          clusterExtend ω ⟨n + 1, 0⟩
            (planarNuMaximizer ω ⟨n + 1, 0⟩ ξ - planarMuMinimizer ω ⟨n + 1, 0⟩ q)
            (planarCoarseAnchor ω x)) ^ 2) ≤ H ω)
    (hΦu : ∀ᵐ ω ∂(latticeBondLaw 2 p), planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q)) ξ ≤ Φu ω)
    (hΦv : ∀ᵐ ω ∂(latticeBondLaw 2 p), planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ ≤ Φv ω)
    (hMμ : ∀ ω, PlanarPartitionEvent ω → PlanarResolved ω ⟨n + 1, 0⟩ →
      ENNReal.ofReal (muSubGap ω ⟨n + 1, 0⟩ n q) ≤ Mμ ω)
    (hBad : ∀ ω, PlanarPartitionEvent ω → PlanarResolved ω ⟨n, 0⟩ →
      ¬ PlanarResolved ω ⟨n + 1, 0⟩ →
      ENNReal.ofReal (planarNu ω ⟨n, 0⟩ ξ) + ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) ≤ Bad ω)
    {bMb bH bΦu bΦv bMμ bX1 bX3 bBad bG : ℝ}
    (IMb : ∫⁻ ω, ENNReal.ofReal (Mb ω) ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal bMb)
    (IH : ∫⁻ ω, H ω ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal bH)
    (IΦu : ∫⁻ ω, ENNReal.ofReal (Φu ω) ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal bΦu)
    (IΦv : ∫⁻ ω, ENNReal.ofReal (Φv ω) ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal bΦv)
    (IMμ : ∫⁻ ω, Mμ ω ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal bMμ)
    (IX1 : ∫⁻ ω, ENNReal.ofReal (subMuSum ω ⟨n + 1, 0⟩ n q) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal bX1)
    (IX3 : ∫⁻ ω, ENNReal.ofReal (subNuSum ω ⟨n + 1, 0⟩ n ξ) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal bX3)
    (IBad : ∫⁻ ω, Bad ω ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal bBad)
    (IG : ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n + 1, 0⟩ then
      ENNReal.ofReal (nuSubGap ω ⟨n + 1, 0⟩ n ξ) else 0) ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal bG)
    (hb : 0 ≤ bMb ∧ 0 ≤ bH ∧ 0 ≤ bΦu ∧ 0 ≤ bΦv ∧ 0 ≤ bMμ ∧ 0 ≤ bX1 ∧ 0 ≤ bX3 ∧ 0 ≤ bBad ∧
      0 ≤ bG) :
    planarNuMean p n ξ + planarMuMean p n q +
        3 / (⟨n, 0⟩ : TriadicCube 2).volume * (⟨n + 1, 0⟩ : TriadicCube 2).volume *
          (planarMuMean p (n + 1) q + planarNuMean p (n + 1) ξ) ≤
      (∑ i, q i * ξ i + (∑ i, q i * ξ i) / ((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℝ)) +
        bMb + 48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) * bH +
        96 * (⟨n + 1, 0⟩ : TriadicCube 2).volume /
          (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) * (bΦu + bΦv) +
        3 / (⟨n, 0⟩ : TriadicCube 2).volume * bMμ +
        3 / (⟨n, 0⟩ : TriadicCube 2).volume * bX1 +
        3 / (⟨n, 0⟩ : TriadicCube 2).volume * bX3 + bBad +
        3 / (⟨n, 0⟩ : TriadicCube 2).volume * bG := by
  obtain ⟨hbMb, hbH, hbΦu, hbΦv, hbMμ, hbX1, hbX3, hbBad, hbG⟩ := hb
  set μP := latticeBondLaw 2 p
  set c : ℝ := 3 / (⟨n, 0⟩ : TriadicCube 2).volume with hc
  have hc0 : 0 ≤ c := div_nonneg (by norm_num) (⟨n, 0⟩ : TriadicCube 2).volume_pos.le
  set c48 : ℝ := 48 / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) with hc48d
  have hc48 : 0 ≤ c48 :=
    div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (⟨n, 0⟩ : TriadicCube 2).volume_pos.le)
  set c96 : ℝ := 96 * (⟨n + 1, 0⟩ : TriadicCube 2).volume /
    (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube 2).volume) with hc96d
  have hc96 : 0 ≤ c96 := div_nonneg (mul_nonneg (by norm_num)
    (⟨n + 1, 0⟩ : TriadicCube 2).volume_pos.le)
    (mul_nonneg (sq_nonneg _) (⟨n, 0⟩ : TriadicCube 2).volume_pos.le)
  set W : ℝ := (⟨n + 1, 0⟩ : TriadicCube 2).volume with hW
  have hW0 : 0 ≤ W := (⟨n + 1, 0⟩ : TriadicCube 2).volume_pos.le
  set s0 : ℝ := ∑ i, q i * ξ i + (∑ i, q i * ξ i) / ((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℝ)
  have hs0 : 0 ≤ s0 := add_nonneg hs (div_nonneg hs (Nat.cast_nonneg _))
  -- the four functions on the left
  set fν : Configuration 2 → ℝ≥0∞ := fun ω => if PlanarPartitionEvent ω ∧
    PlanarResolved ω ⟨n, 0⟩ then ENNReal.ofReal (planarNu ω ⟨n, 0⟩ ξ) else 0
  set fμ : Configuration 2 → ℝ≥0∞ := fun ω => if PlanarPartitionEvent ω ∧
    PlanarResolved ω ⟨n, 0⟩ then ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) else 0
  set gμ : Configuration 2 → ℝ≥0∞ := fun ω => if PlanarPartitionEvent ω ∧
    PlanarResolved ω ⟨n + 1, 0⟩ then ENNReal.ofReal (-planarMu ω ⟨n + 1, 0⟩ q) else 0
  set gν : Configuration 2 → ℝ≥0∞ := fun ω => if PlanarPartitionEvent ω ∧
    PlanarResolved ω ⟨n + 1, 0⟩ then ENNReal.ofReal (planarNu ω ⟨n + 1, 0⟩ ξ) else 0
  set Gt : Configuration 2 → ℝ≥0∞ := fun ω => if PlanarPartitionEvent ω ∧
    PlanarResolved ω ⟨n + 1, 0⟩ then ENNReal.ofReal (nuSubGap ω ⟨n + 1, 0⟩ n ξ) else 0
  have hgμ : ∀ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n + 1, 0⟩ then
      ENNReal.ofReal (W * -planarMu ω ⟨n + 1, 0⟩ q) else 0) = ENNReal.ofReal W * gμ ω := by
    intro ω
    simp only [gμ]
    split_ifs
    · exact ENNReal.ofReal_mul hW0
    · simp
  have hgν : ∀ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n + 1, 0⟩ then
      ENNReal.ofReal (W * planarNu ω ⟨n + 1, 0⟩ ξ) else 0) = ENNReal.ofReal W * gν ω := by
    intro ω
    simp only [gν]
    split_ifs
    · exact ENNReal.ofReal_mul hW0
    · simp
  have hpt : ∀ᵐ ω ∂μP, fν ω + fμ ω + ENNReal.ofReal c * (ENNReal.ofReal W * gμ ω) +
      ENNReal.ofReal c * (ENNReal.ofReal W * gν ω) ≤
      ENNReal.ofReal s0 + ENNReal.ofReal (Mb ω) + ENNReal.ofReal c48 * H ω +
        ENNReal.ofReal (c96 * (Φu ω + Φv ω)) + ENNReal.ofReal c * Mμ ω +
        ENNReal.ofReal c * ENNReal.ofReal (subMuSum ω ⟨n + 1, 0⟩ n q) +
        ENNReal.ofReal c * ENNReal.ofReal (subNuSum ω ⟨n + 1, 0⟩ n ξ) + Bad ω +
        ENNReal.ofReal c * Gt ω := by
    filter_upwards [hΦu, hΦv] with ω hu hv
    rw [← hgμ, ← hgν]
    exact planarOmega_ennreal_le hn ξ q hs ω (hMb ω) (hH ω) hu hv (hMμ ω) (hBad ω)
  have hint := lintegral_mono_ae (μ := μP) hpt
  have hR := lintegral_rhs_le (μ := μP) hs0 hc0 hc48 hc96 mMb mH mΦu mΦv mMμ
    (measurable_ofReal_subMuSum _ n q).aemeasurable (measurable_ofReal_subNuSum _ n ξ).aemeasurable
    mBad hΦu0 hΦv0 IMb IH IΦu IΦv IMμ IX1 IX3 IBad IG
    ⟨hbMb, hbH, hbΦu, hbΦv, hbMμ, hbX1, hbX3, hbBad, hbG⟩
  have htot := ((lintegral_lhs_ge (μ := μP) fν fμ gμ gν).trans hint).trans hR
  have hreal := toReal_add_four_le hc0 hW0 (by positivity) htot
  have e : planarNuMean p n ξ + planarMuMean p n q + c * W *
      (planarMuMean p (n + 1) q + planarNuMean p (n + 1) ξ) =
      (∫⁻ ω, fν ω ∂μP).toReal + (∫⁻ ω, fμ ω ∂μP).toReal +
        c * W * ((∫⁻ ω, gμ ω ∂μP).toReal + (∫⁻ ω, gν ω ∂μP).toReal) := rfl
  rw [e]
  exact hreal

end Rigidity.Percolation

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

end Rigidity.Percolation

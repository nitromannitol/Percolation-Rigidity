import Rigidity.Proofs.Percolation.PlanarOmegaAssembly

/-!
# The expectations of the subadditivity terms in the proof of Lemma 5.9

* `exists_lintegral_subMuSum_le`, `exists_lintegral_subNuSum_le`: by the approximate stationarity
  of `μ` and `ν`, `E[∑_{x ∈ U} -μ(V_x)] ≤ |U| (E[-μ(□_n)] + C |q|₁² exp(-c 3ⁿ))`, and likewise for
  `ν`;
* `exists_lintegral_nuSubGap_le`, `exists_muSubGap_majorant`: the subadditivity gaps have
  expectation at most `C |ξ|₁² |U| / 3^{n/2}` (Lemma 5.4 of Armstrong and Dario, in dimension
  two).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical ENNReal

namespace Rigidity.Percolation

theorem exists_lintegral_subMuSum_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (U : TriadicCube 2) (n : ℕ) (q : Fin 2 → ℝ),
      ∫⁻ ω, ENNReal.ofReal (subMuSum ω U n q) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (U.volume * (planarMuMean p n q +
          C * ((|q 0| + |q 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ n)))) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_lintegral_neg_planarMu_le_of_scale_eq hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, c, hc, fun U n q => ?_⟩
  simp_rw [ofReal_subMuSum_eq]
  rw [lintegral_finsetSum _ fun x _ => measurable_planarMu_indicator _ q]
  set e : ℝ := (|q 0| + |q 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ n) with he
  have he0 : 0 ≤ e := by positivity
  have hfin : ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
      ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) else 0) ∂(latticeBondLaw 2 p) =
      ENNReal.ofReal (planarMuMean p n q) := by
    rw [planarMuMean, ENNReal.ofReal_toReal]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (exists_lintegral_neg_planarMu_le hpc).choose_spec.1
      ENNReal.ofReal_ne_top) ((exists_lintegral_neg_planarMu_le hpc).choose_spec.2 _ q)
  have hpt : ∀ x ∈ U.toIntegerCube.vertices, ∫⁻ ω, (if PlanarPartitionEvent ω ∧
      PlanarResolved ω (scaleCube n x) then ENNReal.ofReal (-planarMu ω (scaleCube n x) q)
      else 0) ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal (planarMuMean p n q + C.toReal * e) := by
    intro x _
    have h1 := h ⟨n, 0⟩ (scaleCube n x) (by rw [scale_scaleCube]) q
    rw [hfin, ← he] at h1
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (p := planarMuMean p n q) (q := C.toReal * e) ENNReal.toReal_nonneg
      (mul_nonneg ENNReal.toReal_nonneg he0),
      ENNReal.ofReal_mul (p := C.toReal) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_toIntegerCube_vertices_eq]
  rfl

theorem exists_lintegral_subNuSum_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (U : TriadicCube 2) (n : ℕ) (ξ : Fin 2 → ℝ),
      ∫⁻ ω, ENNReal.ofReal (subNuSum ω U n ξ) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (U.volume * (planarNuMean p n ξ +
          C * ((|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ n)))) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_lintegral_planarNu_le_of_scale_eq hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, c, hc, fun U n ξ => ?_⟩
  simp_rw [ofReal_subNuSum_eq]
  rw [lintegral_finsetSum _ fun x _ => measurable_planarNu_indicator _ ξ]
  set e : ℝ := (|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ n) with he
  have he0 : 0 ≤ e := by positivity
  have hfin : ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
      ENNReal.ofReal (planarNu ω ⟨n, 0⟩ ξ) else 0) ∂(latticeBondLaw 2 p) =
      ENNReal.ofReal (planarNuMean p n ξ) := by
    rw [planarNuMean, ENNReal.ofReal_toReal]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_planarNu_le p ⟨n, 0⟩ ξ)
  have hpt : ∀ x ∈ U.toIntegerCube.vertices, ∫⁻ ω, (if PlanarPartitionEvent ω ∧
      PlanarResolved ω (scaleCube n x) then ENNReal.ofReal (planarNu ω (scaleCube n x) ξ)
      else 0) ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal (planarNuMean p n ξ + C.toReal * e) := by
    intro x _
    have h1 := h ⟨n, 0⟩ (scaleCube n x) (by rw [scale_scaleCube]) ξ
    rw [hfin, ← he] at h1
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (p := planarNuMean p n ξ) (q := C.toReal * e) ENNReal.toReal_nonneg
      (mul_nonneg ENNReal.toReal_nonneg he0),
      ENNReal.ofReal_mul (p := C.toReal) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_toIntegerCube_vertices_eq]
  rfl

theorem exists_lintegral_nuSubGap_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ ξ : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (nuSubGap ω U n ξ) else 0) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * ((|ξ 0| + |ξ 1|) ^ 2 * U.volume / Real.sqrt (3 ^ n))) := by
  obtain ⟨C, hC, h⟩ := exists_lintegral_le_of_le_nuSubadditivityBound hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun U n hn ξ => ?_⟩
  refine (h U n hn ξ (fun ω => nuSubGap ω U n ξ) fun ω hP hU =>
    planarNuDefect_add_sub_le hP hU hn ξ).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]

theorem exists_muSubGap_majorant {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ q : Fin 2 → ℝ,
      ∃ M : Configuration 2 → ℝ≥0∞, Measurable M ∧
        (∀ ω, PlanarPartitionEvent ω → PlanarResolved ω U →
          ENNReal.ofReal (muSubGap ω U n q) ≤ M ω) ∧
        ∫⁻ ω, M ω ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * ((|q 0| + |q 1|) ^ 2 * U.volume / Real.sqrt (3 ^ n))) := by
  obtain ⟨C, hC, h⟩ := exists_subadditivityMajorant hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun U n hn q => ?_⟩
  obtain ⟨M, hM, hle, hint⟩ := h U n hn q
  refine ⟨M, hM, fun ω hP hU => ?_, hint.trans (le_of_eq ?_)⟩
  · have := hle (fun ω => muSubGap ω U n q) (fun ω hP hU =>
      planarMuDefect_add_sum_sub_le hP hU hn q) ω
    rw [if_pos ⟨hP, hU⟩] at this
    exact this
  · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]

end Rigidity.Percolation

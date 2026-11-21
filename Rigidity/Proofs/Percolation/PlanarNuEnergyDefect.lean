import Rigidity.Proofs.Percolation.PlanarSecondVariation
import Rigidity.Proofs.Percolation.PlanarNuSubadditiveMoments
import Rigidity.Proofs.Percolation.PlanarNuConvergence

/-!
# The energy of the differences between the maximizers of `ν` at two scales

For a triadic cube `U` and `n ≤ U.scale`, let `v` be a maximizer of `ν(U, p)` and `v_V` a maximizer
of `ν(V, p)` for each resolved subcube `V` of scale `n`. The quantity

`D^ν_n(U, p) = ∑_V B_V(v|_V - v_V, v|_V - v_V) / 2`

is the energy of the differences `v - v_V` on the clusters of the subcubes. By the second variation
and the subadditivity error bound,

`D^ν_n(U, p) + |U| ν(U, p) - ∑_{x ∈ U} 1{V(x) resolved} ν(V(x), p) ≤
  (9/4) |p|₁² (3 ^ (n / 2) G + |U| / 3 ^ (n / 2))`,

with `G` the number of exceptional vertices, and, taking expectations and using the stationarity of
`ν` across cubes of the same scale,

`E[D^ν_n(U, p)] + |U| E[ν(U, p)] ≤ |U| E[ν(W, p)] + C |p|₁² |U| (3 ^ (-n / 2) + exp (-c 3 ^ n))`

for every cube `W` of scale `n`. This is Lemma 5.4 of Armstrong and Dario for `ν` (display (5.10),
second term), in dimension two.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- A maximizer of `ν(U, p)`. -/
noncomputable def planarNuMaximizer (ω : Configuration 2) (U : TriadicCube 2) (p : Fin 2 → ℝ) :
    ClusterFun ω U :=
  Classical.choose (exists_planarNu_maximizer (ω := ω) (U := U) p)

theorem planarNuMaximizer_spec (U : TriadicCube 2) (p : Fin 2 → ℝ) :
    planarNuMaximizer ω U p ∈ clusterHarmonic ω U ∧ ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U w (planarNuMaximizer ω U p) = fluxPairing ω U p w := by
  obtain ⟨h1, h2, -⟩ := Classical.choose_spec (exists_planarNu_maximizer (ω := ω) (U := U) p)
  exact ⟨h1, h2⟩

/-- The energy `D^ν_n(U, p)` of the differences between the restrictions of the maximizer of
`ν(U, p)` and the maximizers of `ν(V, p)` on the resolved subcubes `V` of scale `n`. -/
noncomputable def planarNuDefect (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ)
    (p : Fin 2 → ℝ) : ℝ :=
  ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
    clusterForm ω V (clusterRestrictExt V (planarNuMaximizer ω U p) - planarNuMaximizer ω V p)
      (clusterRestrictExt V (planarNuMaximizer ω U p) - planarNuMaximizer ω V p) / 2

theorem planarNuDefect_nonneg (U : TriadicCube 2) (n : ℕ) (p : Fin 2 → ℝ) :
    0 ≤ planarNuDefect ω U n p :=
  Finset.sum_nonneg fun _ _ => div_nonneg (clusterForm_self_nonneg _) (by norm_num)

/-- The energy of the differences and the subadditivity defect of `ν`, with Young's parameter. -/
theorem planarNuDefect_add_le_young (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (p : Fin 2 → ℝ) {t : ℝ} (ht : 0 < t) :
    planarNuDefect ω U n p + planarNu ω U p * U.volume ≤
      ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) p else 0) +
        (|p 0| + |p 1|) * (9 * (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) / t +
          t * (9 * (|p 0| + |p 1|) ^ 2 * U.volume)) / 4 := by
  rw [planarNuDefect]
  obtain ⟨hv, hvar⟩ := planarNuMaximizer_spec (ω := ω) U p
  have hsub := sum_clusterForm_sub_add_planarNu_le_sum_subcubes hP hn p hv hvar
    (fun V => planarNuMaximizer ω V p) (fun V _ _ => planarNuMaximizer_spec V p)
  beta_reduce at hsub
  set v := planarNuMaximizer ω U p with hvdef
  have hvol := U.volume_pos
  have hνB := planarNu_mul_volume_eq p hv hvar
  have hνle := planarNu_le (ω := ω) (U := U) p
  have hB : 2 * clusterForm ω U v v ≤ 9 * (|p 0| + |p 1|) ^ 2 * U.volume := by
    have := mul_le_mul_of_nonneg_right hνle hvol.le
    linarith
  have herr := nuError_le_young hP hU (n := n) p v ht
  set G := ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x with hG
  have hP1 : 0 ≤ |p 0| + |p 1| := by positivity
  have h1 := mul_le_mul_of_nonneg_left hB ht.le
  have h2 := mul_le_mul_of_nonneg_left (add_le_add (le_refl (9 * G / t)) h1) hP1
  linarith

/-- **The energy of the differences and the subadditivity defect of `ν`** (Armstrong and Dario,
proof of Lemma 5.4, analogue of display (5.11) for `ν`, with the planar error bound). -/
theorem planarNuDefect_add_sub_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (ξ : Fin 2 → ℝ) :
    planarNuDefect ω U n ξ + planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
        (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) ≤
      9 / 4 * (|ξ 0| + |ξ 1|) ^ 2 * Real.sqrt (3 ^ n) *
          (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) +
        9 / 4 * ((|ξ 0| + |ξ 1|) ^ 2 * U.volume / Real.sqrt (3 ^ n)) := by
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hvol := U.volume_pos
  have hP0 : 0 ≤ P₁ := by positivity
  have hG0 : 0 ≤ ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x :=
    Finset.sum_nonneg fun x _ => exceptionalIndicator_nonneg n x
  rcases hP0.eq_or_lt with hz | hpos
  · have hy := planarNuDefect_add_le_young hP hU hn ξ (t := 1) one_pos
    rw [← hP₁, ← hz] at hy
    rw [← hz]
    have : (0 : ℝ) ≤ 9 / 4 * 0 ^ 2 * s *
        (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) +
        9 / 4 * (0 ^ 2 * U.volume / s) := by
      simp
    simp only [zero_mul, zero_div, add_zero] at hy
    linarith
  · have ht : 0 < 1 / (P₁ * s) := by positivity
    have hy := planarNuDefect_add_le_young hP hU hn ξ ht
    rw [← hP₁] at hy
    have e : P₁ * (9 * (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) /
        (1 / (P₁ * s)) + 1 / (P₁ * s) * (9 * P₁ ^ 2 * U.volume)) / 4 =
        9 / 4 * P₁ ^ 2 * s *
          (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) +
        9 / 4 * (P₁ ^ 2 * U.volume / s) := by
      field_simp
    rw [e] at hy
    linarith

/-- **Expected size of functions dominated by the subadditivity error bound of `ν`.** -/
theorem exists_lintegral_le_of_le_nuSubadditivityBound {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ ξ : Fin 2 → ℝ,
      ∀ g : Configuration 2 → ℝ, (∀ ω, PlanarPartitionEvent ω → PlanarResolved ω U →
        g ω ≤ 9 / 4 * (|ξ 0| + |ξ 1|) ^ 2 * Real.sqrt (3 ^ n) *
            (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) +
          9 / 4 * ((|ξ 0| + |ξ 1|) ^ 2 * U.volume / Real.sqrt (3 ^ n))) →
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (g ω) else 0) ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 * U.volume / Real.sqrt (3 ^ n)) := by
  obtain ⟨C₂, hC₂, h2⟩ := exists_lintegral_tsum_ninefold_le hpc 2
  obtain ⟨C₆, hC₆, h6⟩ := exists_lintegral_tsum_ninefold_le hpc 6
  refine ⟨3 * C₆ + 9 * (121 * C₂) + 3, by finiteness, fun U n hn ξ g hg => ?_⟩
  have h2' : ∀ a, ∫⁻ ω, reachSum ω 2 a ∂(latticeBondLaw 2 p) ≤ C₂ := h2
  have h6' : ∀ a, ∫⁻ ω, reachSum ω 6 a ∂(latticeBondLaw 2 p) ≤ C₆ := h6
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 3 ^ n := Real.sq_sqrt (by positivity)
  have hvol := U.volume_pos
  have hP0 : 0 ≤ P₁ := by positivity
  set A := ENNReal.ofReal (9 / 4 * P₁ ^ 2 * s) with hA
  set a := ENNReal.ofReal (P₁ ^ 2 * U.volume / s) with ha
  have hpoint : ∀ ω : Configuration 2, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (g ω) else 0) ≤
      A * exceptionalCountBound ω U n + ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) := by
    intro ω
    split_ifs with h
    · have hG0 : 0 ≤ ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x :=
        Finset.sum_nonneg fun x _ => exceptionalIndicator_nonneg n x
      have hb : g ω ≤
          9 / 4 * P₁ ^ 2 * s * (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) +
            9 / 4 * (P₁ ^ 2 * U.volume / s) := hg ω h.1 h.2
      refine (ENNReal.ofReal_le_ofReal hb).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
      exact add_le_add (mul_le_mul_of_nonneg_left (ofReal_sum_exceptionalIndicator_le h.1 hn)
        zero_le) le_rfl
    · exact zero_le
  have hX := lintegral_exceptionalCountBound_le h2' h6' U (n := n)
  have hcardU : (U.toIntegerCube.vertices.card : ℝ≥0∞) = ENNReal.ofReal U.volume :=
    card_toIntegerCube_vertices U
  have hsub : ((subcubesAt U n).card : ℝ) * (9 : ℝ) ^ n = U.volume := card_subcubesAt_mul hn
  have k1 : A * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))))) ≤ 3 * a := by
    rw [hcardU, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hA,
      ← ENNReal.ofReal_mul (by positivity), ha, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (3 : ℝ) * (P₁ ^ 2 * U.volume / s) = 3 * P₁ ^ 2 * U.volume / s by ring,
      le_div_iff₀ hspos]
    have h27 : (3 : ℝ) ^ n * 9 ^ n ≤ 3 ^ (6 * (n + 1)) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hr : s ^ 2 * 9 ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1))) ≤ 1 := by
      rw [hs2, mul_one_div, div_le_one (by positivity)]
      exact h27
    have e : 9 / 4 * P₁ ^ 2 * s * (U.volume * ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1))))) * s =
        9 / 4 * (P₁ ^ 2 * U.volume) * (s ^ 2 * 9 ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)))) := by ring
    rw [e]
    have hc0 : (0 : ℝ) ≤ 9 / 4 * (P₁ ^ 2 * U.volume) := by positivity
    have := mul_le_mul_of_nonneg_left hr hc0
    nlinarith
  have k2 : A * (((subcubesAt U n).card : ℝ≥0∞) * ENNReal.ofReal (4 * (3 : ℝ) ^ n)) ≤ 9 * a := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hA,
      ← ENNReal.ofReal_mul (by positivity), ha, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (9 : ℝ) * (P₁ ^ 2 * U.volume / s) = 9 * P₁ ^ 2 * U.volume / s by ring,
      le_div_iff₀ hspos]
    have h9 : (9 : ℝ) ^ n = 3 ^ n * 3 ^ n := by rw [← mul_pow]; norm_num
    have e : 9 / 4 * P₁ ^ 2 * s * (((subcubesAt U n).card : ℝ) * (4 * (3 : ℝ) ^ n)) * s =
        9 * P₁ ^ 2 * (((subcubesAt U n).card : ℝ) * (9 : ℝ) ^ n) := by
      calc 9 / 4 * P₁ ^ 2 * s * (((subcubesAt U n).card : ℝ) * (4 * (3 : ℝ) ^ n)) * s
          = 9 * P₁ ^ 2 * ((subcubesAt U n).card : ℝ) * 3 ^ n * s ^ 2 := by ring
        _ = 9 * P₁ ^ 2 * ((subcubesAt U n).card : ℝ) * 3 ^ n * 3 ^ n := by rw [hs2]
        _ = _ := by rw [h9]; ring
    exact (e.trans (by rw [hsub])).le
  have k3 : ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) ≤ 3 * a := by
    rw [ha, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ P₁ ^ 2 * U.volume / s := by positivity
    linarith
  refine (lintegral_mono hpoint).trans ?_
  calc ∫⁻ ω, (A * exceptionalCountBound ω U n +
        ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s))) ∂(latticeBondLaw 2 p)
      = A * ∫⁻ ω, exceptionalCountBound ω U n ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul A (measurable_exceptionalCountBound U n), lintegral_const,
          measure_univ, mul_one]
    _ ≤ A * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
          (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * C₆)) +
        ((subcubesAt U n).card : ℝ≥0∞) * (ENNReal.ofReal (4 * (3 : ℝ) ^ n) * (121 * C₂))) +
          ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) := by gcongr
    _ = (A * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1)))))) * C₆ +
        (A * (((subcubesAt U n).card : ℝ≥0∞) * ENNReal.ofReal (4 * (3 : ℝ) ^ n))) *
          (121 * C₂) + ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) := by ring
    _ ≤ (3 * a) * C₆ + (9 * a) * (121 * C₂) + 3 * a := by gcongr
    _ = _ := by ring

/-- **The energy of the differences in expectation for `ν`** (Armstrong and Dario, Lemma 5.4,
display (5.10), second term, in dimension two). For every cube `U`, `n ≤ U.scale` and every cube
`W` of scale `n`,
`E[D^ν_n(U, p)] + |U| E[ν(U, p)] ≤ |U| E[ν(W, p)] + C |p|₁² |U| (3 ^ (-n / 2) + exp (-c 3 ^ n))`,
the expectations being taken on the partition event and the resolution of the cube. -/
theorem exists_lintegral_planarNuDefect_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (U W : TriadicCube 2) (n : ℕ), n ≤ U.scale →
      W.scale = n → ∀ ξ : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNuDefect ω U n ξ) else 0) ∂(latticeBondLaw 2 p) +
        ENNReal.ofReal U.volume * ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ) else 0) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal U.volume * ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
          ENNReal.ofReal (planarNu ω W ξ) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 * U.volume *
          (1 / Real.sqrt (3 ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) := by
  obtain ⟨C₁, hC₁, hint⟩ := exists_lintegral_le_of_le_nuSubadditivityBound hpc
  obtain ⟨C₂, hC₂, c, hc, hstat⟩ := exists_lintegral_planarNu_le_of_scale_eq hpc
  refine ⟨C₁ + C₂, by finiteness, c, hc, fun U W n hn hW ξ => ?_⟩
  set Q := (|ξ 0| + |ξ 1|) ^ 2 with hQ
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  set e := Real.exp (-c * (3 : ℝ) ^ n) with he
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hvol := U.volume_pos
  have hQ0 : 0 ≤ Q := by positivity
  set G : Configuration 2 → ℝ := fun ω => planarNuDefect ω U n ξ + planarNu ω U ξ * U.volume -
    ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) with hG
  set H : Vertex 2 → Configuration 2 → ℝ≥0∞ := fun x ω =>
    if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube n x) then
      ENNReal.ofReal (planarNu ω (scaleCube n x) ξ) else 0 with hH
  have hpoint : ∀ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (planarNuDefect ω U n ξ) else 0) +
      ENNReal.ofReal U.volume * (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (planarNu ω U ξ) else 0) ≤
      ∑ x ∈ U.toIntegerCube.vertices, H x ω +
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (G ω) else 0) := by
    intro ω
    split_ifs with hω
    · have hD := planarNuDefect_nonneg (ω := ω) U n ξ
      have hνU := planarNu_nonneg (ω := ω) (U := U) ξ
      have hnn : ∀ x ∈ U.toIntegerCube.vertices,
          0 ≤ (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) := by
        intro x _
        split_ifs
        · exact planarNu_nonneg ξ
        · exact le_rfl
      have hsplit : planarNuDefect ω U n ξ + U.volume * planarNu ω U ξ = G ω +
          ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) := by
        rw [hG]
        ring
      calc ENNReal.ofReal (planarNuDefect ω U n ξ) +
            ENNReal.ofReal U.volume * ENNReal.ofReal (planarNu ω U ξ)
          = ENNReal.ofReal (planarNuDefect ω U n ξ + U.volume * planarNu ω U ξ) := by
            rw [ENNReal.ofReal_add hD (mul_nonneg hvol.le hνU), ENNReal.ofReal_mul hvol.le]
        _ = ENNReal.ofReal (G ω + ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0)) := by
            rw [hsplit]
        _ ≤ ENNReal.ofReal (G ω) + ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0)) :=
            ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (G ω) + ∑ x ∈ U.toIntegerCube.vertices, ENNReal.ofReal
            (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) := by
            rw [ENNReal.ofReal_sum_of_nonneg hnn]
        _ ≤ ENNReal.ofReal (G ω) + ∑ x ∈ U.toIntegerCube.vertices, H x ω := by
            gcongr with x hx
            simp only [hH]
            split_ifs with h1 h2 h2
            · exact le_rfl
            · exact absurd ⟨hω.1, h1⟩ h2
            · simp
            · simp
        _ = _ := add_comm _ _
    · simp
  have hHmeas : ∀ x ∈ U.toIntegerCube.vertices, Measurable (H x) := fun x _ =>
    measurable_planarNu_indicator (scaleCube n x) ξ
  have hHx : ∀ x ∈ U.toIntegerCube.vertices, ∫⁻ ω, H x ω ∂(latticeBondLaw 2 p) ≤
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
          ENNReal.ofReal (planarNu ω W ξ) else 0) ∂(latticeBondLaw 2 p) +
        C₂ * ENNReal.ofReal (Q * e) := by
    intro x _
    have h := hstat W (scaleCube n x) (by rw [hW, scale_scaleCube]) ξ
    rw [hW] at h
    exact h
  have hGint := hint U n hn ξ G fun ω hP hU => planarNuDefect_add_sub_le hP hU hn ξ
  have hcard : (U.toIntegerCube.vertices.card : ℝ≥0∞) = ENNReal.ofReal U.volume := by
    rw [volume_eq_card, ENNReal.ofReal_natCast]
  set I := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
      ENNReal.ofReal (planarNu ω W ξ) else 0) ∂(latticeBondLaw 2 p) with hI
  have hfin : ENNReal.ofReal (Q * U.volume * (1 / s + e)) =
      ENNReal.ofReal (Q * U.volume / s) + ENNReal.ofReal U.volume * ENNReal.ofReal (Q * e) := by
    rw [← ENNReal.ofReal_mul hvol.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNuDefect ω U n ξ) else 0) ∂(latticeBondLaw 2 p) +
        ENNReal.ofReal U.volume * ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ) else 0) ∂(latticeBondLaw 2 p)
      ≤ ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNuDefect ω U n ξ) else 0) +
        ENNReal.ofReal U.volume * (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ) else 0)) ∂(latticeBondLaw 2 p) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact le_lintegral_add _ _
    _ ≤ ∫⁻ ω, (∑ x ∈ U.toIntegerCube.vertices, H x ω +
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (G ω) else 0))
          ∂(latticeBondLaw 2 p) := lintegral_mono hpoint
    _ = ∑ x ∈ U.toIntegerCube.vertices, ∫⁻ ω, H x ω ∂(latticeBondLaw 2 p) +
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (G ω) else 0)
          ∂(latticeBondLaw 2 p) := by
        rw [lintegral_add_left (Finset.measurable_sum _ hHmeas), lintegral_finsetSum _ hHmeas]
    _ ≤ ∑ _x ∈ U.toIntegerCube.vertices, (I + C₂ * ENNReal.ofReal (Q * e)) +
        C₁ * ENNReal.ofReal (Q * U.volume / s) := add_le_add (Finset.sum_le_sum hHx) hGint
    _ = ENNReal.ofReal U.volume * I + (C₁ * ENNReal.ofReal (Q * U.volume / s) +
        C₂ * (ENNReal.ofReal U.volume * ENNReal.ofReal (Q * e))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
    _ ≤ ENNReal.ofReal U.volume * I + (C₁ + C₂) * ENNReal.ofReal (Q * U.volume * (1 / s + e)) := by
        rw [hfin, add_mul, mul_add, mul_add]
        gcongr
        · exact le_add_right le_rfl
        · exact le_add_left le_rfl

end Rigidity.Percolation

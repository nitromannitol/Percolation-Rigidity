import Rigidity.Proofs.Percolation.PlanarOmegaMajorants

/-!
# The boundary term and the exceptional events in the proof of Lemma 5.9

* `exists_boundaryMajorant`: the boundary error of the maximizer of `ν(V, p)` divided by `|V|` has a
  measurable majorant of expectation at most `C |p|₁ 3^{-n/2}`, `n` the scale of `V`.
* `lintegral_not_resolved_le`: the probability that a cube of scale `n` is not resolved (or the
  partition event fails) is at most `C 9^n 3^{-6(n+1)}`.
* `exists_badMajorant`: on the event that `□_n` is resolved and `□_{n+1}` is not, `ν(□_n, p) - μ(□_n, q)`
  has a measurable majorant of expectation at most `C (1 + |p|₁² + |q|₁⁴) 9^{-n}`, by the inequality
  `y ≤ λ + λ⁻¹ y²` with `λ = 9^n` and the moments of the reach.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **The boundary term of quadratic response with a measurable majorant.** -/
theorem exists_boundaryMajorant {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TriadicCube 2) (ξ : Fin 2 → ℝ), 0 < |ξ 0| + |ξ 1| →
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
        (∀ ω, PlanarPartitionEvent ω → PlanarResolved ω V →
          boundaryError ω V ξ (planarNuMaximizer ω V ξ) / V.volume ≤ M ω) ∧
        ∫⁻ ω, ENNReal.ofReal (M ω) ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (|ξ 0| + |ξ 1|) / Real.sqrt (V.toIntegerCube.size : ℝ)) := by
  obtain ⟨C4, hC4, h4⟩ := exists_lintegral_partSideP_pow_le hpc 3
  refine ⟨9 * (162001 * 4 * C4 + 1 / 2), by positivity, fun V ξ hξ => ?_⟩
  set L : ℝ := (V.toIntegerCube.size : ℝ) with hL
  have hL1 : 1 ≤ L := one_le_cast_size V
  have hL0 : 0 < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set a : ℝ := 9 * P₁ * 162001 / (L * Real.sqrt L) with ha
  set b : ℝ := 9 * P₁ * (1 / 2 / Real.sqrt L) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  refine ⟨fun ω => a * ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ (3 + 1) + b,
    (Finset.measurable_fun_sum _ fun k _ => (measurable_partSideP k.2.2).pow_const _).const_mul
      _ |>.add measurable_const,
    fun ω => add_nonneg (mul_nonneg ha0 (Finset.sum_nonneg fun k _ =>
      pow_nonneg (partSideP_nonneg _ _) _)) hb0, fun ω hP hV => ?_, ?_⟩
  · have h := boundaryError_div_le hP hV ξ hξ
    have hps : ∀ x, partSideP ω x = partSide ω x := fun x => by rw [partSideP, if_pos hP]
    simp only [hps]
    refine h.trans (le_of_eq ?_)
    rw [ha, hb, ← hL]
    field_simp
    ring
  · have hm : ∀ k : Fin 2 × Bool × Vertex 2,
        Measurable fun ω => ENNReal.ofReal (partSideP ω k.2.2 ^ (3 + 1)) := fun k =>
      ((measurable_partSideP k.2.2).pow_const _).ennreal_ofReal
    have hpt : ∀ ω, ENNReal.ofReal (a * ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ (3 + 1) + b) =
        ENNReal.ofReal a * ∑ k ∈ boundaryIndex V, ENNReal.ofReal (partSideP ω k.2.2 ^ (3 + 1)) +
          ENNReal.ofReal b := fun ω => by
      rw [ENNReal.ofReal_add (mul_nonneg ha0 (Finset.sum_nonneg fun k _ =>
        pow_nonneg (partSideP_nonneg _ _) _)) hb0, ENNReal.ofReal_mul ha0,
        ENNReal.ofReal_sum_of_nonneg fun k _ => pow_nonneg (partSideP_nonneg _ _) _]
    simp_rw [hpt]
    have hms : Measurable fun ω => ENNReal.ofReal a *
        ∑ k ∈ boundaryIndex V, ENNReal.ofReal (partSideP ω k.2.2 ^ (3 + 1)) :=
      (Finset.measurable_fun_sum _ fun k _ => hm k).const_mul _
    rw [lintegral_add_left hms, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (Finset.measurable_fun_sum _ fun k _ => hm k),
      lintegral_finsetSum _ fun k _ => hm k]
    have hbI : ((boundaryIndex V).card : ℝ) ≤ 4 * L := card_boundaryIndex_le V
    calc ENNReal.ofReal a * ∑ k ∈ boundaryIndex V,
          ∫⁻ ω, ENNReal.ofReal (partSideP ω k.2.2 ^ (3 + 1)) ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal b
        ≤ ENNReal.ofReal a * ∑ _k ∈ boundaryIndex V, ENNReal.ofReal C4 + ENNReal.ofReal b := by
          gcongr with k hk
          exact h4 k.2.2
      _ = ENNReal.ofReal (a * ((boundaryIndex V).card * C4) + b) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul ha0,
            ← ENNReal.ofReal_add (by positivity) hb0]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have k1 : a * ((boundaryIndex V).card * C4) ≤ a * (4 * L * C4) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbI hC4) ha0
          have e1 : a * (4 * L * C4) = 9 * 162001 * 4 * C4 * P₁ / Real.sqrt L := by
            rw [ha]
            field_simp
          have e2 : b = 9 * (1 / 2) * P₁ / Real.sqrt L := by
            rw [hb]
            ring
          have e3 : 9 * (162001 * 4 * C4 + 1 / 2) * P₁ / Real.sqrt L =
              9 * 162001 * 4 * C4 * P₁ / Real.sqrt L + 9 * (1 / 2) * P₁ / Real.sqrt L := by ring
          rw [e3, ← e1, ← e2]
          linarith

/-- **The probability that a cube is not resolved.** -/
theorem exists_lintegral_not_resolved_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TriadicCube 2,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then 0 else 1) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * W.volume / (3 : ℝ) ^ (6 * (W.scale + 1))) := by
  obtain ⟨C6, hC6, h6⟩ := exists_lintegral_partSideP_pow_le hpc 5
  refine ⟨C6, hC6, fun W => ?_⟩
  set t : ℝ := 1 / (3 : ℝ) ^ (6 * (W.scale + 1)) with ht
  have ht0 : 0 ≤ t := by positivity
  have hae : ∀ᵐ ω ∂(latticeBondLaw 2 p),
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then (0 : ℝ≥0∞) else 1) ≤
        ∑ z ∈ W.toIntegerCube.vertices, ENNReal.ofReal t *
          ENNReal.ofReal (partSideP ω z ^ (5 + 1)) := by
    filter_upwards [ae_planarPartitionEvent hpc] with ω hP
    split_ifs with h
    · exact zero_le
    · have hres : ¬ PlanarResolved ω W := fun hW => h ⟨hP, hW⟩
      have h1 := one_le_sum_of_not_resolved hres
      have hps : ∀ x, partSideP ω x = partSide ω x := fun x => by rw [partSideP, if_pos hP]
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal (∑ z ∈ W.toIntegerCube.vertices,
            (partSide ω z / 3 ^ (W.scale + 1)) ^ 6) := ENNReal.ofReal_le_ofReal h1
        _ = _ := by
            rw [ENNReal.ofReal_sum_of_nonneg fun z _ => by
              have := one_le_partSide (ω := ω) z; positivity]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [← ENNReal.ofReal_mul ht0, hps, ht, div_pow, ← pow_mul, mul_comm (W.scale + 1) 6]
            congr 1
            ring
  have hm : ∀ z, Measurable fun ω => ENNReal.ofReal (partSideP ω z ^ (5 + 1)) := fun z =>
    ((measurable_partSideP z).pow_const _).ennreal_ofReal
  refine (lintegral_mono_ae hae).trans ?_
  rw [lintegral_finsetSum _ fun z _ => (hm z).const_mul _]
  calc ∑ z ∈ W.toIntegerCube.vertices, ∫⁻ ω, ENNReal.ofReal t *
        ENNReal.ofReal (partSideP ω z ^ (5 + 1)) ∂(latticeBondLaw 2 p)
      ≤ ∑ _z ∈ W.toIntegerCube.vertices, ENNReal.ofReal t * ENNReal.ofReal C6 := by
        gcongr with z hz
        rw [lintegral_const_mul _ (hm z)]
        gcongr
        exact h6 z
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_mul ht0, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_toIntegerCube_vertices_eq]
        congr 1
        rw [ht]
        change (9 : ℝ) ^ W.scale * (1 / (3 : ℝ) ^ (6 * (W.scale + 1)) * C6) =
          C6 * (9 : ℝ) ^ W.scale / (3 : ℝ) ^ (6 * (W.scale + 1))
        ring

/-- The weight `Θ_W = ∑_{z ∈ W} (s_z / 3^{n+1})⁶`, at least one when `W` is not resolved. -/
noncomputable def unresolvedWeight (ω : Configuration 2) (W : TriadicCube 2) : ℝ :=
  ∑ z ∈ W.toIntegerCube.vertices, (partSideP ω z / 3 ^ (W.scale + 1)) ^ 6

theorem unresolvedWeight_nonneg (ω : Configuration 2) (W : TriadicCube 2) :
    0 ≤ unresolvedWeight ω W :=
  Finset.sum_nonneg fun z _ => by have := partSideP_nonneg ω z; positivity

theorem measurable_unresolvedWeight (W : TriadicCube 2) :
    Measurable fun ω => unresolvedWeight ω W :=
  Finset.measurable_fun_sum _ fun z _ => ((measurable_partSideP z).div_const _).pow_const 6

theorem one_le_unresolvedWeight (hP : PlanarPartitionEvent ω) {W : TriadicCube 2}
    (h : ¬ PlanarResolved ω W) : 1 ≤ unresolvedWeight ω W := by
  have h1 := one_le_sum_of_not_resolved h
  have hps : ∀ x, partSideP ω x = partSide ω x := fun x => by rw [partSideP, if_pos hP]
  unfold unresolvedWeight
  simp only [hps]
  exact h1

theorem exists_lintegral_unresolvedWeight_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TriadicCube 2,
      ∫⁻ ω, ENNReal.ofReal (unresolvedWeight ω W) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * W.volume / (3 : ℝ) ^ (6 * (W.scale + 1))) := by
  obtain ⟨C6, hC6, h6⟩ := exists_lintegral_partSideP_pow_le hpc 5
  refine ⟨C6, hC6, fun W => ?_⟩
  set t : ℝ := 1 / (3 : ℝ) ^ (6 * (W.scale + 1)) with ht
  have ht0 : 0 ≤ t := by positivity
  have hm : ∀ z, Measurable fun ω => ENNReal.ofReal (partSideP ω z ^ (5 + 1)) := fun z =>
    ((measurable_partSideP z).pow_const _).ennreal_ofReal
  have hpt : ∀ ω, ENNReal.ofReal (unresolvedWeight ω W) = ∑ z ∈ W.toIntegerCube.vertices,
      ENNReal.ofReal t * ENNReal.ofReal (partSideP ω z ^ (5 + 1)) := fun ω => by
    rw [unresolvedWeight, ENNReal.ofReal_sum_of_nonneg fun z _ => by
      have := partSideP_nonneg ω z; positivity]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← ENNReal.ofReal_mul ht0, ht, div_pow, ← pow_mul, mul_comm (W.scale + 1) 6]
    congr 1
    ring
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun z _ => (hm z).const_mul _]
  calc ∑ z ∈ W.toIntegerCube.vertices, ∫⁻ ω, ENNReal.ofReal t *
        ENNReal.ofReal (partSideP ω z ^ (5 + 1)) ∂(latticeBondLaw 2 p)
      ≤ ∑ _z ∈ W.toIntegerCube.vertices, ENNReal.ofReal t * ENNReal.ofReal C6 := by
        gcongr with z hz
        rw [lintegral_const_mul _ (hm z)]
        gcongr
        exact h6 z
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_mul ht0, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_toIntegerCube_vertices_eq]
        congr 1
        rw [ht]
        change (9 : ℝ) ^ W.scale * (1 / (3 : ℝ) ^ (6 * (W.scale + 1)) * C6) =
          C6 * (9 : ℝ) ^ W.scale / (3 : ℝ) ^ (6 * (W.scale + 1))
        ring

/-- `(-μ(V, q))²` by the eighth powers of the reach. -/
theorem ofReal_neg_planarMu_sq_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (q : Fin 2 → ℝ) :
    ENNReal.ofReal (-planarMu ω V q) ^ 2 ≤
      ENNReal.ofReal (162 * 234256 ^ 2 * (|q 0| + |q 1|) ^ 4 / V.volume) *
        ∑ a ∈ V.toIntegerCube.vertices, reachSum ω 8 a := by
  have h := ofReal_neg_planarMu_le hP hV q
  have hvol := V.volume_pos
  set N : ℝ := (V.toIntegerCube.vertices.card : ℝ) with hN
  have hNvol : N = V.volume := card_toIntegerCube_vertices_eq V
  set S4 := ∑ a ∈ V.toIntegerCube.vertices, planarReach ω a ^ 4
  have hS : (∑ a ∈ V.toIntegerCube.vertices, 234256 * planarReach ω a ^ 4) = 234256 * S4 := by
    rw [Finset.mul_sum]
  rw [hS] at h
  have hSS : S4 ^ 2 ≤ ENNReal.ofReal N * (2 * ∑ a ∈ V.toIntegerCube.vertices, reachSum ω 8 a) := by
    have h1 := ENNReal.sum_mul_sum_le V.toIntegerCube.vertices (fun a => planarReach ω a ^ 4)
      (fun a => planarReach ω a ^ 4)
    simp only [← pow_mul] at h1
    rw [sq, hN, ENNReal.ofReal_natCast]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    rw [two_mul]
    exact add_le_add (Finset.sum_le_sum fun a _ => planarReach_pow_le ω a 7)
      (Finset.sum_le_sum fun a _ => planarReach_pow_le ω a 7)
  calc ENNReal.ofReal (-planarMu ω V q) ^ 2
      ≤ (ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / V.volume) * (234256 * S4)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / V.volume) ^ 2 * 234256 ^ 2 * S4 ^ 2 := by ring
    _ ≤ ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / V.volume) ^ 2 * 234256 ^ 2 *
          (ENNReal.ofReal N * (2 * ∑ a ∈ V.toIntegerCube.vertices, reachSum ω 8 a)) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_ofNat 234256,
          ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 2,
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [hNvol]
        field_simp
        ring

/-- **The exceptional event `□_n` resolved, `□_{n+1}` not**, with a measurable majorant. -/
theorem exists_badMajorant {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ξ q : Fin 2 → ℝ),
      ∃ M : Configuration 2 → ℝ≥0∞, Measurable M ∧
        (∀ ω, PlanarPartitionEvent ω → PlanarResolved ω ⟨n, 0⟩ →
          ¬ PlanarResolved ω ⟨n + 1, 0⟩ →
          ENNReal.ofReal (planarNu ω ⟨n, 0⟩ ξ) + ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) ≤ M ω) ∧
        ∫⁻ ω, M ω ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (1 + (|ξ 0| + |ξ 1|) ^ 2 + (|q 0| + |q 1|) ^ 4) / (9 : ℝ) ^ n) := by
  obtain ⟨CW, hCW, hW⟩ := exists_lintegral_unresolvedWeight_le hpc
  obtain ⟨C8, hC8, h8⟩ := exists_lintegral_reachSum_le_ofReal hpc 8
  refine ⟨9 * CW * 4 + 162 * 234256 ^ 2 * C8, by positivity, fun n ξ q => ?_⟩
  set V : TriadicCube 2 := ⟨n, 0⟩ with hV
  set U : TriadicCube 2 := ⟨n + 1, 0⟩ with hU
  set A : ℝ := 9 / 4 * (|ξ 0| + |ξ 1|) ^ 2 + (9 : ℝ) ^ n with hA
  have hA0 : 0 ≤ A := by positivity
  set κ : ℝ := 162 * 234256 ^ 2 * (|q 0| + |q 1|) ^ 4 / V.volume with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by positivity) V.volume_pos.le
  clear_value A κ
  have h9 : (0 : ℝ) < (9 : ℝ) ^ n := by positivity
  refine ⟨fun ω => ENNReal.ofReal A * ENNReal.ofReal (unresolvedWeight ω U) +
      ENNReal.ofReal ((9 : ℝ) ^ n)⁻¹ * (ENNReal.ofReal κ *
        ∑ a ∈ V.toIntegerCube.vertices, reachSum ω 8 a),
    ((measurable_unresolvedWeight U).ennreal_ofReal.const_mul _).add
      (((Finset.measurable_fun_sum _ fun a _ => measurable_reachSum 8 a).const_mul _).const_mul _),
    fun ω hP hVr hUr => ?_, ?_⟩
  · have hΘ := one_le_unresolvedWeight hP hUr
    have hΘ' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (unresolvedWeight ω U) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hΘ
    have hν : ENNReal.ofReal (planarNu ω V ξ) ≤ ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) :=
      ENNReal.ofReal_le_ofReal (planarNu_le ξ)
    set l : ℝ≥0∞ := ENNReal.ofReal ((9 : ℝ) ^ n) with hl
    have hl0 : l ≠ 0 := by rw [hl]; exact (ENNReal.ofReal_pos.2 h9).ne'
    have hlt : l ≠ ∞ := ENNReal.ofReal_ne_top
    have hμ := ENNReal.le_add_inv_mul_sq (y := ENNReal.ofReal (-planarMu ω V q)) hl0 hlt
    have hμ2 := ofReal_neg_planarMu_sq_le hP hVr q
    rw [← hκ] at hμ2
    have hli : l⁻¹ = ENNReal.ofReal ((9 : ℝ) ^ n)⁻¹ := (ENNReal.ofReal_inv_of_pos h9).symm
    rw [hli] at hμ
    calc ENNReal.ofReal (planarNu ω V ξ) + ENNReal.ofReal (-planarMu ω V q)
        ≤ ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) + (l + ENNReal.ofReal ((9 : ℝ) ^ n)⁻¹ *
            (ENNReal.ofReal κ * ∑ a ∈ V.toIntegerCube.vertices, reachSum ω 8 a)) := by
          refine add_le_add hν (hμ.trans ?_)
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hμ2 zero_le)
      _ = ENNReal.ofReal A + ENNReal.ofReal ((9 : ℝ) ^ n)⁻¹ *
            (ENNReal.ofReal κ * ∑ a ∈ V.toIntegerCube.vertices, reachSum ω 8 a) := by
          rw [hA, ENNReal.ofReal_add (by positivity) h9.le, hl, add_assoc]
      _ ≤ _ := by
          refine add_le_add ?_ le_rfl
          calc ENNReal.ofReal A = ENNReal.ofReal A * 1 := (mul_one _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_left hΘ' zero_le
  · have hm8 : Measurable fun ω => ∑ a ∈ V.toIntegerCube.vertices, reachSum ω 8 a :=
      Finset.measurable_fun_sum _ fun a _ => measurable_reachSum 8 a
    have hmA : Measurable fun ω => ENNReal.ofReal A * ENNReal.ofReal (unresolvedWeight ω U) :=
      (measurable_unresolvedWeight U).ennreal_ofReal.const_mul _
    rw [lintegral_add_left hmA, lintegral_const_mul _ (measurable_unresolvedWeight U).ennreal_ofReal,
      lintegral_const_mul _ (hm8.const_mul _), lintegral_const_mul _ hm8]
    have i8 := lintegral_sum_reachSum_le h8 V.toIntegerCube.vertices
    have iW := hW U
    calc ENNReal.ofReal A * ∫⁻ ω, ENNReal.ofReal (unresolvedWeight ω U) ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal ((9 : ℝ) ^ n)⁻¹ * (ENNReal.ofReal κ *
            ∫⁻ ω, ∑ a ∈ V.toIntegerCube.vertices, reachSum ω 8 a ∂(latticeBondLaw 2 p))
        ≤ ENNReal.ofReal A * ENNReal.ofReal (CW * U.volume / (3 : ℝ) ^ (6 * (U.scale + 1))) +
          ENNReal.ofReal ((9 : ℝ) ^ n)⁻¹ * (ENNReal.ofReal κ *
            ENNReal.ofReal ((V.toIntegerCube.vertices.card : ℝ) * C8)) := by gcongr
      _ = ENNReal.ofReal (A * (CW * U.volume / (3 : ℝ) ^ (6 * (U.scale + 1))) +
            ((9 : ℝ) ^ n)⁻¹ * (κ * ((V.toIntegerCube.vertices.card : ℝ) * C8))) := by
          rw [ENNReal.ofReal_add (mul_nonneg hA0 (div_nonneg (mul_nonneg hCW U.volume_pos.le)
              (by positivity))) (mul_nonneg (inv_nonneg.2 h9.le) (mul_nonneg hκ0
              (mul_nonneg (Nat.cast_nonneg _) hC8))),
            ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul (inv_nonneg.2 h9.le),
            ENNReal.ofReal_mul hκ0]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [card_toIntegerCube_vertices_eq]
          have hUv : U.volume = 9 * (9 : ℝ) ^ n := by
            change (9 : ℝ) ^ (n + 1) = _
            ring
          have hVv : V.volume = (9 : ℝ) ^ n := rfl
          have hUs : U.scale = n + 1 := rfl
          rw [hUv, hUs, hA, hκ, hVv]
          have h3 : (3 : ℝ) ^ (6 * (n + 1 + 1)) = 3 ^ 12 * ((9 : ℝ) ^ n) ^ 3 := by
            rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
            congr 1
            ring
          rw [h3]
          have hq : 0 ≤ (|q 0| + |q 1|) ^ 4 := by positivity
          have hxi : 0 ≤ (|ξ 0| + |ξ 1|) ^ 2 := by positivity
          set X := (9 : ℝ) ^ n with hX
          have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
          have hX0 : 0 < X := by linarith
          set ξ2 := (|ξ 0| + |ξ 1|) ^ 2
          set q4 := (|q 0| + |q 1|) ^ 4
          have e : (9 / 4 * ξ2 + X) * (CW * (9 * X) / (3 ^ 12 * X ^ 3)) +
              X⁻¹ * (162 * 234256 ^ 2 * q4 / X * (X * C8)) =
              ((9 / 4 * ξ2 / X + 1) * (9 * CW / 3 ^ 12) + 162 * 234256 ^ 2 * q4 * C8) / X := by
            field_simp
          rw [e]
          refine div_le_div_of_nonneg_right ?_ hX0.le
          have hd : 9 / 4 * ξ2 / X ≤ 9 / 4 * ξ2 := div_le_self (by positivity) hX1
          have k1 : (9 / 4 * ξ2 / X + 1) * (9 * CW / 3 ^ 12) ≤ (9 / 4 * ξ2 + 1) * CW := by
            have hc : 9 * CW / 3 ^ 12 ≤ CW := by
              rw [div_le_iff₀ (by positivity)]
              nlinarith
            calc (9 / 4 * ξ2 / X + 1) * (9 * CW / 3 ^ 12) ≤ (9 / 4 * ξ2 + 1) * (9 * CW / 3 ^ 12) :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
              _ ≤ (9 / 4 * ξ2 + 1) * CW := mul_le_mul_of_nonneg_left hc (by positivity)
          nlinarith [mul_nonneg hCW hxi, mul_nonneg hC8 hq]

end Rigidity.Percolation

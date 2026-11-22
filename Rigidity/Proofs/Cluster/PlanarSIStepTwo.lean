import Rigidity.Proofs.Cluster.PlanarRhoLocal
import Rigidity.Proofs.Cluster.BoundedChernoff

/-!
# Step 2 of the proof of Lemma 5.11 of Armstrong and Dario in dimension two

The concentration step of the proof of Lemma 5.11: for the subcubes `z + □_n` of a large cube,
the average of the truncated local versions `ρ_loc(z + □_n) ∧ C₁` exceeds `t` with probability at
most `exp(-c 3^{d(m-n)} (t - C E[ρ_loc(□_n) ∧ C₁]))`, by the independence of the local versions and
the exponential moment bound, and `E[ρ_loc(□_n) ∧ C₁] ≤ C 3^{-nα}` by Lemma 5.10.

In dimension two the local versions `planarRhoStat` of neighbouring cubes are not independent (their
regions overlap), so the subcubes are grouped by their position `a` inside the triadic cube of scale
`n + 3` containing them: the cubes `⟨n, a + 27 b⟩`, `b` ranging over the indices of a cube of scale
`j`, have pairwise disjoint local regions. Each of the `729` groups is concentrated by the Chernoff
bound `measureReal_sum_ge_le_of_bounded`, and a union bound over the groups gives

`P[∑_a ∑_b ρ_stat(⟨n, a + 27 b⟩) ∧ C₁ > 729 · 9ʲ t]
  ≤ 729 exp(-9ʲ (t - (e - 1) C (1 + C₁) 3^{-nα}) / C₁)`

(`planar_SIupgrade_step2`). The family `⟨n, a + 27 b⟩` with `a` in the cube of scale `3` and `b` in
the cube of scale `j` at the origin is the family of the subcubes of scale `n` of the cube of scale
`n + 3 + j` at the origin; the statement is given for this indexing.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

/-- The cube of scale `n` at the origin: its stationary version of `ρ` is the local version. -/
theorem planarRhoStat_originCube (p : unitInterval) (V : TriadicCube 2) (ω : Configuration 2) :
    planarRhoStat p V.originCube ω = planarRhoLoc p V.originCube ω := by
  have hc : V.originCube.center = 0 := funext fun i => by
    simp [TriadicCube.center, TriadicCube.originCube]
  unfold planarRhoStat
  rw [hc, neg_zero, configurationTranslation_zero]
  rfl

/-- `exp(-c 3ⁿ) ≤ c⁻¹ 3^{-nα}` for `α ≤ 1`. -/
theorem exp_neg_mul_three_pow_le {c α : ℝ} (hc : 0 < c) (hα : α ≤ 1) (n : ℕ) :
    Real.exp (-c * (3 : ℝ) ^ n) ≤ c⁻¹ * (3 : ℝ) ^ (-(n : ℝ) * α) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h1 : Real.exp (-c * (3 : ℝ) ^ n) ≤ (c * (3 : ℝ) ^ n)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    refine inv_anti₀ (by positivity) ?_
    have := Real.add_one_le_exp (c * (3 : ℝ) ^ n)
    linarith
  have h2 : ((3 : ℝ) ^ n)⁻¹ ≤ (3 : ℝ) ^ (-(n : ℝ) * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc Real.exp (-c * (3 : ℝ) ^ n) ≤ (c * (3 : ℝ) ^ n)⁻¹ := h1
    _ = c⁻¹ * ((3 : ℝ) ^ n)⁻¹ := by rw [mul_inv]
    _ ≤ c⁻¹ * (3 : ℝ) ^ (-(n : ℝ) * α) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hc.le)

/-- **The expectation of the truncated local version** (dimension two, `p > p_c(2)`):
`E[ρ_stat(V) ∧ C₁] ≤ C (1 + C₁) 3^{-nα}` for every triadic cube `V` of scale `n`, from Lemma 5.10
and the localization of the planar partition. -/
theorem exists_integral_min_planarRhoStat_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ C ∧ ∀ (V : TriadicCube 2) {C₁ : ℝ}, 0 ≤ C₁ →
      ∫ ω, min (planarRhoStat p V ω) C₁ ∂(latticeBondLaw 2 p) ≤
        C * (1 + C₁) * (3 : ℝ) ^ (-(V.scale : ℝ) * α) := by
  obtain ⟨α, C, hα0, hα, hC, hM⟩ := planar_omegadecayrate hpc
  obtain ⟨Cg, hCg, c, hc, hloc⟩ := exists_planarNuLoc_localization hpc
  refine ⟨α, C + Cg.toReal * c⁻¹, hα0, hα, by positivity, fun V C₁ hC₁ => ?_⟩
  set n := V.scale with hn
  set t : ℝ := (3 : ℝ) ^ (-(n : ℝ) * α) with ht
  have ht0 : 0 ≤ t := by positivity
  have hg : Continuous fun y : ℝ => min y C₁ := continuous_id.min continuous_const
  -- reduction to the cube at the origin
  have hmap := map_planarRhoStat_shift p (V := V.originCube) (z := V.center)
    V.originCube_side_dvd_center
  rw [V.originCube_shift_center] at hmap
  have e1 : ∫ ω, min (planarRhoStat p V ω) C₁ ∂(latticeBondLaw 2 p) =
      ∫ y, min y C₁ ∂((latticeBondLaw 2 p).map (planarRhoStat p V)) :=
    (integral_map (measurable_planarRhoStat p V).aemeasurable hg.aestronglyMeasurable).symm
  have e2 : ∫ ω, min (planarRhoStat p V.originCube ω) C₁ ∂(latticeBondLaw 2 p) =
      ∫ y, min y C₁ ∂((latticeBondLaw 2 p).map (planarRhoStat p V.originCube)) :=
    (integral_map (measurable_planarRhoStat p _).aemeasurable hg.aestronglyMeasurable).symm
  rw [e1, hmap, ← e2]
  simp only [planarRhoStat_originCube]
  -- the bound at the origin
  obtain ⟨M, hMm, hMle, hMint⟩ := hM n
  set W : TriadicCube 2 := V.originCube with hW
  have hWn : W = ⟨n, 0⟩ := rfl
  have hnn : ∀ ω, 0 ≤ min (planarRhoLoc p W ω) C₁ := fun ω =>
    le_min (planarRhoLoc_nonneg p W ω) hC₁
  have hmin_m : Measurable fun ω => min (planarRhoLoc p W ω) C₁ :=
    (measurable_planarRhoLoc p W).min measurable_const
  have hpt : ∀ᵐ ω ∂(latticeBondLaw 2 p), ENNReal.ofReal (min (planarRhoLoc p W ω) C₁) ≤
      M ω + {ω | ¬ PlanarLocalGood ω W}.indicator (fun _ => ENNReal.ofReal C₁) ω := by
    filter_upwards [hMle] with ω hω
    by_cases hgood : PlanarLocalGood ω W
    · have : ENNReal.ofReal (min (planarRhoLoc p W ω) C₁) ≤ M ω := by
        refine (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans ?_
        rw [planarRhoLoc_eq_of_good p hgood, hWn]
        exact hω
      exact this.trans le_self_add
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ¬ PlanarLocalGood ω W} from hgood)]
      exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans le_add_self
  have hlint : ∫⁻ ω, ENNReal.ofReal (min (planarRhoLoc p W ω) C₁) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (C * t) + ENNReal.ofReal C₁ *
        (Cg * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n))) := by
    calc ∫⁻ ω, ENNReal.ofReal (min (planarRhoLoc p W ω) C₁) ∂(latticeBondLaw 2 p)
        ≤ ∫⁻ ω, (M ω + {ω | ¬ PlanarLocalGood ω W}.indicator (fun _ => ENNReal.ofReal C₁) ω)
            ∂(latticeBondLaw 2 p) := lintegral_mono_ae hpt
      _ = ∫⁻ ω, M ω ∂(latticeBondLaw 2 p) + ∫⁻ ω, {ω | ¬ PlanarLocalGood ω W}.indicator
            (fun _ => ENNReal.ofReal C₁) ω ∂(latticeBondLaw 2 p) := lintegral_add_left hMm _
      _ ≤ ENNReal.ofReal (C * t) + ENNReal.ofReal C₁ *
            latticeBondLaw 2 p {ω | ¬ PlanarLocalGood ω W} :=
          add_le_add (by rw [ht]; exact hMint) (lintegral_indicator_const_le _ _)
      _ ≤ _ := by
          gcongr
          exact (hloc W 0).1
  have hfin : ENNReal.ofReal (C * t) + ENNReal.ofReal C₁ *
      (Cg * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n))) ≠ ∞ := by finiteness
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmin_m.aestronglyMeasurable]
  refine (ENNReal.toReal_mono hfin hlint).trans ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hC ht0), ENNReal.toReal_ofReal hC₁,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hexp := exp_neg_mul_three_pow_le hc (hα.trans (by norm_num)) n
  rw [← ht] at hexp
  have hCg0 : 0 ≤ Cg.toReal := ENNReal.toReal_nonneg
  have a := mul_le_mul_of_nonneg_left hexp (mul_nonneg hC₁ hCg0)
  have b : C * t ≤ C * (1 + C₁) * t := by nlinarith [mul_nonneg (mul_nonneg hC hC₁) ht0]
  have d : C₁ * Cg.toReal * (c⁻¹ * t) ≤ Cg.toReal * c⁻¹ * (1 + C₁) * t := by
    have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    nlinarith [mul_nonneg (mul_nonneg hCg0 hci) ht0]
  nlinarith

/-- The cubes `⟨n, a + 27 b⟩` for distinct `b` have disjoint local regions. -/
theorem disjoint_planarLocalRegion_add_smul (n : ℕ) (a : Fin 2 → ℤ) {b b' : Fin 2 → ℤ}
    (hbb : b ≠ b') :
    Disjoint (⟨n, a + (27 : ℤ) • b⟩ : TriadicCube 2).planarLocalRegion
      (⟨n, a + (27 : ℤ) • b'⟩ : TriadicCube 2).planarLocalRegion := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hbb
  rw [Set.disjoint_left]
  intro y hy hy'
  have h1 := hy i
  have h2 := hy' i
  simp only [TriadicCube.center, TriadicCube.side, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at h1 h2
  set s : ℤ := (3 : ℤ) ^ n with hs
  have hs0 : 0 < s := by positivity
  have hd : 1 ≤ |b i - b' i| := Int.one_le_abs (sub_ne_zero.2 hi)
  have key : |s * (a i + 27 * b i) - s * (a i + 27 * b' i)| ≤ 14 * s := by
    calc |s * (a i + 27 * b i) - s * (a i + 27 * b' i)|
        = |(y i - s * (a i + 27 * b' i)) - (y i - s * (a i + 27 * b i))| := by ring_nf
      _ ≤ |y i - s * (a i + 27 * b' i)| + |y i - s * (a i + 27 * b i)| := abs_sub _ _
      _ ≤ 7 * s + 7 * s := add_le_add h2 h1
      _ = 14 * s := by ring
  have e : |s * (a i + 27 * b i) - s * (a i + 27 * b' i)| = 27 * s * |b i - b' i| := by
    rw [show s * (a i + 27 * b i) - s * (a i + 27 * b' i) = (27 * s) * (b i - b' i) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 27 * s)]
  rw [e] at key
  nlinarith

/-- **Step 2 of the proof of Lemma 5.11 of Armstrong and Dario** (dimension two, `p > p_c(2)`):
with `A` the indices of the cube of scale `3` and `B` those of the cube of scale `j` at the origin,
`P[∑_{a ∈ A} ∑_{b ∈ B} ρ_stat(⟨n, a + 27 b⟩) ∧ C₁ > |A| |B| t]
  ≤ |A| exp(-|B| (t - (e - 1) C (1 + C₁) 3^{-nα}) / C₁)`, with `|A| = 729` and `|B| = 9ʲ`. -/
theorem planar_SIupgrade_step2 {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ C ∧ ∀ (n j : ℕ) {C₁ : ℝ}, 0 < C₁ → ∀ t : ℝ,
      (latticeBondLaw 2 p).real {ω |
        ((⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ) *
          ((⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card * t) <
        ∑ a ∈ (⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
          ∑ b ∈ (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
            min (planarRhoStat p ⟨n, a + (27 : ℤ) • b⟩ ω) C₁} ≤
        ((⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ) *
          Real.exp (-(((⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ) *
            (t - (Real.exp 1 - 1) * (C * (1 + C₁) * (3 : ℝ) ^ (-(n : ℝ) * α)))) / C₁) := by
  obtain ⟨α, C, hα0, hα, hC, hE⟩ := exists_integral_min_planarRhoStat_le hpc
  refine ⟨α, C, hα0, hα, hC, fun n j C₁ hC₁ t => ?_⟩
  set A := (⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hA
  set B := (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hB
  set X : (Fin 2 → ℤ) → (Fin 2 → ℤ) → Configuration 2 → ℝ := fun a b ω =>
    min (planarRhoStat p ⟨n, a + (27 : ℤ) • b⟩ ω) C₁ with hX
  have hg : Measurable fun y : ℝ => min y C₁ := measurable_id.min measurable_const
  -- the Chernoff bound for each group
  have hgroup : ∀ a ∈ A, (latticeBondLaw 2 p).real {ω | (B.card : ℝ) * t ≤ ∑ b ∈ B, X a b ω} ≤
      Real.exp (-((B.card : ℝ) *
        (t - (Real.exp 1 - 1) * (C * (1 + C₁) * (3 : ℝ) ^ (-(n : ℝ) * α)))) / C₁) := by
    intro a _
    refine measureReal_sum_ge_le_of_bounded B (X a)
      (fun b => (measurable_planarRhoStat p _).min measurable_const) hC₁
      (fun b ω => le_min (planarRhoStat_nonneg p _ ω) hC₁.le) (fun b ω => min_le_right _ _)
      (fun b _ => hE ⟨n, a + (27 : ℤ) • b⟩ hC₁.le) (fun b hb T hT hbT => ?_) t
    exact indepFun_comp_planarRhoStat_sum p (fun b => (⟨n, a + (27 : ℤ) • b⟩ : TriadicCube 2)) hg
      (fun b _ b' _ hbb => disjoint_planarLocalRegion_add_smul n a hbb) hb hT hbT
  -- the union bound over the groups
  have hsub : {ω | (A.card : ℝ) * ((B.card : ℝ) * t) < ∑ a ∈ A, ∑ b ∈ B, X a b ω} ⊆
      ⋃ a ∈ A, {ω | (B.card : ℝ) * t ≤ ∑ b ∈ B, X a b ω} := by
    intro ω hω
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hne
    have : ∑ a ∈ A, ∑ b ∈ B, X a b ω ≤ ∑ _a ∈ A, (B.card : ℝ) * t :=
      Finset.sum_le_sum fun a ha => (hne a ha).le
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact absurd hω (not_lt.2 this)
  calc (latticeBondLaw 2 p).real
        {ω | (A.card : ℝ) * ((B.card : ℝ) * t) < ∑ a ∈ A, ∑ b ∈ B, X a b ω}
      ≤ (latticeBondLaw 2 p).real (⋃ a ∈ A, {ω | (B.card : ℝ) * t ≤ ∑ b ∈ B, X a b ω}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ a ∈ A, (latticeBondLaw 2 p).real {ω | (B.card : ℝ) * t ≤ ∑ b ∈ B, X a b ω} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ A, Real.exp (-((B.card : ℝ) *
          (t - (Real.exp 1 - 1) * (C * (1 + C₁) * (3 : ℝ) ^ (-(n : ℝ) * α)))) / C₁) :=
        Finset.sum_le_sum hgroup
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Rigidity.Proofs.Cluster

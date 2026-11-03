import LatticeProb.Prob.AkcogluKrengelAE.BoundedErgodic
import LatticeProb.Prob.Percolation.LatticeBondErgodicity
import Rigidity.Steps.S4.RationalMatrix

/-!
# The multiparameter ergodic theorem for the lattice translations of the bond law

Step `step:4.10-ergodic` (eq. (density-quadratics) of the corrected draft): for every
null-measurable event `A`, almost surely the proportion of sites `y` of the centred cube
`B_N = [-N, N]^d` with `τ_y ω ∈ A` tends to `P[A]` (`translateDensity`), and the bounded-function
version (`translateAverage`): for bounded measurable `h`, almost surely the averages of `h ∘ τ_y`
over `y ∈ B_N` tend to `∫ h`.

No literature input is used. The route:

* `exists_ae_tendsto_gridAvg_univ_with_integral` (Lattice-Probability) gives, for every
  measure-preserving additive `ℤ^d`-action `σ` and bounded measurable `h`, almost sure convergence
  of the averages over the anchored cubes `[0, n)^d` to a bounded measurable `G` with
  `∫ G = ∫ h`.
* The anchored-cube sums at `σ_{e_i} ω` and at `ω` differ by a boundary slab of `n^{d-1}` sites
  (`abs_sum_shift_sub_sum_le`), so `G ∘ σ_{e_i} = G` almost everywhere; if `σ_{e_i}` is ergodic,
  `G` is almost everywhere constant, equal to `∫ h` (`ae_tendsto_gridAvg_integral`).
* The centred cube `[-N, N]^d` is the disjoint union over `T ⊆ {1, …, d}` of the images of the
  boxes `∏_{i ∈ T} [0, N) × ∏_{i ∉ T} [0, N]` under `w ↦ c_T + ρ_T w`, where `ρ_T` reflects the
  coordinates in `T` and `c_T = -𝟙_T` (`sum_symmetricBox_eq`). Each piece is an anchored cube of
  the reflected action `z ↦ σ_{ρ_T z}` up to `(N+1)^d - N^d` sites, and the `2^d` pieces carry
  weight `(N / (2N+1))^d → 2^{-d}` each (`ae_tendsto_symmetricBox_average`).
* For the bond law every nonzero translation is ergodic (`ergodic_configurationTranslation`).
-/

namespace Rigidity.Proofs.Ergodic

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}

theorem natToSite_add (v w : Fin d → ℕ) : natToSite (v + w) = natToSite v + natToSite w := by
  funext i
  simp [natToSite]

theorem natToSite_single (i : Fin d) : natToSite (Pi.single i 1 : Fin d → ℕ) = Pi.single i 1 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [natToSite]
  · simp [natToSite, hk]

/-- `|∑_{s} F| ≤ |s| M` for `|F| ≤ M`. -/
theorem abs_sum_le_card_mul {α : Type*} (s : Finset α) (F : α → ℝ) {M : ℝ}
    (hF : ∀ v, |F v| ≤ M) : |∑ v ∈ s, F v| ≤ s.card * M :=
  calc |∑ v ∈ s, F v| ≤ ∑ v ∈ s, |F v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ s, M := Finset.sum_le_sum fun v _ => hF v
    _ = s.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Boundary-slab estimate: the sums of `F` over the anchored cube `[0, n)^d` and over its
translate by `e_i` differ by at most `2 M n^{d-1}`. -/
theorem abs_sum_shift_sub_sum_le (F : (Fin d → ℕ) → ℝ) {M : ℝ} (hF : ∀ v, |F v| ≤ M) (i : Fin d)
    (n : ℕ) :
    |∑ w ∈ gridSet d Finset.univ n, F (w + Pi.single i 1) -
        ∑ w ∈ gridSet d Finset.univ n, F w| ≤ 2 * M * (n : ℝ) ^ (d - 1) := by
  classical
  have hM : 0 ≤ M := (abs_nonneg _).trans (hF 0)
  set A := gridSet d Finset.univ n with hAdef
  set e : Fin d → ℕ := Pi.single i 1 with hedef
  set B := A.map ⟨fun w => w + e, add_left_injective e⟩ with hBdef
  have hB : ∑ w ∈ A, F (w + e) = ∑ v ∈ B, F v := by
    rw [Finset.sum_map]
    rfl
  have hmemA : ∀ w : Fin d → ℕ, w ∈ A ↔ ∀ j, w j < n := by
    intro w
    simp [hAdef, gridSet, Fintype.mem_piFinset]
  have hAB : (A \ B).card ≤ n ^ (d - 1) := by
    have hsub : A \ B ⊆ gridSet d (Finset.univ.erase i) n := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      obtain ⟨hwA, hwB⟩ := hw
      rw [hmemA] at hwA
      simp only [gridSet, Fintype.mem_piFinset, Finset.mem_erase, ne_eq, Finset.mem_univ,
        and_true]
      intro j
      by_cases hji : j = i
      · subst hji
        simp only [not_true_eq_false, if_false, Finset.mem_singleton]
        by_contra hne
        apply hwB
        refine Finset.mem_map.mpr ⟨w - e, (hmemA _).mpr fun k => ?_, ?_⟩
        · by_cases hk : k = j
          · subst hk
            simp only [hedef, Pi.sub_apply, Pi.single_eq_same]
            have := hwA k
            omega
          · simp only [hedef, Pi.sub_apply, Pi.single_eq_of_ne hk]
            have := hwA k
            omega
        · funext k
          simp only [Function.Embedding.coeFn_mk, Pi.add_apply, Pi.sub_apply, hedef]
          by_cases hk : k = j
          · subst hk
            simp only [Pi.single_eq_same]
            omega
          · simp [Pi.single_eq_of_ne hk]
      · simp [hji, Finset.mem_range, hwA j]
    calc (A \ B).card ≤ (gridSet d (Finset.univ.erase i) n).card := Finset.card_le_card hsub
      _ = n ^ (d - 1) := by
        rw [card_gridSet_eq_pow_card, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin]
  have hBA : (B \ A).card = (A \ B).card := by
    have h1 := Finset.card_sdiff_add_card_inter A B
    have h2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at h2
    have h3 : B.card = A.card := Finset.card_map _
    omega
  have hAB' : ((A \ B).card : ℝ) ≤ (n : ℝ) ^ (d - 1) := by exact_mod_cast hAB
  rw [hB, ← Finset.sum_sdiff_sub_sum_sdiff]
  calc |∑ v ∈ B \ A, F v - ∑ v ∈ A \ B, F v|
      ≤ |∑ v ∈ B \ A, F v| + |∑ v ∈ A \ B, F v| := abs_sub _ _
    _ ≤ (B \ A).card * M + (A \ B).card * M :=
        add_le_add (abs_sum_le_card_mul _ _ hF) (abs_sum_le_card_mul _ _ hF)
    _ ≤ (n : ℝ) ^ (d - 1) * M + (n : ℝ) ^ (d - 1) * M := by
        rw [hBA]
        gcongr
    _ = 2 * M * (n : ℝ) ^ (d - 1) := by ring

omit [MeasurableSpace Ω] in
/-- The anchored-cube averages at `σ_{e_i} ω` and at `ω` differ by at most `2M / n`. -/
theorem abs_gridAvg_shift_sub_le {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) {h : Ω → ℝ} {M : ℝ} (hb : ∀ x, |h x| ≤ M)
    (i : Fin d) {n : ℕ} (hn : 1 ≤ n) (ω : Ω) :
    |gridAvg σ h Finset.univ n (σ (Pi.single i 1) ω) - gridAvg σ h Finset.univ n ω| ≤
      2 * M / n := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
  have hshift : ∀ w : Fin d → ℕ, σ (natToSite w) (σ (Pi.single i 1) ω) =
      σ (natToSite (w + Pi.single i 1)) ω := by
    intro w
    rw [natToSite_add, hσadd, natToSite_single]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [gridAvg, Finset.card_univ, Fintype.card_fin, hshift]
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ d),
    div_le_div_iff₀ (by positivity) hn0]
  have := abs_sum_shift_sub_sum_le (fun w => h (σ (natToSite w) ω)) (fun v => hb _) i n
  calc _ ≤ 2 * M * (n : ℝ) ^ (d - 1) * n := mul_le_mul_of_nonneg_right this hn0.le
    _ = 2 * M * (n : ℝ) ^ d := by
        rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hd]

/-- Integrals are invariant under a measure-preserving map. -/
theorem integral_comp_of_measurePreserving {f : Ω → Ω} (hf : MeasurePreserving f μ μ)
    {h : Ω → ℝ} (hh : Measurable h) : ∫ x, h (f x) ∂μ = ∫ x, h x ∂μ := by
  rw [← integral_map hf.aemeasurable hh.aestronglyMeasurable, hf.map_eq]

/-- **Pointwise ergodic theorem along anchored cubes.** For a measure-preserving additive
`ℤ^d`-action `σ` such that `σ_{e_i}` is ergodic for some `i`, and bounded measurable `h`, almost
surely the averages of `h ∘ σ_z` over `z ∈ [0, n)^d` tend to `∫ h`. -/
theorem ae_tendsto_gridAvg_integral [IsProbabilityMeasure μ] {σ : Site d → Ω → Ω}
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    (i : Fin d) (hErg : Ergodic (σ (Pi.single i 1)) μ) {h : Ω → ℝ} (hh : Measurable h)
    {M : ℝ} (hb : ∀ x, |h x| ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h Finset.univ n ω) atTop (𝓝 (∫ ω, h ω ∂μ)) := by
  obtain ⟨G, hGm, -, hGint, hconv⟩ := exists_ae_tendsto_gridAvg_univ_with_integral hσ hσadd hh
    (le_max_right M 0) fun x => (hb x).trans (le_max_left M 0)
  have hconv' : ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h Finset.univ n (σ (Pi.single i 1) ω))
      atTop (𝓝 (G (σ (Pi.single i 1) ω))) :=
    (hσ _).quasiMeasurePreserving.ae hconv
  have hinv : G ∘ σ (Pi.single i 1) =ᵐ[μ] G := by
    filter_upwards [hconv, hconv'] with ω h1 h2
    have hdiff : Tendsto (fun n => gridAvg σ h Finset.univ n (σ (Pi.single i 1) ω) -
        gridAvg σ h Finset.univ n ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * M))
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [Real.norm_eq_abs]
      exact abs_gridAvg_shift_sub_le hσadd hb i hn ω
    have h3 : Tendsto (fun n => gridAvg σ h Finset.univ n (σ (Pi.single i 1) ω)) atTop
        (𝓝 (G ω)) := by
      simpa using hdiff.add h1
    exact tendsto_nhds_unique h2 h3
  obtain ⟨c, hc⟩ := hErg.ae_eq_const_of_ae_eq_comp_ae hGm.aestronglyMeasurable hinv
  have hcint : c = ∫ ω, h ω ∂μ := by
    rw [← hGint, integral_congr_ae hc]
    simp
  filter_upwards [hconv, hc] with ω h1 h2
  rw [← hcint]
  rwa [h2] at h1

/-! ### Centred cubes -/

/-- Reflection `ρ_T` of the coordinates in `T`. -/
def flipSite (T : Finset (Fin d)) (z : Site d) : Site d := fun i => if i ∈ T then -z i else z i

theorem flipSite_add (T : Finset (Fin d)) (z w : Site d) :
    flipSite T (z + w) = flipSite T z + flipSite T w := by
  funext i
  by_cases hi : i ∈ T <;> simp [flipSite, hi, add_comm]

theorem flipSite_single_ne_zero (T : Finset (Fin d)) (i : Fin d) :
    flipSite T (Pi.single i 1) ≠ 0 := by
  intro h
  have := congrFun h i
  by_cases hi : i ∈ T <;> simp [flipSite, hi] at this

/-- The corner `c_T = -𝟙_T`. -/
def orthantCorner (T : Finset (Fin d)) : Site d := fun i => if i ∈ T then -1 else 0

/-- The site `c_T + ρ_T w` of the orthant piece indexed by `T`. -/
def orthantPoint (T : Finset (Fin d)) (w : Fin d → ℕ) : Site d :=
  fun i => if i ∈ T then -(w i : ℤ) - 1 else w i

theorem orthantPoint_eq (T : Finset (Fin d)) (w : Fin d → ℕ) :
    orthantPoint T w = orthantCorner T + flipSite T (natToSite w) := by
  funext i
  by_cases hi : i ∈ T
  · simp only [orthantPoint, orthantCorner, flipSite, natToSite, hi, if_true, Pi.add_apply]
    ring
  · simp [orthantPoint, orthantCorner, flipSite, natToSite, hi]

/-- The box `∏_{i ∈ T} [0, N) × ∏_{i ∉ T} [0, N]` of the orthant piece indexed by `T`. -/
def orthantBox (T : Finset (Fin d)) (N : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => if i ∈ T then Finset.range N else Finset.range (N + 1)

/-- `[-N, N]^d` is the disjoint union over `T` of the images of `orthantBox T N` under
`orthantPoint T`. -/
theorem sum_symmetricBox_eq (F : Site d → ℝ) (N : ℕ) :
    ∑ y ∈ Steps.S4.symmetricBox d N, F y =
      ∑ T : Finset (Fin d), ∑ w ∈ orthantBox T N, F (orthantPoint T w) := by
  classical
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_nbij' (fun x => orthantPoint x.1 x.2)
    (fun y => ⟨Finset.univ.filter fun i => y i < 0,
      fun i => if y i < 0 then (-y i - 1).toNat else (y i).toNat⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨T, w⟩ hx
    rw [Finset.mem_sigma] at hx
    have hx := Fintype.mem_piFinset.mp hx.2
    rw [Steps.S4.symmetricBox, Fintype.mem_piFinset]
    intro i
    have := hx i
    rw [Finset.mem_Icc]
    by_cases hi : i ∈ T
    · simp only [hi, if_true, Finset.mem_range] at this
      simp only [orthantPoint, hi, if_true]
      omega
    · simp only [hi, if_false, Finset.mem_range] at this
      simp only [orthantPoint, hi, if_false]
      omega
  · intro y hy
    rw [Steps.S4.symmetricBox, Fintype.mem_piFinset] at hy
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun i => ?_⟩
    have := Finset.mem_Icc.mp (hy i)
    by_cases hi : y i < 0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi, if_true, Finset.mem_range]
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi, if_false, Finset.mem_range]
      omega
  · rintro ⟨T, w⟩ _
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · ext i
      by_cases hi : i ∈ T
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, orthantPoint, hi, if_true,
          iff_true]
        omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, orthantPoint, hi, if_false,
          iff_false, not_lt]
        omega
    · funext i
      by_cases hi : i ∈ T
      · simp only [orthantPoint, hi, if_true]
        split_ifs <;> omega
      · simp only [orthantPoint, hi, if_false]
        split_ifs <;> omega
  · intro y _
    funext i
    by_cases hi : y i < 0
    · simp only [orthantPoint, Finset.mem_filter, Finset.mem_univ, true_and, hi, if_true]
      omega
    · simp only [orthantPoint, Finset.mem_filter, Finset.mem_univ, true_and, hi, if_false]
      omega
  · intro x _
    rfl

theorem card_symmetricBox (N : ℕ) :
    ((Steps.S4.symmetricBox d N).card : ℝ) = (2 * N + 1 : ℝ) ^ d := by
  have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  simp only [Steps.S4.symmetricBox, Fintype.card_piFinset, Int.card_Icc, this,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

theorem tendsto_div_two_mul_add_one :
    Tendsto (fun N : ℕ => (N : ℝ) / (2 * N + 1)) atTop (𝓝 (1 / 2)) := by
  have h : Tendsto (fun N : ℕ => (2 + 1 / (N : ℝ))⁻¹) atTop (𝓝 (2 + 0)⁻¹) :=
    (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).inv₀ (by norm_num)
  rw [add_zero, ← one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp

theorem tendsto_add_one_div_two_mul_add_one :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (2 * N + 1)) atTop (𝓝 (1 / 2)) := by
  have h0 : Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ) + 1)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by positivity) (fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    gcongr
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have := tendsto_div_two_mul_add_one.add h0
  rw [add_zero] at this
  refine this.congr fun N => ?_
  rw [← add_div]

theorem gridSet_univ_subset_orthantBox (T : Finset (Fin d)) (N : ℕ) :
    gridSet d Finset.univ N ⊆ orthantBox T N := by
  intro w hw
  simp only [gridSet, Finset.mem_univ, if_true, Fintype.mem_piFinset, Finset.mem_range] at hw
  simp only [orthantBox, Fintype.mem_piFinset]
  intro i
  have := hw i
  split_ifs <;> simp only [Finset.mem_range] <;> omega

theorem orthantBox_subset_gridSet_univ (T : Finset (Fin d)) (N : ℕ) :
    orthantBox T N ⊆ gridSet d Finset.univ (N + 1) := by
  intro w hw
  simp only [orthantBox, Fintype.mem_piFinset] at hw
  simp only [gridSet, Finset.mem_univ, if_true, Fintype.mem_piFinset, Finset.mem_range]
  intro i
  have := hw i
  split_ifs at this <;> simp only [Finset.mem_range] at this <;> omega

/-- **Pointwise ergodic theorem along centred cubes.** For a measure-preserving additive
`ℤ^d`-action `σ` all of whose nonzero elements are ergodic, and bounded measurable `h`, almost
surely the averages of `h ∘ σ_y` over `y ∈ [-N, N]^d` tend to `∫ h`. -/
theorem ae_tendsto_symmetricBox_average [NeZero d] [IsProbabilityMeasure μ]
    {σ : Site d → Ω → Ω} (hσ : ∀ z, MeasurePreserving (σ z) μ μ)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (hErg : ∀ z, z ≠ 0 → Ergodic (σ z) μ)
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hb : ∀ x, |h x| ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ y ∈ Steps.S4.symmetricBox d N, h (σ y ω)) /
      (Steps.S4.symmetricBox d N).card) atTop (𝓝 (∫ ω, h ω ∂μ)) := by
  classical
  set M' := max M 0
  have hM' : 0 ≤ M' := le_max_right M 0
  have hb' : ∀ x, |h x| ≤ M' := fun x => (hb x).trans (le_max_left M 0)
  have hpiece : ∀ T : Finset (Fin d), ∀ᵐ ω ∂μ, Tendsto (fun N => gridAvg
      (fun z => σ (flipSite T z)) (fun x => h (σ (orthantCorner T) x)) Finset.univ N ω) atTop
      (𝓝 (∫ ω, h ω ∂μ)) := by
    intro T
    have := ae_tendsto_gridAvg_integral (μ := μ) (σ := fun z => σ (flipSite T z))
      (h := fun x => h (σ (orthantCorner T) x)) (fun z => hσ _) (fun z w ω => by simp only [flipSite_add, hσadd]) 0
      (hErg _ (flipSite_single_ne_zero T 0)) (hh.comp (hσ (orthantCorner T)).measurable)
      (fun x => hb' _)
    rwa [integral_comp_of_measurePreserving (hσ _) hh] at this
  filter_upwards [ae_all_iff.mpr hpiece] with ω hω
  set a : Finset (Fin d) → ℕ → ℝ := fun T N => gridAvg (fun z => σ (flipSite T z))
    (fun x => h (σ (orthantCorner T) x)) Finset.univ N ω with ha
  set F : Site d → ℝ := fun y => h (σ y ω) with hF
  set E : Finset (Fin d) → ℕ → ℝ := fun T N =>
    ∑ w ∈ orthantBox T N \ gridSet d Finset.univ N, F (orthantPoint T w) with hEdef
  have hsplit : ∀ N, 1 ≤ N → (∑ y ∈ Steps.S4.symmetricBox d N, F y) /
      (Steps.S4.symmetricBox d N).card =
      ∑ T : Finset (Fin d), (((N : ℝ) / (2 * N + 1)) ^ d * a T N + E T N / (2 * N + 1) ^ d) := by
    intro N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [sum_symmetricBox_eq, card_symmetricBox, Finset.sum_div]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← Finset.sum_sdiff (gridSet_univ_subset_orthantBox T N)]
    have hgrid : ∑ w ∈ gridSet d Finset.univ N, F (orthantPoint T w) = (N : ℝ) ^ d * a T N := by
      simp only [ha, gridAvg, Finset.card_univ, Fintype.card_fin]
      field_simp
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [hF, orthantPoint_eq, hσadd]
    rw [hgrid, div_pow, add_div]
    field_simp
    ring
  have hE : ∀ T N, |E T N| ≤ M' * (((N : ℝ) + 1) ^ d - (N : ℝ) ^ d) := by
    intro T N
    have h1 := Finset.card_sdiff_add_card_eq_card (gridSet_univ_subset_orthantBox T N)
    have h2 := Finset.card_le_card (orthantBox_subset_gridSet_univ T N)
    rw [card_gridSet_eq_pow_card, Finset.card_univ, Fintype.card_fin] at h1 h2
    have h3 : (orthantBox T N \ gridSet d Finset.univ N).card + N ^ d ≤ (N + 1) ^ d := by
      omega
    have hcard : ((orthantBox T N \ gridSet d Finset.univ N).card : ℝ) ≤
        ((N : ℝ) + 1) ^ d - (N : ℝ) ^ d := by
      have : ((orthantBox T N \ gridSet d Finset.univ N).card : ℝ) + (N : ℝ) ^ d ≤
          ((N : ℝ) + 1) ^ d := by
        exact_mod_cast h3
      linarith
    calc |E T N| ≤ (orthantBox T N \ gridSet d Finset.univ N).card * M' :=
          abs_sum_le_card_mul _ _ fun v => hb' _
      _ ≤ M' * (((N : ℝ) + 1) ^ d - (N : ℝ) ^ d) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hcard hM'
  have herr : ∀ T, Tendsto (fun N : ℕ => E T N / (2 * N + 1) ^ d) atTop (𝓝 0) := by
    intro T
    have hlim := tendsto_const_nhds (x := M') |>.mul
      ((tendsto_add_one_div_two_mul_add_one.pow d).sub (tendsto_div_two_mul_add_one.pow d))
    rw [sub_self, mul_zero] at hlim
    refine squeeze_zero_norm (fun N => ?_) hlim
    have hpos : (0 : ℝ) < (2 * N + 1) ^ d := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_pow, div_pow, ← sub_div, ← mul_div_assoc,
      div_le_div_iff_of_pos_right hpos]
    exact hE T N
  have hlim : Tendsto (fun N : ℕ => ∑ T : Finset (Fin d),
      (((N : ℝ) / (2 * N + 1)) ^ d * a T N + E T N / (2 * N + 1) ^ d)) atTop
      (𝓝 (∑ _T : Finset (Fin d), ((1 / 2 : ℝ) ^ d * ∫ ω, h ω ∂μ + 0))) :=
    tendsto_finsetSum _ fun T _ =>
      ((tendsto_div_two_mul_add_one.pow d).mul (hω T)).add (herr T)
  have hval : ∑ _T : Finset (Fin d), ((1 / 2 : ℝ) ^ d * ∫ ω, h ω ∂μ + 0) = ∫ ω, h ω ∂μ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul,
      add_zero, ← mul_assoc]
    push_cast
    rw [← mul_pow]
    norm_num
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (hsplit N hN).symm

/-! ### The bond law -/

/-- **Ergodic theorem for the lattice translations of the bond law, bounded functions.** For a
bounded measurable `h`, almost surely the averages of `h ∘ τ_y` over the sites `y` of the centred
cube `B_N = [-N, N]^d` tend to `∫ h`. -/
theorem translateAverage {d : ℕ} [NeZero d] (p : unitInterval) {h : Configuration d → ℝ}
    (hh : Measurable h) {M : ℝ} (hb : ∀ ω, |h ω| ≤ M) :
    ∀ᵐ ω ∂latticeBondLaw d p, Tendsto (fun N : ℕ =>
      (∑ y ∈ Steps.S4.symmetricBox d N, h (configurationTranslation y ω)) /
        (Steps.S4.symmetricBox d N).card) atTop (𝓝 (∫ ω, h ω ∂latticeBondLaw d p)) :=
  ae_tendsto_symmetricBox_average (σ := fun z => configurationTranslation z)
    (fun z => measurePreserving_configurationTranslation p z)
    (fun z w ω => (configurationTranslation_add z w ω).symm)
    (fun _ hz => ergodic_configurationTranslation p hz) hh hb

/-- **Step `step:4.10-ergodic`** (eq. (density-quadratics)): for every null-measurable event `A`,
almost surely the proportion of sites `y ∈ B_N` with `τ_y ω ∈ A` tends to `P[A]`. -/
theorem translateDensity {d : ℕ} [NeZero d] (p : unitInterval) :
    Steps.S4.TranslateDensityStep d p := by
  intro A hA
  set μ := latticeBondLaw d p
  set A' := toMeasurable μ A
  have hA' : MeasurableSet A' := measurableSet_toMeasurable μ A
  have hAA' : ∀ᵐ x ∂μ, x ∈ A' ↔ x ∈ A := Filter.eventuallyEq_set.mp hA.toMeasurable_ae_eq
  have hmem : ∀ᵐ ω ∂μ, ∀ y : Vertex d,
      (configurationTranslation y ω ∈ A' ↔ configurationTranslation y ω ∈ A) :=
    ae_all_iff.mpr fun y =>
      (measurePreserving_configurationTranslation p y).quasiMeasurePreserving.ae hAA'
  have hconv := translateAverage p (h := A'.indicator 1) (measurable_one.indicator hA') (M := 1)
    fun ω => by
      by_cases hω : ω ∈ A' <;> simp [hω]
  have hint : ∫ ω, A'.indicator 1 ω ∂μ = (μ A).toReal := by
    rw [integral_indicator_one hA', measureReal_def, measure_toMeasurable]
  rw [hint] at hconv
  filter_upwards [hconv, hmem] with ω h1 h2
  refine h1.congr fun N => ?_
  unfold Steps.S4.boxDensity
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : configurationTranslation y ω ∈ A <;> simp [hy, h2 y]

end Rigidity.Proofs.Ergodic

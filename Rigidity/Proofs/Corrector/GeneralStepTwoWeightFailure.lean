import Rigidity.Proofs.Corrector.GeneralStepTwoDomination
import Rigidity.Proofs.Corrector.GeneralStepTwoBlocks
import Rigidity.Proofs.Corrector.GeneralStepTwoWeightScale

/-!
# The failure probability of the weight bound of a triadic cube of `ℤᵈ`

For the range `R`, the scale `m` with `2((3κ + 9)R + 1) + 1 ≤ 3^m` and the cube `⟨m + j, c⟩`, the
weight bound of the cube with constant `M = (e - 1) M₀ + 1` fails only if a vertex of the cube is
not good for the domination, or the finite-range weights exceed their bound on average. The first
event has probability at most `(3^d)^{m+j} C R^{2d} e^{-c R^σ}`, the second at most
`(3^d)^m exp(-(3^d)^j / (K₀ R^{10d+9})^q)` by the Chernoff bound over the residue classes modulo
`3^m` (`measure_not_weightGood_le_of_bounds`), with `K₀ R^{10d+9}`,
`K₀ = 3^d d ((7κ)^d 15d)^9`, bounding the finite-range weight (`finiteWeightBound_le`). With the
real bounds of `GeneralStepTwoWeightScale` at the range `R = 3^{⌊n/D⌋}`, `D = ⌈3 + (10d + 9)q⌉`,
the weight bound of a cube of scale `n` fails with probability at most `C₁ e^{-c (3ⁿ)^{s₀}}`
(`measure_not_weightGood_le_large`, and `exists_measure_not_weightGood_le_of_moments` for `d ≥ 3`,
given the moments of the finite-range weight).

This ports the planar file `DarioStepTwoWeightFailure` and the last two theorems of the planar file
`DarioStepTwoWeightScale`: the planar `9 = 3²` vertices per scale step become `3^d`, the power
`R⁴` of the domination becomes `R^{2d}`, and the bound `18 (49·29)^9 κ^18 R^{29}` of the
finite-range weight becomes `K₀ R^{10d+9}`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory ProbabilityTheory Filter LatticeProb.Percolation Rigidity.Percolation
  Rigidity.Proofs.Cluster Rigidity.External
open Rigidity.Poincare.GeneralDim (supBox)
open scoped Classical ENNReal

variable {d : ℕ}

/-- The bound of the finite-range weight is at most `K₀ R^{10d+9}`. -/
theorem finiteWeightBound_le {κ R : ℕ} (hd : 1 ≤ d) (hκ : 1 ≤ κ) (hR : 1 ≤ R) :
    (2 * (R : ℝ) + 1) ^ d * (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9) ≤
      (3 ^ d * (d * ((7 * κ) ^ d * (15 * d)) ^ 9) : ℝ) * (R : ℝ) ^ (10 * d + 9) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hκx : (1 : ℝ) ≤ κ * R := by nlinarith
  have hdx : (1 : ℝ) ≤ d * R := by nlinarith
  have h1 : 2 * (R : ℝ) + 1 ≤ 3 * R := by linarith
  have h2 : 6 * (κ : ℝ) * R + 1 ≤ 7 * κ * R := by nlinarith
  have h3 : 1 + 2 * (d : ℝ) * (6 * R + 1) ≤ 15 * d * R := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ d) (sub_nonneg.2 hx1)]
  calc (2 * (R : ℝ) + 1) ^ d * (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9)
      ≤ (3 * (R : ℝ)) ^ d * (d * ((7 * κ * R) ^ d * (15 * d * R)) ^ 9) := by gcongr
    _ = _ := by
        rw [mul_pow (3 : ℝ) (R : ℝ) d, mul_pow (7 * (κ : ℝ)) (R : ℝ) d]
        ring

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The failure probability of the weight bound of a cube at a given range.** -/
theorem measure_not_weightGood_le_of_bounds {p : unitInterval} {κ R m j : ℕ} (hd : 1 ≤ d)
    (hκ : 1 ≤ κ) (hR : 1 ≤ R) {i : Fin d} {q M₀ C c σ : ℝ} (hq : 1 ≤ q) (hM₀ : 0 ≤ M₀)
    (hC : 0 ≤ C)
    (hmom : ∀ u, ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal M₀)
    (hdom : ∀ u, latticeBondLaw d p {ω | ¬ DomGood hG hGv κ R i ω u} ≤
      ENNReal.ofReal (C * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ))))
    (hm : 2 * ((3 * κ + 9) * R + 1) + 1 ≤ 3 ^ m) (idx : Vertex d) :
    latticeBondLaw d p {ω | ¬ weightGood hG hGv κ i q ((Real.exp 1 - 1) * M₀ + 1) ω
        ⟨m + j, idx⟩} ≤
      ENNReal.ofReal (((3 : ℝ) ^ d) ^ (m + j) *
          (C * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ))) +
        ((3 : ℝ) ^ d) ^ m * Real.exp (-(((3 : ℝ) ^ d) ^ j * 1) /
          ((3 ^ d * (d * ((7 * κ) ^ d * (15 * d)) ^ 9) : ℝ) * (R : ℝ) ^ (10 * d + 9)) ^ q)) := by
  set V := (⟨m + j, idx⟩ : TriadicCube d).toIntegerCube.vertices with hV
  set X : Vertex d → Configuration d → ℝ := fun u ω => finiteWeight κ R ω u ^ q with hX
  set A : ℝ :=
    ((3 ^ d * (d * ((7 * κ) ^ d * (15 * d)) ^ 9) : ℝ) * (R : ℝ) ^ (10 * d + 9)) ^ q with hA
  have hq0 : 0 ≤ q := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hA0 : 0 < A := by positivity
  have hcardV : ((V.card : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ (m + j) :=
    card_toIntegerCube_vertices_eq_pow _
  have hsub : {ω | ¬ weightGood hG hGv κ i q ((Real.exp 1 - 1) * M₀ + 1) ω ⟨m + j, idx⟩} ⊆
      (⋃ u ∈ V, {ω | ¬ DomGood hG hGv κ R i ω u}) ∪
        {ω | ((V.card : ℕ) : ℝ) * ((Real.exp 1 - 1) * M₀ + 1) < ∑ u ∈ V, X u ω} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, not_or,
      not_exists, not_and, not_not, not_lt] at hc
    exact hω (weightGood_of_domGood hG hGv hR hq0 (fun u hu => hc.1 u hu)
      (by rw [mul_comm]; exact hc.2))
  have h1 : latticeBondLaw d p (⋃ u ∈ V, {ω | ¬ DomGood hG hGv κ R i ω u}) ≤
      ENNReal.ofReal (((3 : ℝ) ^ d) ^ (m + j) *
        (C * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ)))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun u _ => hdom u).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcardV]
  have h2 : latticeBondLaw d p
      {ω | ((V.card : ℕ) : ℝ) * ((Real.exp 1 - 1) * M₀ + 1) < ∑ u ∈ V, X u ω} ≤
      ENNReal.ofReal (((3 : ℝ) ^ d) ^ m * Real.exp (-(((3 : ℝ) ^ d) ^ j * 1) / A)) := by
    have hXm : ∀ u, Measurable (X u) := fun u => (measurable_finiteWeight κ R u).pow_const q
    have h0 : ∀ u ω, 0 ≤ X u ω := fun u ω => Real.rpow_nonneg (finiteWeight_nonneg hR ω u) q
    have hle : ∀ u ω, X u ω ≤ A := fun u ω =>
      Real.rpow_le_rpow (finiteWeight_nonneg hR ω u)
        ((finiteWeight_le hR ω u).trans (finiteWeightBound_le hd hκ hR)) hq0
    have hε : ∀ u, ∫ ω, X u ω ∂latticeBondLaw d p ≤ M₀ := by
      intro u
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (h0 u)) (hXm u).aestronglyMeasurable]
      refine ENNReal.toReal_le_of_le_ofReal hM₀ ((le_of_eq ?_).trans (hmom u))
      exact lintegral_congr fun ω =>
        (ENNReal.ofReal_rpow_of_nonneg (finiteWeight_nonneg hR ω u) hq0).symm
    have hloc : ∀ u (ω ω' : Configuration d),
        (∀ e ∈ localBonds (↑(supBox u ((3 * κ + 9) * R + 1)) : Set (Vertex d)), ω e = ω' e) →
          X u ω = X u ω' := fun u ω ω' h => by
      simp only [hX]
      rw [finiteWeight_eq_of_localBonds hR h]
    have hch := measureReal_sum_cube_gt_le p X hXm hloc hA0 h0 hle hε (j := j) hm idx
      ((Real.exp 1 - 1) * M₀ + 1)
    rw [show (Real.exp 1 - 1) * M₀ + 1 - (Real.exp 1 - 1) * M₀ = 1 by ring] at hch
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 hch
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add h1 h2).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The failure bound at the large scales. -/
theorem measure_not_weightGood_le_large {p : unitInterval} {κ : ℕ} (hd : 1 ≤ d) (hκ : 1 ≤ κ)
    {i : Fin d} {q M₀ C c σ Cf cf : ℝ} {D : ℕ} (hq : 1 ≤ q) (hM₀ : 0 ≤ M₀) (hC : 0 ≤ C)
    (hmom : ∀ R : ℕ, 1 ≤ R → ∀ u, ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q
      ∂latticeBondLaw d p ≤ ENNReal.ofReal M₀)
    (hdom : ∀ R : ℕ, 1 ≤ R → ∀ u, latticeBondLaw d p {ω | ¬ DomGood hG hGv κ R i ω u} ≤
      ENNReal.ofReal (C * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ))))
    (hreal : ∀ (n : ℕ) (R : ℝ), R = (3 : ℝ) ^ (n / D) → n / D + (6 * κ + 21) ≤ n →
      ((3 : ℝ) ^ d) ^ n * (C * R ^ (2 * d) * Real.exp (-(c * R ^ σ))) +
        ((3 : ℝ) ^ d) ^ (n / D + (6 * κ + 21)) *
          Real.exp (-(((3 : ℝ) ^ d) ^ (n - (n / D + (6 * κ + 21))) * 1) /
            ((3 ^ d * (d * ((7 * κ) ^ d * (15 * d)) ^ 9) : ℝ) * R ^ (10 * d + 9)) ^ q) ≤
      Cf * Real.exp (-cf * ((3 : ℝ) ^ n) ^ (σ / D)))
    {n : ℕ} (hle : n / D + (6 * κ + 21) ≤ n) (idx : Vertex d) :
    latticeBondLaw d p {ω | ¬ weightGood hG hGv κ i q ((Real.exp 1 - 1) * M₀ + 1) ω ⟨n, idx⟩} ≤
      ENNReal.ofReal (Cf * Real.exp (-cf * ((3 : ℝ) ^ n) ^ (σ / D))) := by
  have hR : 1 ≤ 3 ^ (n / D) := Nat.one_le_pow _ _ (by norm_num)
  have hA := measure_not_weightGood_le_of_bounds hG hGv (j := n - (n / D + (6 * κ + 21))) hd hκ
    hR hq hM₀ hC (fun u => hmom _ hR u) (fun u => hdom _ hR u)
    (Rigidity.Corrector.range_le_three_pow κ _) idx
  rw [Nat.add_sub_of_le hle] at hA
  refine hA.trans (ENNReal.ofReal_le_ofReal (hreal n _ ?_ hle))
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- **The failure bound for the weight bound of the triadic cubes**, given the moments of the
finite-range weight (`d ≥ 3`): for each `q ≥ 1` there is `M` such that a triadic cube `T` of side
`3ⁿ` fails `Σ_{u ∈ T} W(u)^q ≤ M |T|` for the weight `W` of the Step 2 sum, or has a vertex of
infinite weight, with probability at most `C₁ exp(−c (3ⁿ)^{s₀})`. -/
theorem exists_measure_not_weightGood_le_of_moments [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {κ : ℕ} (hκ : 1 ≤ κ) {q : ℝ} (hq : 1 ≤ q)
    (hmom : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ R : ℕ, 1 ≤ R → ∀ u : Vertex d,
      ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal M₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ C1 c s0 : ℝ, 0 ≤ C1 ∧ 0 < c ∧ 0 < s0 ∧ ∀ (i : Fin d) (T : TriadicCube d),
      latticeBondLaw d p {ω | ¬ weightGood hG hGv κ i q M ω T} ≤
        ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)) := by
  obtain ⟨M₀, hM₀, hmom⟩ := hmom
  obtain ⟨C, c, σ, hC, hc, hσ0, hσ1, hdom⟩ := measure_not_domGood_le hG hGv hd hpc hp1 hGae hκ
  have hd1 : 1 ≤ d := by omega
  have hq0 : 0 ≤ q := by linarith
  have hK₀ : (0 : ℝ) < 3 ^ d * (d * ((7 * κ) ^ d * (15 * d)) ^ 9) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    have : (0 : ℝ) < κ := by exact_mod_cast hκ
    positivity
  obtain ⟨Cf, cf, hCf, hcf, hreal⟩ := weight_failure_real_le (κ := κ) (a := 2 * d)
    (b := 10 * d + 9) hd1 hq0 hK₀ hC.le hc hσ0 hσ1
  set D : ℕ := ⌈3 + ((10 * d + 9 : ℕ) : ℝ) * q⌉₊
  have hD3 : 3 + ((10 * d + 9 : ℕ) : ℝ) * q ≤ (D : ℝ) := Nat.le_ceil _
  have hbq : (0 : ℝ) ≤ ((10 * d + 9 : ℕ) : ℝ) * q := mul_nonneg (Nat.cast_nonneg _) hq0
  have hD2 : 2 ≤ D := by
    have : (2 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  obtain ⟨s0, hs0e⟩ : ∃ s0 : ℝ, s0 = σ / D := ⟨_, rfl⟩
  have hs0 : 0 < s0 := by
    have : (0 : ℝ) < D := by linarith
    rw [hs0e]
    positivity
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, X₀ = ((3 : ℝ) ^ (2 * (6 * κ + 21))) ^ s0 := ⟨_, rfl⟩
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨(Real.exp 1 - 1) * M₀ + 1, by nlinarith [mul_nonneg (sub_nonneg.2 he1) hM₀],
    max Cf (Real.exp (cf * X₀)), cf, s0, le_max_of_le_left hCf, hcf, hs0, fun i T => ?_⟩
  obtain ⟨n, idx⟩ := T
  show _ ≤ ENNReal.ofReal (max Cf (Real.exp (cf * X₀)) * Real.exp (-cf * ((3 : ℝ) ^ n) ^ s0))
  by_cases hn : 2 * (6 * κ + 21) ≤ n
  · have hA := measure_not_weightGood_le_large hG hGv hd1 hκ (i := i) hq hM₀ hC.le hmom
      (fun R hR u => hdom i R hR u) hreal (Rigidity.Corrector.div_add_le_of_two_mul_le hD2 hn) idx
    rw [← hs0e] at hA
    refine hA.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · refine prob_le_one.trans (ENNReal.one_le_ofReal.2 ?_)
    have hle : ((3 : ℝ) ^ n) ^ s0 ≤ X₀ := by
      rw [hX₀]
      exact Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) hs0.le
    have hexp : Real.exp (-cf * X₀) ≤ Real.exp (-cf * ((3 : ℝ) ^ n) ^ s0) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hle hcf.le
      linarith
    calc (1 : ℝ) = Real.exp (cf * X₀) * Real.exp (-cf * X₀) := by
          rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
      _ ≤ _ := mul_le_mul (le_max_right _ _) hexp (Real.exp_pos _).le
          (le_max_of_le_left hCf)

end Grad

end Rigidity.Corrector.GeneralDim

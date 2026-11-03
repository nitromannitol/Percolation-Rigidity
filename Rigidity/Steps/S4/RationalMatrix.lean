import Mathlib.Dynamics.Ergodic.Conservative
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import Rigidity.Draft.Section4Statements
import Rigidity.Support.IntegerLinearGrowthResult

/-!
# Proposition 4.10 from its steps

Proposition 4.10 (paper L1463-1496 of the corrected draft): for a harmonic quadratic
`p̄(x) = xᵀ M x + bᵀ x + c`, almost surely the infinite cluster carries no nonconstant
integer-valued harmonic function `u` with `|u(x) - p̄(x)| / |x| → 0`.

* `M = 0`: such a `u` has linear growth, and Theorem 1.2 (`integer_valued_linear_growth`) makes it
  constant.
* `M ≠ 0`: the event `E = quadraticGrowthEvent d M b c` is null. Otherwise
  `step:4.10-ergodic` (`TranslateDensityStep`, eq. (density-quadratics)) gives a positive density of
  sites `y` with `τ_y ω ∈ E`, `step:4.10-two-copies` (`TwoCopiesStep`) two of them `y₁, y₂` with
  `M (y₁ - y₂) ≠ 0`, and `step:4.10-difference` (`TranslateDifferenceStep`) a nonconstant
  integer-valued harmonic function of linear growth on the cluster of `ω`, contradicting Theorem 1.2.

The ergodic theorem is applied to `E`, so `E` must be null-measurable; the paper leaves this
implicit. It is the separate step `QuadraticGrowthEventMeasurableStep`.

`rationalMatrix_of_recurrence` gives a second route for `M ≠ 0`: Poincaré recurrence for one
translation `τ_z` with `M z ≠ 0` (`Conservative.ae_mem_imp_frequently_image_mem`) produces the two
translates `0` and `n • z` directly, so `step:4.10-ergodic` and `step:4.10-two-copies` are not
needed.
-/

namespace Rigidity.Steps.S4

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Section4

/-- The cube `B_N = [-N, N]^d ∩ ℤ^d`. -/
noncomputable def symmetricBox (d : ℕ) (N : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- The proportion `|S ∩ B_N| / |B_N|` of sites of the cube `B_N` lying in `S`. -/
noncomputable def boxDensity {d : ℕ} (S : Set (Vertex d)) (N : ℕ) : ℝ :=
  (∑ y ∈ symmetricBox d N, S.indicator (fun _ => (1 : ℝ)) y) / (symmetricBox d N).card

/-- The event `E` of the proof of Proposition 4.10 for `p̄(x) = xᵀ M x + bᵀ x + c`: the infinite
cluster is unique and carries a nonconstant integer-valued harmonic function `u` with
`|u(x) - p̄(x)| / |x| → 0`. -/
def quadraticGrowthEvent (d : ℕ) [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (c : ℝ) : Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ u : uniqueInfiniteComponent h → ℝ,
    (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) ∧
    (∀ x, ∃ z : ℤ, u x = (z : ℝ)) ∧
    Tendsto (fun x : uniqueInfiniteComponent h =>
        |u x - quadratic M b c x.val| / (∑ i, |(x.val i : ℝ)|)) cofinite (𝓝 0) ∧
    ∃ x y, u x ≠ u y}

/-- Step `step:4.10-ergodic` (eq. (density-quadratics)), the multiparameter ergodic theorem for
the lattice translations of the bond law: for every null-measurable event `A`, almost surely the
proportion of sites `y ∈ B_N` with `τ_y ω ∈ A` tends to `P[A]`. -/
def TranslateDensityStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ A : Set (Configuration d), NullMeasurableSet A (latticeBondLaw d p) →
    ∀ᵐ ω ∂latticeBondLaw d p,
      Tendsto (fun N : ℕ => boxDensity {y | configurationTranslation y ω ∈ A} N) atTop
        (𝓝 (latticeBondLaw d p A).toReal)

/-- The event `E` of `step:4.10-ergodic` is null-measurable (implicit in the paper; `E` is the
projection of a Borel set, hence analytic, hence universally measurable). -/
def QuadraticGrowthEventMeasurableStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ (M : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (c : ℝ),
    NullMeasurableSet (quadraticGrowthEvent d M b c) (latticeBondLaw d p)

/-- Step `step:4.10-two-copies`: a set of sites of positive lower density in the cubes `B_N` is
not contained in a translate of `ker M` when `M ≠ 0`, so it contains `y₁, y₂` with
`M (y₁ - y₂) ≠ 0`. -/
def TwoCopiesStep (d : ℕ) : Prop :=
  ∀ M : Matrix (Fin d) (Fin d) ℝ, M ≠ 0 → ∀ S : Set (Vertex d),
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, δ ≤ boxDensity S N) →
    ∃ y₁ ∈ S, ∃ y₂ ∈ S, M.mulVec (fun i => ((y₁ i - y₂ i : ℤ) : ℝ)) ≠ 0

/-- Step `step:4.10-difference`: if `τ_{y₁} ω, τ_{y₂} ω ∈ E` carry `u₁, u₂`, then
`v(x) = u₁(x + y₁) - u₂(x + y₂)` is an integer-valued harmonic function on the cluster of `ω`
with `v(x) = 2 (M (y₁ - y₂))ᵀ x + O(1) + o(|x|)`, hence of linear growth, and nonconstant when
`M (y₁ - y₂) ≠ 0`. Nonconstancy uses that almost surely the cluster is not contained in a
sublinear neighbourhood of a hyperplane, which is why the step is stated almost surely. -/
def TranslateDifferenceStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ (M : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (c : ℝ), M.IsSymm →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ y₁ y₂ : Vertex d,
      M.mulVec (fun i => ((y₁ i - y₂ i : ℤ) : ℝ)) ≠ 0 →
      configurationTranslation y₁ ω ∈ quadraticGrowthEvent d M b c →
      configurationTranslation y₂ ω ∈ quadraticGrowthEvent d M b c →
      ∃ v : uniqueInfiniteComponent h → ℝ,
        (∀ x, componentLaplacian (uniqueInfiniteComponent h) v x = 0) ∧
        (∀ x, ∃ z : ℤ, v x = (z : ℝ)) ∧
        componentPointwiseLinearGrowth (uniqueInfiniteComponent h) v ∧ ∃ x y, v x ≠ v y

/-- The case `M = 0`: a function within `o(|x|)` of an affine function has linear growth. -/
theorem componentPointwiseLinearGrowth_of_tendsto_affine {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (u : C → ℝ) (b : Fin d → ℝ) (c : ℝ)
    (ht : Tendsto (fun x : C => |u x - quadratic 0 b c x.val| / (∑ i, |(x.val i : ℝ)|))
      cofinite (𝓝 0)) :
    componentPointwiseLinearGrowth C u := by
  set B : ℝ := ∑ j, |b j|
  have hfin : {x : C | x.val = 0}.Finite :=
    (Set.finite_singleton (0 : Vertex d)).preimage Subtype.val_injective.injOn
  have hone : ∀ᶠ x : C in cofinite, 1 ≤ ∑ i, |(x.val i : ℝ)| := by
    filter_upwards [hfin.compl_mem_cofinite] with x hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (show x.val ≠ 0 from hx)
    have h1 : (1 : ℝ) ≤ |(x.val i : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hi
    exact h1.trans (Finset.single_le_sum (fun j _ => abs_nonneg ((x.val j : ℤ) : ℝ))
      (Finset.mem_univ i))
  refine Asymptotics.IsBigO.of_bound (1 + B + |c|) ?_
  filter_upwards [hone, ht.eventually_lt_const zero_lt_one] with x hn hlt
  set n : ℝ := ∑ i, |(x.val i : ℝ)|
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hq : quadratic 0 b c x.val = (∑ i, b i * (x.val i : ℝ)) + c := by
    simp [quadratic]
  have hlin : |∑ i, b i * (x.val i : ℝ)| ≤ B * n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i)) (abs_nonneg _)
  have hdiff : |u x - quadratic 0 b c x.val| ≤ n := by
    have := (div_lt_one hn0).mp hlt
    exact this.le
  have hc : |c| ≤ |c| * n := le_mul_of_one_le_right (abs_nonneg c) hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn0]
  calc |u x| = |(u x - quadratic 0 b c x.val) + ((∑ i, b i * (x.val i : ℝ)) + c)| := by
        rw [← hq, sub_add_cancel]
    _ ≤ |u x - quadratic 0 b c x.val| + (|∑ i, b i * (x.val i : ℝ)| + |c|) :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ n + (B * n + |c| * n) := by gcongr
    _ = (1 + B + |c|) * n := by ring

/-- Off the `M = 0` case, the statement reduces to the nullity of `E`. -/
theorem rationalMatrix_of_null_event {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hnull : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (c : ℝ), M.IsSymm → M ≠ 0 →
      latticeBondLaw d p (quadraticGrowthEvent d M b c) = 0) :
    Section4.RationalMatrixStmt d p := by
  intro M b c hM _htr
  have h12 := Rigidity.Support.integer_valued_linear_growth d hd p hpc hp1 hclassical hcorrector
  by_cases hM0 : M = 0
  · subst hM0
    filter_upwards [h12] with ω ⟨h, hc⟩
    refine ⟨h, fun u hu hi ht x y => ?_⟩
    obtain ⟨a, ha⟩ := hc u hu hi
      (componentPointwiseLinearGrowth_of_tendsto_affine (uniqueInfiniteComponent h) u b c ht)
    rw [ha x, ha y]
  · filter_upwards [h12, measure_eq_zero_iff_ae_notMem.mp (hnull M b c hM hM0)] with ω h12ω hnE
    obtain ⟨h, -⟩ := h12ω
    refine ⟨h, fun u hu hi ht x y => ?_⟩
    by_contra hxy
    exact hnE ⟨h, u, hu, hi, ht, x, y, hxy⟩

/-- **Proposition 4.10** from Theorem 1.2 and the steps `step:4.10-ergodic` (with the
null-measurability of `E`), `step:4.10-two-copies` and `step:4.10-difference`. -/
theorem rationalMatrix_of_steps {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hergodic : TranslateDensityStep d p) (hmeas : QuadraticGrowthEventMeasurableStep d p)
    (htwo : TwoCopiesStep d) (hdiff : TranslateDifferenceStep d p) :
    Section4.RationalMatrixStmt d p := by
  refine rationalMatrix_of_null_event hd p hpc hp1 hclassical hcorrector fun M b c hM hM0 => ?_
  have h12 := Rigidity.Support.integer_valued_linear_growth d hd p hpc hp1 hclassical hcorrector
  set E := quadraticGrowthEvent d M b c
  by_contra hE
  have hpos : 0 < (latticeBondLaw d p E).toReal :=
    ENNReal.toReal_pos hE (measure_ne_top _ _)
  have hfalse : ∀ᵐ _ω ∂latticeBondLaw d p, False := by
    filter_upwards [hergodic E (hmeas M b c), hdiff M b c hM, h12] with ω hω hdω h12ω
    obtain ⟨h, hc⟩ := h12ω
    have hdens : ∀ᶠ N : ℕ in atTop,
        (latticeBondLaw d p E).toReal / 2 ≤ boxDensity {y | configurationTranslation y ω ∈ E} N :=
      hω.eventually_const_le (half_lt_self hpos)
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := htwo M hM0 _ ⟨_, half_pos hpos, hdens⟩
    obtain ⟨v, hv, hvi, hvl, x, y, hxy⟩ := hdω h y₁ y₂ hne hy₁ hy₂
    obtain ⟨a, ha⟩ := hc v hv hvi hvl
    exact hxy (by rw [ha x, ha y])
  exact IsProbabilityMeasure.ne_zero (latticeBondLaw d p)
    (ae_eq_bot.mp (eventually_false_iff_eq_bot.mp hfalse))

/-- Iterating a configuration translation translates by the natural multiple. -/
theorem configurationTranslation_iterate {d : ℕ} (z : Vertex d) (n : ℕ) (ω : Configuration d) :
    (configurationTranslation z : Configuration d → Configuration d)^[n] ω =
      configurationTranslation (n • z) ω := by
  induction n with
  | zero => rw [Function.iterate_zero, id, zero_smul, configurationTranslation_zero]
  | succ n ih => rw [Function.iterate_succ_apply', ih, configurationTranslation_add, succ_nsmul']

/-- **Proposition 4.10 by Poincaré recurrence.** For `M ≠ 0` pick a coordinate vector `z` with
`M z ≠ 0`; Poincaré recurrence for the measure-preserving translation `τ_z` returns almost every
`ω ∈ E` to `E` at some time `n ≥ 1`, and `step:4.10-difference` with the translates `n • z` and `0`
contradicts Theorem 1.2. This replaces `step:4.10-ergodic` and `step:4.10-two-copies`. -/
theorem rationalMatrix_of_recurrence {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hmeas : QuadraticGrowthEventMeasurableStep d p) (hdiff : TranslateDifferenceStep d p) :
    Section4.RationalMatrixStmt d p := by
  classical
  refine rationalMatrix_of_null_event hd p hpc hp1 hclassical hcorrector fun M b c hM hM0 => ?_
  have h12 := Rigidity.Support.integer_valued_linear_growth d hd p hpc hp1 hclassical hcorrector
  obtain ⟨j, hj⟩ : ∃ j, M.mulVec (Pi.single j 1) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hM0
    ext i k
    simpa [Matrix.mulVec_single_one] using congrFun (hall k) i
  set z : Vertex d := Pi.single j 1
  set E := quadraticGrowthEvent d M b c
  have hcons := (measurePreserving_configurationTranslation p z).conservative
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hcons.ae_mem_imp_frequently_image_mem (hmeas M b c), hdiff M b c hM, h12]
    with ω hrec hdω h12ω hωE
  obtain ⟨h, hc⟩ := h12ω
  obtain ⟨n, hn1, hnE⟩ := (hrec hωE).forall_exists_of_atTop 1
  rw [configurationTranslation_iterate] at hnE
  have hne : M.mulVec (fun i => (((n • z) i - (0 : Vertex d) i : ℤ) : ℝ)) ≠ 0 := by
    have hzv : (fun i => (((n • z) i - (0 : Vertex d) i : ℤ) : ℝ)) =
        (n : ℝ) • (Pi.single j 1 : Fin d → ℝ) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [z]
      · simp [z, hij]
    rw [hzv, Matrix.mulVec_smul]
    exact smul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hj
  have h0E : configurationTranslation 0 ω ∈ E := by
    rwa [configurationTranslation_zero]
  obtain ⟨v, hv, hvi, hvl, x, y, hxy⟩ := hdω h (n • z) 0 hne hnE h0E
  obtain ⟨a, ha⟩ := hc v hv hvi hvl
  exact hxy (by rw [ha x, ha y])

end Rigidity.Steps.S4

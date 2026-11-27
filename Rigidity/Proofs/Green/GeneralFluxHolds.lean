import Rigidity.Proofs.Green.GeneralFluxBad
import Rigidity.Proofs.Green.DarioGuFluxWeakNormHolds

/-!
# Proposition 2.13 of Dario–Gu on `ℤ^d`

**Dario–Gu, Proposition 2.13** (Proposition B.1, Appendix B) on `ℤ^d`, `d ≥ 2`: for every
supercritical `p < 1`, with the diffusivity `σ̄² = 2 θ(p)^{-1} ā` of (B.5) (`ā` the mean of the
flux, `exists_fluxMeanD`), the centered flux satisfies
`‖[g̃_{e_k}]_i‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ C r^α` for `r ≥ M_flux,α(y)`, `M_flux,α(y) ≤ O_s(C)`
(`darioGuFluxWeakNormD_of_variance`), under the variance bound (3.4) of Gu's proof of his
Proposition 1.1 (`FluxVarianceBoundD`).

The proof is the one of `DarioGuFluxWeakNormHolds.lean` (Steps 1-3 of the source at the triadic
scales `r ∈ [3^n, 3^{n+1})`), with the exponents of `ℤ^d`: the bound of the flux of `ℤ^d` on a
box at the dyadic level `J = dn` (`exists_fluxWeakNormBoxD`), the bound of the density on the
triadic cubes of scale `n + 2` around `y` (`exists_densityWeakNormD`), the gradient terms
normalized by `D_n = 3^{dn/2}`, and the partition of the good cubes with cubes of side at most
`L_n = ⌊3^{βn}⌋`, `β = α'/(2d + 1)`, near `y`, combined by the coarsening of the test functions
(`weakNormLeD_of_scale_bounds`, with `m = 3^{n-d}`). A scale is bad when one of the normalized
weak norms exceeds `3^{βn}` or a partition cube near `y` has size more than `L_n`; the minimal
scale is the first scale after which every scale is good (`exists_minimalScale_of_summable`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Corrector Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.S2 Rigidity.Poincare.GeneralDim
open scoped ENNReal Classical

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ} {p : unitInterval}

/-! ### Regions -/

/-- The indices within `R` of `c` in the sup norm. -/
noncomputable def indexBoxD (c : Vertex d) (R : ℤ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc (c i - R) (c i + R)

/-- The triadic cubes of scale `K` whose indices are within `1` of that of `y`. -/
noncomputable def regionD (K : ℕ) (y : Vertex d) : Finset (Vertex d) :=
  (indexBoxD (cubeIndex K y) 1).biUnion (triadicCubeFinset d K)

theorem mem_regionD {K : ℕ} {y x : Vertex d} :
    x ∈ regionD K y ↔ ∀ i, |cubeIndex K x i - cubeIndex K y i| ≤ 1 := by
  simp only [regionD, Finset.mem_biUnion, mem_triadicCubeFinset_iff, indexBoxD,
    Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨j, hj, rfl⟩ i
    have := hj i
    constructor <;> linarith [this.1, this.2]
  · intro h
    refine ⟨cubeIndex K x, fun i => ?_, rfl⟩
    have := h i
    constructor <;> linarith [this.1, this.2]

theorem isCubeUnion_regionD (K : ℕ) (y : Vertex d) : IsCubeUnion K (regionD K y) :=
  isCubeUnion_biUnion _ _

theorem supBox_subset_regionD (K : ℕ) (y : Vertex d) :
    supBox y (3 ^ K) ⊆ regionD K y := by
  intro x hx
  rw [mem_supBox] at hx
  rw [mem_regionD]
  intro i
  have hQ := three_pow_eq_two_mul_half_add_one K
  have hP : (0 : ℤ) < 3 ^ K := by positivity
  have h1 := abs_sub_mul_cubeIndex_le K x i
  have h2 := abs_sub_mul_cubeIndex_le K y i
  have h3 := hx i
  push_cast at h3
  set a := cubeIndex K x i
  set b := cubeIndex K y i
  have e : |3 ^ K * a - 3 ^ K * b| = 3 ^ K * |a - b| := by
    rw [← mul_sub, abs_mul, abs_of_pos hP]
  have t1 : |3 ^ K * a - 3 ^ K * b| ≤ |x i - 3 ^ K * a| + |x i - y i| + |y i - 3 ^ K * b| := by
    have h4 := abs_sub_le (3 ^ K * a) (x i) (3 ^ K * b)
    have h5 := abs_sub_le (x i) (y i) (3 ^ K * b)
    rw [abs_sub_comm (3 ^ K * a) (x i)] at h4
    linarith
  have h6 : 3 ^ K * |a - b| < 3 ^ K * 2 := by
    rw [← e]
    linarith
  have h7 : |a - b| < 2 := lt_of_mul_lt_mul_left h6 hP.le
  linarith [Int.lt_iff_add_one_le.1 h7]

theorem regionD_subset_supBox (K : ℕ) (y : Vertex d) :
    regionD K y ⊆ supBox y (2 * 3 ^ K) := by
  intro x hx
  rw [mem_regionD] at hx
  rw [mem_supBox]
  intro i
  have hQ := three_pow_eq_two_mul_half_add_one K
  have hP : (0 : ℤ) < 3 ^ K := by positivity
  have h1 := abs_sub_mul_cubeIndex_le K x i
  have h2 := abs_sub_mul_cubeIndex_le K y i
  have h3 := hx i
  set a := cubeIndex K x i
  set b := cubeIndex K y i
  have e : |3 ^ K * a - 3 ^ K * b| = 3 ^ K * |a - b| := by
    rw [← mul_sub, abs_mul, abs_of_pos hP]
  have h4 : 3 ^ K * |a - b| ≤ 3 ^ K * 1 := mul_le_mul_of_nonneg_left h3 hP.le
  have t1 : |x i - y i| ≤ |x i - 3 ^ K * a| + |3 ^ K * a - 3 ^ K * b| + |y i - 3 ^ K * b| := by
    have h5 := abs_sub_le (x i) (3 ^ K * a) (y i)
    have h6 := abs_sub_le (3 ^ K * a) (3 ^ K * b) (y i)
    rw [abs_sub_comm (3 ^ K * b) (y i)] at h6
    linarith
  push_cast
  linarith

theorem card_le_of_subset_supBox {S : Finset (Vertex d)} {y : Vertex d} {R : ℕ}
    (h : S ⊆ supBox y R) : (S.card : ℝ) ≤ (2 * (R : ℝ) + 1) ^ d := by
  have h1 := Finset.card_le_card h
  rw [card_supBox] at h1
  exact_mod_cast h1

/-! ### Conversion of the bounds -/

theorem sqSum_rpow_half_eqD (S : Finset (Vertex d)) (w : Vertex d → ℝ) :
    sqSum S w ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (∑ x ∈ S, w x ^ 2)) := by
  unfold sqSum
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _),
    ofReal_rpow_half _ (Finset.sum_nonneg fun x _ => sq_nonneg _)]

theorem gradSqSum_rpow_half_eqD (T : Finset (Vertex d)) (w : Vertex d → ℝ) :
    gradSqSum T w ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (∑ j : Fin d, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2)) := by
  unfold gradSqSum
  have h0 : ∀ j : Fin d, 0 ≤ ∑ x ∈ T, (w (x + unit j) - w x) ^ 2 :=
    fun j => Finset.sum_nonneg fun x _ => sq_nonneg _
  simp only [← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h0 j),
    ofReal_rpow_half _ (Finset.sum_nonneg fun j _ => h0 j)]

/-! ### Numerics -/

/-- `D_n = 3^{dn/2}`, the normalization of the gradient terms at the scale `n`. -/
noncomputable def scaleNorm (d n : ℕ) : ℝ := Real.sqrt (((3 : ℝ) ^ n) ^ d)

theorem one_le_scaleNorm (d n : ℕ) : 1 ≤ scaleNorm d n := by
  unfold scaleNorm
  rw [Real.le_sqrt (by norm_num) (by positivity), one_pow]
  exact one_le_pow₀ (one_le_pow₀ (by norm_num))

theorem three_rpow_eq_sqrt (d K : ℕ) :
    (3 : ℝ) ^ ((d : ℝ) * K / 2) = Real.sqrt (((3 : ℝ) ^ K) ^ d) := by
  rw [Real.sqrt_eq_rpow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

theorem sqrt_mul_pow_le {a b : ℝ} (ha : 1 ≤ a) :
    Real.sqrt ((a * b) ^ d) ≤ a ^ d * Real.sqrt (b ^ d) := by
  rw [mul_pow, Real.sqrt_mul (by positivity)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : 1 ≤ a ^ d := one_le_pow₀ ha
  nlinarith

theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x :=
  (Real.sqrt_le_left (by linarith)).2 (by nlinarith)

/-- **The final bound at a good scale.** -/
theorem scale_bound_leD [NeZero d] {σ τ r α : ℝ} {n L : ℕ} (hσ : 0 ≤ σ) (hτ : 1 ≤ τ) (hL1 : 1 ≤ L)
    (hLτ : (L : ℝ) ≤ τ) (hdn : d ≤ n) (hτr : τ ^ (2 * d + 1) ≤ r ^ α) :
    max ((τ + σ * τ) * (1 + (L : ℝ)) ^ d)
        ((scaleNorm d n * τ + σ * (scaleNorm d n * τ)) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) *
          Real.sqrt ((L : ℝ) ^ d / (2 * ((3 ^ (n - d) : ℕ) : ℝ)) ^ d)) ≤
      3 * d * 9 ^ d * 3 ^ (d * d) * (1 + σ) * r ^ α := by
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hτ0 : 0 ≤ τ := by linarith
  have hσ1 : 0 ≤ 1 + σ := by linarith
  set K : ℝ := 3 * d * 9 ^ d * 3 ^ (d * d) with hK
  have hK1 : (2 : ℝ) ^ d ≤ K := by
    have h1 : (2 : ℝ) ^ d ≤ 9 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    have h2 : (1 : ℝ) ≤ 3 * d * 3 ^ (d * d) := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
      have : (1 : ℝ) ≤ 3 ^ (d * d) := one_le_pow₀ (by norm_num)
      nlinarith
    calc (2 : ℝ) ^ d ≤ 9 ^ d := h1
      _ ≤ 9 ^ d * (3 * d * 3 ^ (d * d)) := le_mul_of_one_le_right (by positivity) h2
      _ = K := by rw [hK]; ring
  have hτd : τ ^ (d + 1) ≤ τ ^ (2 * d + 1) := pow_le_pow_right₀ hτ (by omega)
  have hKr : K * (1 + σ) * τ ^ (2 * d + 1) ≤ K * (1 + σ) * r ^ α :=
    mul_le_mul_of_nonneg_left hτr (by positivity)
  refine max_le ?_ ?_
  · calc (τ + σ * τ) * (1 + (L : ℝ)) ^ d ≤ (τ + σ * τ) * (2 * τ) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d)
            (by positivity)
      _ = 2 ^ d * (1 + σ) * τ ^ (d + 1) := by ring
      _ ≤ K * (1 + σ) * τ ^ (2 * d + 1) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hK1 hσ1) hτd (by positivity)
            (by positivity)
      _ ≤ K * (1 + σ) * r ^ α := hKr
  · set m : ℝ := ((3 ^ (n - d) : ℕ) : ℝ) with hm
    have hm0 : 0 < m := by rw [hm]; positivity
    have h3n : (3 : ℝ) ^ n = 3 ^ d * m := by
      rw [hm]
      push_cast
      rw [← pow_add, Nat.add_sub_cancel' hdn]
    -- `D_n (L^d/(2m)^d)^{1/2} ≤ (3^d τ)^d`
    have hX : scaleNorm d n * Real.sqrt ((L : ℝ) ^ d / (2 * m) ^ d) ≤ (3 ^ d * τ) ^ d := by
      unfold scaleNorm
      rw [← Real.sqrt_mul (by positivity), ← div_pow, ← mul_pow]
      have hin : (3 : ℝ) ^ n * ((L : ℝ) / (2 * m)) ≤ 3 ^ d * τ := by
        rw [h3n]
        have : (3 : ℝ) ^ d * m * ((L : ℝ) / (2 * m)) = 3 ^ d * ((L : ℝ) / 2) := by
          field_simp
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
      have h1 : (1 : ℝ) ≤ (3 ^ d * τ) ^ d :=
        one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hτ)
      calc Real.sqrt (((3 : ℝ) ^ n * ((L : ℝ) / (2 * m))) ^ d)
          ≤ Real.sqrt ((3 ^ d * τ) ^ d) :=
            Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hin d)
        _ ≤ (3 ^ d * τ) ^ d := sqrt_le_self_of_one_le h1
    have hG : (3 + 6 * (L : ℝ)) ^ d ≤ (9 * τ) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have hD0 : 0 ≤ scaleNorm d n := (zero_le_one).trans (one_le_scaleNorm d n)
    calc (scaleNorm d n * τ + σ * (scaleNorm d n * τ)) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) *
          Real.sqrt ((L : ℝ) ^ d / (2 * m) ^ d)
        = (1 + σ) * τ * (3 * d * (3 + 6 * (L : ℝ)) ^ d) *
            (scaleNorm d n * Real.sqrt ((L : ℝ) ^ d / (2 * m) ^ d)) := by ring
      _ ≤ (1 + σ) * τ * (3 * d * (9 * τ) ^ d) * ((3 ^ d * τ) ^ d) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hG (by positivity)) (by positivity)) hX
            (by positivity) (by positivity)
      _ = K * (1 + σ) * τ ^ (2 * d + 1) := by
          rw [hK, mul_pow, mul_pow, ← pow_mul]
          ring
      _ ≤ K * (1 + σ) * r ^ α := hKr

/-- The moments of the sum of the variables of a scale. -/
theorem growthMomentsD_scaleSum [NeZero d] {Y Z : Fin d × Fin d → Configuration d → ℝ≥0∞}
    {Yd Zd : Configuration d → ℝ≥0∞} (hYm : ∀ q, Measurable (Y q))
    (hZm : ∀ q, Measurable (Z q)) (hYdm : Measurable Yd) {B κ : ℝ} (hB : 0 ≤ B)
    (hY : ∀ q, GrowthMomentsD p (Y q) B κ) (hZ : ∀ q, GrowthMomentsD p (Z q) B κ)
    (hYd : GrowthMomentsD p Yd B κ) (hZd : GrowthMomentsD p Zd B κ) :
    GrowthMomentsD p (fun ω => ∑ q : Fin d × Fin d, (Y q ω + Z q ω) + (Yd ω + Zd ω))
      (4 * d * d * B) κ := by
  have h1 : ∀ q ∈ (Finset.univ : Finset (Fin d × Fin d)),
      GrowthMomentsD p (fun ω => Y q ω + Z q ω) (2 * B) κ :=
    fun q _ => GrowthMomentsD.add (hYm q).aemeasurable (hY q) (hZ q) hB
  have h2 := GrowthMomentsD.finsetSum (Finset.univ : Finset (Fin d × Fin d))
    (fun q => (hYm q).add (hZm q)) (by positivity) h1
  have hcard : ((Finset.univ : Finset (Fin d × Fin d)).card : ℝ) = d * d := by
    rw [Finset.card_univ]
    simp
  rw [hcard] at h2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have h3 := (GrowthMomentsD.add hYdm.aemeasurable hYd hZd hB).of_le (by positivity)
    (le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hd1 hd1)) le_rfl
  have h4 := GrowthMomentsD.add
    (Finset.measurable_sum _ fun q _ => (hYm q).add (hZm q)).aemeasurable h2 h3 (by positivity)
  exact h4.of_le (by positivity) (by nlinarith) le_rfl

/-! ### The variables of a scale -/

/-- The triadic cubes of scale `n + 2` around the cube of `y`. -/
noncomputable def scaleSD (n : ℕ) (y : Vertex d) : Finset (Vertex d) := regionD (n + 2) y

/-- The box of the gradients at the scale `n`. -/
noncomputable def scaleTD (n : ℕ) (y : Vertex d) : Finset (Vertex d) :=
  supBox y (2 * 3 ^ (n + 2) + 1)

theorem isCubeUnion_scaleSD (n : ℕ) (y : Vertex d) : IsCubeUnion (n + 2) (scaleSD n y) :=
  isCubeUnion_regionD _ _

/-- The random variables of the weak norms of the flux of `ℤ^d` on finite sets. -/
abbrev BoxVarD (d : ℕ) : Type :=
  Fin d → Fin d → ℕ → Finset (Vertex d) → Finset (Vertex d) → Configuration d → ℝ≥0∞

/-- The random variables of the weak norms of the density on unions of triadic cubes. -/
abbrev CubeVarD (d : ℕ) : Type :=
  (K : ℕ) → (S : Finset (Vertex d)) → IsCubeUnion K S → Configuration d → ℝ≥0∞

/-- The sum of the normalized weak norm variables at the scale `n`. -/
noncomputable def scaleQD (Yf Zf : BoxVarD d) (Yd Zd : CubeVarD d) (n : ℕ) (y : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑ q : Fin d × Fin d, (Yf q.1 q.2 (d * n) (scaleSD n y) (scaleTD n y) ω +
      ENNReal.ofReal (1 / scaleNorm d n) * Zf q.1 q.2 (d * n) (scaleSD n y) (scaleTD n y) ω) +
    (Yd (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y) ω +
      ENNReal.ofReal (1 / scaleNorm d n) * Zd (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y) ω)

/-- `scaleQD / (n + 1)`. -/
noncomputable def scaleQnD (Yf Zf : BoxVarD d) (Yd Zd : CubeVarD d) (n : ℕ) (y : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (n + 1)) * scaleQD Yf Zf Yd Zd n y ω

/-- The bad event of the scale `n`. -/
noncomputable def scaleBadD (Yf Zf : BoxVarD d) (Yd Zd : CubeVarD d) (β : ℝ) (y : Vertex d)
    (n : ℕ) : Set (Configuration d) :=
  if n < 2 * d + 1 then Set.univ else
    ({ω | ∃ z ∈ supBox y (2 * 3 ^ (n + 2) + 2),
        ((⌊(3 : ℝ) ^ (β * n)⌋₊ : ℕ) : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} ∪
      {ω | scaleQnD Yf Zf Yd Zd n y ω = ⊤}) ∪
    {ω | (3 : ℝ) ^ (β * n) / (n + 1) < (scaleQnD Yf Zf Yd Zd n y ω).toReal}

section Moments

variable {Yf Zf : BoxVarD d} {Yd Zd : CubeVarD d}
  (hYfm : ∀ k i J S T, Measurable (Yf k i J S T)) (hZfm : ∀ k i J S T, Measurable (Zf k i J S T))
  (hYdm : ∀ K S h, Measurable (Yd K S h)) (hZdm : ∀ K S h, Measurable (Zd K S h))

include hYfm hZfm hYdm hZdm in
theorem measurable_scaleQnD (n : ℕ) (y : Vertex d) : Measurable (scaleQnD Yf Zf Yd Zd n y) :=
  ((Finset.measurable_sum _ fun _ _ => (hYfm _ _ _ _ _).add ((hZfm _ _ _ _ _).const_mul _)).add
    ((hYdm _ _ _).add ((hZdm _ _ _).const_mul _))).const_mul _

include hYfm hZfm hYdm hZdm in
theorem measurableSet_scaleBadD (β : ℝ) (y : Vertex d) (n : ℕ) :
    MeasurableSet (scaleBadD Yf Zf Yd Zd β y n) := by
  unfold scaleBadD
  split_ifs
  · exact MeasurableSet.univ
  · exact ((measurableSet_stoppingSize_lt _ _).union
      (measurableSet_eq_fun (measurable_scaleQnD hYfm hZfm hYdm hZdm n y) measurable_const)).union
      (measurableSet_lt measurable_const
        (measurable_scaleQnD hYfm hZfm hYdm hZdm n y).ennreal_toReal)

include hYfm hZfm hYdm in
theorem growthMoments_scaleQnD [NeZero d] {Af κf Ad κd : ℝ} (hAf : 0 < Af) (hAd : 0 < Ad)
    (hYfmom : ∀ k i J S T, GrowthMomentsD p (Yf k i J S T) (Af * Real.sqrt S.card / 2 ^ J) κf)
    (hZfmom : ∀ k i J S T,
      GrowthMomentsD p (Zf k i J S T) (Af * (J + 1) * Real.sqrt T.card) κf)
    (hYdmom : ∀ K S h, GrowthMomentsD p (Yd K S h)
      (Ad * Real.sqrt S.card / (3 : ℝ) ^ ((d : ℝ) * K / 2)) κd)
    (hZdmom : ∀ K S h, GrowthMomentsD p (Zd K S h) (Ad * (K + 1) * Real.sqrt S.card) κd)
    (n : ℕ) (y : Vertex d) :
    GrowthMomentsD p (scaleQnD Yf Zf Yd Zd n y)
      (4 * d * d * (3 * d * 39 ^ d * (Af + Ad))) (max κf κd) := by
  set c₀ := 3 * d * 39 ^ d * (Af + Ad) with hc₀
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hc₀0 : 0 < c₀ := by positivity
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hB : 0 ≤ c₀ * (n + 1) := by positivity
  have h3n : (3 : ℝ) ^ (n + 2) = 9 * 3 ^ n := by ring
  have h1n : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hD1 := one_le_scaleNorm d n
  have hD0 : 0 < scaleNorm d n := lt_of_lt_of_le one_pos hD1
  have h37 : (1 : ℝ) ≤ 37 := by norm_num
  -- the sizes of `S` and `T`
  have hScard : (scaleSD n y).card ≤ ((37 : ℝ) * 3 ^ n) ^ d := by
    refine (card_le_of_subset_supBox (regionD_subset_supBox _ _)).trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ d
    push_cast
    rw [h3n]
    linarith
  have hTcard : (scaleTD n y).card ≤ ((39 : ℝ) * 3 ^ n) ^ d := by
    refine (card_le_of_subset_supBox (subset_refl _)).trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ d
    push_cast
    rw [h3n]
    linarith
  have hSqrtS : Real.sqrt (scaleSD n y).card ≤ 37 ^ d * scaleNorm d n :=
    (Real.sqrt_le_sqrt hScard).trans (sqrt_mul_pow_le h37)
  have hSqrtT : Real.sqrt (scaleTD n y).card ≤ 39 ^ d * scaleNorm d n :=
    (Real.sqrt_le_sqrt hTcard).trans (sqrt_mul_pow_le (by norm_num))
  have h3739 : (37 : ℝ) ^ d ≤ 39 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have hX : (0 : ℝ) ≤ 39 ^ d := by positivity
  have hd0 : (0 : ℝ) ≤ d - 1 := by linarith
  have hc₁ : Af * 39 ^ d ≤ c₀ := by
    rw [hc₀]
    nlinarith [mul_nonneg (mul_nonneg hX hAf.le) hd0,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hX) hAd.le,
      mul_nonneg hX hAf.le]
  have hc₂ : Ad * 39 ^ d ≤ c₀ := by
    rw [hc₀]
    nlinarith [mul_nonneg (mul_nonneg hX hAd.le) hd0,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hX) hAf.le,
      mul_nonneg hX hAd.le]
  have hn1' : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hQ : GrowthMomentsD p (scaleQD Yf Zf Yd Zd n y) (4 * d * d * (c₀ * (n + 1)))
      (max κf κd) := by
    refine growthMomentsD_scaleSum (fun q => hYfm _ _ _ _ _)
      (fun q => (hZfm _ _ _ _ _).const_mul _) (hYdm _ _ _) hB (fun q => ?_) (fun q => ?_) ?_ ?_
    · refine (hYfmom q.1 q.2 (d * n) (scaleSD n y) (scaleTD n y)).of_le (by positivity) ?_
        (le_max_left _ _)
      -- `√|S| ≤ 37^d 2^{dn}`
      have hD2 : scaleNorm d n ≤ 2 ^ (d * n) := by
        unfold scaleNorm
        rw [Real.sqrt_le_left (by positivity)]
        calc ((3 : ℝ) ^ n) ^ d ≤ ((4 : ℝ) ^ n) ^ d :=
              pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) n) d
          _ = (2 ^ (d * n)) ^ 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
              simp only [← pow_mul]
              ring_nf
      rw [div_le_iff₀ (by positivity)]
      calc Af * Real.sqrt (scaleSD n y).card ≤ Af * (37 ^ d * 2 ^ (d * n)) :=
            mul_le_mul_of_nonneg_left (hSqrtS.trans (mul_le_mul_of_nonneg_left hD2
              (by positivity))) hAf.le
        _ ≤ c₀ * (n + 1) * 2 ^ (d * n) := by
            have : Af * 37 ^ d ≤ c₀ * (n + 1) :=
              calc Af * 37 ^ d ≤ Af * 39 ^ d := mul_le_mul_of_nonneg_left h3739 hAf.le
                _ ≤ c₀ := hc₁
                _ ≤ c₀ * (n + 1) := le_mul_of_one_le_right hc₀0.le hn1'
            calc Af * (37 ^ d * 2 ^ (d * n)) = Af * 37 ^ d * 2 ^ (d * n) := by ring
              _ ≤ c₀ * (n + 1) * 2 ^ (d * n) := mul_le_mul_of_nonneg_right this (by positivity)
    · refine ((hZfmom q.1 q.2 (d * n) (scaleSD n y) (scaleTD n y)).const_mul
        (c := 1 / scaleNorm d n) (by positivity) (by positivity)).of_le (by positivity) ?_
        (le_max_left _ _)
      have hJ : ((d * n : ℕ) : ℝ) + 1 ≤ d * (n + 1) := by push_cast; linarith
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hD0]
      calc Af * ((d * n : ℕ) + 1) * Real.sqrt (scaleTD n y).card
          ≤ Af * (d * (n + 1)) * (39 ^ d * scaleNorm d n) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hJ hAf.le) hSqrtT (Real.sqrt_nonneg _)
              (by positivity)
        _ = (Af * 39 ^ d * d) * ((n + 1) * scaleNorm d n) := by ring
        _ ≤ c₀ * ((n + 1) * scaleNorm d n) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hc₀]
            have hX : (0 : ℝ) ≤ 39 ^ d := by positivity
            nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hX) hAf.le,
              mul_nonneg (mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hX) hAd.le]
        _ = c₀ * (n + 1) * scaleNorm d n := by ring
    · refine (hYdmom (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y)).of_le (by positivity) ?_
        (le_max_right _ _)
      have hE : scaleNorm d n ≤ (3 : ℝ) ^ ((d : ℝ) * ((n + 2 : ℕ) : ℝ) / 2) := by
        rw [three_rpow_eq_sqrt]
        exact Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity)
          (pow_le_pow_right₀ (by norm_num) (by omega)) d)
      have hE0 : 0 < (3 : ℝ) ^ ((d : ℝ) * ((n + 2 : ℕ) : ℝ) / 2) := by positivity
      rw [div_le_iff₀ hE0]
      calc Ad * Real.sqrt (scaleSD n y).card ≤ Ad * (37 ^ d * scaleNorm d n) :=
            mul_le_mul_of_nonneg_left hSqrtS hAd.le
        _ ≤ Ad * (39 ^ d * (3 : ℝ) ^ ((d : ℝ) * ((n + 2 : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h3739 hE hD0.le (by positivity)) hAd.le
        _ = Ad * 39 ^ d * (3 : ℝ) ^ ((d : ℝ) * ((n + 2 : ℕ) : ℝ) / 2) := by ring
        _ ≤ c₀ * (n + 1) * (3 : ℝ) ^ ((d : ℝ) * ((n + 2 : ℕ) : ℝ) / 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hE0.le
            exact hc₂.trans (le_mul_of_one_le_right hc₀0.le hn1')
    · refine ((hZdmom (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y)).const_mul
        (c := 1 / scaleNorm d n) (by positivity) (by positivity)).of_le (by positivity) ?_
        (le_max_right _ _)
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hD0]
      have hK : ((n + 2 : ℕ) : ℝ) + 1 ≤ 3 * (n + 1) := by
        push_cast
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc Ad * (((n + 2 : ℕ) : ℝ) + 1) * Real.sqrt (scaleSD n y).card
          ≤ Ad * (3 * (n + 1)) * (39 ^ d * scaleNorm d n) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hK hAd.le)
              (hSqrtS.trans (mul_le_mul_of_nonneg_right h3739 hD0.le)) (Real.sqrt_nonneg _)
              (by positivity)
        _ = (Ad * 39 ^ d * 3) * ((n + 1) * scaleNorm d n) := by ring
        _ ≤ c₀ * ((n + 1) * scaleNorm d n) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hc₀]
            have hX : (0 : ℝ) ≤ 39 ^ d := by positivity
            have hd0 : (0 : ℝ) ≤ d - 1 := by linarith
            nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hX) hAf.le,
              mul_nonneg (mul_nonneg hX hAd.le) hd0]
        _ = c₀ * (n + 1) * scaleNorm d n := by ring
  refine (hQ.const_mul (c := 1 / (n + 1)) (by positivity) (by positivity)).of_le
    (by positivity) (le_of_eq ?_) le_rfl
  field_simp

end Moments

theorem card_supBox_le_pow (y : Vertex d) (n : ℕ) :
    ((supBox y (2 * 3 ^ (n + 2) + 2)).card : ℝ) ≤ 41 ^ d * 9 ^ (d * n) := by
  refine (card_le_of_subset_supBox (subset_refl _)).trans ?_
  push_cast
  have h1 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have h3 : (3 : ℝ) ^ (n + 2) = 9 * 3 ^ n := by ring
  rw [h3]
  calc (2 * (2 * (9 * (3 : ℝ) ^ n) + 2) + 1) ^ d ≤ (41 * 9 ^ n) ^ d := by
        refine pow_le_pow_left₀ (by positivity) ?_ d
        have : (3 : ℝ) ^ n ≤ 9 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
        nlinarith
    _ = 41 ^ d * 9 ^ (d * n) := by rw [mul_pow, ← pow_mul, mul_comm n d]

theorem measure_scaleBadD_le [NeZero d] {Yf Zf : BoxVarD d} {Yd Zd : CubeVarD d}
    (hYfm : ∀ k i J S T, Measurable (Yf k i J S T)) (hZfm : ∀ k i J S T, Measurable (Zf k i J S T))
    (hYdm : ∀ K S h, Measurable (Yd K S h)) (hZdm : ∀ K S h, Measurable (Zd K S h))
    {A κ β θP C₁ s₁ : ℝ} (hθP : 0 < θP)
    (hos : ∀ z : Vertex d,
      IsOsBond d p (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) 1 θP)
    (hmom : ∀ n y, GrowthMomentsD p (scaleQnD Yf Zf Yd Zd n y) A κ)
    (htail : ∀ X : Configuration d → ℝ≥0∞, Measurable X → GrowthMomentsD p X A κ →
      ∀ t : ℝ, 0 ≤ t → latticeBondLaw d p {ω | t < (X ω).toReal} ≤
        ENNReal.ofReal (2 * Real.exp (-(t / C₁) ^ s₁)))
    (y : Vertex d) (n : ℕ) :
    latticeBondLaw d p (scaleBadD Yf Zf Yd Zd β y n) ≤
      ENNReal.ofReal (badBoundD d (2 * d + 1) β θP C₁ s₁ n) := by
  unfold scaleBadD badBoundD
  split_ifs with hn
  · rw [measure_univ, ENNReal.ofReal_one]
  · have hside := (measure_stoppingSize_lt_le hθP hos (supBox y (2 * 3 ^ (n + 2) + 2))
      ⌊(3 : ℝ) ^ (β * n)⌋₊).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (card_supBox_le_pow y n) (by positivity)))
    have hm := measurable_scaleQnD hYfm hZfm hYdm hZdm n y
    have hnull := measure_eq_top_of_growthMomentsD hm (hmom n y)
    have ht := htail _ hm (hmom n y) ((3 : ℝ) ^ (β * n) / (n + 1)) (by positivity)
    rw [div_div] at ht
    refine (measure_union_le (μ := latticeBondLaw d p) _ _).trans ?_
    refine (add_le_add (measure_union_le (μ := latticeBondLaw d p) _ _) le_rfl).trans ?_
    rw [hnull, add_zero, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hside ht

/-! ### A good scale -/

/-- **The weak norm of the centered flux at a good scale.** -/
theorem weakNormLeD_of_not_scaleBad [NeZero d] (hd : 2 ≤ d) {G : Set (Configuration d)}
    (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d) {ω : Configuration d} (hωG : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) (hP : PartitionEvent ω) {y : Vertex d}
    {χ : Fin d → Vertex d → ℝ} (hχ : IsDGCorrectorD (uniqueInfiniteComponent h) y χ)
    {abar σ : ℝ} (habarσ : abar = σ * theta d p / 2) (hσ : 0 ≤ σ)
    {Yf Zf : BoxVarD d} {Yd Zd : CubeVarD d} {α α' : ℝ} (hα'0 : 0 < α') (hα'1 : α' ≤ 1)
    (hα'α : α' ≤ α) {r : ℝ} {n : ℕ} (hr1 : 1 ≤ r) (hn1 : (3 : ℝ) ^ n ≤ r)
    (hn2 : r < 3 ^ (n + 1)) (hnot : ω ∉ scaleBadD Yf Zf Yd Zd (α' / (2 * d + 1)) y n)
    (hfl : ∀ k i : Fin d, ∀ w : Vertex d → ℝ, (∀ x ∉ scaleSD n y, w x = 0) →
      (∀ x ∉ scaleTD n y, ∀ j : Fin d, w (x + unit j) = w x) →
      ENNReal.ofReal |∑ x ∈ scaleSD n y,
          (fluxValD hG hGv k ω x i - if i = k then abar else 0) * w x| ≤
        Yf k i (d * n) (scaleSD n y) (scaleTD n y) ω * sqSum (scaleSD n y) w ^ (1 / 2 : ℝ) +
          Zf k i (d * n) (scaleSD n y) (scaleTD n y) ω * gradSqSum (scaleTD n y) w ^ (1 / 2 : ℝ))
    (hdb : ∀ (T : Finset (Vertex d)) (w : Vertex d → ℝ), scaleSD n y ⊆ T →
      ENNReal.ofReal |∑ x ∈ scaleSD n y, w x * clusterDeviationD ω (theta d p) x| ≤
        Yd (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y) ω * sqSum (scaleSD n y) w ^ (1 / 2 : ℝ) +
          Zd (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y) ω * gradSqSum T w ^ (1 / 2 : ℝ))
    (k i : Fin d) :
    WeakNormLeD ω (dgClusterBallD (uniqueInfiniteComponent h) y r) (centeredFluxD ω σ χ k i)
      (3 * d * 9 ^ d * 3 ^ (d * d) * (1 + σ) * r ^ α) := by
  set β := α' / (2 * d + 1) with hβdef
  have hd0 : (0 : ℝ) < 2 * d + 1 := by positivity
  have hβ : 0 < β := by positivity
  unfold scaleBadD at hnot
  split_ifs at hnot with hn3
  · exact absurd (Set.mem_univ ω) hnot
  have hn3' : 2 * d + 1 ≤ n := not_lt.1 hn3
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, not_lt] at hnot
  obtain ⟨⟨hside, hfin⟩, hQle⟩ := hnot
  set τ := (3 : ℝ) ^ (β * n) with hτ
  have hτ1 : 1 ≤ τ := Real.one_le_rpow (by norm_num) (by positivity)
  have hτ0 : 0 ≤ τ := by linarith
  set L := ⌊τ⌋₊ with hL
  have hL1 : 1 ≤ L := Nat.one_le_floor_iff _ |>.2 hτ1
  have hLτ : (L : ℝ) ≤ τ := Nat.floor_le hτ0
  set m := 3 ^ (n - d) with hm
  have hτm : τ ≤ (m : ℝ) := by
    rw [hτ, hm]
    push_cast
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hn' : ((n - d : ℕ) : ℝ) = n - d := by
      rw [Nat.cast_sub (by omega)]
    rw [hn', hβdef]
    have h1 : (2 * (d : ℝ) + 1) ≤ n := by exact_mod_cast hn3'
    have h2 : α' / (2 * d + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ hd0]
      have : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
      linarith
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hLm : L ≤ m := by
    have : (L : ℝ) ≤ m := hLτ.trans hτm
    exact_mod_cast this
  have hmn : m ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by norm_num)
  have hLn : L ≤ 3 ^ n := hLm.trans hmn
  have hmr : (d : ℝ) * ((m : ℝ) + L) < r := by
    have h1 : (d : ℝ) * ((m : ℝ) + L) ≤ 2 * d * m := by
      have : (L : ℝ) ≤ m := by exact_mod_cast hLm
      have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    have h2 : (2 * d : ℝ) < 3 ^ d := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 2 by norm_num) d
      have h3 : ((3 : ℝ)) ^ d = (1 + 2) ^ d := by norm_num
      linarith
    have h3 : (3 : ℝ) ^ n = 3 ^ d * m := by
      rw [hm]
      push_cast
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    have hm0 : (0 : ℝ) < m := by positivity
    calc (d : ℝ) * ((m : ℝ) + L) ≤ 2 * d * m := h1
      _ < 3 ^ d * m := mul_lt_mul_of_pos_right h2 hm0
      _ = 3 ^ n := h3.symm
      _ ≤ r := hn1
  have hτr : τ ^ (2 * d + 1) ≤ r ^ α := by
    have e : τ ^ (2 * d + 1) = ((3 : ℝ) ^ n) ^ α' := by
      rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), hβdef]
      congr 1
      push_cast
      field_simp
    rw [e]
    calc ((3 : ℝ) ^ n) ^ α' ≤ r ^ α' := Real.rpow_le_rpow (by positivity) hn1 hα'0.le
      _ ≤ r ^ α := Real.rpow_le_rpow_of_exponent_le hr1 hα'α
  -- the bounds of the variables
  have hD0 : 0 < scaleNorm d n := lt_of_lt_of_le one_pos (one_le_scaleNorm d n)
  have hQ'le : scaleQnD Yf Zf Yd Zd n y ω ≤ ENNReal.ofReal (τ / (n + 1)) :=
    (ENNReal.le_ofReal_iff_toReal_le hfin (by positivity)).2 hQle
  have hQle' : scaleQD Yf Zf Yd Zd n y ω ≤ ENNReal.ofReal τ := by
    have h1 := le_ofReal_mul_of_ofReal_div_mul_le (c := (n : ℝ) + 1) (by positivity) hQ'le
    rwa [mul_div_cancel₀ _ (by positivity)] at h1
  have hterm : Yf k i (d * n) (scaleSD n y) (scaleTD n y) ω +
      ENNReal.ofReal (1 / scaleNorm d n) * Zf k i (d * n) (scaleSD n y) (scaleTD n y) ω ≤
        scaleQD Yf Zf Yd Zd n y ω := by
    refine le_trans ?_ le_self_add
    exact Finset.single_le_sum (f := fun q : Fin d × Fin d =>
      Yf q.1 q.2 (d * n) (scaleSD n y) (scaleTD n y) ω +
        ENNReal.ofReal (1 / scaleNorm d n) * Zf q.1 q.2 (d * n) (scaleSD n y) (scaleTD n y) ω)
      (fun _ _ => bot_le) (Finset.mem_univ (k, i))
  have hYfle := (le_self_add.trans hterm).trans hQle'
  have hZfle := le_ofReal_mul_of_ofReal_div_mul_le (t := τ) hD0
    ((le_add_self.trans hterm).trans hQle')
  have hdterm : Yd (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y) ω +
      ENNReal.ofReal (1 / scaleNorm d n) * Zd (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y) ω ≤
        scaleQD Yf Zf Yd Zd n y ω := le_add_self
  have hYdle := (le_self_add.trans hdterm).trans hQle'
  have hZdle := le_ofReal_mul_of_ofReal_div_mul_le (t := τ) hD0
    ((le_add_self.trans hdterm).trans hQle')
  -- the bound at the scale `n`
  have hST : scaleSD n y ⊆ scaleTD n y := by
    intro z hz
    have h1 := mem_supBox.1 (regionD_subset_supBox _ _ hz)
    unfold scaleTD
    rw [mem_supBox]
    intro i'
    have := h1 i'
    push_cast at this ⊢
    linarith
  have hflux' : ∀ w : Vertex d → ℝ, (∀ x ∉ scaleSD n y, w x = 0) →
      (∀ x ∉ supBox y (2 * 3 ^ (n + 2) + 1), ∀ j : Fin d, w (x + unit j) = w x) →
      |∑ x ∈ scaleSD n y, (fluxValD hG hGv k ω x i - if i = k then abar else 0) * w x| ≤
        τ * Real.sqrt (∑ x ∈ scaleSD n y, w x ^ 2) + scaleNorm d n * τ * Real.sqrt (∑ j : Fin d,
          ∑ x ∈ supBox y (2 * 3 ^ (n + 2) + 1), (w (x + unit j) - w x) ^ 2) := by
    intro w hw hT
    have h1 := hfl k i w hw hT
    rw [sqSum_rpow_half_eqD, gradSqSum_rpow_half_eqD] at h1
    exact abs_le_of_ofReal_le hτ0 (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      hYfle hZfle h1
  have hdens' : ∀ w : Vertex d → ℝ,
      |∑ x ∈ scaleSD n y, w x * clusterDeviationD ω (theta d p) x| ≤
        τ * Real.sqrt (∑ x ∈ scaleSD n y, w x ^ 2) + scaleNorm d n * τ * Real.sqrt (∑ j : Fin d,
          ∑ x ∈ supBox y (2 * 3 ^ (n + 2) + 1), (w (x + unit j) - w x) ^ 2) := by
    intro w
    have h1 := hdb (scaleTD n y) w hST
    rw [sqSum_rpow_half_eqD, gradSqSum_rpow_half_eqD] at h1
    exact abs_le_of_ofReal_le hτ0 (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      hYdle hZdle h1
  have hside' : ∀ z ∈ supBox y (2 * 3 ^ (n + 2) + 2), partSide ω z ≤ L :=
    fun z hz => partSide_le_of_stoppingSize_le hP (hside z hz)
  have key := weakNormLeD_of_scale_bounds hG hGv hd hωG h hP hχ k i habarσ hσ (r := r) (n := n)
    (L := L) (m := m) hn2 hL1 hLn hm1 hmn hmr hside' (supBox_subset_regionD _ _) hτ0
    (by positivity) hτ0 (by positivity) hflux' hdens'
  have hb := scale_bound_leD (d := d) (n := n) hσ hτ1 hL1 hLτ (by omega) hτr
  exact key.mono hb

/-! ### Proposition 2.13 -/

/-- **Proposition B.1 of Dario–Gu from the weak norm bounds of the flux of `ℤ^d` and of the
density** (Step 3 of the proof). -/
theorem darioGuFluxWeakNormD_of_bounds [NeZero d] (hd : 2 ≤ d) {G : Set (Configuration d)}
    (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)
    (hpc : criticalProbability d < (p : ℝ))
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {abar σ : ℝ} (habarσ : abar = σ * theta d p / 2)
    (hσ : 0 ≤ σ) {Af κf : ℝ} (hAf : 0 < Af) (hκf : 0 < κf)
    (hbox : ∀ (k i : Fin d) (J : ℕ) (S T : Finset (Vertex d)),
      ∃ Y Z : Configuration d → ℝ≥0∞, Measurable Y ∧ Measurable Z ∧
        GrowthMomentsD p Y (Af * Real.sqrt S.card / 2 ^ J) κf ∧
        GrowthMomentsD p Z (Af * (J + 1) * Real.sqrt T.card) κf ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ w : Vertex d → ℝ, (∀ y ∉ S, w y = 0) →
          (∀ x ∉ T, ∀ j : Fin d, w (x + unit j) = w x) →
          ENNReal.ofReal |∑ x ∈ S, (fluxValD hG hGv k ω x i - if i = k then abar else 0) * w x| ≤
            Y ω * sqSum S w ^ (1 / 2 : ℝ) + Z ω * gradSqSum T w ^ (1 / 2 : ℝ))
    {Ad κd : ℝ} (hAd : 0 < Ad)
    (hdens : ∀ (K : ℕ) (S : Finset (Vertex d)), IsCubeUnion K S →
      ∃ Y Z : Configuration d → ℝ≥0∞, Measurable Y ∧ Measurable Z ∧
        GrowthMomentsD p Y (Ad * Real.sqrt S.card / (3 : ℝ) ^ ((d : ℝ) * K / 2)) κd ∧
        GrowthMomentsD p Z (Ad * (K + 1) * Real.sqrt S.card) κd ∧
        ∀ (ω : Configuration d) (T : Finset (Vertex d)) (w : Vertex d → ℝ), S ⊆ T →
          ENNReal.ofReal |∑ x ∈ S, w x * clusterDeviationD ω (theta d p) x| ≤
            Y ω * sqSum S w ^ (1 / 2 : ℝ) + Z ω * gradSqSum T w ^ (1 / 2 : ℝ)) :
    DarioGuFluxWeakNormD d p σ := by
  intro α hα
  obtain ⟨α', hα'0, hα'1, hα'α⟩ : ∃ α' : ℝ, 0 < α' ∧ α' ≤ 1 ∧ α' ≤ α :=
    ⟨min α 1, lt_min hα one_pos, min_le_right _ _, min_le_left _ _⟩
  have hβ : 0 < α' / (2 * d + 1) := by positivity
  choose Yf Zf hYfm hZfm hYfmom hZfmom hYZae using hbox
  choose Yd Zd hYdm hZdm hYdmom hZdmom hdb using hdens
  have hκ0 : 0 < max κf κd := lt_max_of_lt_left hκf
  have hmom := growthMoments_scaleQnD (p := p) (Yf := Yf) (Zf := Zf) (Yd := Yd) (Zd := Zd)
    hYfm hZfm hYdm hAf hAd hYfmom hZfmom hYdmom hZdmom
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  obtain ⟨s₁, C₁, hs₁, hC₁, htail⟩ := exists_measure_toReal_lt_leD (p := p)
    (A := 4 * d * d * (3 * d * 39 ^ d * (Af + Ad))) (κ := max κf κd) (by positivity) hκ0
  obtain ⟨θP, hθP, hos⟩ := exists_isOsBond_stoppingSizeD (p := p) hd hpc
  obtain ⟨s, hs, hsum⟩ := exists_summable_badBoundD d (2 * d + 1) hβ hθP hC₁ hs₁
  obtain ⟨AM, hAM1, hAMe⟩ : ∃ AM : ℝ, 1 ≤ AM ∧ AM = Real.exp ((1 : ℝ) ^ s) +
      ∑' n, badBoundD d (2 * d + 1) (α' / (2 * d + 1)) θP C₁ s₁ n *
        Real.exp ((1 * 3 ^ (n + 1)) ^ s) := by
    refine ⟨_, ?_, rfl⟩
    have h1 : 0 ≤ ∑' n, badBoundD d (2 * d + 1) (α' / (2 * d + 1)) θP C₁ s₁ n *
        Real.exp ((1 * 3 ^ (n + 1)) ^ s) :=
      tsum_nonneg fun n => mul_nonneg (badBoundD_nonneg _ _ _ _ _ _ n) (Real.exp_pos _).le
    have h2 : 1 ≤ Real.exp ((1 : ℝ) ^ s) := Real.one_le_exp (by rw [Real.one_rpow]; norm_num)
    linarith
  set KC : ℝ := 3 * d * 9 ^ d * 3 ^ (d * d) * (1 + σ) with hKC
  refine ⟨max KC (1 * AM ^ (1 / s)), s, by positivity, hs, fun y => ?_⟩
  obtain ⟨M, hMm, hM0, hMint, hMle, hMae⟩ := exists_minimalScale_of_summable
    (latticeBondLaw d p) (scaleBadD Yf Zf Yd Zd (α' / (2 * d + 1)) y)
    (measurableSet_scaleBadD hYfm hZfm hYdm hZdm (α' / (2 * d + 1)) y) one_pos
    (badBoundD d (2 * d + 1) (α' / (2 * d + 1)) θP C₁ s₁)
    (badBoundD_nonneg d (2 * d + 1) (α' / (2 * d + 1)) θP C₁ s₁)
    (measure_scaleBadD_le hYfm hZfm hYdm hZdm hθP hos hmom htail y) hsum
  refine ⟨M, hMm, hM0, ?_, ?_⟩
  · have e : (fun ω => Real.exp (Real.rpow (max (M ω / 1) 0) s)) =
        fun ω => Real.exp (M ω ^ s) := by
      funext ω
      rw [div_one, max_eq_left (hM0 ω)]
      rfl
    have hint : Integrable (fun ω => Real.exp (Real.rpow (max (M ω / 1) 0) s))
        (latticeBondLaw d p) := by rw [e]; exact hMint
    have hle : ∫ ω, Real.exp (Real.rpow (max (M ω / 1) 0) s) ∂latticeBondLaw d p ≤ AM := by
      rw [e, hAMe]
      exact hMle
    exact IsOsBond.mono_scale hs (by positivity) (le_max_right _ _) hMm
      (isOsBond_of_integral_le hs hAM1 hint hle)
  · filter_upwards [hGae, (partition_estimates hd hpc).1, hMae, ae_all_iff.2 fun n =>
      ae_all_iff.2 fun k => ae_all_iff.2 fun i =>
        hYZae k i (d * n) (scaleSD n y) (scaleTD n y)] with ω hωG hP hMω hfl
    intro h hy χ hχ r hr k i
    obtain ⟨N, hMN, hgood⟩ := hMω
    have h3N : (1 : ℝ) ≤ 3 ^ N := one_le_pow₀ (by norm_num)
    have hrN : (3 : ℝ) ^ N ≤ r := by rw [hMN, one_mul] at hr; exact hr
    have hr1 : (1 : ℝ) ≤ r := h3N.trans hrN
    obtain ⟨n, hn1, hn2⟩ := exists_scale_of_le hr1
    have hNn : N ≤ n := by
      have h1 : (3 : ℝ) ^ N < 3 ^ (n + 1) := lt_of_le_of_lt hrN hn2
      have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1
      omega
    refine (weakNormLeD_of_not_scaleBad hd hG hGv hωG h hP hχ habarσ hσ hα'0 hα'1 hα'α hr1 hn1
      hn2 (hgood n hNn) (fun k i => hfl n k i)
      (fun T w hT => hdb (n + 2) (scaleSD n y) (isCubeUnion_scaleSD n y) ω T w hT) k i).mono ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Dario–Gu, Proposition 2.13 (Proposition B.1), on `ℤ^d`**, from the variance bound (3.4) of
Gu's proof of his Proposition 1.1: for every supercritical `p < 1` there is `σ > 0`
(`σ = 2 ā / θ(p)`, (B.5)) with `DarioGuFluxWeakNormD d p σ`. -/
theorem darioGuFluxWeakNormD_of_variance [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hV : FluxVarianceBoundD d p) :
    ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormD d p σ := by
  obtain ⟨G, hG, hGae, hGv⟩ := exists_measurable_correctorValid hd hpc hp1
  obtain ⟨abar, Af, κf, habar, hAf, hκf, hbox⟩ :=
    exists_fluxWeakNormBoxD hG hGv hd hpc hp1 hGae hV
  obtain ⟨Ad, κd, hAd, -, hdens⟩ := exists_densityWeakNormD (p := p) hd hpc hp1
  have hθ : 0 < theta d p := theta_pos_of_criticalProbability_lt d p hpc
  refine ⟨2 * abar / theta d p, by positivity, ?_⟩
  exact darioGuFluxWeakNormD_of_bounds hd hG hGv hpc hGae (by field_simp) (by positivity) hAf
    hκf hbox hAd hdens

/-- **Dario–Gu, Proposition 2.13, in dimension two** in the form `DarioGuFluxWeakNormD 2`, with no
hypothesis (`Rigidity.Green.darioGuFluxWeakNormTwo_holds`). -/
theorem darioGuFluxWeakNormD_two_holds (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormD 2 p σ := by
  obtain ⟨σ, hσ, h⟩ := Rigidity.Green.darioGuFluxWeakNormTwo_holds p hpc hp1
  exact ⟨σ, hσ, (darioGuFluxWeakNormD_two_iff p σ).2 h⟩

end Rigidity.Green.GeneralFlux

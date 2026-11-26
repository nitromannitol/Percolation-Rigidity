import Rigidity.Proofs.Green.DarioGuFluxWeakNormBad
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds

/-!
# Proposition 2.13 of Dario–Gu in dimension two

**Dario–Gu, Proposition 2.13** (Proposition B.1, Appendix B): for every supercritical `p < 1`,
with the diffusivity `σ̄² = 2 θ(p)^{-1} ā` of (B.5) (`ā` the mean of the flux,
`exists_fluxSpatialAverage_two`), the centered flux `g̃_{e_k}` satisfies
`‖[g̃_{e_k}]_i‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ C r^α` for `r ≥ M_flux,α(y)`, `M_flux,α(y) ≤ O_s(C)`
(`darioGuFluxWeakNormTwo_holds`, the statement `DarioGuFluxWeakNormTwo`).

The proof follows Steps 1-3 of the source at the triadic scales `r ∈ [3^n, 3^{n+1})`: the bound
(eq.gsmallH-1) of the flux of `ℤ²` on a box of side `≈ 3^n` (`exists_fluxWeakNormBox`, dyadic
time `4^{2n}`), the bound (eq:DensityWeakNorm) of the density on the triadic cubes of scale
`n + 2` around `y` (`exists_densityWeakNorm`), and the partition of the good cubes with cubes of
side at most `L_n = ⌊3^{αn/4}⌋` near `y`, combined by the coarsening of the test functions
(`weakNormLe_of_scale_bounds`). A scale is bad when one of the normalized weak norms exceeds
`3^{αn/4}` or a partition cube near `y` has side more than `L_n`; the minimal scale is the first
scale after which every scale is good (`exists_minimalScale_of_summable`, the role of Lemma 1.5 of
the source), with `E[exp(M^s)]` bounded uniformly in `y`. The source's `M_q(𝒫)` and its minimal
scale of the density are replaced by the bound on the sizes of the partition cubes and the
lower bound `|𝒞_∞ ∩ B_r(y)| ≥ (2·3^{n-1} + 1)²/L_n²` of `card_mul_le_card_dgClusterBall`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Poincare Rigidity.Corrector
  Rigidity.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal Classical

namespace Rigidity.Green

variable {p : unitInterval}

/-! ### Regions -/

theorem supBox_subset_gaussianRegion (K : ℕ) (y : Vertex 2) :
    supBox y (3 ^ K) ⊆ gaussianRegion K 1 y := by
  intro x hx
  rw [mem_supBox] at hx
  rw [mem_gaussianRegion]
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

theorem gaussianRegion_subset_supBox (K : ℕ) (y : Vertex 2) :
    gaussianRegion K 1 y ⊆ supBox y (2 * 3 ^ K) := by
  intro x hx
  rw [mem_gaussianRegion] at hx
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

theorem sqrt_card_le_of_subset_supBox {S : Finset (Vertex 2)} {y : Vertex 2} {R : ℕ}
    (h : S ⊆ supBox y R) {c : ℝ} (hc : 0 ≤ c) (hR : 2 * (R : ℝ) + 1 ≤ c) :
    Real.sqrt S.card ≤ c := by
  have h1 := Finset.card_le_card h
  rw [card_supBox] at h1
  rw [Real.sqrt_le_left hc]
  have h2 : (S.card : ℝ) ≤ ((2 * R + 1) ^ 2 : ℕ) := by exact_mod_cast h1
  push_cast at h2
  nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]

/-! ### Conversion of the bounds -/

theorem sqSum_rpow_half_eq (S : Finset (Vertex 2)) (w : Vertex 2 → ℝ) :
    sqSum S w ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (∑ x ∈ S, w x ^ 2)) := by
  unfold sqSum
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _),
    ofReal_rpow_half _ (Finset.sum_nonneg fun x _ => sq_nonneg _)]

theorem gradSqSum_rpow_half_eq (T : Finset (Vertex 2)) (w : Vertex 2 → ℝ) :
    gradSqSum T w ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (∑ j : Fin 2, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2)) := by
  unfold gradSqSum
  have h0 : ∀ j : Fin 2, 0 ≤ ∑ x ∈ T, (w (x + unit j) - w x) ^ 2 :=
    fun j => Finset.sum_nonneg fun x _ => sq_nonneg _
  simp only [← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h0 j),
    ofReal_rpow_half _ (Finset.sum_nonneg fun j _ => h0 j)]

theorem abs_le_of_ofReal_le {X a b N0 N1 : ℝ} {Y Z : ℝ≥0∞} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1) (hY : Y ≤ ENNReal.ofReal a) (hZ : Z ≤ ENNReal.ofReal b)
    (h : ENNReal.ofReal |X| ≤ Y * ENNReal.ofReal N0 + Z * ENNReal.ofReal N1) :
    |X| ≤ a * N0 + b * N1 := by
  have h1 : ENNReal.ofReal |X| ≤ ENNReal.ofReal (a * N0 + b * N1) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul hb]
    exact add_le_add (mul_le_mul_left hY _) (mul_le_mul_left hZ _)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1

/-! ### The moments of the scale sum -/

theorem growthMoments_scaleSum {Y Z : Fin 2 × Fin 2 → Configuration 2 → ℝ≥0∞}
    {Yd Zd : Configuration 2 → ℝ≥0∞} (hYm : ∀ q, Measurable (Y q)) (hZm : ∀ q, Measurable (Z q))
    (hYdm : Measurable Yd) {B κ : ℝ} (hB : 0 ≤ B) (hY : ∀ q, GrowthMoments p (Y q) B κ)
    (hZ : ∀ q, GrowthMoments p (Z q) B κ) (hYd : GrowthMoments p Yd B κ)
    (hZd : GrowthMoments p Zd B κ) :
    GrowthMoments p (fun ω => ∑ q : Fin 2 × Fin 2, (Y q ω + Z q ω) + (Yd ω + Zd ω))
      (16 * B) κ := by
  have h1 : ∀ q ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
      GrowthMoments p (fun ω => Y q ω + Z q ω) (2 * B) κ :=
    fun q _ => GrowthMoments.add (hYm q).aemeasurable (hY q) (hZ q) hB
  have h2 := GrowthMoments.finsetSum (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun q => (hYm q).add (hZm q)) (by positivity) h1
  have hcard : ((Finset.univ : Finset (Fin 2 × Fin 2)).card : ℝ) = 4 := by
    rw [Finset.card_univ]
    simp
  rw [hcard] at h2
  have h3 := (GrowthMoments.add hYdm.aemeasurable hYd hZd hB).of_le (by positivity)
    (show 2 * B ≤ 4 * (2 * B) by linarith) le_rfl
  have h4 := GrowthMoments.add (Finset.measurable_sum _ fun q _ => (hYm q).add (hZm q)).aemeasurable
    h2 h3 (by positivity)
  exact h4.of_le (by positivity) (by linarith) le_rfl

/-! ### The final bound at a good scale -/

theorem scale_bound_le {σ τ r α : ℝ} {n L : ℕ} (hσ : 0 ≤ σ) (hτ : 1 ≤ τ) (hL1 : 1 ≤ L)
    (hLτ : (L : ℝ) ≤ τ) (hn : 1 ≤ n) (hτr : τ ^ 4 ≤ r ^ α) :
    max ((τ + σ * τ) * (1 + L))
        (5 * (3 ^ n * τ + σ * (3 ^ n * τ)) * (3 + 10 * (L : ℝ)) ^ 2 * L / (2 * 3 ^ (n - 1))) ≤
      1268 * (1 + σ) * r ^ α := by
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hτ0 : 0 ≤ τ := by linarith
  have h3n : (3 : ℝ) ^ n = 3 * 3 ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  have hpos : (0 : ℝ) < 3 ^ (n - 1) := by positivity
  have hτ2 : τ ≤ τ ^ 4 := by
    have : τ ^ 4 = τ * τ ^ 3 := by ring
    rw [this]
    have : 1 ≤ τ ^ 3 := one_le_pow₀ hτ
    nlinarith
  have hτ22 : τ ^ 2 ≤ τ ^ 4 := by
    have : τ ^ 4 = τ ^ 2 * τ ^ 2 := by ring
    rw [this]
    have : 1 ≤ τ ^ 2 := one_le_pow₀ hτ
    nlinarith
  have hσ1 : 0 ≤ 1 + σ := by linarith
  refine max_le ?_ ?_
  · calc (τ + σ * τ) * (1 + L) = (1 + σ) * (τ * (1 + L)) := by ring
      _ ≤ (1 + σ) * (τ * (2 * τ)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hτ0) hσ1
      _ = 2 * (1 + σ) * τ ^ 2 := by ring
      _ ≤ 1268 * (1 + σ) * τ ^ 4 := by nlinarith
      _ ≤ 1268 * (1 + σ) * r ^ α := mul_le_mul_of_nonneg_left hτr (by positivity)
  · have h1 : 5 * (3 ^ n * τ + σ * (3 ^ n * τ)) * (3 + 10 * (L : ℝ)) ^ 2 * L / (2 * 3 ^ (n - 1)) =
        15 / 2 * (1 + σ) * τ * ((3 + 10 * (L : ℝ)) ^ 2 * L) := by
      rw [h3n]
      field_simp
      ring
    have h2 : (3 + 10 * (L : ℝ)) ^ 2 * L ≤ 169 * τ ^ 3 := by
      have h3 : 3 + 10 * (L : ℝ) ≤ 13 * τ := by linarith
      have h4 : (3 + 10 * (L : ℝ)) ^ 2 ≤ (13 * τ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
      calc (3 + 10 * (L : ℝ)) ^ 2 * L ≤ (13 * τ) ^ 2 * τ :=
            mul_le_mul h4 hLτ (by positivity) (by positivity)
        _ = 169 * τ ^ 3 := by ring
    rw [h1]
    calc 15 / 2 * (1 + σ) * τ * ((3 + 10 * (L : ℝ)) ^ 2 * L)
        ≤ 15 / 2 * (1 + σ) * τ * (169 * τ ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2535 / 2 * (1 + σ) * τ ^ 4 := by ring
      _ ≤ 1268 * (1 + σ) * τ ^ 4 := by
          have : 0 ≤ (1 + σ) * τ ^ 4 := by positivity
          nlinarith
      _ ≤ 1268 * (1 + σ) * r ^ α := mul_le_mul_of_nonneg_left hτr (by positivity)

/-! ### The triadic scale of a radius -/

theorem exists_scale_of_le {r : ℝ} (hr : 1 ≤ r) :
    ∃ n : ℕ, (3 : ℝ) ^ n ≤ r ∧ r < 3 ^ (n + 1) := by
  have hfl : ⌊r⌋₊ ≠ 0 := (Nat.floor_pos.2 hr).ne'
  refine ⟨Nat.log 3 ⌊r⌋₊, ?_, ?_⟩
  · have h1 : 3 ^ Nat.log 3 ⌊r⌋₊ ≤ ⌊r⌋₊ := Nat.pow_log_le_self 3 hfl
    have h2 : ((3 ^ Nat.log 3 ⌊r⌋₊ : ℕ) : ℝ) ≤ (⌊r⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  · have h1 : ⌊r⌋₊ < 3 ^ (Nat.log 3 ⌊r⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : ((⌊r⌋₊ + 1 : ℕ) : ℝ) ≤ ((3 ^ (Nat.log 3 ⌊r⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith [Nat.lt_floor_add_one r]

theorem card_supBox_le_nine_pow (y : Vertex 2) (n : ℕ) :
    ((supBox y (2 * 3 ^ (n + 2) + 2)).card : ℝ) ≤ 1681 * 9 ^ n := by
  rw [card_supBox]
  push_cast
  have h1 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have h9 : (9 : ℝ) ^ n = (3 ^ n) ^ 2 := by
    rw [← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm]
  have h3 : (3 : ℝ) ^ (n + 2) = 9 * 3 ^ n := by ring
  rw [h9, h3]
  nlinarith

theorem le_ofReal_mul_of_ofReal_div_mul_le {c t : ℝ} (hc : 0 < c) {Z : ℝ≥0∞}
    (h : ENNReal.ofReal (1 / c) * Z ≤ ENNReal.ofReal t) : Z ≤ ENNReal.ofReal (c * t) := by
  calc Z = ENNReal.ofReal c * (ENNReal.ofReal (1 / c) * Z) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_one_div_cancel hc.ne', ENNReal.ofReal_one,
          one_mul]
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal t := mul_le_mul_right h _
    _ = ENNReal.ofReal (c * t) := (ENNReal.ofReal_mul hc.le).symm

theorem flux_moment_le {Af c₀ x : ℝ} (hAf : 0 < Af) (hc₀ : 189 * Af ≤ c₀) (n : ℕ)
    (hx : x ≤ 45 * 3 ^ n) :
    Af * x / 2 ^ (2 * n) ≤ c₀ * (n + 1) := by
  have h4 : (3 : ℝ) ^ n ≤ 2 ^ (2 * n) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hpos : (0 : ℝ) < 2 ^ (2 * n) := by positivity
  rw [div_le_iff₀ hpos]
  have h1 : Af * x ≤ 45 * Af * 3 ^ n := by nlinarith
  have h2 : 45 * Af * 3 ^ n ≤ c₀ * 2 ^ (2 * n) := by
    have : 45 * Af ≤ c₀ := by linarith
    have h3 : (0 : ℝ) ≤ 3 ^ n := by positivity
    calc 45 * Af * 3 ^ n ≤ c₀ * 3 ^ n := mul_le_mul_of_nonneg_right this h3
      _ ≤ c₀ * 2 ^ (2 * n) := mul_le_mul_of_nonneg_left h4 (by linarith)
  have h5 : c₀ * 2 ^ (2 * n) ≤ c₀ * (n + 1) * 2 ^ (2 * n) := by
    have : (0 : ℝ) ≤ c₀ * 2 ^ (2 * n) := by
      have : 0 ≤ c₀ := by linarith
      positivity
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

theorem scale_moment_le {A c x : ℝ} (hA : 0 < A) (hc : 3 * A ≤ c) (n : ℕ) (m : ℝ)
    (hm : m ≤ 3 * (n + 1)) (hm0 : 0 ≤ m) (hx : x ≤ 63 * 3 ^ n) :
    1 / 3 ^ n * (A * m * x) ≤ 63 * c * (n + 1) := by
  have h3pos : (0 : ℝ) < 3 ^ n := by positivity
  calc 1 / 3 ^ n * (A * m * x) ≤ 1 / 3 ^ n * (A * m * (63 * 3 ^ n)) := by
        gcongr
    _ = 63 * A * m * (3 ^ n / 3 ^ n) := by ring
    _ = 63 * A * m := by rw [div_self h3pos.ne', mul_one]
    _ ≤ 63 * c * (n + 1) := by
        have h1 : A * m ≤ A * (3 * (n + 1)) := mul_le_mul_of_nonneg_left hm hA.le
        have h2 : A * (3 * ((n : ℝ) + 1)) ≤ c * (n + 1) := by nlinarith
        nlinarith

/-! ### The variables of a scale -/

/-- The triadic cubes of scale `n + 2` around the cube of `y`. -/
noncomputable def scaleS (n : ℕ) (y : Vertex 2) : Finset (Vertex 2) := gaussianRegion (n + 2) 1 y

/-- The box of the gradients at the scale `n`. -/
noncomputable def scaleT (n : ℕ) (y : Vertex 2) : Finset (Vertex 2) :=
  supBox y (2 * 3 ^ (n + 2) + 1)

theorem isCubeUnion_scaleS (n : ℕ) (y : Vertex 2) : IsCubeUnion (n + 2) (scaleS n y) :=
  isCubeUnion_gaussianRegion _ _ _

/-- The random variables of the weak norms of the flux of `ℤ²` on finite sets. -/
abbrev BoxVar : Type :=
  Fin 2 → Fin 2 → ℕ → Finset (Vertex 2) → Finset (Vertex 2) → Configuration 2 → ℝ≥0∞

/-- The random variables of the weak norms of the density on unions of triadic cubes. -/
abbrev CubeVar : Type :=
  (K : ℕ) → (S : Finset (Vertex 2)) → IsCubeUnion K S → Configuration 2 → ℝ≥0∞

/-- The sum of the normalized weak norm variables at the scale `n`. -/
noncomputable def scaleQ (Yf Zf : BoxVar) (Yd Zd : CubeVar) (n : ℕ) (y : Vertex 2)
    (ω : Configuration 2) : ℝ≥0∞ :=
  ∑ q : Fin 2 × Fin 2, (Yf q.1 q.2 (2 * n) (scaleS n y) (scaleT n y) ω +
      ENNReal.ofReal (1 / 3 ^ n) * Zf q.1 q.2 (2 * n) (scaleS n y) (scaleT n y) ω) +
    (Yd (n + 2) (scaleS n y) (isCubeUnion_scaleS n y) ω +
      ENNReal.ofReal (1 / 3 ^ n) * Zd (n + 2) (scaleS n y) (isCubeUnion_scaleS n y) ω)

/-- `scaleQ / (n + 1)`. -/
noncomputable def scaleQn (Yf Zf : BoxVar) (Yd Zd : CubeVar) (n : ℕ) (y : Vertex 2)
    (ω : Configuration 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (n + 1)) * scaleQ Yf Zf Yd Zd n y ω

/-- The bad event of the scale `n`. -/
noncomputable def scaleBad (Yf Zf : BoxVar) (Yd Zd : CubeVar) (β : ℝ) (y : Vertex 2) (n : ℕ) :
    Set (Configuration 2) :=
  if n < 3 then Set.univ else
    ({ω | ∃ z ∈ supBox y (2 * 3 ^ (n + 2) + 2), ⌊(3 : ℝ) ^ (β * n)⌋₊ < planarSide ω z} ∪
      {ω | scaleQn Yf Zf Yd Zd n y ω = ⊤}) ∪
    {ω | (3 : ℝ) ^ (β * n) / (n + 1) < (scaleQn Yf Zf Yd Zd n y ω).toReal}

section Moments

variable {Yf Zf : BoxVar} {Yd Zd : CubeVar}
  (hYfm : ∀ k i J S T, Measurable (Yf k i J S T)) (hZfm : ∀ k i J S T, Measurable (Zf k i J S T))
  (hYdm : ∀ K S h, Measurable (Yd K S h)) (hZdm : ∀ K S h, Measurable (Zd K S h))

include hYfm hZfm hYdm hZdm in
theorem measurable_scaleQn (n : ℕ) (y : Vertex 2) : Measurable (scaleQn Yf Zf Yd Zd n y) :=
  ((Finset.measurable_sum _ fun _ _ => (hYfm _ _ _ _ _).add ((hZfm _ _ _ _ _).const_mul _)).add
    ((hYdm _ _ _).add ((hZdm _ _ _).const_mul _))).const_mul _

include hYfm hZfm hYdm hZdm in
theorem measurableSet_scaleBad (β : ℝ) (y : Vertex 2) (n : ℕ) :
    MeasurableSet (scaleBad Yf Zf Yd Zd β y n) := by
  unfold scaleBad
  split_ifs
  · exact MeasurableSet.univ
  · exact ((measurableSet_planarSide_lt _ _).union
      (measurableSet_eq_fun (measurable_scaleQn hYfm hZfm hYdm hZdm n y) measurable_const)).union
      (measurableSet_lt measurable_const (measurable_scaleQn hYfm hZfm hYdm hZdm n y).ennreal_toReal)

include hYfm hZfm hYdm in
theorem growthMoments_scaleQn {Af κf Ad κd : ℝ} (hAf : 0 < Af) (hAd : 0 < Ad)
    (hYfmom : ∀ k i J S T, GrowthMoments p (Yf k i J S T) (Af * Real.sqrt S.card / 2 ^ J) κf)
    (hZfmom : ∀ k i J S T,
      GrowthMoments p (Zf k i J S T) (Af * (J + 1) * Real.sqrt T.card) κf)
    (hYdmom : ∀ K S h, GrowthMoments p (Yd K S h) (Ad * Real.sqrt S.card / 3 ^ K) κd)
    (hZdmom : ∀ K S h, GrowthMoments p (Zd K S h) (Ad * (K + 1) * Real.sqrt S.card) κd)
    (n : ℕ) (y : Vertex 2) :
    GrowthMoments p (scaleQn Yf Zf Yd Zd n y) (16 * (63 * (3 * Af + 3 * Ad))) (max κf κd) := by
  set c₀ := 63 * (3 * Af + 3 * Ad) with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  have hB : 0 ≤ c₀ * (n + 1) := by positivity
  have h3n2 : (3 : ℝ) ^ (n + 2) = 9 * 3 ^ n := by ring
  have h1n : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hScard : Real.sqrt (scaleS n y).card ≤ 45 * 3 ^ n := by
    refine sqrt_card_le_of_subset_supBox (gaussianRegion_subset_supBox _ _) (by positivity) ?_
    push_cast
    rw [h3n2]
    linarith
  have hTcard : Real.sqrt (scaleT n y).card ≤ 63 * 3 ^ n := by
    refine sqrt_card_le_of_subset_supBox (subset_refl _) (by positivity) ?_
    push_cast
    rw [h3n2]
    linarith
  have hQ : GrowthMoments p (scaleQ Yf Zf Yd Zd n y) (16 * (c₀ * (n + 1))) (max κf κd) := by
    refine growthMoments_scaleSum (fun q => hYfm _ _ _ _ _) (fun q => (hZfm _ _ _ _ _).const_mul _)
      (hYdm _ _ _) hB (fun q => ?_) (fun q => ?_) ?_ ?_
    · refine (hYfmom q.1 q.2 (2 * n) (scaleS n y) (scaleT n y)).of_le (by positivity) ?_
        (le_max_left _ _)
      exact flux_moment_le hAf (by rw [hc₀]; linarith) n hScard
    · refine ((hZfmom q.1 q.2 (2 * n) (scaleS n y) (scaleT n y)).const_mul (c := 1 / 3 ^ n)
        (by positivity) (by positivity)).of_le (by positivity) ?_ (le_max_left _ _)
      have h := scale_moment_le (A := Af) (c := 3 * Af + 3 * Ad) hAf (by linarith) n
        ((2 * n : ℕ) + 1) (by push_cast; linarith) (by positivity) hTcard
      rw [hc₀]
      linarith
    · refine (hYdmom (n + 2) (scaleS n y) (isCubeUnion_scaleS n y)).of_le (by positivity) ?_
        (le_max_right _ _)
      rw [div_le_iff₀ (by positivity), h3n2]
      calc Ad * Real.sqrt (scaleS n y).card ≤ Ad * (45 * 3 ^ n) :=
            mul_le_mul_of_nonneg_left hScard hAd.le
        _ = 5 * Ad * (9 * 3 ^ n) := by ring
        _ ≤ c₀ * (n + 1) * (9 * 3 ^ n) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hc₀]
            nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · refine ((hZdmom (n + 2) (scaleS n y) (isCubeUnion_scaleS n y)).const_mul (c := 1 / 3 ^ n)
        (by positivity) (by positivity)).of_le (by positivity) ?_ (le_max_right _ _)
      have h := scale_moment_le (A := Ad) (c := 3 * Af + 3 * Ad) hAd (by linarith) n
        (((n + 2 : ℕ) : ℝ) + 1) (by push_cast; linarith) (by positivity)
        (hScard.trans (by linarith))
      rw [hc₀]
      linarith
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  refine (hQ.const_mul (c := 1 / (n + 1)) (by positivity) (by positivity)).of_le
    (by positivity) (le_of_eq ?_) le_rfl
  field_simp

end Moments

theorem measure_scaleBad_le {Yf Zf : BoxVar} {Yd Zd : CubeVar}
    (hYfm : ∀ k i J S T, Measurable (Yf k i J S T)) (hZfm : ∀ k i J S T, Measurable (Zf k i J S T))
    (hYdm : ∀ K S h, Measurable (Yd K S h)) (hZdm : ∀ K S h, Measurable (Zd K S h))
    {A κ β θP C₁ s₁ : ℝ} (hθP : 0 < θP)
    (hos : ∀ z : Vertex 2,
      IsOsBond 2 p (fun ω => TriadicCube.stoppingSize (planarGoodCubes ω) z) 1 θP)
    (hmom : ∀ n y, GrowthMoments p (scaleQn Yf Zf Yd Zd n y) A κ)
    (htail : ∀ X : Configuration 2 → ℝ≥0∞, Measurable X → GrowthMoments p X A κ →
      ∀ t : ℝ, 0 ≤ t → latticeBondLaw 2 p {ω | t < (X ω).toReal} ≤
        ENNReal.ofReal (2 * Real.exp (-(t / C₁) ^ s₁)))
    (y : Vertex 2) (n : ℕ) :
    latticeBondLaw 2 p (scaleBad Yf Zf Yd Zd β y n) ≤ ENNReal.ofReal (badBound 3 β θP C₁ s₁ n) := by
  unfold scaleBad badBound
  split_ifs with hn
  · rw [measure_univ, ENNReal.ofReal_one]
  · have hside := (measure_planarSide_lt_le hθP hos (supBox y (2 * 3 ^ (n + 2) + 2))
      ⌊(3 : ℝ) ^ (β * n)⌋₊).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (card_supBox_le_nine_pow y n) (by positivity)))
    have hm := measurable_scaleQn hYfm hZfm hYdm hZdm n y
    have hnull := measure_eq_top_of_growthMoments hm (hmom n y)
    have ht := htail _ hm (hmom n y) ((3 : ℝ) ^ (β * n) / (n + 1)) (by positivity)
    rw [div_div] at ht
    refine (measure_union_le (μ := latticeBondLaw 2 p) _ _).trans ?_
    refine (add_le_add (measure_union_le (μ := latticeBondLaw 2 p) _ _) le_rfl).trans ?_
    rw [hnull, add_zero, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hside ht

/-! ### A good scale -/

/-- **The weak norm of the centered flux at a good scale.** -/
theorem weakNormLe_of_not_scaleBad {G : Set (Configuration 2)} (hG : MeasurableSet G)
    (hGv : G ⊆ correctorValidEvent 2) {ω : Configuration 2} (hωG : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) (hP : PlanarPartitionEvent ω) {y : Vertex 2}
    {χ : Fin 2 → Vertex 2 → ℝ} (hχ : IsDGCorrector (uniqueInfiniteComponent h) y χ)
    {abar σ : ℝ} (habarσ : abar = σ * theta 2 p / 2) (hσ : 0 ≤ σ)
    {Yf Zf : BoxVar} {Yd Zd : CubeVar} {α α' : ℝ} (hα'0 : 0 < α') (hα'1 : α' ≤ 1)
    (hα'α : α' ≤ α) {r : ℝ} {n : ℕ} (hr1 : 1 ≤ r) (hn1 : (3 : ℝ) ^ n ≤ r)
    (hn2 : r < 3 ^ (n + 1)) (hnot : ω ∉ scaleBad Yf Zf Yd Zd (α' / 4) y n)
    (hfl : ∀ k i : Fin 2, ∀ w : Vertex 2 → ℝ, (∀ x ∉ scaleS n y, w x = 0) →
      (∀ x ∉ scaleT n y, ∀ j : Fin 2, w (x + unit j) = w x) →
      ENNReal.ofReal |∑ x ∈ scaleS n y,
          (fluxVal hG hGv k ω (x, i) - if i = k then abar else 0) * w x| ≤
        Yf k i (2 * n) (scaleS n y) (scaleT n y) ω * sqSum (scaleS n y) w ^ (1 / 2 : ℝ) +
          Zf k i (2 * n) (scaleS n y) (scaleT n y) ω * gradSqSum (scaleT n y) w ^ (1 / 2 : ℝ))
    (hdb : ∀ (T : Finset (Vertex 2)) (w : Vertex 2 → ℝ), scaleS n y ⊆ T →
      ENNReal.ofReal |∑ x ∈ scaleS n y, w x * clusterDeviation ω (theta 2 p) x| ≤
        Yd (n + 2) (scaleS n y) (isCubeUnion_scaleS n y) ω * sqSum (scaleS n y) w ^ (1 / 2 : ℝ) +
          Zd (n + 2) (scaleS n y) (isCubeUnion_scaleS n y) ω * gradSqSum T w ^ (1 / 2 : ℝ))
    (k i : Fin 2) :
    WeakNormLe ω (dgClusterBall (uniqueInfiniteComponent h) y r) (centeredFlux ω σ χ k i)
      (1268 * (1 + σ) * r ^ α) := by
  set β := α' / 4 with hβdef
  have hβ : 0 < β := by positivity
  unfold scaleBad at hnot
  split_ifs at hnot with hn3
  · exact absurd (Set.mem_univ ω) hnot
  have hn3' : 3 ≤ n := not_lt.1 hn3
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, not_lt] at hnot
  obtain ⟨⟨hside, hfin⟩, hQle⟩ := hnot
  set τ := (3 : ℝ) ^ (β * n) with hτ
  have hτ1 : 1 ≤ τ := Real.one_le_rpow (by norm_num) (by positivity)
  have hτ0 : 0 ≤ τ := by linarith
  set L := ⌊τ⌋₊ with hL
  have hL1 : 1 ≤ L := Nat.one_le_floor_iff _ |>.2 hτ1
  have hLτ : (L : ℝ) ≤ τ := Nat.floor_le hτ0
  have hτn : τ ≤ 3 ^ (n - 2) := by
    rw [hτ, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hn' : ((n - 2 : ℕ) : ℝ) = n - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hn', hβdef]
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3'
    nlinarith
  have hLn2 : L ≤ 3 ^ (n - 2) := by
    have : (L : ℝ) ≤ ((3 ^ (n - 2) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hτr : τ ^ 4 ≤ r ^ α := by
    have e : τ ^ 4 = ((3 : ℝ) ^ n) ^ α' := by
      rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), hβdef]
      congr 1
      push_cast
      ring
    rw [e]
    calc ((3 : ℝ) ^ n) ^ α' ≤ r ^ α' := Real.rpow_le_rpow (by positivity) hn1 hα'0.le
      _ ≤ r ^ α := Real.rpow_le_rpow_of_exponent_le hr1 hα'α
  -- the bounds of the variables
  have hQ'le : scaleQn Yf Zf Yd Zd n y ω ≤ ENNReal.ofReal (τ / (n + 1)) :=
    (ENNReal.le_ofReal_iff_toReal_le hfin (by positivity)).2 hQle
  have hQle' : scaleQ Yf Zf Yd Zd n y ω ≤ ENNReal.ofReal τ := by
    have h1 := le_ofReal_mul_of_ofReal_div_mul_le (c := (n : ℝ) + 1) (by positivity) hQ'le
    rwa [mul_div_cancel₀ _ (by positivity)] at h1
  have hterm : Yf k i (2 * n) (scaleS n y) (scaleT n y) ω +
      ENNReal.ofReal (1 / 3 ^ n) * Zf k i (2 * n) (scaleS n y) (scaleT n y) ω ≤
        scaleQ Yf Zf Yd Zd n y ω := by
    refine le_trans ?_ le_self_add
    exact Finset.single_le_sum (f := fun q : Fin 2 × Fin 2 =>
      Yf q.1 q.2 (2 * n) (scaleS n y) (scaleT n y) ω +
        ENNReal.ofReal (1 / 3 ^ n) * Zf q.1 q.2 (2 * n) (scaleS n y) (scaleT n y) ω)
      (fun _ _ => bot_le) (Finset.mem_univ (k, i))
  have hYfle := (le_self_add.trans hterm).trans hQle'
  have hZfle := le_ofReal_mul_of_ofReal_div_mul_le (t := τ) (by positivity)
    ((le_add_self.trans hterm).trans hQle')
  have hdterm : Yd (n + 2) (scaleS n y) (isCubeUnion_scaleS n y) ω +
      ENNReal.ofReal (1 / 3 ^ n) * Zd (n + 2) (scaleS n y) (isCubeUnion_scaleS n y) ω ≤
        scaleQ Yf Zf Yd Zd n y ω := le_add_self
  have hYdle := (le_self_add.trans hdterm).trans hQle'
  have hZdle := le_ofReal_mul_of_ofReal_div_mul_le (t := τ) (by positivity)
    ((le_add_self.trans hdterm).trans hQle')
  -- the bound at the scale `n`
  have hST : scaleS n y ⊆ scaleT n y := by
    intro z hz
    have h1 := mem_supBox.1 (gaussianRegion_subset_supBox _ _ hz)
    unfold scaleT
    rw [mem_supBox]
    intro i'
    have := h1 i'
    push_cast at this ⊢
    linarith
  have hflux' : ∀ w : Vertex 2 → ℝ, (∀ x ∉ scaleS n y, w x = 0) →
      (∀ x ∉ supBox y (2 * 3 ^ (n + 2) + 1), ∀ j : Fin 2, w (x + unit j) = w x) →
      |∑ x ∈ scaleS n y, (fluxVal hG hGv k ω (x, i) - if i = k then abar else 0) * w x| ≤
        τ * Real.sqrt (∑ x ∈ scaleS n y, w x ^ 2) + 3 ^ n * τ * Real.sqrt (∑ j : Fin 2,
          ∑ x ∈ supBox y (2 * 3 ^ (n + 2) + 1), (w (x + unit j) - w x) ^ 2) := by
    intro w hw hT
    have h1 := hfl k i w hw hT
    rw [sqSum_rpow_half_eq, gradSqSum_rpow_half_eq] at h1
    exact abs_le_of_ofReal_le hτ0 (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      hYfle hZfle h1
  have hdens' : ∀ w : Vertex 2 → ℝ,
      |∑ x ∈ scaleS n y, w x * clusterDeviation ω (theta 2 p) x| ≤
        τ * Real.sqrt (∑ x ∈ scaleS n y, w x ^ 2) + 3 ^ n * τ * Real.sqrt (∑ j : Fin 2,
          ∑ x ∈ supBox y (2 * 3 ^ (n + 2) + 1), (w (x + unit j) - w x) ^ 2) := by
    intro w
    have h1 := hdb (scaleT n y) w hST
    rw [sqSum_rpow_half_eq, gradSqSum_rpow_half_eq] at h1
    exact abs_le_of_ofReal_le hτ0 (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      hYdle hZdle h1
  have key := weakNormLe_of_scale_bounds hG hGv hωG h hP hχ k i habarσ hσ (r := r) (n := n)
    (L := L) (by omega) hn1 hn2 hL1 hLn2 (fun z hz => hside z hz)
    (supBox_subset_gaussianRegion _ _) hτ0 (by positivity) hτ0 (by positivity) hflux' hdens'
  exact key.mono (scale_bound_le hσ hτ1 hL1 hLτ (by omega) hτr)

/-- **Proposition B.1 of Dario–Gu from the weak norm bounds of the flux of `ℤ²` and of the
density** (Step 3 of the proof). -/
theorem darioGuFluxWeakNormTwo_of_bounds {G : Set (Configuration 2)} (hG : MeasurableSet G)
    (hGv : G ⊆ correctorValidEvent 2) (hpc : criticalProbability 2 < (p : ℝ))
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {abar σ : ℝ} (habarσ : abar = σ * theta 2 p / 2)
    (hσ : 0 ≤ σ) {Af κf : ℝ} (hAf : 0 < Af) (hκf : 0 < κf)
    (hbox : ∀ (k i : Fin 2) (J : ℕ) (S T : Finset (Vertex 2)),
      ∃ Y Z : Configuration 2 → ℝ≥0∞, Measurable Y ∧ Measurable Z ∧
        GrowthMoments p Y (Af * Real.sqrt S.card / 2 ^ J) κf ∧
        GrowthMoments p Z (Af * (J + 1) * Real.sqrt T.card) κf ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ w : Vertex 2 → ℝ, (∀ y ∉ S, w y = 0) →
          (∀ x ∉ T, ∀ j : Fin 2, w (x + unit j) = w x) →
          ENNReal.ofReal |∑ x ∈ S, (fluxVal hG hGv k ω (x, i) - if i = k then abar else 0) * w x| ≤
            Y ω * sqSum S w ^ (1 / 2 : ℝ) + Z ω * gradSqSum T w ^ (1 / 2 : ℝ))
    {Ad κd : ℝ} (hAd : 0 < Ad)
    (hdens : ∀ (K : ℕ) (S : Finset (Vertex 2)), IsCubeUnion K S →
      ∃ Y Z : Configuration 2 → ℝ≥0∞, Measurable Y ∧ Measurable Z ∧
        GrowthMoments p Y (Ad * Real.sqrt S.card / 3 ^ K) κd ∧
        GrowthMoments p Z (Ad * (K + 1) * Real.sqrt S.card) κd ∧
        ∀ (ω : Configuration 2) (T : Finset (Vertex 2)) (w : Vertex 2 → ℝ), S ⊆ T →
          ENNReal.ofReal |∑ x ∈ S, w x * clusterDeviation ω (theta 2 p) x| ≤
            Y ω * sqSum S w ^ (1 / 2 : ℝ) + Z ω * gradSqSum T w ^ (1 / 2 : ℝ)) :
    DarioGuFluxWeakNormTwo p σ := by
  intro α hα
  obtain ⟨α', hα'0, hα'1, hα'α⟩ : ∃ α' : ℝ, 0 < α' ∧ α' ≤ 1 ∧ α' ≤ α :=
    ⟨min α 1, lt_min hα one_pos, min_le_right _ _, min_le_left _ _⟩
  have hβ : 0 < α' / 4 := by positivity
  choose Yf Zf hYfm hZfm hYfmom hZfmom hYZae using hbox
  choose Yd Zd hYdm hZdm hYdmom hZdmom hdb using hdens
  have hκ0 : 0 < max κf κd := lt_max_of_lt_left hκf
  have hmom := growthMoments_scaleQn (p := p) (Yf := Yf) (Zf := Zf) (Yd := Yd) (Zd := Zd) hYfm hZfm
    hYdm hAf hAd hYfmom hZfmom hYdmom hZdmom
  obtain ⟨s₁, C₁, hs₁, hC₁, htail⟩ := exists_measure_toReal_lt_le (p := p)
    (A := 16 * (63 * (3 * Af + 3 * Ad))) (κ := max κf κd) (by positivity) hκ0
  obtain ⟨θP, hθP, hos⟩ := exists_isOsBond_stoppingSize (p := p) hpc
  obtain ⟨s, hs, hsum⟩ := exists_summable_badBound 3 hβ hθP hC₁ hs₁
  obtain ⟨AM, hAM1, hAMe⟩ : ∃ AM : ℝ, 1 ≤ AM ∧ AM = Real.exp ((1 : ℝ) ^ s) +
      ∑' n, badBound 3 (α' / 4) θP C₁ s₁ n * Real.exp ((1 * 3 ^ (n + 1)) ^ s) := by
    refine ⟨_, ?_, rfl⟩
    have h1 : 0 ≤ ∑' n, badBound 3 (α' / 4) θP C₁ s₁ n * Real.exp ((1 * 3 ^ (n + 1)) ^ s) :=
      tsum_nonneg fun n => mul_nonneg (badBound_nonneg _ _ _ _ _ n) (Real.exp_pos _).le
    have h2 : 1 ≤ Real.exp ((1 : ℝ) ^ s) := Real.one_le_exp (by rw [Real.one_rpow]; norm_num)
    linarith
  refine ⟨max (1268 * (1 + σ)) (1 * AM ^ (1 / s)), s, by positivity, hs, fun y => ?_⟩
  obtain ⟨M, hMm, hM0, hMint, hMle, hMae⟩ := exists_minimalScale_of_summable
    (latticeBondLaw 2 p) (scaleBad Yf Zf Yd Zd (α' / 4) y)
    (measurableSet_scaleBad hYfm hZfm hYdm hZdm (α' / 4) y) one_pos (badBound 3 (α' / 4) θP C₁ s₁)
    (badBound_nonneg 3 (α' / 4) θP C₁ s₁)
    (measure_scaleBad_le hYfm hZfm hYdm hZdm hθP hos hmom htail y) hsum
  refine ⟨M, hMm, hM0, ?_, ?_⟩
  · have e : (fun ω => Real.exp (Real.rpow (max (M ω / 1) 0) s)) =
        fun ω => Real.exp (M ω ^ s) := by
      funext ω
      rw [div_one, max_eq_left (hM0 ω)]
      rfl
    have hint : Integrable (fun ω => Real.exp (Real.rpow (max (M ω / 1) 0) s))
        (latticeBondLaw 2 p) := by rw [e]; exact hMint
    have hle : ∫ ω, Real.exp (Real.rpow (max (M ω / 1) 0) s) ∂latticeBondLaw 2 p ≤ AM := by
      rw [e, hAMe]
      exact hMle
    exact IsOsBond.mono_scale hs (by positivity) (le_max_right _ _) hMm
      (isOsBond_of_integral_le hs hAM1 hint hle)
  · filter_upwards [hGae, ae_planarPartitionEvent hpc, hMae, ae_all_iff.2 fun n =>
      ae_all_iff.2 fun k => ae_all_iff.2 fun i => hYZae k i (2 * n) (scaleS n y) (scaleT n y)] with
      ω hωG hP hMω hfl
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
    refine (weakNormLe_of_not_scaleBad hG hGv hωG h hP hχ habarσ hσ hα'0 hα'1 hα'α hr1 hn1 hn2
      (hgood n hNn) (fun k i => hfl n k i)
      (fun T w hT => hdb (n + 2) (scaleS n y) (isCubeUnion_scaleS n y) ω T w hT) k i).mono ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Dario–Gu, Proposition 2.13 (Proposition B.1), in dimension two.** -/
theorem darioGuFluxWeakNormTwo_holds : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) →
    (p : ℝ) < 1 → ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ := by
  intro p hpc hp1
  obtain ⟨G, hG, hGae, hGv⟩ := exists_measurable_correctorValid_two
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds hpc hp1
  obtain ⟨abar, Af, κf, habar, hAf, hκf, hbox⟩ := exists_fluxWeakNormBox hG hGv hpc hp1 hGae
  obtain ⟨Ad, κd, hAd, -, hdens⟩ := exists_densityWeakNorm (p := p) hpc hp1
  have hθ : 0 < theta 2 p := theta_pos_of_criticalProbability_lt 2 p hpc
  refine ⟨2 * abar / theta 2 p, by positivity, ?_⟩
  exact darioGuFluxWeakNormTwo_of_bounds hG hGv hpc hGae (by field_simp) (by positivity) hAf hκf
    hbox hAd hdens

end Rigidity.Green

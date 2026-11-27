import Rigidity.Proofs.Corrector.OsCalculus
import PercolationClusterHomogenization.External.PlanarInputs
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra

/-!
# The quantitative sublinearity of the planar corrector (Dario–Gu, Proposition 2.12)

Dario–Gu, Proposition 2.12, asserts that for every `α > 0` there are
`s, C` and, for every `y ∈ ℤ^d`, a minimal scale `M_corr,α(y) ≤ O_s(C)` such that
`osc_{𝒞_∞ ∩ B_r(y)} χ_p ≤ C |p| r^α` for every `r ≥ M_corr,α(y)` and every `p`. The proof printed
there combines the optimal corrector bound of Dario (Theorem 1 of *Optimal corrector estimates on
percolation clusters*, Ann. Appl. Probab. 2021, arXiv:1805.00902)
`|χ_p(x) - χ_p(y)| 1_{x, y ∈ 𝒞_∞} ≤ O_s(C |p| log^{1/2} |x - y|)` in dimension two with Lemma 1.6
applied to the sequence `X_n = 3^{-αn} sup_{x ∈ B_{3^n}(y)} |χ_p(x) - χ_p(y)| 1_{x, y ∈ 𝒞_∞}`.

This file states Dario's Theorem 1 in dimension two as `DarioOptimalCorrectorTwo` (proved:
`Rigidity.Poincare.darioOptimalCorrectorTwo_holds`) and proves the planar corrector input
`CorrectorQuantitativeInputTwo` from it and the planar qualitative corrector input
`SupercriticalBondCorrectorInputTwo`.

* The pairs are taken in the lattice ball `B_{3^n}(x)` around the centre `x` of the statement, not
  from the centre: this bounds the oscillation also when `x ∉ 𝒞_∞`.
* The supremum over the `O(3^{4n})` pairs is controlled by a union bound on the Chebyshev tails,
  in place of the sum of `2d/α`-th powers of the printed proof; the minimal scale is the triadic
  scale of Lemma 1.6 of the bad events `{∃ pair: |χ(x) - χ(x')| ≥ 3^{αn}}`, at least `1`.
* The bound for every slope `q` and every corrected plane of slope `q` follows from the two
  coordinate slopes: by the uniqueness of corrected planes (first clause of the qualitative input)
  the corrector is linear in the slope modulo constants (Dario–Gu, §2.3.1).
* Dario's display has `log^{1/2} |x - y|`, which vanishes at `|x - y| = 1`; the statement uses
  `log^{1/2} (2 + |x - y|)`, comparable to it for `|x - y| ≥ 2`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal

/-- **Dario, Theorem 1** (optimal `L^∞` estimates for the first-order correctors), in dimension
two: there are `s > 0` and `C < ∞` such that for all `x, y ∈ ℤ²` and every slope `q`,
`|χ_q(x) - χ_q(y)| 1_{x, y ∈ 𝒞_∞} ≤ O_s(C |q| log^{1/2}(2 + |x - y|))`, where
`χ_q = ℓ_q - q·x` for a corrected plane `ℓ_q` of slope `q`. The random variable is dominated by a
measurable `Z ≤ O_s(·)`. -/
def DarioOptimalCorrectorTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (q : Fin 2 → ℝ) (x y : Vertex 2),
      ∃ Z : Configuration 2 → ℝ, Measurable Z ∧
        IsOsBond 2 p Z s (C * (∑ i, |q i|) *
          Real.sqrt (Real.log (2 + ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖))) ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          ∀ ℓ : uniqueInfiniteComponent h → ℝ,
            IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
          ∀ (hx : x ∈ (uniqueInfiniteComponent h).supp) (hy : y ∈ (uniqueInfiniteComponent h).supp),
            |(ℓ ⟨x, hx⟩ - ∑ i, q i * x i) - (ℓ ⟨y, hy⟩ - ∑ i, q i * y i)| ≤ Z ω

/-! ### Linearity of the corrector in the slope -/

/-- By the uniqueness of normalized corrected planes, the increments of a corrected plane of slope
`q` are the combination of those of the corrected planes of the coordinate slopes. -/
theorem correctedPlane_sub_eq {ω : Configuration 2} {C : OpenComponent ω}
    (hC : ∀ (q : Fin 2 → ℝ) (o : C), ∃! u : C → ℝ, IsCorrectedPlane C q u ∧ u o = 0)
    {q : Fin 2 → ℝ} {ℓ ℓ₀ ℓ₁ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ)
    (h₀ : IsCorrectedPlane C (Pi.single 0 1) ℓ₀) (h₁ : IsCorrectedPlane C (Pi.single 1 1) ℓ₁)
    (a b : C) : ℓ a - ℓ b = q 0 * (ℓ₀ a - ℓ₀ b) + q 1 * (ℓ₁ a - ℓ₁ b) := by
  have hw : IsCorrectedPlane C 0 (ℓ - (q 0 • ℓ₀ + q 1 • ℓ₁)) := by
    have h := isCorrectedPlane_sub C hℓ
      (isCorrectedPlane_add C (isCorrectedPlane_smul C h₀ (q 0)) (isCorrectedPlane_smul C h₁ (q 1)))
    have hq : q - (q 0 • (Pi.single 0 1 : Fin 2 → ℝ) + q 1 • (Pi.single 1 1 : Fin 2 → ℝ)) = 0 := by
      funext i
      fin_cases i <;> simp
    rwa [hq] at h
  set w := ℓ - (q 0 • ℓ₀ + q 1 • ℓ₁) with hwdef
  have hw' : IsCorrectedPlane C 0 (w - fun _ => w b) := by
    simpa only [sub_zero] using isCorrectedPlane_sub C hw (isCorrectedPlane_const C (w b))
  have heq := (hC 0 b).unique ⟨hw', by simp⟩ ⟨isCorrectedPlane_const C 0, rfl⟩
  have ha := congrFun heq a
  simp only [hwdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha
  linarith

theorem sum_single_mul (i : Fin 2) (v : Vertex 2) :
    ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * (v j : ℝ) = v i := by
  fin_cases i <;> simp [Fin.sum_univ_two]

theorem sum_abs_single (i : Fin 2) : ∑ j, |(Pi.single i (1 : ℝ) : Fin 2 → ℝ) j| = 1 := by
  fin_cases i <;> simp [Fin.sum_univ_two]

/-- The increments of the corrector `χ_q = ℓ - q·x` are the combination of those of the coordinate
correctors. -/
theorem corrector_sub_eq {ω : Configuration 2} {C : OpenComponent ω}
    (hC : ∀ (q : Fin 2 → ℝ) (o : C), ∃! u : C → ℝ, IsCorrectedPlane C q u ∧ u o = 0)
    {q : Fin 2 → ℝ} {ℓ ℓ₀ ℓ₁ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ)
    (h₀ : IsCorrectedPlane C (Pi.single 0 1) ℓ₀) (h₁ : IsCorrectedPlane C (Pi.single 1 1) ℓ₁)
    (a b : C) :
    (ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i) =
      q 0 * ((ℓ₀ a - ∑ j, (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) j * a.val j) -
        (ℓ₀ b - ∑ j, (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) j * b.val j)) +
      q 1 * ((ℓ₁ a - ∑ j, (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) j * a.val j) -
        (ℓ₁ b - ∑ j, (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) j * b.val j)) := by
  have h := correctedPlane_sub_eq hC hℓ h₀ h₁ a b
  rw [sum_single_mul, sum_single_mul, sum_single_mul, sum_single_mul, Fin.sum_univ_two,
    Fin.sum_univ_two]
  linear_combination h

/-! ### Lattice balls and bad events -/

/-- The lattice box `x + [-N, N]²`. -/
noncomputable def latticeBox (x : Vertex 2) (N : ℕ) : Finset (Vertex 2) :=
  Fintype.piFinset fun i => Finset.Icc (x i - N) (x i + N)

theorem card_latticeBox (x : Vertex 2) (N : ℕ) : (latticeBox x N).card = (2 * N + 1) ^ 2 := by
  have hI : ∀ i : Fin 2, (Finset.Icc (x i - N) (x i + N)).card = 2 * N + 1 := by
    intro i
    rw [Int.card_Icc, show x i + (N : ℤ) + 1 - (x i - N) = ((2 * N + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
  rw [latticeBox, Fintype.card_piFinset, Fin.prod_univ_two, hI, hI, sq]

/-- The lattice points at Euclidean distance less than `3^m` from `x`. -/
noncomputable def ballPoints (x : Vertex 2) (m : ℕ) : Finset (Vertex 2) :=
  (latticeBox x (3 ^ m)).filter fun a =>
    dist (latticeEuclideanEmbedding a) (latticeEuclideanEmbedding x) < (3 : ℝ) ^ m

theorem mem_ballPoints {x a : Vertex 2} {m : ℕ}
    (ha : dist (latticeEuclideanEmbedding a) (latticeEuclideanEmbedding x) < (3 : ℝ) ^ m) :
    a ∈ ballPoints x m := by
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, ha⟩
  have hc := (regDet_abs_coord_le a x i).trans_lt ha
  have hc' : |a i - x i| < ((3 ^ m : ℕ) : ℤ) := by
    have : ((|a i - x i| : ℤ) : ℝ) < (((3 ^ m : ℕ) : ℤ) : ℝ) := by
      push_cast
      simpa using hc
    exact_mod_cast this
  rw [abs_lt] at hc'
  obtain ⟨h1, h2⟩ := hc'
  rw [Finset.mem_Icc]
  exact ⟨by linarith, by linarith⟩

theorem card_ballPoints_le (x : Vertex 2) (m : ℕ) :
    ((ballPoints x m).card : ℝ) ≤ 9 * ((3 : ℝ) ^ m) ^ 2 := by
  have h1 : (ballPoints x m).card ≤ (2 * 3 ^ m + 1) ^ 2 :=
    (Finset.card_filter_le _ _).trans (card_latticeBox x _).le
  have h2 : ((ballPoints x m).card : ℝ) ≤ ((2 * 3 ^ m + 1) ^ 2 : ℕ) := by exact_mod_cast h1
  have h3 : (((2 * 3 ^ m + 1) ^ 2 : ℕ) : ℝ) ≤ 9 * ((3 : ℝ) ^ m) ^ 2 := by
    push_cast
    have : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  exact h2.trans h3

/-- The triples `(i, a, b)` of a coordinate and two points of `ballPoints x m`. -/
noncomputable def pairIndex (x : Vertex 2) (m : ℕ) : Finset (Fin 2 × Vertex 2 × Vertex 2) :=
  Finset.univ ×ˢ (ballPoints x m ×ˢ ballPoints x m)

theorem card_pairIndex_le (x : Vertex 2) (m : ℕ) :
    ((pairIndex x m).card : ℝ) ≤ 162 * ((3 : ℝ) ^ m) ^ 4 := by
  have hc : ((pairIndex x m).card : ℝ) = 2 * ((ballPoints x m).card : ℝ) ^ 2 := by
    rw [pairIndex, Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  rw [hc]
  have h := card_ballPoints_le x m
  have h0 : (0 : ℝ) ≤ (ballPoints x m).card := Nat.cast_nonneg _
  nlinarith [mul_le_mul h h h0 (by positivity)]

/-- Two points of `ballPoints x m` are at distance less than `2 · 3^m`, so that
`log (2 + |a - b|) ≤ (m + 2) log 3`. -/
theorem log_two_add_norm_le {x a b : Vertex 2} {m : ℕ} (ha : a ∈ ballPoints x m)
    (hb : b ∈ ballPoints x m) :
    Real.log (2 + ‖latticeEuclideanEmbedding a - latticeEuclideanEmbedding b‖) ≤
      ((m : ℝ) + 2) * Real.log 3 := by
  have ha' := (Finset.mem_filter.1 ha).2
  have hb' := (Finset.mem_filter.1 hb).2
  have hd : ‖latticeEuclideanEmbedding a - latticeEuclideanEmbedding b‖ < 2 * (3 : ℝ) ^ m := by
    rw [← dist_eq_norm]
    calc dist (latticeEuclideanEmbedding a) (latticeEuclideanEmbedding b)
        ≤ dist (latticeEuclideanEmbedding a) (latticeEuclideanEmbedding x) +
          dist (latticeEuclideanEmbedding b) (latticeEuclideanEmbedding x) :=
          dist_triangle_right _ _ _
      _ < 2 * (3 : ℝ) ^ m := by linarith
  have h3 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
  have hle : 2 + ‖latticeEuclideanEmbedding a - latticeEuclideanEmbedding b‖ ≤ (3 : ℝ) ^ (m + 2) := by
    rw [pow_add]
    nlinarith
  calc Real.log (2 + ‖latticeEuclideanEmbedding a - latticeEuclideanEmbedding b‖)
      ≤ Real.log ((3 : ℝ) ^ (m + 2)) := Real.log_le_log (by positivity) hle
    _ = ((m : ℝ) + 2) * Real.log 3 := by rw [Real.log_pow]; push_cast; ring

/-- `(m + 2) log 3 ≤ (1/α + 2 log 3) (3^m)^α` for `α > 0`. -/
theorem nat_add_two_mul_log_three_le {α : ℝ} (hα : 0 < α) (m : ℕ) :
    ((m : ℝ) + 2) * Real.log 3 ≤ (1 / α + 2 * Real.log 3) * ((3 : ℝ) ^ m) ^ α := by
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h3 : ((3 : ℝ) ^ m) ^ α = Real.exp (m * Real.log 3 * α) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, mul_comm]
  have hge : (m : ℝ) * Real.log 3 * α ≤ ((3 : ℝ) ^ m) ^ α := by
    rw [h3]
    linarith [Real.add_one_le_exp ((m : ℝ) * Real.log 3 * α)]
  have hone : (1 : ℝ) ≤ ((3 : ℝ) ^ m) ^ α :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) hα.le
  have hm : (m : ℝ) * Real.log 3 ≤ ((3 : ℝ) ^ m) ^ α / α := by
    rw [le_div_iff₀ hα]
    linarith
  calc ((m : ℝ) + 2) * Real.log 3 = (m : ℝ) * Real.log 3 + 2 * Real.log 3 := by ring
    _ ≤ ((3 : ℝ) ^ m) ^ α / α + 2 * Real.log 3 * ((3 : ℝ) ^ m) ^ α :=
        add_le_add hm (by nlinarith)
    _ = (1 / α + 2 * Real.log 3) * ((3 : ℝ) ^ m) ^ α := by ring

/-- `(3^m)^4 ≤ exp(16/(b γ²)) exp((b/2) (3^m)^γ)` for `b, γ > 0`. -/
theorem three_pow_four_le {b γ : ℝ} (hb : 0 < b) (hγ : 0 < γ) (m : ℕ) :
    ((3 : ℝ) ^ m) ^ 4 ≤ Real.exp (16 / (b * γ ^ 2)) * Real.exp (b / 2 * ((3 : ℝ) ^ m) ^ γ) := by
  set x : ℝ := (m : ℝ) * Real.log 3 with hx
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
  have h3 : ((3 : ℝ) ^ m) ^ γ = Real.exp (γ * x) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, hx]
    ring_nf
  have h4 : ((3 : ℝ) ^ m) ^ 4 = Real.exp (4 * x) := by
    calc ((3 : ℝ) ^ m) ^ 4 = Real.exp (Real.log (((3 : ℝ) ^ m) ^ 4)) :=
          (Real.exp_log (by positivity)).symm
      _ = Real.exp (4 * x) := by rw [Real.log_pow, Real.log_pow, hx]; push_cast; ring
  rw [h3, h4, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hγ.le hx0)
  set c := b * γ ^ 2 / 4 with hc
  have hc0 : 0 < c := by positivity
  have hkey' : 4 * x ≤ c * x ^ 2 + 4 / c := by
    have hsq : c * x ^ 2 + 4 / c - 4 * x = (c * x - 2) ^ 2 / c := by
      field_simp
      ring
    have : 0 ≤ (c * x - 2) ^ 2 / c := div_nonneg (sq_nonneg _) hc0.le
    linarith
  have h16 : 4 / c = 16 / (b * γ ^ 2) := by rw [hc]; field_simp; ring
  have hquad : c * x ^ 2 ≤ b / 2 * Real.exp (γ * x) := by
    have : c * x ^ 2 = b / 2 * ((γ * x) ^ 2 / 2) := by rw [hc]; ring
    rw [this]
    gcongr
    nlinarith [mul_nonneg hγ.le hx0]
  linarith

/-- The bad event at scale `3^m`: some corrector increment over a pair of `ballPoints x m` reaches
`(3^m)^α`. -/
def badEvent (Z : Fin 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ) (x : Vertex 2) (α : ℝ)
    (m : ℕ) : Set (Configuration 2) :=
  ⋃ j ∈ pairIndex x m, {ω | ((3 : ℝ) ^ m) ^ α ≤ Z j.1 j.2.1 j.2.2 ω}

/-- The indicator of the bad event. -/
noncomputable def badIndicator (Z : Fin 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ)
    (x : Vertex 2) (α : ℝ) (m : ℕ) : Configuration 2 → ℝ :=
  (badEvent Z x α m).indicator 1

theorem measurableSet_badEvent {Z : Fin 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ}
    (hZ : ∀ i a b, Measurable (Z i a b)) (x : Vertex 2) (α : ℝ) (m : ℕ) :
    MeasurableSet (badEvent Z x α m) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_le measurable_const (hZ _ _ _)

theorem setOf_one_le_badIndicator (Z : Fin 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ)
    (x : Vertex 2) (α : ℝ) (m : ℕ) :
    {ω | 1 ≤ badIndicator Z x α m ω} = badEvent Z x α m := by
  ext ω
  simp only [badIndicator, Set.mem_setOf_eq]
  by_cases hω : ω ∈ badEvent Z x α m
  · simp [hω]
  · simp [hω]

/-- The union bound for the bad event: if every increment variable on `pairIndex x m` is
`O_s(D (3^m)^{α/2})`, the bad event has probability at most
`324 (3^m)^4 exp(-(3^m)^{αs/2} / D^s)`. -/
theorem measure_badEvent_le {p : unitInterval}
    {Z : Fin 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ} {x : Vertex 2} {α s D : ℝ}
    (hs : 0 < s) (hD : 0 < D) {m : ℕ}
    (hO : ∀ j ∈ pairIndex x m, IsOsBond 2 p (Z j.1 j.2.1 j.2.2) s (D * ((3 : ℝ) ^ m) ^ (α / 2))) :
    latticeBondLaw 2 p (badEvent Z x α m) ≤
      ENNReal.ofReal (324 * ((3 : ℝ) ^ m) ^ 4 *
        Real.exp (-(((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s))) := by
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ m) ^ (α / 2) := by positivity
  have hθ : 0 < D * ((3 : ℝ) ^ m) ^ (α / 2) := mul_pos hD h3
  have hsplit : ((3 : ℝ) ^ m) ^ α = ((3 : ℝ) ^ m) ^ (α / 2) * ((3 : ℝ) ^ m) ^ (α / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  have hq : ((3 : ℝ) ^ m) ^ α / (D * ((3 : ℝ) ^ m) ^ (α / 2)) = ((3 : ℝ) ^ m) ^ (α / 2) / D := by
    rw [hsplit]
    field_simp
  have hts : (((3 : ℝ) ^ m) ^ (α / 2) / D) ^ s = ((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s := by
    rw [Real.div_rpow h3.le hD.le, ← Real.rpow_mul (by positivity)]
  have hterm : ∀ j ∈ pairIndex x m,
      latticeBondLaw 2 p {ω | ((3 : ℝ) ^ m) ^ α ≤ Z j.1 j.2.1 j.2.2 ω} ≤
        ENNReal.ofReal (2 * Real.exp (-(((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s))) := by
    intro j hj
    have hm := measure_le_le_of_isOsBond (t := ((3 : ℝ) ^ m) ^ α) hθ hs (by positivity) (hO j hj)
    rwa [hq, hts] at hm
  calc latticeBondLaw 2 p (badEvent Z x α m)
      ≤ ∑ j ∈ pairIndex x m, latticeBondLaw 2 p {ω | ((3 : ℝ) ^ m) ^ α ≤ Z j.1 j.2.1 j.2.2 ω} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ pairIndex x m,
          ENNReal.ofReal (2 * Real.exp (-(((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s))) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((pairIndex x m).card *
          (2 * Real.exp (-(((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc := card_pairIndex_le x m
        have he : 0 ≤ 2 * Real.exp (-(((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hc he]

/-- The tail of the bad event in the form of `isOsBond_triadicScale_of_tail`. -/
theorem measure_badEvent_le_exp {p : unitInterval}
    {Z : Fin 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ} {x : Vertex 2} {α s D : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hD : 0 < D) {m : ℕ}
    (hO : ∀ j ∈ pairIndex x m, IsOsBond 2 p (Z j.1 j.2.1 j.2.2) s (D * ((3 : ℝ) ^ m) ^ (α / 2))) :
    latticeBondLaw 2 p (badEvent Z x α m) ≤
      ENNReal.ofReal (324 * Real.exp (16 / (1 / D ^ s * (α / 2 * s) ^ 2)) *
        Real.exp (-(1 / D ^ s / 2 * ((3 : ℝ) ^ m) ^ (α / 2 * s)))) := by
  refine (measure_badEvent_le hs hD hO).trans (ENNReal.ofReal_le_ofReal ?_)
  have hb : 0 < 1 / D ^ s := by positivity
  have hγ : 0 < α / 2 * s := by positivity
  have h4 := three_pow_four_le hb hγ m
  have he : ((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s = 1 / D ^ s * ((3 : ℝ) ^ m) ^ (α / 2 * s) := by
    ring
  rw [he]
  calc 324 * ((3 : ℝ) ^ m) ^ 4 * Real.exp (-(1 / D ^ s * ((3 : ℝ) ^ m) ^ (α / 2 * s)))
      ≤ 324 * (Real.exp (16 / (1 / D ^ s * (α / 2 * s) ^ 2)) *
          Real.exp (1 / D ^ s / 2 * ((3 : ℝ) ^ m) ^ (α / 2 * s))) *
          Real.exp (-(1 / D ^ s * ((3 : ℝ) ^ m) ^ (α / 2 * s))) := by gcongr
    _ = 324 * Real.exp (16 / (1 / D ^ s * (α / 2 * s) ^ 2)) *
          (Real.exp (1 / D ^ s / 2 * ((3 : ℝ) ^ m) ^ (α / 2 * s)) *
            Real.exp (-(1 / D ^ s * ((3 : ℝ) ^ m) ^ (α / 2 * s)))) := by ring
    _ = 324 * Real.exp (16 / (1 / D ^ s * (α / 2 * s) ^ 2)) *
          Real.exp (-(1 / D ^ s / 2 * ((3 : ℝ) ^ m) ^ (α / 2 * s))) := by
        rw [← Real.exp_add]
        ring_nf

/-! ### Proposition 2.12 in dimension two -/

/-- **Dario–Gu, Proposition 2.12** in dimension two, from Dario's Theorem 1
(`DarioOptimalCorrectorTwo`) and the planar qualitative corrector input. -/
theorem correctorQuantitativeInputTwo_of_dario (hD : DarioOptimalCorrectorTwo)
    (hC : SupercriticalBondCorrectorInputTwo) : CorrectorQuantitativeInputTwo := by
  intro p hpc hp1 α hα
  obtain ⟨s, C₀, hs, hC₀, hZ⟩ := hD p hpc hp1
  choose Z hZm hZO hZae using fun (i : Fin 2) (a b : Vertex 2) => hZ (Pi.single i 1) a b
  set K₁ : ℝ := 1 / α + 2 * Real.log 3 with hK₁
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hK₁0 : 0 < K₁ := by positivity
  set D : ℝ := C₀ * Real.sqrt K₁ with hDdef
  have hD0 : 0 < D := mul_pos hC₀ (Real.sqrt_pos.2 hK₁0)
  set γ : ℝ := α / 2 * s with hγdef
  have hγ : 0 < γ := by positivity
  set A : ℝ := 324 * Real.exp (16 / (1 / D ^ s * γ ^ 2)) with hAdef
  have hA : 0 ≤ A := by positivity
  set cexp : ℝ := 1 / D ^ s / 2 with hcexp
  have ha : 0 < cexp := by positivity
  obtain ⟨θ₁, hθ₁, hT⟩ := isOsBond_triadicScale_of_tail (d := 2) (p := p)
    (C := ENNReal.ofReal A) ENNReal.ofReal_ne_top ha hγ
  set θ := max (max θ₁ (1 * 3 ^ (1 / γ)) * 4 ^ (1 / γ)) (2 * 3 ^ α) with hθdef
  have hθ0 : 0 < max θ₁ (1 * 3 ^ (1 / γ)) * 4 ^ (1 / γ) :=
    mul_pos (lt_of_lt_of_le hθ₁ (le_max_left _ _)) (by positivity)
  refine ⟨γ, θ, hγ, lt_of_lt_of_le hθ0 (le_max_left _ _), fun x => ?_⟩
  -- the increment variables on `pairIndex x m` are `O_s(D (3^m)^{α/2})`
  have hZO' : ∀ m : ℕ, ∀ j ∈ pairIndex x m,
      IsOsBond 2 p (Z j.1 j.2.1 j.2.2) s (D * ((3 : ℝ) ^ m) ^ (α / 2)) := by
    intro m j hj
    obtain ⟨i, a', b'⟩ := j
    have hj' := Finset.mem_product.1 (Finset.mem_product.1 hj).2
    have hpos : 0 < Real.log (2 + ‖latticeEuclideanEmbedding a' - latticeEuclideanEmbedding b'‖) :=
      Real.log_pos (by linarith [norm_nonneg (latticeEuclideanEmbedding a' -
        latticeEuclideanEmbedding b')])
    refine IsOsBond.mono_scale hs ?_ ?_ (hZm i a' b') (hZO i a' b')
    · rw [sum_abs_single, mul_one]
      exact mul_pos hC₀ (Real.sqrt_pos.2 hpos)
    · rw [sum_abs_single, mul_one, hDdef, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC₀.le
      have hlog := (log_two_add_norm_le hj'.1 hj'.2).trans (nat_add_two_mul_log_three_le hα m)
      have hsq : Real.sqrt (((3 : ℝ) ^ m) ^ α) = ((3 : ℝ) ^ m) ^ (α / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        ring_nf
      calc Real.sqrt (Real.log (2 + ‖latticeEuclideanEmbedding a' - latticeEuclideanEmbedding b'‖))
          ≤ Real.sqrt (K₁ * ((3 : ℝ) ^ m) ^ α) := Real.sqrt_le_sqrt hlog
        _ = Real.sqrt K₁ * ((3 : ℝ) ^ m) ^ (α / 2) := by
            rw [Real.sqrt_mul hK₁0.le, hsq]
  set X : ℕ → Configuration 2 → ℝ := badIndicator Z x α with hXdef
  have hXm : ∀ m, Measurable (X m) := fun m =>
    measurable_one.indicator (measurableSet_badEvent hZm x α m)
  have htail : ∀ m : ℕ, latticeBondLaw 2 p {ω | 1 ≤ X m ω} ≤
      ENNReal.ofReal A * ENNReal.ofReal (Real.exp (-cexp * ((3 : ℝ) ^ m) ^ γ)) := by
    intro m
    rw [hXdef, setOf_one_le_badIndicator, ← ENNReal.ofReal_mul hA, neg_mul]
    exact measure_badEvent_le_exp hα hs hD0 (hZO' m)
  obtain ⟨hMO, hMae⟩ := hT X hXm htail
  set M : Configuration 2 → ℝ := fun ω => max (triadicScale X ω) 1 with hMdef
  have hMm : Measurable M := (measurable_triadicScale hXm).max measurable_const
  refine ⟨M, hMm, fun ω => (zero_le_one.trans (le_max_right _ _)), ?_, ?_⟩
  · have h1 := IsOsBond.max hγ hθ₁ (by positivity) (measurable_triadicScale hXm) measurable_const
      hMO (isOsBond_const (d := 2) (p := p) one_pos hγ)
    exact IsOsBond.mono_scale hγ hθ0 (le_max_left _ _) hMm h1
  · have hZall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i : Fin 2) (a' b' : Vertex 2),
        ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ ℓ : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ →
          ∀ (hx : a' ∈ (uniqueInfiniteComponent h).supp)
            (hy : b' ∈ (uniqueInfiniteComponent h).supp),
            |(ℓ ⟨a', hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * a' j) -
              (ℓ ⟨b', hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * b' j)| ≤ Z i a' b' ω := by
      rw [ae_all_iff]; intro i
      rw [ae_all_iff]; intro a'
      rw [ae_all_iff]; intro b'
      exact hZae i a' b'
    filter_upwards [hMae, hZall, hC p hpc hp1] with ω hωM hωZ hωC
    intro h q ℓ hℓ r hr a b a' b' ha hb ha' hb' _
    have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hr1 (by norm_num : (1 : ℝ) < 3)
    -- no bad event at scale `3^{n+1}`
    have hgood : ω ∉ badEvent Z x α (n + 1) := by
      intro hbad
      have h1 : 1 ≤ X (n + 1) ω := by
        rw [hXdef, badIndicator, Set.indicator_of_mem hbad]
        simp
      have h2 := hωM (n + 1) h1
      have h3 : triadicScale X ω ≤ r := (le_max_left _ _).trans hr
      linarith
    have hsmall : ∀ (i : Fin 2) (c c' : uniqueInfiniteComponent h),
        ‖latticeEuclideanEmbedding c.val - latticeEuclideanEmbedding x‖ < r →
        ‖latticeEuclideanEmbedding c'.val - latticeEuclideanEmbedding x‖ < r →
        Z i c.val c'.val ω < ((3 : ℝ) ^ (n + 1)) ^ α := by
      intro i c c' hc hc'
      have hcm : c.val ∈ ballPoints x (n + 1) := mem_ballPoints (by rw [dist_eq_norm]; linarith)
      have hcm' : c'.val ∈ ballPoints x (n + 1) :=
        mem_ballPoints (by rw [dist_eq_norm]; linarith)
      by_contra hcon
      exact hgood (Set.mem_iUnion₂.2 ⟨(i, c.val, c'.val),
        Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨hcm, hcm'⟩⟩,
        not_lt.1 hcon⟩)
    obtain ⟨ℓ₀, ⟨hℓ₀, -⟩, -⟩ := (hωC h).1 (Pi.single 0 1) a
    obtain ⟨ℓ₁, ⟨hℓ₁, -⟩, -⟩ := (hωC h).1 (Pi.single 1 1) a
    have hscale : ((3 : ℝ) ^ (n + 1)) ^ α ≤ 3 ^ α * r ^ α := by
      rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num), mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn1 hα.le)
        (by positivity)
    have hpair : ∀ c c' : uniqueInfiniteComponent h,
        ‖latticeEuclideanEmbedding c.val - latticeEuclideanEmbedding x‖ < r →
        ‖latticeEuclideanEmbedding c'.val - latticeEuclideanEmbedding x‖ < r →
        |(ℓ c - ∑ i, q i * c.val i) - (ℓ c' - ∑ i, q i * c'.val i)| ≤
          (∑ i, |q i|) * (3 ^ α * r ^ α) := by
      intro c c' hc hc'
      rw [corrector_sub_eq (hωC h).1 hℓ hℓ₀ hℓ₁ c c']
      have h0 := (hωZ 0 c.val c'.val h ℓ₀ hℓ₀ c.2 c'.2).trans (hsmall 0 c c' hc hc').le
      have h1 := (hωZ 1 c.val c'.val h ℓ₁ hℓ₁ c.2 c'.2).trans (hsmall 1 c c' hc hc').le
      simp only [Subtype.coe_eta] at h0 h1
      calc _ ≤ |q 0 * ((ℓ₀ c - ∑ j, (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) j * c.val j) -
              (ℓ₀ c' - ∑ j, (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) j * c'.val j))| +
            |q 1 * ((ℓ₁ c - ∑ j, (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) j * c.val j) -
              (ℓ₁ c' - ∑ j, (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) j * c'.val j))| := abs_add_le _ _
        _ ≤ |q 0| * (3 ^ α * r ^ α) + |q 1| * (3 ^ α * r ^ α) := by
            rw [abs_mul, abs_mul]
            gcongr
            · exact h0.trans hscale
            · exact h1.trans hscale
        _ = (∑ i, |q i|) * (3 ^ α * r ^ α) := by rw [Fin.sum_univ_two]; ring
    have hab := hpair a b ha hb
    have hab' := hpair a' b' ha' hb'
    have hθ2 : 2 * 3 ^ α ≤ θ := le_max_right _ _
    have hq0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hr0 : 0 ≤ r ^ α := Real.rpow_nonneg (zero_le_one.trans hr1) _
    calc _ ≤ (∑ i, |q i|) * (3 ^ α * r ^ α) + (∑ i, |q i|) * (3 ^ α * r ^ α) := add_le_add hab hab'
      _ = (2 * 3 ^ α) * (∑ i, |q i|) * r ^ α := by ring
      _ ≤ θ * (∑ i, |q i|) * r ^ α :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθ2 hq0) hr0

end Rigidity.Corrector

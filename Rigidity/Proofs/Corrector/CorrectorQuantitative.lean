import Rigidity.Proofs.Corrector.PlanarCorrectorQuantitative
import Rigidity.Proofs.Poincare.DarioStepTwoHolds

/-!
# The quantitative sublinearity of the corrector in every dimension (Dario–Gu, Proposition 2.12)

Dario–Gu, Proposition 2.12, asserts that for every `α > 0` there are `s, C` and, for every
`y ∈ ℤ^d`, a minimal scale `M_corr,α(y) ≤ O_s(C)` such that
`osc_{𝒞_∞ ∩ B_r(y)} χ_p ≤ C |p| r^α` for every `r ≥ M_corr,α(y)` and every `p`. The proof printed
there combines Theorem 1 of Dario (*Optimal corrector estimates on percolation clusters*,
Ann. Appl. Probab. 2021, arXiv:1805.00902), which in dimension `d ≥ 3` reads
`|χ_p(x) - χ_p(y)| 1_{x, y ∈ 𝒞_∞} ≤ O_s(C |p|)`, with Lemma 1.6 applied to the sequence
`X_n = 3^{-αn} sup_{x ∈ B_{3^n}(y)} |χ_p(x) - χ_p(y)| 1_{x, y ∈ 𝒞_∞}`.

This file states Dario's Theorem 1 in dimension `d ≥ 3` as `DarioOptimalCorrectorThree`, proved
in `darioOptimalCorrectorThree_holds`, and proves the corrector input `CorrectorQuantitativeInput`
in every dimension from it (`correctorQuantitativeInput_of_dario`) and the qualitative corrector input `SupercriticalBondCorrectorInput`; in
dimension two it is `Rigidity.Poincare.correctorQuantitativeInputTwo_holds`. The argument is the
one of `PlanarCorrectorQuantitative.lean` in dimension `d`:

* the pairs are taken in the lattice ball `B_{3^n}(x)` around the centre `x` of the statement;
* the supremum over the `O(3^{2dn})` pairs is controlled by a union bound on the Chebyshev tails,
  in place of the sum of `2d/α`-th powers of the printed proof; the minimal scale is the triadic
  scale of Lemma 1.6 of the bad events `{∃ pair: |χ(x) - χ(x')| ≥ 3^{αn}}`, at least `1`;
* the bound for every slope `q` follows from the `d` coordinate slopes: by the uniqueness of
  corrected planes (first clause of the qualitative input) the corrector is linear in the slope
  modulo constants (Dario–Gu, §2.3.1).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal

variable {d : ℕ}

/-- **Dario, Theorem 1** (optimal `L^∞` estimates for the first-order correctors), in dimension
`d ≥ 3`: there are `s > 0` and `C < ∞` such that for all `x, y ∈ ℤ^d` and every slope `q`,
`|χ_q(x) - χ_q(y)| 1_{x, y ∈ 𝒞_∞} ≤ O_s(C |q|)`, where `χ_q = ℓ_q - q·x` for a corrected plane
`ℓ_q` of slope `q`. The random variable is dominated by a measurable `Z ≤ O_s(·)`. -/
def DarioOptimalCorrectorThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (q : Fin d → ℝ) (x y : Vertex d),
      ∃ Z : Configuration d → ℝ, Measurable Z ∧ IsOsBond d p Z s (C * ∑ i, |q i|) ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          ∀ ℓ : uniqueInfiniteComponent h → ℝ,
            IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
          ∀ (hx : x ∈ (uniqueInfiniteComponent h).supp) (hy : y ∈ (uniqueInfiniteComponent h).supp),
            |(ℓ ⟨x, hx⟩ - ∑ i, q i * x i) - (ℓ ⟨y, hy⟩ - ∑ i, q i * y i)| ≤ Z ω

/-! ### Linearity of the corrector in the slope -/

/-- By the uniqueness of normalized corrected planes, the increments of a corrected plane of slope
`q` are the combination of those of the corrected planes of the coordinate slopes. -/
theorem correctedPlane_sub_eq {ω : Configuration d} {C : OpenComponent ω}
    (hC : ∀ (q : Fin d → ℝ) (o : C), ∃! u : C → ℝ, IsCorrectedPlane C q u ∧ u o = 0)
    {q : Fin d → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) {L : Fin d → C → ℝ}
    (hL : ∀ i, IsCorrectedPlane C (Pi.single i 1) (L i)) (a b : C) :
    ℓ a - ℓ b = ∑ i, q i * (L i a - L i b) := by
  have hsum : ∀ S : Finset (Fin d), IsCorrectedPlane C
      (∑ i ∈ S, q i • (Pi.single i 1 : Fin d → ℝ)) (∑ i ∈ S, q i • L i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact isCorrectedPlane_const C 0
    | insert i S hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        exact isCorrectedPlane_add C (isCorrectedPlane_smul C (hL i) (q i)) ih
  have hq : q - ∑ i, q i • (Pi.single i 1 : Fin d → ℝ) = 0 := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw := isCorrectedPlane_sub C hℓ (hsum Finset.univ)
  rw [hq] at hw
  set w := ℓ - ∑ i, q i • L i with hwdef
  have hw' : IsCorrectedPlane C 0 (w - fun _ => w b) := by
    simpa only [sub_zero] using isCorrectedPlane_sub C hw (isCorrectedPlane_const C (w b))
  have heq := (hC 0 b).unique ⟨hw', by simp⟩ ⟨isCorrectedPlane_const C 0, rfl⟩
  have ha := congrFun heq a
  simp only [hwdef, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at ha
  have e : ∑ i, q i * (L i a - L i b) = ∑ i, q i * L i a - ∑ i, q i * L i b := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  linarith

theorem sum_single_mul (i : Fin d) (v : Vertex d) :
    ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * (v j : ℝ) = v i := by
  simp [Pi.single_apply]

theorem sum_abs_single (i : Fin d) : ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j| = 1 := by
  simp [Pi.single_apply, apply_ite]

/-- The increments of the corrector `χ_q = ℓ - q·x` are the combination of those of the coordinate
correctors `L i - x_i`. -/
theorem corrector_sub_eq {ω : Configuration d} {C : OpenComponent ω}
    (hC : ∀ (q : Fin d → ℝ) (o : C), ∃! u : C → ℝ, IsCorrectedPlane C q u ∧ u o = 0)
    {q : Fin d → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) {L : Fin d → C → ℝ}
    (hL : ∀ i, IsCorrectedPlane C (Pi.single i 1) (L i)) (a b : C) :
    (ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i) =
      ∑ i, q i * ((L i a - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * a.val j) -
        (L i b - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * b.val j)) := by
  have h := correctedPlane_sub_eq hC hℓ hL a b
  simp only [sum_single_mul]
  have e : ∑ i, q i * ((L i a - (a.val i : ℝ)) - (L i b - (b.val i : ℝ))) =
      ∑ i, q i * (L i a - L i b) - (∑ i, q i * (a.val i : ℝ) - ∑ i, q i * (b.val i : ℝ)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, ← h]
  ring

/-! ### Lattice balls and bad events -/

/-- The lattice box `x + [-N, N]^d`. -/
noncomputable def latticeBox (x : Vertex d) (N : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc (x i - N) (x i + N)

theorem card_latticeBox (x : Vertex d) (N : ℕ) : (latticeBox x N).card = (2 * N + 1) ^ d := by
  have hI : ∀ i : Fin d, (Finset.Icc (x i - N) (x i + N)).card = 2 * N + 1 := by
    intro i
    rw [Int.card_Icc, show x i + (N : ℤ) + 1 - (x i - N) = ((2 * N + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
  rw [latticeBox, Fintype.card_piFinset, Finset.prod_congr rfl fun i _ => hI i, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The lattice points at Euclidean distance less than `3^m` from `x`. -/
noncomputable def ballPoints (x : Vertex d) (m : ℕ) : Finset (Vertex d) :=
  (latticeBox x (3 ^ m)).filter fun a =>
    dist (latticeEuclideanEmbedding a) (latticeEuclideanEmbedding x) < (3 : ℝ) ^ m

theorem mem_ballPoints {x a : Vertex d} {m : ℕ}
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

theorem card_ballPoints_le (x : Vertex d) (m : ℕ) :
    ((ballPoints x m).card : ℝ) ≤ 3 ^ d * ((3 : ℝ) ^ m) ^ d := by
  have h1 : (ballPoints x m).card ≤ (2 * 3 ^ m + 1) ^ d :=
    (Finset.card_filter_le _ _).trans (card_latticeBox x _).le
  have h2 : ((ballPoints x m).card : ℝ) ≤ ((2 * 3 ^ m + 1) ^ d : ℕ) := by exact_mod_cast h1
  have h3 : (((2 * 3 ^ m + 1) ^ d : ℕ) : ℝ) ≤ 3 ^ d * ((3 : ℝ) ^ m) ^ d := by
    push_cast
    rw [← mul_pow]
    have : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  exact h2.trans h3

/-- The triples `(i, a, b)` of a coordinate and two points of `ballPoints x m`. -/
noncomputable def pairIndex (x : Vertex d) (m : ℕ) : Finset (Fin d × Vertex d × Vertex d) :=
  Finset.univ ×ˢ (ballPoints x m ×ˢ ballPoints x m)

theorem card_pairIndex_le (x : Vertex d) (m : ℕ) :
    ((pairIndex x m).card : ℝ) ≤ d * 9 ^ d * ((3 : ℝ) ^ m) ^ (2 * d) := by
  have hc : ((pairIndex x m).card : ℝ) = d * ((ballPoints x m).card : ℝ) ^ 2 := by
    rw [pairIndex, Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  rw [hc]
  have h := card_ballPoints_le x m
  have h0 : (0 : ℝ) ≤ (ballPoints x m).card := Nat.cast_nonneg _
  have hsq : ((ballPoints x m).card : ℝ) ^ 2 ≤ (3 ^ d * ((3 : ℝ) ^ m) ^ d) ^ 2 :=
    pow_le_pow_left₀ h0 h 2
  have h9 : (9 : ℝ) ^ d = (3 ^ d) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e : (3 ^ d * ((3 : ℝ) ^ m) ^ d) ^ 2 = 9 ^ d * ((3 : ℝ) ^ m) ^ (2 * d) := by
    rw [h9, mul_pow, ← pow_mul ((3 : ℝ) ^ m) d 2, mul_comm d 2]
  rw [e] at hsq
  calc (d : ℝ) * ((ballPoints x m).card : ℝ) ^ 2 ≤ d * (9 ^ d * ((3 : ℝ) ^ m) ^ (2 * d)) :=
        mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = d * 9 ^ d * ((3 : ℝ) ^ m) ^ (2 * d) := by ring

/-- `(3^m)^k ≤ exp(k²/(b γ²)) exp((b/2) (3^m)^γ)` for `b, γ > 0`. -/
theorem three_pow_le {b γ : ℝ} (hb : 0 < b) (hγ : 0 < γ) (k m : ℕ) :
    ((3 : ℝ) ^ m) ^ k ≤
      Real.exp ((k : ℝ) ^ 2 / (b * γ ^ 2)) * Real.exp (b / 2 * ((3 : ℝ) ^ m) ^ γ) := by
  set x : ℝ := (m : ℝ) * Real.log 3 with hx
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
  have h3 : ((3 : ℝ) ^ m) ^ γ = Real.exp (γ * x) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, hx]
    ring_nf
  have h4 : ((3 : ℝ) ^ m) ^ k = Real.exp (k * x) := by
    calc ((3 : ℝ) ^ m) ^ k = Real.exp (Real.log (((3 : ℝ) ^ m) ^ k)) :=
          (Real.exp_log (by positivity)).symm
      _ = Real.exp (k * x) := by rw [Real.log_pow, Real.log_pow, hx]
  rw [h3, h4, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hγ.le hx0)
  set c := b * γ ^ 2 / 4 with hc
  have hc0 : 0 < c := by positivity
  have hkey' : (k : ℝ) * x ≤ c * x ^ 2 + (k : ℝ) ^ 2 / (4 * c) := by
    have hsq : c * x ^ 2 + (k : ℝ) ^ 2 / (4 * c) - k * x = (2 * c * x - k) ^ 2 / (4 * c) := by
      field_simp
      ring
    have : 0 ≤ (2 * c * x - k) ^ 2 / (4 * c) := div_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hk : (k : ℝ) ^ 2 / (4 * c) = (k : ℝ) ^ 2 / (b * γ ^ 2) := by
    rw [hc]
    congr 1
    ring
  have hquad : c * x ^ 2 ≤ b / 2 * Real.exp (γ * x) := by
    have : c * x ^ 2 = b / 2 * ((γ * x) ^ 2 / 2) := by rw [hc]; ring
    rw [this]
    gcongr
    nlinarith [mul_nonneg hγ.le hx0]
  linarith

/-- The bad event at scale `3^m`: some corrector increment over a pair of `ballPoints x m` reaches
`(3^m)^α`. -/
def badEvent (Z : Fin d → Vertex d → Vertex d → Configuration d → ℝ) (x : Vertex d) (α : ℝ)
    (m : ℕ) : Set (Configuration d) :=
  ⋃ j ∈ pairIndex x m, {ω | ((3 : ℝ) ^ m) ^ α ≤ Z j.1 j.2.1 j.2.2 ω}

/-- The indicator of the bad event. -/
noncomputable def badIndicator (Z : Fin d → Vertex d → Vertex d → Configuration d → ℝ)
    (x : Vertex d) (α : ℝ) (m : ℕ) : Configuration d → ℝ :=
  (badEvent Z x α m).indicator 1

theorem measurableSet_badEvent {Z : Fin d → Vertex d → Vertex d → Configuration d → ℝ}
    (hZ : ∀ i a b, Measurable (Z i a b)) (x : Vertex d) (α : ℝ) (m : ℕ) :
    MeasurableSet (badEvent Z x α m) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_le measurable_const (hZ _ _ _)

theorem setOf_one_le_badIndicator (Z : Fin d → Vertex d → Vertex d → Configuration d → ℝ)
    (x : Vertex d) (α : ℝ) (m : ℕ) :
    {ω | 1 ≤ badIndicator Z x α m ω} = badEvent Z x α m := by
  ext ω
  simp only [badIndicator, Set.mem_setOf_eq]
  by_cases hω : ω ∈ badEvent Z x α m
  · simp [hω]
  · simp [hω]

/-- The union bound for the bad event: if every increment variable on `pairIndex x m` is
`O_s(D (3^m)^{α/2})`, the bad event has probability at most
`2 d 9^d (3^m)^{2d} exp(-(3^m)^{αs/2} / D^s)`. -/
theorem measure_badEvent_le [NeZero d] {p : unitInterval}
    {Z : Fin d → Vertex d → Vertex d → Configuration d → ℝ} {x : Vertex d} {α s D : ℝ}
    (hs : 0 < s) (hD : 0 < D) {m : ℕ}
    (hO : ∀ j ∈ pairIndex x m, IsOsBond d p (Z j.1 j.2.1 j.2.2) s (D * ((3 : ℝ) ^ m) ^ (α / 2))) :
    latticeBondLaw d p (badEvent Z x α m) ≤
      ENNReal.ofReal (2 * d * 9 ^ d * ((3 : ℝ) ^ m) ^ (2 * d) *
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
      latticeBondLaw d p {ω | ((3 : ℝ) ^ m) ^ α ≤ Z j.1 j.2.1 j.2.2 ω} ≤
        ENNReal.ofReal (2 * Real.exp (-(((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s))) := by
    intro j hj
    have hm := measure_le_le_of_isOsBond (t := ((3 : ℝ) ^ m) ^ α) hθ hs (by positivity) (hO j hj)
    rwa [hq, hts] at hm
  calc latticeBondLaw d p (badEvent Z x α m)
      ≤ ∑ j ∈ pairIndex x m, latticeBondLaw d p {ω | ((3 : ℝ) ^ m) ^ α ≤ Z j.1 j.2.1 j.2.2 ω} :=
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
theorem measure_badEvent_le_exp [NeZero d] {p : unitInterval}
    {Z : Fin d → Vertex d → Vertex d → Configuration d → ℝ} {x : Vertex d} {α s D : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hD : 0 < D) {m : ℕ}
    (hO : ∀ j ∈ pairIndex x m, IsOsBond d p (Z j.1 j.2.1 j.2.2) s (D * ((3 : ℝ) ^ m) ^ (α / 2))) :
    latticeBondLaw d p (badEvent Z x α m) ≤
      ENNReal.ofReal (2 * d * 9 ^ d *
        Real.exp (((2 * d : ℕ) : ℝ) ^ 2 / (1 / D ^ s * (α / 2 * s) ^ 2)) *
        Real.exp (-(1 / D ^ s / 2 * ((3 : ℝ) ^ m) ^ (α / 2 * s)))) := by
  refine (measure_badEvent_le hs hD hO).trans (ENNReal.ofReal_le_ofReal ?_)
  have hb : 0 < 1 / D ^ s := by positivity
  have hγ : 0 < α / 2 * s := by positivity
  have h4 := three_pow_le hb hγ (2 * d) m
  have he : ((3 : ℝ) ^ m) ^ (α / 2 * s) / D ^ s = 1 / D ^ s * ((3 : ℝ) ^ m) ^ (α / 2 * s) := by
    ring
  rw [he]
  have hK : (0 : ℝ) ≤ 2 * d * 9 ^ d := by positivity
  calc 2 * d * 9 ^ d * ((3 : ℝ) ^ m) ^ (2 * d) *
        Real.exp (-(1 / D ^ s * ((3 : ℝ) ^ m) ^ (α / 2 * s)))
      ≤ 2 * d * 9 ^ d * (Real.exp (((2 * d : ℕ) : ℝ) ^ 2 / (1 / D ^ s * (α / 2 * s) ^ 2)) *
          Real.exp (1 / D ^ s / 2 * ((3 : ℝ) ^ m) ^ (α / 2 * s))) *
          Real.exp (-(1 / D ^ s * ((3 : ℝ) ^ m) ^ (α / 2 * s))) := by gcongr
    _ = 2 * d * 9 ^ d * Real.exp (((2 * d : ℕ) : ℝ) ^ 2 / (1 / D ^ s * (α / 2 * s) ^ 2)) *
          (Real.exp (1 / D ^ s / 2 * ((3 : ℝ) ^ m) ^ (α / 2 * s)) *
            Real.exp (-(1 / D ^ s * ((3 : ℝ) ^ m) ^ (α / 2 * s)))) := by ring
    _ = 2 * d * 9 ^ d * Real.exp (((2 * d : ℕ) : ℝ) ^ 2 / (1 / D ^ s * (α / 2 * s) ^ 2)) *
          Real.exp (-(1 / D ^ s / 2 * ((3 : ℝ) ^ m) ^ (α / 2 * s))) := by
        rw [← Real.exp_add]
        ring_nf

/-! ### Proposition 2.12 in every dimension -/

/-- **Dario–Gu, Proposition 2.12**, in every dimension `d ≥ 2`, from Dario's Theorem 1 in
dimension `d ≥ 3` (`DarioOptimalCorrectorThree`) and the qualitative corrector input; in
dimension two it is `Rigidity.Poincare.correctorQuantitativeInputTwo_holds`. -/
theorem correctorQuantitativeInput_of_dario (hD : DarioOptimalCorrectorThree)
    (hC : LatticeProb.External.SupercriticalBondCorrectorInput) : CorrectorQuantitativeInput := by
  intro d _ hd p hpc hp1 α hα
  rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | hd3
  · exact Rigidity.Poincare.correctorQuantitativeInputTwo_holds p hpc hp1 α hα
  obtain ⟨s, C₀, hs, hC₀, hZ⟩ := hD d hd3 p hpc hp1
  choose Z hZm hZO hZae using fun (i : Fin d) (a b : Vertex d) => hZ (Pi.single i 1) a b
  set D : ℝ := C₀ with hDdef
  have hD0 : 0 < D := hC₀
  set γ : ℝ := α / 2 * s with hγdef
  have hγ : 0 < γ := by positivity
  set A : ℝ := 2 * d * 9 ^ d * Real.exp (((2 * d : ℕ) : ℝ) ^ 2 / (1 / D ^ s * γ ^ 2)) with hAdef
  have hA : 0 ≤ A := by positivity
  set cexp : ℝ := 1 / D ^ s / 2 with hcexp
  have ha : 0 < cexp := by positivity
  obtain ⟨θ₁, hθ₁, hT⟩ := isOsBond_triadicScale_of_tail (d := d) (p := p)
    (C := ENNReal.ofReal A) ENNReal.ofReal_ne_top ha hγ
  set θ := max (max θ₁ (1 * 3 ^ (1 / γ)) * 4 ^ (1 / γ)) (2 * 3 ^ α) with hθdef
  have hθ0 : 0 < max θ₁ (1 * 3 ^ (1 / γ)) * 4 ^ (1 / γ) :=
    mul_pos (lt_of_lt_of_le hθ₁ (le_max_left _ _)) (by positivity)
  refine ⟨γ, θ, hγ, lt_of_lt_of_le hθ0 (le_max_left _ _), fun x => ?_⟩
  -- the increment variables on `pairIndex x m` are `O_s(D (3^m)^{α/2})`
  have hZO' : ∀ m : ℕ, ∀ j ∈ pairIndex x m,
      IsOsBond d p (Z j.1 j.2.1 j.2.2) s (D * ((3 : ℝ) ^ m) ^ (α / 2)) := by
    intro m j _
    obtain ⟨i, a', b'⟩ := j
    refine IsOsBond.mono_scale hs ?_ ?_ (hZm i a' b') (hZO i a' b')
    · rw [sum_abs_single, mul_one]
      exact hC₀
    · rw [sum_abs_single, mul_one, hDdef]
      exact le_mul_of_one_le_right hC₀.le
        (Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity))
  set X : ℕ → Configuration d → ℝ := badIndicator Z x α with hXdef
  have hXm : ∀ m, Measurable (X m) := fun m =>
    measurable_one.indicator (measurableSet_badEvent hZm x α m)
  have htail : ∀ m : ℕ, latticeBondLaw d p {ω | 1 ≤ X m ω} ≤
      ENNReal.ofReal A * ENNReal.ofReal (Real.exp (-cexp * ((3 : ℝ) ^ m) ^ γ)) := by
    intro m
    rw [hXdef, setOf_one_le_badIndicator, ← ENNReal.ofReal_mul hA, neg_mul]
    exact measure_badEvent_le_exp hα hs hD0 (hZO' m)
  obtain ⟨hMO, hMae⟩ := hT X hXm htail
  set M : Configuration d → ℝ := fun ω => max (triadicScale X ω) 1 with hMdef
  have hMm : Measurable M := (measurable_triadicScale hXm).max measurable_const
  refine ⟨M, hMm, fun ω => (zero_le_one.trans (le_max_right _ _)), ?_, ?_⟩
  · have h1 := IsOsBond.max hγ hθ₁ (by positivity) (measurable_triadicScale hXm) measurable_const
      hMO (isOsBond_const (d := d) (p := p) one_pos hγ)
    exact IsOsBond.mono_scale hγ hθ0 (le_max_left _ _) hMm h1
  · have hZall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i : Fin d) (a' b' : Vertex d),
        ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ ℓ : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ →
          ∀ (hx : a' ∈ (uniqueInfiniteComponent h).supp)
            (hy : b' ∈ (uniqueInfiniteComponent h).supp),
            |(ℓ ⟨a', hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * a' j) -
              (ℓ ⟨b', hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * b' j)| ≤ Z i a' b' ω := by
      rw [ae_all_iff]; intro i
      rw [ae_all_iff]; intro a'
      rw [ae_all_iff]; intro b'
      exact hZae i a' b'
    filter_upwards [hMae, hZall, hC d hd p hpc hp1] with ω hωM hωZ hωC
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
    have hsmall : ∀ (i : Fin d) (c c' : uniqueInfiniteComponent h),
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
    choose L hL using fun i : Fin d => ((hωC h).1 (Pi.single i 1) a).exists
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
      rw [corrector_sub_eq (hωC h).1 hℓ (fun i => (hL i).1) c c', Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have hi := (hωZ i c.val c'.val h (L i) (hL i).1 c.2 c'.2).trans (hsmall i c c' hc hc').le
      simp only [Subtype.coe_eta] at hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hi.trans hscale) (abs_nonneg _)
    have hab := hpair a b ha hb
    have hab' := hpair a' b' ha' hb'
    have hθ2 : 2 * 3 ^ α ≤ θ := le_max_right _ _
    have hq0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hr0 : 0 ≤ r ^ α := Real.rpow_nonneg (zero_le_one.trans hr1) _
    calc _ ≤ (∑ i, |q i|) * (3 ^ α * r ^ α) + (∑ i, |q i|) * (3 ^ α * r ^ α) := add_le_add hab hab'
      _ = (2 * 3 ^ α) * (∑ i, |q i|) * r ^ α := by ring
      _ ≤ θ * (∑ i, |q i|) * r ^ α :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθ2 hq0) hr0

end Rigidity.Corrector.GeneralDim

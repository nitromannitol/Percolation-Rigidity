import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.GeomSum
import Rigidity.Proofs.Regularity.BallExcess

/-!
# The iteration in the proof of Armstrong–Dario Lemma 7.2 along a geometric sequence of radii

Armstrong and Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(arXiv:1609.09431v2), Lemma 7.2, transfer the excess decay of `ā`-harmonic functions to a function
`u` which is close to `ā`-harmonic functions on every ball `B_r` of a range of radii. Its proof for
the order `k` iterates an excess decay estimate one degree higher, for `D_{k+1}`, along radii
`θ^n ρ₀`, and then recovers `D_k` from `D_{k+1}` by summing the top-degree parts of the best
approximating polynomials of degree `k + 1` over the scales (Step 3 of the proof for `k = 0`; for
general `k` the paper refers to Step 3 of the proof of Lemma 2.4 of Armstrong–Kuusi–Mourrat,
*Mesoscopic higher regularity and subadditivity in elliptic homogenization*). Here the slope
`|∇ w|` of the paper is replaced by the excess of `w` over the polynomials of lower degree, which
scales like the `(k + 1)`-th power of the radius by `PolynomialComparison`.

The main result, `ballExcess_geometric_le`, states: if `u` is within `(θ^i ρ₀) ^ (1 - α) Γ` of the
harmonic functions on the balls of radii `θ^i ρ₀`, `i < n`, then
`D_k(θ^n ρ₀) ≤ K₁ θ^{n (k+1)} D_k(ρ₀) + K₂ (θ^n ρ₀) ^ (1 - α) Γ` with constants depending only on
the constants of the hypotheses and on `θ`, which is any number in `(0, 1/2]` with `CH θ ≤ 1/2`.
-/

namespace Rigidity.Proofs.Regularity

open Finset

/-- The sum of a sequence obeying the halving recurrence `T (i + 1) ≤ T i / 2 + f i`. -/
theorem sum_range_le_of_le_half_add {T f : ℕ → ℝ} {n : ℕ} (hTn : 0 ≤ T n)
    (h : ∀ i < n, T (i + 1) ≤ T i / 2 + f i) :
    ∑ i ∈ range (n + 1), T i ≤ 2 * T 0 + 2 * ∑ i ∈ range n, f i := by
  have h1 : ∑ i ∈ range n, T (i + 1) ≤ ∑ i ∈ range n, (T i / 2 + f i) :=
    sum_le_sum fun i hi => h i (mem_range.1 hi)
  rw [sum_add_distrib, ← sum_div] at h1
  have h2 := sum_range_succ' T n
  have h3 := sum_range_succ T n
  linarith

/-- A reflected geometric sum. -/
theorem sum_range_pow_sub_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ i ∈ range n, q ^ (n - i) ≤ 1 / (1 - q) := by
  have h1 : ∑ i ∈ range n, q ^ (n - i) ≤ ∑ i ∈ range (n + 1), q ^ (n - i) :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 n.le_succ)
      fun _ _ _ => pow_nonneg hq0 _
  have h2 : ∑ i ∈ range (n + 1), q ^ (n - i) = ∑ i ∈ range (n + 1), q ^ i := by
    have := sum_range_reflect (fun i => q ^ i) (n + 1)
    simpa using this
  have h3 : ∑ i ∈ range (n + 1), q ^ i ≤ q ^ 0 / (1 - q) := by
    rw [range_eq_Ico]
    exact geom_sum_Ico_le_of_lt_one hq0 hq1
  rw [pow_zero] at h3
  linarith

/-- Negative powers along a geometric sequence of radii. -/
theorem rpow_neg_geometric {θ ρ₀ β : ℝ} (hθ : 0 < θ) (hρ₀ : 0 < ρ₀) {i n : ℕ} (hin : i ≤ n) :
    (θ ^ i * ρ₀) ^ (-β) = (θ ^ β) ^ (n - i) * (θ ^ n * ρ₀) ^ (-β) := by
  have hsplit : θ ^ n * ρ₀ = θ ^ (n - i) * (θ ^ i * ρ₀) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hin]
  have h1 : (θ ^ n * ρ₀) ^ (-β) = (θ ^ (n - i)) ^ (-β) * (θ ^ i * ρ₀) ^ (-β) := by
    rw [hsplit, Real.mul_rpow (pow_nonneg hθ.le _) (by positivity)]
  have h2 : (θ ^ (n - i)) ^ (-β) = ((θ ^ β) ^ (n - i))⁻¹ := by
    rw [Real.rpow_neg (pow_nonneg hθ.le _), Real.rpow_pow_comm hθ.le]
  rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Real.rpow_pos_of_pos hθ _).ne'),
    one_mul]

/-- The first constant of `ballExcess_geometric_le`. -/
noncomputable def geometricConstOne (CV CP γ θ : ℝ) (j : ℕ) : ℝ :=
  2 * (1 + CP + CP * CV * θ⁻¹ ^ γ / θ ^ j) + 2 * CP

/-- The second constant of `ballExcess_geometric_le`. -/
noncomputable def geometricConstTwo (CV CP CH γ α θ : ℝ) (j : ℕ) : ℝ :=
  2 * (1 + CP + CP * CV * θ⁻¹ ^ γ / θ ^ j) * ((CV * θ⁻¹ ^ γ + CH * θ ^ (j + 1)) / θ ^ j) /
    (1 - θ ^ ((j : ℝ) + α - 1))

variable {F : Type*} [AddCommGroup F] (N : ℝ → AddGroupSeminorm F)

/-- From `∀ η > 0, a ≤ b + c η` with `c ≥ 0`, deduce `a ≤ b`. -/
theorem le_of_forall_pos_le_add_mul {a b c : ℝ} (hc : 0 ≤ c) (h : ∀ η : ℝ, 0 < η → a ≤ b + c * η) :
    a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  have hη : 0 < (a - b) / (2 * (c + 1)) := div_pos (by linarith) (by linarith)
  have h1 := h _ hη
  have h2 : c * ((a - b) / (2 * (c + 1))) < a - b := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **Halving step.** Along the radii `θ^i ρ₀`, the normalized excess
`T i = D(θ^i ρ₀) / (θ^i ρ₀) ^ j` over `P` satisfies `T (i + 1) ≤ T i / 2 + B Γ (θ^i ρ₀) ^ (1 - α - j)`
when `u` is within `(θ^i ρ₀) ^ (1 - α) Γ` of `Abar (θ^i ρ₀)`. -/
theorem ballExcess_halving_step (P : AddSubgroup F) {Abar : ℝ → Set F} {j : ℕ}
    {X R CV CH γ α θ Γ ρ₀ : ℝ} (hX0 : 0 < X) (hCV : 0 ≤ CV) (hCH : 0 ≤ CH)
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hCHθ : CH * θ ≤ 1 / 2)
    (hmono : RadiusMonotone N X R CV γ) (hreg : HarmonicRegularity N Abar P j X R CH)
    {i : ℕ} (hρR : θ ^ i * ρ₀ ≤ R) (hXi : X ≤ θ ^ (i + 1) * ρ₀)
    (hne : (Abar (θ ^ i * ρ₀)).Nonempty) (u : F)
    (happ : ballDist N (Abar (θ ^ i * ρ₀)) (θ ^ i * ρ₀) u ≤ (θ ^ i * ρ₀) ^ (1 - α) * Γ) :
    ballExcess N P (θ ^ (i + 1) * ρ₀) u / (θ ^ (i + 1) * ρ₀) ^ j ≤
      ballExcess N P (θ ^ i * ρ₀) u / (θ ^ i * ρ₀) ^ j / 2 +
        (CV * θ⁻¹ ^ γ + CH * θ ^ (j + 1)) / θ ^ j * Γ * (θ ^ i * ρ₀) ^ (1 - α - j) := by
  set r := θ ^ i * ρ₀ with hr
  have hs : θ ^ (i + 1) * ρ₀ = θ * r := by rw [hr, pow_succ]; ring
  rw [hs] at hXi ⊢
  have hs0 : 0 < θ * r := hX0.trans_le hXi
  have hr0 : 0 < r := pos_of_mul_pos_right hs0 hθ0.le
  have hsr : θ * r ≤ r / 2 := by nlinarith
  have hstep := ballExcess_le_of_harmonicRegularity N P hCV hCH hmono hreg hXi hs0 hsr hρR hne u
  have e1 : θ * r / r = θ := by field_simp
  have e2 : r / (θ * r) = θ⁻¹ := by field_simp
  rw [e1, e2] at hstep
  set D₀ := ballExcess N P r u
  set D₁ := ballExcess N P (θ * r) u
  set K := CV * θ⁻¹ ^ γ + CH * θ ^ (j + 1)
  have hK : 0 ≤ K := add_nonneg (mul_nonneg hCV (Real.rpow_nonneg (inv_nonneg.2 hθ0.le) _))
    (mul_nonneg hCH (pow_nonneg hθ0.le _))
  have hD₀ : 0 ≤ D₀ := ballExcess_nonneg N P r u
  have hdist := mul_le_mul_of_nonneg_left happ hK
  have hθj : 0 < θ ^ j := pow_pos hθ0 j
  have hrj : 0 < r ^ j := pow_pos hr0 j
  have hpow : r ^ (1 - α - j) = r ^ (1 - α) / r ^ j := Real.rpow_sub_natCast hr0.ne' _ _
  rw [hpow, mul_pow, div_le_iff₀ (mul_pos hθj hrj)]
  have hgoal : (D₀ / r ^ j / 2 + K / θ ^ j * Γ * (r ^ (1 - α) / r ^ j)) * (θ ^ j * r ^ j) =
      θ ^ j * D₀ / 2 + K * (r ^ (1 - α) * Γ) := by
    field_simp
  rw [hgoal]
  have h1 : CH * θ ^ (j + 1) * D₀ ≤ θ ^ j * D₀ / 2 := by
    rw [pow_succ]
    have : CH * (θ ^ j * θ) * D₀ = (CH * θ) * (θ ^ j * D₀) := by ring
    rw [this]
    nlinarith [mul_nonneg hθj.le hD₀]
  linarith

/-- **One step of the summation over the scales.** For near-best approximations `a` at radius
`ρa` and `b` at radius `θ ρa` (both in `Phigh`), the excess of `b - a` over `Plow` at a radius
`ρn ≤ θ ρa` is controlled through `PolynomialComparison` and `RadiusMonotone`. -/
theorem ballExcess_sub_le_of_scale {Plow Phigh : AddSubgroup F} {j : ℕ} {X R CV CP γ θ : ℝ}
    (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hmono : RadiusMonotone N X R CV γ)
    (hpc : PolynomialComparison N Plow Phigh j X R CP) {ρn ρa : ℝ} (hX0 : 0 < X) (hX : X ≤ ρn)
    (hn : ρn ≤ θ * ρa) (hρa : 0 < ρa) (hR : ρa ≤ R) {u a b : F} (ha : a ∈ Phigh) (hb : b ∈ Phigh)
    {η : ℝ} (hη : 0 ≤ η) (hua : N ρa (u - a) ≤ ballExcess N Phigh ρa u + η)
    (hub : N (θ * ρa) (u - b) ≤ ballExcess N Phigh (θ * ρa) u + η) :
    ballExcess N Plow ρn (b - a) ≤
      CP * (ρn ^ j * (ballExcess N Phigh (θ * ρa) u / (θ * ρa) ^ j)) +
        CP * CV * θ⁻¹ ^ γ / θ ^ j * (ρn ^ j * (ballExcess N Phigh ρa u / ρa ^ j)) +
          CP * (1 + CV * θ⁻¹ ^ γ) * η := by
  have hρb : 0 < θ * ρa := mul_pos hθ0 hρa
  have hρn : 0 < ρn := hX0.trans_le hX
  have hbR : θ * ρa ≤ R := (mul_le_of_le_one_left hρa.le hθ1).trans hR
  set Θ := θ⁻¹ ^ γ with hΘ
  have hΘ0 : 0 ≤ Θ := Real.rpow_nonneg (inv_nonneg.2 hθ0.le) _
  set Da := ballExcess N Phigh ρa u
  set Db := ballExcess N Phigh (θ * ρa) u
  have h1 := hpc _ (Phigh.sub_mem hb ha) ρn (θ * ρa) hX hn hbR
  have h2 := ballExcess_le_self N Plow (θ * ρa) (b - a)
  have h3 : N (θ * ρa) (b - a) ≤ N (θ * ρa) (u - a) + N (θ * ρa) (u - b) := by
    have := map_sub_le_add (N (θ * ρa)) (u - a) (u - b)
    rwa [sub_sub_sub_cancel_left] at this
  have h4 := hmono (u - a) (θ * ρa) ρa (hX.trans hn) (mul_le_of_le_one_left hρa.le hθ1) hR
  have e1 : ρa / (θ * ρa) = θ⁻¹ := by field_simp
  rw [e1] at h4
  set c := (ρn / (θ * ρa)) ^ j with hcdef
  have hc0 : 0 ≤ c := pow_nonneg (div_nonneg hρn.le hρb.le) _
  have hc1 : c ≤ 1 := pow_le_one₀ (div_nonneg hρn.le hρb.le) ((div_le_one hρb).2 hn)
  have r1 : c * Db = ρn ^ j * (Db / (θ * ρa) ^ j) := by
    rw [hcdef, div_pow]; field_simp [(pow_pos hρb j).ne']
  have r2 : c * Da = ρn ^ j * (Da / ρa ^ j) / θ ^ j := by
    rw [hcdef, div_pow, mul_pow]
    field_simp [(pow_pos hρa j).ne', (pow_pos hθ0 j).ne']
  have hN : N (θ * ρa) (b - a) ≤ (Db + η) + CV * Θ * (Da + η) := by
    have : CV * Θ * N ρa (u - a) ≤ CV * Θ * (Da + η) :=
      mul_le_mul_of_nonneg_left hua (mul_nonneg hCV hΘ0)
    linarith
  have hcN := mul_le_mul_of_nonneg_left hN (mul_nonneg hCP hc0)
  have hexp : CP * c * ((Db + η) + CV * Θ * (Da + η)) =
      CP * (c * Db) + CP * CV * Θ * (c * Da) + CP * (1 + CV * Θ) * (c * η) := by ring
  rw [hexp, r1, r2] at hcN
  have hcη : CP * (1 + CV * Θ) * (c * η) ≤ CP * (1 + CV * Θ) * η := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have h5 : CP * CV * Θ * (ρn ^ j * (Da / ρa ^ j) / θ ^ j) =
      CP * CV * Θ / θ ^ j * (ρn ^ j * (Da / ρa ^ j)) := by ring
  have hcq : ballExcess N Plow ρn (b - a) ≤ CP * c * N (θ * ρa) (b - a) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hCP hc0))
  linarith

/-- **Summation over the scales.** With near-best approximations `w m ∈ Phigh` of `u` at the radii
`θ^m ρ₀` and `w₀ ∈ Plow` at `ρ₀`, the excess of `u` over `Plow` at `θ^n ρ₀` is at most the excess
of `u - w n` plus the excess of `w n - w₀`; the latter is the sum of the excesses of the differences
`w (m + 1) - w m` and of `w 0 - w₀`, each transported to the radius `θ^n ρ₀` by
`PolynomialComparison`. -/
theorem ballExcess_le_sum_geometric {Plow Phigh : AddSubgroup F} (hP : Plow ≤ Phigh) {j : ℕ}
    {X R CV CP γ θ ρ₀ : ℝ} (hX0 : 0 < X) (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (hmono : RadiusMonotone N X R CV γ)
    (hpc : PolynomialComparison N Plow Phigh j X R CP) {n : ℕ} (hρR : ρ₀ ≤ R)
    (hXn : X ≤ θ ^ n * ρ₀) (u : F) :
    ballExcess N Plow (θ ^ n * ρ₀) u ≤
      (θ ^ n * ρ₀) ^ j * ((1 + CP + CP * CV * θ⁻¹ ^ γ / θ ^ j) *
        ∑ m ∈ range (n + 1), ballExcess N Phigh (θ ^ m * ρ₀) u / (θ ^ m * ρ₀) ^ j) +
      2 * CP * (θ ^ n) ^ j * ballExcess N Plow ρ₀ u := by
  have hρ₀ : 0 < ρ₀ := pos_of_mul_pos_right (hX0.trans_le hXn) (pow_nonneg hθ0.le _)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ρ = fun m => θ ^ m * ρ₀ := ⟨_, rfl⟩
  have hρm : ∀ m, θ ^ m * ρ₀ = ρ m := fun m => by rw [hρ]
  have hρpos : ∀ m, 0 < ρ m := fun m => by rw [← hρm]; exact mul_pos (pow_pos hθ0 m) hρ₀
  have hρanti : ∀ m m', m ≤ m' → ρ m' ≤ ρ m := fun m m' h => by
    rw [← hρm, ← hρm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0.le hθ1 h) hρ₀.le
  have hρX : ∀ m ≤ n, X ≤ ρ m := fun m hm => (hρm n ▸ hXn).trans (hρanti m n hm)
  have hρ0 : ρ 0 = ρ₀ := by rw [← hρm, pow_zero, one_mul]
  have hρR' : ∀ m, ρ m ≤ R := fun m => (hρanti 0 m (Nat.zero_le m)).trans (hρ0 ▸ hρR)
  have hρs : ∀ m, ρ (m + 1) = θ * ρ m := fun m => by rw [← hρm, ← hρm, pow_succ]; ring
  have hθn : ρ n / ρ₀ = θ ^ n := by rw [← hρm]; field_simp
  simp only [hρm]
  clear hρ
  set T : ℕ → ℝ := fun m => ballExcess N Phigh (ρ m) u / (ρ m) ^ j with hT
  have hT0 : ∀ m, 0 ≤ T m := fun m =>
    div_nonneg (ballExcess_nonneg N Phigh _ _) (pow_nonneg (hρpos m).le _)
  have hTmul : ∀ m, (ρ m) ^ j * T m = ballExcess N Phigh (ρ m) u := fun m => by
    simp only [hT]; field_simp [(pow_pos (hρpos m) j).ne']
  set Θ := θ⁻¹ ^ γ with hΘ
  have hΘ0 : 0 ≤ Θ := Real.rpow_nonneg (inv_nonneg.2 hθ0.le) _
  set S := ∑ m ∈ range (n + 1), T m with hS
  have hTnS : T n ≤ S := by
    rw [hS, sum_range_succ]; linarith [sum_nonneg fun m (_ : m ∈ range n) => hT0 m]
  have hTS : ∑ m ∈ range n, T m ≤ S := by rw [hS, sum_range_succ]; linarith [hT0 n]
  have hTS' : ∑ m ∈ range n, T (m + 1) ≤ S := by rw [hS, sum_range_succ']; linarith [hT0 0]
  set ρn := ρ n with hρn
  have hρnj : 0 ≤ ρn ^ j := pow_nonneg (hρpos n).le _
  have hθnj0 : 0 ≤ (θ ^ n) ^ j := pow_nonneg (pow_nonneg hθ0.le _) _
  have hθnj1 : (θ ^ n) ^ j ≤ 1 := pow_le_one₀ (pow_nonneg hθ0.le _) (pow_le_one₀ hθ0.le hθ1)
  have hc : 0 ≤ 1 + 2 * CP + n * (CP * (1 + CV * Θ)) := by positivity
  apply le_of_forall_pos_le_add_mul hc
  intro η hη
  choose w hwP hw using fun m : ℕ => exists_lt_ballExcess_add N Phigh hη (ρ m) u
  obtain ⟨w₀, hw₀P, hw₀⟩ := exists_lt_ballExcess_add N Plow hη ρ₀ u
  set q := ballExcess N Plow ρn with hq
  have ha := ballExcess_le_add N Plow ρn u (w n)
  have hb : q (w n) = q (w n - w₀) := (ballExcess_sub_mem N Plow ρn (w n) hw₀P).symm
  have htel : w n - w₀ = (w 0 - w₀) + ∑ m ∈ range n, (w (m + 1) - w m) := by
    rw [sum_range_sub]; abel
  have hq0 : q 0 ≤ 0 := (ballExcess_of_mem N Plow Plow.zero_mem).le
  have hcsum : q (w n - w₀) ≤ q (w 0 - w₀) + ∑ m ∈ range n, q (w (m + 1) - w m) := by
    rw [htel]
    exact (ballExcess_add_le N Plow _ _ _).trans
      (add_le_add le_rfl (le_sum_of_subadditive q hq0 (ballExcess_add_le N Plow ρn) _ _))
  have hsub : ∀ s : ℝ, ∀ a b : F, N s (a - b) ≤ N s (u - b) + N s (u - a) := by
    intro s a b
    have := map_sub_le_add (N s) (u - b) (u - a)
    rwa [sub_sub_sub_cancel_left] at this
  have hd : ∀ m < n, q (w (m + 1) - w m) ≤ CP * (ρn ^ j * T (m + 1)) +
      CP * CV * Θ / θ ^ j * (ρn ^ j * T m) + CP * (1 + CV * Θ) * η := by
    intro m hm
    have hn : ρn ≤ θ * ρ m := hρs m ▸ hρanti _ _ hm
    have key := ballExcess_sub_le_of_scale N hCV hCP hθ0 hθ1 hmono hpc hX0 (hρX n le_rfl) hn
      (hρpos m) (hρR' m) (hwP m) (hwP (m + 1)) hη.le (hw m).le (hρs m ▸ (hw (m + 1)).le)
    simp only [hT]
    rw [hρs m]
    exact key
  have he : q (w 0 - w₀) ≤ 2 * CP * (θ ^ n) ^ j * ballExcess N Plow ρ₀ u + 2 * CP * η := by
    have hmem : w 0 - w₀ ∈ Phigh := Phigh.sub_mem (hwP 0) (hP hw₀P)
    have h1 := hpc _ hmem ρn (ρ 0) (hρX n le_rfl) (hρanti _ _ (Nat.zero_le n)) (hρR' 0)
    have h2 := ballExcess_le_self N Plow (ρ 0) (w 0 - w₀)
    have h3 := hsub (ρ 0) (w 0) w₀
    have h5 := hw 0
    rw [hρ0] at h1 h2 h3 h5
    have h6 := ballExcess_anti N hP ρ₀ u
    rw [hθn] at h1
    have hN : N ρ₀ (w 0 - w₀) ≤ 2 * ballExcess N Plow ρ₀ u + 2 * η := by linarith
    have := mul_le_mul_of_nonneg_left hN (mul_nonneg hCP hθnj0)
    have h7 : CP * (θ ^ n) ^ j * (2 * η) ≤ 2 * CP * η := by
      nlinarith [mul_nonneg (mul_nonneg hCP hη.le) (sub_nonneg.2 hθnj1)]
    calc q (w 0 - w₀) ≤ CP * (θ ^ n) ^ j * N ρ₀ (w 0 - w₀) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hCP hθnj0))
      _ ≤ _ := by linarith
  have hf : N ρn (u - w n) ≤ ρn ^ j * T n + η := by
    have := hw n; rw [← hTmul n] at this; exact this.le
  have hsumd : ∑ m ∈ range n, q (w (m + 1) - w m) ≤
      CP * (ρn ^ j * ∑ m ∈ range n, T (m + 1)) +
        CP * CV * Θ / θ ^ j * (ρn ^ j * ∑ m ∈ range n, T m) + n * (CP * (1 + CV * Θ)) * η := by
    calc ∑ m ∈ range n, q (w (m + 1) - w m) ≤ ∑ m ∈ range n, (CP * (ρn ^ j * T (m + 1)) +
          CP * CV * Θ / θ ^ j * (ρn ^ j * T m) + CP * (1 + CV * Θ) * η) :=
          sum_le_sum fun m hm => hd m (mem_range.1 hm)
      _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum,
          sum_const, card_range, nsmul_eq_mul]
        ring
  have hL1 := mul_le_mul_of_nonneg_left hTS' (mul_nonneg hCP hρnj)
  have hL2 := mul_le_mul_of_nonneg_left hTS
    (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hCP hCV) hΘ0) (pow_nonneg hθ0.le j)) hρnj)
  have hL3 := mul_le_mul_of_nonneg_left hTnS hρnj
  have hfin : ρn ^ j * ((1 + CP + CP * CV * Θ / θ ^ j) * S) =
      ρn ^ j * S + CP * ρn ^ j * S + CP * CV * Θ / θ ^ j * ρn ^ j * S := by ring
  rw [hfin]
  have hq' : ballExcess N Plow ρn u ≤ N ρn (u - w n) + q (w n - w₀) := by rw [← hb]; exact ha
  linarith

/-- **The iteration along a geometric sequence of radii** (Armstrong–Dario, proof of Lemma 7.2,
Steps 2 and 3). If `u` is within `(θ^i ρ₀) ^ (1 - α) Γ` of `Abar (θ^i ρ₀)` for every `i < n`, then
`D(θ^n ρ₀) ≤ K₁ θ^{n j} D(ρ₀) + K₂ (θ^n ρ₀) ^ (1 - α) Γ` for the excess `D` over `Plow`, where
`Phigh` carries the excess decay of degree `j ≥ 1` of the harmonic functions. -/
theorem ballExcess_geometric_le {Plow Phigh : AddSubgroup F} (hP : Plow ≤ Phigh)
    {Abar : ℝ → Set F} {j : ℕ} (hj : 1 ≤ j) {X R CV CP CH γ α θ Γ ρ₀ : ℝ} (hX0 : 0 < X)
    (hCV : 0 ≤ CV) (hCP : 0 ≤ CP) (hCH : 0 ≤ CH) (hα : 0 < α) (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    (hCHθ : CH * θ ≤ 1 / 2) (hΓ : 0 ≤ Γ) (hmono : RadiusMonotone N X R CV γ)
    (hpc : PolynomialComparison N Plow Phigh j X R CP)
    (hreg : HarmonicRegularity N Abar Phigh j X R CH) {n : ℕ} (hρR : ρ₀ ≤ R)
    (hXn : X ≤ θ ^ n * ρ₀) (u : F) (hne : ∀ i < n, (Abar (θ ^ i * ρ₀)).Nonempty)
    (happ : ∀ i < n, ballDist N (Abar (θ ^ i * ρ₀)) (θ ^ i * ρ₀) u ≤ (θ ^ i * ρ₀) ^ (1 - α) * Γ) :
    ballExcess N Plow (θ ^ n * ρ₀) u ≤
      geometricConstOne CV CP γ θ j * (θ ^ n) ^ j * ballExcess N Plow ρ₀ u +
        geometricConstTwo CV CP CH γ α θ j * (θ ^ n * ρ₀) ^ (1 - α) * Γ := by
  have hθ1 : θ ≤ 1 := by linarith
  have hρ₀ : 0 < ρ₀ := pos_of_mul_pos_right (hX0.trans_le hXn) (pow_nonneg hθ0.le _)
  have hρpos : ∀ m : ℕ, 0 < θ ^ m * ρ₀ := fun m => mul_pos (pow_pos hθ0 m) hρ₀
  have hρanti : ∀ m m' : ℕ, m ≤ m' → θ ^ m' * ρ₀ ≤ θ ^ m * ρ₀ := fun m m' h =>
    mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0.le hθ1 h) hρ₀.le
  set T : ℕ → ℝ := fun m => ballExcess N Phigh (θ ^ m * ρ₀) u / (θ ^ m * ρ₀) ^ j with hT
  set Θ := θ⁻¹ ^ γ with hΘ
  set B := (CV * Θ + CH * θ ^ (j + 1)) / θ ^ j with hB
  have hB0 : 0 ≤ B := div_nonneg (add_nonneg (mul_nonneg hCV
    (Real.rpow_nonneg (inv_nonneg.2 hθ0.le) _)) (mul_nonneg hCH (pow_nonneg hθ0.le _)))
    (pow_nonneg hθ0.le _)
  set L := 1 + CP + CP * CV * Θ / θ ^ j with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ CP * CV * Θ / θ ^ j := div_nonneg (mul_nonneg (mul_nonneg hCP hCV)
      (Real.rpow_nonneg (inv_nonneg.2 hθ0.le) _)) (pow_nonneg hθ0.le _)
    linarith
  set β : ℝ := (j : ℝ) + α - 1 with hβ
  have hβ0 : 0 < β := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  set q := θ ^ β with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hθ0.le _
  have hq1 : q < 1 := Real.rpow_lt_one hθ0.le (by linarith) hβ0
  have he : (1 - α - j : ℝ) = -β := by rw [hβ]; ring
  -- the halving recurrence
  have hhalf : ∀ i < n, T (i + 1) ≤ T i / 2 + B * Γ * (θ ^ i * ρ₀) ^ (1 - α - j) := by
    intro i hi
    have hXi : X ≤ θ ^ (i + 1) * ρ₀ := hXn.trans (hρanti _ _ hi)
    have hRi : θ ^ i * ρ₀ ≤ R := (hρanti 0 i (Nat.zero_le i)).trans (by simpa using hρR)
    exact ballExcess_halving_step N Phigh hX0 hCV hCH hθ0 hθ hCHθ hmono hreg hRi hXi
      (hne i hi) u (happ i hi)
  have hsumT := sum_range_le_of_le_half_add
    (div_nonneg (ballExcess_nonneg N Phigh _ _) (pow_nonneg (hρpos n).le _)) hhalf
  -- the forcing sum
  have hforce : ∑ i ∈ range n, B * Γ * (θ ^ i * ρ₀) ^ (1 - α - j) ≤
      B * Γ * ((θ ^ n * ρ₀) ^ (1 - α - j) / (1 - q)) := by
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB0 hΓ)
    rw [he]
    have hrw : ∀ i ∈ range n, (θ ^ i * ρ₀) ^ (-β) = (θ ^ n * ρ₀) ^ (-β) * q ^ (n - i) :=
      fun i hi => by
        rw [rpow_neg_geometric hθ0 hρ₀ (mem_range.1 hi).le, mul_comm]
    rw [sum_congr rfl hrw, ← mul_sum, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (sum_range_pow_sub_le hq0 hq1 n)
      (Real.rpow_nonneg (hρpos n).le _)
  -- the summation over the scales
  have htel := ballExcess_le_sum_geometric N hP hX0 hCV hCP hθ0 hθ1 hmono hpc hρR hXn u
  -- the first term
  have hT0 : (θ ^ n * ρ₀) ^ j * T 0 ≤ (θ ^ n) ^ j * ballExcess N Plow ρ₀ u := by
    have h1 : (θ ^ n * ρ₀) ^ j * T 0 = (θ ^ n) ^ j * ballExcess N Phigh ρ₀ u := by
      simp only [hT, pow_zero, one_mul]
      rw [mul_pow]
      field_simp [(pow_pos hρ₀ j).ne']
    rw [h1]
    exact mul_le_mul_of_nonneg_left (ballExcess_anti N hP ρ₀ u)
      (pow_nonneg (pow_nonneg hθ0.le _) _)
  have hpow : (θ ^ n * ρ₀) ^ j * (θ ^ n * ρ₀) ^ (1 - α - j) = (θ ^ n * ρ₀) ^ (1 - α) := by
    rw [Real.rpow_sub_natCast (hρpos n).ne']
    field_simp [(pow_pos (hρpos n) j).ne']
  set S := ∑ m ∈ range (n + 1), T m with hS
  set ρn := θ ^ n * ρ₀ with hρn
  have hρnj : 0 ≤ ρn ^ j := pow_nonneg (hρpos n).le _
  have hS' : S ≤ 2 * T 0 + 2 * (B * Γ * (ρn ^ (1 - α - j) / (1 - q))) := by linarith
  have hmain : ρn ^ j * (L * S) ≤ 2 * L * (ρn ^ j * T 0) +
      2 * L * B / (1 - q) * (ρn ^ j * ρn ^ (1 - α - j)) * Γ := by
    have := mul_le_mul_of_nonneg_left hS' (mul_nonneg hρnj hL0)
    have hq' : 0 < 1 - q := by linarith
    calc ρn ^ j * (L * S) = ρn ^ j * L * S := by ring
      _ ≤ ρn ^ j * L * (2 * T 0 + 2 * (B * Γ * (ρn ^ (1 - α - j) / (1 - q)))) := this
      _ = 2 * L * (ρn ^ j * T 0) +
          2 * L * B / (1 - q) * (ρn ^ j * ρn ^ (1 - α - j)) * Γ := by
        field_simp
  rw [hpow] at hmain
  have hK1 : geometricConstOne CV CP γ θ j = 2 * L + 2 * CP := by
    simp only [geometricConstOne, hL, hΘ]
  have hK2 : geometricConstTwo CV CP CH γ α θ j = 2 * L * B / (1 - q) := by
    simp only [geometricConstTwo, hL, hB, hΘ, hq, hβ]
  rw [hK1, hK2]
  have hLT := mul_le_mul_of_nonneg_left hT0 (by linarith : (0 : ℝ) ≤ 2 * L)
  nlinarith

end Rigidity.Proofs.Regularity

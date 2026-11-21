import Rigidity.Proofs.Cluster.GehringLayer
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Gehring's lemma on triadic cubes

**Theorem** (`gehring_triadic`). Let `0 < θ < 1`, `A ≥ 1` and `j ≥ 1`. There are `ε ∈ (0, 1]` and
`C < ∞`, depending only on `d, θ, A, j`, such that for every triadic cube `□ = cube n x₀`, with
`3□ = enl 1 n x₀`, and every `g ≥ 0` satisfying the reverse Hölder inequality
`avg_{□'} g ≤ A (avg_{enl j □'} g^θ)^{1/θ}` on every triadic cube `□'` whose enlargement
`enl j □'` (same center, side `3^j` times larger) lies in `3□`,

`avg_□ g^{1+ε} ≤ C (avg_{3□} g)^{1+ε}`.

This is the discrete form of Gehring's lemma used by Armstrong–Dario, *Elliptic regularity and
quantitative homogenization on percolation clusters*, in the proof of Proposition 3.8 (they quote
Giusti, *Direct methods in the calculus of variations*, Theorem 6.6 and Corollary 6.1, and pass to
the lattice by affine interpolation); here it is proved on the triadic cubes of `ℤ^d` directly.

The single-cube estimate `sum_rpow_le_of_reverse_holder` gives, for the cubes of scale `k` in the
ball of radius `ρ_k = h_{n+1} - 2·3^{k+j}` around the center of `□`,
`avg g^{1+ε} ≤ (3^{(n+1-k)d} avg_{3□} g)^{1+ε} + η 3^{jd} max_{scale k-1} avg g^{1+ε}`, and the
enlargements of these cubes are unions of cubes of scale `k - 1` in the ball of radius `ρ_{k-1}`.
For `ε` so small that `3 η 3^{(j+2)d} ≤ 2` (`exists_small_gehring_exponent`), the bound
`avg_{cube k x} g^{1+ε} ≤ 3 (3^{(n+1-k)d} avg_{3□} g)^{1+ε}` propagates from single points
(`k = 0`) up to the scale `n - j - 1`, whose cubes tile `□`.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

theorem box_subset_box_of_mem {c x : Vertex d} {R S T : ℤ} (hx : x ∈ box c R) (h : R + S ≤ T) :
    box x S ⊆ box c T := by
  intro y hy
  rw [mem_box] at hx hy ⊢
  intro i
  have := abs_sub_le (y i) (x i) (c i)
  linarith [hx i, hy i]

theorem avg_le_of_forall_le {V : Type*} {S : Finset V} (hS : S.Nonempty) {F : V → ℝ} {M : ℝ}
    (h : ∀ x ∈ S, F x ≤ M) : avg S F ≤ M := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [avg, div_le_iff₀ hcard]
  calc ∑ x ∈ S, F x ≤ ∑ _x ∈ S, M := Finset.sum_le_sum h
    _ = M * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The factor `η` of the single-cube estimate for the exponent `1 + ε`. -/
noncomputable def gehringFactor (d : ℕ) (θ A δ ε : ℝ) : ℝ :=
  (2 ^ ε - 1) * (2 * 9 ^ d * A ^ θ) * (2 ^ (1 + ε - θ) / (2 ^ (1 + ε - θ) - 1)) *
    (1 / δ) ^ (1 + ε - θ)

/-- **Choice of the exponent.** For `0 < θ < 1`, `A > 0`, `0 < δ ≤ 1` and any `M ≥ 0` there is
`ε ∈ (0, 1]` with `M · gehringFactor d θ A δ ε ≤ 2`. -/
theorem exists_small_gehring_exponent {θ A δ M : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ M * gehringFactor d θ A δ ε ≤ 2 := by
  set L : ℝ := 2 * 9 ^ d * A ^ θ with hL
  have hL0 : 0 < L := mul_pos (by positivity) (Real.rpow_pos_of_pos hA θ)
  have hb1 : 1 < (2 : ℝ) ^ (1 - θ) := Real.one_lt_rpow (by norm_num) (by linarith)
  set R : ℝ := 1 + 1 / ((2 : ℝ) ^ (1 - θ) - 1) with hR
  have hR0 : 0 < R := add_pos one_pos (div_pos one_pos (by linarith))
  have hδ' : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ, one_mul]; exact hδ1
  set D : ℝ := (1 / δ) ^ (2 : ℝ) with hD
  have hD0 : 0 < D := Real.rpow_pos_of_pos (div_pos one_pos hδ) _
  set K : ℝ := L * R * D with hK
  have hK0 : 0 < K := mul_pos (mul_pos hL0 hR0) hD0
  set ε : ℝ := min 1 (2 / ((M + 1) * K)) with hε
  have hε0 : 0 < ε := lt_min one_pos (div_pos two_pos (mul_pos (by linarith) hK0))
  have hε1 : ε ≤ 1 := min_le_left _ _
  refine ⟨ε, hε0, hε1, ?_⟩
  have ha : 0 < 1 + ε - θ := by linarith
  -- `2^ε - 1 ≤ ε`
  have h1 : (2 : ℝ) ^ ε - 1 ≤ ε := by
    have := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hε0.le hε1
    norm_num at this
    linarith
  have h1' : 0 ≤ (2 : ℝ) ^ ε - 1 := by
    have := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hε0.le
    linarith
  -- `2^a / (2^a - 1) ≤ R`
  have h2 : (2 : ℝ) ^ (1 + ε - θ) / (2 ^ (1 + ε - θ) - 1) ≤ R := by
    have hle : (2 : ℝ) ^ (1 - θ) ≤ 2 ^ (1 + ε - θ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hpos : 0 < (2 : ℝ) ^ (1 + ε - θ) - 1 := by linarith
    have hpos' : 0 < (2 : ℝ) ^ (1 - θ) - 1 := by linarith
    have heq : (2 : ℝ) ^ (1 + ε - θ) / (2 ^ (1 + ε - θ) - 1) =
        1 + 1 / (2 ^ (1 + ε - θ) - 1) := by
      rw [div_eq_iff hpos.ne', add_mul, one_div_mul_cancel hpos.ne']
      ring
    rw [heq, hR]
    have : 1 / ((2 : ℝ) ^ (1 + ε - θ) - 1) ≤ 1 / ((2 : ℝ) ^ (1 - θ) - 1) :=
      one_div_le_one_div_of_le hpos' (by linarith)
    linarith
  have h2' : 0 ≤ (2 : ℝ) ^ (1 + ε - θ) / (2 ^ (1 + ε - θ) - 1) := by
    have : 1 < (2 : ℝ) ^ (1 + ε - θ) := Real.one_lt_rpow (by norm_num) ha
    exact div_nonneg (by linarith) (by linarith)
  -- `(1/δ)^a ≤ D`
  have h3 : (1 / δ) ^ (1 + ε - θ) ≤ D :=
    Real.rpow_le_rpow_of_exponent_le hδ' (by linarith)
  have h3' : 0 ≤ (1 / δ) ^ (1 + ε - θ) := Real.rpow_nonneg (div_nonneg zero_le_one hδ.le) _
  have hη : gehringFactor d θ A δ ε ≤ ε * K := by
    unfold gehringFactor
    rw [← hL]
    calc (2 ^ ε - 1) * L * (2 ^ (1 + ε - θ) / (2 ^ (1 + ε - θ) - 1)) * (1 / δ) ^ (1 + ε - θ)
        ≤ ε * L * R * D := by
          have e1 : (2 ^ ε - 1) * L ≤ ε * L := mul_le_mul_of_nonneg_right h1 hL0.le
          have e2 : (2 ^ ε - 1) * L * (2 ^ (1 + ε - θ) / (2 ^ (1 + ε - θ) - 1)) ≤ ε * L * R :=
            mul_le_mul e1 h2 h2' (mul_nonneg hε0.le hL0.le)
          exact mul_le_mul e2 h3 h3' (mul_nonneg (mul_nonneg hε0.le hL0.le) hR0.le)
      _ = ε * K := by rw [hK]; ring
  have hεK : ε * ((M + 1) * K) ≤ 2 := by
    have : ε ≤ 2 / ((M + 1) * K) := min_le_right _ _
    rwa [le_div_iff₀ (mul_pos (by linarith) hK0)] at this
  calc M * gehringFactor d θ A δ ε ≤ M * (ε * K) := mul_le_mul_of_nonneg_left hη hM
    _ ≤ ε * ((M + 1) * K) := by nlinarith [mul_nonneg hε0.le hK0.le]
    _ ≤ 2 := hεK

/-- **Gehring's lemma on triadic cubes.** -/
theorem gehring_triadic {θ A : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hA : 1 ≤ A) {j : ℕ} (hj : 1 ≤ j) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (x₀ : Vertex d) (g : Vertex d → ℝ), (∀ x, 0 ≤ g x) →
        (∀ k y, enl j k y ⊆ enl 1 n x₀ →
          avg (cube k y) g ≤ A * avg (enl j k y) (fun x => g x ^ θ) ^ (1 / θ)) →
        avg (cube n x₀) (fun x => g x ^ (1 + ε)) ≤ C * avg (enl 1 n x₀) g ^ (1 + ε) := by
  have hA0 : 0 < A := by linarith
  -- the fraction `δ` of the levels
  set δ : ℝ := (1 / 2) ^ (1 / θ) / A with hδdef
  have hhalf : 0 < ((1 : ℝ) / 2) ^ (1 / θ) := Real.rpow_pos_of_pos (by norm_num) _
  have hδ0 : 0 < δ := div_pos hhalf hA0
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hA0]
    exact (Real.rpow_le_one (by norm_num) (by norm_num) (one_div_nonneg.mpr hθ.le)).trans hA
  have hAδ : 2 * (A * δ) ^ θ ≤ 1 := by
    have h1 : A * δ = (1 / 2) ^ (1 / θ) := by
      rw [hδdef]
      have := hA0.ne'
      field_simp
    rw [h1, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hθ.ne', Real.rpow_one]
    norm_num
  set M : ℝ := 3 * (3 : ℝ) ^ ((j + 2) * d) with hMdef
  obtain ⟨ε, hε0, hε1, hη⟩ := exists_small_gehring_exponent (d := d) hθ hθ1 hA0 hδ0 hδ1
    (by positivity : (0 : ℝ) ≤ M)
  set η := gehringFactor d θ A δ ε with hηdef
  have hη0 : 0 ≤ η := by
    have h1 : 0 ≤ (2 : ℝ) ^ ε - 1 := by
      have := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hε0.le
      linarith
    have h2 : 0 ≤ (2 : ℝ) ^ (1 + ε - θ) / (2 ^ (1 + ε - θ) - 1) := by
      have : 1 < (2 : ℝ) ^ (1 + ε - θ) := Real.one_lt_rpow (by norm_num) (by linarith)
      exact div_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ (1 / δ) ^ (1 + ε - θ) := Real.rpow_nonneg (div_nonneg zero_le_one hδ0.le) _
    have h4 : 0 ≤ (2 : ℝ) * 9 ^ d * A ^ θ :=
      (mul_pos (by positivity) (Real.rpow_pos_of_pos hA0 θ)).le
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h4) h2) h3
  refine ⟨ε, hε0, hε1, 3 * ((3 : ℝ) ^ ((j + 2) * d)) ^ (1 + ε), by positivity, ?_⟩
  intro n x₀ g hg hRH
  have h1ε : (1 : ℝ) + ε ≠ 0 := ne_of_gt (by linarith)
  set c := center n x₀ with hc
  set Ω := enl 1 n x₀ with hΩ
  have hΩbox : Ω = box c (halfSide (n + 1)) := rfl
  have hΩcard : (Ω.card : ℝ) = ((3 : ℝ) ^ (n + 1)) ^ d := card_enl 1 n x₀
  have hΩpos : (0 : ℝ) < Ω.card := by rw [hΩcard]; positivity
  have hΩne : (Ω.card : ℝ) ≠ 0 := hΩpos.ne'
  set a := avg Ω g with ha
  have ha0 : 0 ≤ a := div_nonneg (Finset.sum_nonneg fun x _ => hg x) hΩpos.le
  have hsumΩ : ∑ x ∈ Ω, g x = Ω.card * a := by
    rw [ha, avg]
    field_simp
  -- averages of `g` over cubes in `Ω`
  set B : ℕ → ℝ := fun k => ((3 : ℝ) ^ (n + 1)) ^ d / ((3 : ℝ) ^ k) ^ d * a with hB
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    simp only [hB]
    positivity
  have hBsucc : ∀ k, B k = 3 ^ d * B (k + 1) := fun k => by
    simp only [hB]
    rw [pow_succ (3 : ℝ) k, mul_pow]
    have h1 : ((3 : ℝ) ^ k) ^ d ≠ 0 := by positivity
    have h2 : (3 : ℝ) ^ d ≠ 0 := by positivity
    field_simp
  have hcubeavg : ∀ k x, cube k x ⊆ Ω → avg (cube k x) g ≤ B k := by
    intro k x hsub
    have hpos := card_cube_pos k x
    rw [avg, div_le_iff₀ hpos, card_cube]
    have h1 : ∑ y ∈ cube k x, g y ≤ ∑ y ∈ Ω, g y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => hg y
    rw [hsumΩ, hΩcard] at h1
    simp only [hB]
    have h3 : (0 : ℝ) < ((3 : ℝ) ^ k) ^ d := by positivity
    have h3' := h3.ne'
    calc ∑ y ∈ cube k x, g y ≤ ((3 : ℝ) ^ (n + 1)) ^ d * a := h1
      _ = ((3 : ℝ) ^ (n + 1)) ^ d / ((3 : ℝ) ^ k) ^ d * a * ((3 : ℝ) ^ k) ^ d := by
          field_simp
  have hpt : ∀ x ∈ Ω, g x ^ (1 + ε) ≤ B 0 ^ (1 + ε) := by
    intro x hx
    have h1 : g x ≤ ∑ y ∈ Ω, g y := Finset.single_le_sum (fun y _ => hg y) hx
    have h2 : B 0 = Ω.card * a := by
      simp only [hB, pow_zero, one_pow, div_one]
      rw [hΩcard]
    rw [hsumΩ, ← h2] at h1
    exact Real.rpow_le_rpow (hg x) h1 (by linarith)
  have hBpow : ∀ k, B k ^ (1 + ε) ≤ (3 : ℝ) ^ (2 * d) * B (k + 1) ^ (1 + ε) := by
    intro k
    rw [hBsucc k, Real.mul_rpow (by positivity) (hB0 _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (hB0 _) _)
    have h1 : ((3 : ℝ) ^ d) ^ (1 + ε) ≤ ((3 : ℝ) ^ d) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
    rw [Real.rpow_two, ← pow_mul, mul_comm d 2] at h1
    exact h1
  have hfinal : ∀ k, (n + 1 = k + (j + 2)) → B k = (3 : ℝ) ^ ((j + 2) * d) * a := by
    intro k hk
    simp only [hB]
    rw [hk, pow_add, mul_pow, pow_mul]
    have : ((3 : ℝ) ^ k) ^ d ≠ 0 := by positivity
    field_simp
  rcases Nat.lt_or_ge n (j + 1) with hsmall | hlarge
  · -- small cubes: the pointwise bound
    have hB0le : B 0 ≤ (3 : ℝ) ^ ((j + 2) * d) * a := by
      simp only [hB, pow_zero, one_pow, div_one]
      refine mul_le_mul_of_nonneg_right ?_ ha0
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right d (by omega))
    have hQΩ : cube n x₀ ⊆ Ω := cube_subset_enl 1 n x₀
    have hle : avg (cube n x₀) (fun x => g x ^ (1 + ε)) ≤ B 0 ^ (1 + ε) :=
      avg_le_of_forall_le ⟨x₀, mem_cube_self n x₀⟩ fun x hx => hpt x (hQΩ hx)
    refine hle.trans ?_
    calc B 0 ^ (1 + ε) ≤ ((3 : ℝ) ^ ((j + 2) * d) * a) ^ (1 + ε) :=
            Real.rpow_le_rpow (hB0 0) hB0le (by linarith)
        _ = ((3 : ℝ) ^ ((j + 2) * d)) ^ (1 + ε) * a ^ (1 + ε) :=
            Real.mul_rpow (by positivity) ha0
        _ ≤ 3 * ((3 : ℝ) ^ ((j + 2) * d)) ^ (1 + ε) * a ^ (1 + ε) := by
            have : 0 ≤ ((3 : ℝ) ^ ((j + 2) * d)) ^ (1 + ε) * a ^ (1 + ε) :=
              mul_nonneg (by positivity) (Real.rpow_nonneg ha0 _)
            linarith
  · -- the iteration from single points to the scale `n - j - 1`
    set k₀ := n - (j + 1) with hk₀
    set ρ : ℕ → ℤ := fun k => halfSide (n + 1) - 2 * 3 ^ (k + j) with hρ
    have hgrow : ∀ k, halfSide k + halfSide (k + j) ≤ 2 * 3 ^ (k + j) - 1 := by
      intro k
      have e1 := two_mul_halfSide_add_one k
      have e2 := two_mul_halfSide_add_one (k + j)
      have e3 : (3 : ℤ) ^ k ≤ 3 ^ (k + j) := pow_le_pow_right₀ (by norm_num) (by omega)
      have e4 : (0 : ℤ) ≤ 3 ^ (k + j) := by positivity
      linarith
    have hstep : ∀ k, ρ (k + 1) + (halfSide (k + 1) + halfSide (k + 1 + j)) ≤ ρ k := by
      intro k
      simp only [hρ]
      have e1 := two_mul_halfSide_add_one (k + 1)
      have e1' := two_mul_halfSide_add_one (k + 1 + j)
      have e5 : (3 : ℤ) ^ (k + 1) ≤ 3 ^ (k + j) := pow_le_pow_right₀ (by norm_num) (by omega)
      have e2 : (3 : ℤ) ^ (k + 1 + j) = 3 * 3 ^ (k + j) := by
        rw [show k + 1 + j = (k + j) + 1 by omega, pow_succ]
        ring
      have e3 : (0 : ℤ) ≤ 3 ^ (k + j) := by positivity
      linarith
    have hinΩ : ∀ k, ρ k + (halfSide k + halfSide (k + j)) ≤ halfSide (n + 1) := by
      intro k
      simp only [hρ]
      linarith [hgrow k]
    have henlΩ : ∀ k x, x ∈ box c (ρ k) → enl j k x ⊆ Ω := fun k x hx =>
      (enl_subset_box j k x).trans (box_subset_box_of_mem hx (hinΩ k))
    have hcubeΩ : ∀ k x, x ∈ box c (ρ k) → cube k x ⊆ Ω := fun k x hx =>
      (cube_subset_enl j k x).trans (henlΩ k x hx)
    have hρmono : ∀ k, ρ (k + 1) ≤ ρ k := fun k => by
      have := hstep k
      have : 0 ≤ halfSide (k + 1) + halfSide (k + 1 + j) :=
        add_nonneg (halfSide_nonneg _) (halfSide_nonneg _)
      linarith
    -- the invariant
    have hinv : ∀ k, k ≤ k₀ → ∀ x ∈ box c (ρ k),
        avg (cube k x) (fun y => g y ^ (1 + ε)) ≤ 3 * B k ^ (1 + ε) := by
      intro k
      induction k with
      | zero =>
          intro _ x hx
          rw [avg_cube_zero]
          show g x ^ (1 + ε) ≤ 3 * B 0 ^ (1 + ε)
          have hxΩ : x ∈ Ω := hcubeΩ 0 x hx (mem_cube_self 0 x)
          have := hpt x hxΩ
          have : 0 ≤ B 0 ^ (1 + ε) := Real.rpow_nonneg (hB0 0) _
          linarith
      | succ k ih =>
          intro hk x hx
          have ih' := ih (by omega)
          set P := cube (k + 1) x with hP
          set E := enl j (k + 1) x with hE
          have hEbox : E ⊆ box c (ρ k) :=
            (enl_subset_box j (k + 1) x).trans (box_subset_box_of_mem hx (hstep k))
          have hEΩ : E ⊆ Ω := henlΩ (k + 1) x hx
          have hRH' : ∀ k' < k + 1, ∀ y ∈ cube (k + 1) x,
              avg (cube k' y) g ≤ A * avg (enl j k' y) (fun x => g x ^ θ) ^ (1 / θ) := by
            intro k' hk' y hy
            refine hRH k' y ((enl_subset_enl hk'.le j y).trans ?_)
            rw [enl_eq_of_mem hy]
            exact hEΩ
          have hsingle := sum_rpow_le_of_reverse_holder hθ hθ1 hA0 hδ0 hAδ hε0 j (k + 1) x hg hRH'
          set τ := avg P g with hτ
          have hτ0 : 0 ≤ τ := div_nonneg (Finset.sum_nonneg fun y _ => hg y)
            (card_cube_pos _ x).le
          have hτB : τ ≤ B (k + 1) := hcubeavg (k + 1) x (hcubeΩ (k + 1) x hx)
          have hPcard := card_cube_pos (k + 1) x
          have hsumP : ∑ y ∈ P, g y = τ * P.card := by
            rw [hτ, avg, div_mul_cancel₀ _ hPcard.ne']
          -- the enlargement is a union of cubes of scale `k`
          have hEunion : ∀ y ∈ E, cube k y ⊆ E := fun y hy =>
            (cube_subset_succ k y).trans (cube_subset_enl_of_mem hy)
          have hEsum : ∑ y ∈ E, g y ^ (1 + ε) ≤ E.card * (3 * B k ^ (1 + ε)) := by
            rw [sum_eq_sum_cube_avg hEunion]
            calc ∑ y ∈ E, (∑ z ∈ cube k y, g z ^ (1 + ε)) / (cube k y).card
                ≤ ∑ _y ∈ E, 3 * B k ^ (1 + ε) :=
                  Finset.sum_le_sum fun y hy => ih' y (hEbox hy)
              _ = E.card * (3 * B k ^ (1 + ε)) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
          have hEcard : (E.card : ℝ) = ((3 : ℝ) ^ j) ^ d * P.card := card_enl_eq j (k + 1) x
          have hτpow : τ ^ ε * (τ * P.card) = τ ^ (1 + ε) * P.card := by
            rw [Real.rpow_add' hτ0 h1ε, Real.rpow_one]
            ring
          have hτB' : τ ^ (1 + ε) ≤ B (k + 1) ^ (1 + ε) :=
            Real.rpow_le_rpow hτ0 hτB (by linarith)
          have hηM : η * (3 * (3 : ℝ) ^ ((j + 2) * d)) ≤ 2 := by
            rw [mul_comm]
            exact hη
          have h3pow : ((3 : ℝ) ^ j) ^ d * (3 : ℝ) ^ (2 * d) = (3 : ℝ) ^ ((j + 2) * d) := by
            rw [← pow_mul, ← pow_add]
            congr 1
            ring
          rw [avg, div_le_iff₀ hPcard]
          have hBk := hBpow k
          have hBk1 : 0 ≤ B (k + 1) ^ (1 + ε) := Real.rpow_nonneg (hB0 _) _
          calc ∑ y ∈ P, g y ^ (1 + ε)
              ≤ τ ^ ε * ∑ y ∈ P, g y + η * ∑ y ∈ E, g y ^ (1 + ε) := hsingle
            _ ≤ τ ^ (1 + ε) * P.card + η * (E.card * (3 * B k ^ (1 + ε))) := by
                rw [hsumP, hτpow]
                linarith [mul_le_mul_of_nonneg_left hEsum hη0]
            _ ≤ B (k + 1) ^ (1 + ε) * P.card +
                  η * (((3 : ℝ) ^ j) ^ d * P.card *
                    (3 * ((3 : ℝ) ^ (2 * d) * B (k + 1) ^ (1 + ε)))) := by
                rw [hEcard]
                have i1 : τ ^ (1 + ε) * P.card ≤ B (k + 1) ^ (1 + ε) * P.card :=
                  mul_le_mul_of_nonneg_right hτB' hPcard.le
                have i2 : η * (((3 : ℝ) ^ j) ^ d * P.card * (3 * B k ^ (1 + ε))) ≤
                    η * (((3 : ℝ) ^ j) ^ d * P.card *
                      (3 * ((3 : ℝ) ^ (2 * d) * B (k + 1) ^ (1 + ε)))) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hBk])
                    (mul_nonneg (by positivity) (Nat.cast_nonneg _))) hη0
                linarith
            _ = B (k + 1) ^ (1 + ε) * P.card *
                  (1 + η * (3 * (((3 : ℝ) ^ j) ^ d * (3 : ℝ) ^ (2 * d)))) := by ring
            _ ≤ B (k + 1) ^ (1 + ε) * P.card * 3 := by
                rw [h3pow]
                refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hBk1 hPcard.le)
                linarith
            _ = 3 * B (k + 1) ^ (1 + ε) * P.card := by ring
    -- the cube `□` is a union of cubes of scale `k₀` in the ball of radius `ρ k₀`
    have hnk : n + 1 = k₀ + (j + 2) := by omega
    have hQbox : cube n x₀ ⊆ box c (ρ k₀) := by
      refine box_mono c ?_
      simp only [hρ]
      have e1 := two_mul_halfSide_add_one n
      have e2 : halfSide (n + 1) = 3 * halfSide n + 1 := rfl
      have e3 : (3 : ℤ) ^ n = 3 * 3 ^ (k₀ + j) := by
        rw [show n = (k₀ + j) + 1 by omega, pow_succ]
        ring
      have e4 : (0 : ℤ) ≤ 3 ^ (k₀ + j) := by positivity
      linarith
    have hQunion : ∀ y ∈ cube n x₀, cube k₀ y ⊆ cube n x₀ := fun y hy => by
      rw [← cube_eq_of_mem hy]
      exact cube_mono (by omega) y
    have hQ : avg (cube n x₀) (fun x => g x ^ (1 + ε)) ≤ 3 * B k₀ ^ (1 + ε) := by
      rw [avg, sum_eq_sum_cube_avg hQunion]
      exact avg_le_of_forall_le (F := fun y => avg (cube k₀ y) (fun x => g x ^ (1 + ε)))
        ⟨x₀, mem_cube_self n x₀⟩ fun y hy => hinv k₀ le_rfl y (hQbox hy)
    rw [hfinal k₀ hnk, Real.mul_rpow (by positivity) ha0] at hQ
    calc avg (cube n x₀) (fun x => g x ^ (1 + ε))
        ≤ 3 * (((3 : ℝ) ^ ((j + 2) * d)) ^ (1 + ε) * a ^ (1 + ε)) := hQ
      _ = 3 * ((3 : ℝ) ^ ((j + 2) * d)) ^ (1 + ε) * a ^ (1 + ε) := by ring

end Rigidity.Proofs.Cluster

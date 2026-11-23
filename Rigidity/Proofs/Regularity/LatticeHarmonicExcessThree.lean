import Rigidity.Proofs.Regularity.LatticeHarmonicCubic

/-!
# Excess decay of order three of lattice harmonic functions on `ℤ²`

For `F` harmonic on `B_r(z)` and a lattice harmonic cubic polynomial `w`
(`latticeHarmonicCubic`), `f = F - w` is harmonic and its fourth forward differences are bounded
on `Q_m(z)` by `m^{-d/2 - 4}` times its `ℓ²` norm on `B_r(z)` (`sq_fwd4_le`, in every dimension).
In the plane, the third-order expansion of `f` at a corner `c` (`harmonicTaylorThree f c`) is the
cubic part `cubicPart t c` with the third differences `t` of `f` at `c`, corrected by `cubicCorr`
to be harmonic, plus the harmonic second-order expansion (`abs_sub_harmonicTaylor_two_le`) of
the remainder `f - cubicPart t c`, whose third differences move by fourth differences of `f`
from their value `0` at `c`. The trace of the third differences, which the correction removes, is
a sum of fourth differences (`sum_hessAt_eq` applied to the first differences of `f`), so the
expansion is a lattice harmonic cubic polynomial within `29 S⁴ M₄` of `f` on the box
`[c, c + S 𝟙]` (`abs_sub_harmonicTaylorThree_le`). This gives the excess decay of order three,
`HarmonicRegularity` with `j = 3` for the class `latticeHarmonicClass z` and `Ā_3`
(`harmonicRegularity_three_latticeHarmonicClass`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- The coefficient of `sq_fwd4_le` at the scale `m`. -/
noncomputable def fourthDiffCoeff (d m : ℕ) : ℝ :=
  thirdDiffCoeff d m * (16 * d / ((2 * (4 * (4 ^ d * (2 * m)) + 6) + 2 : ℕ) : ℝ) ^ 2)

theorem fourthDiffCoeff_nonneg (d m : ℕ) : 0 ≤ fourthDiffCoeff d m := by
  have := thirdDiffCoeff_nonneg d m
  unfold fourthDiffCoeff; positivity

/-- **Fourth differences of lattice harmonic functions.** -/
theorem sq_fwd4_le (f : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) {m : ℕ} (hm : 0 < m)
    (hf : ∀ x ∈ supBox z (2 * (2 * (4 * (4 ^ d * (2 * m)) + 6) + 2)), latticeLaplacian f x = 0)
    (a b e g : Fin d) {x₀ : Fin d → ℤ} (hx₀ : x₀ ∈ supBox z m) :
    fwd g (fwd e (fwd a (fwd b f))) x₀ ^ 2 ≤
      fourthDiffCoeff d m *
        ∑ x ∈ supBox z (2 * (2 * (4 * (4 ^ d * (2 * m)) + 6) + 2) + 2), f x ^ 2 := by
  set ρ := 4 ^ d * (2 * m) with hρ
  have hL0 : 0 < 2 * (4 * ρ + 6) + 2 := by omega
  have hfg : ∀ x ∈ supBox z (4 * (4 * ρ + 4) + 5), latticeLaplacian (fwd g f) x = 0 :=
    latticeLaplacian_fwd_eq_zero (fun x hx => hf x (by
      rw [mem_supBox_iff_supDist_le] at hx ⊢; omega)) g
  have h1 := sq_fwd_fwd_fwd_le (fwd g f) z hm (by rw [← hρ]; exact hfg) a b e hx₀
  have hcomm : fwd g (fwd e (fwd a (fwd b f))) = fwd e (fwd a (fwd b (fwd g f))) := by
    rw [fwd_comm g e, fwd_comm g a, fwd_comm g b]
  rw [hcomm]
  have h2 := sum_sq_fwd_le f z hL0 (fun x hx => hf x hx) g
  have hc : 0 ≤ secondDiffCoeff d m * (16 * d / ((4 * ρ + 6 : ℕ) : ℝ) ^ 2) := by
    have := secondDiffCoeff_nonneg d m; positivity
  calc fwd e (fwd a (fwd b (fwd g f))) x₀ ^ 2
      ≤ secondDiffCoeff d m * (16 * d / ((4 * ρ + 6 : ℕ) : ℝ) ^ 2 *
          ∑ x ∈ supBox z (2 * (4 * ρ + 6) + 2), fwd g f x ^ 2) := h1
    _ = secondDiffCoeff d m * (16 * d / ((4 * ρ + 6 : ℕ) : ℝ) ^ 2) *
          ∑ x ∈ supBox z (2 * (4 * ρ + 6) + 2), fwd g f x ^ 2 := by ring
    _ ≤ secondDiffCoeff d m * (16 * d / ((4 * ρ + 6 : ℕ) : ℝ) ^ 2) *
          (16 * d / ((2 * (4 * ρ + 6) + 2 : ℕ) : ℝ) ^ 2 *
            ∑ x ∈ supBox z (2 * (2 * (4 * ρ + 6) + 2) + 2), f x ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by rw [fourthDiffCoeff, thirdDiffCoeff, ← hρ]; ring

/-- The constant of `fourthDiffCoeff_le`. -/
noncomputable def fourthDiffConst (d : ℕ) : ℝ :=
  4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 * (16 * d) * (16 * d)

theorem fourthDiffConst_nonneg (d : ℕ) : 0 ≤ fourthDiffConst d := by
  unfold fourthDiffConst; positivity

theorem fourthDiffCoeff_le (d : ℕ) {m : ℕ} (hm : 0 < m) :
    fourthDiffCoeff d m ≤ fourthDiffConst d / (m : ℝ) ^ (d + 8) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : (m : ℝ) ≤ ((2 * (4 * (4 ^ d * (2 * m)) + 6) + 2 : ℕ) : ℝ) := by
    have : m ≤ 2 * (4 * (4 ^ d * (2 * m)) + 6) + 2 := by
      have := Nat.one_le_pow d 4 (by norm_num); nlinarith
    exact_mod_cast this
  have h1 := thirdDiffCoeff_le d hm
  have h2 : 16 * (d : ℝ) / ((2 * (4 * (4 ^ d * (2 * m)) + 6) + 2 : ℕ) : ℝ) ^ 2 ≤
      16 * d / (m : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hm'.le hL 2)
  rw [fourthDiffCoeff, fourthDiffConst]
  calc thirdDiffCoeff d m * (16 * d / ((2 * (4 * (4 ^ d * (2 * m)) + 6) + 2 : ℕ) : ℝ) ^ 2)
      ≤ 4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 * (16 * d) / (m : ℝ) ^ (d + 6) *
          (16 * d / (m : ℝ) ^ 2) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by rw [pow_add, pow_add]; field_simp

/-! ### The third-order expansion in the plane -/

/-- The third differences of `f` at `c`, as the coefficients of `cubicPart`. -/
noncomputable def taylorCubic (f : (Fin 2 → ℤ) → ℝ) (c : Fin 2 → ℤ) : (Fin 2 → ℤ) → ℝ :=
  cubicPart (fwd 0 (fwd 0 (fwd 0 f)) c) (fwd 0 (fwd 0 (fwd 1 f)) c) (fwd 0 (fwd 1 (fwd 1 f)) c)
    (fwd 1 (fwd 1 (fwd 1 f)) c) c

/-- The correction of `taylorCubic f c`, removing the trace of the third differences. -/
noncomputable def taylorCorr (f : (Fin 2 → ℤ) → ℝ) (c : Fin 2 → ℤ) : (Fin 2 → ℤ) → ℝ :=
  cubicCorr (fwd 0 (fwd 0 (fwd 0 f)) c + fwd 0 (fwd 1 (fwd 1 f)) c)
    (fwd 0 (fwd 0 (fwd 1 f)) c + fwd 1 (fwd 1 (fwd 1 f)) c) c

/-- The harmonic second-order expansion at `c` of `abs_sub_harmonicTaylor_two_le`. -/
noncomputable def harmonicTaylorTwo (g : (Fin 2 → ℤ) → ℝ) (c : Fin 2 → ℤ) (y : Fin 2 → ℤ) : ℝ :=
  halfQuad (harmHess g c) c y + (g c - halfQuad (hessAt g c) c c) +
    ∑ i, ((y i - c i : ℤ) : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c

/-- The remainder `f - taylorCubic f c`. -/
noncomputable def taylorRest (f : (Fin 2 → ℤ) → ℝ) (c : Fin 2 → ℤ) (y : Fin 2 → ℤ) : ℝ :=
  f y - taylorCubic f c y

/-- **The harmonic third-order expansion** of `f` at `c`. -/
noncomputable def harmonicTaylorThree (f : (Fin 2 → ℤ) → ℝ) (c : Fin 2 → ℤ) (y : Fin 2 → ℤ) :
    ℝ :=
  taylorCubic f c y - taylorCorr f c y + harmonicTaylorTwo (taylorRest f c) c y

theorem fwd_fwd_fwd_eq_cubicCoeff (f : (Fin 2 → ℤ) → ℝ) (c : Fin 2 → ℤ) (a b e : Fin 2) :
    fwd a (fwd b (fwd e f)) c =
      cubicCoeff (fwd 0 (fwd 0 (fwd 0 f)) c) (fwd 0 (fwd 0 (fwd 1 f)) c)
        (fwd 0 (fwd 1 (fwd 1 f)) c) (fwd 1 (fwd 1 (fwd 1 f)) c) (a.val + b.val + e.val) := by
  have h1 : fwd 0 (fwd 1 (fwd 0 f)) = fwd 0 (fwd 0 (fwd 1 f)) := by rw [fwd_comm 1 0]
  have h2 : fwd 1 (fwd 0 (fwd 0 f)) = fwd 0 (fwd 0 (fwd 1 f)) := by
    rw [fwd_comm 1 0, fwd_comm 1 0]
  have h3 : fwd 1 (fwd 0 (fwd 1 f)) = fwd 0 (fwd 1 (fwd 1 f)) := by rw [fwd_comm 1 0]
  have h4 : fwd 1 (fwd 1 (fwd 0 f)) = fwd 0 (fwd 1 (fwd 1 f)) := by
    rw [fwd_comm 1 0, fwd_comm 1 0]
  fin_cases a <;> fin_cases b <;> fin_cases e <;> simp [cubicCoeff, h1, h2, h3, h4]

/-- The third differences of the remainder `f - taylorCubic f c`. -/
theorem fwd_fwd_fwd_taylorRest (f : (Fin 2 → ℤ) → ℝ) (c : Fin 2 → ℤ) (a b e : Fin 2)
    (y : Fin 2 → ℤ) :
    fwd e (fwd a (fwd b (taylorRest f c))) y =
      fwd e (fwd a (fwd b f)) y - fwd e (fwd a (fwd b f)) c := by
  show fwd e (fwd a (fwd b (fun y => f y - taylorCubic f c y))) y = _
  rw [fwd_sub, fwd_sub, fwd_sub]
  show fwd e (fwd a (fwd b f)) y - fwd e (fwd a (fwd b (taylorCubic f c))) y = _
  rw [taylorCubic, fwd_fwd_fwd_cubicPart, fwd_fwd_fwd_eq_cubicCoeff f c e a b]

/-- **The harmonic third-order expansion is a lattice harmonic cubic polynomial.** -/
theorem mem_latticeHarmonicCubic_harmonicTaylorThree (f : (Fin 2 → ℤ) → ℝ) (c : Fin 2 → ℤ) :
    (fun x : latticeComponent 2 => harmonicTaylorThree f c x.val) ∈ latticeHarmonicCubic := by
  set g : (Fin 2 → ℤ) → ℝ := taylorRest f c with hg
  have hK : (fun x : latticeComponent 2 => taylorCubic f c x.val - taylorCorr f c x.val) ∈
      latticeHarmonicCubic := by
    refine ⟨(isLatticeCubic_cubicPart _ _ _ _ c).sub (isLatticeCubic_cubicCorr _ _ c),
      fun y => ?_⟩
    have e : latticeExt (fun x : latticeComponent 2 => taylorCubic f c x.val -
        taylorCorr f c x.val) = fun y => taylorCubic f c y - taylorCorr f c y := rfl
    rw [e, latticeLaplacian_sub, taylorCubic, taylorCorr, latticeLaplacian_cubicPart,
      latticeLaplacian_cubicCorr, sub_self]
  have hQ : (fun x : latticeComponent 2 => halfQuad (harmHess g c) c x.val) ∈
      latticeHarmonicQuadratic 2 :=
    ⟨halfQuad_mem_clusterQuadratic (harmHess g c) c,
      fun y => latticeLaplacian_halfQuad_harmHess (by norm_num) g c y⟩
  set q : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 fun i => fwd i (fun y => g y - halfQuad (hessAt g c) c y) c with hq
  set α := (g c - halfQuad (hessAt g c) c c) -
    ∑ i, (c i : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c with hα
  have hA : (fun x : latticeComponent 2 => α + inner ℝ q (latticeEuclideanEmbedding x.val)) ∈
      latticeHarmonicQuadratic 2 :=
    clusterAffine_le_latticeHarmonicQuadratic ⟨α, q, fun _ => rfl⟩
  have hsum := latticeHarmonicCubic.add_mem (latticeHarmonicCubic.add_mem hK
    (latticeHarmonicQuadratic_le_latticeHarmonicCubic hQ))
    (latticeHarmonicQuadratic_le_latticeHarmonicCubic hA)
  convert hsum using 1
  funext x
  have hinner : inner ℝ q (latticeEuclideanEmbedding x.val) =
      ∑ i, (x.val i : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c := by
    rw [inner_eq_sum]
    exact sum_congr rfl fun i _ => mul_comm _ _
  have hsplit : ∑ i, ((x.val i - c i : ℤ) : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c =
      ∑ i, (x.val i : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c -
        ∑ i, (c i : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by push_cast; ring
  show harmonicTaylorThree f c x.val = taylorCubic f c x.val - taylorCorr f c x.val +
    halfQuad (harmHess g c) c x.val + (α + inner ℝ q (latticeEuclideanEmbedding x.val))
  rw [harmonicTaylorThree, harmonicTaylorTwo, ← hg, hinner, hα, hsplit]
  ring

/-- **Harmonic third-order expansion on `ℤ²`**: if `f` is harmonic at `c`, `c + e₀`, `c + e₁`
and its fourth forward differences are bounded by `M₄` on the box `[c - 𝟙, x]`, `x - c ≤ S 𝟙`,
then `|f(x) - harmonicTaylorThree f c x| ≤ 29 S⁴ M₄`. -/
theorem abs_sub_harmonicTaylorThree_le (f : (Fin 2 → ℤ) → ℝ) {c x : Fin 2 → ℤ}
    (hcx : ∀ i, c i ≤ x i) {S : ℕ} (hS : 1 ≤ S) (hs : ∀ i, x i - c i ≤ S) {M₄ : ℝ}
    (hM₀ : 0 ≤ M₄)
    (hM : ∀ y : Fin 2 → ℤ, (∀ i, c i - 1 ≤ y i ∧ y i ≤ x i) →
      ∀ a b e g, |fwd g (fwd e (fwd a (fwd b f))) y| ≤ M₄)
    (hΔ : latticeLaplacian f c = 0) (hΔ₀ : latticeLaplacian f (c + unit 0) = 0)
    (hΔ₁ : latticeLaplacian f (c + unit 1) = 0) :
    |f x - harmonicTaylorThree f c x| ≤ 29 * S ^ 4 * M₄ := by
  set g : (Fin 2 → ℤ) → ℝ := taylorRest f c with hg
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hS0 : (0 : ℝ) ≤ S := by linarith
  set M₃ := 2 * (S : ℝ) * M₄ with hM₃
  have hM₃0 : 0 ≤ M₃ := by positivity
  have hM₄M₃ : M₄ ≤ M₃ := by rw [hM₃]; nlinarith
  -- third differences of the remainder on the box `[c, x]`
  have hMg : ∀ y : Fin 2 → ℤ, (∀ i, c i ≤ y i ∧ y i ≤ x i) →
      ∀ a b e, |fwd e (fwd a (fwd b g)) y| ≤ M₃ := by
    intro y hy a b e
    rw [hg, fwd_fwd_fwd_taylorRest]
    have hcy : ∀ i, c i ≤ y i := fun i => (hy i).1
    have hsy : ∀ i, y i - c i ≤ S := fun i => by have := hs i; have := (hy i).2; omega
    have h := abs_cornerPoint_sub_le (fwd e (fwd a (fwd b f))) hcy hsy hM₀
      (fun y' hy' i => hM y' (fun j => ⟨by have := (hy' j).1; omega,
        by have := (hy' j).2; have := (hy j).2; omega⟩) a b e i) univ
    rw [cornerPoint_univ, card_univ, Fintype.card_fin] at h
    calc |fwd e (fwd a (fwd b f)) y - fwd e (fwd a (fwd b f)) c|
        ≤ ((2 : ℕ) : ℝ) * S * M₄ := h
      _ = M₃ := by rw [hM₃]; norm_num
  -- the points `c - eₐ`
  have hbox0 : ∀ a : Fin 2, ∀ i, c i - 1 ≤ (c - unit a) i ∧ (c - unit a) i ≤ x i := by
    intro a i
    have hci := hcx i
    by_cases hia : i = a
    · subst hia
      simp only [unit, Pi.sub_apply, Pi.single_eq_same]
      omega
    · simp only [unit, Pi.sub_apply, Pi.single_eq_of_ne hia]
      omega
  -- the third differences of the remainder at `c - eₐ`
  have hMc : ∀ a, |fwd a (fwd a (fwd a g)) (c - unit a)| ≤ M₃ := by
    intro a
    rw [hg, fwd_fwd_fwd_taylorRest]
    have e1 : fwd a (fwd a (fwd a f)) (c - unit a) - fwd a (fwd a (fwd a f)) c =
        -fwd a (fwd a (fwd a (fwd a f))) (c - unit a) := by
      simp only [fwd, sub_add_cancel]; ring
    rw [e1, abs_neg]
    exact (hM (c - unit a) (hbox0 a) a a a a).trans hM₄M₃
  -- the remainder is harmonic at `c`
  have hΔg : latticeLaplacian g c = 0 := by
    show latticeLaplacian (fun y => f y - taylorCubic f c y) c = 0
    rw [latticeLaplacian_sub, hΔ, taylorCubic, latticeLaplacian_cubicPart]
    simp
  have h2 := abs_sub_harmonicTaylor_two_le (d := 2) (by norm_num) g hcx hs hM₃0 hMg hMc hΔg
  -- the correction is small
  have hσ₀ : |fwd 0 (fwd 0 (fwd 0 f)) c + fwd 0 (fwd 1 (fwd 1 f)) c| ≤ 2 * M₄ := by
    have hΔ' : latticeLaplacian (fwd 0 f) c = 0 := by
      rw [latticeLaplacian_fwd, hΔ₀, hΔ, sub_zero]
    have h := sum_hessAt_eq (fwd 0 f) c hΔ'
    simp only [hessAt, Fin.sum_univ_two] at h
    have e : fwd 0 (fwd 1 (fwd 1 f)) = fwd 1 (fwd 1 (fwd 0 f)) := by
      rw [fwd_comm 0 1, fwd_comm 0 1]
    rw [e, h]
    have hc0 := hM (c - unit 0) (hbox0 0) 0 0 0 0
    have hc1 := hM (c - unit 1) (hbox0 1) 1 0 1 1
    calc |fwd 0 (fwd 0 (fwd 0 (fwd 0 f))) (c - unit 0) + fwd 1 (fwd 1 (fwd 1 (fwd 0 f))) (c - unit 1)|
        ≤ |fwd 0 (fwd 0 (fwd 0 (fwd 0 f))) (c - unit 0)| +
            |fwd 1 (fwd 1 (fwd 1 (fwd 0 f))) (c - unit 1)| := abs_add_le _ _
      _ ≤ M₄ + M₄ := add_le_add hc0 hc1
      _ = 2 * M₄ := by ring
  have hσ₁ : |fwd 0 (fwd 0 (fwd 1 f)) c + fwd 1 (fwd 1 (fwd 1 f)) c| ≤ 2 * M₄ := by
    have hΔ' : latticeLaplacian (fwd 1 f) c = 0 := by
      rw [latticeLaplacian_fwd, hΔ₁, hΔ, sub_zero]
    have h := sum_hessAt_eq (fwd 1 f) c hΔ'
    simp only [hessAt, Fin.sum_univ_two] at h
    rw [h]
    have hc0 := hM (c - unit 0) (hbox0 0) 0 1 0 0
    have hc1 := hM (c - unit 1) (hbox0 1) 1 1 1 1
    calc |fwd 0 (fwd 0 (fwd 0 (fwd 1 f))) (c - unit 0) + fwd 1 (fwd 1 (fwd 1 (fwd 1 f))) (c - unit 1)|
        ≤ |fwd 0 (fwd 0 (fwd 0 (fwd 1 f))) (c - unit 0)| +
            |fwd 1 (fwd 1 (fwd 1 (fwd 1 f))) (c - unit 1)| := abs_add_le _ _
      _ ≤ M₄ + M₄ := add_le_add hc0 hc1
      _ = 2 * M₄ := by ring
  have hcorr : |taylorCorr f c x| ≤ M₄ * S ^ 3 := by
    have h := abs_cubicCorr_le (fwd 0 (fwd 0 (fwd 0 f)) c + fwd 0 (fwd 1 (fwd 1 f)) c)
      (fwd 0 (fwd 0 (fwd 1 f)) c + fwd 1 (fwd 1 (fwd 1 f)) c) (c := c) (y := x) (S := (S : ℝ))
      (fun i => by
        have h1 := hcx i
        have h2 := hs i
        rw [abs_le]
        constructor
        · have : (0 : ℝ) ≤ ((x i - c i : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ x i - c i)
          linarith
        · exact_mod_cast h2)
    rw [taylorCorr]
    refine h.trans ?_
    have hS3 : (0 : ℝ) ≤ (S : ℝ) ^ 3 := by positivity
    have := add_le_add hσ₀ hσ₁
    calc (|fwd 0 (fwd 0 (fwd 0 f)) c + fwd 0 (fwd 1 (fwd 1 f)) c| +
          |fwd 0 (fwd 0 (fwd 1 f)) c + fwd 1 (fwd 1 (fwd 1 f)) c|) * (S : ℝ) ^ 3 / 4
        ≤ (2 * M₄ + 2 * M₄) * (S : ℝ) ^ 3 / 4 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hS3) (by norm_num)
      _ = M₄ * S ^ 3 := by ring
  -- assemble
  have e : f x - harmonicTaylorThree f c x =
      (g x - harmonicTaylorTwo g c x) + taylorCorr f c x := by
    rw [hg]
    simp only [harmonicTaylorThree, taylorRest]
    ring
  rw [e]
  have h2' : |g x - harmonicTaylorTwo g c x| ≤
      ((2 : ℕ) : ℝ) * ((2 : ℕ) + 1) * S ^ 2 * ((2 : ℕ) * S * M₃) + (2 : ℕ) * S ^ 2 * M₃ := h2
  have hS3 : (S : ℝ) ^ 3 ≤ S ^ 4 := pow_le_pow_right₀ hS1 (by norm_num)
  have hS2 : (S : ℝ) ^ 2 * S ≤ S ^ 4 := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hS1 (by norm_num)
  calc |(g x - harmonicTaylorTwo g c x) + taylorCorr f c x|
      ≤ |g x - harmonicTaylorTwo g c x| + |taylorCorr f c x| := abs_add_le _ _
    _ ≤ ((2 : ℕ) : ℝ) * ((2 : ℕ) + 1) * S ^ 2 * ((2 : ℕ) * S * M₃) + (2 : ℕ) * S ^ 2 * M₃ +
          M₄ * S ^ 3 := add_le_add h2' hcorr
    _ = 24 * S ^ 4 * M₄ + 4 * (S ^ 2 * S) * M₄ + M₄ * S ^ 3 := by rw [hM₃]; push_cast; ring
    _ ≤ 24 * S ^ 4 * M₄ + 4 * S ^ 4 * M₄ + M₄ * S ^ 4 := by
        have h1 := mul_le_mul_of_nonneg_right hS2 hM₀
        have h3 := mul_le_mul_of_nonneg_left hS3 hM₀
        linarith
    _ = 29 * S ^ 4 * M₄ := by ring

/-! ### The excess decay of order three -/

theorem latticeExt_apply (v : latticeComponent 2 → ℝ) (x : latticeComponent 2) :
    latticeExt v x.val = v x :=
  rfl

/-- **Excess decay of order three below the interior scale.** -/
theorem ballExcess_three_le_of_latticeHarmonic (z : Vertex 2) {r s : ℝ} {m : ℕ} (hm : 0 < m)
    (hbox : Real.sqrt 2 * ((512 * m + 30 : ℕ) : ℝ) < r) (hsm : s + 1 ≤ m) (hs1 : 1 ≤ s)
    {v : latticeComponent 2 → ℝ} (hv : v ∈ latticeHarmonicClass z r)
    {w : latticeComponent 2 → ℝ} (hw : w ∈ latticeHarmonicCubic) :
    ballExcess (componentBallSeminorm (latticeComponent 2) z) latticeHarmonicCubic s v ≤
      29 * (2 * s) ^ 4 * Real.sqrt (fourthDiffCoeff 2 m *
        (((componentEuclideanBall (latticeComponent 2) z r).card : ℝ) *
          componentBallL2 (latticeComponent 2) z r (v - w) ^ 2)) := by
  classical
  obtain ⟨F, hvF, hF⟩ := hv
  have hW := hw.2
  set f : (Fin 2 → ℤ) → ℝ := fun y => F y - latticeExt w y with hfdef
  have e2 : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
  have hf : ∀ x ∈ supBox z (512 * m + 30), latticeLaplacian f x = 0 := by
    intro x hx
    rw [hfdef, latticeLaplacian_sub, hW x, sub_zero]
    have := dist_le_of_mem_supBox hx
    rw [e2] at this
    exact hF x (this.trans_lt hbox)
  have hs0 : 0 ≤ s := by linarith
  set n := ⌊s⌋₊ with hn
  have hns : (n : ℝ) ≤ s := Nat.floor_le hs0
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hs1)
  have hnm : n + 1 ≤ m := by
    have : ((n + 1 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  set M := Real.sqrt (fourthDiffCoeff 2 m * ∑ y ∈ supBox z (512 * m + 30), f y ^ 2) with hMdef
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have e4 : 4 ^ 2 * (2 * m) = 32 * m := by ring
  have hM : ∀ y ∈ supBox z m, ∀ a b e g, |fwd g (fwd e (fwd a (fwd b f))) y| ≤ M := by
    intro y hy a b e g
    apply Real.abs_le_sqrt
    have h := sq_fwd4_le (d := 2) f z hm (by
      rw [e4]
      exact fun x hx => hf x (by rw [mem_supBox_iff_supDist_le] at hx ⊢; omega)) a b e g hy
    rw [e4, show 2 * (2 * (4 * (32 * m) + 6) + 2) + 2 = 512 * m + 30 by ring] at h
    exact h
  set c : Fin 2 → ℤ := fun i => z i - n with hc
  have hcn : c ∈ supBox z n := corner_mem_supBox z n
  have hΔc : latticeLaplacian f c = 0 := hf c (by
    rw [mem_supBox_iff_supDist_le] at hcn ⊢; omega)
  have hΔc0 : latticeLaplacian f (c + unit 0) = 0 := hf _ (by
    rw [mem_supBox_iff_supDist_le] at hcn ⊢
    have := supDist_add_unit_le' c z 0; omega)
  have hΔc1 : latticeLaplacian f (c + unit 1) = 0 := hf _ (by
    rw [mem_supBox_iff_supDist_le] at hcn ⊢
    have := supDist_add_unit_le' c z 1; omega)
  have hP := mem_latticeHarmonicCubic_harmonicTaylorThree f c
  have hsum := latticeHarmonicCubic.add_mem hw hP
  refine (ballExcess_le _ _ hsum).trans ?_
  rw [componentBallSeminorm_apply]
  have hbound : 0 ≤ 29 * ((2 * n : ℕ) : ℝ) ^ 4 * M := by positivity
  refine (componentBallL2_le_of_abs_le (latticeComponent 2) z s hbound ?_).trans ?_
  · intro x hx
    have hxz := abs_sub_le_floor_of_mem_ball hx
    have hcx : ∀ i, c i ≤ x.val i := fun i => by
      have := abs_le.1 (hxz i); simp only [hc]; rw [← hn] at this; omega
    have hs2 : ∀ i, x.val i - c i ≤ (2 * n : ℕ) := fun i => by
      have := abs_le.1 (hxz i); simp only [hc]; rw [← hn] at this; push_cast; omega
    have htay := abs_sub_harmonicTaylorThree_le f hcx (S := 2 * n) (by omega) hs2 hM0
      (fun y hy a b e g => hM y (by
        simp only [supBox, Fintype.mem_piFinset, mem_Icc]
        intro i
        have h1 := hy i
        have h2 := abs_le.1 (hxz i)
        simp only [hc] at h1
        rw [← hn] at h2
        constructor <;> omega) a b e g) hΔc hΔc0 hΔc1
    have hval : (v - (w + fun x : latticeComponent 2 => harmonicTaylorThree f c x.val)) x =
        f x.val - harmonicTaylorThree f c x.val := by
      show v x - (w x + harmonicTaylorThree f c x.val) = F x.val - latticeExt w x.val -
        harmonicTaylorThree f c x.val
      rw [hvF, latticeExt_apply]
      ring
    rw [hval]
    exact htay
  · have ht : ((2 * n : ℕ) : ℝ) ≤ 2 * s := by push_cast; linarith
    have ht0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : ((2 * n : ℕ) : ℝ) ^ 4 ≤ (2 * s) ^ 4 := pow_le_pow_left₀ ht0 ht 4
    have hMle : M ≤ Real.sqrt (fourthDiffCoeff 2 m *
        (((componentEuclideanBall (latticeComponent 2) z r).card : ℝ) *
          componentBallL2 (latticeComponent 2) z r (v - w) ^ 2)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (fourthDiffCoeff_nonneg 2 m)
      rw [← sum_sq_eq_card_mul_componentBallL2_sq]
      have hL : Real.sqrt ((2 : ℕ) : ℝ) * ((512 * m + 30 : ℕ) : ℝ) < r := by rw [e2]; exact hbox
      have hball := sum_sq_supBox_le_ball z hL f
      refine hball.trans (le_of_eq (sum_congr rfl fun x _ => ?_))
      rw [Pi.sub_apply, hvF]
      rfl
    calc 29 * ((2 * n : ℕ) : ℝ) ^ 4 * M ≤ 29 * (2 * s) ^ 4 * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num)) hM0
      _ ≤ _ := mul_le_mul_of_nonneg_left hMle (by positivity)

/-- The lower radius `X₃ = 2 √2 · 542` of the excess decay of order three. -/
noncomputable def latticeHRScaleThree : ℝ := 2 * Real.sqrt 2 * 542

/-- The constant of the excess decay of order three of lattice harmonic functions. -/
noncomputable def latticeHRConstThree : ℝ :=
  29 * 16 * Real.sqrt (fourthDiffConst 2 * 5 ^ 2 * (2 * latticeHRScaleThree) ^ (2 + 8)) +
    Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) *
      (2 * (2 * latticeHRScaleThree)) ^ (((2 : ℕ) : ℝ) / 2) * (2 * (2 * latticeHRScaleThree)) ^ 4

theorem latticeHRScaleThree_pos : 0 < latticeHRScaleThree := by
  unfold latticeHRScaleThree; positivity

theorem latticeHRConstThree_nonneg : 0 ≤ latticeHRConstThree := by
  have := latticeHRScaleThree_pos
  rw [latticeHRConstThree]; positivity

/-- **Excess decay of order three, against one harmonic cubic polynomial.** -/
theorem ballExcess_le_latticeHRConstThree_mul (z : Vertex 2) {R r s : ℝ} (hrR : r ≤ R)
    {v : latticeComponent 2 → ℝ} (hv : v ∈ latticeHarmonicClass z r)
    (hXs : latticeHRScaleThree ≤ s) (hsr : s ≤ r / 2) {w : latticeComponent 2 → ℝ}
    (hw : w ∈ latticeHarmonicCubic) :
    ballExcess (componentBallSeminorm (latticeComponent 2) z) latticeHarmonicCubic s v ≤
      latticeHRConstThree * (s / r) ^ 4 * componentBallL2 (latticeComponent 2) z r (v - w) := by
  have hsd1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  set X₀ := latticeHRScaleThree with hX₀
  have hX₀def : X₀ = 2 * Real.sqrt 2 * 542 := rfl
  have hX₀pos : 0 < X₀ := latticeHRScaleThree_pos
  set B := 2 * X₀ with hB
  have hBpos : 0 < B := by positivity
  have hs0 : 0 < s := hX₀pos.trans_le hXs
  have hX₀1 : 1 ≤ X₀ := by rw [hX₀def]; nlinarith
  have hs1 : 1 ≤ s := hX₀1.trans hXs
  have hr2 : 2 * X₀ ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  set N := componentBallL2 (latticeComponent 2) z r (v - w) with hN
  have hN0 : 0 ≤ N := componentBallL2_nonneg _ _ _ _
  set m := ⌊r / X₀⌋₊ with hmdef
  have hrX : 2 ≤ r / X₀ := by rw [le_div_iff₀ hX₀pos]; linarith
  have hm2 : 2 ≤ m := Nat.le_floor (by exact_mod_cast hrX)
  have hm0 : 0 < m := by omega
  have hmle : (m : ℝ) ≤ r / X₀ := Nat.floor_le (by positivity)
  have hmge : r / B ≤ m := by
    have h1 := Nat.lt_floor_add_one (r / X₀)
    rw [← hmdef] at h1
    have : r / B = r / X₀ / 2 := by rw [hB]; field_simp
    rw [this]; linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have hbox : Real.sqrt 2 * ((512 * m + 30 : ℕ) : ℝ) < r := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have h1 : ((512 * m + 30 : ℕ) : ℝ) ≤ 542 * m := by push_cast; linarith
    have h2 : (542 : ℝ) * m ≤ 542 * (r / X₀) := mul_le_mul_of_nonneg_left hmle (by norm_num)
    have h3 : Real.sqrt 2 * (542 * (r / X₀)) = r / 2 := by
      rw [hX₀def]; field_simp
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : 0 ≤ Real.sqrt 2)
    linarith
  have hCH1 : 0 ≤ 29 * 16 * Real.sqrt (fourthDiffConst 2 * 5 ^ 2 * B ^ (2 + 8)) := by
    positivity
  have hCH2 : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) *
      (2 * B) ^ (((2 : ℕ) : ℝ) / 2) * (2 * B) ^ 4 := by
    positivity
  have hsr4 : 0 ≤ (s / r) ^ 4 := by positivity
  by_cases hsm : s + 1 ≤ m
  · have h := ballExcess_three_le_of_latticeHarmonic z hm0 hbox hsm hs1 hv hw
    refine h.trans ?_
    set K₀ : ℝ := fourthDiffConst 2 with hK₀
    have hK₀0 : 0 ≤ K₀ := fourthDiffConst_nonneg 2
    have hcoef := fourthDiffCoeff_le 2 hm0
    have hcard : ((componentEuclideanBall (latticeComponent 2) z r).card : ℝ) ≤ (5 * r) ^ 2 :=
      (card_componentEuclideanBall_le _ z hr0.le).trans
        (pow_le_pow_left₀ (by linarith) (by linarith) 2)
    have hinv : 1 / (m : ℝ) ^ (2 + 8) ≤ (B / r) ^ (2 + 8) := by
      rw [one_div, ← inv_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_le_comm₀ hmpos (by positivity), inv_div]
      exact hmge
    have hin : fourthDiffCoeff 2 m *
        (((componentEuclideanBall (latticeComponent 2) z r).card : ℝ) * N ^ 2) ≤
        (K₀ * 5 ^ 2 * B ^ (2 + 8)) * (N / r ^ 4) ^ 2 := by
      calc fourthDiffCoeff 2 m *
            (((componentEuclideanBall (latticeComponent 2) z r).card : ℝ) * N ^ 2)
          ≤ K₀ / (m : ℝ) ^ (2 + 8) * ((5 * r) ^ 2 * N ^ 2) :=
            mul_le_mul hcoef (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)) (by positivity)
              (by positivity)
        _ ≤ K₀ * (B / r) ^ (2 + 8) * ((5 * r) ^ 2 * N ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_left hinv hK₀0
        _ = (K₀ * 5 ^ 2 * B ^ (2 + 8)) * (N / r ^ 4) ^ 2 := by
            rw [div_pow, div_pow, mul_pow]
            field_simp
    have hsq : Real.sqrt (fourthDiffCoeff 2 m *
        (((componentEuclideanBall (latticeComponent 2) z r).card : ℝ) * N ^ 2)) ≤
        Real.sqrt (K₀ * 5 ^ 2 * B ^ (2 + 8)) * (N / r ^ 4) := by
      calc _ ≤ Real.sqrt ((K₀ * 5 ^ 2 * B ^ (2 + 8)) * (N / r ^ 4) ^ 2) := Real.sqrt_le_sqrt hin
        _ = _ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc 29 * (2 * s) ^ 4 * Real.sqrt (fourthDiffCoeff 2 m *
          (((componentEuclideanBall (latticeComponent 2) z r).card : ℝ) * N ^ 2))
        ≤ 29 * (2 * s) ^ 4 * (Real.sqrt (K₀ * 5 ^ 2 * B ^ (2 + 8)) * (N / r ^ 4)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 29 * 16 * Real.sqrt (K₀ * 5 ^ 2 * B ^ (2 + 8)) * (s / r) ^ 4 * N := by
          field_simp
          ring
      _ ≤ latticeHRConstThree * (s / r) ^ 4 * N := by
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul_of_nonneg_right _ hsr4
          rw [latticeHRConstThree, ← hX₀, ← hB, ← hK₀]
          linarith
  · push Not at hsm
    have hm2s : (m : ℝ) < 2 * s := by linarith
    have hsm' : r / B < 2 * s := lt_of_le_of_lt hmge hm2s
    have hvol := clusterBallVolumeComparison_of_clusterCubeDensity (latticeComponent 2) z R
      (by norm_num) one_pos
      (clusterCubeDensity_latticeComponent z (24 * Real.sqrt ((2 : ℕ) : ℝ)) 1)
    have h6 : 6 * Real.sqrt ((2 : ℕ) : ℝ) * max 1 1 ≤ s := by
      rw [max_self, mul_one]
      have e2 : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
      rw [e2]
      have : 6 * Real.sqrt 2 ≤ X₀ := by rw [hX₀def]; nlinarith
      linarith
    have hmono := radiusMonotone_componentBallSeminorm (latticeComponent 2) z
      (by positivity : (0 : ℝ) < 6 * Real.sqrt ((2 : ℕ) : ℝ) * max 1 1) (by positivity) hvol
    have h1 := ballExcess_le (componentBallSeminorm (latticeComponent 2) z)
      latticeHarmonicCubic (s := s) (u := v) hw
    have h2 := hmono (v - w) s r h6 (by linarith) hrR
    rw [componentBallSeminorm_apply, componentBallSeminorm_apply] at h2
    rw [componentBallSeminorm_apply] at h1
    have h2B : 0 < 2 * B := by positivity
    have hrs : r / s ≤ 2 * B := by
      rw [div_le_iff₀ hs0]; rw [div_lt_iff₀ hBpos] at hsm'; linarith
    have hrs0 : 0 ≤ r / s := by positivity
    have h3 : (r / s) ^ (((2 : ℕ) : ℝ) / 2) ≤ (2 * B) ^ (((2 : ℕ) : ℝ) / 2) :=
      Real.rpow_le_rpow hrs0 hrs (by positivity)
    have h4 : 1 ≤ (2 * B) ^ 4 * (s / r) ^ 4 := by
      rw [← mul_pow]
      have : 1 ≤ 2 * B * (s / r) := by
        rw [div_lt_iff₀ hBpos] at hsm'
        rw [mul_div_assoc', le_div_iff₀ hr0]; linarith
      exact one_le_pow₀ this
    have hK : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) := Real.sqrt_nonneg _
    calc ballExcess (componentBallSeminorm (latticeComponent 2) z) latticeHarmonicCubic s v
        ≤ Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) *
            (r / s) ^ (((2 : ℕ) : ℝ) / 2) * N := h1.trans h2
      _ ≤ Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) *
            (2 * B) ^ (((2 : ℕ) : ℝ) / 2) * N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hK) hN0
      _ ≤ Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) *
            (2 * B) ^ (((2 : ℕ) : ℝ) / 2) * ((2 * B) ^ 4 * (s / r) ^ 4) * N := by
          have h5 : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) *
              (2 * B) ^ (((2 : ℕ) : ℝ) / 2) * N := by positivity
          nlinarith
      _ ≤ latticeHRConstThree * (s / r) ^ 4 * N := by
          have e : Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) *
              (2 * B) ^ (((2 : ℕ) : ℝ) / 2) * ((2 * B) ^ 4 * (s / r) ^ 4) * N =
              (Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) *
                (2 * B) ^ (((2 : ℕ) : ℝ) / 2) * (2 * B) ^ 4) * (s / r) ^ 4 * N := by ring
          rw [e]
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul_of_nonneg_right _ hsr4
          rw [latticeHRConstThree, ← hX₀, ← hB]
          exact le_add_of_nonneg_left hCH1

/-- **Excess decay of order three of lattice harmonic functions on the balls of `ℤ²`**:
`HarmonicRegularity` with `j = 3` for the class `latticeHarmonicClass z` and the lattice harmonic
cubic polynomials, above the radius `latticeHRScaleThree`. -/
theorem harmonicRegularity_three_latticeHarmonicClass (z : Vertex 2) (R : ℝ) :
    HarmonicRegularity (componentBallSeminorm (latticeComponent 2) z) (latticeHarmonicClass z)
      latticeHarmonicCubic 3 latticeHRScaleThree R latticeHRConstThree := by
  intro r hrR v hv s hXs hsr
  have hK : 0 ≤ latticeHRConstThree * (s / r) ^ (3 + 1) := by
    have hs : 0 < s := latticeHRScaleThree_pos.trans_le hXs
    have hr : 0 < r := by linarith
    exact mul_nonneg latticeHRConstThree_nonneg (pow_nonneg (div_nonneg hs.le hr.le) _)
  have e : latticeHRConstThree * (s / r) ^ (3 + 1) *
      ballExcess (componentBallSeminorm (latticeComponent 2) z) latticeHarmonicCubic r v =
      ⨅ w : latticeHarmonicCubic, latticeHRConstThree * (s / r) ^ (3 + 1) *
        componentBallSeminorm (latticeComponent 2) z r (v - w) :=
    Real.mul_iInf_of_nonneg hK _
  rw [e]
  refine le_ciInf fun w => ?_
  rw [componentBallSeminorm_apply]
  exact ballExcess_le_latticeHRConstThree_mul z hrR hv hXs hsr w.2

end Rigidity.Proofs.Regularity

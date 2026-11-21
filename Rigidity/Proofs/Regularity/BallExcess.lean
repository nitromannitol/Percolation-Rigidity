import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Pointwise

/-!
# Excess over a space of polynomials on balls

Armstrong and Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(arXiv:1609.09431v2), Section 7, measure the distance of a function `u` on the ball `B_R` to the
space `Ā_k` of `ā`-harmonic polynomials of degree at most `k` by
`D_k(s) = inf_{w ∈ Ā_k} ‖u - w‖_{L̲²(B_s)}`, `s ∈ (0, R]`, and the distance to the space `Ā(B_r)`
of `ā`-harmonic functions on `B_r` by `inf_{v ∈ Ā(B_r)} ‖u - v‖_{L̲²(B_r)}`.

Lemma 7.2 of that paper (the transfer of regularity from `ā`-harmonic functions to functions that
are well approximated by `ā`-harmonic functions on large scales) only uses a few properties of the
normalized norms `‖·‖_{L̲²(B_s)}`. We therefore work with an abstract additive group `F`, a family
`N s` of additive group seminorms on `F` indexed by the radius `s`, additive subgroups `P` of `F`
(the polynomial spaces) and sets `Ā r ⊆ F` (the harmonic functions on `B_r`). The properties used
are recorded as the predicates `RadiusMonotone` (the normalized norm on a smaller ball is controlled
by the one on a larger ball up to the volume factor), `PolynomialComparison` (the distance of a
polynomial of degree `j` to the polynomials of lower degree scales like the `j`-th power of the
radius) and `HarmonicRegularity` (the excess decay of an `ā`-harmonic function). For the normalized
Lebesgue norms on Euclidean balls the volume factor is `(r / s) ^ (d / 2)`.

This file proves the elementary properties of the excess `ballExcess N P s u` and the first step of
the proof of Lemma 7.2 (`ballExcess_le_of_harmonicRegularity`): an excess decay estimate for `u`
from the excess decay of `ā`-harmonic functions and the triangle inequality.
-/

namespace Rigidity.Proofs.Regularity

variable {F : Type*} [AddCommGroup F]

/-- The excess `inf_{w ∈ P} N s (u - w)` of `u` over the additive subgroup `P` at radius `s`. -/
noncomputable def ballExcess (N : ℝ → AddGroupSeminorm F) (P : AddSubgroup F) (s : ℝ) (u : F) :
    ℝ :=
  ⨅ w : P, N s (u - w)

/-- The distance `inf_{v ∈ S} N s (u - v)` of `u` to a set `S` at radius `s`. -/
noncomputable def ballDist (N : ℝ → AddGroupSeminorm F) (S : Set F) (s : ℝ) (u : F) : ℝ :=
  ⨅ v : S, N s (u - v)

/-- The normalized norm on a ball of radius `s ∈ [X, R]` is at most `CV (r / s) ^ γ` times the one
on a ball of radius `r ∈ [s, R]`. -/
def RadiusMonotone (N : ℝ → AddGroupSeminorm F) (X R CV γ : ℝ) : Prop :=
  ∀ f : F, ∀ s r : ℝ, X ≤ s → s ≤ r → r ≤ R → N s f ≤ CV * (r / s) ^ γ * N r f

/-- The excess of an element of `Phigh` over `Plow` at radius `ρ` is at most `CP (ρ / ρ') ^ j`
times its excess at the larger radius `ρ'`, for `X ≤ ρ ≤ ρ' ≤ R`. -/
def PolynomialComparison (N : ℝ → AddGroupSeminorm F) (Plow Phigh : AddSubgroup F) (j : ℕ)
    (X R CP : ℝ) : Prop :=
  ∀ w ∈ Phigh, ∀ ρ ρ' : ℝ, X ≤ ρ → ρ ≤ ρ' → ρ' ≤ R →
    ballExcess N Plow ρ w ≤ CP * (ρ / ρ') ^ j * ballExcess N Plow ρ' w

/-- Every `v ∈ Abar r`, `r ≤ R`, satisfies the excess decay
`ballExcess N P s v ≤ CH (s / r) ^ (j + 1) ballExcess N P r v` for `X ≤ s ≤ r / 2`. -/
def HarmonicRegularity (N : ℝ → AddGroupSeminorm F) (Abar : ℝ → Set F) (P : AddSubgroup F)
    (j : ℕ) (X R CH : ℝ) : Prop :=
  ∀ r : ℝ, r ≤ R → ∀ v ∈ Abar r, ∀ s : ℝ, X ≤ s → s ≤ r / 2 →
    ballExcess N P s v ≤ CH * (s / r) ^ (j + 1) * ballExcess N P r v

variable (N : ℝ → AddGroupSeminorm F) (P : AddSubgroup F)

theorem bddBelow_range_ballExcess (s : ℝ) (u : F) :
    BddBelow (Set.range fun w : P => N s (u - w)) :=
  ⟨0, by rintro _ ⟨w, rfl⟩; exact apply_nonneg _ _⟩

theorem ballExcess_nonneg (s : ℝ) (u : F) : 0 ≤ ballExcess N P s u :=
  le_ciInf fun _ => apply_nonneg _ _

theorem ballExcess_le {s : ℝ} {u w : F} (hw : w ∈ P) : ballExcess N P s u ≤ N s (u - w) :=
  ciInf_le (bddBelow_range_ballExcess N P s u) ⟨w, hw⟩

theorem le_ballExcess {s a : ℝ} {u : F} (h : ∀ w ∈ P, a ≤ N s (u - w)) :
    a ≤ ballExcess N P s u :=
  le_ciInf fun w => h w w.2

theorem exists_lt_ballExcess_add {η : ℝ} (hη : 0 < η) (s : ℝ) (u : F) :
    ∃ w ∈ P, N s (u - w) < ballExcess N P s u + η := by
  obtain ⟨w, hw⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (ballExcess N P s u) hη)
  exact ⟨w, w.2, hw⟩

theorem ballExcess_le_self (s : ℝ) (u : F) : ballExcess N P s u ≤ N s u := by
  simpa using ballExcess_le N P (s := s) (u := u) P.zero_mem

theorem ballExcess_of_mem {s : ℝ} {w : F} (hw : w ∈ P) : ballExcess N P s w = 0 :=
  le_antisymm (by simpa using ballExcess_le N P (s := s) (u := w) hw) (ballExcess_nonneg N P s w)

/-- The excess is controlled by the distance to any `v` plus the excess of `v`. -/
theorem ballExcess_le_add (s : ℝ) (u v : F) :
    ballExcess N P s u ≤ N s (u - v) + ballExcess N P s v := by
  have h : ∀ w ∈ P, ballExcess N P s u - N s (u - v) ≤ N s (v - w) := by
    intro w hw
    have h1 := ballExcess_le N P (s := s) (u := u) hw
    have h2 := map_add_le_add (N s) (u - v) (v - w)
    rw [sub_add_sub_cancel] at h2
    linarith
  linarith [le_ballExcess N P h]

/-- The excess is subadditive. -/
theorem ballExcess_add_le (s : ℝ) (u v : F) :
    ballExcess N P s (u + v) ≤ ballExcess N P s u + ballExcess N P s v := by
  have h : ∀ w ∈ P, ∀ w' ∈ P, ballExcess N P s (u + v) ≤ N s (u - w) + N s (v - w') := by
    intro w hw w' hw'
    calc ballExcess N P s (u + v) ≤ N s (u + v - (w + w')) := ballExcess_le N P (P.add_mem hw hw')
      _ = N s ((u - w) + (v - w')) := by congr 1; abel
      _ ≤ N s (u - w) + N s (v - w') := map_add_le_add _ _ _
  have h2 : ∀ w ∈ P, ballExcess N P s (u + v) - ballExcess N P s v ≤ N s (u - w) := by
    intro w hw
    have : ballExcess N P s (u + v) - N s (u - w) ≤ ballExcess N P s v :=
      le_ballExcess N P fun w' hw' => by linarith [h w hw w' hw']
    linarith
  linarith [le_ballExcess N P h2]

/-- The excess of `u - w` equals the excess of `u` for `w ∈ P`. -/
theorem ballExcess_sub_mem (s : ℝ) (u : F) {w : F} (hw : w ∈ P) :
    ballExcess N P s (u - w) = ballExcess N P s u := by
  apply le_antisymm
  · have := ballExcess_add_le N P s u (-w)
    rwa [ballExcess_of_mem N P (P.neg_mem hw), add_zero, ← sub_eq_add_neg] at this
  · have := ballExcess_add_le N P s (u - w) w
    rwa [ballExcess_of_mem N P hw, add_zero, sub_add_cancel] at this

/-- A larger subgroup has a smaller excess. -/
theorem ballExcess_anti {P Q : AddSubgroup F} (hPQ : P ≤ Q) (s : ℝ) (u : F) :
    ballExcess N Q s u ≤ ballExcess N P s u :=
  le_ballExcess N P fun _ hw => ballExcess_le N Q (hPQ hw)

/-- A pointwise comparison of the seminorms passes to the excess. -/
theorem ballExcess_le_mul {s r K : ℝ} (hK : 0 ≤ K) (u : F) (h : ∀ f, N s f ≤ K * N r f) :
    ballExcess N P s u ≤ K * ballExcess N P r u := by
  have : K * ballExcess N P r u = ⨅ w : P, K * N r (u - w) := Real.mul_iInf_of_nonneg hK _
  rw [this]
  exact le_ciInf fun w => (ballExcess_le N P w.2).trans (h _)

/-- The excess at radius `s` is controlled by the excess at radius `r` with the volume factor. -/
theorem ballExcess_le_of_radiusMonotone {X R CV γ : ℝ} (hCV : 0 ≤ CV)
    (hmono : RadiusMonotone N X R CV γ) {s r : ℝ} (hs : X ≤ s) (hsr : s ≤ r) (hr : r ≤ R)
    (hs0 : 0 < s) (u : F) :
    ballExcess N P s u ≤ CV * (r / s) ^ γ * ballExcess N P r u :=
  ballExcess_le_mul N P
    (mul_nonneg hCV (Real.rpow_nonneg (div_nonneg (hs0.le.trans hsr) hs0.le) _)) u
    fun f => hmono f s r hs hsr hr

theorem ballDist_nonneg (S : Set F) (s : ℝ) (u : F) : 0 ≤ ballDist N S s u := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp [ballDist]
  · exact le_ciInf fun _ => apply_nonneg _ _

/-- A lower bound, valid for every element of a nonempty set, passes to the distance. -/
theorem le_ballDist {S : Set F} (hS : S.Nonempty) {s a : ℝ} {u : F}
    (h : ∀ v ∈ S, a ≤ N s (u - v)) : a ≤ ballDist N S s u :=
  haveI := hS.to_subtype
  le_ciInf fun v => h v v.2

/-- **Armstrong–Dario, proof of Lemma 7.2, Step 1.** If every element of `Abar r` has the excess
decay of `HarmonicRegularity`, then for `X ≤ s ≤ r / 2`, `r ≤ R`,
`D(s) ≤ CH (s / r) ^ (j + 1) D(r) + (CV (r / s) ^ γ + CH (s / r) ^ (j + 1)) dist(u, Abar r)`. -/
theorem ballExcess_le_of_harmonicRegularity {Abar : ℝ → Set F} {j : ℕ} {X R CV CH γ : ℝ}
    (hCV : 0 ≤ CV) (hCH : 0 ≤ CH) (hmono : RadiusMonotone N X R CV γ)
    (hreg : HarmonicRegularity N Abar P j X R CH) {s r : ℝ} (hX : X ≤ s) (hs0 : 0 < s)
    (hsr : s ≤ r / 2) (hr : r ≤ R) (hne : (Abar r).Nonempty) (u : F) :
    ballExcess N P s u ≤ CH * (s / r) ^ (j + 1) * ballExcess N P r u +
      (CV * (r / s) ^ γ + CH * (s / r) ^ (j + 1)) * ballDist N (Abar r) r u := by
  have hsr' : s ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  set a := CH * (s / r) ^ (j + 1) with ha
  have ha0 : 0 ≤ a := mul_nonneg hCH (pow_nonneg (div_nonneg hs0.le hr0.le) _)
  have key : ∀ v ∈ Abar r, ballExcess N P s u - a * ballExcess N P r u ≤
      (CV * (r / s) ^ γ + a) * N r (u - v) := by
    intro v hv
    have h1 := ballExcess_le_add N P s u v
    have h2 := hmono (u - v) s r hX hsr' hr
    have h3 := hreg r hr v hv s hX hsr
    have h4 := ballExcess_le_add N P r v u
    rw [map_sub_rev] at h4
    have h5 : a * ballExcess N P r v ≤ a * (N r (u - v) + ballExcess N P r u) :=
      mul_le_mul_of_nonneg_left h4 ha0
    nlinarith
  have hK : 0 ≤ CV * (r / s) ^ γ + a :=
    add_nonneg (mul_nonneg hCV (Real.rpow_nonneg (div_nonneg hr0.le hs0.le) _)) ha0
  by_cases hK0 : CV * (r / s) ^ γ + a = 0
  · rcases hne with ⟨v, hv⟩
    have := key v hv
    rw [hK0, zero_mul] at this
    have hd := ballDist_nonneg N (Abar r) r u
    rw [hK0, zero_mul, add_zero]
    linarith
  · have hKpos : 0 < CV * (r / s) ^ γ + a := lt_of_le_of_ne hK (Ne.symm hK0)
    have : (ballExcess N P s u - a * ballExcess N P r u) / (CV * (r / s) ^ γ + a) ≤
        ballDist N (Abar r) r u :=
      le_ballDist N hne fun v hv => by rw [div_le_iff₀ hKpos]; linarith [key v hv]
    rw [div_le_iff₀ hKpos] at this
    linarith

end Rigidity.Proofs.Regularity

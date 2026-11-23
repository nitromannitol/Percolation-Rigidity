import Rigidity.Proofs.Regularity.PlanarCorrectorSupOs
import Rigidity.Proofs.Section5.PlanarLiteratureAdapters

/-!
# (1.22) in dimension two: the oscillation of the correctors on the balls

`PlanarCorrectorOscSublinearTwo` is (1.22) of Armstrong and Dario (arXiv:1609.09431v2) in the
oscillation form: for `R ≥ 1` there is a measurable `Z_R ≥ 0` of class `O_s(C R^{1-δ})` such that
almost surely, for every corrected plane `ℓ` of slope `q` and all `a, b` of the infinite cluster in
the ball of radius `R`, `|χ(a) - χ(b)| ≤ |q|₁ Z_R` with `χ = ℓ - q · x`.

`planarCorrectorOscSublinearTwo_of_sublinearL2`: it follows from (1.18) in the form `O_s`, the
order-zero regularity and the minimal scales:
* the correctors `u₀, u₁` of the slopes `e₀, e₁` are bounded on the balls by
  `C max(R, 9 max(X, 1))^{1-7η}` (`exists_corrector_sup_os`, the Remark after (1.19));
* a corrected plane of slope `q` differs from `q₀ u₀ + q₁ u₁` by a constant: the difference is
  harmonic and sublinear, hence constant by the Liouville theorem of order zero
  (`Rigidity.Proofs.Section5.sublinearLiouvilleStep_two`);
* `Z_R = 2 C max(R, 9 max(X, 1))^{1-7η}` is measurable and at most `20 C R^{1-7η} max(X, 1)`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

/-- **(1.22) in dimension two, in the oscillation form.** -/
def PlanarCorrectorOscSublinearTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s δ C : ℝ, 0 < s ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ Z : Configuration 2 → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond 2 p Z s (C * R ^ (1 - δ)) ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ (q : Fin 2 → ℝ)
          (ℓ : uniqueInfiniteComponent h → ℝ), IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
          ∀ a b : uniqueInfiniteComponent h,
            ‖latticeEuclideanEmbedding a.val‖ < R → ‖latticeEuclideanEmbedding b.val‖ < R →
            |(ℓ a - ∑ i, q i * (a.val i : ℝ)) - (ℓ b - ∑ i, q i * (b.val i : ℝ))| ≤
              (|q 0| + |q 1|) * Z ω

/-- A power of `3` between `T / 9` and `T`. -/
theorem exists_three_pow_between {T : ℝ} (hT : 1 ≤ T) :
    ∃ m : ℕ, (3 : ℝ) ^ m ≤ T ∧ T ≤ 9 * 3 ^ m := by
  set n : ℕ := ⌊T⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hT)
  refine ⟨Nat.log 3 n, ?_, ?_⟩
  · have h1 : 3 ^ Nat.log 3 n ≤ n := Nat.pow_log_le_self 3 (by omega)
    have h2 : (n : ℝ) ≤ T := Nat.floor_le (by linarith)
    exact (by exact_mod_cast h1 : ((3 ^ Nat.log 3 n : ℕ) : ℝ) ≤ n).trans h2 |>.trans' (by push_cast; rfl)
  · have h1 : n < 3 ^ (Nat.log 3 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : T < n + 1 := Nat.lt_floor_add_one T
    have h3 : ((n : ℕ) : ℝ) + 1 ≤ (3 : ℝ) ^ (Nat.log 3 n + 1) := by exact_mod_cast h1
    have h4 : (3 : ℝ) ^ (Nat.log 3 n + 1) ≤ 9 * 3 ^ Nat.log 3 n := by
      rw [pow_succ]; have : (0 : ℝ) ≤ 3 ^ Nat.log 3 n := by positivity
      linarith
    linarith

/-- **The uniform bound on a ball** from the bounds on the boxes above the scale `X`. -/
theorem abs_le_on_ball {ω : Configuration 2} {C : OpenComponent ω} {f : C → ℝ} {X B η : ℝ}
    (hB : 0 ≤ B) (hη : 7 * η ≤ 1)
    (hsup : ∀ m : ℕ, X ≤ 3 ^ m → ∀ x : C, (∀ i, |x.val i| ≤ 9 * 3 ^ m) →
      |f x| ≤ B * ((3 : ℝ) ^ m) ^ (1 - 7 * η))
    {R : ℝ} (hR : 1 ≤ R) (x : C) (hx : ‖latticeEuclideanEmbedding x.val‖ < R) :
    |f x| ≤ B * (max R (9 * max X 1)) ^ (1 - 7 * η) := by
  set T : ℝ := max R (9 * max X 1) with hT
  have hT1 : 1 ≤ T := hR.trans (le_max_left _ _)
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_between hT1
  have hXm : X ≤ 3 ^ m := by
    have : 9 * max X 1 ≤ 9 * 3 ^ m := (le_max_right _ _).trans hm2
    have : max X 1 ≤ 3 ^ m := by linarith
    exact (le_max_left _ _).trans this
  have hbox : ∀ i, |x.val i| ≤ 9 * 3 ^ m := by
    intro i
    have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex 2) i
    rw [dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero] at h1
    have e : (((0 : Vertex 2) i : ℤ) : ℝ) = 0 := by simp
    rw [e, sub_zero] at h1
    have h2 : |((x.val i : ℤ) : ℝ)| ≤ 9 * 3 ^ m := by
      linarith [le_max_left R (9 * max X 1)]
    have h3 : ((|x.val i| : ℤ) : ℝ) ≤ ((9 * 3 ^ m : ℤ) : ℝ) := by push_cast; exact h2
    exact_mod_cast h3
  refine (hsup m hXm x hbox).trans (mul_le_mul_of_nonneg_left ?_ hB)
  exact Real.rpow_le_rpow (by positivity) hm1 (by linarith)

end Rigidity.Proofs.Regularity

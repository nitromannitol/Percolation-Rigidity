import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorSupOs
import Rigidity.Proofs.Section5.PlanarLiteratureAdapters
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorOsc
import Rigidity.Proofs.Regularity.PlanarCorrectedPlaneExistence

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
* `Z_R = 2 (C + 1) max(R, 9 max(X, 1))^{1-7η}` is measurable and at most
  `18 (C + 1) R^{1-7η} max(X, 1)`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

/-- **(1.22) in dimension two** from (1.18) in the form `O_s`, the order-zero regularity and the
minimal scales of Proposition 2.4. -/
theorem planarCorrectorOscSublinearTwo_of_sublinearL2 (h118 : PlanarCorrectorSublinearL2Two)
    (hR3 : ArmstrongDarioOrderZeroTwo)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p) :
    PlanarCorrectorOscSublinearTwo := by
  intro p hpc hp1
  obtain ⟨s, θ, η, Cs, hs, hθ, hη, hη28, hCs, X, hXm, -, hXos, hae⟩ :=
    exists_corrector_sup_os h118 hR3 hM5 p hpc hp1
  have hη1 : 7 * η ≤ 1 := by linarith
  have hc1 := isOsBond_const (d := 2) (p := p) one_pos hs
  obtain ⟨θ', hθ', hX'⟩ := exists_isOsBond_max hs hs hθ (by positivity) hXm measurable_const
    hXos hc1
  refine ⟨min s s, 7 * η, 18 * (Cs + 1) * θ', lt_min hs hs, by positivity, hη1, by positivity,
    fun R hR => ?_⟩
  refine ⟨fun ω => 2 * (Cs + 1) * (max R (9 * max (X ω) 1)) ^ (1 - 7 * η), ?_,
    fun ω => by positivity, ?_, ?_⟩
  · exact measurable_const.mul ((measurable_const.max (measurable_const.mul
      (hXm.max measurable_const))).pow_const _)
  · have hc : (0 : ℝ) < 18 * (Cs + 1) * R ^ (1 - 7 * η) := by positivity
    have h := IsOsBond.const_mul hc hX'
    refine IsOsBond.mono_variable
      (Y := fun ω => 18 * (Cs + 1) * R ^ (1 - 7 * η) * max (X ω) 1) (lt_min hs hs) (by positivity)
      (measurable_const.mul ((measurable_const.max (measurable_const.mul
        (hXm.max measurable_const))).pow_const _)) (fun ω => ?_) ?_
    · have := max_rpow_le (X := X ω) hR hη hη1
      have hC0 : 0 ≤ 2 * (Cs + 1) := by positivity
      calc 2 * (Cs + 1) * (max R (9 * max (X ω) 1)) ^ (1 - 7 * η)
          ≤ 2 * (Cs + 1) * (9 * R ^ (1 - 7 * η) * max (X ω) 1) :=
            mul_le_mul_of_nonneg_left this hC0
        _ = 18 * (Cs + 1) * R ^ (1 - 7 * η) * max (X ω) 1 := by ring
    · have e : 18 * (Cs + 1) * θ' * R ^ (1 - 7 * η) = 18 * (Cs + 1) * R ^ (1 - 7 * η) * θ' := by
        ring
      rw [e]
      exact h
  · filter_upwards [hae, Rigidity.Proofs.Section5.sublinearLiouvilleStep_two p hpc hp1 hR3] with
      ω hω hL
    intro h q ℓ hℓ a b ha hb
    obtain ⟨u₀, hu₀, hs₀⟩ := hω h (Pi.single 0 1)
    obtain ⟨u₁, hu₁, hs₁⟩ := hω h (Pi.single 1 1)
    have hsup : ∀ i : Fin 2, ∀ m : ℕ, X ω ≤ 3 ^ m → ∀ x : uniqueInfiniteComponent h,
        (∀ j, |x.val j| ≤ 9 * 3 ^ m) →
        |componentCorrector (uniqueInfiniteComponent h) (Pi.single i 1)
          (if i = 0 then u₀ else u₁) x| ≤ Cs * ((3 : ℝ) ^ m) ^ (1 - 7 * η) := by
      intro i m hm x hx
      fin_cases i
      · have := hs₀ m hm x hx
        rwa [abs_single_add, mul_one] at this
      · have := hs₁ m hm x hx
        rwa [abs_single_add, mul_one] at this
    have hball : ∀ i : Fin 2, ∀ R' : ℝ, 1 ≤ R' → ∀ x : uniqueInfiniteComponent h,
        ‖latticeEuclideanEmbedding x.val‖ < R' →
        |componentCorrector (uniqueInfiniteComponent h) (Pi.single i 1)
          (if i = 0 then u₀ else u₁) x| ≤ Cs * (max R' (9 * max (X ω) 1)) ^ (1 - 7 * η) :=
      fun i R' hR' x hx => abs_le_on_ball hCs hη1 (hsup i) hR' x hx
    obtain ⟨c, hc⟩ := eq_add_of_isCorrectedPlane hu₀ hu₁ hCs hη hη1 hball (hL h) hℓ
    set T : ℝ := (max R (9 * max (X ω) 1)) ^ (1 - 7 * η) with hT
    have hb0a := hball 0 R hR a ha
    have hb0b := hball 0 R hR b hb
    have hb1a := hball 1 R hR a ha
    have hb1b := hball 1 R hR b hb
    simp only [if_true, one_ne_zero, if_false, componentCorrector,
      componentSlope_single] at hb0a hb0b hb1a hb1b
    have e : (ℓ a - ∑ i, q i * (a.val i : ℝ)) - (ℓ b - ∑ i, q i * (b.val i : ℝ)) =
        q 0 * ((u₀ a - (a.val 0 : ℝ)) - (u₀ b - (b.val 0 : ℝ))) +
          q 1 * ((u₁ a - (a.val 1 : ℝ)) - (u₁ b - (b.val 1 : ℝ))) := by
      rw [hc a, hc b, Fin.sum_univ_two, Fin.sum_univ_two]; ring
    rw [e]
    have hT0 : 0 ≤ T := by positivity
    have k0 : |q 0 * ((u₀ a - (a.val 0 : ℝ)) - (u₀ b - (b.val 0 : ℝ)))| ≤ |q 0| * (2 * Cs * T) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_sub (u₀ a - (a.val 0 : ℝ)) (u₀ b - (b.val 0 : ℝ))
      linarith
    have k1 : |q 1 * ((u₁ a - (a.val 1 : ℝ)) - (u₁ b - (b.val 1 : ℝ)))| ≤ |q 1| * (2 * Cs * T) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_sub (u₁ a - (a.val 1 : ℝ)) (u₁ b - (b.val 1 : ℝ))
      linarith
    have k2 : 2 * Cs * T ≤ 2 * (Cs + 1) * T := by nlinarith
    calc _ ≤ |q 0 * ((u₀ a - (a.val 0 : ℝ)) - (u₀ b - (b.val 0 : ℝ)))| +
          |q 1 * ((u₁ a - (a.val 1 : ℝ)) - (u₁ b - (b.val 1 : ℝ)))| := abs_add_le _ _
      _ ≤ |q 0| * (2 * Cs * T) + |q 1| * (2 * Cs * T) := add_le_add k0 k1
      _ ≤ |q 0| * (2 * (Cs + 1) * T) + |q 1| * (2 * (Cs + 1) * T) :=
          add_le_add (mul_le_mul_of_nonneg_left k2 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left k2 (abs_nonneg _))
      _ = (|q 0| + |q 1|) * (2 * (Cs + 1) * T) := by ring

/-- **(1.22) in dimension two** from Proposition 5.2 for `ν` in the form `O_s`, the minimal scales
of Proposition 2.4 and the order-zero regularity. -/
theorem planarCorrectorOscSublinearTwo_of_subaddOs
    (hsub : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarNuSubaddOsTwo p)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hR3 : ArmstrongDarioOrderZeroTwo) : PlanarCorrectorOscSublinearTwo :=
  planarCorrectorOscSublinearTwo_of_sublinearL2
    (planarCorrectorSublinearL2Two_of_subaddOs hsub hM5 hR3) hR3 hM5

end Rigidity.Proofs.Regularity

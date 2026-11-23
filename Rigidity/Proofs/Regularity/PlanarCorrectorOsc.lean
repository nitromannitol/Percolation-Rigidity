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

theorem componentSlope_single {ω : Configuration 2} (C : OpenComponent ω) (i : Fin 2) (x : C) :
    componentSlope C (Pi.single i 1) x = (x.val i : ℝ) := by
  unfold componentSlope
  exact sum_single_mul i _

/-- **Uniqueness of the corrected planes up to constants**: a corrected plane of slope `q` is
`c + q₀ u₀ + q₁ u₁` when the correctors of `u₀, u₁` are sublinear on the balls and the sublinear
harmonic functions are constant. -/
theorem eq_add_of_isCorrectedPlane {ω : Configuration 2} {C : OpenComponent ω} {u₀ u₁ : C → ℝ}
    (hu₀ : u₀ ∈ harmonicGrowthSpace C 1) (hu₁ : u₁ ∈ harmonicGrowthSpace C 1) {X B η : ℝ}
    (hB : 0 ≤ B) (hη : 0 < η) (hη1 : 7 * η ≤ 1)
    (hb : ∀ i : Fin 2, ∀ R : ℝ, 1 ≤ R → ∀ x : C, ‖latticeEuclideanEmbedding x.val‖ < R →
      |componentCorrector C (Pi.single i 1) (if i = 0 then u₀ else u₁) x| ≤
        B * (max R (9 * max X 1)) ^ (1 - 7 * η))
    (hL : ∀ v : C → ℝ, (∀ x, componentLaplacian C v x = 0) →
      componentSlopeAsymptotics C 0 v → ∃ c : ℝ, ∀ x, v x = c)
    {q : Fin 2 → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) :
    ∃ c : ℝ, ∀ x, ℓ x = c + q 0 * u₀ x + q 1 * u₁ x := by
  set w : C → ℝ := ℓ - (q 0 • u₀ + q 1 • u₁) with hw
  have hwH : w ∈ harmonicGrowthSpace C 1 :=
    sub_mem hℓ.1 (add_mem (Submodule.smul_mem _ _ hu₀) (Submodule.smul_mem _ _ hu₁))
  set qn : ℝ := |q 0| + |q 1| with hqn
  have hsub : componentSlopeAsymptotics C 0 w := by
    intro ε hε
    obtain ⟨R₁, hR₁0, hR₁⟩ := hℓ.2 (ε / 2) (by positivity)
    set R₂ : ℝ := (2 * B * qn / ε + 1) ^ (1 / (7 * η)) with hR₂
    refine ⟨max (max R₁ (9 * max X 1)) (max R₂ 1), by positivity, fun R hR x hx => ?_⟩
    have hR1 : 1 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
    have hR9 : 9 * max X 1 ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
    have hxR := norm_lt_of_mem_componentEuclideanBall hx
    have hT : max R (9 * max X 1) = R := max_eq_left hR9
    have h0 := hb 0 R hR1 x hxR
    have h1 := hb 1 R hR1 x hxR
    simp only [if_true, hT, one_ne_zero, if_false] at h0 h1
    have hℓx := hR₁ R ((le_max_left _ _).trans ((le_max_left _ _).trans hR)) x hx
    have hsl0 : componentSlope C 0 x = 0 := by simp [componentSlope]
    have hsl : componentSlope C q x = q 0 * (x.val 0 : ℝ) + q 1 * (x.val 1 : ℝ) := by
      simp [componentSlope, Fin.sum_univ_two]
    have hc0 : componentCorrector C (Pi.single 0 1) u₀ x = u₀ x - (x.val 0 : ℝ) := by
      rw [componentCorrector, componentSlope_single]
    have hc1 : componentCorrector C (Pi.single 1 1) u₁ x = u₁ x - (x.val 1 : ℝ) := by
      rw [componentCorrector, componentSlope_single]
    rw [hc0] at h0
    rw [hc1] at h1
    have hwx : w x - componentSlope C 0 x = (ℓ x - componentSlope C q x) -
        q 0 * (u₀ x - (x.val 0 : ℝ)) - q 1 * (u₁ x - (x.val 1 : ℝ)) := by
      rw [hsl0, hsl, hw]; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    -- the sublinear part
    have hR7 : 2 * B * qn / ε < R ^ (7 * η) := by
      have h1' : R₂ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
      have h2' : R₂ ^ (7 * η) ≤ R ^ (7 * η) :=
        Real.rpow_le_rpow (by positivity) h1' (by positivity)
      have h3' : R₂ ^ (7 * η) = 2 * B * qn / ε + 1 := by
        rw [hR₂, ← Real.rpow_mul (by positivity), one_div_mul_cancel (by positivity),
          Real.rpow_one]
      linarith
    have hRp : 0 < R ^ (7 * η) := by positivity
    have hpow : R ^ (1 - 7 * η) = R / R ^ (7 * η) := by
      rw [Real.rpow_sub (by positivity), Real.rpow_one]
    have hBq : B * qn * R ^ (1 - 7 * η) ≤ ε / 2 * R := by
      rw [hpow, mul_div_assoc', div_le_iff₀ hRp]
      rw [div_lt_iff₀ hε] at hR7
      nlinarith [hR7, (by positivity : (0 : ℝ) ≤ R)]
    have hq0 : |q 0 * (u₀ x - (x.val 0 : ℝ))| ≤ |q 0| * (B * R ^ (1 - 7 * η)) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
    have hq1 : |q 1 * (u₁ x - (x.val 1 : ℝ))| ≤ |q 1| * (B * R ^ (1 - 7 * η)) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    rw [hwx]
    calc |(ℓ x - componentSlope C q x) - q 0 * (u₀ x - (x.val 0 : ℝ)) -
          q 1 * (u₁ x - (x.val 1 : ℝ))|
        ≤ |ℓ x - componentSlope C q x| + |q 0 * (u₀ x - (x.val 0 : ℝ))| +
            |q 1 * (u₁ x - (x.val 1 : ℝ))| := by
          have := abs_sub (ℓ x - componentSlope C q x - q 0 * (u₀ x - (x.val 0 : ℝ)))
            (q 1 * (u₁ x - (x.val 1 : ℝ)))
          have := abs_sub (ℓ x - componentSlope C q x) (q 0 * (u₀ x - (x.val 0 : ℝ)))
          linarith
      _ ≤ ε / 2 * R + (|q 0| * (B * R ^ (1 - 7 * η)) + |q 1| * (B * R ^ (1 - 7 * η))) := by
          linarith
      _ = ε / 2 * R + B * qn * R ^ (1 - 7 * η) := by rw [hqn]; ring
      _ ≤ ε * R := by linarith
  obtain ⟨c, hc⟩ := hL w hwH.1 hsub
  refine ⟨c, fun x => ?_⟩
  have := hc x
  rw [hw] at this
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-- `max(R, 9 max(X, 1))^{1-7η} ≤ 9 R^{1-7η} max(X, 1)` for `R ≥ 1`. -/
theorem max_rpow_le {R X η : ℝ} (hR : 1 ≤ R) (hη : 0 < η) (hη1 : 7 * η ≤ 1) :
    (max R (9 * max X 1)) ^ (1 - 7 * η) ≤ 9 * R ^ (1 - 7 * η) * max X 1 := by
  have hX1 : 1 ≤ max X 1 := le_max_right _ _
  have h1 : max R (9 * max X 1) ≤ 9 * max X 1 * R := by
    refine max_le ?_ ?_
    · have : R ≤ 9 * max X 1 * R := le_mul_of_one_le_left (by linarith) (by linarith)
      exact this
    · exact le_mul_of_one_le_right (by positivity) hR
  have h2 : (max R (9 * max X 1)) ^ (1 - 7 * η) ≤ (9 * max X 1 * R) ^ (1 - 7 * η) :=
    Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have h3 : (9 * max X 1) ^ (1 - 7 * η) ≤ 9 * max X 1 := by
    calc (9 * max X 1) ^ (1 - 7 * η) ≤ (9 * max X 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 9 * max X 1 := Real.rpow_one _
  rw [Real.mul_rpow (by positivity) (by positivity)] at h2
  calc _ ≤ (9 * max X 1) ^ (1 - 7 * η) * R ^ (1 - 7 * η) := h2
    _ ≤ 9 * max X 1 * R ^ (1 - 7 * η) := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by ring

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

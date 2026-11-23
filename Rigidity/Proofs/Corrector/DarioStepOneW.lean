import Rigidity.Proofs.Corrector.DarioStepOneGrowth
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationHolds

/-!
# Moments of the local sums of Step 1 of Lemma 3.3 of Dario, and Step 1

Dario bounds the sum (3.18) `W(y) = Σ_e 1{y ∈ B_e} F_e` through (3.19)-(3.20), the random-ball
bounds of Proposition 2.15 and (3.12). Here `E[W(y)^q] ≤ (A q^k)^q` uniformly in `y`
(`stepOneW_moments`), which with `flipSumOne_isOsBond_of_moments` gives Step 1 of Lemma 3.3
(`flipSumOne_isOsBond_of_resample`, given Lemma 3.5).

* `stepOne_lipschitz_data`: the Lipschitz bounds `Λ` of `stepSix_data`, with the moments
  `E[(1 + Λ(x))^q] ≤ (B q^κ)^q` of the single bounds (from `lipschitz_correctorDiff` and
  `lintegral_add_two_rpow_le`).
* `stepOneFactorSelf`: the factor `F_e` of `W` computed in the configuration itself; the factor of
  `W` at `ω` is its value at `ω^{e,1}` (`stepOneFactor_eq_self`), so (3.12) in the form
  `E[f(ω^{e,1})] ≤ p^{-1} E[f]` removes the flip.
* `stepOneFactorSelf_le`: on the partition event, `F_e ≤ 1{|a_e - y| ≤ κ₁ s} · 64 T³` with
  `s = size(□_𝒫(a_e))` and `T` the sum of `1 + Λ` over the ball of radius `κ₃ s` around `a_e`.
* The moments of `T` (`lintegral_randomBallSum_rpow_le_of_growth`), Cauchy–Schwarz on the event
  `|a_e - y| ≤ κ₁ s` (whose probability decays exponentially in `|a_e - y|`), and Jensen's
  inequality over the bonds (`lintegral_tsum_rpow_le_of_decay`) give the moments of `W(y)`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare
open scoped Classical ENNReal

/-- The points of a box of radius `r` are within Euclidean distance `2r` of its centre. -/
theorem norm_sub_le_of_mem_supBox {a z : Vertex 2} {r : ℕ} (h : z ∈ supBox a r) :
    ‖latticeEuclideanEmbedding (z - a)‖ ≤ 2 * r ∧ ‖latticeEuclideanEmbedding (a - z)‖ ≤ 2 * r := by
  have hc : ∀ i, |(((z - a) i : ℤ) : ℝ)| ≤ r ∧ |(((a - z) i : ℤ) : ℝ)| ≤ r := by
    intro i
    have hi := (mem_supBox.1 h) i
    have hi' : |a i - z i| ≤ (r : ℤ) := by rw [abs_sub_comm]; exact hi
    constructor
    · rw [Pi.sub_apply]
      exact_mod_cast hi
    · rw [Pi.sub_apply]
      exact_mod_cast hi'
  constructor
  · have := norm_latticeEuclideanEmbedding_le_sum (z - a)
    linarith [(hc 0).1, (hc 1).1]
  · have := norm_latticeEuclideanEmbedding_le_sum (a - z)
    linarith [(hc 0).2, (hc 1).2]

/-- `x^{n q} = (x^n)^q`. -/
theorem rpow_natCast_mul_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (q : ℝ) :
    x ^ ((n : ℝ) * q) = (x ^ n) ^ q := by
  rw [Real.rpow_mul hx, Real.rpow_natCast]

section Data

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The Lipschitz bounds of the corrector and their moments**: the bounds `Λ i x` of
`stepSix_data` satisfy `E[(1 + Λ i x)^q] ≤ (B q^κ)^q` for all `q ≥ 1`. -/
theorem stepOne_lipschitz_data (hR3 : ArmstrongDarioOrderZeroTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ (Λ : Fin 2 → Vertex 2 → Configuration 2 → ℝ) (B κ : ℝ), 0 < B ∧ 0 < κ ∧
      (∀ i x, Measurable (Λ i x)) ∧ (∀ i x ω, 0 ≤ Λ i x ω) ∧
      (∀ i, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
        (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω) ∧
      (∀ i x (q : ℝ), 1 ≤ q → ∫⁻ ω, ENNReal.ofReal (1 + Λ i x ω) ^ q ∂latticeBondLaw 2 p ≤
        ENNReal.ofReal ((B * q ^ κ) ^ q)) := by
  obtain ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXO, hlip⟩ :=
    lipschitz_correctorDiff hG hGv hR3 hpc hp1 hGae
  have hD0 : 0 < θ * (4 / s) ^ (1 / s) + 2 := by positivity
  have hQ : ∀ i : Fin 2, ∑ j, |(Pi.single i (1 : ℝ) : Fin 2 → ℝ) j| = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  refine ⟨fun i x ω => (L * max (X (configurationTranslation (-x) ω)) 2 ^ 2 + 1) *
      ∑ j, |(Pi.single i (1 : ℝ) : Fin 2 → ℝ) j|,
    48 * (L + 1) * (θ * (4 / s) ^ (1 / s) + 2) ^ 4, 4 / s, by positivity, by positivity,
    fun i x => ?_, fun i x ω => ?_, fun i => ae_all_iff.2 fun x => hlip _ x, fun i x q hq => ?_⟩
  · exact ((((hXm.comp (measurable_configurationTranslation (-x))).max
      measurable_const).pow_const 2).const_mul L |>.add_const 1).mul_const _
  · simp only [hQ]
    positivity
  · have hq0 : 0 < q := by linarith
    simp only [hQ, mul_one]
    have hpt : ∀ ω, ENNReal.ofReal (1 + (L * max (X (configurationTranslation (-x) ω)) 2 ^ 2 + 1))
        ^ q ≤ ENNReal.ofReal ((L + 1) ^ q * (X (configurationTranslation (-x) ω) + 2) ^ (4 * q)) := by
      intro ω
      have hY0 : 0 ≤ X (configurationTranslation (-x) ω) := hX0 _
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      set Y := X (configurationTranslation (-x) ω)
      have h1 : 1 + (L * max Y 2 ^ 2 + 1) ≤ (L + 1) * (Y + 2) ^ 2 := by
        have hm : max Y 2 ^ 2 ≤ (Y + 2) ^ 2 :=
          pow_le_pow_left₀ (le_max_of_le_right (by norm_num)) (max_le (by linarith) (by linarith)) 2
        have h4 : 4 ≤ (Y + 2) ^ 2 := by nlinarith
        nlinarith
      have h2 : (Y + 2) ^ 2 ≤ (Y + 2) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      calc (1 + (L * max Y 2 ^ 2 + 1)) ^ q ≤ ((L + 1) * (Y + 2) ^ 4) ^ q :=
            Real.rpow_le_rpow (by positivity)
              (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) hq0.le
        _ = (L + 1) ^ q * (Y + 2) ^ (4 * q) := by
            rw [Real.mul_rpow (by positivity) (by positivity)]
            have := rpow_natCast_mul_eq (by positivity : 0 ≤ Y + 2) 4 q
            simp only [Nat.cast_ofNat] at this
            rw [this]
    calc ∫⁻ ω, ENNReal.ofReal (1 + (L * max (X (configurationTranslation (-x) ω)) 2 ^ 2 + 1)) ^ q
          ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, ENNReal.ofReal ((L + 1) ^ q * (X (configurationTranslation (-x) ω) + 2) ^ (4 * q))
            ∂latticeBondLaw 2 p := lintegral_mono hpt
      _ = ENNReal.ofReal ((L + 1) ^ q) *
            ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * q)) ∂latticeBondLaw 2 p := by
          simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (L + 1) ^ q by positivity)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact (measurePreserving_configurationTranslation p (-x)).lintegral_comp
            ((hXm.add_const 2).pow_const _).ennreal_ofReal
      _ ≤ ENNReal.ofReal ((L + 1) ^ q) *
            ENNReal.ofReal (3 * (2 * (θ * (4 / s) ^ (1 / s) + 2) * q ^ (1 / s)) ^ (4 * q)) := by
          gcongr
          exact lintegral_add_two_rpow_le hs hθ hXm hX0 hXO hq
      _ ≤ ENNReal.ofReal ((48 * (L + 1) * (θ * (4 / s) ^ (1 / s) + 2) ^ 4 * q ^ (4 / s)) ^ q) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          set D := θ * (4 / s) ^ (1 / s) + 2
          have e1 : (2 * D * q ^ (1 / s)) ^ (4 * q) = (16 * D ^ 4 * q ^ (4 / s)) ^ q := by
            have := rpow_natCast_mul_eq (by positivity : 0 ≤ 2 * D * q ^ (1 / s)) 4 q
            simp only [Nat.cast_ofNat] at this
            rw [this]
            congr 1
            rw [mul_pow, mul_pow, ← Real.rpow_natCast (q ^ (1 / s)) 4,
              ← Real.rpow_mul hq0.le, show 1 / s * ((4 : ℕ) : ℝ) = 4 / s by push_cast; ring]
            norm_num
          have h3 : (3 : ℝ) ≤ 3 ^ q := by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hq
          rw [e1]
          calc (L + 1) ^ q * (3 * (16 * D ^ 4 * q ^ (4 / s)) ^ q)
              ≤ (L + 1) ^ q * (3 ^ q * (16 * D ^ 4 * q ^ (4 / s)) ^ q) := by gcongr
            _ = (48 * (L + 1) * D ^ 4 * q ^ (4 / s)) ^ q := by
                rw [← Real.mul_rpow (by norm_num) (by positivity),
                  ← Real.mul_rpow (by positivity) (by positivity)]
                congr 1
                ring

end Data

/-- The local factor of Step 1 at the bond `e` seen from `y`, for the side `n`, computed in the
configuration itself. -/
noncomputable def stepOneFactorSelfAt (Λ : Vertex 2 → Configuration 2 → ℝ) (C₀ C : ℕ)
    (e : Bond 2) (y : Vertex 2) (n : ℕ) (ω : Configuration 2) : ℝ≥0∞ :=
  if y ∈ supBox (bondBase e) (C₀ * C * n) then
    ENNReal.ofReal ((supBox (bondBase e) (C₀ * C * n)).card *
      (8 * ∑ z ∈ supBox (bondBase e) ((C₀ * C * n + 1) + 5 * (C * (C * n))), Λ z ω) ^ 2)
  else 0

/-- The local factor of Step 1 at the bond `e` seen from `y`, computed in the configuration
itself, with the side of its partition cube at the base of `e`. -/
noncomputable def stepOneFactorSelf (Λ : Vertex 2 → Configuration 2 → ℝ) (C₀ C : ℕ) (e : Bond 2)
    (y : Vertex 2) (ω : Configuration 2) : ℝ≥0∞ :=
  stepOneFactorSelfAt Λ C₀ C e y
    ⌊TriadicCube.stoppingSize (planarGoodCubes ω) (bondBase e)⌋₊ ω

theorem stepOneFactor_eq_self (Λ : Vertex 2 → Configuration 2 → ℝ) (C₀ C : ℕ) (e : Bond 2)
    (y : Vertex 2) (ω : Configuration 2) :
    stepOneFactor Λ C₀ C e y ω = stepOneFactorSelf Λ C₀ C e y (setBond e true ω) := by
  unfold stepOneFactor stepOneFactorSelf stepOneFactorAt stepOneFactorSelfAt flipSide
  rfl

theorem measurable_stepOneFactorSelf {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (C₀ C : ℕ) (e : Bond 2) (y : Vertex 2) :
    Measurable (stepOneFactorSelf Λ C₀ C e y) := by
  have hF : ∀ n, Measurable (stepOneFactorSelfAt Λ C₀ C e y n) := fun n => by
    by_cases hc : y ∈ supBox (bondBase e) (C₀ * C * n)
    · unfold stepOneFactorSelfAt
      simp only [if_pos hc]
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul (((Finset.measurable_sum _
        fun z _ => hΛm z).const_mul 8).pow_const 2))
    · unfold stepOneFactorSelfAt
      simp only [if_neg hc]
      exact measurable_const
  have h : Measurable fun x : Configuration 2 × ℕ => stepOneFactorSelfAt Λ C₀ C e y x.2 x.1 :=
    measurable_from_prod_countable_left fun n => hF n
  have e' : stepOneFactorSelf Λ C₀ C e y =
      (fun x : Configuration 2 × ℕ => stepOneFactorSelfAt Λ C₀ C e y x.2 x.1) ∘
        (fun ω => (ω, ⌊TriadicCube.stoppingSize (planarGoodCubes ω) (bondBase e)⌋₊)) := rfl
  rw [e']
  exact h.comp (measurable_id.prodMk
    (Nat.measurable_floor.comp (measurable_stoppingSize_planar (bondBase e))))

/-- The sum of `1 + Λ` over the ball of radius `κ size(□_𝒫(v))` around `v`. -/
noncomputable def stepOneBallSum (Λ : Vertex 2 → Configuration 2 → ℝ) (κ : ℝ) (v : Vertex 2)
    (ω : Configuration 2) : ℝ≥0∞ :=
  ∑' z, if ‖latticeEuclideanEmbedding (z - v)‖ ≤ κ * TriadicCube.stoppingSize (planarGoodCubes ω) v
    then ENNReal.ofReal (1 + Λ z ω) else 0

theorem measurable_stepOneBallSum {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (κ : ℝ) (v : Vertex 2) : Measurable (stepOneBallSum Λ κ v) :=
  Measurable.tsum fun z => Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_planar v).const_mul κ))
    ((measurable_const.add (hΛm z)).ennreal_ofReal) measurable_const

/-- **The local factor on the partition event**: `F_e ≤ 1{|a_e - y| ≤ κ₁ s} · 64 T³`, with
`κ₁ = 2 (C₀ C + 1)`, `s = size(□_𝒫(a_e))` and `T` the sum of `1 + Λ` over the ball of radius
`κ₃ s`, `κ₃ = 2 (C₀ C + 1 + 5 C²)`. -/
theorem stepOneFactorSelf_le {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛ0 : ∀ z ω, 0 ≤ Λ z ω)
    (C₀ C : ℕ) (e : Bond 2) (y : Vertex 2) {ω : Configuration 2} (hP : PlanarPartitionEvent ω) :
    stepOneFactorSelf Λ C₀ C e y ω ≤
      {ω' | ‖latticeEuclideanEmbedding (bondBase e - y)‖ ≤
          2 * ((C₀ : ℝ) * C + 1) * TriadicCube.stoppingSize (planarGoodCubes ω') (bondBase e)}.indicator
        (fun ω' => ENNReal.ofReal 64 *
          stepOneBallSum Λ (2 * ((C₀ : ℝ) * C + 1 + 5 * (C : ℝ) ^ 2)) (bondBase e) ω' ^ 3) ω := by
  set a := bondBase e
  have hS : TriadicCube.stoppingSize (planarGoodCubes ω) a =
      ((3 ^ (planarPartCube ω a).scale : ℕ) : ℝ) := by
    rw [TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP _).1 (planarPartCube_spec hP _).2]
    push_cast
    rfl
  set n : ℕ := 3 ^ (planarPartCube ω a).scale with hn
  have hn1 : 1 ≤ n := Nat.one_le_pow _ _ (by norm_num)
  have hfl : ⌊TriadicCube.stoppingSize (planarGoodCubes ω) a⌋₊ = n := by
    rw [hS, Nat.floor_natCast]
  unfold stepOneFactorSelf stepOneFactorSelfAt
  rw [hfl]
  split_ifs with hy
  · have hA : ‖latticeEuclideanEmbedding (a - y)‖ ≤
        2 * ((C₀ : ℝ) * C + 1) * TriadicCube.stoppingSize (planarGoodCubes ω) a := by
      have h := (norm_sub_le_of_mem_supBox hy).2
      rw [hS]
      have : ((C₀ * C * n : ℕ) : ℝ) ≤ ((C₀ : ℝ) * C + 1) * n := by
        push_cast
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    rw [Set.indicator_of_mem (show ω ∈ {ω' | ‖latticeEuclideanEmbedding (a - y)‖ ≤
      2 * ((C₀ : ℝ) * C + 1) * TriadicCube.stoppingSize (planarGoodCubes ω') a} from hA)]
    set B := supBox a (C₀ * C * n)
    set B' := supBox a ((C₀ * C * n + 1) + 5 * (C * (C * n)))
    have hBB' : B ⊆ B' := supBox_subset_of_le a (by omega)
    set T₀ := ∑ z ∈ B', (1 + Λ z ω) with hT₀
    have hcard : (B.card : ℝ) ≤ T₀ := by
      have h1 : (B.card : ℝ) ≤ B'.card := by exact_mod_cast Finset.card_le_card hBB'
      have h2 : (B'.card : ℝ) = ∑ z ∈ B', (1 : ℝ) := by simp
      rw [h2] at h1
      exact h1.trans (Finset.sum_le_sum fun z _ => by linarith [hΛ0 z ω])
    have hsum : ∑ z ∈ B', Λ z ω ≤ T₀ := Finset.sum_le_sum fun z _ => by linarith
    have hΛs0 : 0 ≤ ∑ z ∈ B', Λ z ω := Finset.sum_nonneg fun z _ => hΛ0 z ω
    have hT0 : 0 ≤ T₀ := hΛs0.trans hsum
    have hreal : (B.card : ℝ) * (8 * ∑ z ∈ B', Λ z ω) ^ 2 ≤ 64 * T₀ ^ 3 := by
      have hsq : (∑ z ∈ B', Λ z ω) ^ 2 ≤ T₀ ^ 2 := pow_le_pow_left₀ hΛs0 hsum 2
      have := mul_le_mul hcard hsq (sq_nonneg _) hT0
      nlinarith
    have hball : ∀ z ∈ B', ‖latticeEuclideanEmbedding (z - a)‖ ≤
        2 * ((C₀ : ℝ) * C + 1 + 5 * (C : ℝ) ^ 2) * TriadicCube.stoppingSize (planarGoodCubes ω) a := by
      intro z hz
      have h := (norm_sub_le_of_mem_supBox hz).1
      rw [hS]
      have : (((C₀ * C * n + 1) + 5 * (C * (C * n)) : ℕ) : ℝ) ≤
          ((C₀ : ℝ) * C + 1 + 5 * (C : ℝ) ^ 2) * n := by
        push_cast
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith
      linarith
    have hT : ENNReal.ofReal T₀ ≤
        stepOneBallSum Λ (2 * ((C₀ : ℝ) * C + 1 + 5 * (C : ℝ) ^ 2)) a ω := by
      rw [hT₀, ENNReal.ofReal_sum_of_nonneg fun z _ => by linarith [hΛ0 z ω]]
      unfold stepOneBallSum
      calc ∑ z ∈ B', ENNReal.ofReal (1 + Λ z ω)
          = ∑ z ∈ B', (if ‖latticeEuclideanEmbedding (z - a)‖ ≤
              2 * ((C₀ : ℝ) * C + 1 + 5 * (C : ℝ) ^ 2) *
                TriadicCube.stoppingSize (planarGoodCubes ω) a
              then ENNReal.ofReal (1 + Λ z ω) else 0) :=
            Finset.sum_congr rfl fun z hz => by rw [if_pos (hball z hz)]
        _ ≤ _ := ENNReal.sum_le_tsum _
    calc ENNReal.ofReal ((B.card : ℝ) * (8 * ∑ z ∈ B', Λ z ω) ^ 2)
        ≤ ENNReal.ofReal (64 * T₀ ^ 3) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal 64 * ENNReal.ofReal T₀ ^ 3 := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hT0]
      _ ≤ _ := by gcongr
  · exact zero_le

end Rigidity.Corrector

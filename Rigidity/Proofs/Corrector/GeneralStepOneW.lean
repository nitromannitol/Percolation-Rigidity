import Rigidity.Proofs.Corrector.GeneralStepOneGrowth

/-!
# The local factors of Step 1 of Lemma 3.3 of Dario on `ℤᵈ`

Dario bounds the sum (3.18) `W(y) = Σ_e 1{y ∈ B_e} F_e` through (3.19)-(3.20), the random-ball
bounds of Proposition 2.15 and (3.12). The pieces on `ℤᵈ`, as in the planar file `DarioStepOneW`:

* `stepOne_lipschitz_data`: Lipschitz bounds `Λ` of the corrector (from `lipschitz_correctorDiff`)
  with the moments `E[(1 + Λ(x))^q] ≤ (B q^κ)^q` of the single bounds (from
  `lintegral_add_two_rpow_le`).
* `stepOneFactorSelf`: the factor `F_e` of `W` computed in the configuration itself; the factor of
  `W` at `ω` is its value at `ω^{e,1}` (`stepOneFactor_eq_self`), so (3.12) in the form
  `E[f(ω^{e,1})] ≤ p^{-1} E[f]` removes the flip.
* `stepOneFactorSelf_le`: on the partition event, `F_e ≤ 1{|a_e - y| ≤ κ₁ s} · 16 d² T³` with
  `s = size(□_𝒫(a_e))` and `T` the sum of `1 + Λ` over the ball of radius `κ₃ s` around `a_e`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ}

/-- The points of a box of radius `r` are within Euclidean distance `d r` of its centre. -/
theorem norm_sub_le_of_mem_supBox {a z : Vertex d} {r : ℕ} (h : z ∈ supBox a r) :
    ‖latticeEuclideanEmbedding (z - a)‖ ≤ d * r ∧ ‖latticeEuclideanEmbedding (a - z)‖ ≤ d * r := by
  have hc : ∀ i, |(((z - a) i : ℤ) : ℝ)| ≤ r ∧ |(((a - z) i : ℤ) : ℝ)| ≤ r := by
    intro i
    have hi := (mem_supBox.1 h) i
    have hi' : |a i - z i| ≤ (r : ℤ) := by rw [abs_sub_comm]; exact hi
    constructor
    · rw [Pi.sub_apply]
      exact_mod_cast hi
    · rw [Pi.sub_apply]
      exact_mod_cast hi'
  exact ⟨norm_latticeEuclideanEmbedding_le_of_abs_le (Nat.cast_nonneg r) fun i => (hc i).1,
    norm_latticeEuclideanEmbedding_le_of_abs_le (Nat.cast_nonneg r) fun i => (hc i).2⟩

section Data

variable [NeZero d] {G : Set (Configuration d)} (hG : MeasurableSet G)
  (hGv : G ⊆ correctorValidEvent d)

/-- **The Lipschitz bounds of the corrector and their moments**: bounds `Λ i x` of the corrector
increments of slope `e_i` along the open edges at `x` with `E[(1 + Λ i x)^q] ≤ (B q^κ)^q` for all
`q ≥ 1`. -/
theorem stepOne_lipschitz_data (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ (Λ : Fin d → Vertex d → Configuration d → ℝ) (B κ : ℝ), 0 < B ∧ 0 < κ ∧
      (∀ i x, Measurable (Λ i x)) ∧ (∀ i x ω, 0 ≤ Λ i x ω) ∧
      (∀ i, ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
        (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω) ∧
      (∀ i x (q : ℝ), 1 ≤ q → ∫⁻ ω, ENNReal.ofReal (1 + Λ i x ω) ^ q ∂latticeBondLaw d p ≤
        ENNReal.ofReal ((B * q ^ κ) ^ q)) := by
  obtain ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXO, hlip⟩ :=
    lipschitz_correctorDiff hG hGv hd hpc hp1 hGae
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  set D := θ * (4 / s) ^ (1 / s) + 2 with hD
  have hD2 : 2 ≤ D := by have : 0 ≤ θ * (4 / s) ^ (1 / s) := (by positivity); linarith
  have hQ : ∀ i : Fin d, ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j| = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  refine ⟨fun i x ω => (L * max (X (configurationTranslation (-x) ω)) 2 ^ d + 1) *
      ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j|,
    3 * (L + 2) * (2 * D * (d : ℝ) ^ (1 / s)) ^ (4 * d), 4 * d / s, by positivity, by positivity,
    fun i x => ?_, fun i x ω => ?_, fun i => ae_all_iff.2 fun x => hlip _ x, fun i x q hq => ?_⟩
  · exact ((((hXm.comp (measurable_configurationTranslation (-x))).max
      measurable_const).pow_const d).const_mul L |>.add_const 1).mul_const _
  · simp only [hQ]
    positivity
  · have hq0 : 0 < q := by linarith
    set r : ℝ := d * q with hr
    have hr1 : 1 ≤ r := by rw [hr]; nlinarith
    simp only [hQ, mul_one]
    have hpt : ∀ ω, ENNReal.ofReal (1 + (L * max (X (configurationTranslation (-x) ω)) 2 ^ d + 1))
        ^ q ≤ ENNReal.ofReal ((L + 2) ^ q * (X (configurationTranslation (-x) ω) + 2) ^ (4 * r)) := by
      intro ω
      have hY0 : 0 ≤ X (configurationTranslation (-x) ω) := hX0 _
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      set Y := X (configurationTranslation (-x) ω)
      have h1 : 1 + (L * max Y 2 ^ d + 1) ≤ (L + 2) * (Y + 2) ^ (4 * d) := by
        have hm : max Y 2 ^ d ≤ (Y + 2) ^ d :=
          pow_le_pow_left₀ (le_max_of_le_right (by norm_num)) (max_le (by linarith) (by linarith)) d
        have h4 : 1 ≤ (Y + 2) ^ d := one_le_pow₀ (by linarith)
        have h5 : (Y + 2) ^ d ≤ (Y + 2) ^ (4 * d) :=
          pow_le_pow_right₀ (by linarith) (by omega)
        nlinarith
      calc (1 + (L * max Y 2 ^ d + 1)) ^ q ≤ ((L + 2) * (Y + 2) ^ (4 * d)) ^ q :=
            Real.rpow_le_rpow (by positivity) h1 hq0.le
        _ = (L + 2) ^ q * (Y + 2) ^ (4 * r) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul (by positivity)]
            congr 2
            rw [hr]
            push_cast
            ring
    calc ∫⁻ ω, ENNReal.ofReal (1 + (L * max (X (configurationTranslation (-x) ω)) 2 ^ d + 1)) ^ q
          ∂latticeBondLaw d p
        ≤ ∫⁻ ω, ENNReal.ofReal ((L + 2) ^ q * (X (configurationTranslation (-x) ω) + 2) ^ (4 * r))
            ∂latticeBondLaw d p := lintegral_mono hpt
      _ = ENNReal.ofReal ((L + 2) ^ q) *
            ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * r)) ∂latticeBondLaw d p := by
          simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (L + 2) ^ q by positivity)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact (measurePreserving_configurationTranslation p (-x)).lintegral_comp
            ((hXm.add_const 2).pow_const _).ennreal_ofReal
      _ ≤ ENNReal.ofReal ((L + 2) ^ q) *
            ENNReal.ofReal (3 * (2 * D * r ^ (1 / s)) ^ (4 * r)) := by
          gcongr
          exact lintegral_add_two_rpow_le hs hθ hXm hX0 hXO hr1
      _ ≤ ENNReal.ofReal
            ((3 * (L + 2) * (2 * D * (d : ℝ) ^ (1 / s)) ^ (4 * d) * q ^ (4 * d / s)) ^ q) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          -- `(2 D (d q)^{1/s})^{4 d q} = ((2 D d^{1/s})^{4d} q^{4d/s})^q`
          have e1 : (2 * D * r ^ (1 / s)) ^ (4 * r) =
              ((2 * D * (d : ℝ) ^ (1 / s)) ^ (4 * d) * q ^ (4 * d / s)) ^ q := by
            have h4r : 4 * r = ((4 * d : ℕ) : ℝ) * q := by rw [hr]; push_cast; ring
            have hx0 : 0 ≤ 2 * D * r ^ (1 / s) := by positivity
            have hqd : (q ^ (1 / s)) ^ (4 * d) = q ^ (4 * (d : ℝ) / s) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
              congr 1
              push_cast
              ring
            rw [h4r, Real.rpow_mul hx0, Real.rpow_natCast, hr, Real.mul_rpow hd0.le hq0.le, ← hqd]
            congr 1
            ring
          have h3 : (3 : ℝ) ≤ 3 ^ q := by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hq
          rw [e1]
          calc (L + 2) ^ q * (3 * ((2 * D * (d : ℝ) ^ (1 / s)) ^ (4 * d) * q ^ (4 * d / s)) ^ q)
              ≤ (L + 2) ^ q *
                  (3 ^ q * ((2 * D * (d : ℝ) ^ (1 / s)) ^ (4 * d) * q ^ (4 * d / s)) ^ q) := by
                gcongr
            _ = (3 * (L + 2) * (2 * D * (d : ℝ) ^ (1 / s)) ^ (4 * d) * q ^ (4 * d / s)) ^ q := by
                rw [← Real.mul_rpow (by norm_num) (by positivity),
                  ← Real.mul_rpow (by positivity) (by positivity)]
                congr 1
                ring

end Data

/-- The local factor of Step 1 at the bond `e` seen from `y`, for the side `n`, computed in the
configuration itself. -/
noncomputable def stepOneFactorSelfAt (Λ : Vertex d → Configuration d → ℝ) (C₀ C : ℕ)
    (e : Bond d) (y : Vertex d) (n : ℕ) (ω : Configuration d) : ℝ≥0∞ :=
  if y ∈ supBox (bondBase e) (C₀ * C * n) then
    ENNReal.ofReal ((supBox (bondBase e) (C₀ * C * n)).card *
      (4 * d * ∑ z ∈ supBox (bondBase e) ((C₀ * C * n + 1) + 3 * (C * (C * n))), Λ z ω) ^ 2)
  else 0

/-- The local factor of Step 1 at the bond `e` seen from `y`, computed in the configuration
itself, with the side of its partition cube at the base of `e`. -/
noncomputable def stepOneFactorSelf (Λ : Vertex d → Configuration d → ℝ) (C₀ C : ℕ) (e : Bond d)
    (y : Vertex d) (ω : Configuration d) : ℝ≥0∞ :=
  stepOneFactorSelfAt Λ C₀ C e y
    ⌊TriadicCube.stoppingSize (TriadicCube.goodCubes ω) (bondBase e)⌋₊ ω

theorem stepOneFactor_eq_self (Λ : Vertex d → Configuration d → ℝ) (C₀ C : ℕ) (e : Bond d)
    (y : Vertex d) (ω : Configuration d) :
    stepOneFactor Λ C₀ C e y ω = stepOneFactorSelf Λ C₀ C e y (setBond e true ω) := by
  unfold stepOneFactor stepOneFactorSelf stepOneFactorAt stepOneFactorSelfAt flipSide
  rfl

theorem measurable_stepOneFactorSelf {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (C₀ C : ℕ) (e : Bond d) (y : Vertex d) :
    Measurable (stepOneFactorSelf Λ C₀ C e y) := by
  have hF : ∀ n, Measurable (stepOneFactorSelfAt Λ C₀ C e y n) := fun n => by
    by_cases hc : y ∈ supBox (bondBase e) (C₀ * C * n)
    · unfold stepOneFactorSelfAt
      simp only [if_pos hc]
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul (((Finset.measurable_sum _
        fun z _ => hΛm z).const_mul _).pow_const 2))
    · unfold stepOneFactorSelfAt
      simp only [if_neg hc]
      exact measurable_const
  have h : Measurable fun x : Configuration d × ℕ => stepOneFactorSelfAt Λ C₀ C e y x.2 x.1 :=
    measurable_from_prod_countable_left fun n => hF n
  have e' : stepOneFactorSelf Λ C₀ C e y =
      (fun x : Configuration d × ℕ => stepOneFactorSelfAt Λ C₀ C e y x.2 x.1) ∘
        (fun ω => (ω, ⌊TriadicCube.stoppingSize (TriadicCube.goodCubes ω) (bondBase e)⌋₊)) := rfl
  rw [e']
  exact h.comp (measurable_id.prodMk
    (Nat.measurable_floor.comp (measurable_stoppingSize_goodCubes (bondBase e))))

/-- The sum of `1 + Λ` over the ball of radius `κ size(□_𝒫(v))` around `v`. -/
noncomputable def stepOneBallSum (Λ : Vertex d → Configuration d → ℝ) (κ : ℝ) (v : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑' z, if ‖latticeEuclideanEmbedding (z - v)‖ ≤
      κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v
    then ENNReal.ofReal (1 + Λ z ω) else 0

theorem measurable_stepOneBallSum {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (κ : ℝ) (v : Vertex d) : Measurable (stepOneBallSum Λ κ v) :=
  Measurable.tsum fun z => Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_goodCubes v).const_mul κ))
    ((measurable_const.add (hΛm z)).ennreal_ofReal) measurable_const

/-- **The local factor on the partition event**: `F_e ≤ 1{|a_e - y| ≤ κ₁ s} · 16 d² T³`, with
`κ₁ = d (C₀ C + 1)`, `s = size(□_𝒫(a_e))` and `T` the sum of `1 + Λ` over the ball of radius
`κ₃ s`, `κ₃ = d (C₀ C + 1 + 3 C²)`. -/
theorem stepOneFactorSelf_le {Λ : Vertex d → Configuration d → ℝ} (hΛ0 : ∀ z ω, 0 ≤ Λ z ω)
    (C₀ C : ℕ) (e : Bond d) (y : Vertex d) {ω : Configuration d} (hP : PartitionEvent ω) :
    stepOneFactorSelf Λ C₀ C e y ω ≤
      {ω' | ‖latticeEuclideanEmbedding (bondBase e - y)‖ ≤
          d * ((C₀ : ℝ) * C + 1) *
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω') (bondBase e)}.indicator
        (fun ω' => ENNReal.ofReal (16 * d ^ 2) *
          stepOneBallSum Λ (d * ((C₀ : ℝ) * C + 1 + 3 * (C : ℝ) ^ 2)) (bondBase e) ω' ^ 3) ω := by
  set a := bondBase e
  have hS : TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a =
      ((3 ^ (partitionCube ω a).scale : ℕ) : ℝ) := by
    rw [TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP _) (partitionCube_spec hP _).2]
    push_cast
    rfl
  set n : ℕ := 3 ^ (partitionCube ω a).scale with hn
  have hn1 : 1 ≤ n := Nat.one_le_pow _ _ (by norm_num)
  have hfl : ⌊TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a⌋₊ = n := by
    rw [hS, Nat.floor_natCast]
  unfold stepOneFactorSelf stepOneFactorSelfAt
  rw [hfl]
  split_ifs with hy
  · have hA : ‖latticeEuclideanEmbedding (a - y)‖ ≤
        d * ((C₀ : ℝ) * C + 1) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a := by
      have h := (norm_sub_le_of_mem_supBox hy).2
      rw [hS]
      have : ((C₀ * C * n : ℕ) : ℝ) ≤ ((C₀ : ℝ) * C + 1) * n := by
        push_cast
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      calc ‖latticeEuclideanEmbedding (a - y)‖ ≤ d * ((C₀ * C * n : ℕ) : ℝ) := h
        _ ≤ d * (((C₀ : ℝ) * C + 1) * n) := mul_le_mul_of_nonneg_left this hd0
        _ = d * ((C₀ : ℝ) * C + 1) * n := by ring
    rw [Set.indicator_of_mem (show ω ∈ {ω' | ‖latticeEuclideanEmbedding (a - y)‖ ≤
      d * ((C₀ : ℝ) * C + 1) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω') a} from hA)]
    set B := supBox a (C₀ * C * n)
    set B' := supBox a ((C₀ * C * n + 1) + 3 * (C * (C * n)))
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
    have hreal : (B.card : ℝ) * (4 * d * ∑ z ∈ B', Λ z ω) ^ 2 ≤ 16 * d ^ 2 * T₀ ^ 3 := by
      have hsq : (∑ z ∈ B', Λ z ω) ^ 2 ≤ T₀ ^ 2 := pow_le_pow_left₀ hΛs0 hsum 2
      have := mul_le_mul hcard hsq (sq_nonneg _) hT0
      have hd2 : (0 : ℝ) ≤ 16 * d ^ 2 := by positivity
      calc (B.card : ℝ) * (4 * d * ∑ z ∈ B', Λ z ω) ^ 2
          = 16 * d ^ 2 * ((B.card : ℝ) * (∑ z ∈ B', Λ z ω) ^ 2) := by ring
        _ ≤ 16 * d ^ 2 * (T₀ * T₀ ^ 2) := mul_le_mul_of_nonneg_left this hd2
        _ = 16 * d ^ 2 * T₀ ^ 3 := by ring
    have hball : ∀ z ∈ B', ‖latticeEuclideanEmbedding (z - a)‖ ≤
        d * ((C₀ : ℝ) * C + 1 + 3 * (C : ℝ) ^ 2) *
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a := by
      intro z hz
      have h := (norm_sub_le_of_mem_supBox hz).1
      rw [hS]
      have : (((C₀ * C * n + 1) + 3 * (C * (C * n)) : ℕ) : ℝ) ≤
          ((C₀ : ℝ) * C + 1 + 3 * (C : ℝ) ^ 2) * n := by
        push_cast
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      calc ‖latticeEuclideanEmbedding (z - a)‖
          ≤ d * (((C₀ * C * n + 1) + 3 * (C * (C * n)) : ℕ) : ℝ) := h
        _ ≤ d * (((C₀ : ℝ) * C + 1 + 3 * (C : ℝ) ^ 2) * n) := mul_le_mul_of_nonneg_left this hd0
        _ = d * ((C₀ : ℝ) * C + 1 + 3 * (C : ℝ) ^ 2) * n := by ring
    have hT : ENNReal.ofReal T₀ ≤
        stepOneBallSum Λ (d * ((C₀ : ℝ) * C + 1 + 3 * (C : ℝ) ^ 2)) a ω := by
      rw [hT₀, ENNReal.ofReal_sum_of_nonneg fun z _ => by linarith [hΛ0 z ω]]
      unfold stepOneBallSum
      calc ∑ z ∈ B', ENNReal.ofReal (1 + Λ z ω)
          = ∑ z ∈ B', (if ‖latticeEuclideanEmbedding (z - a)‖ ≤
              d * ((C₀ : ℝ) * C + 1 + 3 * (C : ℝ) ^ 2) *
                TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a
              then ENNReal.ofReal (1 + Λ z ω) else 0) :=
            Finset.sum_congr rfl fun z hz => by rw [if_pos (hball z hz)]
        _ ≤ _ := ENNReal.sum_le_tsum _
    calc ENNReal.ofReal ((B.card : ℝ) * (4 * d * ∑ z ∈ B', Λ z ω) ^ 2)
        ≤ ENNReal.ofReal (16 * d ^ 2 * T₀ ^ 3) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (16 * d ^ 2) * ENNReal.ofReal T₀ ^ 3 := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hT0]
      _ ≤ _ := by gcongr
  · exact zero_le

end Rigidity.Corrector.GeneralDim

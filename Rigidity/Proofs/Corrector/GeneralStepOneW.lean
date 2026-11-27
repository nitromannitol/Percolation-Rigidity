import Rigidity.Proofs.Corrector.GeneralStepOneGrowth

/-!
# The local factors of Step 1 of Lemma 3.3 of Dario on `ℤᵈ`

Dario bounds the sum (3.18) `W(y) = Σ_e 1{y ∈ B_e} F_e` through (3.19)-(3.20), the random-ball
bounds of Proposition 2.15 and (3.12). The pieces on `ℤᵈ`, as in the planar file `DarioStepOneW`:

* `stepOne_lipschitz_data`: Lipschitz bounds `Λ` of the corrector (from `lipschitz_correctorDiff`)
  with the moments `E[(1 + Λ(x))^q] ≤ (B q^κ)^q` of the single bounds (from
  `lintegral_add_two_rpow_le`).
* `stepOneFactor_le`: on the partition events of both flips,
  `F_e ≤ 1{|a_e - y| ≤ κ₁ S} · 16 d² (U(ω^{e,0}) + U(ω^{e,1}))³` with `S` the scale of the flips of
  `e` at its base `a_e` (corrected Lemma 3.5) and `U(ζ)` the sum of `1 + Λ(·, ζ^{e,1})` over the ball
  of radius `κ₃ size(□_{𝒫(ζ)}(a_e))` (`stepOneBallSum`), so that (3.12) in the form
  `E[f(ω^{e,b})] ≤ min(p, 1 - p)^{-1} E[f]` reduces the moments to those of the partition sizes and
  of a sum over a ball of random radius.
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
  · exact ((((hXm.comp (configurationTranslationMeasurableEquiv (-x)).measurable).max
      measurable_const).pow_const d).const_mul L |>.add_const 1).mul_const _
  · simp only [hQ]
    positivity
  · have hq0 : 0 < q := by linarith
    set r : ℝ := d * q with hr
    have hr1 : 1 ≤ r := by rw [hr]; nlinarith
    simp only [hQ, mul_one]
    have hpt : ∀ ω,
        ENNReal.ofReal (1 + (L * max (X (configurationTranslation (-x) ω)) 2 ^ d + 1)) ^ q ≤
          ENNReal.ofReal
            ((L + 2) ^ q * (X (configurationTranslation (-x) ω) + 2) ^ (4 * r)) := by
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
            ring_nf
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

theorem setBond_setBond (e : Bond d) (b b' : Bool) (ω : Configuration d) :
    setBond e b (setBond e b' ω) = setBond e b ω := by
  unfold setBond
  exact Function.update_idem b' b ω

/-- The sum of `1 + Λ(·, ζ^{e,1})` over the ball of radius `κ size(□_{𝒫(ζ)}(a_e))` around the base
`a_e` of `e`. -/
noncomputable def stepOneBallSum (Λ : Vertex d → Configuration d → ℝ) (κ : ℝ) (e : Bond d)
    (ζ : Configuration d) : ℝ≥0∞ :=
  ∑' z, if ‖latticeEuclideanEmbedding (z - bondBase e)‖ ≤
      κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ζ) (bondBase e)
    then ENNReal.ofReal (1 + Λ z (setBond e true ζ)) else 0

theorem measurable_stepOneBallSum {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (κ : ℝ) (e : Bond d) : Measurable (stepOneBallSum Λ κ e) :=
  Measurable.tsum fun z => Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_goodCubes (bondBase e)).const_mul κ))
    ((measurable_const.add ((hΛm z).comp (measurable_setBond e true))).ennreal_ofReal)
    measurable_const

/-- The scale `S` of the flips of `e` at its base, through the stopping sizes, as a real. -/
noncomputable def flipSideReal (e : Bond d) (ω : Configuration d) : ℝ :=
  max (TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e false ω)) (bondBase e))
    (TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e true ω)) (bondBase e))

theorem measurable_flipSideReal (e : Bond d) : Measurable (flipSideReal e) :=
  ((measurable_stoppingSize_goodCubes (bondBase e)).comp (measurable_setBond e false)).max
    ((measurable_stoppingSize_goodCubes (bondBase e)).comp (measurable_setBond e true))

/-- **The local factor on the partition events of both flips**:
`F_e ≤ 1{|a_e - y| ≤ κ₁ S} · 16 d² (U(ω^{e,0}) + U(ω^{e,1}))³`, with `κ₁ = d (C₀ + 1)`, `S` the scale
of the flips of `e` at its base `a_e` and `U = stepOneBallSum Λ κ₃ e`, `κ₃ = d (C₀ + 1 + 3 C)`. -/
theorem stepOneFactor_le {Λ : Vertex d → Configuration d → ℝ} (hΛ0 : ∀ z ω, 0 ≤ Λ z ω)
    (C₀ C : ℕ) (e : Bond d) (y : Vertex d) {ω : Configuration d}
    (hP₀ : PartitionEvent (setBond e false ω)) (hP₁ : PartitionEvent (setBond e true ω)) :
    stepOneFactor Λ C₀ C e y ω ≤
      {ω' | ‖latticeEuclideanEmbedding (bondBase e - y)‖ ≤
          d * ((C₀ : ℝ) + 1) * flipSideReal e ω'}.indicator
        (fun ω' => ENNReal.ofReal (16 * d ^ 2) *
          (stepOneBallSum Λ (d * ((C₀ : ℝ) + 1 + 3 * C)) e (setBond e false ω') +
            stepOneBallSum Λ (d * ((C₀ : ℝ) + 1 + 3 * C)) e (setBond e true ω')) ^ 3) ω := by
  set a := bondBase e
  set N : ℕ := flipScale e ω with hN
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_pow _ _ (by norm_num))
    (le_resampleScale_left (setBond e false ω) (setBond e true ω) a)
  have hS0 : TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e false ω)) a =
      ((3 ^ (partitionCube (setBond e false ω) a).scale : ℕ) : ℝ) :=
    stoppingSize_goodCubes_eq_cast hP₀ a
  have hS1 : TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e true ω)) a =
      ((3 ^ (partitionCube (setBond e true ω) a).scale : ℕ) : ℝ) :=
    stoppingSize_goodCubes_eq_cast hP₁ a
  have hSN : flipSideReal e ω = (N : ℝ) := by
    unfold flipSideReal
    rw [hS0, hS1, ← Nat.cast_max]
    rfl
  unfold stepOneFactor stepOneFactorAt
  rw [flipSide_eq hP₀ hP₁, ← hN]
  split_ifs with hy
  · have hA : ‖latticeEuclideanEmbedding (a - y)‖ ≤ d * ((C₀ : ℝ) + 1) * flipSideReal e ω := by
      have h := (norm_sub_le_of_mem_supBox hy).2
      rw [hSN]
      have : ((C₀ * N : ℕ) : ℝ) ≤ ((C₀ : ℝ) + 1) * N := by
        push_cast
        nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      calc ‖latticeEuclideanEmbedding (a - y)‖ ≤ d * ((C₀ * N : ℕ) : ℝ) := h
        _ ≤ d * (((C₀ : ℝ) + 1) * N) := mul_le_mul_of_nonneg_left this hd0
        _ = d * ((C₀ : ℝ) + 1) * N := by ring
    rw [Set.indicator_of_mem (show ω ∈ {ω' | ‖latticeEuclideanEmbedding (a - y)‖ ≤
      d * ((C₀ : ℝ) + 1) * flipSideReal e ω'} from hA)]
    set B := supBox a (C₀ * N)
    set B' := supBox a ((C₀ * N + 1) + 3 * (C * N))
    have hBB' : B ⊆ B' := supBox_subset_of_le a (by omega)
    set T₀ := ∑ z ∈ B', (1 + Λ z (setBond e true ω)) with hT₀
    have hcard : (B.card : ℝ) ≤ T₀ := by
      have h1 : (B.card : ℝ) ≤ B'.card := by exact_mod_cast Finset.card_le_card hBB'
      have h2 : (B'.card : ℝ) = ∑ z ∈ B', (1 : ℝ) := by simp
      rw [h2] at h1
      exact h1.trans (Finset.sum_le_sum fun z _ => by linarith [hΛ0 z (setBond e true ω)])
    have hsum : ∑ z ∈ B', Λ z (setBond e true ω) ≤ T₀ :=
      Finset.sum_le_sum fun z _ => by linarith
    have hΛs0 : 0 ≤ ∑ z ∈ B', Λ z (setBond e true ω) :=
      Finset.sum_nonneg fun z _ => hΛ0 z _
    have hT0 : 0 ≤ T₀ := hΛs0.trans hsum
    have hreal : (B.card : ℝ) * (4 * d * ∑ z ∈ B', Λ z (setBond e true ω)) ^ 2 ≤
        16 * d ^ 2 * T₀ ^ 3 := by
      have hsq : (∑ z ∈ B', Λ z (setBond e true ω)) ^ 2 ≤ T₀ ^ 2 := pow_le_pow_left₀ hΛs0 hsum 2
      have := mul_le_mul hcard hsq (sq_nonneg _) hT0
      have hd2 : (0 : ℝ) ≤ 16 * d ^ 2 := by positivity
      calc (B.card : ℝ) * (4 * d * ∑ z ∈ B', Λ z (setBond e true ω)) ^ 2
          = 16 * d ^ 2 * ((B.card : ℝ) * (∑ z ∈ B', Λ z (setBond e true ω)) ^ 2) := by ring
        _ ≤ 16 * d ^ 2 * (T₀ * T₀ ^ 2) := mul_le_mul_of_nonneg_left this hd2
        _ = 16 * d ^ 2 * T₀ ^ 3 := by ring
    -- the box `B'` lies in the ball of radius `κ₃ size` of the flip with the larger side
    have hball : ∀ z ∈ B', ‖latticeEuclideanEmbedding (z - a)‖ ≤
        d * ((C₀ : ℝ) + 1 + 3 * C) * N := by
      intro z hz
      have h := (norm_sub_le_of_mem_supBox hz).1
      have : (((C₀ * N + 1) + 3 * (C * N) : ℕ) : ℝ) ≤ ((C₀ : ℝ) + 1 + 3 * C) * N := by
        push_cast
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        nlinarith
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      calc ‖latticeEuclideanEmbedding (z - a)‖
          ≤ d * (((C₀ * N + 1) + 3 * (C * N) : ℕ) : ℝ) := h
        _ ≤ d * (((C₀ : ℝ) + 1 + 3 * C) * N) := mul_le_mul_of_nonneg_left this hd0
        _ = d * ((C₀ : ℝ) + 1 + 3 * C) * N := by ring
    have hT : ENNReal.ofReal T₀ ≤
        stepOneBallSum Λ (d * ((C₀ : ℝ) + 1 + 3 * C)) e (setBond e false ω) +
          stepOneBallSum Λ (d * ((C₀ : ℝ) + 1 + 3 * C)) e (setBond e true ω) := by
      have hNmax : (N : ℝ) = max (TriadicCube.stoppingSize (TriadicCube.goodCubes
          (setBond e false ω)) a) (TriadicCube.stoppingSize (TriadicCube.goodCubes
          (setBond e true ω)) a) := hSN.symm
      have key : ∀ b : Bool, (N : ℝ) = TriadicCube.stoppingSize
          (TriadicCube.goodCubes (setBond e b ω)) a →
          ENNReal.ofReal T₀ ≤ stepOneBallSum Λ (d * ((C₀ : ℝ) + 1 + 3 * C)) e (setBond e b ω) := by
        intro b hb
        rw [hT₀, ENNReal.ofReal_sum_of_nonneg fun z _ => by linarith [hΛ0 z (setBond e true ω)]]
        unfold stepOneBallSum
        calc ∑ z ∈ B', ENNReal.ofReal (1 + Λ z (setBond e true ω))
            = ∑ z ∈ B', (if ‖latticeEuclideanEmbedding (z - a)‖ ≤
                d * ((C₀ : ℝ) + 1 + 3 * C) *
                  TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e b ω)) a
                then ENNReal.ofReal (1 + Λ z (setBond e true (setBond e b ω))) else 0) :=
              Finset.sum_congr rfl fun z hz => by
                rw [if_pos (by rw [← hb]; exact hball z hz), setBond_setBond]
          _ ≤ _ := ENNReal.sum_le_tsum _
      rcases le_total (TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e false ω)) a)
          (TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e true ω)) a) with h | h
      · exact (key true (by rw [hNmax, max_eq_right h])).trans le_add_self
      · exact (key false (by rw [hNmax, max_eq_left h])).trans le_self_add
    calc ENNReal.ofReal ((B.card : ℝ) * (4 * d * ∑ z ∈ B', Λ z (setBond e true ω)) ^ 2)
        ≤ ENNReal.ofReal (16 * d ^ 2 * T₀ ^ 3) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (16 * d ^ 2) * ENNReal.ofReal T₀ ^ 3 := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hT0]
      _ ≤ _ := by gcongr
  · exact zero_le

end Rigidity.Corrector.GeneralDim

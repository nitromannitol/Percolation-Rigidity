import Rigidity.Proofs.Corrector.GeneralStepOneW
import Rigidity.Proofs.Corrector.GeneralVarianceSums
import Rigidity.Proofs.Corrector.DarioStepOneHolds

/-!
# Step 1 of Lemma 3.3 of Dario on `ℤᵈ` from Lemma 3.5

`stepOneW_moments`: the sums (3.18) `W(y) = Σ_e 1{y ∈ B_e} F_e` satisfy `E[W(y)^q] ≤ (A q^k)^q`
for all `y` and `q ≥ 1`, for the Lipschitz bounds `Λ` of `stepOne_lipschitz_data`. For each bond,
the factor is at most `1{|a_e - y| ≤ κ₁ S} 16 d² (U(ω^{e,0}) + U(ω^{e,1}))³` (`stepOneFactor_le`), with
`S` the scale of the corrected Lemma 3.5 and `U` a sum over a ball of random radius; forcing one
bond changes the law by a density at most `min(p, 1 - p)⁻¹` (`lintegral_comp_setBond_le`, (3.12)),
so the probability of the event decays exponentially in `|a_e - y|` with the tail of the partition
sizes, and the moments of `U(ω^{e,b})` are those of a ball sum (Cauchy–Schwarz on the event).
Jensen's inequality over the bonds (`lintegral_tsum_rpow_le_of_decay`) then bounds the moments of
`W(y)`.

`flipSumOne_isOsBond_of_resample`: given the corrected Lemma 3.5 for the partition into good cubes of
`ℤᵈ` (`ResamplePartitionBound C₀ C`), the Step 1 sum `Σ_e T₁(e)²` is almost surely finite and
`O_s(C' r^{-d})`. With Lemma 3.5 the change of partition of each bond is supported in a box, so
the heat series of `T₁(e)` converges (`flipTermOneSummable_of_resample`), and
`darioStepOneSumBoundThree_of_resample` gives the bound of the Step 1 sum
`DarioStepOneSumBoundThree` from Lemma 3.5 in dimension `d ≥ 3` (`DarioResamplePartitionThree`).
Consequently Lemma 3.3 in dimension `d ≥ 3` follows from Lemma 3.5 and the bound of the Step 2 sum
(`darioVarianceBoundThree_of_resample`). This is the planar argument of `DarioStepOneHolds` on `ℤᵈ`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ} [NeZero d]

/-- The arithmetic of the sixfold moments of the ball sums. -/
theorem sixfold_moment_eq_const {K A m q : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hq : 0 < q) :
    K ^ (2 * q) * (A * (6 * q) ^ m) ^ (6 * q) =
      ((K * (A * 6 ^ m) ^ 3 * q ^ (3 * m)) ^ q) ^ 2 := by
  have h6 : (6 * q) ^ m = 6 ^ m * q ^ m := Real.mul_rpow (by norm_num) hq.le
  have h3 : q ^ (3 * m) = (q ^ m) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hq.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e1 : A * (6 ^ m * q ^ m) = A * 6 ^ m * q ^ m := by ring
  have e2 : K * (A * 6 ^ m) ^ 3 * (q ^ m) ^ 3 = K * (A * 6 ^ m * q ^ m) ^ 3 := by ring
  rw [h6, h3, e1, e2]
  obtain ⟨w, hw0, hw⟩ : ∃ w, 0 ≤ w ∧ A * 6 ^ m * q ^ m = w := ⟨_, by positivity, rfl⟩
  rw [hw, ← Real.rpow_natCast ((K * w ^ 3) ^ q) 2, ← Real.rpow_mul (by positivity),
    Real.mul_rpow hK (by positivity), ← Rigidity.Corrector.rpow_natCast_mul_eq hw0 3]
  congr 2
  all_goals (push_cast; ring)

section Holds

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

omit [NeZero d] in
/-- **Forcing one bond** changes the law by a density at most `min(p, 1 - p)⁻¹`:
`E[f(ω^{e,b})] ≤ min(p, 1 - p)⁻¹ E[f]`. -/
theorem lintegral_comp_setBond_le {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f : Configuration d → ℝ≥0∞} (hf : Measurable f) (e : Bond d) (b : Bool) :
    ∫⁻ ω, f (setBond e b ω) ∂latticeBondLaw d p ≤
      ENNReal.ofReal (min (p : ℝ) (1 - p))⁻¹ * ∫⁻ ω, f ω ∂latticeBondLaw d p := by
  have hw0 : 0 < min (p : ℝ) (1 - p) := lt_min hp0 (by linarith)
  have hwb : min (p : ℝ) (1 - p) ≤ Rigidity.Corrector.bondWeight p b := by
    unfold Rigidity.Corrector.bondWeight
    split_ifs <;> simp
  have hb0 : 0 < Rigidity.Corrector.bondWeight p b := lt_of_lt_of_le hw0 hwb
  have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p hf e b
  have hne : ENNReal.ofReal (Rigidity.Corrector.bondWeight p b) ≠ 0 := by simp [hb0]
  calc ∫⁻ ω, f (setBond e b ω) ∂latticeBondLaw d p
      = (ENNReal.ofReal (Rigidity.Corrector.bondWeight p b))⁻¹ *
          (ENNReal.ofReal (Rigidity.Corrector.bondWeight p b) *
            ∫⁻ ω, f (setBond e b ω) ∂latticeBondLaw d p) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal (Rigidity.Corrector.bondWeight p b))⁻¹ *
          ∫⁻ ω, f ω ∂latticeBondLaw d p := mul_le_mul' le_rfl hflip
    _ ≤ _ := by
        refine mul_le_mul' ?_ le_rfl
        rw [ENNReal.ofReal_inv_of_pos hw0]
        exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal hwb)

theorem sqrt_mul_exp_neg {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    Real.sqrt (a * Real.exp (-x)) = Real.sqrt a * Real.exp (-(x / 2)) := by
  rw [Real.sqrt_mul ha]
  congr 1
  have : Real.exp (-x) = Real.exp (-(x / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [this, Real.sqrt_sq (Real.exp_pos _).le]

/-- **The moments of the factor of one bond of Dario's sums (3.18) on `ℤᵈ`**, with the scale `S` of
the corrected Lemma 3.5: they decay exponentially in the distance from `y` to the base of the bond,
`E[F_e(y)^q] ≤ 4 min(p, 1 - p)⁻¹ Y₀^q e^{-|a_e - y|/(2 κ₁ θ)}`. -/
theorem lintegral_stepOneFactor_rpow_le (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {Λ : Vertex d → Configuration d → ℝ} (hΛm : ∀ z, Measurable (Λ z)) (hΛ0 : ∀ z ω, 0 ≤ Λ z ω)
    {B κ : ℝ} (hB : 0 < B)
    (hmom : ∀ x (q : ℝ), 1 ≤ q → ∫⁻ ω, ENNReal.ofReal (1 + Λ x ω) ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((B * q ^ κ) ^ q))
    {θ' : ℝ} (hθ' : 0 < θ')
    (hexp : ∀ x : Vertex d, Integrable (fun ω =>
        Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ')) (latticeBondLaw d p) ∧
      ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ')
        ∂latticeBondLaw d p ≤ 2)
    (C₀ C : ℕ) (e : Bond d) (y : Vertex d) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ ω, stepOneFactor Λ C₀ C e y ω ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal (4 * (min (p : ℝ) (1 - p))⁻¹ *
        (128 * (d : ℝ) ^ 2 * ((2 * (1 + 8 * d * (d * ((C₀ : ℝ) + 1 + 3 * C) * θ'))) ^ d *
          Real.sqrt 2 * ((min (p : ℝ) (1 - p))⁻¹ * B * 2 ^ κ) * 6 ^ (κ + d)) ^ 3 *
          q ^ (3 * (κ + d))) ^ q *
        Real.exp (-(‖latticeEuclideanEmbedding (bondBase e - y)‖ /
          (2 * (d * ((C₀ : ℝ) + 1) * θ'))))) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have hd0 : 0 < d := by omega
  set w : ℝ := min (p : ℝ) (1 - p) with hw
  have hw0 : 0 < w := lt_min hp0 (by linarith)
  have hw1 : w ≤ 1 := (min_le_left _ _).trans (by have := p.2.2; exact_mod_cast this)
  have hwi : 1 ≤ w⁻¹ := one_le_inv₀ hw0 |>.2 hw1
  set κ₁ : ℝ := d * ((C₀ : ℝ) + 1) with hκ₁
  set κ₃ : ℝ := d * ((C₀ : ℝ) + 1 + 3 * C) with hκ₃
  have hκ₁0 : 0 < κ₁ := by positivity
  have hκ₃0 : 0 < κ₃ := by positivity
  set A₁ : ℝ := (2 * (1 + 8 * d * (κ₃ * θ'))) ^ d * Real.sqrt 2 * (w⁻¹ * B * 2 ^ κ) with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  set c : ℝ := 4 * w⁻¹ with hc
  set K₀ : ℝ := 128 * (d : ℝ) ^ 2 with hK₀
  have hq0 : 0 < q := by linarith
  set Y₀ : ℝ := K₀ * (A₁ * 6 ^ (κ + d)) ^ 3 * q ^ (3 * (κ + d)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  -- the summands `1 + Λ(·, ζ^{e,1})` of the ball sums
  have hYm : ∀ (e : Bond d) x (q' : ℝ), 1 ≤ q' →
      ∫⁻ ζ, ENNReal.ofReal (1 + Λ x (setBond e true ζ)) ^ q' ∂latticeBondLaw d p ≤
        ENNReal.ofReal ((w⁻¹ * B * q' ^ κ) ^ q') := by
    intro e x q' hq'
    have hq'0 : 0 ≤ q' := by linarith
    have hfm : Measurable fun ζ : Configuration d => ENNReal.ofReal (1 + Λ x ζ) ^ q' :=
      ((measurable_const.add (hΛm x)).ennreal_ofReal).pow_const q'
    refine (lintegral_comp_setBond_le hp0 hp1 hfm e true).trans ?_
    calc ENNReal.ofReal w⁻¹ * ∫⁻ ζ, ENNReal.ofReal (1 + Λ x ζ) ^ q' ∂latticeBondLaw d p
        ≤ ENNReal.ofReal w⁻¹ * ENNReal.ofReal ((B * q' ^ κ) ^ q') :=
          mul_le_mul' le_rfl (hmom x q' hq')
      _ ≤ ENNReal.ofReal ((w⁻¹) ^ q') * ENNReal.ofReal ((B * q' ^ κ) ^ q') := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          simpa using Real.rpow_le_rpow_of_exponent_le hwi hq'
      _ = ENNReal.ofReal ((w⁻¹ * B * q' ^ κ) ^ q') := by
          rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity)
            (by positivity), mul_assoc]
  -- the moments of the ball sums
  have hball : ∀ e : Bond d, ∫⁻ ζ, stepOneBallSum Λ κ₃ e ζ ^ (6 * q) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((A₁ * (6 * q) ^ (κ + d)) ^ (6 * q)) := by
    intro e
    unfold stepOneBallSum
    exact lintegral_randomBallSum_rpow_le_of_growth (bondBase e) (θ := κ₃ * θ') (by positivity)
      (fun t _ => measure_le_mul_stoppingSize_le hθ' hκ₃0 _ (hexp _).1 (hexp _).2 t)
      ((measurable_stoppingSize_goodCubes _).const_mul κ₃)
      (fun x => (measurable_const.add ((hΛm x).comp (measurable_setBond e true))).ennreal_ofReal)
      (by positivity) (hYm e) (by linarith)
  -- the arithmetic of the sixfold moments
  have hsix : K₀ ^ (2 * q) * (A₁ * (6 * q) ^ (κ + d)) ^ (6 * q) = (Y₀ ^ q) ^ 2 := by
    rw [hY₀]
    exact sixfold_moment_eq_const (by positivity) hA₁0.le hq0
  -- the moments of the factor of each bond
  have hedge : ∀ e : Bond d,
      ∫⁻ ω, stepOneFactor Λ C₀ C e y ω ^ q ∂latticeBondLaw d p ≤
        ENNReal.ofReal (c * Y₀ ^ q * Real.exp
          (-(‖latticeEuclideanEmbedding (bondBase e - y)‖ / (2 * (κ₁ * θ'))))) := by
    intro e
    set t := ‖latticeEuclideanEmbedding (bondBase e - y)‖ with ht
    set U : Configuration d → ℝ≥0∞ := stepOneBallSum Λ κ₃ e with hU
    have hUm : Measurable U := measurable_stepOneBallSum (hΛm) κ₃ e
    set Z : Configuration d → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal (16 * d ^ 2) * (U (setBond e false ω) + U (setBond e true ω)) ^ 3 with hZ
    have hZm : Measurable Z := measurable_const.mul
      (((hUm.comp (measurable_setBond e false)).add (hUm.comp (measurable_setBond e true))).pow_const
        3)
    set Aev := {ω' : Configuration d | t ≤ κ₁ * flipSideReal e ω'} with hAev
    have hAm : MeasurableSet Aev :=
      measurableSet_le measurable_const ((measurable_flipSideReal e).const_mul κ₁)
    -- the factor is dominated on the partition events of the flips
    have h2 : ∫⁻ ω, stepOneFactor Λ C₀ C e y ω ^ q ∂latticeBondLaw d p ≤
        ∫⁻ ω, Aev.indicator Z ω ^ q ∂latticeBondLaw d p := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_setBond hp0 hp1 (ae_partitionEvent hd hpc)] with ω hP
      exact ENNReal.rpow_le_rpow (stepOneFactor_le (hΛ0) C₀ C e y (hP e false) (hP e true))
        hq0.le
    -- the probability of the event
    set Ab : Set (Configuration d) := {η | t ≤ κ₁ *
      TriadicCube.stoppingSize (TriadicCube.goodCubes η) (bondBase e)} with hAb
    have hAbm : MeasurableSet Ab :=
      measurableSet_le measurable_const ((measurable_stoppingSize_goodCubes _).const_mul κ₁)
    have hAb : latticeBondLaw d p Ab ≤ ENNReal.ofReal (2 * Real.exp (-(t / (κ₁ * θ')))) :=
      measure_le_mul_stoppingSize_le hθ' hκ₁0 _ (hexp _).1 (hexp _).2 t
    have hpre : ∀ b : Bool, latticeBondLaw d p (setBond e b ⁻¹' Ab) ≤
        ENNReal.ofReal w⁻¹ * ENNReal.ofReal (2 * Real.exp (-(t / (κ₁ * θ')))) := by
      intro b
      have h := lintegral_comp_setBond_le hp0 hp1 (f := Ab.indicator 1)
        (measurable_one.indicator hAbm) e b
      rw [lintegral_indicator_one hAbm] at h
      have e1 : (fun ω => Ab.indicator (1 : Configuration d → ℝ≥0∞) (setBond e b ω)) =
          (setBond e b ⁻¹' Ab).indicator 1 := by
        funext ω
        simp [Set.indicator_apply]
      rw [e1, lintegral_indicator_one (hAbm.preimage (measurable_setBond e b))] at h
      exact h.trans (mul_le_mul' le_rfl hAb)
    have hsub : Aev ⊆ setBond e false ⁻¹' Ab ∪ setBond e true ⁻¹' Ab := by
      intro ω hω
      simp only [hAev, Set.mem_setOf_eq, flipSideReal] at hω
      rw [mul_max_of_nonneg _ _ hκ₁0.le, le_max_iff] at hω
      rcases hω with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hPA : latticeBondLaw d p Aev ≤
        ENNReal.ofReal (4 * w⁻¹ * Real.exp (-(t / (κ₁ * θ')))) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      refine (add_le_add (hpre false) (hpre true)).trans (le_of_eq ?_)
      rw [← two_mul, ← ENNReal.ofReal_mul (by positivity)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    -- the moments of `Z`
    set Mb : ℝ := (A₁ * (6 * q) ^ (κ + d)) ^ (6 * q) with hMb
    have hZ2 : ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p ≤
        ENNReal.ofReal ((Real.sqrt (2 * w⁻¹) * Y₀ ^ q) ^ 2) := by
      have h6 : (1 : ℝ) ≤ 6 * q := by linarith
      have hU0 : Measurable fun ω => U (setBond e false ω) ^ (6 * q) :=
        (hUm.comp (measurable_setBond e false)).pow_const _
      have hU1 : Measurable fun ω => U (setBond e true ω) ^ (6 * q) :=
        (hUm.comp (measurable_setBond e true)).pow_const _
      have hpt : ∀ ω, Z ω ^ (2 * q) ≤ ENNReal.ofReal ((16 * d ^ 2) ^ (2 * q)) *
          (2 ^ (6 * q) * (U (setBond e false ω) ^ (6 * q) + U (setBond e true ω) ^ (6 * q))) := by
        intro ω
        simp only [hZ]
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        refine mul_le_mul' le_rfl ?_
        rw [show ((3 : ℕ) : ℝ) * (2 * q) = 6 * q by push_cast; ring]
        exact (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ h6).trans
          (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) le_rfl)
      have hb : ∀ b : Bool, ∫⁻ ω, U (setBond e b ω) ^ (6 * q) ∂latticeBondLaw d p ≤
          ENNReal.ofReal w⁻¹ * ENNReal.ofReal Mb := fun b =>
        (lintegral_comp_setBond_le hp0 hp1 (hUm.pow_const _) e b).trans
          (mul_le_mul' le_rfl (hball e))
      have h2top : (2 : ℝ≥0∞) ^ (6 * q) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofNat_ne_top
      have h2e : (2 : ℝ≥0∞) ^ (6 * q) = ENNReal.ofReal (2 ^ (6 * q)) := by
        rw [← ENNReal.ofReal_rpow_of_pos (by norm_num), ENNReal.ofReal_ofNat]
      have h8 : (8 : ℝ) ^ (2 * q) = 2 ^ (6 * q) := by
        rw [show (8 : ℝ) = 2 ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
          ← Real.rpow_mul (by norm_num)]
        congr 1
        push_cast
        ring
      calc ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p
          ≤ ∫⁻ ω, ENNReal.ofReal ((16 * d ^ 2) ^ (2 * q)) *
              (2 ^ (6 * q) * (U (setBond e false ω) ^ (6 * q) +
                U (setBond e true ω) ^ (6 * q))) ∂latticeBondLaw d p := lintegral_mono hpt
        _ = ENNReal.ofReal ((16 * d ^ 2) ^ (2 * q)) * (2 ^ (6 * q) *
              (∫⁻ ω, U (setBond e false ω) ^ (6 * q) ∂latticeBondLaw d p +
                ∫⁻ ω, U (setBond e true ω) ^ (6 * q) ∂latticeBondLaw d p)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ h2top,
              lintegral_add_left hU0]
        _ ≤ ENNReal.ofReal ((16 * d ^ 2) ^ (2 * q)) * (2 ^ (6 * q) *
              (ENNReal.ofReal w⁻¹ * ENNReal.ofReal Mb + ENNReal.ofReal w⁻¹ * ENNReal.ofReal Mb)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add (hb false) (hb true)))
        _ = ENNReal.ofReal ((16 * d ^ 2) ^ (2 * q) * (2 ^ (6 * q) * (2 * (w⁻¹ * Mb)))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← two_mul, h2e,
              show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal ((Real.sqrt (2 * w⁻¹) * Y₀ ^ q) ^ 2) := by
            congr 1
            have hK : K₀ ^ (2 * q) = (16 * (d : ℝ) ^ 2) ^ (2 * q) * 2 ^ (6 * q) := by
              rw [hK₀, show (128 : ℝ) * d ^ 2 = 16 * d ^ 2 * 8 by ring,
                Real.mul_rpow (by positivity) (by norm_num), h8]
            rw [mul_pow, Real.sq_sqrt (by positivity), ← hsix, hK, hMb]
            ring
    have hPA' : latticeBondLaw d p Aev ≤
        ENNReal.ofReal (8 * w⁻¹ * Real.exp (-(t / (κ₁ * θ')))) :=
      hPA.trans (ENNReal.ofReal_le_ofReal (by
        have : 0 ≤ w⁻¹ * Real.exp (-(t / (κ₁ * θ'))) := by positivity
        nlinarith))
    have h3 := lintegral_indicator_rpow_le (p := p) hAm hZm hq0
      (c := 8 * w⁻¹ * Real.exp (-(t / (κ₁ * θ')))) (m := Real.sqrt (2 * w⁻¹) * Y₀ ^ q)
      (by positivity) (by positivity) hPA' hZ2
    refine h2.trans (h3.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
    have hs : Real.sqrt (8 * w⁻¹) * Real.sqrt (2 * w⁻¹) = 4 * w⁻¹ := by
      rw [← Real.sqrt_mul (by positivity), show 8 * w⁻¹ * (2 * w⁻¹) = (4 * w⁻¹) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [sqrt_mul_exp_neg (by positivity), hc,
      show t / (κ₁ * θ') / 2 = t / (2 * (κ₁ * θ')) by rw [div_div, mul_comm 2]]
    linear_combination (Y₀ ^ q * Real.exp (-(t / (2 * (κ₁ * θ'))))) * hs
  exact hedge e

/-- **The moments of Dario's sums (3.18) on `ℤᵈ`**: for the Lipschitz bounds `Λ` of the
corrector, the sums `W(y) = stepOneW (Λ i) C₀ C y` satisfy `E[W(y)^q] ≤ (A q^k)^q` uniformly
in `y`. -/
theorem stepOneW_moments (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (C₀ C : ℕ) :
    ∃ (Λ : Fin d → Vertex d → Configuration d → ℝ) (A k : ℝ), 0 < A ∧ 0 < k ∧
      (∀ i x, Measurable (Λ i x)) ∧ (∀ i x ω, 0 ≤ Λ i x ω) ∧
      (∀ i, ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
        (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω) ∧
      (∀ i y (q : ℝ), 1 ≤ q →
        ∫⁻ ω, stepOneW (Λ i) C₀ C y ω ^ q ∂latticeBondLaw d p ≤
          ENNReal.ofReal ((A * q ^ k) ^ q)) := by
  obtain ⟨Λ, B, κ, hB, hκ, hΛm, hΛ0, hlip, hmom⟩ :=
    stepOne_lipschitz_data hG hGv hd hpc hp1 hGae
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  set w : ℝ := min (p : ℝ) (1 - p) with hw
  have hw0 : 0 < w := lt_min hp0 (by linarith)
  have hw1 : w ≤ 1 := (min_le_left _ _).trans (by have := p.2.2; exact_mod_cast this)
  have hwi : 1 ≤ w⁻¹ := one_le_inv₀ hw0 |>.2 hw1
  set κ₁ : ℝ := d * ((C₀ : ℝ) + 1) with hκ₁
  set κ₃ : ℝ := d * ((C₀ : ℝ) + 1 + 3 * C) with hκ₃
  have hκ₁0 : 0 < κ₁ := by positivity
  have hκ₃0 : 0 < κ₃ := by positivity
  set A₁ : ℝ := (2 * (1 + 8 * d * (κ₃ * θ'))) ^ d * Real.sqrt 2 * (w⁻¹ * B * 2 ^ κ) with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  set N : ℝ := 2 * d * (2 * d) ^ d with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    have h1 : (1 : ℝ) ≤ 2 * d := by linarith
    have h2 : (1 : ℝ) ≤ (2 * d) ^ d := one_le_pow₀ h1
    nlinarith
  set X : ℝ := N * (1 + 4 * (κ₁ * θ')) ^ d with hX
  set c : ℝ := 4 * w⁻¹ with hc
  set K₀ : ℝ := 128 * (d : ℝ) ^ 2 with hK₀
  have hX1 : 1 ≤ X := by
    have h0 : 0 ≤ κ₁ * θ' := by positivity
    have : 1 ≤ (1 + 4 * (κ₁ * θ')) ^ d := one_le_pow₀ (by linarith)
    nlinarith
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := by linarith
  refine ⟨Λ, X * c * (K₀ * (A₁ * 6 ^ (κ + d)) ^ 3), 3 * (κ + d) + d, by positivity,
    by positivity, hΛm, hΛ0, hlip, fun i y q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  set Y₀ : ℝ := K₀ * (A₁ * 6 ^ (κ + d)) ^ 3 * q ^ (3 * (κ + d)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  have hedge : ∀ e : Bond d,
      ∫⁻ ω, stepOneFactor (Λ i) C₀ C e y ω ^ q ∂latticeBondLaw d p ≤
        ENNReal.ofReal (c * Y₀ ^ q * Real.exp
          (-(‖latticeEuclideanEmbedding (bondBase e - y)‖ / (2 * (κ₁ * θ'))))) := fun e => by
    have h := lintegral_stepOneFactor_rpow_le hd hpc hp1 (hΛm i) (hΛ0 i) hB (hmom i) hθ' hexp
      C₀ C e y hq
    rw [hc, hY₀, hK₀, hA₁, hκ₁, hκ₃, hw]
    exact h
  clear_value c X N
  -- Jensen's inequality over the bonds
  letI : MeasurableSpace (Bond d) := ⊤
  haveI : MeasurableSingletonClass (Bond d) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hJ := lintegral_tsum_rpow_le_of_decay (ι := Bond d) (p := p)
    (I := fun e => stepOneFactor (Λ i) C₀ C e y)
    (fun e => measurable_stepOneFactor (hΛm i) C₀ C _ y)
    (a := fun e => ‖latticeEuclideanEmbedding (bondBase e - y)‖)
    (fun e => norm_nonneg _) hq (θ := κ₁ * θ') (by positivity) (M := c * Y₀ ^ q) (N := N)
    (m := d) (by positivity) (by positivity)
    (fun κ' hκ' => by rw [hN]; exact tsum_exp_neg_norm_bondBase_le hd0 y hκ') hedge
  have hbase : N * (1 + 4 * q * (κ₁ * θ')) ^ d ≤ X * q ^ d := by
    have h1 : 1 + 4 * q * (κ₁ * θ') ≤ q * (1 + 4 * (κ₁ * θ')) := by
      have h0 : 0 ≤ κ₁ * θ' := by positivity
      nlinarith
    have h0 : 0 ≤ 1 + 4 * q * (κ₁ * θ') := by positivity
    have := pow_le_pow_left₀ h0 h1 d
    rw [mul_pow] at this
    rw [hX]
    calc N * (1 + 4 * q * (κ₁ * θ')) ^ d ≤ N * (q ^ d * (1 + 4 * (κ₁ * θ')) ^ d) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = N * (1 + 4 * (κ₁ * θ')) ^ d * q ^ d := by ring
  have hXq1 : (X * q ^ d) ^ (q - 1) * X ≤ (X * q ^ d) ^ q := by
    have hXq : 0 < X * q ^ d := by positivity
    rw [Real.rpow_sub hXq, Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hXq]
    have : 0 ≤ (X * q ^ d) ^ q := by positivity
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ hq)) this
  have hcq : c ≤ c ^ q := by
    have h := Real.rpow_le_rpow_of_exponent_le hc1 hq
    rwa [Real.rpow_one] at h
  calc ∫⁻ ω, stepOneW (Λ i) C₀ C y ω ^ q ∂latticeBondLaw d p
      = ∫⁻ ω, (∑' e, stepOneFactor (Λ i) C₀ C e y ω) ^ q ∂latticeBondLaw d p := rfl
    _ ≤ _ := hJ
    _ ≤ ENNReal.ofReal ((X * c * (K₀ * (A₁ * 6 ^ (κ + d)) ^ 3) * q ^ (3 * (κ + d) + d)) ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (N * (1 + 4 * q * (κ₁ * θ')) ^ d) ^ (q - 1) *
              (c * Y₀ ^ q * (N * (1 + 4 * (κ₁ * θ')) ^ d))
            ≤ (X * q ^ d) ^ (q - 1) * (X * (c * Y₀ ^ q)) := by
              rw [show c * Y₀ ^ q * (N * (1 + 4 * (κ₁ * θ')) ^ d) = X * (c * Y₀ ^ q) by
                rw [hX]; ring]
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow (by positivity) hbase (by linarith)) (by positivity)
          _ = ((X * q ^ d) ^ (q - 1) * X) * (c * Y₀ ^ q) := by ring
          _ ≤ (X * q ^ d) ^ q * (c ^ q * Y₀ ^ q) :=
              mul_le_mul hXq1 (mul_le_mul_of_nonneg_right hcq (by positivity)) (by positivity)
                (by positivity)
          _ = (X * c * (K₀ * (A₁ * 6 ^ (κ + d)) ^ 3) * q ^ (3 * (κ + d) + d)) ^ q := by
              rw [← Real.mul_rpow (by positivity) hY₀0,
                ← Real.mul_rpow (by positivity) (by positivity), hY₀,
                Real.rpow_add hq0, Real.rpow_natCast]
              congr 1
              ring

/-- **Step 1 of Lemma 3.3 of Dario on `ℤᵈ`, given Lemma 3.5**: the sum over the bonds of the
squares of the change-of-partition terms is almost surely finite and `O_s(C' r^{-d})`. -/
theorem flipSumOne_isOsBond_of_resample (hd : 2 ≤ d) {C₀ C : ℕ}
    (hres : ResamplePartitionBound (d := d) C₀ C) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ s C' : ℝ, 0 < s ∧ 0 < C' ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
      (∀ᵐ ω ∂latticeBondLaw d p, flipSumOne hG hGv i j r x ω < ∞) ∧
      IsOsBond d p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C' / r ^ (d : ℝ)) := by
  obtain ⟨Λ, A, k, hA, hk, hΛm, hΛ0, hlip, hmom⟩ :=
    stepOneW_moments hG hGv hd hpc hp1 hGae C₀ C
  obtain ⟨s, C', hs, hC', h⟩ := isOsBond_heatSqSum_of_moments (d := d) (p := p) hA hk
  refine ⟨s, C', hs, hC', fun i j r hr x => ?_⟩
  have hle := ae_flipSumOne_le hG hGv hd hpc hp1 hGae hres (Λ := Λ i)
    (fun z ω => hΛ0 i z ω) (hlip i)
  refine h r hr x (stepOneW (Λ i) C₀ C) (fun y => measurable_stepOneW (hΛm i) C₀ C y) (hmom i) _
    (measurable_flipSumOne hG hGv i j r x) ?_
  filter_upwards [hle] with ω hω
  exact hω j r x

/-- **The heat series of the change of partition converges**: with Lemma 3.5 the change of
partition of each bond is supported in a box (`partitionChange_eq_zero`), so the series of
`T₁(e)` is a finite sum. -/
theorem flipTermOneSummable_of_resample (hd : 2 ≤ d) {C₀ C : ℕ}
    (hres : ResamplePartitionBound (d := d) C₀ C) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (i j : Fin d) (r : ℝ)
    (x : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ e, FlipTermOneSummable hG hGv i j r x e ω := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 (ae_partitionEvent hd hpc)] with ω hP' e
  have hloc := resampleLocal_of_bound hres (setBond_agree_off e false true ω) (hP' e false)
    (hP' e true) (bondBase_mem e)
  set ρ := C₀ * resampleScale (setBond e false ω) (setBond e true ω) (bondBase e)
  set B : Finset (Vertex d) := supBox (bondBase e) ρ
  refine summable_of_ne_finset_zero (s := B) fun y hy => ?_
  have h0 : partitionChange (setBond e false ω) (setBond e true ω)
      (flipCorrector hG hGv i true e ω) j y = 0 := by
    refine partitionChange_eq_zero hloc _ j (fun hb => hy ?_) (fun hb => hy ?_)
    · rw [mem_supBox]
      exact fun i => (hb i).le
    · rw [mem_supBox]
      intro i
      have t := abs_sub_le (y i) ((y + LatticeProb.unit j) i) (bondBase e i)
      have h1 := (abs_sub_add_unit_le y j i).1
      have h2 := Int.add_one_le_iff.mpr (hb i)
      linarith
  show zdHeat d (r ^ 2) x y * partitionChange (setBond e false ω) (setBond e true ω)
    (flipCorrector hG hGv i true e ω) j y = 0
  rw [h0, mul_zero]

end Holds

/-- **The bound of the Step 1 sum of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`, from
Lemma 3.5 for the partition into good cubes of `ℤᵈ`.** -/
theorem darioStepOneSumBoundThree_of_resample (h35 : DarioResamplePartitionThree) :
    DarioStepOneSumBoundThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  have hd : 2 ≤ d := by omega
  obtain ⟨C₀, C, -, hres⟩ := h35 d hd3
  obtain ⟨s, C', hs, hC', h⟩ := flipSumOne_isOsBond_of_resample hG hGv hd hres hpc hp1 hGae
  refine ⟨s, C', hs, hC', fun i j r hr x => ?_⟩
  obtain ⟨hf, hO⟩ := h i j r hr x
  exact ⟨flipTermOneSummable_of_resample hG hGv hd hres hpc hp1 i j r x, hf, hO⟩

/-- **Dario, Lemma 3.3 in dimension `d ≥ 3`, from Lemma 3.5 and the bound of the Step 2 sum.** -/
theorem darioVarianceBoundThree_of_resample (h35 : DarioResamplePartitionThree)
    (h2 : DarioStepTwoSumBoundThree) : DarioVarianceBoundThree :=
  darioVarianceBoundThree_of_sums (darioStepOneSumBoundThree_of_resample h35) h2

end Rigidity.Corrector.GeneralDim

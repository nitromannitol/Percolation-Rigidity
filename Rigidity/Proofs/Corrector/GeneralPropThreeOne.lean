import Rigidity.Proofs.Corrector.GeneralHeatSmoothing
import Rigidity.Proofs.Corrector.Concentration

/-!
# Dario's Proposition 3.1 in dimension `d ≥ 3`

Dario proves Proposition 3.1, `|Φ_{r²} * ∇[χ_p]_𝒫(x)| ≤ O_s(C |p| r^{-d/2})`, by applying the
concentration inequality of Proposition 2.17 (Armstrong and Lin, ARMA 225, 2017, Proposition 2.2) to
`X = Φ_{r²} * ∇[χ_p]_𝒫(x)`, with the bound `|E[X]| ≤ C r^{-d/2}` of Lemma 3.2 and the bound
`𝕍[X] ≤ O_s(C r^{-d})` of Lemma 3.3. Here, for the coarsened correctors `coarseField` of the
partition into good cubes of `ℤᵈ` and the components
`heatComp u r x j = Σ_y Φ(r², x, y) (u(y + e_j) - u(y))`:

* `lintegral_abs_sub_integral_rpow_le`: the concentration inequality in dimension `d`
  (`concentration_holds`) and `𝕍[X] ≤ O_s(θ)` bound the moments of `|X - E[X]|` by
  `(A √θ q^{(1+s)/(2s)})^q`;
* `DarioMeanBoundThree`, `DarioVarianceBoundThree`: Lemmas 3.2 and 3.3 in dimension `d ≥ 3`
  at every point `x`, both proved (`darioMeanBoundThree_holds`,
  `darioVarianceBoundThree_holds`);
* `darioPropThreeOneThree_of_lemmas`: Proposition 3.1 (`DarioPropThreeOneThree`) from these,
  as in the source: `|X| ≤ |E[X]| + |X - E[X]|` componentwise;
* `darioOptimalCorrectorThree_of_lemmas`: Dario's Theorem 1 in dimension `d ≥ 3` from Lemmas 3.2
  and 3.3.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.S2
open scoped Classical ENNReal

variable {d : ℕ}

/-- The `j`-th component `Σ_y Φ(r², x, y) (u(y + e_j) - u(y))` of `Φ_{r²} * ∇u(x)` on `ℤᵈ`. -/
noncomputable def heatComp (u : Vertex d → ℝ) (r : ℝ) (x : Vertex d) (j : Fin d) : ℝ :=
  ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * (u (y + LatticeProb.unit j) - u y)

theorem heatGradient_eq_sum_abs_heatComp (u : Vertex d → ℝ) (r : ℝ) (x : Vertex d) :
    Rigidity.Poincare.GeneralDim.heatGradient u r x = ∑ j : Fin d, |heatComp u r x j| := rfl

theorem abs_heatComp_le_heatGradient (u : Vertex d → ℝ) (r : ℝ) (x : Vertex d) (j : Fin d) :
    |heatComp u r x j| ≤ Rigidity.Poincare.GeneralDim.heatGradient u r x := by
  rw [heatGradient_eq_sum_abs_heatComp]
  exact Finset.single_le_sum (f := fun j => |heatComp u r x j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ j)

theorem measurable_heatComp {F : Vertex d → Configuration d → ℝ} (hF : ∀ z, Measurable (F z))
    (r : ℝ) (x : Vertex d) (j : Fin d) :
    Measurable fun ω => heatComp (fun z => F z ω) r x j := by
  unfold heatComp
  exact Measurable.tsum fun y => ((hF _).sub (hF y)).const_mul _

section Concentration

variable (p : unitInterval)

/-- `𝕍[c X] = c² 𝕍[X]` almost surely, by the linearity of the conditional expectations. -/
theorem ae_resampleVar_const_mul (X : Configuration d → ℝ) (c : ℝ) :
    ∀ᵐ ω ∂latticeBondLaw d p, resampleVar p (fun ω => c * X ω) ω =
      ENNReal.ofReal (c ^ 2) * resampleVar p X ω := by
  have h : ∀ e : Bond d, condExp (bondsExcept e) (latticeBondLaw d p) (fun ω => c * X ω)
      =ᵐ[latticeBondLaw d p] fun ω => c * condExp (bondsExcept e) (latticeBondLaw d p) X ω := by
    intro e
    have hcX : (fun ω => c * X ω) = c • X := by
      funext ω
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hcX]
    filter_upwards [condExp_smul (μ := latticeBondLaw d p) c X (bondsExcept e)] with ω hω
    rw [hω, Pi.smul_apply, smul_eq_mul]
  filter_upwards [ae_all_iff.2 h] with ω hω
  dsimp only [resampleVar]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun e => ?_
  rw [hω e, ← mul_sub, mul_pow, ENNReal.ofReal_mul (sq_nonneg c)]

/-- **The moments of `X - E[X]` from the concentration inequality**: if `𝕍[X] ≤ O_s(θ)`, then
`E[|X - E[X]|^q] ≤ (A √θ q^{(1+s)/(2s)})^q` for `q ≥ 1`, with `A` depending on `s` only. -/
theorem lintegral_abs_sub_integral_rpow_le (hconc : Concentration d) {s : ℝ} (hs : 0 < s) :
    ∃ A : ℝ, 0 < A ∧ ∀ (X : Configuration d → ℝ) (θ : ℝ), 0 < θ →
      Integrable X (latticeBondLaw d p) →
      (∀ᵐ ω ∂latticeBondLaw d p, resampleVar p X ω < ∞) →
      IsOsBond d p (fun ω => (resampleVar p X ω).toReal) s θ →
      ∀ q : ℝ, 1 ≤ q → ∫⁻ ω, ENNReal.ofReal (|X ω - ∫ ω', X ω' ∂latticeBondLaw d p| ^ q)
          ∂latticeBondLaw d p ≤
        ENNReal.ofReal ((A * Real.sqrt θ * q ^ ((1 + s) / (2 * s))) ^ q) := by
  set β : ℝ := 2 * s / (1 + s) with hβ
  have hβ0 : 0 < β := by positivity
  have hβ' : β * (1 + s) = 2 * s := by rw [hβ]; exact div_mul_cancel₀ _ (by positivity)
  have hβ2 : β < 2 := by nlinarith
  have hβs : β / (2 - β) = s := by
    rw [div_eq_iff (sub_pos.2 hβ2).ne']
    linear_combination hβ'
  have hβi : (2 - β) / β = 1 / s := by
    rw [div_eq_div_iff hβ0.ne' hs.ne']
    linear_combination -hβ'
  have hβk : (1 + s) / (2 * s) = 1 / β := by
    rw [div_eq_div_iff (by positivity) hβ0.ne']
    linear_combination hβ'
  obtain ⟨Cc, hCc, hc⟩ := hconc p β hβ0 hβ2
  refine ⟨Real.sqrt Cc / β ^ (1 / β) * max 1 (Cc * 2 ^ (1 / s)), by positivity,
    fun X θ hθ hXi hXV hXO q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  set L : ℝ := Real.sqrt (Cc * θ) with hL
  have hL0 : 0 < L := Real.sqrt_pos.2 (by positivity)
  have hLsq : L⁻¹ ^ 2 = (Cc * θ)⁻¹ := by
    rw [inv_pow, hL, Real.sq_sqrt (by positivity)]
  -- the rescaled variable `Y = X / L`
  have hYi : Integrable (fun ω => L⁻¹ * X ω) (latticeBondLaw d p) := hXi.const_mul L⁻¹
  have hV := ae_resampleVar_const_mul p X L⁻¹
  have hYV : ∀ᵐ ω ∂latticeBondLaw d p, resampleVar p (fun ω => L⁻¹ * X ω) ω < ∞ := by
    filter_upwards [hV, hXV] with ω hω h'
    rw [hω]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h'
  have h := hc (fun ω => L⁻¹ * X ω) hYi hYV
  -- the right-hand side
  have hrhs : ∫⁻ ω, ENNReal.ofReal (Real.exp ((Cc * (resampleVar p
      (fun ω => L⁻¹ * X ω) ω).toReal) ^ (β / (2 - β)))) ∂latticeBondLaw d p ≤ ENNReal.ofReal 2 := by
    have hcongr : ∀ᵐ ω ∂latticeBondLaw d p, ENNReal.ofReal (Real.exp ((Cc * (resampleVar p
        (fun ω => L⁻¹ * X ω) ω).toReal) ^ (β / (2 - β)))) =
        ENNReal.ofReal (Real.exp (Real.rpow (max ((resampleVar p X ω).toReal / θ) 0) s)) := by
      filter_upwards [hV] with ω hω
      rw [hω, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), hLsq, hβs,
        max_eq_left (div_nonneg ENNReal.toReal_nonneg hθ.le), Real.rpow_eq_pow]
      congr 3
      rw [mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hCc.ne', one_mul, div_eq_inv_mul]
    rw [lintegral_congr_ae hcongr, ← ofReal_integral_eq_lintegral_ofReal hXO.1
      (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hXO.2
  have hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (|L⁻¹ * X ω - ∫ ω', L⁻¹ * X ω' ∂latticeBondLaw d p|
      ^ β)) ∂latticeBondLaw d p ≤ ENNReal.ofReal (Cc * 2 ^ (1 / s)) := by
    refine h.trans ?_
    calc ENNReal.ofReal Cc * (∫⁻ ω, ENNReal.ofReal (Real.exp ((Cc * (resampleVar p
          (fun ω => L⁻¹ * X ω) ω).toReal) ^ (β / (2 - β)))) ∂latticeBondLaw d p) ^ ((2 - β) / β)
        ≤ ENNReal.ofReal Cc * ENNReal.ofReal 2 ^ ((2 - β) / β) :=
          mul_le_mul_right (ENNReal.rpow_le_rpow hrhs (by rw [hβi]; positivity)) _
      _ = ENNReal.ofReal (Cc * 2 ^ (1 / s)) := by
          rw [hβi, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity),
            ← ENNReal.ofReal_mul hCc.le]
  -- the pointwise bound
  have hpt : ∀ ω, |X ω - ∫ ω', X ω' ∂latticeBondLaw d p| ^ q ≤
      L ^ q * (q / β) ^ (q / β) * Real.exp (|L⁻¹ * X ω - ∫ ω', L⁻¹ * X ω' ∂latticeBondLaw d p|
        ^ β) := by
    intro ω
    set a := |L⁻¹ * X ω - ∫ ω', L⁻¹ * X ω' ∂latticeBondLaw d p| with ha
    have ha0 : 0 ≤ a := abs_nonneg _
    have hXa : |X ω - ∫ ω', X ω' ∂latticeBondLaw d p| = L * a := by
      rw [ha, integral_const_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hL0), ← mul_assoc,
        mul_inv_cancel₀ hL0.ne', one_mul]
    have hqβ : β * (q / β) = q := by field_simp
    have haq : a ^ q = (a ^ β) ^ (q / β) := by
      rw [← Real.rpow_mul ha0, hqβ]
    have hb := rpow_le_rpow_mul_exp (Real.rpow_nonneg ha0 β) (div_pos hq0 hβ0)
    have he : Real.exp (-(q / β)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [div_pos hq0 hβ0])
    rw [hXa, Real.mul_rpow hL0.le ha0, haq, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hb.trans ?_) (by positivity)
    calc (q / β) ^ (q / β) * Real.exp (-(q / β)) * Real.exp (a ^ β)
        ≤ (q / β) ^ (q / β) * 1 * Real.exp (a ^ β) := by gcongr
      _ = (q / β) ^ (q / β) * Real.exp (a ^ β) := by rw [mul_one]
  have hint : ∫⁻ ω, ENNReal.ofReal (|X ω - ∫ ω', X ω' ∂latticeBondLaw d p| ^ q)
      ∂latticeBondLaw d p ≤ ENNReal.ofReal (L ^ q * (q / β) ^ (q / β) * (Cc * 2 ^ (1 / s))) := by
    calc ∫⁻ ω, ENNReal.ofReal (|X ω - ∫ ω', X ω' ∂latticeBondLaw d p| ^ q) ∂latticeBondLaw d p
        ≤ ∫⁻ ω, ENNReal.ofReal (L ^ q * (q / β) ^ (q / β)) * ENNReal.ofReal (Real.exp
            (|L⁻¹ * X ω - ∫ ω', L⁻¹ * X ω' ∂latticeBondLaw d p| ^ β)) ∂latticeBondLaw d p := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpt ω)
      _ = ENNReal.ofReal (L ^ q * (q / β) ^ (q / β)) * ∫⁻ ω, ENNReal.ofReal (Real.exp
            (|L⁻¹ * X ω - ∫ ω', L⁻¹ * X ω' ∂latticeBondLaw d p| ^ β)) ∂latticeBondLaw d p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (L ^ q * (q / β) ^ (q / β)) * ENNReal.ofReal (Cc * 2 ^ (1 / s)) :=
          mul_le_mul_right hexp _
      _ = ENNReal.ofReal (L ^ q * (q / β) ^ (q / β) * (Cc * 2 ^ (1 / s))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  refine hint.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the constants
  have hM : Cc * 2 ^ (1 / s) ≤ max 1 (Cc * 2 ^ (1 / s)) ^ q :=
    (le_max_right 1 _).trans ((Real.rpow_one _).symm.le.trans
      (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hq))
  have hqb : (q / β) ^ (q / β) = (q ^ (1 / β) / β ^ (1 / β)) ^ q := by
    rw [← Real.div_rpow hq0.le hβ0.le, ← Real.rpow_mul (div_nonneg hq0.le hβ0.le),
      one_div_mul_eq_div]
  rw [hβk, hqb, hL, Real.sqrt_mul hCc.le]
  calc (Real.sqrt Cc * Real.sqrt θ) ^ q * (q ^ (1 / β) / β ^ (1 / β)) ^ q * (Cc * 2 ^ (1 / s))
      ≤ (Real.sqrt Cc * Real.sqrt θ) ^ q * (q ^ (1 / β) / β ^ (1 / β)) ^ q *
          max 1 (Cc * 2 ^ (1 / s)) ^ q :=
        mul_le_mul_of_nonneg_left hM (by positivity)
    _ = (Real.sqrt Cc / β ^ (1 / β) * max 1 (Cc * 2 ^ (1 / s)) * Real.sqrt θ *
          q ^ (1 / β)) ^ q := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          ← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        ring

end Concentration

/-- `r X ≤ O_s(C)` gives `X ≤ O_s(C/r)`. -/
theorem isOsBond_div_of_mul {p : unitInterval} {X : Configuration d → ℝ} {s C r : ℝ}
    (h : IsOsBond d p (fun ω => r * X ω) s C) : IsOsBond d p X s (C / r) := by
  have e : ∀ ω, X ω / (C / r) = r * X ω / C := fun ω => by
    rw [div_div_eq_mul_div, mul_comm (X ω) r]
  unfold IsOsBond at h ⊢
  simp only [e]
  exact h

/-- **Dario, Lemma 3.2 in dimension `d ≥ 3`**:
`|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C r^{-d/2}` for `r ≥ 1`. It holds
(`darioMeanBoundThree_holds`). -/
def DarioMeanBoundThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
        |∫ ω, heatComp (fun z => coarseField hG hGv i 0 z ω) r x j ∂latticeBondLaw d p| ≤
          C / r ^ ((d : ℝ) / 2)

/-- **Dario, Lemma 3.3 in dimension `d ≥ 3`**, proved in `darioVarianceBoundThree_holds`:
`𝕍[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)] ≤ O_s(C r^{-d})` for `r ≥ 1`. -/
def DarioVarianceBoundThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
        (∀ᵐ ω ∂latticeBondLaw d p, resampleVar p
          (fun ω => heatComp (fun z => coarseField hG hGv i 0 z ω) r x j) ω < ∞) ∧
        IsOsBond d p (fun ω => (resampleVar p
          (fun ω => heatComp (fun z => coarseField hG hGv i 0 z ω) r x j) ω).toReal) s
          (C / r ^ (d : ℝ))

/-- **Dario, Proposition 3.1 in dimension `d ≥ 3`**, from the concentration inequality
(Proposition 2.17, proved in every dimension) and Lemmas 3.2 and 3.3, as in the source:
`|X| ≤ |E[X]| + |X - E[X]|` componentwise, the second term bounded through the concentration
inequality. -/
theorem darioPropThreeOneThree_of_lemmas (h32 : DarioMeanBoundThree)
    (h33 : DarioVarianceBoundThree) : DarioPropThreeOneThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  have hd : 2 ≤ d := by omega
  obtain ⟨C₁, hC₁, h1⟩ := h32 d hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨s, C₂, hs, hC₂, h2⟩ := h33 d hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨s₀, C₀, hs₀, hC₀, h0⟩ := heatGradient_coarseField_isOsBond hG hGv hd hpc hp1 hGae
  obtain ⟨A, hA, hmomX⟩ := lintegral_abs_sub_integral_rpow_le p (concentration_holds (d := d)) hs
  set k : ℝ := (1 + s) / (2 * s) with hkdef
  have hk : 0 < k := by positivity
  set B : ℝ := A * Real.sqrt C₂ with hB
  have hB0 : 0 < B := by positivity
  set s' : ℝ := 1 / (2 * k) with hs'def
  have hs' : 0 < s' := by positivity
  have hsk : s' * k < 1 := by
    rw [hs'def, one_div_mul_eq_div, div_lt_one (by positivity)]
    linarith
  obtain ⟨C', hC', hmom⟩ := isOsBond_of_moment_le (d := d) (p := p) hB0 hs' hsk
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set κ : ℝ := d * C₁ with hκ
  have hκ0 : 0 < κ := by positivity
  set θW : ℝ := (2 * 4 ^ (1 / s')) ^ (Finset.univ : Finset (Fin d)).card *
    max C' (3 ^ (1 / s')) with hθW
  have hθW0 : 0 < θW := by positivity
  refine ⟨s', 2 * (max (κ * 3 ^ (1 / s')) θW * 4 ^ (1 / s')), hs', by positivity,
    fun i r hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  have hrd : 0 < r ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hr0 _
  have hF : ∀ z, Measurable (coarseField hG hGv i 0 z) := fun z =>
    measurable_coarseField hG hGv i 0 z
  have hHm := measurable_heatGradient_const hF r x
  have hXm : ∀ j, Measurable fun ω => heatComp (fun z => coarseField hG hGv i 0 z ω) r x j :=
    fun j => measurable_heatComp hF r x j
  have hHi : Integrable
      (fun ω => Rigidity.Poincare.GeneralDim.heatGradient (fun z => coarseField hG hGv i 0 z ω) r x)
      (latticeBondLaw d p) := by
    have := (IsOsBond.integral_rpow_le hs₀ hC₀ one_pos hHm (fun ω => heatGradient_nonneg' _ _ _)
      (h0 i r x)).1
    simpa only [Real.rpow_one] using this
  have hXi : ∀ j, Integrable (fun ω => heatComp (fun z => coarseField hG hGv i 0 z ω) r x j)
      (latticeBondLaw d p) := fun j =>
    hHi.mono' (hXm j).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_heatComp_le_heatGradient _ _ _ _)
  set E : Fin d → ℝ := fun j =>
    ∫ ω, heatComp (fun z => coarseField hG hGv i 0 z ω) r x j ∂latticeBondLaw d p with hE
  set Y : Fin d → Configuration d → ℝ := fun j ω => r ^ ((d : ℝ) / 2) *
    |heatComp (fun z => coarseField hG hGv i 0 z ω) r x j - E j| with hY
  have hYm : ∀ j, Measurable (Y j) := fun j =>
    measurable_const.mul ((hXm j).sub measurable_const).abs
  have hY0 : ∀ j ω, 0 ≤ Y j ω := fun j ω => by simp only [hY]; positivity
  -- the moments of the centred components
  have hmomj : ∀ j (q : ℝ), 1 ≤ q → ∫⁻ ω, ENNReal.ofReal (Y j ω) ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((B * q ^ k) ^ q) := by
    intro j q hq
    have hq0 : 0 < q := by linarith
    have hθ : 0 < C₂ / r ^ (d : ℝ) := by positivity
    have h := hmomX _ _ hθ (hXi j) (h2 i j r hr x).1 (h2 i j r hr x).2 q hq
    calc ∫⁻ ω, ENNReal.ofReal (Y j ω) ^ q ∂latticeBondLaw d p
        = ∫⁻ ω, ENNReal.ofReal ((r ^ ((d : ℝ) / 2)) ^ q) * ENNReal.ofReal (|heatComp
            (fun z => coarseField hG hGv i 0 z ω) r x j - E j| ^ q) ∂latticeBondLaw d p := by
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_rpow_of_nonneg (hY0 j ω) hq0.le, hY,
            Real.mul_rpow hrd.le (abs_nonneg _), ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((r ^ ((d : ℝ) / 2)) ^ q) * ∫⁻ ω, ENNReal.ofReal (|heatComp
            (fun z => coarseField hG hGv i 0 z ω) r x j - E j| ^ q) ∂latticeBondLaw d p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((r ^ ((d : ℝ) / 2)) ^ q) * ENNReal.ofReal
            ((A * Real.sqrt (C₂ / r ^ (d : ℝ)) * q ^ k) ^ q) :=
          mul_le_mul_right h _
      _ = ENNReal.ofReal ((B * q ^ k) ^ q) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hrd.le (by positivity)]
          congr 2
          have hsq : Real.sqrt (C₂ / r ^ (d : ℝ)) = Real.sqrt C₂ / r ^ ((d : ℝ) / 2) := by
            rw [Real.sqrt_div' _ (by positivity), Real.sqrt_eq_rpow (r ^ (d : ℝ)),
              ← Real.rpow_mul hr0.le, show (d : ℝ) * (1 / 2) = d / 2 by ring]
          rw [hsq, hB, show r ^ ((d : ℝ) / 2) * (A * (Real.sqrt C₂ / r ^ ((d : ℝ) / 2)) * q ^ k) =
            A * Real.sqrt C₂ * q ^ k * (r ^ ((d : ℝ) / 2) / r ^ ((d : ℝ) / 2)) by ring,
            div_self hrd.ne', mul_one]
  have hYO : ∀ j, IsOsBond d p (Y j) s' C' := fun j =>
    isOsBond_of_ae_ofReal_le hB0.le hmom (hYm j) (hY0 j) (T := fun ω => ENNReal.ofReal (Y j ω))
      (Eventually.of_forall fun ω => le_rfl) fun q hq => hmomj j q hq
  have hW := isOsBond_sum (Finset.univ : Finset (Fin d)) Y hYm hY0 hs' hC' fun j _ => hYO j
  have hc := isOsBond_const (d := d) (p := p) hκ0 hs'
  have hWm : Measurable fun ω => ∑ j, Y j ω := Finset.measurable_sum _ fun j _ => hYm j
  have hmax := IsOsBond.max hs' (by positivity) hθW0 measurable_const hWm hc hW
  have h2max := IsOsBond.const_mul two_pos hmax
  -- the pointwise bound
  have hpt : ∀ ω, r ^ ((d : ℝ) / 2) *
      Rigidity.Poincare.GeneralDim.heatGradient (fun z => coarseField hG hGv i 0 z ω) r x ≤
      2 * max κ (∑ j, Y j ω) := by
    intro ω
    have hEj : ∀ j, r ^ ((d : ℝ) / 2) * |E j| ≤ C₁ := fun j => by
      have := h1 i j r hr x
      rw [le_div_iff₀ hrd, mul_comm] at this
      exact this
    have hj : ∀ j, r ^ ((d : ℝ) / 2) * |heatComp (fun z => coarseField hG hGv i 0 z ω) r x j| ≤
        C₁ + Y j ω := fun j => by
      have h3 := mul_le_mul_of_nonneg_left (abs_sub_abs_le_abs_sub
        (heatComp (fun z => coarseField hG hGv i 0 z ω) r x j) (E j)) hrd.le
      rw [mul_sub] at h3
      simp only [hY]
      linarith [hEj j]
    rw [heatGradient_eq_sum_abs_heatComp, Finset.mul_sum]
    calc ∑ j, r ^ ((d : ℝ) / 2) * |heatComp (fun z => coarseField hG hGv i 0 z ω) r x j|
        ≤ ∑ j, (C₁ + Y j ω) := Finset.sum_le_sum fun j _ => hj j
      _ = κ + ∑ j, Y j ω := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, hκ]
      _ ≤ 2 * max κ (∑ j, Y j ω) := by
          have := le_max_left κ (∑ j, Y j ω)
          have := le_max_right κ (∑ j, Y j ω)
          linarith
  exact isOsBond_div_of_mul
    (IsOsBond.mono_variable hs' (by positivity) (measurable_const.mul hHm) hpt h2max)

/-- **Dario's Theorem 1 in dimension `d ≥ 3`** (`DarioOptimalCorrectorThree`) from his Lemmas 3.2
and 3.3 in dimension `d ≥ 3`. -/
theorem darioOptimalCorrectorThree_of_lemmas (h32 : DarioMeanBoundThree)
    (h33 : DarioVarianceBoundThree) : DarioOptimalCorrectorThree :=
  darioOptimalCorrectorThree_of_prop31 (darioPropThreeOneThree_of_lemmas h32 h33)

end Rigidity.Corrector.GeneralDim

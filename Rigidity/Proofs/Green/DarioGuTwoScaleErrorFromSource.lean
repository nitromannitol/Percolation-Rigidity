import Rigidity.Proofs.Green.DarioGuTwoScaleAssembly

/-!
# Proposition 4.3 of Dario–Gu from the estimate of the source term

`DarioGuTwoScaleSourceBoundTwo` is the estimate of Steps 3-4 of the proof of Proposition 4.3 of
Dario–Gu (lines 2333-2446 of the source), (4.32) and (4.39) combined with Young's inequality: for
`r ≥ M(y)`, every truncated weight `ψ_R = dgWeightTrunc C r R y` (`ψ_0 = 1`) and every square
summable `v` vanishing off the cluster,
`Σ_x ψ_R² v G(r) ≤ E(ψ_R v) + (2r)^{-1} Σ_x (ψ_R v)² + Q r^{α - 3}`, where
`G = 1_{𝒞_∞} θ^{-1} twoScaleSource` is the source term of the equation of `w`.

`darioGuTwoScaleErrorTwo_of_sourceBound` proves `DarioGuTwoScaleErrorTwo` (Proposition 4.3) from
this estimate and the quantitative corrector estimate (Proposition 2.12,
`CorrectorQuantitativeInputTwo`), which gives the
linear growth of the corrector on the cluster used by the summability layer.
-/

open scoped Classical
open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- **Steps 3-4 of the proof of Proposition 4.3 of Dario–Gu** (the estimates (4.32) and (4.39)
combined with Young's inequality), in dimension two, for the weights `ψ_R` with `C ≥ C₀`. -/
def DarioGuTwoScaleSourceBoundTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ Q s : ℝ, 0 < Q ∧ 0 < s ∧
    ∀ y : Vertex 2, ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      IsOsBond 2 p M s Q ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin 2 → Vertex 2 → ℝ,
          IsDGCorrector (uniqueInfiniteComponent h) y χ → ∀ r : ℝ, M ω ≤ r →
          ∀ R : ℝ, 0 ≤ R → ∀ v : Vertex 2 → ℝ, Summable (fun x => v x ^ 2) →
            (∀ x, x ∉ (uniqueInfiniteComponent h).supp → v x = 0) →
            ∑' x, dgWeightTrunc C r R y x ^ 2 * v x *
                clusterSource (uniqueInfiniteComponent h) σ (theta 2 p) χ y r x ≤
              openEnergy ω (fun x => dgWeightTrunc C r R y x * v x) +
                1 / (2 * r) * ∑' x, (dgWeightTrunc C r R y x * v x) ^ 2 + Q * r ^ (α - 3)

/-- `WeightedL2Le` is monotone in the constant of the weight and in the bound. -/
theorem WeightedL2Le.mono {K : Set (Vertex 2)} {C C' t : ℝ} {y : Vertex 2} {f : Vertex 2 → ℝ}
    {B B' : ℝ} (h : WeightedL2Le K C t y f B) (hC : 0 < C) (hCC : C ≤ C') (ht : 0 < t)
    (hB : 0 ≤ B) (hBB : B ≤ B') : WeightedL2Le K C' t y f B' := by
  intro S hS
  refine (Finset.sum_le_sum fun x _ => ?_).trans ((h S hS).trans (pow_le_pow_left₀ hB hBB 2))
  rw [mul_pow, mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le
    (Real.exp_le_exp.2 ?_) 2) (sq_nonneg _)
  rw [dgExponent_eq, dgExponent_eq]
  exact div_le_div_of_nonneg_left (dgShape_nonneg ht (latticeDist_nonneg x y)) hC hCC

/-- **Proposition 4.3 of Dario–Gu** (`DarioGuTwoScaleErrorTwo`) from the estimate of Steps 3-4
and Proposition 2.12. -/
theorem darioGuTwoScaleErrorTwo_of_sourceBound (hR5 : CorrectorQuantitativeInputTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hσ : 0 < σ) (hsb : DarioGuTwoScaleSourceBoundTwo p σ) : DarioGuTwoScaleErrorTwo p σ := by
  intro α hα
  set θ := theta 2 p with hθdef
  set α' := min α 1 with hα'
  have hα'0 : 0 < α' := lt_min hα one_pos
  have hα'1 : α' ≤ 1 := min_le_right _ _
  have hα'α : α' ≤ α := min_le_left _ _
  obtain ⟨C₀s, hC₀s, hsb'⟩ := hsb α' hα'0
  obtain ⟨C₀w, hC₀w, hw⟩ := dgWeightTrunc_edgeKappa_bound (K := 1) (A := 1 / 2) one_pos
    (by norm_num)
  set Cw := max C₀s C₀w with hCw
  have hCw0 : 0 < Cw := lt_max_of_lt_left hC₀s
  obtain ⟨C₁, hC₁, hwb⟩ := hw Cw (le_max_right _ _)
  obtain ⟨Q, s₁, hQ, hs₁, h1⟩ := hsb' Cw (le_max_left _ _)
  obtain ⟨s₂, C₅, hs₂, hC₅, h5⟩ := hR5 p hpc hp1 (1 / 2) (by norm_num)
  choose M₁ hM1m hM10 hM1os hM1ae using h1
  choose M₂ hM2m hM20 hM2os hM2ae using h5
  set s := min s₁ (s₂ / 2) with hs
  have hs0 : 0 < s := lt_min hs₁ (by positivity)
  set θ1 := Q * (6 : ℝ) ^ (1 / s) with hθ1
  set θ2 := C₅ ^ 2 * (6 : ℝ) ^ (1 / s) with hθ2
  set θ3 := (1 : ℝ) * (3 : ℝ) ^ (1 / s) with hθ3
  set θM := max (max θ1 θ2 * (4 : ℝ) ^ (1 / s)) θ3 * (4 : ℝ) ^ (1 / s) with hθM
  set K' := 2 * C₁ * (2 * Q / (3 - α')) + 2 * Q / (2 - α') with hK'
  set Cf := max (max θM Cw) (Real.sqrt K') with hCf
  have hθM0 : 0 < θM := by positivity
  have hCf0 : 0 < Cf := lt_max_of_lt_left (lt_max_of_lt_left hθM0)
  refine ⟨Cf, s, hCf0, hs0, fun y => ?_⟩
  set M : Configuration 2 → ℝ := fun ω => max (max (M₁ y ω) (M₂ y ω ^ 2)) 1 with hM
  have hMm : Measurable M := ((hM1m y).max ((hM2m y).pow_const 2)).max measurable_const
  have hos1 : IsOsBond 2 p (M₁ y) s θ1 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_left _ _) (hM1m y) (hM1os y)
  have hos2 : IsOsBond 2 p (fun ω => M₂ y ω ^ 2) s θ2 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_right _ _) ((hM2m y).pow_const 2)
      (IsOsBond.sq_of_nonneg hC₅ (hM20 y) (hM2os y))
  have hos12 := Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
    (hM1m y) ((hM2m y).pow_const 2) hos1 hos2
  have hosM : IsOsBond 2 p M s θM :=
    Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
      ((hM1m y).max ((hM2m y).pow_const 2)) measurable_const hos12
      (Rigidity.Proofs.S2.isOsBond_const one_pos hs0)
  refine ⟨M, hMm, fun ω => le_max_of_le_right zero_le_one,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs0 hθM0
      ((le_max_left _ _).trans (le_max_left _ _)) hMm hosM, ?_⟩
  filter_upwards [hM1ae y, hM2ae y] with ω hω1 hω2
  intro h hy χ hχ t τ hτ h3τ
  set K := uniqueInfiniteComponent h with hK
  have hτ1 : 1 ≤ τ := (le_max_right _ _).trans hτ
  have hτ0 : 0 < τ := by linarith
  have hτt : τ ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hM1τ : M₁ y ω ≤ τ := (le_max_left _ _).trans ((le_max_left _ _).trans hτ)
  have hM2τ : M₂ y ω ≤ Real.sqrt τ := by
    rw [← Real.sqrt_sq (hM20 y ω)]
    exact Real.sqrt_le_sqrt ((le_max_right _ _).trans ((le_max_left _ _).trans hτ))
  -- the linear growth of the corrector on the cluster (Proposition 2.12 at the centre `y`)
  set A := C₅ * (Real.sqrt τ + 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hχb : ∀ x ∈ K.supp, ∀ k : Fin 2, |χ k x| ≤ A * (1 + latticeDist x y) := by
    intro x hx k
    obtain ⟨b', hadj, hb'd⟩ := exists_adj_near (uniqueInfiniteComponent_infinite h) ⟨x, hx⟩
    have hd0 := latticeDist_nonneg x y
    have hsq0 := Real.sqrt_nonneg τ
    have hr : M₂ y ω ≤ Real.sqrt τ + latticeDist x y + 2 := by linarith
    have hb'y : latticeDist b'.val y ≤ latticeDist x y + 1 := by
      have := latticeDist_triangle b'.val x y
      rw [latticeDist_comm x b'.val] at this
      linarith
    have := hω2 h (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) (hχ k).1 _ hr
      ⟨x, hx⟩ ⟨y, hy⟩ ⟨x, hx⟩ b' (by change latticeDist x y < _; linarith)
      (by change latticeDist y y < _
          rw [show latticeDist y y = 0 by simp [latticeDist]]; linarith)
      (by change latticeDist x y < _; linarith) (by change latticeDist b'.val y < _; linarith) hadj
    simp only [Rigidity.Corrector.sum_single_mul, Rigidity.Corrector.sum_abs_single,
      mul_one] at this
    have e1 : (x k : ℝ) + χ k x - x k - ((y k : ℝ) + χ k y - y k) = χ k x := by
      rw [(hχ k).2]; ring
    rw [e1] at this
    have hχ1 := le_of_add_le_of_nonneg_left this (abs_nonneg _)
    have hbase : 1 ≤ Real.sqrt τ + latticeDist x y + 2 := by linarith
    have hpow : (Real.sqrt τ + latticeDist x y + 2) ^ (1 / 2 : ℝ) ≤
        Real.sqrt τ + latticeDist x y + 2 := by
      calc (Real.sqrt τ + latticeDist x y + 2) ^ (1 / 2 : ℝ)
          ≤ (Real.sqrt τ + latticeDist x y + 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
        _ = Real.sqrt τ + latticeDist x y + 2 := Real.rpow_one _
    have hlin : Real.sqrt τ + latticeDist x y + 2 ≤ (Real.sqrt τ + 2) * (1 + latticeDist x y) := by
      nlinarith
    calc |χ k x| ≤ C₅ * (Real.sqrt τ + latticeDist x y + 2) ^ (1 / 2 : ℝ) := hχ1
      _ ≤ C₅ * ((Real.sqrt τ + 2) * (1 + latticeDist x y)) :=
          mul_le_mul_of_nonneg_left (hpow.trans hlin) hC₅.le
      _ = A * (1 + latticeDist x y) := by rw [hA]; ring
  -- the estimate of Steps 3-4 along `u = 1_K w`
  have hsrc : ∀ r ∈ Set.Ioo τ t, ∀ R : ℝ, 0 ≤ R →
      ∑' x, dgWeightTrunc Cw r R y x ^ 2 * clusterW K σ θ χ τ y r x *
          clusterSource K σ θ χ y r x ≤
        openEnergy ω (fun x => dgWeightTrunc Cw r R y x * clusterW K σ θ χ τ y r x) +
          1 / (2 * r) * ∑' x, (dgWeightTrunc Cw r R y x * clusterW K σ θ χ τ y r x) ^ 2 +
            Q * r ^ (α' - 3) := by
    intro r hr R hR
    obtain ⟨D, hD, hDu⟩ := exists_clusterW_dom (θ := θ) hσ hτ0 hr.1.le hA0 hχb
    have hv : Summable fun x => clusterW K σ θ χ τ y r x ^ 2 :=
      Summable.of_nonneg_of_le (fun x => sq_nonneg _)
        (fun x => sq_le_sq_of_abs_le (hDu r ⟨hr.1.le, le_rfl⟩ x)) hD
    exact hω1 h hy χ hχ r (hM1τ.trans hr.1.le) R hR _ hv
      (fun x hx => by
        unfold clusterW
        exact if_neg hx)
  have hwtb : ∀ (s R : ℝ) (x : Vertex 2), 1 ≤ s → 0 ≤ R →
      dgWeightTrunc Cw s R y x ^ 2 *
          (dgShapeTimeDeriv s (min (latticeDist x y) R) / Cw + 1 / 2 / s) +
        1 * edgeKappa ω (dgWeightTrunc Cw s R y) x ≤ C₁ / s :=
    fun s R x hs hR => hwb ω s R y x hs hR
  have hmain := dgW_weightedL2Le_of_sourceBound hχ hσ hτ1 hτt hA0 hχb hQ.le
    (by linarith : α' < 2) hCw0 hC₁.le hwtb hsrc
  refine hmain.mono hCw0 ((le_max_right _ _).trans (le_max_left _ _)) ht0 (by positivity) ?_
  have hτα : τ ^ (-(1 : ℝ) + α' / 2) ≤ τ ^ (-(1 : ℝ) + α / 2) :=
    Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
  have hsK : Real.sqrt K' ≤ Cf := le_max_right _ _
  have h0 : 0 ≤ (t / τ) ^ (1 / 2 : ℝ) := by positivity
  have h0' : 0 ≤ τ ^ (-(1 : ℝ) + α' / 2) := by positivity
  calc Real.sqrt K' * (t / τ) ^ (1 / 2 : ℝ) * τ ^ (-(1 : ℝ) + α' / 2)
      ≤ Cf * (t / τ) ^ (1 / 2 : ℝ) * τ ^ (-(1 : ℝ) + α' / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsK h0) h0'
    _ ≤ Cf * (t / τ) ^ (1 / 2 : ℝ) * τ ^ (-(1 : ℝ) + α / 2) :=
        mul_le_mul_of_nonneg_left hτα (by positivity)

end Rigidity.Green

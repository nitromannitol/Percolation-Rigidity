import Rigidity.Proofs.Green.HeatKernelCoreD
import Rigidity.Proofs.Green.LatticeSupD
import Rigidity.Proofs.Green.DensityGaussianD
import Rigidity.Proofs.BarlowLattice.GaussianHolds

/-!
# Theorem 1 of Dario–Gu on `ℤ^d` from the whole-cluster estimate

`darioGuHeatKernelD_of_gaussianFlow`: for `d ≥ 2`, Theorem 1 of Dario–Gu (`DarioGuHeatKernelD d`)
follows from the whole-cluster estimate (4.40) with Proposition 2.12 (`DarioGuGaussianFlowD d p σ`)
alone. The other inputs are proved: the Gaussian upper bound of Barlow, Theorem 4
(`barlowGaussianUpperBound_holds`), the Carne–Varopoulos bound, Proposition 2.15
(`cvBranches_sixteen`), Proposition A.7 (`darioGuDensityGaussianD_holds`) and the order-zero
estimate of Armstrong and Dario at every centre (`exists_orderZero_clusterBallD`).

The random time. With `s = t/2`, the point source at a pole `w`
(`exists_l2norm_pointSource_le_rpow`) needs at `w` the order-zero scale `X(w) ≤ s^{η/2}`, the scale
`Y(w) = sup {T_NA(v) : |v - w| ≤ T_NA(v) + 1}` (`latticeSupD`) of the on-diagonal bound around `w`
with `max(Y(w), 1) ≤ s^{η/2}`, `T_NA(w) ≤ s^η`, `2 T_dense(w) ≤ s^η` and `M(w) ≤ s^η`, and the
pair estimate (`exists_abs_vsrwHeat_sub_le_gaussian`) needs `T_NA ≤ s^η` and `T_dense < s^η` at
the points of `B_{2t+1}(y)`. With `F(w)` the maximum of `X(w)²`, `max(Y(w), 1)²`, `T_NA(w)`,
`2 T_dense(w)` and `M(w)`, all of them follow from `4 F(w)^{1/η} ≤ 2t` on `B_{2t+1}(y)`, which
holds for `t ≥ latticeSupD (4 F^{1/η}) y`; its tail is that of `F` (`hasTail_latticeSupD`).
The bound has the exponent `1/2 - 6η` with `η = min(δ, 1/2)/6`.
-/

open scoped Classical
open MeasureTheory Filter LatticeProb.Percolation Rigidity.WeakPoincare Rigidity.External

namespace Rigidity.Green

local notation "ldist" => Rigidity.WeakPoincare.latticeDist

variable {d : ℕ} {p : unitInterval}

/-- A tail with a larger constant and a smaller exponent. -/
theorem HasTailD.lower {X : Configuration d → ℝ} {C s s' : ℝ} (h : HasTailD p X C s)
    (hC : 0 < C) (hs' : 0 < s') (hss : s' ≤ s) : HasTailD p X (Max.max C 2) s' :=
  (h.mono hC (le_max_left _ _)).mono_exponent (le_max_right _ _) hs' hss

/-- The tail of the maximum of two variables with tails of the same exponent. -/
theorem HasTailD.max_of {X Y : Configuration d → ℝ} {C C' s : ℝ} (hX : HasTailD p X C s)
    (hY : HasTailD p Y C' s) (hC : 0 < C) (hC' : 0 < C') :
    HasTailD p (fun ω => Max.max (X ω) (Y ω)) (2 * Max.max C C') s :=
  (hX.mono hC (le_max_left _ _)).max (hY.mono hC' (le_max_right _ _)) (lt_max_of_lt_left hC)

/-- Tails uniform in the point give a tail of the maximum, uniform in the point. -/
theorem exists_hasTailD_max {X Y : Vertex d → Configuration d → ℝ} {s : ℝ}
    (hX : ∃ C, 0 < C ∧ ∀ w, HasTailD p (X w) C s) (hY : ∃ C, 0 < C ∧ ∀ w, HasTailD p (Y w) C s) :
    ∃ C, 0 < C ∧ ∀ w, HasTailD p (fun ω => max (X w ω) (Y w ω)) C s := by
  obtain ⟨C, hC, hX⟩ := hX
  obtain ⟨C', hC', hY⟩ := hY
  exact ⟨2 * max C C', mul_pos two_pos (lt_max_of_lt_left hC),
    fun w => (hX w).max_of (hY w) hC hC'⟩

/-- `C t^a e^{-D²/(C t)}` is nondecreasing in `C`. -/
theorem mul_rpow_mul_exp_le {C C' t a D : ℝ} (hC : 0 < C) (hCC : C ≤ C') (ht : 0 < t) :
    C * t ^ a * Real.exp (-(D ^ 2 / (C * t))) ≤ C' * t ^ a * Real.exp (-(D ^ 2 / (C' * t))) := by
  have hC' : 0 < C' := lt_of_lt_of_le hC hCC
  have hE : Real.exp (-(D ^ 2 / (C * t))) ≤ Real.exp (-(D ^ 2 / (C' * t))) :=
    exp_neg_div_le (sq_nonneg D) (by positivity) (mul_le_mul_of_nonneg_right hCC ht.le)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hCC (by positivity)) hE (Real.exp_pos _).le
    (by positivity)

/-- `F ≤ (t/2)^η` from `4 F^{1/η} ≤ 2t`. -/
theorem le_rpow_of_four_mul_rpow_inv_le {F η t : ℝ} (hF : 0 ≤ F) (hη : 0 < η)
    (h : 4 * F ^ η⁻¹ ≤ 2 * t) : F ≤ (t / 2) ^ η := by
  have h1 : F ^ η⁻¹ ≤ t / 2 := by linarith
  calc F = (F ^ η⁻¹) ^ η := (Real.rpow_inv_rpow hF hη.ne').symm
    _ ≤ (t / 2) ^ η := Real.rpow_le_rpow (by positivity) h1 hη.le

/-- `x ≤ u^{η/2}` from `x² ≤ u^η`. -/
theorem le_rpow_half_of_rpow_two_le {x u η : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u)
    (h : x ^ (2 : ℝ) ≤ u ^ η) : x ≤ u ^ (η / 2) := by
  have h1 := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  rwa [Real.rpow_rpow_inv hx (by norm_num), ← Real.rpow_mul hu, ← div_eq_mul_inv] at h1

variable [NeZero d]

/-- **Dario–Gu, Theorem 1, on `ℤ^d`** (`d ≥ 2`) from the whole-cluster estimate (4.40) with
Proposition 2.12 (`DarioGuGaussianFlowD`). -/
theorem darioGuHeatKernelD_of_gaussianFlow (hd : 2 ≤ d)
    (hflow : ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuGaussianFlowD d p σ) : DarioGuHeatKernelD d := by
  intro p hpc hp1
  obtain ⟨σ, hσ, hGF⟩ := hflow p hpc hp1
  refine ⟨σ, hσ, fun δ hδ => ?_⟩
  have hθ : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  set θ := theta d p with hθdef
  set η := min δ (1 / 2) / 6 with hηdef
  have hη0 : 0 < η := div_pos (lt_min hδ (by norm_num)) (by norm_num)
  have hη12 : η ≤ 1 / 12 := by
    have := min_le_right δ (1 / 2)
    rw [hηdef]
    linarith
  have hηδ : 6 * η ≤ δ := by
    have := min_le_left δ (1 / 2)
    rw [hηdef]
    linarith
  -- the inputs
  obtain ⟨sB, Cb, hsB, hCb, hBarlow⟩ :=
    Rigidity.BarlowLattice.barlowGaussianUpperBound_holds hd p hpc hp1
  choose TNA hTNAm hTNA0 hTNAos hTNAae using hBarlow
  obtain ⟨CA, sA, hCA, hsA, hA7⟩ := darioGuDensityGaussianD_holds hd hpc hp1 hσ η hη0
  choose Td hTdm hTd0 hTdos hTdae using hA7
  obtain ⟨CG, sG, hCG, hsG, hGFy⟩ := hGF η hη0
  choose M hMm hM0 hMos hMae using hGFy
  obtain ⟨sX, θX, C₀, hsX, hθX, hC₀, X, hXm, hX0, hXos, hXae⟩ :=
    exists_orderZero_clusterBallD hd hpc hp1
  obtain ⟨E, t₁, hE, ht₁, hPS⟩ := exists_l2norm_pointSource_le_rpow (d := d) hσ hθ hη0
    (by linarith only [hη12]) hC₀.le hCb.le hCA.le hCG.le
  obtain ⟨K₀, t₂, hK₀, ht₂, hPair⟩ := exists_abs_vsrwHeat_sub_le_gaussian (d := d) hσ hθ hη0
    hη12 hE.le hCb hCA.le
  obtain ⟨a₄, ha₄⟩ := eventually_atTop.1 (eventually_twelve_mul_le (γ := 0) (η := η)
    (by linarith only [hη12]))
  -- the scale of the on-diagonal bound around each point
  have hTNAt : ∀ w, HasTailD p (TNA w) (max 2 (Cb ^ sB)) sB :=
    fun w => hasTailD_of_isOsBond hsB hCb (hTNAos w)
  obtain ⟨CY, hCY, hY⟩ := hasTail_latticeSupD (lt_max_of_lt_left two_pos) hsB hTNAt
  set Y : Vertex d → Configuration d → ℝ := fun w => latticeSupD TNA w with hYdef
  -- the five quantities and their maximum
  set F : Vertex d → Configuration d → ℝ := fun w ω =>
    max (max (X w ω ^ (2 : ℝ)) (max (Y w ω) 1 ^ (2 : ℝ)))
      (max (TNA w ω) (max (2 * Td w ω) (M w ω))) with hFdef
  set Φ : Vertex d → Configuration d → ℝ := fun w ω => 4 * F w ω ^ η⁻¹ with hΦdef
  have hF0 : ∀ w ω, 0 ≤ F w ω := fun w ω =>
    le_max_of_le_right (le_max_of_le_left (hTNA0 w ω))
  have hYm : ∀ w, Measurable (Y w) := fun w => measurable_latticeSupD hTNAm w
  have hFm : ∀ w, Measurable (F w) := fun w =>
    (((hXm w).pow_const _).max (((hYm w).max measurable_const).pow_const _)).max
      ((hTNAm w).max (((hTdm w).const_mul 2).max (hMm w)))
  have hΦm : ∀ w, Measurable (Φ w) := fun w => ((hFm w).pow_const _).const_mul 4
  -- the tails
  set s₀ := min (min (sX / 2) (sB / 2)) (min sA sG) with hs₀
  have hs₀0 : 0 < s₀ :=
    lt_min (lt_min (by linarith only [hsX]) (by linarith only [hsB])) (lt_min hsA hsG)
  have hs₀X : s₀ ≤ sX / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hs₀B : s₀ ≤ sB / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hs₀A : s₀ ≤ sA := (min_le_right _ _).trans (min_le_left _ _)
  have hs₀G : s₀ ≤ sG := (min_le_right _ _).trans (min_le_right _ _)
  have h1 : ∃ C, 0 < C ∧ ∀ w, HasTailD p (fun ω => X w ω ^ (2 : ℝ)) C s₀ :=
    ⟨_, lt_max_of_lt_right two_pos, fun w =>
      ((hasTailD_of_isOsBond hsX hθX (hXos w)).rpow two_pos (hX0 w)).lower
        (lt_max_of_lt_left two_pos) hs₀0 hs₀X⟩
  have h2 : ∃ C, 0 < C ∧ ∀ w, HasTailD p (fun ω => max (Y w ω) 1 ^ (2 : ℝ)) C s₀ :=
    ⟨_, lt_max_of_lt_right two_pos, fun w =>
      (((hY w).1.max_const hCY hsB (a := 1)).rpow two_pos
        (fun ω => zero_le_one.trans (le_max_right _ _))).lower
        (lt_max_of_lt_left hCY) hs₀0 hs₀B⟩
  have h3 : ∃ C, 0 < C ∧ ∀ w, HasTailD p (TNA w) C s₀ :=
    ⟨_, lt_max_of_lt_right two_pos, fun w =>
      (hTNAt w).lower (lt_max_of_lt_left two_pos) hs₀0 (by linarith only [hs₀B, hsB])⟩
  have h4 : ∃ C, 0 < C ∧ ∀ w, HasTailD p (fun ω => 2 * Td w ω) C s₀ :=
    ⟨_, lt_max_of_lt_right two_pos, fun w =>
      ((hasTailD_of_isOsBond hsA hCA (hTdos w)).const_mul (lt_max_of_lt_left two_pos)
        two_pos).lower (lt_max_of_lt_left (lt_max_of_lt_left two_pos)) hs₀0 hs₀A⟩
  have h5 : ∃ C, 0 < C ∧ ∀ w, HasTailD p (M w) C s₀ :=
    ⟨_, lt_max_of_lt_right two_pos, fun w =>
      (hasTailD_of_isOsBond hsG hCG (hMos w)).lower (lt_max_of_lt_left two_pos) hs₀0 hs₀G⟩
  obtain ⟨CF, hCF, hFt⟩ := exists_hasTailD_max (exists_hasTailD_max h1 h2)
    (exists_hasTailD_max h3 (exists_hasTailD_max h4 h5))
  have hsΦ : 0 < s₀ / η⁻¹ := div_pos hs₀0 (inv_pos.2 hη0)
  have hCΦ : 0 < max CF (4 ^ (s₀ / η⁻¹) * CF) := lt_max_of_lt_left hCF
  have hΦt : ∀ w, HasTailD p (Φ w) (max CF (4 ^ (s₀ / η⁻¹) * CF)) (s₀ / η⁻¹) := fun w =>
    ((hFt w).rpow (inv_pos.2 hη0) (hF0 w)).const_mul hCF (by norm_num)
  obtain ⟨CZ, hCZ, hZ⟩ := hasTail_latticeSupD hCΦ hsΦ hΦt
  -- the deterministic time and the constant
  set t₀ := max (max (2 * t₁) t₂) (max (2 * a₄) (d : ℝ)) with ht₀
  have ht₀1 : 2 ≤ t₀ :=
    le_trans (by linarith only [ht₁]) ((le_max_left _ _).trans (le_max_left _ _))
  set CT := max CZ (max 3 (Real.rpow t₀ (s₀ / η⁻¹))) with hCT
  have hCT0 : 0 < CT := lt_max_of_lt_left hCZ
  refine ⟨max CT K₀, s₀ / η⁻¹, lt_max_of_lt_left hCT0, hsΦ, fun y =>
    ⟨fun ω => max (latticeSupD Φ y ω) t₀, (measurable_latticeSupD hΦm y).max measurable_const,
      fun ω => le_max_of_le_right (by linarith only [ht₀1]),
      ((hZ y).1.max_const hCZ hsΦ).mono hCT0 (le_max_left _ _), ?_⟩⟩
  filter_upwards [hXae, ae_all_iff.2 hTNAae, ae_all_iff.2 hTdae, ae_all_iff.2 hMae,
    ae_all_iff.2 (fun w => (hY w).2), (hZ y).2] with ω hOZ hB hA hM hYb hZb
  intro h hy x hx t ht1 hTt hDt
  have hK : (uniqueInfiniteComponent h).supp.Infinite := uniqueInfiniteComponent_infinite h
  set K := uniqueInfiniteComponent h with hKdef
  have hT0 : t₀ ≤ t := (le_max_right _ _).trans hTt
  have ht0 : 0 < t := by linarith only [ht1]
  have hZt : latticeSupD Φ y ω ≤ 2 * t := by
    have := (le_max_left _ _).trans hTt
    linarith only [this, ht0]
  have ht₁t : 2 * t₁ ≤ t := ((le_max_left _ _).trans (le_max_left _ _)).trans hT0
  have ht₂t : t₂ ≤ t := ((le_max_right _ _).trans (le_max_left _ _)).trans hT0
  have ha₄t : 2 * a₄ ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans hT0
  have hdt : (d : ℝ) ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans hT0
  have hs0 : 0 < t / 2 := by positivity
  have hsη : 0 < (t / 2) ^ η := by positivity
  have hsq : (t / 2) ^ η ≤ t / 2 / 4 := by
    have h := ha₄ (t / 2) (by linarith only [ha₄t])
    rw [Real.rpow_zero, one_pow, mul_one] at h
    linarith only [h, ht0]
  have hsqrt : Real.sqrt (t / 2) ≤ t := by
    have h := Real.sqrt_le_sqrt (show t / 2 ≤ t ^ 2 by nlinarith only [ht1])
    rwa [Real.sqrt_sq ht0.le] at h
  -- the thresholds on `B_{2t+1}(y)`
  have hcomp : ∀ w, ldist w y ≤ 2 * t + 1 →
      X w ω ≤ (t / 2) ^ (η / 2) ∧ max (Y w ω) 1 ≤ (t / 2) ^ (η / 2) ∧
        TNA w ω ≤ (t / 2) ^ η ∧ Td w ω < (t / 2) ^ η ∧ M w ω ≤ (t / 2) ^ η := by
    intro w hw
    have hFw : F w ω ≤ (t / 2) ^ η :=
      le_rpow_of_four_mul_rpow_inv_le (hF0 w ω) hη0 (le_of_latticeSupD_le hZb hZt hw)
    simp only [hFdef, max_le_iff] at hFw
    obtain ⟨⟨hX1, hY1⟩, hT1, hTd1, hM1⟩ := hFw
    exact ⟨le_rpow_half_of_rpow_two_le (hX0 w ω) hs0.le hX1,
      le_rpow_half_of_rpow_two_le (zero_le_one.trans (le_max_right _ _)) hs0.le hY1, hT1,
      by linarith only [hTd0 w ω, hTd1, hsη], hM1⟩
  -- the point source at the poles
  have hPSw : ∀ w ∈ K.supp, ldist w y ≤ t →
      l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) (t / 2) z w -
          clusterGaussNorm K σ (t / 2) w z) ≤
        E * (t / 2) ^ (3 * η - (d : ℝ) / 4 - 1 / 2) := by
    intro w hwK hwy
    obtain ⟨hXw, hYw, hTw, hTdw, hMw⟩ := hcomp w (by linarith only [hwy, ht0])
    refine hPS ω K hK w hwK (X w ω) (max (Y w ω) 1) (t / 2) (by linarith only [ht₁t])
      (le_max_right _ _)
      hXw hYw (hOZ h w) ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ z hz v hv τ hτ
      have hρ1 : 1 ≤ ρ := (le_max_right _ _).trans hρ
      have hvK := (WeakPoincare.mem_clusterBall.1 hv).1
      have hzK := (WeakPoincare.mem_clusterBall.1 hz).1
      have hvw := (WeakPoincare.mem_clusterBall.1 hv).2
      have hρρ : ρ ≤ ρ ^ 2 := by nlinarith only [hρ1]
      have hTv : TNA v ω ≤ ρ ^ 2 :=
        le_of_latticeSupD_le (hYb w) (((le_max_left _ _).trans hρ).trans hρρ)
          (by linarith only [hvw, hρρ])
      have hτ0 : 0 < τ := by nlinarith only [hτ, hρ1]
      exact (hB v h hvK τ hτ0 (hTv.trans hτ) z hzK).trans
        (dgPhiDim_le_rpow hCb hτ0 (WeakPoincare.latticeDist_nonneg _ _))
    · intro z hz r hr
      have hzK := (WeakPoincare.mem_clusterBall.1 hz).1
      have hzw := (WeakPoincare.mem_clusterBall.1 hz).2
      have hzy : ldist z y ≤ 2 * t + 1 := by
        have := WeakPoincare.latticeDist_triangle z w y
        linarith only [this, hzw, hwy, hsqrt]
      have hTz := (hcomp z hzy).2.2.1
      have hr0 : 0 < r := by linarith only [hr, ht0]
      exact (hB z h hzK r hr0 (by linarith only [hTz, hsq, hr]) z hzK).trans
        (dgPhiDim_le_rpow hCb hr0 (WeakPoincare.latticeDist_nonneg _ _))
    · intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le hsη hr
      exact (hB w h hwK r hr0 (hTw.trans hr) w hwK).trans
        (dgPhiDim_le_rpow hCb hr0 (WeakPoincare.latticeDist_nonneg _ _))
    · intro u hu _
      have hAw := hA w h u (by linarith only [hTdw, hu])
      rwa [show -(1 / 2 - η) = η - 1 / 2 by ring] at hAw
    · intro u hu _
      exact hM w h hwK u (hMw.trans hu)
  -- the pair
  have hD : ldist x y ≤ t := by rw [latticeDist_eq_norm_edzD]; exact hDt
  have hyy : ldist y y = 0 := Rigidity.WeakPoincare.latticeDist_self y
  obtain ⟨-, -, hTy, hTdy, -⟩ := hcomp y (by rw [hyy]; linarith only [ht0])
  obtain ⟨-, -, -, hTdx, -⟩ := hcomp x (by linarith only [hD, ht0])
  have hmid : ldist (midLattice x y) y ≤ 2 * t + 1 := by
    have := latticeDist_midLattice_le x y
    linarith only [this, hD, hdt]
  obtain ⟨-, -, -, hTdm, -⟩ := hcomp (midLattice x y) hmid
  have hexp : ∀ u : ℝ, u ^ (-(1 / 2 - η)) = u ^ (η - 1 / 2) := fun u => by
    rw [show -(1 / 2 - η) = η - 1 / 2 by ring]
  have hdiag : vsrwHeat (openGraph ω) (2 * d) (t / 2 + t / 2) y y ≤
      Cb * (t / 2) ^ (-((d : ℝ) / 2)) := by
    have hss : 0 < t / 2 + t / 2 := by positivity
    refine (hB y h hy (t / 2 + t / 2) hss (by linarith only [hTy, hsq, ht0]) y hy).trans
      ((dgPhiDim_le_rpow hCb hss (WeakPoincare.latticeDist_nonneg _ _)).trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs0 (by linarith only [hs0])
      (by
        have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
        linarith only [this])) hCb.le
  have hP := hPair ω K x y t ht₂t hD (hPSw x hx hD)
    (hPSw y hy (by rw [hyy]; linarith only [ht0])) hdiag
    (by rw [← hexp]; exact hA x h (t / 2) (by linarith only [hTdx, hsq, ht0]))
    (by rw [← hexp]; exact hA y h (t / 2) (by linarith only [hTdy, hsq, ht0]))
    (by rw [← hexp]; exact hA (midLattice x y) h (t / 2 / 2) (by linarith only [hTdm, hsq, ht0]))
    (hB y h hy t ht0 (by linarith only [hTy, hsq, ht0]) x hx)
  refine hP.trans ?_
  have hpow : t ^ (-((d : ℝ) / 2) - (1 / 2 - 6 * η)) ≤ t ^ (-((d : ℝ) / 2) - (1 / 2 - δ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [ht1]) (by linarith only [hηδ])
  calc K₀ * t ^ (-((d : ℝ) / 2) - (1 / 2 - 6 * η)) * Real.exp (-(‖edzD x y‖ ^ 2 / (K₀ * t)))
      ≤ K₀ * t ^ (-((d : ℝ) / 2) - (1 / 2 - δ)) * Real.exp (-(‖edzD x y‖ ^ 2 / (K₀ * t))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK₀.le) (Real.exp_pos _).le
    _ ≤ _ := mul_rpow_mul_exp_le hK₀ (le_max_right _ _) ht0

end Rigidity.Green

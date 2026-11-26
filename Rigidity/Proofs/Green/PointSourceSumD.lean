import Rigidity.Proofs.Green.PointSourceTermD
import Rigidity.Proofs.Green.PointSourceArith

/-!
# From smooth initial data to a point source at one configuration

With geometric times `s_{j+1} = 3 s_j`, `s_0 ≥ 1`, `t = s_J`, radii `l_j = √(s_j) L` (`L ≥ 2`,
`4L² s_0 ≤ t`), the diagonal bound `p_r(z, z) ≤ C_B t^{-d/2}` on `V_{√t}(y)` for `r ∈ [t/4, 2t]`,
the order-zero estimate and the exit-time bound at the pole above the scale `l_0`, and

* `‖D_{s_j}‖ ≤ C_N s_j^{η - d/4 - 1/2}` and `Σ_{x ∉ V_{l_j}(y)} |D_{s_j}(x)| ≤ T₀` for `j < J`,
* `‖E‖ ≤ C_E s_0^{-d/4}` and `Σ_{x ∉ V_{l_0}(y)} |E(x)| ≤ T₀` for `E = p_{s_0}(·, y) - G_{s_0}`,

the telescoping identity gives (`l2norm_pointSource_le`)

  `‖p_t(·, y) - G_t‖ ≤ Q_E + J Q`,
  `Q = 5^{d/2} κ √C_B C_N L^{d/2+1} t^{η-d/4-1/2} + C_N (4L²)^{d/4+1/2} t^{η-d/4-1/2}`
    `+ (2 + κ√C_B) T₀`,
  `Q_E = 5^{d/2} κ √C_B C_E L^{d/2+1} s_0^{1/2} t^{-d/4-1/2} + (2 + κ√C_B) T₀`.

The terms with `4L² s_j ≤ t` are paired with the time slices (`l2norm_heatFlowG_le_of_scale`), the
others are bounded by contraction (`caseB_le`).
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.WeakPoincare

namespace Rigidity.Green

variable {d : ℕ} [NeZero d] {ω : Configuration d}

omit [NeZero d] in
theorem term_factor_le {t l κ CB : ℝ} (ht : 1 ≤ t) (hl : 0 ≤ l) (hlt : 2 * l ≤ Real.sqrt t)
    (hκ : 0 ≤ κ) (hCB : 0 ≤ CB) :
    κ * l * Real.sqrt (CB * t ^ (-((d : ℝ) / 2))) / Real.sqrt t ≤ κ * Real.sqrt CB := by
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hp : t ^ (-((d : ℝ) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (by
      have : (0 : ℝ) ≤ d / 2 := by positivity
      linarith)
  have h1 : Real.sqrt (CB * t ^ (-((d : ℝ) / 2))) ≤ Real.sqrt CB :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right hCB hp)
  have h2 : l / Real.sqrt t ≤ 1 / 2 := by
    rw [div_le_iff₀ hst]; linarith
  calc κ * l * Real.sqrt (CB * t ^ (-((d : ℝ) / 2))) / Real.sqrt t
      = κ * Real.sqrt (CB * t ^ (-((d : ℝ) / 2))) * (l / Real.sqrt t) := by ring
    _ ≤ κ * Real.sqrt CB * (1 / 2) := by gcongr
    _ ≤ κ * Real.sqrt CB := by
        have : 0 ≤ κ * Real.sqrt CB := by positivity
        linarith

omit [NeZero d] in
/-- `2 √u L ≤ √t` from `4 L² u ≤ t`. -/
theorem two_mul_sqrt_le {u t L : ℝ} (hL0 : 0 ≤ L) (hut : 4 * L ^ 2 * u ≤ t) :
    2 * (Real.sqrt u * L) ≤ Real.sqrt t := by
  rcases le_or_gt 0 u with hu | hu
  · rw [show 2 * (Real.sqrt u * L) = Real.sqrt (4 * L ^ 2 * u) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hL0,
        show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      ring]
    exact Real.sqrt_le_sqrt hut
  · rw [Real.sqrt_eq_zero'.2 hu.le]
    simp [Real.sqrt_nonneg]

/-- The initial error term. -/
theorem pointSource_initial_le {K : OpenComponent ω} {y : Vertex d} (hy : y ∈ K.supp)
    (hacc : ∀ ρ, LatticeProb.Network.BoundaryAccessible (openGraph ω)
      (interiorOf (openGraph ω) (clusterBall K y ρ)))
    {X C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hOZ : ∀ R', 2 * X ≤ R' → ∀ u : Vertex d → ℝ,
      (∀ x ∈ interiorOf (openGraph ω) (clusterBall K y R'),
        LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
      ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
        nL2 (clusterBall K y r) (fun x => u x - c) ≤ C₀ * (r / R') * nL2 (clusterBall K y R') u)
    {A ρ₀ : ℝ} (hA : 0 ≤ A)
    (hHK : ∀ ρ, ρ₀ ≤ ρ → ∀ z ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) (2 * d) (A * ρ ^ 2) z w ≤ 1 / 2)
    {σ : ℝ} (hσ : 0 < σ) {u t L : ℝ} (hu : 1 ≤ u) (hL : 2 ≤ L) (hXl : X ≤ Real.sqrt u * L)
    (hρ₀ : ρ₀ ≤ 2 * (Real.sqrt u * L)) (hut : 4 * L ^ 2 * u ≤ t)
    {CB CE T₀ : ℝ} (hCB : 0 ≤ CB) (hT₀ : 0 ≤ T₀)
    (hdiag : ∀ z ∈ clusterBall K y (Real.sqrt t), ∀ r, t / 4 ≤ r → r ≤ 2 * t →
      vsrwHeat (openGraph ω) (2 * d) r z z ≤ CB * t ^ (-((d : ℝ) / 2)))
    (hM : 0 < clusterGaussMass K σ u y)
    (hNE : l2norm (fun x => vsrwHeat (openGraph ω) (2 * d) u x y -
      clusterGaussNorm K σ u y x) ≤ CE * u ^ (-((d : ℝ) / 4)))
    (hTE : ∑' x, (if x ∈ clusterBall K y (Real.sqrt u * L) then 0 else
      |vsrwHeat (openGraph ω) (2 * d) u x y - clusterGaussNorm K σ u y x|) ≤ T₀) :
    l2norm (heatFlowG (openGraph ω) (2 * d) (t - u)
        (fun w => vsrwHeat (openGraph ω) (2 * d) u w y - clusterGaussNorm K σ u y w)) ≤
      5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) * Real.sqrt CB * CE *
          L ^ ((d : ℝ) / 2 + 1) * u ^ ((1 : ℝ) / 2) * t ^ (-((d : ℝ) / 4) - 1 / 2) +
        (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * Real.sqrt CB) * T₀ := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  set κ := (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 < u := by linarith
  have hL4 : 4 ≤ L ^ 2 := by nlinarith
  have h16 : 16 * u ≤ t := by nlinarith [mul_le_mul_of_nonneg_right hL4 hu0.le]
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hl1 : 1 ≤ Real.sqrt u * L := by
    have : 1 ≤ Real.sqrt u := Real.one_le_sqrt.2 hu
    nlinarith
  have hlt : 2 * (Real.sqrt u * L) ≤ Real.sqrt t := two_mul_sqrt_le hL0 hut
  have hE1 := summable_abs_initialError (K := K) (y := y) hσ hu0
  have hE2 : Summable fun x => (vsrwHeat (openGraph ω) (2 * d) u x y -
      clusterGaussNorm K σ u y x) ^ 2 :=
    summable_sq_sub_l2 (summable_sq_vsrwHeat_col hD hdeg hu0.le y)
      (summable_sq_clusterGaussNorm hσ hu0)
  have hE0 := tsum_initialError (K := K) (y := y) hσ hu0 hM.ne'
  have hb := l2norm_heatFlowG_le_of_scale hy hacc hC₀ hOZ hA hHK ht0
    (σ := t - u) (by linarith) (by linarith) hE1 hE2 hE0 hXl hl1 hρ₀ hlt
    (by positivity) hdiag hNE hTE
  refine hb.trans (add_le_add ?_ ?_)
  · rw [← hκ, caseE_eq hu0 ht0 hL0 hCB d]
  · exact mul_le_mul_of_nonneg_right (add_le_add le_rfl
      (term_factor_le ht1 (by linarith) hlt hκ0 hCB)) hT₀

/-- One difference term. -/
theorem pointSource_term_le {K : OpenComponent ω} {y : Vertex d} (hy : y ∈ K.supp)
    (hacc : ∀ ρ, LatticeProb.Network.BoundaryAccessible (openGraph ω)
      (interiorOf (openGraph ω) (clusterBall K y ρ)))
    {X C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hOZ : ∀ R', 2 * X ≤ R' → ∀ u : Vertex d → ℝ,
      (∀ x ∈ interiorOf (openGraph ω) (clusterBall K y R'),
        LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
      ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
        nL2 (clusterBall K y r) (fun x => u x - c) ≤ C₀ * (r / R') * nL2 (clusterBall K y R') u)
    {A ρ₀ : ℝ} (hA : 0 ≤ A)
    (hHK : ∀ ρ, ρ₀ ≤ ρ → ∀ z ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) (2 * d) (A * ρ ^ 2) z w ≤ 1 / 2)
    {σ η : ℝ} (hσ : 0 < σ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    {u t L : ℝ} (hu : 1 ≤ u) (hut : 3 * u ≤ t) (hL : 2 ≤ L) (hXl : X ≤ Real.sqrt u * L)
    (hρ₀ : ρ₀ ≤ 2 * (Real.sqrt u * L))
    {CB CN T₀ : ℝ} (hCB : 0 ≤ CB) (hCN : 0 ≤ CN) (hT₀ : 0 ≤ T₀)
    (hdiag : ∀ z ∈ clusterBall K y (Real.sqrt t), ∀ r, t / 4 ≤ r → r ≤ 2 * t →
      vsrwHeat (openGraph ω) (2 * d) r z z ≤ CB * t ^ (-((d : ℝ) / 2)))
    (hM1 : 0 < clusterGaussMass K σ u y) (hM3 : 0 < clusterGaussMass K σ (3 * u) y)
    (hN : l2norm (gaussFlowDiff K σ u y) ≤ CN * u ^ (η - (d : ℝ) / 4 - 1 / 2))
    (hT : ∑' x, (if x ∈ clusterBall K y (Real.sqrt u * L) then 0 else
      |gaussFlowDiff K σ u y x|) ≤ T₀) :
    l2norm (heatFlowG (openGraph ω) (2 * d) (t - 3 * u) (gaussFlowDiff K σ u y)) ≤
      5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) * Real.sqrt CB *
          CN * L ^ ((d : ℝ) / 2 + 1) * t ^ (η - (d : ℝ) / 4 - 1 / 2) +
        CN * (4 * L ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2) +
        (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * Real.sqrt CB) * T₀ := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  set κ := (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hu0 : 0 < u := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hD1 := summable_abs_gaussFlowDiff (K := K) (y := y) hσ hu0
  have hD2 := summable_sq_gaussFlowDiff (K := K) (y := y) hσ hu0
  have hD0 := tsum_gaussFlowDiff (K := K) (y := y) hσ hu0 hM1.ne' hM3.ne'
  have hQ1 : 0 ≤ 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN * L ^ ((d : ℝ) / 2 + 1) *
      t ^ (η - (d : ℝ) / 4 - 1 / 2) := by positivity
  have hQ2 : 0 ≤ CN * (4 * L ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2) := by
    positivity
  have hQ3 : 0 ≤ (2 + κ * Real.sqrt CB) * T₀ := by positivity
  by_cases hcase : 4 * L ^ 2 * u ≤ t
  · have hL4 : 4 ≤ L ^ 2 := by nlinarith
    have h16 : 16 * u ≤ t := by nlinarith [mul_le_mul_of_nonneg_right hL4 hu0.le]
    have hl1 : 1 ≤ Real.sqrt u * L := by
      have : 1 ≤ Real.sqrt u := Real.one_le_sqrt.2 hu
      nlinarith
    have hlt : 2 * (Real.sqrt u * L) ≤ Real.sqrt t := two_mul_sqrt_le hL0 hcase
    have hb := l2norm_heatFlowG_le_of_scale hy hacc hC₀ hOZ hA hHK ht0
      (σ := t - 3 * u) (by linarith) (by linarith) hD1 hD2 hD0 hXl hl1 hρ₀ hlt
      (by positivity) hdiag hN hT
    refine hb.trans ?_
    have hA1 := caseA_le (t := t) hu0 (by linarith) hL0 hCB hκ0 hCN hη0 d
    have hA2 : (2 + κ * (Real.sqrt u * L) * Real.sqrt (CB * t ^ (-((d : ℝ) / 2))) /
        Real.sqrt t) * T₀ ≤ (2 + κ * Real.sqrt CB) * T₀ :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl
        (term_factor_le ht1 (by linarith) hlt hκ0 hCB)) hT₀
    rw [← hκ]
    linarith
  · push Not at hcase
    have hb := l2norm_heatFlowG_le hD hdeg (by linarith : 0 ≤ t - 3 * u) hD2
    have hB := caseB_le ht0 hL1 hCN hη0 hη d (s := u)
      (by rw [div_le_iff₀ (by positivity)]; linarith)
    linarith

/-- **From smooth initial data to a point source**, at one configuration. -/
theorem l2norm_pointSource_le {K : OpenComponent ω} {y : Vertex d} (hy : y ∈ K.supp)
    (hacc : ∀ ρ, LatticeProb.Network.BoundaryAccessible (openGraph ω)
      (interiorOf (openGraph ω) (clusterBall K y ρ)))
    {X C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hOZ : ∀ R', 2 * X ≤ R' → ∀ u : Vertex d → ℝ,
      (∀ x ∈ interiorOf (openGraph ω) (clusterBall K y R'),
        LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
      ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
        nL2 (clusterBall K y r) (fun x => u x - c) ≤ C₀ * (r / R') * nL2 (clusterBall K y R') u)
    {A ρ₀ : ℝ} (hA : 0 ≤ A)
    (hHK : ∀ ρ, ρ₀ ≤ ρ → ∀ z ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) (2 * d) (A * ρ ^ 2) z w ≤ 1 / 2)
    {σ η : ℝ} (hσ : 0 < σ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    {s : ℕ → ℝ} (hs1 : 1 ≤ s 0) (hs : ∀ j, s (j + 1) = 3 * s j) (J : ℕ)
    {L : ℝ} (hL : 2 ≤ L) (hXl : X ≤ Real.sqrt (s 0) * L)
    (hρ₀ : ρ₀ ≤ 2 * (Real.sqrt (s 0) * L)) (hs0t : 4 * L ^ 2 * s 0 ≤ s J)
    {CB CN CE T₀ : ℝ} (hCB : 0 ≤ CB) (hCN : 0 ≤ CN) (hT₀ : 0 ≤ T₀)
    (hdiag : ∀ z ∈ clusterBall K y (Real.sqrt (s J)), ∀ r, s J / 4 ≤ r → r ≤ 2 * s J →
      vsrwHeat (openGraph ω) (2 * d) r z z ≤ CB * s J ^ (-((d : ℝ) / 2)))
    (hM : ∀ j, j ≤ J → 0 < clusterGaussMass K σ (s j) y)
    (hN : ∀ j < J, l2norm (gaussFlowDiff K σ (s j) y) ≤ CN * s j ^ (η - (d : ℝ) / 4 - 1 / 2))
    (hT : ∀ j < J, ∑' x, (if x ∈ clusterBall K y (Real.sqrt (s j) * L) then 0 else
      |gaussFlowDiff K σ (s j) y x|) ≤ T₀)
    (hNE : l2norm (fun x => vsrwHeat (openGraph ω) (2 * d) (s 0) x y -
      clusterGaussNorm K σ (s 0) y x) ≤ CE * s 0 ^ (-((d : ℝ) / 4)))
    (hTE : ∑' x, (if x ∈ clusterBall K y (Real.sqrt (s 0) * L) then 0 else
      |vsrwHeat (openGraph ω) (2 * d) (s 0) x y - clusterGaussNorm K σ (s 0) y x|) ≤ T₀) :
    l2norm (fun x => vsrwHeat (openGraph ω) (2 * d) (s J) x y - clusterGaussNorm K σ (s J) y x) ≤
      (5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) * Real.sqrt CB * CE *
          L ^ ((d : ℝ) / 2 + 1) * s 0 ^ ((1 : ℝ) / 2) * s J ^ (-((d : ℝ) / 4) - 1 / 2) +
        (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * Real.sqrt CB) * T₀) +
      J * (5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) * Real.sqrt CB *
          CN * L ^ ((d : ℝ) / 2 + 1) * s J ^ (η - (d : ℝ) / 4 - 1 / 2) +
        CN * (4 * L ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) * s J ^ (η - (d : ℝ) / 4 - 1 / 2) +
        (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * Real.sqrt CB) * T₀) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have hsnn : ∀ j, 1 ≤ s j := by
    intro j
    induction j with
    | zero => exact hs1
    | succ j ih => rw [hs j]; linarith
  have hmono : ∀ i j, i ≤ j → s i ≤ s j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | @step m _ ih => exact ih.trans (by rw [hs m]; linarith [hsnn m])
  have hL0 : 0 ≤ L := by linarith
  have hsqrt_mono : ∀ j, Real.sqrt (s 0) * L ≤ Real.sqrt (s j) * L := fun j =>
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hmono 0 j (Nat.zero_le j))) hL0
  have hF : ∀ j, Summable fun x => clusterGaussNorm K σ (s j) y x ^ 2 := fun j =>
    summable_sq_clusterGaussNorm hσ (by linarith [hsnn j])
  have htel := l2norm_vsrwHeat_sub_le (G := openGraph ω) hD hdeg
    (F := fun j => clusterGaussNorm K σ (s j) y) hF (by linarith) hs J y (hmono 0 J (Nat.zero_le J))
  refine htel.trans (add_le_add ?_ ?_)
  · exact pointSource_initial_le hy hacc hC₀ hOZ hA hHK hσ hs1 hL hXl hρ₀ hs0t hCB hT₀ hdiag
      (hM 0 (Nat.zero_le J)) hNE hTE
  · have hterm : ∀ j ∈ Finset.range J, l2norm (heatFlowG (openGraph ω) (2 * d) (s J - s (j + 1))
        (fun w => heatFlowG (openGraph ω) (2 * d) (2 * s j)
          (clusterGaussNorm K σ (s j) y) w - clusterGaussNorm K σ (s (j + 1)) y w)) ≤
        5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) * Real.sqrt CB *
          CN * L ^ ((d : ℝ) / 2 + 1) * s J ^ (η - (d : ℝ) / 4 - 1 / 2) +
        CN * (4 * L ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) * s J ^ (η - (d : ℝ) / 4 - 1 / 2) +
        (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * Real.sqrt CB) * T₀ := by
      intro j hj
      have hjJ : j < J := Finset.mem_range.1 hj
      have heq : (fun w => heatFlowG (openGraph ω) (2 * d) (2 * s j)
          (clusterGaussNorm K σ (s j) y) w - clusterGaussNorm K σ (s (j + 1)) y w) =
          gaussFlowDiff K σ (s j) y := by
        funext w; rw [hs j]; rfl
      rw [heq, hs j]
      have hs1J : s (j + 1) ≤ s J := hmono (j + 1) J hjJ
      rw [hs j] at hs1J
      have hM3 : 0 < clusterGaussMass K σ (3 * s j) y := by rw [← hs j]; exact hM (j + 1) hjJ
      exact pointSource_term_le hy hacc hC₀ hOZ hA hHK hσ hη0 hη (hsnn j) hs1J hL
        (hXl.trans (hsqrt_mono j)) (hρ₀.trans (by linarith [hsqrt_mono j])) hCB hCN hT₀ hdiag
        (hM j hjJ.le) hM3 (hN j hjJ) (hT j hjJ)
    calc _ ≤ ∑ j ∈ Finset.range J, _ := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Rigidity.Green

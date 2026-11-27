import Rigidity.Proofs.Green.LatticeGaussianD
import Rigidity.Proofs.Green.HeatFlowPairingD

/-!
# The Gaussian kernel on the cluster, normalized to mass one

For an open component `K` of a configuration of `ℤ^d`, a pole `y` and `s > 0`, let
`b_s(z) = p̄(s, z - y) 1_{z ∈ K}` (`clusterInd`), `M_s = Σ_z b_s(z)` (`clusterGaussMass`, the sum of
Proposition A.7 of Dario–Gu), `H_s = θ^{-1} b_s` and `G_s = b_s / M_s` (`clusterGaussNorm`). Then

* `‖b_s‖² ≤ (2πσs)^{-d/2} M_s` (`sq_l2norm_clusterInd_le`);
* `Σ G_s = 1` (`tsum_clusterGaussNorm`) and `‖G_s - H_s‖ = |M_s^{-1} - θ^{-1}| ‖b_s‖`
  (`l2norm_clusterGaussNorm_sub`);
* `D_s = P_{2s} G_s - G_{3s}` has mass zero (`tsum_gaussFlowDiff`) and
  `‖D_s‖ ≤ ‖G_s - H_s‖ + ‖P_{2s} H_s - H_{3s}‖ + ‖H_{3s} - G_{3s}‖` (`l2norm_gaussFlowDiff_le`);
* the initial error `E = p_{s}(·, y) - G_s` has mass zero (`tsum_initialError`).

These are the differences `D_s` of the passage from smooth initial data to a point source in the
proof of Theorem 1 of Dario–Gu given here; `‖P_{2s} H_s - H_{3s}‖` is the whole-cluster estimate
(4.40) of Dario–Gu with the initial error of Proposition 2.12.
-/

open scoped Classical
open LatticeProb.Percolation

namespace Rigidity.Green

section Generic

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

/-- `P_t` is a contraction of `ℓ²`. -/
theorem l2norm_heatFlowG_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun x => f x ^ 2) :
    l2norm (heatFlowG G D t f) ≤ l2norm f :=
  Real.sqrt_le_sqrt (hasSum_sq_heatFlowG_le hD hdeg ht hf).2

theorem l2norm_const_mul (c : ℝ) (f : V → ℝ) :
    l2norm (fun x => c * f x) = |c| * l2norm f := by
  unfold l2norm
  simp_rw [mul_pow]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- `P_t f` is summable for summable `f`. -/
theorem summable_heatFlowG (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf1 : Summable fun w => |f w|) : Summable (heatFlowG G D t f) := by
  have hdom : Summable (Function.uncurry fun x w => vsrwHeat G D t x w * |f w|) :=
    summable_uncurry_of_nonneg' (fun x w => mul_nonneg (vsrwHeat_nonneg hD hdeg ht x w)
      (abs_nonneg _))
      (fun w => by
        have h := ((hasSum_vsrwHeat hD hdeg ht w).summable).mul_right |f w|
        refine h.congr fun x => ?_
        rw [vsrwHeat_symm hD hdeg t w x])
      (by
        refine hf1.congr fun w => ?_
        rw [tsum_mul_right]
        have h := hasSum_vsrwHeat hD hdeg ht w
        rw [show (∑' x, vsrwHeat G D t x w) = ∑' x, vsrwHeat G D t w x from
          tsum_congr fun x => vsrwHeat_symm hD hdeg t x w, h.tsum_eq, one_mul])
  have hs : Summable (Function.uncurry fun x w => vsrwHeat G D t x w * f w) :=
    hdom.of_norm_bounded fun q => by
      rw [Real.norm_eq_abs]
      show |vsrwHeat G D t q.1 q.2 * f q.2| ≤ vsrwHeat G D t q.1 q.2 * |f q.2|
      rw [abs_mul, abs_of_nonneg (vsrwHeat_nonneg hD hdeg ht q.1 q.2)]
  exact hs.prod

end Generic

variable {d : ℕ} {ω : Configuration d}

/-- `b_s(z) = p̄(s, z - y) 1_{z ∈ K}`. -/
noncomputable def clusterInd (K : OpenComponent ω) (σ s : ℝ) (y z : Vertex d) : ℝ :=
  if z ∈ K.supp then gaussianHeatD d σ s (edzD z y) else 0

/-- `M_s(y) = Σ_{z ∈ K} p̄(s, z - y)`, the Gaussian mass of the component (Dario–Gu, Proposition
A.7). -/
noncomputable def clusterGaussMass (K : OpenComponent ω) (σ s : ℝ) (y : Vertex d) : ℝ :=
  ∑' z, clusterInd K σ s y z

/-- `G_s = b_s / M_s`. -/
noncomputable def clusterGaussNorm (K : OpenComponent ω) (σ s : ℝ) (y z : Vertex d) : ℝ :=
  clusterInd K σ s y z / clusterGaussMass K σ s y

section Basic

variable {K : OpenComponent ω} {σ s : ℝ} {y : Vertex d}

theorem clusterInd_nonneg (hσ : 0 < σ) (hs : 0 < s) (z : Vertex d) : 0 ≤ clusterInd K σ s y z := by
  unfold clusterInd
  split_ifs
  · exact gaussianHeatD_nonneg' σ s (by positivity) _
  · exact le_rfl

theorem clusterInd_le (hσ : 0 < σ) (hs : 0 < s) (z : Vertex d) :
    clusterInd K σ s y z ≤ gaussianHeatD d σ s (edzD z y) := by
  unfold clusterInd
  split_ifs
  · exact le_rfl
  · exact gaussianHeatD_nonneg' σ s (by positivity) _

theorem gaussianHeatD_le_sup (hσ : 0 < σ) (hs : 0 < s) (z : EuclideanSpace ℝ (Fin d)) :
    gaussianHeatD d σ s z ≤ (2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)) := by
  unfold gaussianHeatD
  refine mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) ?_
  rw [Real.exp_le_one_iff, neg_nonpos]
  positivity

theorem summable_clusterInd (hσ : 0 < σ) (hs : 0 < s) : Summable (clusterInd K σ s y) :=
  (summable_gaussianHeatD (d := d) hσ hs y).of_nonneg_of_le (clusterInd_nonneg hσ hs)
    (clusterInd_le hσ hs)

theorem summable_abs_clusterInd (hσ : 0 < σ) (hs : 0 < s) :
    Summable fun z => |clusterInd K σ s y z| :=
  (summable_clusterInd hσ hs).congr fun z => (abs_of_nonneg (clusterInd_nonneg hσ hs z)).symm

theorem sq_clusterInd_le (hσ : 0 < σ) (hs : 0 < s) (z : Vertex d) :
    clusterInd K σ s y z ^ 2 ≤ (2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)) * clusterInd K σ s y z := by
  rw [sq]
  exact mul_le_mul_of_nonneg_right ((clusterInd_le hσ hs z).trans (gaussianHeatD_le_sup hσ hs _))
    (clusterInd_nonneg hσ hs z)

theorem summable_sq_clusterInd (hσ : 0 < σ) (hs : 0 < s) :
    Summable fun z => clusterInd K σ s y z ^ 2 :=
  ((summable_clusterInd hσ hs).mul_left _).of_nonneg_of_le (fun _ => sq_nonneg _)
    (sq_clusterInd_le hσ hs)

/-- `‖b_s‖² ≤ (2πσs)^{-d/2} M_s`. -/
theorem sq_l2norm_clusterInd_le (hσ : 0 < σ) (hs : 0 < s) :
    l2norm (clusterInd K σ s y) ^ 2 ≤
      (2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)) * clusterGaussMass K σ s y := by
  rw [sq_l2norm, clusterGaussMass, ← tsum_mul_left]
  exact (summable_sq_clusterInd hσ hs).tsum_le_tsum (sq_clusterInd_le hσ hs)
    ((summable_clusterInd hσ hs).mul_left _)

theorem clusterGaussMass_nonneg (hσ : 0 < σ) (hs : 0 < s) : 0 ≤ clusterGaussMass K σ s y :=
  tsum_nonneg (clusterInd_nonneg hσ hs)

theorem summable_clusterGaussNorm (hσ : 0 < σ) (hs : 0 < s) :
    Summable (clusterGaussNorm K σ s y) :=
  (summable_clusterInd hσ hs).div_const _

theorem summable_abs_clusterGaussNorm (hσ : 0 < σ) (hs : 0 < s) :
    Summable fun z => |clusterGaussNorm K σ s y z| :=
  (summable_clusterGaussNorm hσ hs).congr fun z => (abs_of_nonneg
    (div_nonneg (clusterInd_nonneg hσ hs z) (clusterGaussMass_nonneg hσ hs))).symm

theorem summable_sq_clusterGaussNorm (hσ : 0 < σ) (hs : 0 < s) :
    Summable fun z => clusterGaussNorm K σ s y z ^ 2 := by
  unfold clusterGaussNorm
  simp_rw [div_pow]
  exact (summable_sq_clusterInd hσ hs).div_const _

/-- `Σ G_s = 1`. -/
theorem tsum_clusterGaussNorm (hM : clusterGaussMass K σ s y ≠ 0) :
    ∑' z, clusterGaussNorm K σ s y z = 1 := by
  unfold clusterGaussNorm
  rw [tsum_div_const, ← clusterGaussMass, div_self hM]

/-- `‖G_s - θ^{-1} b_s‖ = |M_s^{-1} - θ^{-1}| ‖b_s‖`. -/
theorem l2norm_clusterGaussNorm_sub (θ : ℝ) :
    l2norm (fun z => clusterGaussNorm K σ s y z - θ⁻¹ * clusterInd K σ s y z) =
      |(clusterGaussMass K σ s y)⁻¹ - θ⁻¹| * l2norm (clusterInd K σ s y) := by
  rw [← l2norm_const_mul]
  congr 1
  funext z
  unfold clusterGaussNorm
  ring

end Basic

section Flow

variable {K : OpenComponent ω} {σ : ℝ} {y : Vertex d}

/-- `D_s = P_{2s} G_s - G_{3s}`. -/
noncomputable def gaussFlowDiff (K : OpenComponent ω) (σ s : ℝ) (y x : Vertex d) : ℝ :=
  heatFlowG (openGraph ω) (2 * d) (2 * s) (clusterGaussNorm K σ s y) x -
    clusterGaussNorm K σ (3 * s) y x

variable [NeZero d]

theorem two_mul_pos_d : 0 < 2 * d := by have := NeZero.pos d; omega

theorem summable_abs_gaussFlowDiff (hσ : 0 < σ) {s : ℝ} (hs : 0 < s) :
    Summable fun x => |gaussFlowDiff K σ s y x| := by
  have h1 := summable_heatFlowG (G := openGraph ω) two_mul_pos_d (openGraph_degree_le ω)
    (by linarith : (0 : ℝ) ≤ 2 * s) (summable_abs_clusterGaussNorm (K := K) (y := y) hσ hs)
  have h2 := summable_clusterGaussNorm (K := K) (y := y) hσ (by linarith : (0 : ℝ) < 3 * s)
  exact (h1.sub h2).abs

theorem summable_sq_gaussFlowDiff (hσ : 0 < σ) {s : ℝ} (hs : 0 < s) :
    Summable fun x => gaussFlowDiff K σ s y x ^ 2 :=
  summable_sq_sub_l2 (summable_sq_heatFlowG two_mul_pos_d (openGraph_degree_le ω)
    (by linarith : (0 : ℝ) ≤ 2 * s) (summable_sq_clusterGaussNorm hσ hs))
    (summable_sq_clusterGaussNorm hσ (by linarith : (0 : ℝ) < 3 * s))

/-- `D_s` has mass zero. -/
theorem tsum_gaussFlowDiff (hσ : 0 < σ) {s : ℝ} (hs : 0 < s)
    (hM1 : clusterGaussMass K σ s y ≠ 0) (hM3 : clusterGaussMass K σ (3 * s) y ≠ 0) :
    ∑' x, gaussFlowDiff K σ s y x = 0 := by
  unfold gaussFlowDiff
  have h1 := summable_heatFlowG (G := openGraph ω) two_mul_pos_d (openGraph_degree_le ω)
    (by linarith : (0 : ℝ) ≤ 2 * s) (summable_abs_clusterGaussNorm (K := K) (y := y) hσ hs)
  have h2 := summable_clusterGaussNorm (K := K) (y := y) hσ (by linarith : (0 : ℝ) < 3 * s)
  rw [h1.tsum_sub h2, tsum_heatFlowG_eq two_mul_pos_d (openGraph_degree_le ω)
    (by linarith : (0 : ℝ) ≤ 2 * s) (summable_abs_clusterGaussNorm hσ hs),
    tsum_clusterGaussNorm hM1, tsum_clusterGaussNorm hM3, sub_self]

/-- `‖D_s‖ ≤ ‖G_s - H_s‖ + ‖P_{2s} H_s - H_{3s}‖ + ‖H_{3s} - G_{3s}‖` with `H = θ^{-1} b`. -/
theorem l2norm_gaussFlowDiff_le (hσ : 0 < σ) {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    l2norm (gaussFlowDiff K σ s y) ≤
      l2norm (fun z => clusterGaussNorm K σ s y z - θ⁻¹ * clusterInd K σ s y z) +
      l2norm (fun x => heatFlowG (openGraph ω) (2 * d) (2 * s)
        (fun z => θ⁻¹ * clusterInd K σ s y z) x - θ⁻¹ * clusterInd K σ (3 * s) y x) +
      l2norm (fun z => clusterGaussNorm K σ (3 * s) y z -
        θ⁻¹ * clusterInd K σ (3 * s) y z) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have h2s : (0 : ℝ) ≤ 2 * s := by linarith
  have h3s : (0 : ℝ) < 3 * s := by linarith
  set G1 := clusterGaussNorm K σ s y
  set G3 := clusterGaussNorm K σ (3 * s) y
  set H1 : Vertex d → ℝ := fun z => θ⁻¹ * clusterInd K σ s y z
  set H3 : Vertex d → ℝ := fun z => θ⁻¹ * clusterInd K σ (3 * s) y z
  have hG1 : Summable fun z => G1 z ^ 2 := summable_sq_clusterGaussNorm hσ hs
  have hG3 : Summable fun z => G3 z ^ 2 := summable_sq_clusterGaussNorm hσ h3s
  have hH1 : Summable fun z => H1 z ^ 2 := by
    simp_rw [H1, mul_pow]; exact (summable_sq_clusterInd hσ hs).mul_left _
  have hH3 : Summable fun z => H3 z ^ 2 := by
    simp_rw [H3, mul_pow]; exact (summable_sq_clusterInd hσ h3s).mul_left _
  have hA : Summable fun z => (G1 z - H1 z) ^ 2 := summable_sq_sub_l2 hG1 hH1
  have hB : Summable fun x => (heatFlowG (openGraph ω) (2 * d) (2 * s) H1 x - H3 x) ^ 2 :=
    summable_sq_sub_l2 (summable_sq_heatFlowG hD hdeg h2s hH1) hH3
  have hC : Summable fun z => (H3 z - G3 z) ^ 2 := summable_sq_sub_l2 hH3 hG3
  have hPA : Summable fun x => heatFlowG (openGraph ω) (2 * d) (2 * s)
      (fun z => G1 z - H1 z) x ^ 2 := summable_sq_heatFlowG hD hdeg h2s hA
  have heq : gaussFlowDiff K σ s y = fun x =>
      (heatFlowG (openGraph ω) (2 * d) (2 * s) (fun z => G1 z - H1 z) x +
        (heatFlowG (openGraph ω) (2 * d) (2 * s) H1 x - H3 x)) + (H3 x - G3 x) := by
    funext x
    unfold gaussFlowDiff
    rw [heatFlowG_sub hD hdeg h2s hG1 hH1]
    ring
  obtain ⟨hAB, h1⟩ := l2norm_add_le hPA hB
  obtain ⟨-, h2⟩ := l2norm_add_le hAB hC
  have h3 := l2norm_heatFlowG_le hD hdeg h2s hA
  have h4 : l2norm (fun z => H3 z - G3 z) = l2norm (fun z => G3 z - H3 z) := by
    unfold l2norm
    congr 1
    exact tsum_congr fun z => by ring
  rw [heq]
  calc _ ≤ _ := h2
    _ ≤ _ := add_le_add h1 le_rfl
    _ ≤ _ := by rw [h4]; linarith

/-- The initial error `E = p_s(·, y) - G_s` has mass zero. -/
theorem tsum_initialError (hσ : 0 < σ) {s : ℝ} (hs : 0 < s)
    (hM : clusterGaussMass K σ s y ≠ 0) :
    ∑' x, (vsrwHeat (openGraph ω) (2 * d) s x y - clusterGaussNorm K σ s y x) = 0 := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have hp : HasSum (fun x => vsrwHeat (openGraph ω) (2 * d) s x y) 1 :=
    (hasSum_vsrwHeat hD hdeg hs.le y).congr_fun fun x => vsrwHeat_symm hD hdeg s x y
  rw [hp.summable.tsum_sub (summable_clusterGaussNorm hσ hs), hp.tsum_eq,
    tsum_clusterGaussNorm hM, sub_self]

theorem summable_abs_initialError (hσ : 0 < σ) {s : ℝ} (hs : 0 < s) :
    Summable fun x => |vsrwHeat (openGraph ω) (2 * d) s x y - clusterGaussNorm K σ s y x| := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have hp : Summable fun x => vsrwHeat (openGraph ω) (2 * d) s x y :=
    ((hasSum_vsrwHeat hD hdeg hs.le y).congr_fun fun x => vsrwHeat_symm hD hdeg s x y).summable
  exact (hp.sub (summable_clusterGaussNorm hσ hs)).abs

end Flow

end Rigidity.Green

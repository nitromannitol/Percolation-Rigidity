import Rigidity.Proofs.Green.GeneralTwoScaleCluster

/-!
# The dyadic cutoffs of Step 3 of Proposition 4.3 of Dario–Gu on `ℤ^d`

Step 3 of the proof of Proposition 4.3 of Dario–Gu (lines 2356-2376 of the source) uses the
cutoffs `η_m` with `|∇η_m| ≤ (2^m √t)^{-1}`, `η_m = 1` on `B_{2^m √t}(y)` and `supp η_m ⊂
B_{2^{m+1} √t}(y)`, and the partition of unity `1 = Σ_m (η_m - η_{m-1})`; each piece is estimated
separately ((4.37)). On `ℤ^d` (the planar `DarioGuTwoScaleCutoff`, `DarioGuTwoScaleFluxSum` with
the Euclidean distance `|x - y|` of `ℤ^d`):

* `dyCutD ρ y x = min(1, max(0, 2 - |x - y|/ρ))`, `1` on `B_ρ(y)`, `0` outside `B_{2ρ}(y)`,
  `|dyCutD ρ y x' - dyCutD ρ y x| ≤ ||x' - y| - |x - y||/ρ` (`abs_dyCutD_sub_le`);
* `dyEtaD r y m = dyCutD (2^m √r) y` and `dyPieceD r y m` (`η_0`, then `η_m - η_{m-1}`), with
  `Σ_{m ≤ M} dyPieceD r y m = dyEtaD r y M` (`sum_dyPieceD`), `0 ≤ dyPieceD ≤ 1`, the support
  bounds `dyPieceD_eq_zero_of_le`, `dyPieceD_succ_eq_zero_of_le` and the Lipschitz bound
  `abs_dyPieceD_sub_le`;
* `neg_tsum_le_of_piecesD`: if `Σ_x G W` converges absolutely and every piece satisfies
  `-Σ_x G (dyPieceD r y m) W ≤ c_m` with `Σ_{m ≤ M} c_m ≤ S` for all `M`, then `-Σ_x G W ≤ S`
  (dominated convergence, since `η_M = 1` eventually at each point).
-/

open Filter Topology LatticeProb LatticeProb.Percolation

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}


theorem abs_clamp_sub_leD (a b : ℝ) : |min 1 (max 0 b) - min 1 (max 0 a)| ≤ |b - a| := by
  have h5 := le_abs_self (b - a)
  have h6 := neg_abs_le (b - a)
  simp only [min_def, max_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- The cutoff `min(1, max(0, 2 - |x - y|/ρ))`. -/
noncomputable def dyCutD (ρ : ℝ) (y x : Vertex d) : ℝ :=
  min 1 (max 0 (2 - ‖edzD x y‖ / ρ))

theorem dyCutD_nonneg (ρ : ℝ) (y x : Vertex d) : 0 ≤ dyCutD ρ y x :=
  le_min zero_le_one (le_max_left _ _)

theorem dyCutD_le_one (ρ : ℝ) (y x : Vertex d) : dyCutD ρ y x ≤ 1 := min_le_left _ _

theorem dyCutD_eq_one {ρ : ℝ} (hρ : 0 < ρ) {y x : Vertex d} (h : ‖edzD x y‖ ≤ ρ) :
    dyCutD ρ y x = 1 := by
  unfold dyCutD
  have h1 : ‖edzD x y‖ / ρ ≤ 1 := by rw [div_le_one hρ]; exact h
  exact min_eq_left (le_max_of_le_right (by linarith))

theorem dyCutD_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {y x : Vertex d} (h : 2 * ρ ≤ ‖edzD x y‖) :
    dyCutD ρ y x = 0 := by
  unfold dyCutD
  have h1 : 2 ≤ ‖edzD x y‖ / ρ := by rw [le_div_iff₀ hρ]; linarith
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

theorem dyCutD_mono {ρ ρ' : ℝ} (hρ : 0 < ρ) (h : ρ ≤ ρ') (y x : Vertex d) :
    dyCutD ρ y x ≤ dyCutD ρ' y x := by
  unfold dyCutD
  have : ‖edzD x y‖ / ρ' ≤ ‖edzD x y‖ / ρ :=
    div_le_div_of_nonneg_left (norm_nonneg (edzD x y)) hρ h
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

theorem abs_dyCutD_sub_le {ρ : ℝ} (hρ : 0 < ρ) (y x x' : Vertex d) :
    |dyCutD ρ y x' - dyCutD ρ y x| ≤ |‖edzD x' y‖ - ‖edzD x y‖| / ρ := by
  unfold dyCutD
  refine (abs_clamp_sub_leD _ _).trans (le_of_eq ?_)
  rw [show 2 - ‖edzD x' y‖ / ρ - (2 - ‖edzD x y‖ / ρ) =
    -((‖edzD x' y‖ - ‖edzD x y‖) / ρ) by ring, abs_neg, abs_div, abs_of_pos hρ]

/-- `η_m = dyCutD (2^m √r) y`. -/
noncomputable def dyEtaD (r : ℝ) (y : Vertex d) (m : ℕ) (x : Vertex d) : ℝ :=
  dyCutD (2 ^ m * Real.sqrt r) y x

/-- The pieces `η_0` and `η_{m+1} - η_m` of the partition of unity. -/
noncomputable def dyPieceD (r : ℝ) (y : Vertex d) : ℕ → Vertex d → ℝ
  | 0 => dyEtaD r y 0
  | m + 1 => fun x => dyEtaD r y (m + 1) x - dyEtaD r y m x

/-- **The partition of unity**: `Σ_{m ≤ M} dyPieceD r y m = η_M`. -/
theorem sum_dyPieceD (r : ℝ) (y : Vertex d) (M : ℕ) (x : Vertex d) :
    ∑ m ∈ Finset.range (M + 1), dyPieceD r y m x = dyEtaD r y M x := by
  induction M with
  | zero => simp [dyPieceD]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [dyPieceD]
    ring

theorem dyEtaD_mono {r : ℝ} (hr : 0 < r) (y : Vertex d) (m : ℕ) (x : Vertex d) :
    dyEtaD r y m x ≤ dyEtaD r y (m + 1) x := by
  unfold dyEtaD
  have hs := Real.sqrt_pos.2 hr
  exact dyCutD_mono (by positivity) (by rw [pow_succ]; nlinarith [pow_pos (two_pos (α := ℝ)) m])
    y x

theorem dyPieceD_nonneg {r : ℝ} (hr : 0 < r) (y : Vertex d) (m : ℕ) (x : Vertex d) :
    0 ≤ dyPieceD r y m x := by
  cases m with
  | zero => exact dyCutD_nonneg _ _ _
  | succ m =>
    simp only [dyPieceD]
    linarith [dyEtaD_mono hr y m x]

theorem dyPieceD_le_one {r : ℝ} (y : Vertex d) (m : ℕ) (x : Vertex d) : dyPieceD r y m x ≤ 1 := by
  cases m with
  | zero => exact dyCutD_le_one _ _ _
  | succ m =>
    simp only [dyPieceD]
    linarith [dyCutD_le_one (2 ^ (m + 1) * Real.sqrt r) y x,
      dyCutD_nonneg (2 ^ m * Real.sqrt r) y x, show dyEtaD r y (m + 1) x =
        dyCutD (2 ^ (m + 1) * Real.sqrt r) y x from rfl,
      show dyEtaD r y m x = dyCutD (2 ^ m * Real.sqrt r) y x from rfl]

/-- `η_M = 1` on `B_{2^M √r}(y)`. -/
theorem dyEtaD_eq_one {r : ℝ} (hr : 0 < r) {y x : Vertex d} {M : ℕ}
    (h : ‖edzD x y‖ ≤ 2 ^ M * Real.sqrt r) : dyEtaD r y M x = 1 :=
  dyCutD_eq_one (by have := Real.sqrt_pos.2 hr; positivity) h

/-- The pieces vanish outside `B_{2^{m+1} √r}(y)`. -/
theorem dyPieceD_eq_zero_of_le {r : ℝ} (hr : 0 < r) {y x : Vertex d} {m : ℕ}
    (h : 2 ^ (m + 1) * Real.sqrt r ≤ ‖edzD x y‖) : dyPieceD r y m x = 0 := by
  have hs := Real.sqrt_pos.2 hr
  have hm : 2 * (2 ^ m * Real.sqrt r) ≤ ‖edzD x y‖ := by
    rw [pow_succ] at h
    linarith
  cases m with
  | zero => exact dyCutD_eq_zero (by positivity) hm
  | succ m =>
    simp only [dyPieceD]
    have hm' : 2 * (2 ^ m * Real.sqrt r) ≤ ‖edzD x y‖ := by
      have : 2 ^ m * Real.sqrt r ≤ 2 ^ (m + 1) * Real.sqrt r := by
        rw [pow_succ]
        nlinarith [pow_pos (two_pos (α := ℝ)) m]
      linarith
    rw [show dyEtaD r y (m + 1) x = 0 from dyCutD_eq_zero (by positivity) hm,
      show dyEtaD r y m x = 0 from dyCutD_eq_zero (by positivity) hm']
    ring

/-- The pieces `η_{m+1} - η_m` vanish on `B_{2^m √r}(y)`. -/
theorem dyPieceD_succ_eq_zero_of_le {r : ℝ} (hr : 0 < r) {y x : Vertex d} {m : ℕ}
    (h : ‖edzD x y‖ ≤ 2 ^ m * Real.sqrt r) : dyPieceD r y (m + 1) x = 0 := by
  have hs := Real.sqrt_pos.2 hr
  simp only [dyPieceD]
  have h' : ‖edzD x y‖ ≤ 2 ^ (m + 1) * Real.sqrt r := by
    have : 2 ^ m * Real.sqrt r ≤ 2 ^ (m + 1) * Real.sqrt r := by
      rw [pow_succ]
      nlinarith [pow_pos (two_pos (α := ℝ)) m]
    linarith
  rw [dyEtaD_eq_one hr h, dyEtaD_eq_one hr h']
  ring

/-- **The Lipschitz bound of the pieces**: `|dyPieceD r y m x' - dyPieceD r y m x| ≤
4 ||x' - y| - |x - y|| / (2^m √r)`. -/
theorem abs_dyPieceD_sub_le {r : ℝ} (hr : 0 < r) (y x x' : Vertex d) (m : ℕ) :
    |dyPieceD r y m x' - dyPieceD r y m x| ≤
      4 * |‖edzD x' y‖ - ‖edzD x y‖| / (2 ^ m * Real.sqrt r) := by
  have hs := Real.sqrt_pos.2 hr
  have hD := abs_nonneg (‖edzD x' y‖ - ‖edzD x y‖)
  cases m with
  | zero =>
    refine (abs_dyCutD_sub_le (by positivity) y x x').trans ?_
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  | succ m =>
    simp only [dyPieceD]
    have h1 := abs_dyCutD_sub_le (show 0 < 2 ^ (m + 1) * Real.sqrt r by positivity) y x x'
    have h2 := abs_dyCutD_sub_le (show 0 < 2 ^ m * Real.sqrt r by positivity) y x x'
    have e : dyEtaD r y (m + 1) x' - dyEtaD r y m x' - (dyEtaD r y (m + 1) x - dyEtaD r y m x) =
        (dyCutD (2 ^ (m + 1) * Real.sqrt r) y x' - dyCutD (2 ^ (m + 1) * Real.sqrt r) y x) -
          (dyCutD (2 ^ m * Real.sqrt r) y x' - dyCutD (2 ^ m * Real.sqrt r) y x) := by
      unfold dyEtaD
      ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have hp : (0 : ℝ) < 2 ^ m * Real.sqrt r := by positivity
    have e1 : |‖edzD x' y‖ - ‖edzD x y‖| / (2 ^ (m + 1) * Real.sqrt r) ≤
        |‖edzD x' y‖ - ‖edzD x y‖| / (2 ^ m * Real.sqrt r) := by
      refine div_le_div_of_nonneg_left hD hp ?_
      rw [pow_succ]
      nlinarith
    have e2 : 4 * |‖edzD x' y‖ - ‖edzD x y‖| / (2 ^ (m + 1) * Real.sqrt r) =
        2 * (|‖edzD x' y‖ - ‖edzD x y‖| / (2 ^ m * Real.sqrt r)) := by
      rw [pow_succ]
      field_simp
      ring
    rw [e2]
    linarith

/-- For each `x` the cutoffs `η_M` are eventually `1`. -/
theorem exists_dyEtaD_eq_one {r : ℝ} (hr : 0 < r) (y x : Vertex d) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → dyEtaD r y M x = 1 := by
  have hs := Real.sqrt_pos.2 hr
  obtain ⟨M₀, hM₀⟩ := pow_unbounded_of_one_lt (‖edzD x y‖ / Real.sqrt r)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨M₀, fun M hM => dyEtaD_eq_one hr ?_⟩
  have h1 : (2 : ℝ) ^ M₀ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
  have h2 : ‖edzD x y‖ < 2 ^ M₀ * Real.sqrt r := by
    rw [div_lt_iff₀ hs] at hM₀
    exact hM₀
  nlinarith



theorem abs_dyEtaD_le {r : ℝ} (y : Vertex d) (M : ℕ) (x : Vertex d) : |dyEtaD r y M x| ≤ 1 := by
  unfold dyEtaD
  rw [abs_of_nonneg (dyCutD_nonneg _ _ _)]
  exact dyCutD_le_one _ _ _

/-- **The exchange of the dyadic sum with the lattice sum.** -/
theorem neg_tsum_le_of_piecesD {r S : ℝ} (hr : 0 < r) {y : Vertex d} {G W : Vertex d → ℝ}
    {c : ℕ → ℝ} (hGW : Summable fun x => |G x * W x|)
    (hpiece : ∀ m, Summable fun x => G x * (dyPieceD r y m x * W x))
    (hc : ∀ m, -(∑' x, G x * (dyPieceD r y m x * W x)) ≤ c m)
    (hS : ∀ M, ∑ m ∈ Finset.range (M + 1), c m ≤ S) :
    -(∑' x, G x * W x) ≤ S := by
  -- the truncated sums
  have htrunc : ∀ M, -(∑' x, G x * (dyEtaD r y M x * W x)) ≤ S := by
    intro M
    have e : ∑' x, G x * (dyEtaD r y M x * W x) =
        ∑ m ∈ Finset.range (M + 1), ∑' x, G x * (dyPieceD r y m x * W x) := by
      rw [← Summable.tsum_finsetSum fun m _ => hpiece m]
      refine tsum_congr fun x => ?_
      rw [← sum_dyPieceD r y M x, Finset.sum_mul, Finset.mul_sum]
    rw [e, ← Finset.sum_neg_distrib]
    exact (Finset.sum_le_sum fun m _ => hc m).trans (hS M)
  -- the limit
  have hlim : Tendsto (fun M => ∑' x, G x * (dyEtaD r y M x * W x)) atTop
      (𝓝 (∑' x, G x * W x)) := by
    refine tendsto_tsum_of_dominated_convergence hGW (fun x => ?_) (Eventually.of_forall
      fun M x => ?_)
    · obtain ⟨M₀, hM₀⟩ := exists_dyEtaD_eq_one hr y x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop M₀] with M hM
      rw [hM₀ M hM, one_mul]
    · rw [Real.norm_eq_abs, mul_left_comm, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_dyEtaD_le y M x)
  have hneg := hlim.neg
  exact le_of_tendsto' hneg htrunc

end Rigidity.Green.GeneralDim

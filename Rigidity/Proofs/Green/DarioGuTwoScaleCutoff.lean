import Rigidity.Proofs.Green.DarioGuTwoScaleFluxDuality

/-!
# The dyadic cutoffs of Step 3 of Proposition 4.3 of Dario–Gu

Step 3 of the proof of Proposition 4.3 of Dario–Gu (lines 2356-2368 of the source) uses the
cutoffs `η_m` with `|∇η_m| ≤ (2^m √t)^{-1}`, `η_m = 1` on `B_{2^m √t}(y)` and `supp η_m ⊂
B_{2^{m+1} √t}(y)`, and the partition of unity `1 = Σ_m (η_m - η_{m-1})`. On the lattice:

* `dyCut ρ y x = min(1, max(0, 2 - |x - y|/ρ))`, `1` on `B_ρ(y)`, `0` outside `B_{2ρ}(y)`,
  `|dyCut ρ y x' - dyCut ρ y x| ≤ ||x' - y| - |x - y||/ρ` (`abs_dyCut_sub_le`);
* `dyEta r y m = dyCut (2^m √r) y` and `dyPiece r y m` (`η_0`, then `η_m - η_{m-1}`), with
  `Σ_{m ≤ M} dyPiece r y m = dyEta r y M` (`sum_dyPiece`), `0 ≤ dyPiece ≤ 1`, the support
  bounds `dyPiece_eq_zero_of_le`, `dyPiece_succ_eq_zero_of_le` and the Lipschitz bound
  `abs_dyPiece_sub_le`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem abs_clamp_sub_le (a b : ℝ) : |min 1 (max 0 b) - min 1 (max 0 a)| ≤ |b - a| := by
  have h5 := le_abs_self (b - a)
  have h6 := neg_abs_le (b - a)
  simp only [min_def, max_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- The cutoff `min(1, max(0, 2 - |x - y|/ρ))`. -/
noncomputable def dyCut (ρ : ℝ) (y x : Vertex 2) : ℝ :=
  min 1 (max 0 (2 - latticeDist x y / ρ))

theorem dyCut_nonneg (ρ : ℝ) (y x : Vertex 2) : 0 ≤ dyCut ρ y x :=
  le_min zero_le_one (le_max_left _ _)

theorem dyCut_le_one (ρ : ℝ) (y x : Vertex 2) : dyCut ρ y x ≤ 1 := min_le_left _ _

theorem dyCut_eq_one {ρ : ℝ} (hρ : 0 < ρ) {y x : Vertex 2} (h : latticeDist x y ≤ ρ) :
    dyCut ρ y x = 1 := by
  unfold dyCut
  have h1 : latticeDist x y / ρ ≤ 1 := by rw [div_le_one hρ]; exact h
  exact min_eq_left (le_max_of_le_right (by linarith))

theorem dyCut_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {y x : Vertex 2} (h : 2 * ρ ≤ latticeDist x y) :
    dyCut ρ y x = 0 := by
  unfold dyCut
  have h1 : 2 ≤ latticeDist x y / ρ := by rw [le_div_iff₀ hρ]; linarith
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

theorem dyCut_mono {ρ ρ' : ℝ} (hρ : 0 < ρ) (h : ρ ≤ ρ') (y x : Vertex 2) :
    dyCut ρ y x ≤ dyCut ρ' y x := by
  unfold dyCut
  have : latticeDist x y / ρ' ≤ latticeDist x y / ρ :=
    div_le_div_of_nonneg_left (latticeDist_nonneg x y) hρ h
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

theorem abs_dyCut_sub_le {ρ : ℝ} (hρ : 0 < ρ) (y x x' : Vertex 2) :
    |dyCut ρ y x' - dyCut ρ y x| ≤ |latticeDist x' y - latticeDist x y| / ρ := by
  unfold dyCut
  refine (abs_clamp_sub_le _ _).trans (le_of_eq ?_)
  rw [show 2 - latticeDist x' y / ρ - (2 - latticeDist x y / ρ) =
    -((latticeDist x' y - latticeDist x y) / ρ) by ring, abs_neg, abs_div, abs_of_pos hρ]

/-- `η_m = dyCut (2^m √r) y`. -/
noncomputable def dyEta (r : ℝ) (y : Vertex 2) (m : ℕ) (x : Vertex 2) : ℝ :=
  dyCut (2 ^ m * Real.sqrt r) y x

/-- The pieces `η_0` and `η_{m+1} - η_m` of the partition of unity. -/
noncomputable def dyPiece (r : ℝ) (y : Vertex 2) : ℕ → Vertex 2 → ℝ
  | 0 => dyEta r y 0
  | m + 1 => fun x => dyEta r y (m + 1) x - dyEta r y m x

/-- **The partition of unity**: `Σ_{m ≤ M} dyPiece r y m = η_M`. -/
theorem sum_dyPiece (r : ℝ) (y : Vertex 2) (M : ℕ) (x : Vertex 2) :
    ∑ m ∈ Finset.range (M + 1), dyPiece r y m x = dyEta r y M x := by
  induction M with
  | zero => simp [dyPiece]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [dyPiece]
    ring

theorem dyEta_mono {r : ℝ} (hr : 0 < r) (y : Vertex 2) (m : ℕ) (x : Vertex 2) :
    dyEta r y m x ≤ dyEta r y (m + 1) x := by
  unfold dyEta
  have hs := Real.sqrt_pos.2 hr
  exact dyCut_mono (by positivity) (by rw [pow_succ]; nlinarith [pow_pos (two_pos (α := ℝ)) m])
    y x

theorem dyPiece_nonneg {r : ℝ} (hr : 0 < r) (y : Vertex 2) (m : ℕ) (x : Vertex 2) :
    0 ≤ dyPiece r y m x := by
  cases m with
  | zero => exact dyCut_nonneg _ _ _
  | succ m =>
    simp only [dyPiece]
    linarith [dyEta_mono hr y m x]

theorem dyPiece_le_one {r : ℝ} (y : Vertex 2) (m : ℕ) (x : Vertex 2) : dyPiece r y m x ≤ 1 := by
  cases m with
  | zero => exact dyCut_le_one _ _ _
  | succ m =>
    simp only [dyPiece]
    linarith [dyCut_le_one (2 ^ (m + 1) * Real.sqrt r) y x,
      dyCut_nonneg (2 ^ m * Real.sqrt r) y x, show dyEta r y (m + 1) x =
        dyCut (2 ^ (m + 1) * Real.sqrt r) y x from rfl,
      show dyEta r y m x = dyCut (2 ^ m * Real.sqrt r) y x from rfl]

/-- `η_M = 1` on `B_{2^M √r}(y)`. -/
theorem dyEta_eq_one {r : ℝ} (hr : 0 < r) {y x : Vertex 2} {M : ℕ}
    (h : latticeDist x y ≤ 2 ^ M * Real.sqrt r) : dyEta r y M x = 1 :=
  dyCut_eq_one (by have := Real.sqrt_pos.2 hr; positivity) h

/-- The pieces vanish outside `B_{2^{m+1} √r}(y)`. -/
theorem dyPiece_eq_zero_of_le {r : ℝ} (hr : 0 < r) {y x : Vertex 2} {m : ℕ}
    (h : 2 ^ (m + 1) * Real.sqrt r ≤ latticeDist x y) : dyPiece r y m x = 0 := by
  have hs := Real.sqrt_pos.2 hr
  have hm : 2 * (2 ^ m * Real.sqrt r) ≤ latticeDist x y := by
    rw [pow_succ] at h
    linarith
  cases m with
  | zero => exact dyCut_eq_zero (by positivity) hm
  | succ m =>
    simp only [dyPiece]
    have hm' : 2 * (2 ^ m * Real.sqrt r) ≤ latticeDist x y := by
      have : 2 ^ m * Real.sqrt r ≤ 2 ^ (m + 1) * Real.sqrt r := by
        rw [pow_succ]
        nlinarith [pow_pos (two_pos (α := ℝ)) m]
      linarith
    rw [show dyEta r y (m + 1) x = 0 from dyCut_eq_zero (by positivity) hm,
      show dyEta r y m x = 0 from dyCut_eq_zero (by positivity) hm']
    ring

/-- The pieces `η_{m+1} - η_m` vanish on `B_{2^m √r}(y)`. -/
theorem dyPiece_succ_eq_zero_of_le {r : ℝ} (hr : 0 < r) {y x : Vertex 2} {m : ℕ}
    (h : latticeDist x y ≤ 2 ^ m * Real.sqrt r) : dyPiece r y (m + 1) x = 0 := by
  have hs := Real.sqrt_pos.2 hr
  simp only [dyPiece]
  have h' : latticeDist x y ≤ 2 ^ (m + 1) * Real.sqrt r := by
    have : 2 ^ m * Real.sqrt r ≤ 2 ^ (m + 1) * Real.sqrt r := by
      rw [pow_succ]
      nlinarith [pow_pos (two_pos (α := ℝ)) m]
    linarith
  rw [dyEta_eq_one hr h, dyEta_eq_one hr h']
  ring

/-- **The Lipschitz bound of the pieces**: `|dyPiece r y m x' - dyPiece r y m x| ≤
4 ||x' - y| - |x - y|| / (2^m √r)`. -/
theorem abs_dyPiece_sub_le {r : ℝ} (hr : 0 < r) (y x x' : Vertex 2) (m : ℕ) :
    |dyPiece r y m x' - dyPiece r y m x| ≤
      4 * |latticeDist x' y - latticeDist x y| / (2 ^ m * Real.sqrt r) := by
  have hs := Real.sqrt_pos.2 hr
  have hD := abs_nonneg (latticeDist x' y - latticeDist x y)
  cases m with
  | zero =>
    refine (abs_dyCut_sub_le (by positivity) y x x').trans ?_
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  | succ m =>
    simp only [dyPiece]
    have h1 := abs_dyCut_sub_le (show 0 < 2 ^ (m + 1) * Real.sqrt r by positivity) y x x'
    have h2 := abs_dyCut_sub_le (show 0 < 2 ^ m * Real.sqrt r by positivity) y x x'
    have e : dyEta r y (m + 1) x' - dyEta r y m x' - (dyEta r y (m + 1) x - dyEta r y m x) =
        (dyCut (2 ^ (m + 1) * Real.sqrt r) y x' - dyCut (2 ^ (m + 1) * Real.sqrt r) y x) -
          (dyCut (2 ^ m * Real.sqrt r) y x' - dyCut (2 ^ m * Real.sqrt r) y x) := by
      unfold dyEta
      ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have hp : (0 : ℝ) < 2 ^ m * Real.sqrt r := by positivity
    have e1 : |latticeDist x' y - latticeDist x y| / (2 ^ (m + 1) * Real.sqrt r) ≤
        |latticeDist x' y - latticeDist x y| / (2 ^ m * Real.sqrt r) := by
      refine div_le_div_of_nonneg_left hD hp ?_
      rw [pow_succ]
      nlinarith
    have e2 : 4 * |latticeDist x' y - latticeDist x y| / (2 ^ (m + 1) * Real.sqrt r) =
        2 * (|latticeDist x' y - latticeDist x y| / (2 ^ m * Real.sqrt r)) := by
      rw [pow_succ]
      field_simp
      ring
    rw [e2]
    linarith

/-- For each `x` the cutoffs `η_M` are eventually `1`. -/
theorem exists_dyEta_eq_one {r : ℝ} (hr : 0 < r) (y x : Vertex 2) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → dyEta r y M x = 1 := by
  have hs := Real.sqrt_pos.2 hr
  obtain ⟨M₀, hM₀⟩ := pow_unbounded_of_one_lt (latticeDist x y / Real.sqrt r)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨M₀, fun M hM => dyEta_eq_one hr ?_⟩
  have h1 : (2 : ℝ) ^ M₀ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
  have h2 : latticeDist x y < 2 ^ M₀ * Real.sqrt r := by
    rw [div_lt_iff₀ hs] at hM₀
    exact hM₀
  nlinarith

end Rigidity.Green

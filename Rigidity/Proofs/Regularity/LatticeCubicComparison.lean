import Rigidity.Proofs.Regularity.LatticeHarmonicExcessThree

/-!
# Harmonic cubic and quadratic polynomials on the balls of `ℤ²`

A lattice harmonic cubic polynomial `w = c₀ + … + c₆ y₀³ + c₇ y₀² y₁ + c₈ y₀ y₁² + c₉ y₁³` has
`c₅ = -c₃`, `c₈ = -3 c₆`, `c₇ = -3 c₉` (`harmonic_relations`). Its excess over the lattice
harmonic quadratic functions `Ā_2` on `B_ρ(z)` is at most `4 (|c₆| + |c₉|) ρ³`: removing the
cubic part centred at `z` leaves a lattice harmonic quadratic function
(`ballExcess_cubicEval_le`). It is at least `(|c₆| + |c₉|) ρ³ / 655360` for `ρ ≥ 16`: for every
quadratic `h`, the third difference of `w - h` along `n eᵢ` is `6 c n³` with `c = c₆` or `c₉`,
and summing the inequality `(6 c n³)² ≤ 20 (g₀² + g₁² + g₂² + g₃²)` over the points of a box of
side `n ≈ ρ / 8` bounds the `ℓ²` norm of `w - h` on the ball from below
(`le_componentBallL2_of_third_difference`). This gives `PolynomialComparison` for `Ā_2 ≤ Ā_3`
with degree `3` on the balls of `ℤ²` (`polynomialComparison_latticeHarmonicCubic`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

/-- **The coefficients of a lattice harmonic cubic polynomial.** -/
theorem harmonic_relations {F : (Fin 2 → ℤ) → ℝ} {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ}
    (hF : ∀ y : Fin 2 → ℤ, F y = c₀ + c₁ * y 0 + c₂ * y 1 + c₃ * y 0 ^ 2 + c₄ * y 0 * y 1 +
      c₅ * y 1 ^ 2 + c₆ * y 0 ^ 3 + c₇ * y 0 ^ 2 * y 1 + c₈ * y 0 * y 1 ^ 2 + c₉ * y 1 ^ 3)
    (hΔ : ∀ y, latticeLaplacian F y = 0) : c₅ = -c₃ ∧ c₈ = -3 * c₆ ∧ c₇ = -3 * c₉ := by
  have h0 := hΔ 0
  have h1 := hΔ (unit 0)
  have h2 := hΔ (unit 1)
  rw [latticeLaplacian_eq_of_cubic hF] at h0 h1 h2
  have u00 : (unit 0 : Fin 2 → ℤ) 0 = 1 := by simp [unit]
  have u01 : (unit 0 : Fin 2 → ℤ) 1 = 0 := by simp [unit]
  have u10 : (unit 1 : Fin 2 → ℤ) 0 = 0 := by simp [unit]
  have u11 : (unit 1 : Fin 2 → ℤ) 1 = 1 := by simp [unit]
  rw [u00, u01] at h1
  rw [u10, u11] at h2
  simp only [Pi.zero_apply, Int.cast_zero, Int.cast_one, mul_zero, mul_one, add_zero] at h0 h1 h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The coefficients of a member of `latticeHarmonicCubic`. -/
theorem exists_coeffs_of_mem_latticeHarmonicCubic {w : latticeComponent 2 → ℝ}
    (hw : w ∈ latticeHarmonicCubic) :
    ∃ c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ,
      (∀ x : latticeComponent 2, w x = c₀ + c₁ * x.val 0 + c₂ * x.val 1 + c₃ * x.val 0 ^ 2 +
        c₄ * x.val 0 * x.val 1 + c₅ * x.val 1 ^ 2 + c₆ * x.val 0 ^ 3 +
        c₇ * x.val 0 ^ 2 * x.val 1 + c₈ * x.val 0 * x.val 1 ^ 2 + c₉ * x.val 1 ^ 3) ∧
      c₅ = -c₃ ∧ c₈ = -3 * c₆ ∧ c₇ = -3 * c₉ := by
  obtain ⟨⟨c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hF⟩, hΔ⟩ := hw
  exact ⟨c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, fun x => hF x.val,
    harmonic_relations hF hΔ⟩

theorem abs_coord_sub_lt_of_mem_ball {z : Vertex 2} {ρ : ℝ} {x : latticeComponent 2}
    (hx : x ∈ componentEuclideanBall (latticeComponent 2) z ρ) (i : Fin 2) :
    |((x.val i - z i : ℤ) : ℝ)| < ρ := by
  rw [mem_componentEuclideanBall] at hx
  have := abs_sub_le_dist_latticeEuclideanEmbedding x.val z i
  push_cast
  exact this.trans_lt hx

/-- **Upper bound for the excess of a harmonic cubic polynomial over `Ā_2`.** -/
theorem ballExcess_cubicEval_le (z : Vertex 2) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {w : latticeComponent 2 → ℝ} {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ}
    (hw : ∀ x : latticeComponent 2, w x = c₀ + c₁ * x.val 0 + c₂ * x.val 1 + c₃ * x.val 0 ^ 2 +
      c₄ * x.val 0 * x.val 1 + c₅ * x.val 1 ^ 2 + c₆ * x.val 0 ^ 3 +
      c₇ * x.val 0 ^ 2 * x.val 1 + c₈ * x.val 0 * x.val 1 ^ 2 + c₉ * x.val 1 ^ 3)
    (h5 : c₅ = -c₃) (h8 : c₈ = -3 * c₆) (h7 : c₇ = -3 * c₉) :
    ballExcess (componentBallSeminorm (latticeComponent 2) z) (latticeHarmonicQuadratic 2) ρ w ≤
      4 * (|c₆| + |c₉|) * ρ ^ 3 := by
  set a : ℝ := (z 0 : ℝ) with ha
  set b : ℝ := (z 1 : ℝ) with hb
  set Cub : latticeComponent 2 → ℝ := fun x =>
    c₆ * ((x.val 0 - z 0 : ℤ) : ℝ) ^ 3 + c₇ * ((x.val 0 - z 0 : ℤ) : ℝ) ^ 2 * ((x.val 1 - z 1 : ℤ) : ℝ) +
      c₈ * ((x.val 0 - z 0 : ℤ) : ℝ) * ((x.val 1 - z 1 : ℤ) : ℝ) ^ 2 +
        c₉ * ((x.val 1 - z 1 : ℤ) : ℝ) ^ 3 with hCub
  set d₀ := c₀ + c₆ * a ^ 3 + c₇ * a ^ 2 * b + c₈ * a * b ^ 2 + c₉ * b ^ 3 with hd₀
  set d₁ := c₁ - 3 * c₆ * a ^ 2 - 2 * c₇ * a * b - c₈ * b ^ 2 with hd₁
  set d₂ := c₂ - c₇ * a ^ 2 - 2 * c₈ * a * b - 3 * c₉ * b ^ 2 with hd₂
  set d₃ := c₃ + 3 * c₆ * a + c₇ * b with hd₃
  set d₄ := c₄ + 2 * c₇ * a + 2 * c₈ * b with hd₄
  set d₅ := c₅ + c₈ * a + 3 * c₉ * b with hd₅
  have hh : ∀ x : latticeComponent 2, w x - Cub x = d₀ + d₁ * x.val 0 + d₂ * x.val 1 +
      d₃ * x.val 0 ^ 2 + d₄ * x.val 0 * x.val 1 + d₅ * x.val 1 ^ 2 := by
    intro x
    rw [hw x, hCub]
    simp only [Int.cast_sub, hd₀, hd₁, hd₂, hd₃, hd₄, hd₅, ha, hb]
    ring
  have hmem : (w - Cub) ∈ latticeHarmonicQuadratic 2 := by
    refine ⟨⟨d₀, WithLp.toLp 2 ![d₁, d₂], !![d₃, d₄; 0, d₅], fun x => ?_⟩, fun y => ?_⟩
    · rw [Pi.sub_apply, hh x, inner_latticeEuclideanEmbedding_two,
        quadForm_latticeEuclideanEmbedding_two]
      simp
      ring
    · have hrep : ∀ y : Fin 2 → ℤ, latticeExt (w - Cub) y = d₀ + d₁ * y 0 + d₂ * y 1 +
          d₃ * y 0 ^ 2 + d₄ * y 0 * y 1 + d₅ * y 1 ^ 2 + 0 * y 0 ^ 3 + 0 * y 0 ^ 2 * y 1 +
          0 * y 0 * y 1 ^ 2 + 0 * y 1 ^ 3 := fun y => by
        have := hh ⟨y, mem_latticeComponent_supp y⟩
        rw [latticeExt, Pi.sub_apply, this]
        ring
      rw [latticeLaplacian_eq_of_cubic hrep, hd₃, hd₅, h5, h8, h7]
      ring
  refine (ballExcess_le _ _ hmem).trans ?_
  rw [componentBallSeminorm_apply]
  apply componentBallL2_le_of_abs_le _ _ _ (by positivity)
  intro x hx
  have e : (w - (w - Cub)) x = Cub x := by simp
  rw [e, hCub]
  have h0 := (abs_coord_sub_lt_of_mem_ball hx 0).le
  have h1 := (abs_coord_sub_lt_of_mem_ball hx 1).le
  set v₀ : ℝ := ((x.val 0 - z 0 : ℤ) : ℝ)
  set v₁ : ℝ := ((x.val 1 - z 1 : ℤ) : ℝ)
  have p3 : |v₀| ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h0 3
  have q3 : |v₁| ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
  have p21 : |v₀| ^ 2 * |v₁| ≤ ρ ^ 3 := by
    calc |v₀| ^ 2 * |v₁| ≤ ρ ^ 2 * ρ :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h0 2) h1 (abs_nonneg _) (by positivity)
      _ = ρ ^ 3 := by ring
  have p12 : |v₀| * |v₁| ^ 2 ≤ ρ ^ 3 := by
    calc |v₀| * |v₁| ^ 2 ≤ ρ * ρ ^ 2 :=
          mul_le_mul h0 (pow_le_pow_left₀ (abs_nonneg _) h1 2) (by positivity) hρ
      _ = ρ ^ 3 := by ring
  rw [h8, h7]
  calc |c₆ * v₀ ^ 3 + -3 * c₉ * v₀ ^ 2 * v₁ + -3 * c₆ * v₀ * v₁ ^ 2 + c₉ * v₁ ^ 3|
      ≤ |c₆| * |v₀| ^ 3 + 3 * |c₉| * (|v₀| ^ 2 * |v₁|) + 3 * |c₆| * (|v₀| * |v₁| ^ 2) +
          |c₉| * |v₁| ^ 3 := by
        have e1 : |c₆ * v₀ ^ 3| = |c₆| * |v₀| ^ 3 := by rw [abs_mul, abs_pow]
        have e2 : |-3 * c₉ * v₀ ^ 2 * v₁| = 3 * |c₉| * (|v₀| ^ 2 * |v₁|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 3)]
          ring
        have e3 : |-3 * c₆ * v₀ * v₁ ^ 2| = 3 * |c₆| * (|v₀| * |v₁| ^ 2) := by
          rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 3)]
          ring
        have e4 : |c₉ * v₁ ^ 3| = |c₉| * |v₁| ^ 3 := by rw [abs_mul, abs_pow]
        calc _ ≤ |c₆ * v₀ ^ 3 + -3 * c₉ * v₀ ^ 2 * v₁ + -3 * c₆ * v₀ * v₁ ^ 2| +
              |c₉ * v₁ ^ 3| := abs_add_le _ _
          _ ≤ |c₆ * v₀ ^ 3 + -3 * c₉ * v₀ ^ 2 * v₁| + |-3 * c₆ * v₀ * v₁ ^ 2| +
              |c₉ * v₁ ^ 3| := add_le_add (abs_add_le _ _) le_rfl
          _ ≤ |c₆ * v₀ ^ 3| + |-3 * c₉ * v₀ ^ 2 * v₁| + |-3 * c₆ * v₀ * v₁ ^ 2| +
              |c₉ * v₁ ^ 3| := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
          _ = _ := by rw [e1, e2, e3, e4]
    _ ≤ |c₆| * ρ ^ 3 + 3 * |c₉| * ρ ^ 3 + 3 * |c₆| * ρ ^ 3 + |c₉| * ρ ^ 3 := by
        have a6 := abs_nonneg c₆
        have a9 := abs_nonneg c₉
        gcongr
    _ = 4 * (|c₆| + |c₉|) * ρ ^ 3 := by ring

/-- **Lower bound by a third difference.** If the third difference of `G` along `n eᵢ` is
`6 γ n³` at every point, then `|γ| ρ³ / 327680 ≤ ‖G‖_{L̲²(B_ρ(z))}` on the balls of `ℤ²` with
`ρ ≥ 16`. -/
theorem le_componentBallL2_of_third_difference (z : Vertex 2) {ρ : ℝ} (hρ : 16 ≤ ρ)
    (G : (Fin 2 → ℤ) → ℝ) (i : Fin 2) (γ : ℝ)
    (hG : ∀ (y : Fin 2 → ℤ) (n : ℤ), G (y + (3 * n) • unit i) - 3 * G (y + (2 * n) • unit i) +
      3 * G (y + n • unit i) - G y = 6 * γ * n ^ 3) :
    |γ| * ρ ^ 3 / 327680 ≤ componentBallL2 (latticeComponent 2) z ρ (fun x => G x.val) := by
  classical
  have hρ0 : 0 < ρ := by linarith
  set n := ⌊ρ / 8⌋₊ with hn
  have hn8 : (n : ℝ) ≤ ρ / 8 := Nat.floor_le (by positivity)
  have hn16 : ρ / 16 ≤ n := by
    have := Nat.lt_floor_add_one (ρ / 8)
    rw [← hn] at this
    linarith
  -- the base points `S = q + [0, n]²` and the box `T = Q_{3n}(z)`
  have hshift : ∀ k : ℤ, 0 ≤ k → k ≤ 3 →
      ∀ y ∈ latticeBox univ ((z - fun _ => (n : ℤ)) - (2 * (n : ℤ)) • unit i) n,
        y + (k * n) • unit i ∈ supBox z (3 * n) := by
    intro k hk0 hk3 y hy
    rw [mem_latticeBox] at hy
    simp only [supBox, Fintype.mem_piFinset, mem_Icc]
    intro j
    have hyj := (hy j).1 (mem_univ j)
    rw [add_smul_unit_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply] at hyj
    have hkn : 0 ≤ k * n := mul_nonneg hk0 (Int.natCast_nonneg n)
    have hkn3 : k * n ≤ 3 * n := mul_le_mul_of_nonneg_right hk3 (Int.natCast_nonneg n)
    push_cast
    split_ifs at hyj ⊢ <;> constructor <;> linarith [hyj.1, hyj.2]
  have hST : latticeBox univ ((z - fun _ => (n : ℤ)) - (2 * (n : ℤ)) • unit i) n ⊆
      supBox z (3 * n) := fun y hy => by
    have := hshift 0 le_rfl (by norm_num) y hy
    simpa using this
  -- the box lies in the ball
  have hTball : Real.sqrt ((2 : ℕ) : ℝ) * ((3 * n : ℕ) : ℝ) < ρ := by
    have hs : Real.sqrt ((2 : ℕ) : ℝ) < 3 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h3 : ((3 * n : ℕ) : ℝ) ≤ 3 * (ρ / 8) := by push_cast; linarith
    have h0 : (0 : ℝ) ≤ ((3 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc Real.sqrt ((2 : ℕ) : ℝ) * ((3 * n : ℕ) : ℝ) ≤ 3 / 2 * (3 * (ρ / 8)) :=
          mul_le_mul hs.le h3 h0 (by norm_num)
      _ < ρ := by linarith
  have hball := sum_sq_supBox_le_ball z hTball G
  -- the pointwise inequality
  have hpt : ∀ y ∈ latticeBox univ ((z - fun _ => (n : ℤ)) - (2 * (n : ℤ)) • unit i) n,
      36 * γ ^ 2 * (n : ℝ) ^ 6 ≤
        20 * (G (y + (3 * (n : ℤ)) • unit i) ^ 2 + G (y + (2 * (n : ℤ)) • unit i) ^ 2 +
          G (y + (n : ℤ) • unit i) ^ 2 + G y ^ 2) := by
    intro y _
    have h := hG y n
    set g₃ := G (y + (3 * (n : ℤ)) • unit i)
    set g₂ := G (y + (2 * (n : ℤ)) • unit i)
    set g₁ := G (y + (n : ℤ) • unit i)
    set g₀ := G y
    have e : 36 * γ ^ 2 * (n : ℝ) ^ 6 = (g₃ - 3 * g₂ + 3 * g₁ - g₀) ^ 2 := by
      rw [h]; push_cast; ring
    rw [e]
    nlinarith [sq_nonneg (g₂ + 3 * g₃), sq_nonneg (g₁ - 3 * g₃), sq_nonneg (g₀ + g₃),
      sq_nonneg (3 * g₁ + 3 * g₂), sq_nonneg (g₂ - 3 * g₀), sq_nonneg (g₁ + 3 * g₀)]
  have hsumS := sum_le_sum hpt
  rw [sum_const, card_latticeBox_univ, nsmul_eq_mul, ← mul_sum, sum_add_distrib, sum_add_distrib,
    sum_add_distrib] at hsumS
  have hk : ∀ k : ℤ, 0 ≤ k → k ≤ 3 →
      ∑ y ∈ latticeBox univ ((z - fun _ => (n : ℤ)) - (2 * (n : ℤ)) • unit i) n,
        G (y + (k * n) • unit i) ^ 2 ≤ ∑ y ∈ supBox z (3 * n), G y ^ 2 := fun k hk0 hk3 =>
    sum_comp_add_le (fun y => G y ^ 2) (fun _ => sq_nonneg _) _ (hshift k hk0 hk3)
  have h3 := hk 3 (by norm_num) le_rfl
  have h2 := hk 2 (by norm_num) (by norm_num)
  have h1 := hk 1 (by norm_num) (by norm_num)
  simp only [one_mul] at h1
  have h0 : ∑ y ∈ latticeBox univ ((z - fun _ => (n : ℤ)) - (2 * (n : ℤ)) • unit i) n, G y ^ 2 ≤
      ∑ y ∈ supBox z (3 * n), G y ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hST fun _ _ _ => sq_nonneg _
  have hTS : ((n + 1 : ℕ) : ℝ) ^ 2 * (36 * γ ^ 2 * (n : ℝ) ^ 6) ≤
      80 * ∑ y ∈ supBox z (3 * n), G y ^ 2 := by
    push_cast at hsumS ⊢
    linarith
  -- the ball
  set N := componentBallL2 (latticeComponent 2) z ρ (fun x => G x.val) with hN
  have hcardpos : 0 < ((componentEuclideanBall (latticeComponent 2) z ρ).card : ℝ) := by
    have : (⟨z, mem_latticeComponent_supp z⟩ : latticeComponent 2) ∈
        componentEuclideanBall (latticeComponent 2) z ρ := by
      rw [mem_componentEuclideanBall, dist_self]; exact hρ0
    exact_mod_cast Finset.card_pos.2 ⟨_, this⟩
  have hcard : ((componentEuclideanBall (latticeComponent 2) z ρ).card : ℝ) ≤ 9 * ρ ^ 2 := by
    have := card_componentEuclideanBall_le (latticeComponent 2) z hρ0.le
    calc _ ≤ (2 * ρ + 3) ^ 2 := this
      _ ≤ 9 * ρ ^ 2 := by nlinarith
  have hsq : ∑ x ∈ componentEuclideanBall (latticeComponent 2) z ρ, G x.val ^ 2 =
      ((componentEuclideanBall (latticeComponent 2) z ρ).card : ℝ) * N ^ 2 :=
    sum_sq_eq_card_mul_componentBallL2_sq (latticeComponent 2) z ρ (fun x => G x.val)
  have hmain : (|γ| * ρ ^ 3 / 327680) ^ 2 * (9 * ρ ^ 2) ≤
      ((componentEuclideanBall (latticeComponent 2) z ρ).card : ℝ) * N ^ 2 := by
    rw [← hsq]
    refine le_trans ?_ hball
    have hn1 : ρ / 16 ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hn6 : (ρ / 16) ^ 6 ≤ (n : ℝ) ^ 6 := pow_le_pow_left₀ (by positivity) hn16 6
    have hn2 : (ρ / 16) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hn1 2
    have hlow : (ρ / 16) ^ 2 * (36 * γ ^ 2 * (ρ / 16) ^ 6) ≤
        ((n + 1 : ℕ) : ℝ) ^ 2 * (36 * γ ^ 2 * (n : ℝ) ^ 6) := by
      apply mul_le_mul hn2 _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hn6 (by positivity)
    have e : (|γ| * ρ ^ 3 / 327680) ^ 2 * (9 * ρ ^ 2) =
        (ρ / 16) ^ 2 * (36 * γ ^ 2 * (ρ / 16) ^ 6) * (9 * 16 ^ 8 / (36 * 327680 ^ 2)) := by
      rw [div_pow, mul_pow, sq_abs]; ring
    rw [e]
    have hc : (9 * 16 ^ 8 / (36 * 327680 ^ 2) : ℝ) ≤ 1 / 80 := by norm_num
    have hnn : 0 ≤ (ρ / 16) ^ 2 * (36 * γ ^ 2 * (ρ / 16) ^ 6) := by positivity
    nlinarith
  have hN0 : 0 ≤ N := componentBallL2_nonneg _ _ _ _
  have hfinal : (|γ| * ρ ^ 3 / 327680) ^ 2 ≤ N ^ 2 := by
    have h9 : (|γ| * ρ ^ 3 / 327680) ^ 2 *
        ((componentEuclideanBall (latticeComponent 2) z ρ).card : ℝ) ≤
        (|γ| * ρ ^ 3 / 327680) ^ 2 * (9 * ρ ^ 2) :=
      mul_le_mul_of_nonneg_left hcard (sq_nonneg _)
    nlinarith [h9.trans hmain, hcardpos]
  have hpos : 0 ≤ |γ| * ρ ^ 3 / 327680 := by positivity
  nlinarith [hfinal, hpos, hN0]

@[simp] theorem add_smul_unit_zero_zero (y : Fin 2 → ℤ) (k : ℤ) : (y + k • unit 0 : Fin 2 → ℤ) 0 = y 0 + k := by
  simp [unit]

@[simp] theorem add_smul_unit_zero_one (y : Fin 2 → ℤ) (k : ℤ) : (y + k • unit 0 : Fin 2 → ℤ) 1 = y 1 := by
  simp [unit]

@[simp] theorem add_smul_unit_one_zero (y : Fin 2 → ℤ) (k : ℤ) : (y + k • unit 1 : Fin 2 → ℤ) 0 = y 0 := by
  simp [unit]

@[simp] theorem add_smul_unit_one_one (y : Fin 2 → ℤ) (k : ℤ) : (y + k • unit 1 : Fin 2 → ℤ) 1 = y 1 + k := by
  simp [unit]

/-- The third differences of a cubic polynomial along `n e₀` and `n e₁`. -/
theorem third_difference_cubic {G : (Fin 2 → ℤ) → ℝ} {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ}
    (hG : ∀ y : Fin 2 → ℤ, G y = c₀ + c₁ * y 0 + c₂ * y 1 + c₃ * y 0 ^ 2 + c₄ * y 0 * y 1 +
      c₅ * y 1 ^ 2 + c₆ * y 0 ^ 3 + c₇ * y 0 ^ 2 * y 1 + c₈ * y 0 * y 1 ^ 2 + c₉ * y 1 ^ 3)
    (y : Fin 2 → ℤ) (n : ℤ) :
    (G (y + (3 * n) • unit 0) - 3 * G (y + (2 * n) • unit 0) + 3 * G (y + n • unit 0) - G y =
      6 * c₆ * n ^ 3) ∧
    (G (y + (3 * n) • unit 1) - 3 * G (y + (2 * n) • unit 1) + 3 * G (y + n • unit 1) - G y =
      6 * c₉ * n ^ 3) := by
  constructor <;>
  · simp only [hG, add_smul_unit_zero_zero, add_smul_unit_zero_one, add_smul_unit_one_zero,
      add_smul_unit_one_one]
    push_cast
    ring

/-- **Polynomial comparison for harmonic cubic polynomials over `Ā_2` on the balls of `ℤ²`**,
with degree `3` and `CP = 2621440`, above the radius `16`. -/
theorem polynomialComparison_latticeHarmonicCubic (z : Vertex 2) (R : ℝ) :
    PolynomialComparison (componentBallSeminorm (latticeComponent 2) z)
      (latticeHarmonicQuadratic 2) latticeHarmonicCubic 3 16 R 2621440 := by
  intro w hw ρ ρ' hXρ hρρ' _
  obtain ⟨c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hcw, h5, h8, h7⟩ :=
    exists_coeffs_of_mem_latticeHarmonicCubic hw
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ' : 16 ≤ ρ' := hXρ.trans hρρ'
  have hup := ballExcess_cubicEval_le z hρ0 hcw h5 h8 h7
  have hlow : (|c₆| + |c₉|) * ρ' ^ 3 / 655360 ≤
      ballExcess (componentBallSeminorm (latticeComponent 2) z) (latticeHarmonicQuadratic 2) ρ'
        w := by
    apply le_ballExcess
    intro h hh
    obtain ⟨a, p, M, hhq⟩ := hh.1
    set G : (Fin 2 → ℤ) → ℝ := fun y => latticeExt w y - latticeExt h y with hGdef
    have hGc : ∀ y : Fin 2 → ℤ, G y = (c₀ - a) + (c₁ - p 0) * y 0 + (c₂ - p 1) * y 1 +
        (c₃ - M 0 0) * y 0 ^ 2 + (c₄ - (M 0 1 + M 1 0)) * y 0 * y 1 + (c₅ - M 1 1) * y 1 ^ 2 +
        c₆ * y 0 ^ 3 + c₇ * y 0 ^ 2 * y 1 + c₈ * y 0 * y 1 ^ 2 + c₉ * y 1 ^ 3 := by
      intro y
      simp only [hGdef, latticeExt, hcw, hhq, inner_latticeEuclideanEmbedding_two,
        quadForm_latticeEuclideanEmbedding_two]
      ring
    have hd := third_difference_cubic hGc
    have hN : componentBallSeminorm (latticeComponent 2) z ρ' (w - h) =
        componentBallL2 (latticeComponent 2) z ρ' (fun x => G x.val) := by
      rw [componentBallSeminorm_apply]; rfl
    rw [hN]
    have hb6 := le_componentBallL2_of_third_difference z hρ' G 0 c₆ fun y n => (hd y n).1
    have hb9 := le_componentBallL2_of_third_difference z hρ' G 1 c₉ fun y n => (hd y n).2
    have hρ3 : 0 ≤ ρ' ^ 3 := by positivity
    have e : (|c₆| + |c₉|) * ρ' ^ 3 / 655360 =
        (|c₆| * ρ' ^ 3 / 327680 + |c₉| * ρ' ^ 3 / 327680) / 2 := by ring
    rw [e]
    linarith
  have hρ'0 : 0 < ρ' := by linarith
  calc _ ≤ 4 * (|c₆| + |c₉|) * ρ ^ 3 := hup
    _ = 2621440 * (ρ / ρ') ^ 3 * ((|c₆| + |c₉|) * ρ' ^ 3 / 655360) := by
        field_simp
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

end Rigidity.Proofs.Regularity

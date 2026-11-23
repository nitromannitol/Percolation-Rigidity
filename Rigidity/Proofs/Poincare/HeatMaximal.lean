import Rigidity.Proofs.Poincare.BoxMaximal
import Rigidity.Proofs.Poincare.HeatKernelBounds

/-!
# Domination of the tilted heat semigroup of `ℤ²` by the box maximal function

The lattice form of the maximal bound (D.9) of Armstrong, Kuusi and Mourrat (Proposition D.2,
Step 1), with the exponential tilt needed for the weights of their Remark D.6:

* `tsum_exp_mul_le_boxMax`: for `σ ≥ 1`, `Σ_z e^{-|z|₁/σ} F(x + z) ≤ C σ² boxMax F x`, by
  splitting `ℤ²` into the boxes of radii `⌈σ⌉ 2^j` and `e^{-2^{j-1}} ≤ 24 · 2^{-4(j-1)}`;
* `exists_heat_le_boxMax`: for `0 ≤ s ≤ T`, `0 ≤ a ≤ 1/6`, `a max(√T, 1) ≤ 1`,
  `Σ_y Φ_s(x, y) e^{a|y - x|₁} G(y) ≤ C boxMax G x`, from the tilted heat kernel bound
  `exists_openHeat_mul_exp_le`.
-/

open LatticeProb LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Poincare

theorem exp_neg_le_div_pow_four {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 24 / x ^ 4 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 4
  have h24 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by positivity)]
  have hx4 : 0 < x ^ 4 := by positivity
  rw [div_le_iff₀ (by norm_num)] at h
  linarith

/-- The layer weights `e_j = e^{1 - 2^j/2}` satisfy `e_j 4^j ≤ 384 e 2^{-j}`. -/
theorem exp_layer_mul_four_pow_le (j : ℕ) :
    Real.exp (1 - 2 ^ j / 2) * 4 ^ j ≤ 384 * Real.exp 1 * (1 / 2) ^ j := by
  have hx : (0 : ℝ) < 2 ^ j / 2 := by positivity
  have h := exp_neg_le_div_pow_four hx
  have e1 : Real.exp (1 - 2 ^ j / 2) = Real.exp 1 * Real.exp (-(2 ^ j / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1]
  have h16 : (24 : ℝ) / (2 ^ j / 2) ^ 4 * 4 ^ j = 384 * (1 / 2) ^ j * (1 / 2) ^ j := by
    have hu : (0 : ℝ) < 2 ^ j := by positivity
    have e4 : (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e2 : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [one_div_pow]
    rw [e4, e2]
    field_simp
    ring
  have h2 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc Real.exp 1 * Real.exp (-(2 ^ j / 2)) * 4 ^ j
      ≤ Real.exp 1 * (24 / (2 ^ j / 2) ^ 4) * 4 ^ j := by gcongr
    _ = Real.exp 1 * (384 * (1 / 2) ^ j * (1 / 2) ^ j) := by rw [mul_assoc, h16]
    _ ≤ Real.exp 1 * (384 * (1 / 2) ^ j * 1) := by gcongr
    _ = 384 * Real.exp 1 * (1 / 2) ^ j := by ring

theorem supBox_eq_image (x : Fin 2 → ℤ) (r : ℕ) :
    supBox x r = (supBox 0 r).image (x + ·) := by
  ext w
  simp only [Finset.mem_image, mem_supBox, Pi.zero_apply, sub_zero]
  constructor
  · intro h
    exact ⟨w - x, fun i => by simpa using h i, by abel⟩
  · rintro ⟨z, hz, rfl⟩ i
    simpa using hz i

theorem sum_supBox_add (F : (Fin 2 → ℤ) → ℝ) (x : Fin 2 → ℤ) (r : ℕ) :
    ∑ z ∈ supBox 0 r, F (x + z) = ∑ w ∈ supBox x r, F w := by
  rw [supBox_eq_image x r, Finset.sum_image fun a _ b _ h => add_left_cancel h]

/-- **Exponential kernels are dominated by the box maximal function**: for `σ ≥ 1`,
`Σ_z e^{-|z|₁/σ} F(x + z) ≤ 27648 e σ² boxMax F x`. -/
theorem tsum_exp_mul_le_boxMax {F : (Fin 2 → ℤ) → ℝ} (hF : ∀ z, 0 ≤ F z) (hFs : Summable F)
    {σ : ℝ} (hσ : 1 ≤ σ) (x : Fin 2 → ℤ) :
    ∑' z : Fin 2 → ℤ, ENNReal.ofReal
        (Real.exp (-(|((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)|) / σ) * F (x + z)) ≤
      ENNReal.ofReal (27648 * Real.exp 1 * σ ^ 2 * boxMax F x) := by
  classical
  have hσ0 : 0 < σ := by linarith
  set ρ : ℕ := ⌈σ⌉₊ with hρ
  have hρσ : σ ≤ ρ := Nat.le_ceil σ
  have hρ2 : (ρ : ℝ) ≤ 2 * σ := by
    have := Nat.ceil_lt_add_one hσ0.le
    linarith
  set e : ℕ → ℝ := fun j => Real.exp (1 - 2 ^ j / 2) with he
  set B : ℕ → Finset (Fin 2 → ℤ) := fun j => supBox 0 (ρ * 2 ^ j) with hB
  have hM0 := boxMax_nonneg hF hFs x
  -- every point lies in a layer whose weight dominates the kernel
  have hlayer : ∀ z : Fin 2 → ℤ, ∃ j, z ∈ B j ∧
      Real.exp (-(|((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)|) / σ) ≤ e j := by
    intro z
    set n : ℕ := max (z 0).natAbs (z 1).natAbs with hn
    have hex : ∃ j : ℕ, n ≤ ρ * 2 ^ j := by
      refine ⟨n, ?_⟩
      have h1 : n < 2 ^ n := Nat.lt_two_pow_self
      have h2 : 1 ≤ ρ := Nat.one_le_iff_ne_zero.2 (by
        intro h0
        have : σ ≤ 0 := by rw [← Nat.cast_zero, ← h0]; exact hρσ
        linarith)
      nlinarith
    refine ⟨Nat.find hex, ?_, ?_⟩
    · rw [hB, mem_supBox]
      intro i
      have hn' := Nat.find_spec hex
      have hi : (z i).natAbs ≤ n := by
        fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
      simp only [Pi.zero_apply, sub_zero]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hi.trans hn'
    · rw [he]
      refine Real.exp_le_exp.2 ?_
      have hz1 : (n : ℝ) ≤ |((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)| := by
        have h0 : ((z 0).natAbs : ℝ) = |((z 0 : ℤ) : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        have h1 : ((z 1).natAbs : ℝ) = |((z 1 : ℤ) : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [hn, ← h0, ← h1]
        rcases le_total (z 0).natAbs (z 1).natAbs with h | h
        · rw [max_eq_right h]; linarith [Nat.cast_nonneg (α := ℝ) (z 0).natAbs]
        · rw [max_eq_left h]; linarith [Nat.cast_nonneg (α := ℝ) (z 1).natAbs]
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero]
        have : 0 ≤ (|((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)|) / σ := by positivity
        rw [neg_div]
        linarith
      · obtain ⟨j', hj'⟩ : ∃ j', Nat.find hex = j' + 1 := ⟨Nat.find hex - 1, by omega⟩
        have hmin := Nat.find_min hex (show j' < Nat.find hex by omega)
        have hlt : (ρ : ℝ) * 2 ^ j' < n := by exact_mod_cast not_le.1 hmin
        have hge : (2 : ℝ) ^ j' ≤ (|((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)|) / σ := by
          rw [le_div_iff₀ hσ0]
          nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) j']
        rw [hj', pow_succ, neg_div]
        linarith
  -- the layer decomposition
  have hpt : ∀ z : Fin 2 → ℤ, ENNReal.ofReal
      (Real.exp (-(|((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)|) / σ) * F (x + z)) ≤
      ∑' j, if z ∈ B j then ENNReal.ofReal (e j * F (x + z)) else 0 := by
    intro z
    obtain ⟨j, hjB, hje⟩ := hlayer z
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [if_pos hjB]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hje (hF _))
  have hbox : ∀ j, (∑' z, if z ∈ B j then ENNReal.ofReal (e j * F (x + z)) else 0) ≤
      ENNReal.ofReal (e j * (2 * (ρ * 2 ^ j : ℕ) + 1) ^ 2 * boxMax F x) := by
    intro j
    rw [tsum_eq_sum (s := B j) fun z hz => if_neg hz, Finset.sum_congr rfl fun z hz => if_pos hz,
      ← ENNReal.ofReal_sum_of_nonneg fun z _ => mul_nonneg (Real.exp_pos _).le (hF _),
      ← Finset.mul_sum, hB, sum_supBox_add]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have h := boxAvg_le_boxMax hF hFs x (ρ * 2 ^ j)
    have hpos : (0 : ℝ) < ((2 * (ρ * 2 ^ j) + 1) ^ 2 : ℕ) := by positivity
    rw [boxAvg, div_le_iff₀ hpos] at h
    push_cast at h ⊢
    linarith
  have hgeom : ∀ j : ℕ, e j * (2 * (ρ * 2 ^ j : ℕ) + 1) ^ 2 ≤
      9 * (ρ : ℝ) ^ 2 * (384 * Real.exp 1 * (1 / 2) ^ j) := by
    intro j
    have h1 : (2 * ((ρ * 2 ^ j : ℕ) : ℝ) + 1) ^ 2 ≤ 9 * (ρ : ℝ) ^ 2 * 4 ^ j := by
      have hρ1 : (1 : ℝ) ≤ ρ := le_trans hσ hρσ
      have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have e4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
      push_cast
      rw [e4]
      nlinarith [mul_le_mul hρ1 h2j zero_le_one (by linarith)]
    calc e j * (2 * ((ρ * 2 ^ j : ℕ) : ℝ) + 1) ^ 2 ≤ e j * (9 * (ρ : ℝ) ^ 2 * 4 ^ j) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 9 * (ρ : ℝ) ^ 2 * (e j * 4 ^ j) := by ring
      _ ≤ 9 * (ρ : ℝ) ^ 2 * (384 * Real.exp 1 * (1 / 2) ^ j) :=
          mul_le_mul_of_nonneg_left (exp_layer_mul_four_pow_le j) (by positivity)
  calc ∑' z, ENNReal.ofReal
        (Real.exp (-(|((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)|) / σ) * F (x + z))
      ≤ ∑' z, ∑' j, if z ∈ B j then ENNReal.ofReal (e j * F (x + z)) else 0 :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' j, ∑' z, if z ∈ B j then ENNReal.ofReal (e j * F (x + z)) else 0 :=
        ENNReal.tsum_comm
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (e j * (2 * (ρ * 2 ^ j : ℕ) + 1) ^ 2 * boxMax F x) :=
        ENNReal.tsum_le_tsum hbox
    _ ≤ ∑' j : ℕ,
          ENNReal.ofReal (9 * (ρ : ℝ) ^ 2 * (384 * Real.exp 1) * boxMax F x * (1 / 2) ^ j) :=
        ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (by
          have := mul_le_mul_of_nonneg_right (hgeom j) hM0
          linarith)
    _ = ENNReal.ofReal (9 * (ρ : ℝ) ^ 2 * (384 * Real.exp 1) * boxMax F x * 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          ((summable_geometric_two).mul_left _), tsum_mul_left, tsum_geometric_two]
    _ ≤ ENNReal.ofReal (27648 * Real.exp 1 * σ ^ 2 * boxMax F x) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hρ2' : (ρ : ℝ) ^ 2 ≤ 4 * σ ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ρ]
        have he1 : 0 ≤ Real.exp 1 * boxMax F x := mul_nonneg (Real.exp_pos 1).le hM0
        nlinarith

/-- **The weighted heat maximal bound**: for `0 ≤ s ≤ T`, `0 ≤ a ≤ 1/6`, `a max(√T, 1) ≤ 1` and
`G ≥ 0` summable, `Σ_y Φ_s(x, y) e^{a|y - x|₁} G(y) ≤ C boxMax G x`. -/
theorem exists_heat_le_boxMax : ∃ C : ℝ, 0 < C ∧ ∀ T a : ℝ, 0 ≤ T → 0 ≤ a → a ≤ 1 / 6 →
    a * max (Real.sqrt T) 1 ≤ 1 → ∀ s : ℝ, 0 ≤ s → s ≤ T → ∀ G : Vertex 2 → ℝ,
      (∀ z, 0 ≤ G z) → Summable G → ∀ x : Vertex 2,
        ∑' y, ENNReal.ofReal (openHeat (allOpen 2) s x y *
            Real.exp (a * (|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|)) * G y) ≤
          ENNReal.ofReal (C * boxMax G x) := by
  obtain ⟨C₁, hC₁, h⟩ := exists_openHeat_mul_exp_le
  refine ⟨C₁ * (27648 * Real.exp 1), by positivity,
    fun T a hT ha0 ha6 haT s hs hsT G hG hGs x => ?_⟩
  set σ := max (Real.sqrt s) 1 with hσ
  have hσ1 : 1 ≤ σ := le_max_right _ _
  have hσ0 : 0 < σ := by linarith
  have haσ : a * σ ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ ha0) haT
    exact max_le_max (Real.sqrt_le_sqrt hsT) le_rfl
  have hpt : ∀ y, ENNReal.ofReal (openHeat (allOpen 2) s x y *
      Real.exp (a * (|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|)) * G y) ≤
      ENNReal.ofReal (C₁ / σ ^ 2) * ENNReal.ofReal (Real.exp
        (-(|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|) / σ) * G (x + (y - x))) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), add_sub_cancel, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (h s hs a ha0 ha6 haσ x y) (hG y))
  calc ∑' y, ENNReal.ofReal (openHeat (allOpen 2) s x y *
          Real.exp (a * (|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|)) * G y)
      ≤ ∑' y, ENNReal.ofReal (C₁ / σ ^ 2) * ENNReal.ofReal (Real.exp
          (-(|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|) / σ) * G (x + (y - x))) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (C₁ / σ ^ 2) * ∑' z : Fin 2 → ℤ, ENNReal.ofReal (Real.exp
          (-(|((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)|) / σ) * G (x + z)) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact (Equiv.subRight x).tsum_eq (fun z : Fin 2 → ℤ => ENNReal.ofReal (Real.exp
          (-(|((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)|) / σ) * G (x + z)))
    _ ≤ ENNReal.ofReal (C₁ / σ ^ 2) *
          ENNReal.ofReal (27648 * Real.exp 1 * σ ^ 2 * boxMax G x) :=
        mul_le_mul_of_nonneg_left (tsum_exp_mul_le_boxMax hG hGs hσ1 x) zero_le
    _ = ENNReal.ofReal (C₁ * (27648 * Real.exp 1) * boxMax G x) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end Rigidity.Poincare

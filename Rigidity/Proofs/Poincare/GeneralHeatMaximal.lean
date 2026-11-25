import Rigidity.Proofs.Poincare.HeatMaximal
import Rigidity.Proofs.Poincare.GeneralBoxMaximal
import Rigidity.Proofs.Poincare.GeneralHeatKernelBounds

/-!
# Domination of the tilted heat semigroup of `ℤ^d` by the box maximal function

The extension of `HeatMaximal.lean` from `ℤ²` to `ℤ^d`:

* `exists_tsum_exp_mul_le_boxMax`: for `σ ≥ 1`, `Σ_z e^{-|z|₁/σ} F(x + z) ≤ K σ^d boxMax F x`, by
  splitting `ℤ^d` into the boxes of radii `⌈σ⌉ 2^j` and
  `e^{-2^{j-1}} ≤ (d + 1)! 2^{d+1} 2^{-(d+1) j}`;
* `exists_heat_le_boxMax`: for `0 ≤ s ≤ T`, `0 ≤ a ≤ 1/6`, `a max(√T, 1) ≤ 1`,
  `Σ_y Φ_s(x, y) e^{a|y - x|₁} G(y) ≤ C boxMax G x`, from the tilted heat kernel bound
  `exists_zdHeat_mul_exp_le`.
-/

open LatticeProb LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- `e^{-x} ≤ (d + 1)!/x^{d+1}` for `x > 0`. -/
theorem exp_neg_le_factorial_div_pow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-x) ≤ (n.factorial : ℝ) / x ^ n := by
  have h := Real.pow_div_factorial_le_exp x hx.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by positivity), one_mul]
  rw [div_le_iff₀ hf] at h
  linarith

/-- The layer weights `e_j = e^{1 - 2^j/2}` satisfy `e_j (2^j)^d ≤ e (d + 1)! 2^{d+1} 2^{-j}`. -/
theorem exp_layer_mul_pow_le (d j : ℕ) :
    Real.exp (1 - 2 ^ j / 2) * ((2 : ℝ) ^ j) ^ d ≤
      Real.exp 1 * ((d + 1).factorial * 2 ^ (d + 1)) * (1 / 2) ^ j := by
  have hu : (0 : ℝ) < 2 ^ j := by positivity
  have hx : (0 : ℝ) < 2 ^ j / 2 := by positivity
  have h := exp_neg_le_factorial_div_pow hx (d + 1)
  have e1 : Real.exp (1 - 2 ^ j / 2) = Real.exp 1 * Real.exp (-(2 ^ j / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : ((d + 1).factorial : ℝ) / (2 ^ j / 2) ^ (d + 1) * ((2 : ℝ) ^ j) ^ d =
      ((d + 1).factorial * 2 ^ (d + 1)) * (1 / 2) ^ j := by
    rw [div_pow, one_div_pow, pow_succ]
    field_simp
  rw [e1]
  calc Real.exp 1 * Real.exp (-(2 ^ j / 2)) * ((2 : ℝ) ^ j) ^ d
      ≤ Real.exp 1 * (((d + 1).factorial : ℝ) / (2 ^ j / 2) ^ (d + 1)) * ((2 : ℝ) ^ j) ^ d := by
        gcongr
    _ = Real.exp 1 * ((d + 1).factorial * 2 ^ (d + 1)) * (1 / 2) ^ j := by
        rw [mul_assoc, h2]
        ring

theorem supBox_eq_image (x : Fin d → ℤ) (r : ℕ) :
    supBox x r = (supBox 0 r).image (x + ·) := by
  ext w
  simp only [Finset.mem_image, mem_supBox, Pi.zero_apply, sub_zero]
  constructor
  · intro h
    exact ⟨w - x, fun i => by simpa using h i, by abel⟩
  · rintro ⟨z, hz, rfl⟩ i
    simpa using hz i

theorem sum_supBox_add (F : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) (r : ℕ) :
    ∑ z ∈ supBox 0 r, F (x + z) = ∑ w ∈ supBox x r, F w := by
  rw [supBox_eq_image x r, Finset.sum_image fun a _ b _ h => add_left_cancel h]

/-- The largest coordinate `max_i |z_i|` of `z ∈ ℤ^d`. -/
def supNorm (z : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (z i).natAbs

theorem natAbs_le_supNorm (z : Fin d → ℤ) (i : Fin d) : (z i).natAbs ≤ supNorm z :=
  Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ i)

theorem supNorm_le_sum_abs (z : Fin d → ℤ) : (supNorm z : ℝ) ≤ ∑ i, |((z i : ℤ) : ℝ)| := by
  obtain ⟨i, -, hi⟩ | h := (Finset.univ : Finset (Fin d)).eq_empty_or_nonempty.symm.imp
    (fun hne => Finset.exists_mem_eq_sup _ hne fun i => (z i).natAbs) id
  · rw [supNorm, hi]
    have : ((z i).natAbs : ℝ) = |((z i : ℤ) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this]
    exact Finset.single_le_sum (f := fun i => |((z i : ℤ) : ℝ)|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  · rw [supNorm, h]
    simp

/-- **Exponential kernels are dominated by the box maximal function**: there is `K` such that for
`σ ≥ 1`, `Σ_z e^{-|z|₁/σ} F(x + z) ≤ K σ^d boxMax F x`. -/
theorem exists_tsum_exp_mul_le_boxMax (d : ℕ) : ∃ K : ℝ, 0 < K ∧
    ∀ {F : (Fin d → ℤ) → ℝ}, (∀ z, 0 ≤ F z) → Summable F → ∀ {σ : ℝ}, 1 ≤ σ →
      ∀ x : Fin d → ℤ, ∑' z : Fin d → ℤ, ENNReal.ofReal
        (Real.exp (-(∑ i, |((z i : ℤ) : ℝ)|) / σ) * F (x + z)) ≤
      ENNReal.ofReal (K * σ ^ d * boxMax F x) := by
  classical
  set A : ℝ := Real.exp 1 * ((d + 1).factorial * 2 ^ (d + 1)) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨2 * 6 ^ d * A, by positivity, fun {F} hF hFs {σ} hσ x => ?_⟩
  have hσ0 : 0 < σ := by linarith
  set ρ : ℕ := ⌈σ⌉₊ with hρ
  have hρσ : σ ≤ ρ := Nat.le_ceil σ
  have hρ2 : (ρ : ℝ) ≤ 2 * σ := by
    have := Nat.ceil_lt_add_one hσ0.le
    linarith
  have hρ1 : (1 : ℝ) ≤ ρ := le_trans hσ hρσ
  set e : ℕ → ℝ := fun j => Real.exp (1 - 2 ^ j / 2) with he
  set B : ℕ → Finset (Fin d → ℤ) := fun j => supBox 0 (ρ * 2 ^ j) with hB
  have hM0 := boxMax_nonneg hF hFs x
  -- every point lies in a layer whose weight dominates the kernel
  have hlayer : ∀ z : Fin d → ℤ, ∃ j, z ∈ B j ∧
      Real.exp (-(∑ i, |((z i : ℤ) : ℝ)|) / σ) ≤ e j := by
    intro z
    set n : ℕ := supNorm z with hn
    have hex : ∃ j : ℕ, n ≤ ρ * 2 ^ j := by
      refine ⟨n, ?_⟩
      have h1 : n < 2 ^ n := Nat.lt_two_pow_self
      have h2 : 1 ≤ ρ := by exact_mod_cast hρ1
      nlinarith
    refine ⟨Nat.find hex, ?_, ?_⟩
    · rw [hB, mem_supBox]
      intro i
      have hn' := Nat.find_spec hex
      simp only [Pi.zero_apply, sub_zero]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (natAbs_le_supNorm z i).trans hn'
    · rw [he]
      refine Real.exp_le_exp.2 ?_
      have hz1 : (n : ℝ) ≤ ∑ i, |((z i : ℤ) : ℝ)| := supNorm_le_sum_abs z
      have hS0 : 0 ≤ ∑ i, |((z i : ℤ) : ℝ)| := Finset.sum_nonneg fun i _ => abs_nonneg _
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero]
        have : 0 ≤ (∑ i, |((z i : ℤ) : ℝ)|) / σ := by positivity
        rw [neg_div]
        linarith
      · obtain ⟨j', hj'⟩ : ∃ j', Nat.find hex = j' + 1 := ⟨Nat.find hex - 1, by omega⟩
        have hmin := Nat.find_min hex (show j' < Nat.find hex by omega)
        have hlt : (ρ : ℝ) * 2 ^ j' < n := by exact_mod_cast not_le.1 hmin
        have hge : (2 : ℝ) ^ j' ≤ (∑ i, |((z i : ℤ) : ℝ)|) / σ := by
          rw [le_div_iff₀ hσ0]
          nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) j']
        rw [hj', pow_succ, neg_div]
        linarith
  -- the layer decomposition
  have hpt : ∀ z : Fin d → ℤ, ENNReal.ofReal
      (Real.exp (-(∑ i, |((z i : ℤ) : ℝ)|) / σ) * F (x + z)) ≤
      ∑' j, if z ∈ B j then ENNReal.ofReal (e j * F (x + z)) else 0 := by
    intro z
    obtain ⟨j, hjB, hje⟩ := hlayer z
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [if_pos hjB]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hje (hF _))
  have hbox : ∀ j, (∑' z, if z ∈ B j then ENNReal.ofReal (e j * F (x + z)) else 0) ≤
      ENNReal.ofReal (e j * (2 * (ρ * 2 ^ j : ℕ) + 1) ^ d * boxMax F x) := by
    intro j
    rw [tsum_eq_sum (s := B j) fun z hz => if_neg hz, Finset.sum_congr rfl fun z hz => if_pos hz,
      ← ENNReal.ofReal_sum_of_nonneg fun z _ => mul_nonneg (Real.exp_pos _).le (hF _),
      ← Finset.mul_sum, hB, sum_supBox_add]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have h := boxAvg_le_boxMax hF hFs x (ρ * 2 ^ j)
    have hpos : (0 : ℝ) < ((2 * (ρ * 2 ^ j) + 1) ^ d : ℕ) := by positivity
    rw [boxAvg, div_le_iff₀ hpos] at h
    push_cast at h ⊢
    linarith
  have hgeom : ∀ j : ℕ, e j * (2 * (ρ * 2 ^ j : ℕ) + 1) ^ d ≤
      3 ^ d * (ρ : ℝ) ^ d * (A * (1 / 2) ^ j) := by
    intro j
    have h1 : (2 * ((ρ * 2 ^ j : ℕ) : ℝ) + 1) ^ d ≤ 3 ^ d * (ρ : ℝ) ^ d * ((2 : ℝ) ^ j) ^ d := by
      have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      rw [← mul_pow, ← mul_pow]
      push_cast
      exact pow_le_pow_left₀ (by positivity)
        (by nlinarith [mul_le_mul hρ1 h2j zero_le_one (by linarith)]) d
    calc e j * (2 * ((ρ * 2 ^ j : ℕ) : ℝ) + 1) ^ d
        ≤ e j * (3 ^ d * (ρ : ℝ) ^ d * ((2 : ℝ) ^ j) ^ d) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 3 ^ d * (ρ : ℝ) ^ d * (e j * ((2 : ℝ) ^ j) ^ d) := by ring
      _ ≤ 3 ^ d * (ρ : ℝ) ^ d * (A * (1 / 2) ^ j) :=
          mul_le_mul_of_nonneg_left (exp_layer_mul_pow_le d j) (by positivity)
  calc ∑' z, ENNReal.ofReal (Real.exp (-(∑ i, |((z i : ℤ) : ℝ)|) / σ) * F (x + z))
      ≤ ∑' z, ∑' j, if z ∈ B j then ENNReal.ofReal (e j * F (x + z)) else 0 :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' j, ∑' z, if z ∈ B j then ENNReal.ofReal (e j * F (x + z)) else 0 :=
        ENNReal.tsum_comm
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (e j * (2 * (ρ * 2 ^ j : ℕ) + 1) ^ d * boxMax F x) :=
        ENNReal.tsum_le_tsum hbox
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (3 ^ d * (ρ : ℝ) ^ d * A * boxMax F x * (1 / 2) ^ j) :=
        ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (by
          have := mul_le_mul_of_nonneg_right (hgeom j) hM0
          linarith)
    _ = ENNReal.ofReal (3 ^ d * (ρ : ℝ) ^ d * A * boxMax F x * 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          ((summable_geometric_two).mul_left _), tsum_mul_left, tsum_geometric_two]
    _ ≤ ENNReal.ofReal (2 * 6 ^ d * A * σ ^ d * boxMax F x) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hρd : (ρ : ℝ) ^ d ≤ 2 ^ d * σ ^ d := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hρ2 d
        have h6 : (6 : ℝ) ^ d = 3 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
        have hc : 0 ≤ 3 ^ d * A * boxMax F x * 2 := by positivity
        calc 3 ^ d * (ρ : ℝ) ^ d * A * boxMax F x * 2
            = (ρ : ℝ) ^ d * (3 ^ d * A * boxMax F x * 2) :=
              by ring
          _ ≤ 2 ^ d * σ ^ d * (3 ^ d * A * boxMax F x * 2) := mul_le_mul_of_nonneg_right hρd hc
          _ = 2 * 6 ^ d * A * σ ^ d * boxMax F x := by rw [h6]; ring

/-- **The weighted heat maximal bound**: for `0 ≤ s ≤ T`, `0 ≤ a ≤ 1/6`, `a max(√T, 1) ≤ 1` and
`G ≥ 0` summable, `Σ_y Φ_s(x, y) e^{a|y - x|₁} G(y) ≤ C boxMax G x`. -/
theorem exists_heat_le_boxMax [NeZero d] : ∃ C : ℝ, 0 < C ∧ ∀ T a : ℝ, 0 ≤ T → 0 ≤ a →
    a ≤ 1 / 6 → a * max (Real.sqrt T) 1 ≤ 1 → ∀ s : ℝ, 0 ≤ s → s ≤ T → ∀ G : Vertex d → ℝ,
      (∀ z, 0 ≤ G z) → Summable G → ∀ x : Vertex d,
        ∑' y, ENNReal.ofReal (zdHeat d s x y *
            Real.exp (a * ∑ i, |(((y - x) i : ℤ) : ℝ)|) * G y) ≤
          ENNReal.ofReal (C * boxMax G x) := by
  obtain ⟨C₁, hC₁, h⟩ := exists_zdHeat_mul_exp_le (d := d)
  obtain ⟨K, hK, hKb⟩ := exists_tsum_exp_mul_le_boxMax d
  refine ⟨C₁ ^ d * K, by positivity, fun T a hT ha0 ha6 haT s hs hsT G hG hGs x => ?_⟩
  set σ := max (Real.sqrt s) 1 with hσ
  have hσ1 : 1 ≤ σ := le_max_right _ _
  have hσ0 : 0 < σ := by linarith
  have haσ : a * σ ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ ha0) haT
    exact max_le_max (Real.sqrt_le_sqrt hsT) le_rfl
  have hpt : ∀ y, ENNReal.ofReal (zdHeat d s x y *
      Real.exp (a * ∑ i, |(((y - x) i : ℤ) : ℝ)|) * G y) ≤
      ENNReal.ofReal (C₁ ^ d / σ ^ d) * ENNReal.ofReal (Real.exp
        (-(∑ i, |(((y - x) i : ℤ) : ℝ)|) / σ) * G (x + (y - x))) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), add_sub_cancel, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (h s hs a ha0 ha6 haσ x y) (hG y))
  calc ∑' y, ENNReal.ofReal (zdHeat d s x y *
          Real.exp (a * ∑ i, |(((y - x) i : ℤ) : ℝ)|) * G y)
      ≤ ∑' y, ENNReal.ofReal (C₁ ^ d / σ ^ d) * ENNReal.ofReal (Real.exp
          (-(∑ i, |(((y - x) i : ℤ) : ℝ)|) / σ) * G (x + (y - x))) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (C₁ ^ d / σ ^ d) * ∑' z : Fin d → ℤ, ENNReal.ofReal (Real.exp
          (-(∑ i, |((z i : ℤ) : ℝ)|) / σ) * G (x + z)) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact (Equiv.subRight x).tsum_eq (fun z : Fin d → ℤ => ENNReal.ofReal (Real.exp
          (-(∑ i, |((z i : ℤ) : ℝ)|) / σ) * G (x + z)))
    _ ≤ ENNReal.ofReal (C₁ ^ d / σ ^ d) * ENNReal.ofReal (K * σ ^ d * boxMax G x) :=
        mul_le_mul_of_nonneg_left (hKb hG hGs hσ1 x) zero_le
    _ = ENNReal.ofReal (C₁ ^ d * K * boxMax G x) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end Rigidity.Poincare.GeneralDim

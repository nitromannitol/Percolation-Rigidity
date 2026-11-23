import Rigidity.Proofs.Corrector.DarioMoments
import Rigidity.Proofs.Corrector.PlanarCorrectorQuantitative

/-!
# Boxes, box averages and moments (for Dario, §5)

The proof of Dario's Theorem 1 (*Optimal corrector estimates on percolation clusters*, §5,
Steps 1–4) compares the value of a random field at a point with its averages over the boxes
`c + □_m` of side `3^m` and with the double averages
`3^{-2dm} Σ_{y ∈ □_m} Σ_{z ∈ c + y + □_m}`, in the `L^q(P)` norms. This file collects the box
combinatorics (cardinality `9^m`, translation, reflection, inclusion `x + □_m ⊆ □_{m+2}` for
`|x|_∞ < 3^{m+1}`) and the inequalities on the moments `E[|f|^q]`, written as lower Lebesgue
integrals, that the argument uses: Jensen's inequality for box averages and the bound
`(a + b + c)^q ≤ 3^q (a^q + b^q + c^q)`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation
open scoped ENNReal

/-- The box `c + □_m` of side `3^m` centred at `c`. -/
noncomputable def boxAt (c : Vertex 2) (m : ℕ) : Finset (Vertex 2) :=
  latticeBox c (3 ^ m / 2)

theorem mem_boxAt {c z : Vertex 2} {m : ℕ} :
    z ∈ boxAt c m ↔ ∀ i, c i - ((3 ^ m / 2 : ℕ) : ℤ) ≤ z i ∧ z i ≤ c i + ((3 ^ m / 2 : ℕ) : ℤ) := by
  simp only [boxAt, latticeBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem card_boxAt (c : Vertex 2) (m : ℕ) : (boxAt c m).card = 9 ^ m := by
  rw [boxAt, card_latticeBox]
  have hodd : Odd (3 ^ m) := Odd.pow (by decide)
  rw [Nat.two_mul_div_two_add_one_of_odd hodd, ← pow_mul, show (9 : ℕ) = 3 ^ 2 by norm_num,
    ← pow_mul, mul_comm]

theorem card_boxAt_real (c : Vertex 2) (m : ℕ) : ((boxAt c m).card : ℝ) = 9 ^ m := by
  rw [card_boxAt]
  push_cast
  rfl

theorem boxAt_nonempty (c : Vertex 2) (m : ℕ) : (boxAt c m).Nonempty := by
  rw [← Finset.card_pos, card_boxAt]
  positivity

theorem self_mem_boxAt (c : Vertex 2) (m : ℕ) : c ∈ boxAt c m := by
  rw [mem_boxAt]
  intro i
  have h0 : (0 : ℤ) ≤ ((3 ^ m / 2 : ℕ) : ℤ) := Nat.cast_nonneg _
  constructor <;> linarith

/-- Translating the summation variable translates the box. -/
theorem sum_boxAt_add {M : Type*} [AddCommMonoid M] (f : Vertex 2 → M) (c y : Vertex 2) (m : ℕ) :
    ∑ w ∈ boxAt c m, f (w + y) = ∑ z ∈ boxAt (c + y) m, f z := by
  refine Finset.sum_nbij' (fun w => w + y) (fun z => z - y) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [mem_boxAt] at hw ⊢
    intro i
    have := hw i
    simp only [Pi.add_apply]
    constructor <;> linarith [this.1, this.2]
  · intro z hz
    rw [mem_boxAt] at hz ⊢
    intro i
    have := hz i
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · intro w _
    simp
  · intro z _
    simp
  · intro _ _
    rfl

/-- The box `□_m` centred at the origin is symmetric. -/
theorem sum_boxAt_neg {M : Type*} [AddCommMonoid M] (f : Vertex 2 → M) (m : ℕ) :
    ∑ y ∈ boxAt 0 m, f (-y) = ∑ z ∈ boxAt 0 m, f z := by
  refine Finset.sum_nbij' (fun y => -y) (fun z => -z) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [mem_boxAt] at hy ⊢
    intro i
    have := hy i
    simp only [Pi.zero_apply, Pi.neg_apply, zero_sub, zero_add] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · intro z hz
    rw [mem_boxAt] at hz ⊢
    intro i
    have := hz i
    simp only [Pi.zero_apply, Pi.neg_apply, zero_sub, zero_add] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · intro y _
    simp
  · intro z _
    simp
  · intro _ _
    rfl

theorem boxAt_subset_boxAt_add_two (m : ℕ) : boxAt 0 m ⊆ boxAt 0 (m + 2) := by
  intro z hz
  rw [mem_boxAt] at hz ⊢
  intro i
  have h := hz i
  have e : 3 ^ (m + 2) = 9 * 3 ^ m := by ring
  rw [e]
  simp only [Pi.zero_apply, zero_sub, zero_add] at h ⊢
  generalize 3 ^ m = t at *
  omega

/-- `x + □_m ⊆ □_{m+2}` when `|x|_∞ < 3^{m+1}`. -/
theorem boxAt_subset_of_lt {x : Vertex 2} {m : ℕ} (hx : ∀ i, |x i| < ((3 ^ (m + 1) : ℕ) : ℤ)) :
    boxAt x m ⊆ boxAt 0 (m + 2) := by
  intro z hz
  rw [mem_boxAt] at hz ⊢
  intro i
  have h := hz i
  have hxi := abs_lt.1 (hx i)
  have e1 : 3 ^ (m + 2) = 9 * 3 ^ m := by ring
  have e2 : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
  rw [e1]
  rw [e2] at hxi
  simp only [Pi.zero_apply, zero_sub, zero_add]
  generalize 3 ^ m = t at *
  omega

/-- The average of a field over the box `c + □_m`. -/
noncomputable def boxAvg (G : Vertex 2 → Configuration 2 → ℝ) (c : Vertex 2) (m : ℕ)
    (ω : Configuration 2) : ℝ :=
  (∑ z ∈ boxAt c m, G z ω) / 9 ^ m

/-- The double average `3^{-2dm} Σ_{y ∈ □_m} Σ_{z ∈ c + y + □_m} G(z)`. -/
noncomputable def boxAvg2 (G : Vertex 2 → Configuration 2 → ℝ) (c : Vertex 2) (m : ℕ)
    (ω : Configuration 2) : ℝ :=
  (∑ y ∈ boxAt 0 m, boxAvg G (c + y) m ω) / 9 ^ m

theorem measurable_boxAvg {G : Vertex 2 → Configuration 2 → ℝ} (hG : ∀ z, Measurable (G z))
    (c : Vertex 2) (m : ℕ) : Measurable (boxAvg G c m) :=
  (Finset.measurable_sum _ fun z _ => hG z).div_const _

theorem measurable_boxAvg2 {G : Vertex 2 → Configuration 2 → ℝ} (hG : ∀ z, Measurable (G z))
    (c : Vertex 2) (m : ℕ) : Measurable (boxAvg2 G c m) :=
  (Finset.measurable_sum _ fun _ _ => measurable_boxAvg hG _ m).div_const _

/-- A value minus a box average is the average of the differences. -/
theorem sub_boxAvg_eq (G : Vertex 2 → Configuration 2 → ℝ) (a : ℝ) (c : Vertex 2) (m : ℕ)
    (ω : Configuration 2) :
    a - boxAvg G c m ω = (∑ z ∈ boxAt c m, (a - G z ω)) / 9 ^ m := by
  rw [boxAvg, Finset.sum_sub_distrib, Finset.sum_const, card_boxAt, nsmul_eq_mul]
  push_cast
  field_simp

/-- A value minus a double average is the average of the values minus the box averages. -/
theorem sub_boxAvg2_eq (G : Vertex 2 → Configuration 2 → ℝ) (a : ℝ) (c : Vertex 2) (m : ℕ)
    (ω : Configuration 2) :
    a - boxAvg2 G c m ω = (∑ y ∈ boxAt 0 m, (a - boxAvg G (c + y) m ω)) / 9 ^ m := by
  rw [boxAvg2, Finset.sum_sub_distrib, Finset.sum_const, card_boxAt, nsmul_eq_mul]
  push_cast
  field_simp

/-! ### Real inequalities -/

/-- Jensen's inequality for averages: `|(Σ_S a_i)/N|^q ≤ (Σ_S |a_i|^q)/N`, `N = #S > 0`, `q ≥ 1`. -/
theorem abs_sum_div_rpow_le {ι : Type*} (S : Finset ι) (a : ι → ℝ) {N : ℝ}
    (hN : (S.card : ℝ) = N) (hNpos : 0 < N) {q : ℝ} (hq : 1 ≤ q) :
    |(∑ i ∈ S, a i) / N| ^ q ≤ (∑ i ∈ S, |a i| ^ q) / N := by
  have hw : ∀ i ∈ S, (0 : ℝ) ≤ 1 / N := fun _ _ => by positivity
  have hw' : ∑ _i ∈ S, (1 / N) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hN]
    field_simp
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow S (fun _ => 1 / N) (fun i => |a i|) hw hw'
    (fun i _ => abs_nonneg _) hq
  have habs : |(∑ i ∈ S, a i) / N| ≤ ∑ i ∈ S, 1 / N * |a i| := by
    rw [abs_div, abs_of_pos hNpos]
    calc |∑ i ∈ S, a i| / N ≤ (∑ i ∈ S, |a i|) / N :=
          div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hNpos.le
      _ = ∑ i ∈ S, 1 / N * |a i| := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
  calc |(∑ i ∈ S, a i) / N| ^ q ≤ (∑ i ∈ S, 1 / N * |a i|) ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) habs (by linarith)
    _ ≤ ∑ i ∈ S, 1 / N * |a i| ^ q := hJ
    _ = (∑ i ∈ S, |a i| ^ q) / N := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring

theorem add_rpow_le_two {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ q ≤ (2 * b) ^ q := Real.rpow_le_rpow (by positivity) (by linarith) hq
      _ = 2 ^ q * b ^ q := Real.mul_rpow (by norm_num) hb
      _ ≤ 2 ^ q * (a ^ q + b ^ q) := by
          have := Real.rpow_nonneg ha q
          have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
          nlinarith
  · calc (a + b) ^ q ≤ (2 * a) ^ q := Real.rpow_le_rpow (by positivity) (by linarith) hq
      _ = 2 ^ q * a ^ q := Real.mul_rpow (by norm_num) ha
      _ ≤ 2 ^ q * (a ^ q + b ^ q) := by
          have := Real.rpow_nonneg hb q
          have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
          nlinarith

theorem add_rpow_le_three {a b c q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q) :
    (a + b + c) ^ q ≤ 3 ^ q * (a ^ q + b ^ q + c ^ q) := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = max a (max b c) := ⟨_, rfl⟩
  have hM : a + b + c ≤ 3 * M := by
    have h1 : a ≤ M := by rw [hMdef]; exact le_max_left _ _
    have h2 : b ≤ M := by rw [hMdef]; exact (le_max_left _ _).trans (le_max_right _ _)
    have h3 : c ≤ M := by rw [hMdef]; exact (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hMq : M ^ q ≤ a ^ q + b ^ q + c ^ q := by
    have ha' := Real.rpow_nonneg ha q
    have hb' := Real.rpow_nonneg hb q
    have hc' := Real.rpow_nonneg hc q
    rcases max_choice a (max b c) with h | h <;> rw [hMdef, h]
    · linarith
    · rcases max_choice b c with h' | h' <;> rw [h'] <;> linarith
  have hM0 : 0 ≤ M := by rw [hMdef]; exact ha.trans (le_max_left _ _)
  calc (a + b + c) ^ q ≤ (3 * M) ^ q := Real.rpow_le_rpow (by positivity) hM hq
    _ = 3 ^ q * M ^ q := Real.mul_rpow (by norm_num) hM0
    _ ≤ 3 ^ q * (a ^ q + b ^ q + c ^ q) :=
        mul_le_mul_of_nonneg_left hMq (by positivity)

/-! ### Moments as lower integrals -/

variable {p : unitInterval}

/-- The moment `E[|f|^q]` as a lower Lebesgue integral. -/
noncomputable def mom (p : unitInterval) (f : Configuration 2 → ℝ) (q : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|f ω| ^ q) ∂latticeBondLaw 2 p

theorem measurable_ofReal_abs_rpow {f : Configuration 2 → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable fun ω => ENNReal.ofReal (|f ω| ^ q) :=
  (hf.abs.pow_const q).ennreal_ofReal

theorem mom_mono_ae {f g : Configuration 2 → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ᵐ ω ∂latticeBondLaw 2 p, |f ω| ≤ |g ω|) : mom p f q ≤ mom p g q := by
  refine lintegral_mono_ae ?_
  filter_upwards [h] with ω hω
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) hω hq)

/-- `E|f|^q ≤ 2^q (E|g₁|^q + E|g₂|^q)` when `|f| ≤ |g₁| + |g₂|`. -/
theorem mom_le_two {f g₁ g₂ : Configuration 2 → ℝ} {q : ℝ} (hq : 0 ≤ q) (h₁ : Measurable g₁)
    (h : ∀ᵐ ω ∂latticeBondLaw 2 p, |f ω| ≤ |g₁ ω| + |g₂ ω|) :
    mom p f q ≤ ENNReal.ofReal (2 ^ q) * (mom p g₁ q + mom p g₂ q) := by
  calc mom p f q ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ q) *
        (ENNReal.ofReal (|g₁ ω| ^ q) + ENNReal.ofReal (|g₂ ω| ^ q)) ∂latticeBondLaw 2 p := by
        refine lintegral_mono_ae ?_
        filter_upwards [h] with ω hω
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        exact (Real.rpow_le_rpow (abs_nonneg _) hω hq).trans
          (add_rpow_le_two (abs_nonneg _) (abs_nonneg _) hq)
    _ = ENNReal.ofReal (2 ^ q) * (mom p g₁ q + mom p g₂ q) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (measurable_ofReal_abs_rpow h₁ q)]
        rfl

/-- `E|f|^q ≤ 3^q (E|g₁|^q + E|g₂|^q + E|g₃|^q)` when `|f| ≤ |g₁| + |g₂| + |g₃|`. -/
theorem mom_le_three {f g₁ g₂ g₃ : Configuration 2 → ℝ} {q : ℝ} (hq : 0 ≤ q) (h₁ : Measurable g₁)
    (h₂ : Measurable g₂) (h : ∀ᵐ ω ∂latticeBondLaw 2 p, |f ω| ≤ |g₁ ω| + |g₂ ω| + |g₃ ω|) :
    mom p f q ≤ ENNReal.ofReal (3 ^ q) * (mom p g₁ q + mom p g₂ q + mom p g₃ q) := by
  calc mom p f q ≤ ∫⁻ ω, ENNReal.ofReal (3 ^ q) *
        (ENNReal.ofReal (|g₁ ω| ^ q) + ENNReal.ofReal (|g₂ ω| ^ q) +
          ENNReal.ofReal (|g₃ ω| ^ q)) ∂latticeBondLaw 2 p := by
        refine lintegral_mono_ae ?_
        filter_upwards [h] with ω hω
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        exact (Real.rpow_le_rpow (abs_nonneg _) hω hq).trans
          (add_rpow_le_three (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hq)
    _ = ENNReal.ofReal (3 ^ q) * (mom p g₁ q + mom p g₂ q + mom p g₃ q) := by
        have hm12 : Measurable fun ω => ENNReal.ofReal (|g₁ ω| ^ q) + ENNReal.ofReal (|g₂ ω| ^ q) :=
          (measurable_ofReal_abs_rpow h₁ q).add (measurable_ofReal_abs_rpow h₂ q)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm12,
          lintegral_add_left (measurable_ofReal_abs_rpow h₁ q)]
        rfl

/-- Jensen for moments of averages: `E|(Σ_S g_i)/N|^q ≤ (Σ_S E|g_i|^q)/N`. -/
theorem mom_sum_div_le {ι : Type*} (S : Finset ι) (g : ι → Configuration 2 → ℝ)
    (hg : ∀ i, Measurable (g i)) {N : ℝ} (hN : (S.card : ℝ) = N) (hNpos : 0 < N) {q : ℝ}
    (hq : 1 ≤ q) :
    mom p (fun ω => (∑ i ∈ S, g i ω) / N) q ≤ (∑ i ∈ S, mom p (g i) q) * ENNReal.ofReal (1 / N) := by
  calc mom p (fun ω => (∑ i ∈ S, g i ω) / N) q
      ≤ ∫⁻ ω, (∑ i ∈ S, ENNReal.ofReal (|g i ω| ^ q)) * ENNReal.ofReal (1 / N)
          ∂latticeBondLaw 2 p := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
          ← ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        refine (abs_sum_div_rpow_le S (fun i => g i ω) hN hNpos hq).trans (le_of_eq ?_)
        ring
    _ = (∑ i ∈ S, mom p (g i) q) * ENNReal.ofReal (1 / N) := by
        rw [lintegral_mul_const _ (Finset.measurable_sum _ fun i _ =>
          measurable_ofReal_abs_rpow (hg i) q), lintegral_finsetSum _ fun i _ =>
          measurable_ofReal_abs_rpow (hg i) q]
        rfl

/-- If every term has moment at most `b`, so does the average. -/
theorem mom_sum_div_le_of_le {ι : Type*} (S : Finset ι) (g : ι → Configuration 2 → ℝ)
    (hg : ∀ i, Measurable (g i)) {N : ℝ} (hN : (S.card : ℝ) = N) (hNpos : 0 < N) {q : ℝ}
    (hq : 1 ≤ q) {b : ℝ≥0∞} (hb : ∀ i ∈ S, mom p (g i) q ≤ b) :
    mom p (fun ω => (∑ i ∈ S, g i ω) / N) q ≤ b := by
  refine (mom_sum_div_le S g hg hN hNpos hq).trans ?_
  calc (∑ i ∈ S, mom p (g i) q) * ENNReal.ofReal (1 / N)
      ≤ (∑ _i ∈ S, b) * ENNReal.ofReal (1 / N) := by gcongr with i hi; exact hb i hi
    _ = b := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm, ← mul_assoc,
          show (S.card : ℝ≥0∞) = ENNReal.ofReal N by rw [← hN, ENNReal.ofReal_natCast],
          ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hNpos.ne',
          ENNReal.ofReal_one, one_mul]

end Rigidity.Corrector

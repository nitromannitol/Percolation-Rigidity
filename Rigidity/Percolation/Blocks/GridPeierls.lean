import Rigidity.Percolation.Blocks.GridCrossing
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real

/-!
# Two-point connections for dependent site percolation on a square of sites

Let the sites of a `K × L` grid be bad with probability at most `ε`, with badness events of
pairwise distant sites satisfying the product bound. A site is attached to the four sides of the
grid if it is attached to the four sides of its quadrant, the band of the quadrant's rows has a
left–right crossing and the band of the quadrant's columns has a top–bottom crossing. Both
crossings fail with probability exponentially small in the side (Peierls bound), so by recursion
on the side every site is attached with probability close to one when `ε` is small, uniformly in
the size of the grid. Two attached sites are joined.
-/

noncomputable section

namespace Rigidity.Percolation

open LQGMetric MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The hypotheses of the Peierls bound for the bad events `B` on the `K × L` grid. -/
def PeierlsHyp (μ : Measure Ω) (K L : ℤ) (B : ℤ × ℤ → Set Ω) (r : ℕ) (ε : ℝ≥0∞) : Prop :=
  (∀ x, percInGrid K L x → μ (B x) ≤ ε) ∧
    ∀ F : Finset (ℤ × ℤ), (∀ x ∈ F, percInGrid K L x) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x)

/-- Pulling the hypotheses back by an injective map preserving distant pairs. -/
theorem PeierlsHyp.comp {μ : Measure Ω} {K L : ℤ} {B : ℤ × ℤ → Set Ω} {r : ℕ} {ε : ℝ≥0∞}
    (h : PeierlsHyp μ K L B r ε) {K' L' : ℤ} (φ : ℤ × ℤ → ℤ × ℤ) (hφ : Function.Injective φ)
    (hgrid : ∀ z, percInGrid K' L' z → percInGrid K L (φ z))
    (hfar : ∀ x y, PercFar r x y → PercFar r (φ x) (φ y)) :
    PeierlsHyp μ K' L' (B ∘ φ) r ε := by
  classical
  refine ⟨fun x hx => h.1 _ (hgrid x hx), fun F hF hfarF => ?_⟩
  have himg := h.2 (F.image φ) (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hgrid x (hF x hx)) (fun x' hx' y' hy' hne => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
      exact hfar x y (hfarF x hx y hy fun h => hne (h ▸ rfl)))
  rw [Finset.set_biInter_finset_image, Finset.prod_image fun x _ y _ h => hφ h] at himg
  exact himg

/-- The hypotheses hold on every sub-grid. -/
theorem PeierlsHyp.mono {μ : Measure Ω} {K L : ℤ} {B : ℤ × ℤ → Set Ω} {r : ℕ} {ε : ℝ≥0∞}
    (h : PeierlsHyp μ K L B r ε) {K' L' : ℤ} (hK : K' ≤ K) (hL : L' ≤ L) :
    PeierlsHyp μ K' L' B r ε :=
  h.comp id Function.injective_id (fun z hz => by unfold percInGrid at hz ⊢; simp only [id]; omega)
    fun _ _ h => h

theorem PeierlsHyp.comp_swap {μ : Measure Ω} {K L : ℤ} {B : ℤ × ℤ → Set Ω} {r : ℕ} {ε : ℝ≥0∞}
    (h : PeierlsHyp μ K L B r ε) : PeierlsHyp μ L K (B ∘ swapSite) r ε :=
  h.comp swapSite (fun x y hxy => by simpa [swapSite, Prod.ext_iff, and_comm] using hxy)
    (fun z hz => by unfold percInGrid swapSite at *; omega)
    (fun x y h => by unfold PercFar swapSite at *; omega)

theorem PeierlsHyp.comp_reflCol {μ : Measure Ω} {K L : ℤ} {B : ℤ × ℤ → Set Ω} {r : ℕ} {ε : ℝ≥0∞}
    (h : PeierlsHyp μ K L B r ε) : PeierlsHyp μ K L (B ∘ reflCol K) r ε :=
  h.comp (reflCol K) (fun x y hxy => by
      simp only [reflCol, Prod.mk.injEq] at hxy
      exact Prod.ext (by omega) hxy.2)
    (fun z hz => by unfold percInGrid reflCol at *; omega)
    (fun x y h => by unfold PercFar reflCol at *; omega)

theorem PeierlsHyp.comp_reflRow {μ : Measure Ω} {K L : ℤ} {B : ℤ × ℤ → Set Ω} {r : ℕ} {ε : ℝ≥0∞}
    (h : PeierlsHyp μ K L B r ε) : PeierlsHyp μ K L (B ∘ reflRow L) r ε :=
  h.comp (reflRow L) (fun x y hxy => by
      simp only [reflRow, Prod.mk.injEq] at hxy
      exact Prod.ext hxy.1 (by omega))
    (fun z hz => by unfold percInGrid reflRow at *; omega)
    (fun x y h => by unfold PercFar reflRow at *; omega)

/-- The Peierls bound for left–right crossings with `θ = 1/128`. -/
theorem peierlsHyp_LR {μ : Measure Ω} {K L : ℤ} {B : ℤ × ℤ → Set Ω} {r : ℕ} {ε : ℝ≥0∞}
    (h : PeierlsHyp μ K L B r ε) (hε : ε ≤ (128 : ℝ≥0∞)⁻¹ ^ ((r + 1) ^ 2)) (hK : 1 ≤ K)
    (hL : 1 ≤ L) :
    μ {ω | ¬ PercGoodLR K L (· ∈ {x | ω ∉ B x})} ≤ K.toNat * ((16 : ℝ≥0∞)⁻¹) ^ L.toNat := by
  have hK' : ((K.toNat : ℕ) : ℤ) = K := Int.toNat_of_nonneg (by omega)
  have hL' : ((L.toNat : ℕ) : ℤ) = L := Int.toNat_of_nonneg (by omega)
  have h8 : 8 * (128 : ℝ≥0∞)⁻¹ = 16⁻¹ := by
    rw [show (128 : ℝ≥0∞) = 8 * 16 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
      ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hθ : 8 * (128 : ℝ≥0∞)⁻¹ ≤ 2⁻¹ := by
    rw [h8]
    exact ENNReal.inv_le_inv.2 (by norm_num)
  have := perc_peierls μ K.toNat L.toNat (by omega) (by omega) B r hθ hε
    (fun x hx => h.1 x (by rw [hK', hL'] at hx; exact hx))
    (fun F hF hfar => h.2 F (fun x hx => by have := hF x hx; rw [hK', hL'] at this; exact this)
      hfar)
  rw [hK', hL', h8] at this
  exact this

/-- The Peierls bound for top–bottom crossings with `θ = 1/128`. -/
theorem peierlsHyp_TB {μ : Measure Ω} {K L : ℤ} {B : ℤ × ℤ → Set Ω} {r : ℕ} {ε : ℝ≥0∞}
    (h : PeierlsHyp μ K L B r ε) (hε : ε ≤ (128 : ℝ≥0∞)⁻¹ ^ ((r + 1) ^ 2)) (hK : 1 ≤ K)
    (hL : 1 ≤ L) :
    μ {ω | ¬ GridTB K L {x | ω ∉ B x}} ≤ L.toNat * ((16 : ℝ≥0∞)⁻¹) ^ K.toNat := by
  refine le_trans (measure_mono ?_) (peierlsHyp_LR h.comp_swap hε hL hK)
  intro ω hω hLR
  apply hω
  obtain ⟨c, d, hc, hd, hcg, hcG, hcd⟩ := hLR
  have hconn : GridConn L K (swapSite ⁻¹' {x | ω ∉ B x}) c d := ⟨hcg, hcG, hcd⟩
  exact ⟨swapSite c, swapSite d, hc, hd, gridConn_swap hconn⟩

/-- An `ℝ≥0∞` bound by a finite quantity gives the real bound. -/
theorem measureReal_le_of_le {μ : Measure Ω} {s : Set Ω} {b : ℝ≥0∞} (h : μ s ≤ b) (hb : b ≠ ⊤) :
    μ.real s ≤ b.toReal :=
  ENNReal.toReal_mono hb h

/-- The crossing failure bound at side `n`. -/
theorem cross_bound_le (n : ℕ) {K L : ℤ} (hK : K ≤ n + 1)
    (hL : ((n - n / 2 : ℕ) : ℤ) ≤ L) :
    ((K.toNat : ℝ≥0∞) * ((16 : ℝ≥0∞)⁻¹) ^ L.toNat).toReal ≤ (1 / 2 : ℝ) ^ n := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have h16 : ((16 : ℝ≥0∞)).toReal = 16 := by norm_num
  rw [h16]
  have hKr : ((K.toNat : ℕ) : ℝ) ≤ n + 1 := by
    have : K.toNat ≤ n + 1 := by omega
    exact_mod_cast this
  have hpow : ((16 : ℝ)⁻¹) ^ L.toNat ≤ ((1 / 4 : ℝ)) ^ n := by
    have h1 : ((16 : ℝ)⁻¹) ^ L.toNat = ((1 / 4 : ℝ)) ^ (2 * L.toNat) := by
      rw [pow_mul]
      norm_num
    rw [h1]
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    omega
  have h2n : ((n + 1 : ℕ) : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  calc ((K.toNat : ℕ) : ℝ) * ((16 : ℝ)⁻¹) ^ L.toNat ≤ (n + 1) * ((1 / 4 : ℝ)) ^ n :=
        mul_le_mul hKr hpow (by positivity) (by positivity)
    _ ≤ 2 ^ n * ((1 / 4 : ℝ)) ^ n := by
        push_cast at h2n
        exact mul_le_mul_of_nonneg_right h2n (by positivity)
    _ = (1 / 2 : ℝ) ^ n := by
        rw [← mul_pow]
        norm_num

/-! ### The recursion -/

/-- The error budget of the recursion. -/
def attBudget (n₀ n : ℕ) : ℝ := if n ≤ n₀ then 0 else 4 * (1 / 2 : ℝ) ^ n₀ - 4 * (1 / 2 : ℝ) ^ n

theorem attBudget_le (n₀ n : ℕ) : attBudget n₀ n ≤ 4 * (1 / 2 : ℝ) ^ n₀ := by
  unfold attBudget
  split_ifs
  · positivity
  · have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    linarith

theorem attBudget_step {n₀ n n' : ℕ} (hn : n₀ < n) (hn' : n' < n) :
    attBudget n₀ n' + 2 * (1 / 2 : ℝ) ^ n ≤ attBudget n₀ n := by
  unfold attBudget
  have h1 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (n₀ + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (n' + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn'
  rw [pow_succ] at h1 h2
  have hnn : ¬ n ≤ n₀ := by omega
  simp only [hnn, ↓reduceIte]
  have p1 : 0 ≤ (1 / 2 : ℝ) ^ n₀ := by positivity
  have p2 : 0 ≤ (1 / 2 : ℝ) ^ n' := by positivity
  split_ifs
  · linarith
  · linarith

/-- The sites of the grid as a finite set. -/
def gridFinset (K L : ℤ) : Finset (ℤ × ℤ) := Finset.Ico 0 K ×ˢ Finset.Ico 0 L

theorem mem_gridFinset {K L : ℤ} {z : ℤ × ℤ} : z ∈ gridFinset K L ↔ percInGrid K L z := by
  simp only [gridFinset, Finset.mem_product, Finset.mem_Ico, percInGrid]
  tauto

/-- **Attachment with high probability.** On a grid of sides between `n` and `n + 1`, every site
is attached to the four sides except with probability at most
`(n₀ + 1)² ε + attBudget n₀ n`. -/
theorem att4_prob_le {μ : Measure Ω} [IsProbabilityMeasure μ] {r : ℕ} {ε : ℝ≥0∞}
    (hε : ε ≤ (128 : ℝ≥0∞)⁻¹ ^ ((r + 1) ^ 2)) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    ∀ n : ℕ, ∀ K L : ℤ, (n : ℤ) ≤ K → K ≤ n + 1 → (n : ℤ) ≤ L → L ≤ n + 1 → 1 ≤ K → 1 ≤ L →
      ∀ B : ℤ × ℤ → Set Ω, PeierlsHyp μ K L B r ε → ∀ a, percInGrid K L a →
        μ.real {ω | ¬ Att4 K L {x | ω ∉ B x} a} ≤
          ((n₀ + 1 : ℕ) ^ 2 : ℝ) * ε.toReal + attBudget n₀ n := by
  have hεtop : ε ≠ ⊤ := ne_top_of_le_ne_top (by simp) hε
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L hK1 hK2 hL1 hL2 hK hL B hB a ha
  by_cases hn : n ≤ n₀
  · have hsub : {ω | ¬ Att4 K L {x | ω ∉ B x} a} ⊆ ⋃ x ∈ gridFinset K L, B x := by
      intro ω hω
      by_contra hnot
      apply hω
      exact att4_of_all (G := {x | ω ∉ B x})
        (fun z hz hzB => hnot (Set.mem_biUnion (mem_gridFinset.2 hz) hzB)) ha
    have hcard : ((gridFinset K L).card : ℝ) ≤ ((n₀ + 1 : ℕ) ^ 2 : ℝ) := by
      have : (gridFinset K L).card ≤ (n₀ + 1) ^ 2 := by
        simp only [gridFinset, Finset.card_product, Int.card_Ico, sub_zero]
        have h1 : K.toNat ≤ n₀ + 1 := by omega
        have h2 : L.toNat ≤ n₀ + 1 := by omega
        calc K.toNat * L.toNat ≤ (n₀ + 1) * (n₀ + 1) := Nat.mul_le_mul h1 h2
          _ = (n₀ + 1) ^ 2 := by ring
      exact_mod_cast this
    rw [show attBudget n₀ n = 0 by simp [attBudget, hn], add_zero]
    calc μ.real {ω | ¬ Att4 K L {x | ω ∉ B x} a} ≤ μ.real (⋃ x ∈ gridFinset K L, B x) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ x ∈ gridFinset K L, μ.real (B x) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _x ∈ gridFinset K L, ε.toReal := Finset.sum_le_sum fun x hx =>
          measureReal_le_of_le (hB.1 x (mem_gridFinset.1 hx)) hεtop
      _ = (gridFinset K L).card * ε.toReal := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard ENNReal.toReal_nonneg
  · push Not at hn
    set K' := K - K / 2 with hK'
    set L' := L - L / 2 with hL'
    set n' := n - n / 2 with hn'
    have hn'n : n' < n := by omega
    have hK'1 : (n' : ℤ) ≤ K' := by omega
    have hK'2 : K' ≤ n' + 1 := by omega
    have hL'1 : (n' : ℤ) ≤ L' := by omega
    have hL'2 : L' ≤ n' + 1 := by omega
    have hK'K : K' ≤ K := by omega
    have hL'L : L' ≤ L := by omega
    -- reduce to a site of the lower left quadrant
    obtain ⟨a₁, B₁, hB₁, ha₁, ha₁K, ha₁L, hsub⟩ : ∃ (a₁ : ℤ × ℤ) (B₁ : ℤ × ℤ → Set Ω),
        PeierlsHyp μ K L B₁ r ε ∧ percInGrid K L a₁ ∧ a₁.1 < K' ∧ a₁.2 < L' ∧
        {ω | ¬ Att4 K L {x | ω ∉ B x} a} ⊆ {ω | ¬ Att4 K L {x | ω ∉ B₁ x} a₁} := by
      have hga := ha
      unfold percInGrid at hga
      by_cases h1 : a.1 < K'
      · by_cases h2 : a.2 < L'
        · exact ⟨a, B, hB, ha, h1, h2, le_rfl⟩
        · refine ⟨reflRow L a, B ∘ reflRow L, hB.comp_reflRow, ?_, ?_, ?_, ?_⟩
          · unfold percInGrid reflRow
            simp only
            omega
          · simp only [reflRow]
            omega
          · simp only [reflRow]
            omega
          · intro ω hω hatt
            exact hω (att4_reflRow hatt)
      · by_cases h2 : a.2 < L'
        · refine ⟨reflCol K a, B ∘ reflCol K, hB.comp_reflCol, ?_, ?_, ?_, ?_⟩
          · unfold percInGrid reflCol
            simp only
            omega
          · simp only [reflCol]
            omega
          · simp only [reflCol]
            omega
          · intro ω hω hatt
            exact hω (att4_reflCol hatt)
        · refine ⟨reflRow L (reflCol K a), B ∘ reflCol K ∘ reflRow L,
            hB.comp_reflCol.comp_reflRow, ?_, ?_, ?_, ?_⟩
          · unfold percInGrid reflRow reflCol
            simp only
            omega
          · simp only [reflRow, reflCol]
            omega
          · simp only [reflRow, reflCol]
            omega
          · intro ω hω hatt
            exact hω (att4_reflCol (att4_reflRow hatt))
    set G₁ : Ω → Set (ℤ × ℤ) := fun ω => {x | ω ∉ B₁ x} with hG₁
    have hcore : {ω | ¬ Att4 K L (G₁ ω) a₁} ⊆ ({ω | ¬ Att4 K' L' (G₁ ω) a₁} ∪
        {ω | ¬ PercGoodLR K L' (· ∈ G₁ ω)}) ∪ {ω | ¬ GridTB K' L (G₁ ω)} := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
      exact hω (att4_of_quadrant hK'K hL'L hnot.1.1 hnot.1.2 hnot.2)
    have ha₁' : percInGrid K' L' a₁ := by
      unfold percInGrid at ha₁ ⊢
      omega
    have hIH := ih n' hn'n K' L' hK'1 hK'2 hL'1 hL'2 (by omega) (by omega) B₁
      (hB₁.mono hK'K hL'L) a₁ ha₁'
    have hfin : ∀ (M N : ℤ), (M.toNat : ℝ≥0∞) * ((16 : ℝ≥0∞)⁻¹) ^ N.toNat ≠ ⊤ := fun M N =>
      ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp))
    have hLR : μ.real {ω | ¬ PercGoodLR K L' (· ∈ G₁ ω)} ≤ (1 / 2 : ℝ) ^ n :=
      (measureReal_le_of_le (peierlsHyp_LR (hB₁.mono le_rfl hL'L) hε hK (by omega))
        (hfin _ _)).trans (cross_bound_le n hK2 (by omega))
    have hTB : μ.real {ω | ¬ GridTB K' L (G₁ ω)} ≤ (1 / 2 : ℝ) ^ n :=
      (measureReal_le_of_le (peierlsHyp_TB (hB₁.mono hK'K le_rfl) hε (by omega) hL)
        (hfin _ _)).trans (cross_bound_le n hL2 (by omega))
    calc μ.real {ω | ¬ Att4 K L {x | ω ∉ B x} a}
        ≤ μ.real {ω | ¬ Att4 K L (G₁ ω) a₁} := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ μ.real (({ω | ¬ Att4 K' L' (G₁ ω) a₁} ∪ {ω | ¬ PercGoodLR K L' (· ∈ G₁ ω)}) ∪
          {ω | ¬ GridTB K' L (G₁ ω)}) := measureReal_mono hcore (measure_ne_top _ _)
      _ ≤ (μ.real {ω | ¬ Att4 K' L' (G₁ ω) a₁} + μ.real {ω | ¬ PercGoodLR K L' (· ∈ G₁ ω)}) +
          μ.real {ω | ¬ GridTB K' L (G₁ ω)} :=
          (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
      _ ≤ (((n₀ + 1 : ℕ) ^ 2 : ℝ) * ε.toReal + attBudget n₀ n') + 2 * (1 / 2 : ℝ) ^ n := by
          linarith
      _ ≤ _ := by
          have := attBudget_step hn hn'n (n₀ := n₀)
          linarith

/-- **Two-point connections on a square of sites.** -/
theorem gridConn_prob_le {μ : Measure Ω} [IsProbabilityMeasure μ] {r : ℕ} {ε : ℝ≥0∞}
    (hε : ε ≤ (128 : ℝ≥0∞)⁻¹ ^ ((r + 1) ^ 2)) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {n : ℕ} {K L : ℤ}
    (hK1 : (n : ℤ) ≤ K) (hK2 : K ≤ n + 1) (hL1 : (n : ℤ) ≤ L) (hL2 : L ≤ n + 1) (hK : 1 ≤ K)
    (hL : 1 ≤ L) {B : ℤ × ℤ → Set Ω} (hB : PeierlsHyp μ K L B r ε) {a b : ℤ × ℤ}
    (ha : percInGrid K L a) (hb : percInGrid K L b) :
    μ.real {ω | ¬ GridConn K L {x | ω ∉ B x} a b} ≤
      2 * (((n₀ + 1 : ℕ) ^ 2 : ℝ) * ε.toReal + 4 * (1 / 2 : ℝ) ^ n₀) := by
  have h1 := att4_prob_le hε hn₀ n K L hK1 hK2 hL1 hL2 hK hL B hB a ha
  have h2 := att4_prob_le hε hn₀ n K L hK1 hK2 hL1 hL2 hK hL B hB b hb
  have h3 := attBudget_le n₀ n
  have hsub : {ω | ¬ GridConn K L {x | ω ∉ B x} a b} ⊆
      {ω | ¬ Att4 K L {x | ω ∉ B x} a} ∪ {ω | ¬ Att4 K L {x | ω ∉ B x} b} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    exact hω (gridConn_of_att4 hnot.1 hnot.2)
  calc _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

end Rigidity.Percolation

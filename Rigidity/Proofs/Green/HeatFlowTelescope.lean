import Rigidity.Proofs.Green.HeatFlowAlgebra

/-!
# The telescoping identity for the heat semigroup over geometric times

For a locally finite graph `G` with degrees at most `D > 0`, square summable `F_0, …, F_J` and times
`s_{j+1} = 3 s_j ≥ 0` with `t = s_J`,

  `P_{t - s_0} F_0 - F_J = Σ_{j < J} P_{t - s_{j+1}} (P_{2 s_j} F_j - F_{j+1})`

(`heatFlowG_telescope`), since `P_{t - s_{j+1}} P_{2 s_j} = P_{t - s_j}`. With `F_j` the Gaussian
kernel normalized on the cluster at the time `s_j`, this is the identity
`p_t^y - G_t = P_{t-s_0} E + Σ_j P_{t-3s_j} D_{s_j}` of the passage from smooth initial data to a
point source in the proof of Theorem 2 of Dario–Gu given here. The `ℓ²` norm `l2norm` satisfies the
triangle inequality (`l2norm_add_le`, `l2norm_sum_le`), so the identity bounds
`‖P_{t - s_0} F_0 - F_J‖` by the sum of the norms of its terms.
-/

open scoped Classical
open Finset

namespace Rigidity.Green

variable {V : Type*}

/-- The `ℓ²` norm `(Σ_x f(x)²)^{1/2}`. -/
noncomputable def l2norm (f : V → ℝ) : ℝ := Real.sqrt (∑' x, f x ^ 2)

theorem l2norm_nonneg (f : V → ℝ) : 0 ≤ l2norm f := Real.sqrt_nonneg _

theorem sq_l2norm {f : V → ℝ} : l2norm f ^ 2 = ∑' x, f x ^ 2 :=
  Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)

/-- The triangle inequality in `ℓ²`. -/
theorem l2norm_add_le {f g : V → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) :
    Summable (fun x => (f x + g x) ^ 2) ∧ l2norm (fun x => f x + g x) ≤ l2norm f + l2norm g := by
  have hfg := summable_mul_of_sq' hf hg
  have hs : Summable fun x => (f x + g x) ^ 2 :=
    ((hf.add (hfg.mul_left 2)).add hg).congr fun x => by ring
  refine ⟨hs, ?_⟩
  have hcs := sq_le_mul_of_hasSum hfg.hasSum hf.hasSum hg.hasSum
  have hA : 0 ≤ ∑' x, f x ^ 2 := tsum_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∑' x, g x ^ 2 := tsum_nonneg fun x => sq_nonneg _
  have hsum : ∑' x, (f x + g x) ^ 2 =
      ∑' x, f x ^ 2 + 2 * ∑' x, f x * g x + ∑' x, g x ^ 2 := by
    rw [← tsum_mul_left, ← hf.tsum_add (hfg.mul_left 2), ← (hf.add (hfg.mul_left 2)).tsum_add hg]
    exact tsum_congr fun x => by ring
  have hP : ∑' x, f x * g x ≤ l2norm f * l2norm g := by
    rw [l2norm, l2norm, ← Real.sqrt_mul hA]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)
  rw [l2norm, show l2norm f + l2norm g = Real.sqrt ((l2norm f + l2norm g) ^ 2) from
    (Real.sqrt_sq (by have := l2norm_nonneg f; have := l2norm_nonneg g; positivity)).symm]
  apply Real.sqrt_le_sqrt
  rw [hsum, add_sq, sq_l2norm, sq_l2norm]
  linarith

theorem summable_sq_sub_l2 {f g : V → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) : Summable fun x => (f x - g x) ^ 2 :=
  (l2norm_add_le (g := fun x => -g x) hf (by simpa using hg)).1.congr fun x => by ring

/-- The triangle inequality for finite sums in `ℓ²`. -/
theorem l2norm_sum_le {ι : Type*} (s : Finset ι) {f : ι → V → ℝ}
    (hf : ∀ i ∈ s, Summable fun x => f i x ^ 2) :
    Summable (fun x => (∑ i ∈ s, f i x) ^ 2) ∧
      l2norm (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, l2norm (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [l2norm]
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨h3, h4⟩ := l2norm_add_le hfa h1
    simp only [Finset.sum_insert ha]
    exact ⟨h3, h4.trans (add_le_add le_rfl h2)⟩

variable {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

theorem heatFlowG_sub (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f g : V → ℝ} (hf : Summable fun x => f x ^ 2) (hg : Summable fun x => g x ^ 2) (x : V) :
    heatFlowG G D t (fun w => f w - g w) x = heatFlowG G D t f x - heatFlowG G D t g x := by
  unfold heatFlowG
  rw [← (summable_vsrwHeat_mul_l2 hD hdeg ht hf x).tsum_sub
    (summable_vsrwHeat_mul_l2 hD hdeg ht hg x)]
  exact tsum_congr fun w => by ring

theorem heatFlowG_zero (f : V → ℝ) (x : V) : heatFlowG G D 0 f x = f x := by
  unfold heatFlowG
  simp_rw [vsrwHeat_zero]
  rw [tsum_eq_single x fun w hw => by rw [if_neg (Ne.symm hw), zero_mul]]
  rw [if_pos rfl, one_mul]

theorem summable_sq_heatFlowG (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun x => f x ^ 2) :
    Summable fun x => heatFlowG G D t f x ^ 2 :=
  (hasSum_sq_heatFlowG_le hD hdeg ht hf).1

/-- **The telescoping identity** over the geometric times `s_{j+1} = 3 s_j`, `t = s_J`. -/
theorem heatFlowG_telescope (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {F : ℕ → V → ℝ}
    (hF : ∀ j, Summable fun x => F j x ^ 2) {s : ℕ → ℝ} (hs0 : 0 ≤ s 0)
    (hs : ∀ j, s (j + 1) = 3 * s j) (J : ℕ) (x : V) :
    heatFlowG G D (s J - s 0) (F 0) x - F J x =
      ∑ j ∈ Finset.range J, heatFlowG G D (s J - s (j + 1))
        (fun w => heatFlowG G D (2 * s j) (F j) w - F (j + 1) w) x := by
  have hsnn : ∀ j, 0 ≤ s j := by
    intro j
    induction j with
    | zero => exact hs0
    | succ j ih => rw [hs j]; linarith
  have hmono : ∀ i j, i ≤ j → s i ≤ s j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | @step m _ ih => exact ih.trans (by rw [hs m]; linarith [hsnn m])
  set T : ℕ → ℝ := fun j => heatFlowG G D (s J - s j) (F j) x with hT
  have hterm : ∀ j ∈ Finset.range J, heatFlowG G D (s J - s (j + 1))
      (fun w => heatFlowG G D (2 * s j) (F j) w - F (j + 1) w) x = T j - T (j + 1) := by
    intro j hj
    have hjJ : j + 1 ≤ J := Finset.mem_range.1 hj
    have ht1 : 0 ≤ s J - s (j + 1) := by linarith [hmono _ _ hjJ]
    rw [heatFlowG_sub hD hdeg ht1 (summable_sq_heatFlowG hD hdeg (by linarith [hsnn j]) (hF j))
      (hF (j + 1)), heatFlowG_heatFlowG hD hdeg ht1 (by linarith [hsnn j]) (hF j)]
    have e : s J - s (j + 1) + 2 * s j = s J - s j := by rw [hs j]; ring
    rw [e]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  have hTJ : T J = F J x := by
    simp only [hT, sub_self]
    exact heatFlowG_zero (F J) x
  rw [hTJ]

/-- `P_a p_b(·, y) = p_{a+b}(·, y)`. -/
theorem heatFlowG_vsrwHeat (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (y x : V) :
    heatFlowG G D a (fun w => vsrwHeat G D b w y) x = vsrwHeat G D (a + b) x y :=
  (hasSum_vsrwHeat_mul hD hdeg ha hb x y).tsum_eq

theorem summable_sq_vsrwHeat_col (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {b : ℝ} (hb : 0 ≤ b)
    (y : V) : Summable fun w => vsrwHeat G D b w y ^ 2 := by
  have h := (hasSum_heatDeriv_sq hD hdeg 0 hb y).summable
  exact h.congr fun w => by rw [heatDeriv_zero, vsrwHeat_symm hD hdeg b y w]

/-- **From smooth initial data to a point source**: with `s_{j+1} = 3 s_j`, `t = s_J`,
`E = p_{s_0}(·, y) - F_0` and `D_j = P_{2 s_j} F_j - F_{j+1}`,
`‖p_t(·, y) - F_J‖ ≤ ‖P_{t - s_0} E‖ + Σ_{j < J} ‖P_{t - s_{j+1}} D_j‖`. -/
theorem l2norm_vsrwHeat_sub_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {F : ℕ → V → ℝ}
    (hF : ∀ j, Summable fun x => F j x ^ 2) {s : ℕ → ℝ} (hs0 : 0 ≤ s 0)
    (hs : ∀ j, s (j + 1) = 3 * s j) (J : ℕ) (y : V) (hJ : s 0 ≤ s J) :
    l2norm (fun x => vsrwHeat G D (s J) x y - F J x) ≤
      l2norm (heatFlowG G D (s J - s 0) (fun w => vsrwHeat G D (s 0) w y - F 0 w)) +
        ∑ j ∈ Finset.range J, l2norm (heatFlowG G D (s J - s (j + 1))
          (fun w => heatFlowG G D (2 * s j) (F j) w - F (j + 1) w)) := by
  have ht : 0 ≤ s J - s 0 := by linarith
  have hsnn : ∀ j, 0 ≤ s j := by
    intro j
    induction j with
    | zero => exact hs0
    | succ j ih => rw [hs j]; linarith
  have hmono : ∀ i j, i ≤ j → s i ≤ s j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | @step m _ ih => exact ih.trans (by rw [hs m]; linarith [hsnn m])
  have hcol := summable_sq_vsrwHeat_col hD hdeg hs0 y
  have hE : Summable fun w => (vsrwHeat G D (s 0) w y - F 0 w) ^ 2 := summable_sq_sub_l2 hcol (hF 0)
  have hpt : ∀ x, vsrwHeat G D (s J) x y - F J x =
      heatFlowG G D (s J - s 0) (fun w => vsrwHeat G D (s 0) w y - F 0 w) x +
        ∑ j ∈ Finset.range J, heatFlowG G D (s J - s (j + 1))
          (fun w => heatFlowG G D (2 * s j) (F j) w - F (j + 1) w) x := by
    intro x
    rw [← heatFlowG_telescope hD hdeg hF hs0 hs J x,
      heatFlowG_sub hD hdeg ht hcol (hF 0) x, heatFlowG_vsrwHeat hD hdeg ht hs0 y x,
      show s J - s 0 + s 0 = s J by ring]
    ring
  have hterms : ∀ j ∈ Finset.range J, Summable fun x => heatFlowG G D (s J - s (j + 1))
      (fun w => heatFlowG G D (2 * s j) (F j) w - F (j + 1) w) x ^ 2 := by
    intro j hj
    have hjJ : j + 1 ≤ J := Finset.mem_range.1 hj
    exact summable_sq_heatFlowG hD hdeg (by linarith [hmono _ _ hjJ])
      (summable_sq_sub_l2 (summable_sq_heatFlowG hD hdeg (by linarith [hsnn j]) (hF j))
        (hF (j + 1)))
  obtain ⟨hsum2, hsum⟩ := l2norm_sum_le (Finset.range J) hterms
  obtain ⟨-, htot⟩ := l2norm_add_le (summable_sq_heatFlowG hD hdeg ht hE) hsum2
  have heq : (fun x => vsrwHeat G D (s J) x y - F J x) = fun x =>
      heatFlowG G D (s J - s 0) (fun w => vsrwHeat G D (s 0) w y - F 0 w) x +
        ∑ j ∈ Finset.range J, heatFlowG G D (s J - s (j + 1))
          (fun w => heatFlowG G D (2 * s j) (F j) w - F (j + 1) w) x := funext hpt
  rw [heq]
  exact htot.trans (add_le_add le_rfl hsum)

end Rigidity.Green

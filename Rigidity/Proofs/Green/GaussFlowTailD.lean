import Rigidity.Proofs.Green.NormalizedGaussianD

/-!
# The mass of the differences `D_s` outside a ball

For an open component `K`, a pole `y ∈ K`, `s ≥ 1` and `l ≥ 0`, if the heat kernel started in `K`
moves by at least `l/2` in time `2s` with mass at most `τ`
(`Σ_{|x - w| ≥ l/2} p_{2s}(w, x) ≤ τ` for `w ∈ K`), then

  `Σ_{x ∉ V_l(y)} |D_s(x)| ≤ τ + 2^{d/2} M_σ (M_s^{-1} e^{-l²/(16σs)} + M_{3s}^{-1} e^{-l²/(12σs)})`

(`tsum_out_abs_gaussFlowDiff_le`), where `V_l(y) = K ∩ B_l(y)`: the initial points outside
`B_{l/2}(y)` are discarded by the Gaussian tail (`tsum_gaussianHeatD_far_le`), and from the others a
displacement at least `l/2` is necessary. The same computation from the pole bounds the mass of the
initial error `E = p_s(·, y) - G_s` outside `V_l(y)` (`tsum_out_abs_initialError_le`).
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.WeakPoincare

namespace Rigidity.Green

local notation "ldist" => Rigidity.WeakPoincare.latticeDist

variable {d : ℕ} [NeZero d] {ω : Configuration d}

omit [NeZero d] in
theorem latticeDist_eq_norm_edzD (x y : Vertex d) : ldist x y = ‖edzD x y‖ := rfl

omit [NeZero d] in
theorem vsrwHeat_open_eq_zero {K : OpenComponent ω} {x y : Vertex d} (hx : x ∈ K.supp)
    (hy : y ∉ K.supp) (t : ℝ) : vsrwHeat (openGraph ω) (2 * d) t x y = 0 := by
  apply vsrwHeat_eq_zero_of_not_reachable
  intro hr
  apply hy
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  rw [← hx]
  exact (SimpleGraph.ConnectedComponent.sound hr).symm

theorem vsrwHeat_open_eq_zero' {K : OpenComponent ω} {x y : Vertex d} (hx : x ∉ K.supp)
    (hy : y ∈ K.supp) (t : ℝ) : vsrwHeat (openGraph ω) (2 * d) t x y = 0 := by
  rw [vsrwHeat_symm two_mul_pos_d (openGraph_degree_le ω)]
  exact vsrwHeat_open_eq_zero hy hx t

/-- The heat flow of a function supported on `K` vanishes off `K`. -/
theorem heatFlowG_eq_zero_of_notMem {K : OpenComponent ω} {f : Vertex d → ℝ}
    (hf : ∀ w, w ∉ K.supp → f w = 0) {x : Vertex d} (hx : x ∉ K.supp) (t : ℝ) :
    heatFlowG (openGraph ω) (2 * d) t f x = 0 := by
  unfold heatFlowG
  refine (tsum_congr fun w => ?_).trans tsum_zero
  by_cases hw : w ∈ K.supp
  · rw [vsrwHeat_open_eq_zero' hx hw, zero_mul]
  · rw [hf w hw, mul_zero]

/-- **Displacement from a function on `K`**: for `f ≥ 0` summable and supported on `K`,
`Σ_{|x - y| ≥ l} P_u f(x) ≤ τ Σ f + Σ_{|w - y| ≥ l/2} f(w)` when the heat kernel from every point of
`K` moves by at least `l/2` in time `u` with mass at most `τ`. -/
theorem tsum_far_heatFlowG_le {K : OpenComponent ω} {y : Vertex d} {u l τ : ℝ} (hu : 0 ≤ u)
    {f : Vertex d → ℝ} (hf0 : ∀ w, 0 ≤ f w) (hf : Summable f) (hfK : ∀ w, w ∉ K.supp → f w = 0)
    (hτ : 0 ≤ τ)
    (hdisp : ∀ w ∈ K.supp, ∑' x, (if l / 2 ≤ ldist x w then
      vsrwHeat (openGraph ω) (2 * d) u w x else 0) ≤ τ) :
    ∑' x, (if l ≤ ldist x y then heatFlowG (openGraph ω) (2 * d) u f x else 0) ≤
      τ * ∑' w, f w + ∑' w, (if l / 2 ≤ ldist w y then f w else 0) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  set p := vsrwHeat (openGraph ω) (2 * d) u with hp
  have hp0 : ∀ a b, 0 ≤ p a b := fun a b => vsrwHeat_nonneg hD hdeg hu a b
  have hpsum : ∀ w, HasSum (fun x => p w x) 1 := fun w => hasSum_vsrwHeat hD hdeg hu w
  -- the double sum
  set F : Vertex d → Vertex d → ℝ := fun x w =>
    if l ≤ ldist x y then p x w * f w else 0 with hF
  have hF0 : ∀ x w, 0 ≤ F x w := fun x w => by
    simp only [hF]; split_ifs
    · exact mul_nonneg (hp0 x w) (hf0 w)
    · exact le_rfl
  have hFle : ∀ x w, F x w ≤ p w x * f w := fun x w => by
    simp only [hF]; split_ifs
    · rw [hp, vsrwHeat_symm hD hdeg u x w]
    · exact mul_nonneg (hp0 w x) (hf0 w)
  have hcol : ∀ w, Summable fun x => F x w := fun w =>
    ((hpsum w).summable.mul_right (f w)).of_nonneg_of_le (fun x => hF0 x w) (fun x => hFle x w)
  have hcolsum : ∀ w, ∑' x, F x w ≤ f w := fun w => by
    calc ∑' x, F x w ≤ ∑' x, p w x * f w :=
          (hcol w).tsum_le_tsum (fun x => hFle x w) ((hpsum w).summable.mul_right _)
      _ = f w := by rw [tsum_mul_right, (hpsum w).tsum_eq, one_mul]
  have hU : Summable (Function.uncurry F) :=
    summable_uncurry_of_nonneg' hF0 hcol
      (hf.of_nonneg_of_le (fun w => tsum_nonneg fun x => hF0 x w) hcolsum)
  have hrow : ∀ x, (if l ≤ ldist x y then heatFlowG (openGraph ω) (2 * d) u f x else 0) =
      ∑' w, F x w := fun x => by
    simp only [hF]
    split_ifs
    · rfl
    · exact tsum_zero.symm
  simp_rw [hrow]
  rw [tsum_comm_of_abs_le (g := F) (fun x w => (abs_of_nonneg (hF0 x w)).le) hU]
  -- the bound for each initial point
  have hpt : ∀ w, ∑' x, F x w ≤ τ * f w + (if l / 2 ≤ ldist w y then f w else 0) := by
    intro w
    by_cases hwK : w ∈ K.supp
    · by_cases hwy : l / 2 ≤ ldist w y
      · rw [if_pos hwy]
        have := hcolsum w
        nlinarith [hf0 w]
      · rw [if_neg hwy, add_zero]
        push Not at hwy
        have hle : ∀ x, F x w ≤ (if l / 2 ≤ ldist x w then p w x else 0) * f w := by
          intro x
          simp only [hF]
          by_cases hxy : l ≤ ldist x y
          · rw [if_pos hxy]
            have htri := WeakPoincare.latticeDist_triangle x w y
            rw [if_pos (by linarith), hp, vsrwHeat_symm hD hdeg u x w]
          · rw [if_neg hxy]
            exact mul_nonneg (by split_ifs <;> simp [hp0]) (hf0 w)
        have hT : Summable fun x => (if l / 2 ≤ ldist x w then p w x else 0) :=
          (hpsum w).summable.of_nonneg_of_le (fun x => by split_ifs <;> simp [hp0])
            (fun x => by split_ifs <;> simp [hp0])
        calc ∑' x, F x w ≤ ∑' x, (if l / 2 ≤ ldist x w then p w x else 0) * f w :=
              (hcol w).tsum_le_tsum hle (hT.mul_right _)
          _ = (∑' x, (if l / 2 ≤ ldist x w then p w x else 0)) * f w := tsum_mul_right
          _ ≤ τ * f w := mul_le_mul_of_nonneg_right (hdisp w hwK) (hf0 w)
    · have : f w = 0 := hfK w hwK
      have h0 : ∀ x, F x w = 0 := fun x => by simp only [hF, this, mul_zero, ite_self]
      rw [tsum_congr h0, tsum_zero, this, mul_zero, zero_add]
      split_ifs <;> exact le_rfl
  have hT2 : Summable fun w => (if l / 2 ≤ ldist w y then f w else 0) :=
    hf.of_nonneg_of_le (fun w => by split_ifs <;> simp [hf0]) (fun w => by
      split_ifs <;> simp [hf0])
  calc ∑' w, ∑' x, F x w ≤ ∑' w, (τ * f w + (if l / 2 ≤ ldist w y then f w else 0)) :=
        (hf.of_nonneg_of_le (fun w => tsum_nonneg fun x => hF0 x w) hcolsum).tsum_le_tsum hpt
          ((hf.mul_left τ).add hT2)
    _ = τ * ∑' w, f w + ∑' w, (if l / 2 ≤ ldist w y then f w else 0) := by
        rw [(hf.mul_left τ).tsum_add hT2, tsum_mul_left]

variable {K : OpenComponent ω} {σ : ℝ} {y : Vertex d}

omit [NeZero d] in
theorem clusterInd_eq_zero {s : ℝ} {w : Vertex d} (hw : w ∉ K.supp) : clusterInd K σ s y w = 0 := by
  unfold clusterInd; rw [if_neg hw]

omit [NeZero d] in
/-- The Gaussian tail of `G_s`. -/
theorem tsum_far_clusterGaussNorm_le (hσ : 0 < σ) {s L : ℝ} (hs : 1 ≤ s) (hL : 0 ≤ L)
    (hM : 0 < clusterGaussMass K σ s y) :
    ∑' w, (if L ≤ ldist w y then clusterGaussNorm K σ s y w else 0) ≤
      (clusterGaussMass K σ s y)⁻¹ *
        (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * Real.exp (-(L ^ 2 / (4 * σ * s)))) := by
  have hs0 : 0 < s := by linarith
  have hle : ∀ w, (if L ≤ ldist w y then clusterGaussNorm K σ s y w else 0) ≤
      (clusterGaussMass K σ s y)⁻¹ *
        (if L ≤ ‖edzD w y‖ then gaussianHeatD d σ s (edzD w y) else 0) := by
    intro w
    rw [← latticeDist_eq_norm_edzD]
    split_ifs
    · unfold clusterGaussNorm
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (clusterInd_le hσ hs0 w) (inv_nonneg.2 hM.le)
    · simp
  have hg : Summable fun w => (if L ≤ ‖edzD w y‖ then gaussianHeatD d σ s (edzD w y) else 0) :=
    (summable_gaussianHeatD (d := d) hσ hs0 y).of_nonneg_of_le
      (fun w => by split_ifs <;> simp [gaussianHeatD_nonneg' σ s (by positivity)])
      (fun w => by split_ifs <;> simp [gaussianHeatD_nonneg' σ s (by positivity)])
  have hT : Summable fun w => (if L ≤ ldist w y then clusterGaussNorm K σ s y w else 0) :=
    (summable_clusterGaussNorm (K := K) (y := y) hσ hs0).of_nonneg_of_le
      (fun w => by
        split_ifs
        · exact div_nonneg (clusterInd_nonneg hσ hs0 w) hM.le
        · exact le_rfl)
      (fun w => by
        split_ifs
        · exact le_rfl
        · exact div_nonneg (clusterInd_nonneg hσ hs0 w) hM.le)
  calc _ ≤ ∑' w, (clusterGaussMass K σ s y)⁻¹ *
        (if L ≤ ‖edzD w y‖ then gaussianHeatD d σ s (edzD w y) else 0) :=
        hT.tsum_le_tsum hle (hg.mul_left _)
    _ = (clusterGaussMass K σ s y)⁻¹ *
        ∑' w, (if L ≤ ‖edzD w y‖ then gaussianHeatD d σ s (edzD w y) else 0) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_gaussianHeatD_far_le hσ hs hL y)
        (inv_nonneg.2 hM.le)

/-- **The mass of `D_s` outside `V_l(y)`.** -/
theorem tsum_out_abs_gaussFlowDiff_le (hσ : 0 < σ) {s l τ : ℝ} (hs : 1 ≤ s) (hl : 0 ≤ l)
    (hM1 : 0 < clusterGaussMass K σ s y) (hM3 : 0 < clusterGaussMass K σ (3 * s) y) (hτ : 0 ≤ τ)
    (hdisp : ∀ w ∈ K.supp, ∑' x, (if l / 2 ≤ ldist x w then
      vsrwHeat (openGraph ω) (2 * d) (2 * s) w x else 0) ≤ τ) :
    ∑' x, (if x ∈ clusterBall K y l then 0 else |gaussFlowDiff K σ s y x|) ≤
      τ + (clusterGaussMass K σ s y)⁻¹ *
          (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * Real.exp (-((l / 2) ^ 2 / (4 * σ * s)))) +
        (clusterGaussMass K σ (3 * s) y)⁻¹ *
          (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ *
            Real.exp (-(l ^ 2 / (4 * σ * (3 * s))))) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have hs0 : 0 < s := by linarith
  have h2s : (0 : ℝ) ≤ 2 * s := by linarith
  set G1 := clusterGaussNorm K σ s y with hG1
  set G3 := clusterGaussNorm K σ (3 * s) y with hG3
  have hG10 : ∀ w, 0 ≤ G1 w := fun w => div_nonneg (clusterInd_nonneg hσ hs0 w) hM1.le
  have hG30 : ∀ w, 0 ≤ G3 w := fun w => div_nonneg (clusterInd_nonneg hσ (by linarith) w) hM3.le
  have hG1K : ∀ w, w ∉ K.supp → G1 w = 0 := fun w hw => by
    simp only [hG1, clusterGaussNorm, clusterInd_eq_zero hw, zero_div]
  have hG3K : ∀ w, w ∉ K.supp → G3 w = 0 := fun w hw => by
    simp only [hG3, clusterGaussNorm, clusterInd_eq_zero hw, zero_div]
  have hPG := summable_heatFlowG (G := openGraph ω) hD hdeg h2s
    (summable_abs_clusterGaussNorm (K := K) (y := y) hσ hs0)
  have hPG0 : ∀ x, 0 ≤ heatFlowG (openGraph ω) (2 * d) (2 * s) G1 x :=
    fun x => heatFlowG_nonneg hD hdeg h2s hG10 x
  set A : Vertex d → ℝ := fun x =>
    if l ≤ ldist x y then heatFlowG (openGraph ω) (2 * d) (2 * s) G1 x else 0 with hA
  set B : Vertex d → ℝ := fun x => if l ≤ ldist x y then G3 x else 0 with hB
  have hA0 : ∀ x, 0 ≤ A x := fun x => by simp only [hA]; split_ifs <;> simp [hPG0]
  have hB0 : ∀ x, 0 ≤ B x := fun x => by simp only [hB]; split_ifs <;> simp [hG30]
  have hAs : Summable A := hPG.of_nonneg_of_le hA0 (fun x => by
    simp only [hA]; split_ifs; exacts [le_rfl, hPG0 x])
  have hBs : Summable B := (summable_clusterGaussNorm (K := K) (y := y) hσ
    (by linarith : (0 : ℝ) < 3 * s)).of_nonneg_of_le hB0 (fun x => by
      simp only [hB]; split_ifs; exacts [le_rfl, hG30 x])
  have hpt : ∀ x, (if x ∈ clusterBall K y l then 0 else |gaussFlowDiff K σ s y x|) ≤ A x + B x := by
    intro x
    by_cases hxV : x ∈ clusterBall K y l
    · rw [if_pos hxV]; exact add_nonneg (hA0 x) (hB0 x)
    · rw [if_neg hxV]
      by_cases hxK : x ∈ K.supp
      · have hxy : l ≤ ldist x y := by
          by_contra h
          push Not at h
          exact hxV (mem_clusterBall.2 ⟨hxK, h⟩)
        simp only [hA, hB, if_pos hxy]
        unfold gaussFlowDiff
        calc _ ≤ |heatFlowG (openGraph ω) (2 * d) (2 * s) G1 x| + |G3 x| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (hPG0 x), abs_of_nonneg (hG30 x)]
      · unfold gaussFlowDiff
        rw [heatFlowG_eq_zero_of_notMem hG1K hxK, ← hG3, hG3K x hxK, sub_zero, abs_zero]
        exact add_nonneg (hA0 x) (hB0 x)
  have hT : Summable fun x => (if x ∈ clusterBall K y l then 0 else |gaussFlowDiff K σ s y x|) :=
    (hAs.add hBs).of_nonneg_of_le (fun x => by split_ifs <;> simp) hpt
  have hAb := tsum_far_heatFlowG_le (K := K) (y := y) h2s hG10
    (summable_clusterGaussNorm hσ hs0) hG1K hτ hdisp
  rw [tsum_clusterGaussNorm hM1.ne', mul_one] at hAb
  have hG1far := tsum_far_clusterGaussNorm_le (K := K) (y := y) hσ hs (by linarith : 0 ≤ l / 2) hM1
  have hG3far := tsum_far_clusterGaussNorm_le (K := K) (y := y) hσ (s := 3 * s) (by linarith) hl hM3
  calc _ ≤ ∑' x, (A x + B x) := hT.tsum_le_tsum hpt (hAs.add hBs)
    _ = ∑' x, A x + ∑' x, B x := hAs.tsum_add hBs
    _ ≤ _ := by
        have e1 : ∑' x, A x = ∑' x, (if l ≤ ldist x y then
            heatFlowG (openGraph ω) (2 * d) (2 * s) G1 x else 0) := rfl
        have e2 : ∑' x, B x = ∑' x, (if l ≤ ldist x y then G3 x else 0) := rfl
        rw [e1, e2]
        linarith

/-- **The mass of the initial error outside `V_l(y)`.** -/
theorem tsum_out_abs_initialError_le (hσ : 0 < σ) {s l τ : ℝ} (hs : 1 ≤ s) (hl : 0 ≤ l)
    (hy : y ∈ K.supp) (hM : 0 < clusterGaussMass K σ s y)
    (hdisp : ∑' x, (if l ≤ ldist x y then vsrwHeat (openGraph ω) (2 * d) s y x else 0) ≤ τ) :
    ∑' x, (if x ∈ clusterBall K y l then 0 else
        |vsrwHeat (openGraph ω) (2 * d) s x y - clusterGaussNorm K σ s y x|) ≤
      τ + (clusterGaussMass K σ s y)⁻¹ *
        (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * Real.exp (-(l ^ 2 / (4 * σ * s)))) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have hs0 : 0 < s := by linarith
  set G1 := clusterGaussNorm K σ s y with hG1
  have hG10 : ∀ w, 0 ≤ G1 w := fun w => div_nonneg (clusterInd_nonneg hσ hs0 w) hM.le
  have hG1K : ∀ w, w ∉ K.supp → G1 w = 0 := fun w hw => by
    simp only [hG1, clusterGaussNorm, clusterInd_eq_zero hw, zero_div]
  have hp0 : ∀ a b, 0 ≤ vsrwHeat (openGraph ω) (2 * d) s a b :=
    fun a b => vsrwHeat_nonneg hD hdeg hs0.le a b
  set A : Vertex d → ℝ := fun x =>
    if l ≤ ldist x y then vsrwHeat (openGraph ω) (2 * d) s y x else 0 with hA
  set B : Vertex d → ℝ := fun x => if l ≤ ldist x y then G1 x else 0 with hB
  have hA0 : ∀ x, 0 ≤ A x := fun x => by simp only [hA]; split_ifs <;> simp [hp0]
  have hB0 : ∀ x, 0 ≤ B x := fun x => by simp only [hB]; split_ifs <;> simp [hG10]
  have hAs : Summable A := (hasSum_vsrwHeat hD hdeg hs0.le y).summable.of_nonneg_of_le hA0
    (fun x => by simp only [hA]; split_ifs <;> simp [hp0])
  have hBs : Summable B := (summable_clusterGaussNorm (K := K) (y := y) hσ hs0).of_nonneg_of_le
    hB0 (fun x => by simp only [hB]; split_ifs; exacts [le_rfl, hG10 x])
  have hpt : ∀ x, (if x ∈ clusterBall K y l then 0 else
      |vsrwHeat (openGraph ω) (2 * d) s x y - G1 x|) ≤ A x + B x := by
    intro x
    by_cases hxV : x ∈ clusterBall K y l
    · rw [if_pos hxV]; exact add_nonneg (hA0 x) (hB0 x)
    · rw [if_neg hxV]
      by_cases hxK : x ∈ K.supp
      · have hxy : l ≤ ldist x y := by
          by_contra h
          push Not at h
          exact hxV (mem_clusterBall.2 ⟨hxK, h⟩)
        simp only [hA, hB, if_pos hxy]
        calc _ ≤ |vsrwHeat (openGraph ω) (2 * d) s x y| + |G1 x| := abs_sub _ _
          _ = _ := by
            rw [abs_of_nonneg (hp0 x y), abs_of_nonneg (hG10 x), vsrwHeat_symm hD hdeg s x y]
      · rw [vsrwHeat_open_eq_zero' hxK hy, hG1K x hxK, sub_zero, abs_zero]
        exact add_nonneg (hA0 x) (hB0 x)
  have hT : Summable fun x => (if x ∈ clusterBall K y l then 0 else
      |vsrwHeat (openGraph ω) (2 * d) s x y - G1 x|) :=
    (hAs.add hBs).of_nonneg_of_le (fun x => by split_ifs <;> simp) hpt
  have hGfar := tsum_far_clusterGaussNorm_le (K := K) (y := y) hσ hs hl hM
  calc _ ≤ ∑' x, (A x + B x) := hT.tsum_le_tsum hpt (hAs.add hBs)
    _ = ∑' x, A x + ∑' x, B x := hAs.tsum_add hBs
    _ ≤ _ := by
        have e2 : ∑' x, B x = ∑' x, (if l ≤ ldist x y then G1 x else 0) := rfl
        rw [e2]
        linarith

end Rigidity.Green

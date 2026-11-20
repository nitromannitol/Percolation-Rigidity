import Rigidity.Proofs.Section5.PlanarGreenAsymptotics
import Rigidity.Proofs.Section5.PlanarCorrectorGradient

/-!
# Planar two-scale expansion

The two-scale expansion uses the quantitative corrector and Green estimates only in dimension
two.
-/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section2 Rigidity.Section5 Rigidity.Steps.S2

/-- The two-scale expansion from planar Green and corrector estimates. -/
theorem twoScaleExpansion_of_planar_inputs {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo) (hU : UniqueClusterAe p)
    (h26 : GreenGradientHomogenizationStmt 2 le_rfl p)
    (hC : ConnectingSetAt p) (hF : FlowOnConnectedSetStep) (hS : SummationByPartsStep)
    (hrad : ConnectedSetRadiusStep) (hedge : ForwardDiffEdgeStep) (htay : GreenTaylorStep)
    (htail : TailOfOsStep 2 p) (hmin : MinimalScaleStep 2 p)
    (f : Vertex 2 → ℤ) : TwoScaleExpansionStmt p f := by
  intro hf
  obtain ⟨κ, h26'⟩ := h26
  obtain ⟨s6, C6, hs6, hC6, h26δ⟩ := h26' (1 / 8) (by norm_num)
  choose M6 hM6m _ hM6os hM6ae using h26δ
  obtain ⟨θR, sR, hθR, hsR, R, hRm, hRos, hRae⟩ := hC f hf
  obtain ⟨sΛ, θΛ, hsΛ, hθΛ, Λ, hΛm, hΛos, hΛae⟩ := Rigidity.Proofs.Section5.correctedPlaneGradientStep_two hCQ p hpc hp1
  obtain ⟨CT, hCT, hT⟩ := htay κ
  obtain ⟨c6, hc6, ht6⟩ := htail s6 C6 hs6 hC6
  obtain ⟨cR, hcR, htR⟩ := htail sR θR hsR hθR
  obtain ⟨cΛ, hcΛ, htΛ⟩ := htail sΛ θΛ hsΛ hθΛ
  obtain ⟨mf, hmf⟩ : ∃ m : ℝ, m = ∑ y ∈ hf.toFinset, |(f y : ℝ)| := ⟨_, rfl⟩
  obtain ⟨ρf, hρf⟩ : ∃ m : ℝ, m = ∑ y ∈ hf.toFinset, l1 y := ⟨_, rfl⟩
  have hmf0 : 0 ≤ mf := hmf ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρf0 : 0 ≤ ρf := hρf ▸ Finset.sum_nonneg fun y _ => l1_nonneg y
  have hfm : ∀ y, |(f y : ℝ)| ≤ mf := by
    intro y
    by_cases hy : f y = 0
    · simp only [hy, Int.cast_zero, abs_zero]
      exact hmf0
    · rw [hmf]
      exact Finset.single_le_sum (f := fun y => |(f y : ℝ)|) (fun _ _ => abs_nonneg _)
        (hf.mem_toFinset.mpr hy)
  have hfl : ∀ y, f y ≠ 0 → l1 y ≤ ρf := fun y hy => hρf ▸
    Finset.single_le_sum (f := l1) (fun y _ => l1_nonneg y) (hf.mem_toFinset.mpr hy)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 4 + 4 * (ρf + 1) + (2 * mf * C6 + mf * CT * (2 + ρf) ^ 2) :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ 2 * mf * C6 + mf * CT * (2 + ρf) ^ 2 := by positivity
  have hA4 : 4 ≤ A := by linarith
  obtain ⟨s', C', hs', hAC', hM⟩ := hmin 3 ![s6, sR, sΛ] ![c6, cR, cΛ] A 24
    (by intro i; fin_cases i <;> simp [hs6, hsR, hsΛ])
    (by intro i; fin_cases i <;> simp [hc6, hcR, hcΛ]) (by linarith)
  obtain ⟨M, hMm, -, hMos, hMae⟩ := hM 0 ![fun y => M6 y, fun _ => R, fun _ => Λ]
    (by intro i y; fin_cases i <;> simp [hM6m, hRm, hΛm])
    (by
      intro i y
      fin_cases i
      · exact ht6 _ (hM6m y) (hM6os y)
      · exact htR _ hRm hRos
      · exact htΛ _ hΛm hΛos)
  refine ⟨C', s', by linarith, hs', κ, M, hMm, hMos, ?_⟩
  filter_upwards [hU, hRae, hΛae, hMae, ae_all_iff.2 hM6ae, Rigidity.Proofs.Section5.greenSymmetry_two hGQ hpc hp1]
    with ω hω hV hΛω hMω h6ω hsymω
  refine ⟨hω, fun hmass G hG ℓ hℓ => ?_⟩
  obtain ⟨V, hVc, hVf, hVR⟩ := hV hω
  have hsum : ∑ y ∈ V, (f y.val : ℝ) = 0 := by
    have h1 : mass (uniqueInfiniteComponent hω) f = ∑ y ∈ V, f y.val :=
      finsum_eq_sum_of_support_subset _ fun y hy => Finset.mem_coe.mpr (hVf y hy)
    have h2 : ∑ y ∈ V, f y.val = 0 := h1 ▸ hmass
    exact_mod_cast h2
  obtain ⟨F, hanti, hsupp, hdiv, hbd⟩ := hF (componentGraph (uniqueInfiniteComponent hω)) V
    (fun y => (f y.val : ℝ)) hVc (fun y hy => hVf y (Int.cast_ne_zero.mp hy)) hsum
  have hSF : ∀ a b, F a b ≠ 0 → (a, b) ∈ V ×ˢ V := fun a b h =>
    Finset.mem_product.mpr ⟨(hsupp a b h).2.1, (hsupp a b h).2.2⟩
  have hSb : ∀ k : (uniqueInfiniteComponent hω) → ℝ, ∑ᶠ a, (f a.val : ℝ) * k a =
      (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * (k e.1 - k e.2) := hS F _ (V ×ˢ V) hanti hSF hdiv
  obtain ⟨K, hK⟩ := hsymω hω G hG
  refine ⟨∑ᶠ y : (uniqueInfiniteComponent hω), (f y.val : ℝ) * K y, fun x hx => ?_⟩
  set Dx : Fin 2 → ℝ := fun i =>
    fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val) (EuclideanSpace.single i 1) with hDx
  set Tm : (uniqueInfiniteComponent hω) × (uniqueInfiniteComponent hω) → ℝ := fun e =>
    G e.1 x - G e.2 x + ∑ i, (ℓ i e.1 - ℓ i e.2) * Dx i with hTm
  have hid : potential (uniqueInfiniteComponent hω) G f x - ∑ᶠ y : (uniqueInfiniteComponent hω), (f y.val : ℝ) * K y +
      ∑ i, pairing (uniqueInfiniteComponent hω) f (ℓ i) * Dx i = (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * Tm e := by
    have h1 : potential (uniqueInfiniteComponent hω) G f x = (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * (G x e.1 - G x e.2) :=
      hSb (fun y => G x y)
    have h3 : ∀ i, pairing (uniqueInfiniteComponent hω) f (ℓ i) =
        (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * (ℓ i e.1 - ℓ i e.2) := fun i => hSb (ℓ i)
    have h4 : ∑ i, pairing (uniqueInfiniteComponent hω) f (ℓ i) * Dx i =
        (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * ∑ i, (ℓ i e.1 - ℓ i e.2) * Dx i := by
      simp only [h3]
      calc ∑ i, (1 / 2 * ∑ e ∈ V ×ˢ V, F e.1 e.2 * (ℓ i e.1 - ℓ i e.2)) * Dx i
          = ∑ i, ∑ e ∈ V ×ˢ V, 1 / 2 * (F e.1 e.2 * ((ℓ i e.1 - ℓ i e.2) * Dx i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun e _ => by ring
        _ = ∑ e ∈ V ×ˢ V, ∑ i, 1 / 2 * (F e.1 e.2 * ((ℓ i e.1 - ℓ i e.2) * Dx i)) :=
            Finset.sum_comm
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
    rw [h1, hSb K, h4, ← mul_sub, ← Finset.sum_sub_distrib, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hTm]
    linear_combination F e.1 e.2 * (hK x e.1 - hK x e.2)
  rw [hid]
  have hcond := hMω x.val (by rwa [latticeL1Dist_zero])
  rw [latticeL1Dist_zero] at hcond
  have c0 := hcond 0
  have c1 := hcond 1
  have c2 := hcond 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at c0 c1 c2
  obtain ⟨r, hr2, hRr, hrt⟩ : ∃ r : ℝ, 2 ≤ r ∧ R ω ≤ r ∧ A * r ^ 24 < l1 x.val :=
    ⟨_, le_max_right _ _, le_max_left _ _, c1⟩
  obtain ⟨lam, hlam2, hΛlam, hlamt⟩ : ∃ r : ℝ, 2 ≤ r ∧ Λ ω ≤ r ∧ A * r ^ 24 < l1 x.val :=
    ⟨_, le_max_right _ _, le_max_left _ _, c2⟩
  obtain ⟨m, hm2, hMm6, hmt⟩ : ∃ r : ℝ, 2 ≤ r ∧ M6 x.val ω ≤ r ∧ A * r ^ 24 < l1 x.val :=
    ⟨_, le_max_right _ _, le_max_left _ _, c0⟩
  have ht0 : 0 < l1 x.val := lt_of_le_of_lt (by positivity) hrt
  obtain ⟨τ, hτ24, hτ0⟩ : ∃ τ : ℝ, τ ^ 24 = l1 x.val ∧ 0 < τ :=
    ⟨l1 x.val ^ (((24 : ℕ) : ℝ)⁻¹), Real.rpow_inv_natCast_pow ht0.le (by norm_num),
      Real.rpow_pos_of_pos ht0 _⟩
  have hle : ∀ {u : ℝ}, 0 ≤ u → A * u ^ 24 < l1 x.val → u < τ := fun hu h => by
    rw [← hτ24] at h
    exact lt_of_pow_lt_pow_left₀ 24 hτ0.le
      (lt_of_le_of_lt (le_mul_of_one_le_left (by positivity) (by linarith)) h)
  have hrτ := hle (by linarith) hrt
  have hlamτ := hle (by linarith) hlamt
  have hτ1 : 1 ≤ τ := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℝ, (V.card : ℝ) = n := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := hn ▸ Nat.cast_nonneg _
  have hnr : n ≤ r := hn ▸ hVR.trans hRr
  have hx0 : x.val ≠ 0 := by
    intro h
    rw [h] at ht0
    simp [l1] at ht0
  have h4ρ : 4 * (ρf + n) < l1 x.val := by
    have h1 : ρf * 1 ≤ ρf * r := mul_le_mul_of_nonneg_left (by linarith) hρf0
    have h2 : r ≤ r ^ 24 := le_self_pow₀ (by linarith) (by norm_num)
    have h3 : 4 * (ρf + 1) * r ^ 24 ≤ A * r ^ 24 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : 4 * (ρf + 1) * r ≤ 4 * (ρf + 1) * r ^ 24 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hM6x : 4 * M6 x.val ω < l1 x.val := by
    have : m ≤ m ^ 24 := le_self_pow₀ (by linarith) (by norm_num)
    have h3 : 4 * m ^ 24 ≤ A * m ^ 24 := mul_le_mul_of_nonneg_right hA4 (by positivity)
    linarith
  obtain ⟨Err, hErr⟩ : ∃ E : ℝ,
      E = 4 * C6 / τ ^ 33 + 2 * lam * (1 + (ρf + n)) * CT * (ρf + n) / τ ^ 48 := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by linarith
  have hErr0 : 0 ≤ Err := by
    have hρn : 0 ≤ ρf + n := by linarith
    have h1 : 0 ≤ 2 * lam * (1 + (ρf + n)) * CT * (ρf + n) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlam0) (by linarith))
        hCT.le) hρn
    rw [hErr]
    exact add_nonneg (div_nonneg (by linarith) (pow_nonneg hτ0.le _))
      (div_nonneg h1 (pow_nonneg hτ0.le _))
  have hedgeb : ∀ e ∈ V ×ˢ V, |F e.1 e.2| * |Tm e| ≤ n * mf * Err := by
    intro e _
    by_cases hFe : F e.1 e.2 = 0
    · rw [hFe, abs_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hn0 hmf0) hErr0
    obtain ⟨hadj, he1, he2⟩ := hsupp e.1 e.2 hFe
    have hFb : |F e.1 e.2| ≤ n * mf :=
      (hbd _ _).trans <| (Finset.sum_le_sum fun c _ => hfm c.val).trans
        (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul, hn]))
    obtain ⟨y0, hy0V, hy0f⟩ : ∃ y0 ∈ V, f y0.val ≠ 0 := by
      by_contra hno
      simp only [not_exists, not_and, not_not] at hno
      apply hFe
      have h0 : ∑ c ∈ V, |(f c.val : ℝ)| = 0 :=
        Finset.sum_eq_zero fun c hc => by simp [hno c hc]
      have := hbd e.1 e.2
      rw [h0] at this
      exact abs_nonpos_iff.mp this
    have hlV : ∀ a ∈ V, l1 a.val ≤ ρf + n := fun a ha => by
      have := hrad ω _ V hVc a ha y0 hy0V
      linarith [hfl _ hy0f]
    obtain ⟨z, hz, hez⟩ := hedge ω _ (fun w => G w x) ℓ
      (fun z i => fderiv ℝ (greenBar 2 le_rfl κ) (toReal z.val - toReal x.val)
        (EuclideanSpace.single i 1)) e.1 e.2 hadj
    have hzV : z ∈ V := by rcases hz with rfl | rfl <;> assumption
    have hlz := hlV z hzV
    have hD : l1 x.val / 2 ≤ ∑ i, |((z.val i - x.val i : ℤ) : ℝ)| := by
      have := l1_le_dist_add x.val z.val
      linarith
    have hP := h6ω x.val hω x.prop (fun w => G w x) (hG x) ℓ hℓ z (by linarith)
    have hP' := green_error_le (D := ∑ i, |((z.val i - x.val i : ℤ) : ℝ)|) hC6.le hτ0
      (by rw [hτ24]; exact hD)
    have hfirst := hez.trans (hP.trans hP')
    beta_reduce at hfirst
    have hTz : ∀ i, |fderiv ℝ (greenBar 2 le_rfl κ) (toReal z.val - toReal x.val)
        (EuclideanSpace.single i 1) + Dx i| ≤ CT * (ρf + n) / τ ^ 48 := by
      intro i
      refine (hT x.val z.val hx0 (by linarith) i).trans ?_
      rw [show τ ^ 48 = l1 x.val ^ 2 by rw [← hτ24]; ring]
      gcongr
    have hli : ∀ i, |ℓ i e.1 - ℓ i e.2| ≤ lam * (1 + (ρf + n)) := fun i =>
      (hΛω hω i (ℓ i) (hℓ i) e.1 e.2 hadj).trans
        (mul_le_mul hΛlam (by linarith [hlV _ he1]) (by linarith [l1_nonneg e.1.val])
          (by linarith))
    have hsplit : Tm e = (G e.1 x - G e.2 x - ∑ i, (ℓ i e.1 - ℓ i e.2) *
          fderiv ℝ (greenBar 2 le_rfl κ) (toReal z.val - toReal x.val)
            (EuclideanSpace.single i 1)) +
        ∑ i, (ℓ i e.1 - ℓ i e.2) * (fderiv ℝ (greenBar 2 le_rfl κ)
          (toReal z.val - toReal x.val) (EuclideanSpace.single i 1) + Dx i) := by
      simp only [hTm, mul_add, Finset.sum_add_distrib]
      ring
    have hsum2 : |∑ i, (ℓ i e.1 - ℓ i e.2) * (fderiv ℝ (greenBar 2 le_rfl κ)
        (toReal z.val - toReal x.val) (EuclideanSpace.single i 1) + Dx i)| ≤
        2 * lam * (1 + (ρf + n)) * CT * (ρf + n) / τ ^ 48 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |(ℓ i e.1 - ℓ i e.2) * (fderiv ℝ (greenBar 2 le_rfl κ)
            (toReal z.val - toReal x.val) (EuclideanSpace.single i 1) + Dx i)|
          ≤ ∑ _i : Fin 2, lam * (1 + (ρf + n)) * (CT * (ρf + n) / τ ^ 48) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            exact mul_le_mul (hli i) (hTz i) (abs_nonneg _) (by positivity)
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have hTb : |Tm e| ≤ Err := by
      rw [hsplit, hErr]
      exact (abs_add_le _ _).trans (add_le_add hfirst hsum2)
    exact mul_le_mul hFb hTb (abs_nonneg _) (mul_nonneg hn0 hmf0)
  have hcard : ((V ×ˢ V).card : ℝ) = n ^ 2 := by
    rw [Finset.card_product, ← hn]
    push_cast
    ring
  have hrpow : (l1 x.val).rpow (-5 / 4) = 1 / τ ^ 30 := by
    rw [Real.rpow_eq_pow, ← hτ24, show (-5 / 4 : ℝ) = -(5 / 4) by norm_num,
      Real.rpow_neg (by positivity), rpow_pow_twentyFour hτ0.le (5 / 4) 30 (by norm_num),
      one_div]
  calc |1 / 2 * ∑ e ∈ V ×ˢ V, F e.1 e.2 * Tm e|
      ≤ 1 / 2 * ∑ e ∈ V ×ˢ V, |F e.1 e.2| * |Tm e| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul]
    _ ≤ 1 / 2 * ∑ _e ∈ V ×ˢ V, n * mf * Err :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hedgeb) (by norm_num)
    _ = 1 / 2 * n ^ 2 * (n * mf) * Err := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
    _ ≤ A / τ ^ 30 := by
        rw [hErr]
        exact two_scale_numeric hτ1 hn0 hnr hrτ.le hlamτ.le hmf0 hC6.le hCT.le hρf0
          (by linarith)
    _ ≤ C' / τ ^ 30 := by gcongr
    _ = C' * (l1 x.val).rpow (-5 / 4) := by rw [hrpow]; ring

end Rigidity.Steps.Section5

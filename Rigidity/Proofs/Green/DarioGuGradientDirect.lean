import Rigidity.Proofs.Green.OrderZeroClusterBall
import Rigidity.Proofs.Green.EllipticCaccioppoliSource
import Rigidity.Proofs.Green.DarioGuGradientFromLipschitz
import Rigidity.Proofs.Green.DarioGuParabolicTimeslice
import Rigidity.Proofs.Green.DarioGuApproxLemma

/-!
# Theorem 3 of Dario–Gu in dimension two from Theorem 4, without Theorem 5

`darioGuGradientBoundTwo_of_barlow` proves the gradient bound of Dario–Gu, Theorem 3 in the form of
Remark 1.3 (`DarioGuGradientBoundTwo`), from the Gaussian upper bound of Barlow (Dario–Gu, Theorem
4, `BarlowGaussianUpperBoundTwo`), with the order-zero regularity of Armstrong and Dario
(`exists_orderZero_clusterBall`) and the volume lower bound of Proposition A.1. The proof does not
go through Theorem 5 and Proposition 3.9 of the source. With `D = |x - y| ≤ t` and
`r ≤ √t/2`, the time slice `v = p(t, x, ·)` satisfies

* `|v| ≤ U = C t^{-1} e^{-D²/(20 C t)}` on `B_{3√t}(y)` (Theorem 4 at the pole `x`,
  `dgPhi_shift_le`);
* `|Δv| = |∂_t p(t, ·, x)| ≤ 2U'/h + B h ≤ F = C t^{-2} e^{-D²/(20 C t)}` there, with
  `h = t e^{-D²/(20 C t)}` (Taylor's formula `abs_deriv_le_of_taylor`, the second time derivative
  `abs_heatDeriv_two_le` and the diagonal bounds of Theorem 4);
* the elliptic oscillation estimate `exists_nL2_sub_le_of_laplacian` at the radius `3r` with
  `R = 3√t`, whose exit-time hypothesis is Theorem 4 on the balls;
* the Caccioppoli inequality `pairEnergy_le_of_laplacian` at the radius `r`, normalized with
  `|𝒞_∞ ∩ B_r(y)| ≥ c r²`;

so that `‖∇v‖_{L̲²(𝒞_∞ ∩ B_r(y))} ≤ C (U/R + R F) ≤ C t^{-3/2} e^{-D²/(C t)}`
(`sqrt_gradEnergy_openHeat_le`). The minimal scale is
`M(y) = max(X(y), T'(y)^{1/2}, M_dens(y), 9)`, with `X` the order-zero scale, `T'` the lattice
supremum (3.52) of `4 T_NA` and `M_dens` the scale of Proposition A.1.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

variable {p : unitInterval}

/-! ### Elementary facts -/

theorem sum_sq_eq_card_mul_nL2_sq {V : Type*} (S : Finset V) (f : V → ℝ) :
    ∑ x ∈ S, f x ^ 2 = S.card * nL2 S f ^ 2 := by
  unfold nL2
  have h0 : 0 ≤ (∑ x ∈ S, f x ^ 2) / S.card :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
  rw [Real.sq_sqrt h0]
  rcases Nat.eq_zero_or_pos S.card with hc | hc
  · rw [Finset.card_eq_zero.1 hc]; simp
  · rw [mul_div_cancel₀ _ (by exact_mod_cast hc.ne' : (S.card : ℝ) ≠ 0)]

/-- **Taylor's formula at first order**: `|f'(t)| ≤ 2A/h + B h` if `|f| ≤ A` and `|f''| ≤ B` on
`[t, t + h]`. -/
theorem abs_deriv_le_of_taylor {f f' f'' : ℝ → ℝ} {t h A B : ℝ} (hh : 0 < h)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : ∀ s, HasDerivAt f' (f'' s) s)
    (hA : ∀ s ∈ Set.Icc t (t + h), |f s| ≤ A) (hB : ∀ s ∈ Set.Icc t (t + h), |f'' s| ≤ B) :
    |f' t| ≤ 2 * A / h + B * h := by
  have h1 : ∀ s ∈ Set.Icc t (t + h), |f' s - f' t| ≤ B * (s - t) := by
    intro s hs
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f') (f' := f'') (a := t) (b := s)
      (C := B) (fun u _ => (hf' u).hasDerivWithinAt)
      (fun u hu => by
        rw [Real.norm_eq_abs]
        exact hB u ⟨hu.1, hu.2.le.trans hs.2⟩) s ⟨hs.1, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  have h2 : |(f (t + h) - (t + h) * f' t) - (f t - t * f' t)| ≤ B * h * ((t + h) - t) := by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => f s - s * f' t)
      (f' := fun s => f' s - f' t) (a := t) (b := t + h) (C := B * h)
      (fun u _ => ((hf u).fun_sub (hasDerivAt_mul_const (f' t))).hasDerivWithinAt)
      (fun u hu => by
        rw [Real.norm_eq_abs]
        have hu' : u ∈ Set.Icc t (t + h) := ⟨hu.1, hu.2.le⟩
        exact (h1 u hu').trans (mul_le_mul_of_nonneg_left (by linarith [hu.2])
          ((abs_nonneg _).trans (hB u hu')))) (t + h) ⟨by linarith, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  have hA1 := hA (t + h) ⟨by linarith, le_rfl⟩
  have hA2 := hA t ⟨le_rfl, by linarith⟩
  have key : h * |f' t| ≤ 2 * A + B * h * h := by
    have e : h * f' t = (f (t + h) - f t) - ((f (t + h) - (t + h) * f' t) - (f t - t * f' t)) := by
      ring
    have h3 : |f (t + h) - f t| ≤ |f (t + h)| + |f t| := abs_sub _ _
    calc h * |f' t| = |h * f' t| := by rw [abs_mul, abs_of_pos hh]
      _ ≤ |f (t + h) - f t| + |(f (t + h) - (t + h) * f' t) - (f t - t * f' t)| := by
          rw [e]; exact abs_sub _ _
      _ ≤ (|f (t + h)| + |f t|) + B * h * ((t + h) - t) := add_le_add h3 h2
      _ ≤ 2 * A + B * h * h := by
          have : (t + h) - t = h := by ring
          rw [this]; linarith
  rw [show 2 * A / h + B * h = (2 * A + B * h * h) / h by field_simp, le_div_iff₀ hh]
  linarith

theorem abs_latticeDist_sub_le_of_adj {ω : Configuration 2} {a b : Vertex 2}
    (hab : (openGraph ω).Adj a b) (y : Vertex 2) : |latticeDist a y - latticeDist b y| ≤ 1 := by
  have h1 := latticeDist_le_one_of_adj (ω := ω) hab
  have h2 := latticeDist_triangle a b y
  have h3 := latticeDist_triangle b a y
  rw [latticeDist_comm b a] at h2
  rw [abs_le]
  constructor <;> linarith

theorem boundaryAccessible_of_infinite {ω : Configuration 2} {K : OpenComponent ω}
    (hK : K.supp.Infinite) {A : Finset (Vertex 2)} (hA : ∀ v ∈ A, v ∈ K.supp) :
    LatticeProb.Network.BoundaryAccessible (openGraph ω) A := by
  intro v hv
  obtain ⟨w, hwK, hwA⟩ := (hK.sdiff A.finite_toSet).nonempty
  refine ⟨w, hwA, ?_⟩
  exact SimpleGraph.ConnectedComponent.exact
    (((SimpleGraph.ConnectedComponent.mem_supp_iff K v).1 (hA v hv)).trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff K w).1 hwK).symm)

/-! ### The deterministic estimate -/

/-- The constant of the gradient bound, as a function of the constant `CB` of Theorem 4, the
constant `C₀` of the order-zero estimate and the volume constant `cv`. -/
noncomputable def gradConst (CB C₀ cv : ℝ) : ℝ :=
  max (Real.sqrt ((1800 + 145800 * (C₀ + (10 * C₀ + 32) * (50 * CB + 1)) ^ 2) / cv) *
    (8 * CB * Real.exp (36 / (10 * CB)) / 3 +
      3 * (2 * (8 * CB * Real.exp (36 / (10 * CB))) + 32 * CB))) (20 * CB)

theorem gradConst_pos {CB C₀ cv : ℝ} (hCB : 0 < CB) : 0 < gradConst CB C₀ cv :=
  lt_max_of_lt_right (by positivity)

theorem slice_scales {r t : ℝ} (hr9 : 9 ≤ r) (hrt : 4 * r ^ 2 ≤ t) :
    0 < t ∧ 2 * r ≤ Real.sqrt t ∧ 3 * Real.sqrt t + 1 ≤ t := by
  have ht : 0 < t := by nlinarith
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have h2r : 2 * r ≤ Real.sqrt t := by
    rw [show 2 * r = Real.sqrt ((2 * r) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h18 : (18 : ℝ) ≤ Real.sqrt t := by linarith
  have h18' := mul_le_mul_of_nonneg_left h18 (Real.sqrt_nonneg t)
  exact ⟨ht, h2r, by nlinarith⟩

section Slice

variable {CB : ℝ} {ω : Configuration 2} {K : OpenComponent ω} {y x : Vertex 2} {r t : ℝ}

/-- Theorem 4 at the pole `x`, on the ball `B_{3√t}(y)` and for `s ∈ [t, 2t]`. -/
theorem openHeat_slice_le (hCB : 0 < CB) (hx : x ∈ K.supp) (hr9 : 9 ≤ r)
    (hrt : 4 * r ^ 2 ≤ t) (hDt : latticeDist x y ≤ t)
    (hB : ∀ w ∈ K.supp, ∀ τ, r ^ 2 ≤ τ → latticeDist w y ≤ τ + 1 → ∀ τ', τ / 4 ≤ τ' →
      ∀ z ∈ K.supp, openHeat ω τ' z w ≤ dgPhi CB τ' (latticeDist z w))
    {z : Vertex 2} (hz : z ∈ K.supp) (hzy : latticeDist z y < 3 * Real.sqrt t) {s : ℝ}
    (hs1 : t ≤ s) (hs2 : s ≤ 2 * t) :
    openHeat ω s z x ≤ 8 * CB * Real.exp (36 / (10 * CB)) * t⁻¹ *
      Real.exp (-(latticeDist x y ^ 2 / (10 * CB * t))) := by
  obtain ⟨ht, -, -⟩ := slice_scales hr9 hrt
  have h1 := hB x hx t (by nlinarith) (by linarith) s (by linarith) z hz
  have hρ : latticeDist x y - 3 * Real.sqrt t ≤ latticeDist z x := by
    have := latticeDist_triangle x z y
    linarith
  exact h1.trans (dgPhi_shift_le hCB ht (by linarith) hs2 (latticeDist_nonneg z x)
    (latticeDist_nonneg x y) hDt hρ)

/-- The diagonal bound of Theorem 4. -/
theorem openHeat_diag_slice_le (hCB : 0 < CB) (hr9 : 9 ≤ r) (hrt : 4 * r ^ 2 ≤ t)
    (hB : ∀ w ∈ K.supp, ∀ τ, r ^ 2 ≤ τ → latticeDist w y ≤ τ + 1 → ∀ τ', τ / 4 ≤ τ' →
      ∀ z ∈ K.supp, openHeat ω τ' z w ≤ dgPhi CB τ' (latticeDist z w))
    {w : Vertex 2} (hw : w ∈ K.supp) (hwy : latticeDist w y ≤ t + 1) {s : ℝ} (hs : t ≤ s) :
    openHeat ω (s / 4) w w ≤ 4 * CB / s := by
  have ht : 0 < t := by nlinarith
  have hs0 : 0 < s := by linarith
  have h1 := hB w hw t (by nlinarith) hwy (s / 4) (by linarith) w hw
  rw [latticeDist_self, dgPhi_zero_eq (by positivity)] at h1
  calc openHeat ω (s / 4) w w ≤ CB * (s / 4)⁻¹ := h1
    _ = 4 * CB / s := by field_simp

/-- The second time derivative on the ball `B_{3√t}(y)`. -/
theorem abs_heatDeriv_two_slice_le (hCB : 0 < CB) (hx : x ∈ K.supp) (hr9 : 9 ≤ r)
    (hrt : 4 * r ^ 2 ≤ t) (hDt : latticeDist x y ≤ t)
    (hB : ∀ w ∈ K.supp, ∀ τ, r ^ 2 ≤ τ → latticeDist w y ≤ τ + 1 → ∀ τ', τ / 4 ≤ τ' →
      ∀ z ∈ K.supp, openHeat ω τ' z w ≤ dgPhi CB τ' (latticeDist z w))
    {z : Vertex 2} (hz : z ∈ K.supp) (hzy : latticeDist z y < 3 * Real.sqrt t) {s : ℝ}
    (hs : t ≤ s) : |heatDeriv (openGraph ω) 4 2 s z x| ≤ 32 * CB / t ^ 3 := by
  obtain ⟨ht, -, h3t⟩ := slice_scales hr9 hrt
  have hs0 : 0 < s := by linarith
  have h1 := abs_heatDeriv_two_le (by norm_num : 0 < 4) (openGraph_degree_le_four ω) hs0 z x
  have hz' := openHeat_diag_slice_le hCB hr9 hrt hB hz (by linarith) hs
  have hx' := openHeat_diag_slice_le hCB hr9 hrt hB hx (by linarith) hs
  have hpx : 0 ≤ openHeat ω (s / 4) x x := openHeat_nonneg ω (by positivity) x x
  have hprod : vsrwHeat (openGraph ω) 4 (s / 4) z z * vsrwHeat (openGraph ω) 4 (s / 4) x x ≤
      (4 * CB / s) ^ 2 := by
    rw [sq]
    exact mul_le_mul hz' hx' hpx (by positivity)
  have hsq' : Real.sqrt (vsrwHeat (openGraph ω) 4 (s / 4) z z *
      vsrwHeat (openGraph ω) 4 (s / 4) x x) ≤ 4 * CB / s :=
    (Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq (by positivity))
  calc |heatDeriv (openGraph ω) 4 2 s z x| ≤ 8 / s ^ 2 * (4 * CB / s) :=
        h1.trans (mul_le_mul_of_nonneg_left hsq' (by positivity))
    _ = 32 * CB / s ^ 3 := by field_simp; ring
    _ ≤ 32 * CB / t ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ ht.le hs 3)

/-- The Laplacian of the time slice `p(t, x, ·)` on the ball `B_{3√t}(y)`, by Taylor's formula with
`h = t e^{-D²/(20 C t)}`. -/
theorem abs_laplacian_slice_le (hCB : 0 < CB) (hx : x ∈ K.supp) (hr9 : 9 ≤ r)
    (hrt : 4 * r ^ 2 ≤ t) (hDt : latticeDist x y ≤ t)
    (hB : ∀ w ∈ K.supp, ∀ τ, r ^ 2 ≤ τ → latticeDist w y ≤ τ + 1 → ∀ τ', τ / 4 ≤ τ' →
      ∀ z ∈ K.supp, openHeat ω τ' z w ≤ dgPhi CB τ' (latticeDist z w))
    {z : Vertex 2} (hz : z ∈ K.supp) (hzy : latticeDist z y < 3 * Real.sqrt t) :
    |LatticeProb.Graph.laplacian (openGraph ω) (fun z => openHeat ω t x z) z| ≤
      (2 * (8 * CB * Real.exp (36 / (10 * CB))) + 32 * CB) * (t ^ 2)⁻¹ *
        Real.exp (-(latticeDist x y ^ 2 / (20 * CB * t))) := by
  obtain ⟨ht, -, -⟩ := slice_scales hr9 hrt
  have hdeg := openGraph_degree_le_four ω
  have hLv : LatticeProb.Graph.laplacian (openGraph ω) (fun z => openHeat ω t x z) z =
      heatDeriv (openGraph ω) 4 1 t z x := by
    rw [heatDeriv_symm (by norm_num) hdeg 1 t z x,
      heatDeriv_one_eq_laplacian (by norm_num) hdeg t x z]
    rfl
  rw [hLv]
  have hE2 : Real.exp (-(latticeDist x y ^ 2 / (10 * CB * t))) =
      Real.exp (-(latticeDist x y ^ 2 / (20 * CB * t))) *
        Real.exp (-(latticeDist x y ^ 2 / (20 * CB * t))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hgauss := fun s (hs1 : t ≤ s) (hs2 : s ≤ 2 * t) =>
    openHeat_slice_le hCB hx hr9 hrt hDt hB hz hzy hs1 hs2
  generalize hE : Real.exp (-(latticeDist x y ^ 2 / (20 * CB * t))) = E at hE2 ⊢
  rw [hE2] at hgauss
  have hE0 : 0 < E := by rw [← hE]; exact Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [← hE]
    apply Real.exp_le_one_iff.2
    have : 0 ≤ latticeDist x y ^ 2 / (20 * CB * t) := by positivity
    linarith
  have hE0' : E ≠ 0 := hE0.ne'
  have ht' : t ≠ 0 := ht.ne'
  have hh : 0 < t * E := by positivity
  have hht : t * E ≤ t := by nlinarith
  have htay := abs_deriv_le_of_taylor (f := fun s => heatDeriv (openGraph ω) 4 0 s z x)
    (f' := fun s => heatDeriv (openGraph ω) 4 1 s z x)
    (f'' := fun s => heatDeriv (openGraph ω) 4 2 s z x)
    (A := 8 * CB * Real.exp (36 / (10 * CB)) * t⁻¹ * (E * E)) (B := 32 * CB / t ^ 3) hh
    (fun s => hasDerivAt_heatDeriv (by norm_num) hdeg 0 s z x)
    (fun s => hasDerivAt_heatDeriv (by norm_num) hdeg 1 s z x)
    (fun s hs => by
      have hs0 : 0 ≤ s := by linarith [hs.1]
      show |vsrwHeat (openGraph ω) 4 s z x| ≤ _
      rw [abs_of_nonneg (vsrwHeat_nonneg (by norm_num) hdeg hs0 z x)]
      exact hgauss s hs.1 (by linarith [hs.2]))
    (fun s hs => abs_heatDeriv_two_slice_le hCB hx hr9 hrt hDt hB hz hzy hs.1)
  refine htay.trans (le_of_eq ?_)
  field_simp

end Slice

/-- Theorem 4 on the balls gives the exit-time hypothesis of the elliptic estimate. -/
theorem exitHyp_clusterBall {CB : ℝ} (hCB : 0 < CB) {ω : Configuration 2} {K : OpenComponent ω}
    {y : Vertex 2} {r : ℝ} (hr1 : 1 ≤ r)
    (hB : ∀ w ∈ K.supp, ∀ τ, r ^ 2 ≤ τ → latticeDist w y ≤ τ + 1 → ∀ τ', τ / 4 ≤ τ' →
      ∀ z ∈ K.supp, openHeat ω τ' z w ≤ dgPhi CB τ' (latticeDist z w)) :
    ∀ ρ, r ≤ ρ → ∀ z ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) 4 ((50 * CB + 1) * ρ ^ 2) z w ≤ 1 / 2 := by
  intro ρ hρ z hz
  have hρ1 : 1 ≤ ρ := hr1.trans hρ
  have hA1 : 1 ≤ 50 * CB + 1 := by linarith
  have hτ : 0 < (50 * CB + 1) * ρ ^ 2 := by positivity
  have hzK : z ∈ K.supp := (mem_clusterBall.1 (interiorOf_subset _ hz)).1
  have hterm : ∀ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      vsrwHeat (openGraph ω) 4 ((50 * CB + 1) * ρ ^ 2) z w ≤ CB * ((50 * CB + 1) * ρ ^ 2)⁻¹ := by
    intro w hw
    have hw' := mem_clusterBall.1 (interiorOf_subset _ hw)
    have hρ2 : ρ ≤ (50 * CB + 1) * ρ ^ 2 := by nlinarith
    have h1 := hB w hw'.1 ((50 * CB + 1) * ρ ^ 2) (by nlinarith) (by linarith [hw'.2])
      ((50 * CB + 1) * ρ ^ 2) (by linarith) z hzK
    have h2 := dgPhi_anti hCB hτ le_rfl (latticeDist_nonneg z w)
    rw [dgPhi_zero_eq hτ] at h2
    exact h1.trans h2
  have hc1 : ((interiorOf (openGraph ω) (clusterBall K y ρ)).card : ℝ) ≤
      (clusterBall K y ρ).card := by
    exact_mod_cast Finset.card_le_card (interiorOf_subset _)
  have hcard := hc1.trans (card_clusterBall_le K y hρ1)
  calc ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) 4 ((50 * CB + 1) * ρ ^ 2) z w
      ≤ ∑ _w ∈ interiorOf (openGraph ω) (clusterBall K y ρ), CB * ((50 * CB + 1) * ρ ^ 2)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (interiorOf (openGraph ω) (clusterBall K y ρ)).card *
          (CB * ((50 * CB + 1) * ρ ^ 2)⁻¹) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 25 * ρ ^ 2 * (CB * ((50 * CB + 1) * ρ ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 25 * CB / (50 * CB + 1) := by field_simp
    _ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith

/-- The combination of the oscillation estimate, the Caccioppoli inequality and the volume bound. -/
theorem sqrt_div_le_of_energy {Γ P N0 NW SW N3 nl Q K₁ cv r F : ℝ} (hcv : 0 < cv) (hr : 0 < r)
    (hQ : 0 ≤ Q) (hΓ : Γ ≤ 4 * P) (hP : P ≤ 2 * r ^ 2 * F ^ 2 * NW + 18 / r ^ 2 * SW)
    (hNW : NW ≤ 225 * r ^ 2) (hNW0 : 0 ≤ NW) (hSW : SW ≤ N3 * nl ^ 2)
    (hN3 : N3 ≤ 225 * r ^ 2) (hnl0 : 0 ≤ nl) (hnl : nl ≤ K₁ * (3 * r) * Q)
    (hrF : r ^ 2 * F ^ 2 ≤ Q ^ 2) (hN0 : cv * r ^ 2 ≤ N0) :
    Real.sqrt (Γ / N0) ≤ Real.sqrt ((1800 + 145800 * K₁ ^ 2) / cv) * Q := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hnl2 : nl ^ 2 ≤ (K₁ * (3 * r) * Q) ^ 2 := pow_le_pow_left₀ hnl0 hnl 2
  have hS : SW ≤ 225 * r ^ 2 * (K₁ * (3 * r) * Q) ^ 2 :=
    hSW.trans (mul_le_mul hN3 hnl2 (sq_nonneg _) (by positivity))
  have e1 : 18 / r ^ 2 * SW ≤ 36450 * K₁ ^ 2 * r ^ 2 * Q ^ 2 := by
    calc 18 / r ^ 2 * SW ≤ 18 / r ^ 2 * (225 * r ^ 2 * (K₁ * (3 * r) * Q) ^ 2) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 36450 * K₁ ^ 2 * r ^ 2 * Q ^ 2 := by field_simp; ring
  have e2 : 2 * r ^ 2 * F ^ 2 * NW ≤ 450 * r ^ 2 * Q ^ 2 := by
    calc 2 * r ^ 2 * F ^ 2 * NW = 2 * (r ^ 2 * F ^ 2) * NW := by ring
      _ ≤ 2 * Q ^ 2 * (225 * r ^ 2) :=
          mul_le_mul (by linarith) hNW hNW0 (by positivity)
      _ = 450 * r ^ 2 * Q ^ 2 := by ring
  have hΓ' : Γ ≤ (1800 + 145800 * K₁ ^ 2) * r ^ 2 * Q ^ 2 := by nlinarith
  have hN0' : 0 < N0 := lt_of_lt_of_le (by positivity) hN0
  have hratio : Γ / N0 ≤ ((1800 + 145800 * K₁ ^ 2) / cv) * Q ^ 2 := by
    rw [div_le_iff₀ hN0']
    calc Γ ≤ (1800 + 145800 * K₁ ^ 2) * r ^ 2 * Q ^ 2 := hΓ'
      _ = ((1800 + 145800 * K₁ ^ 2) / cv) * Q ^ 2 * (cv * r ^ 2) := by field_simp
      _ ≤ ((1800 + 145800 * K₁ ^ 2) / cv) * Q ^ 2 * N0 :=
          mul_le_mul_of_nonneg_left hN0 (by positivity)
  calc Real.sqrt (Γ / N0) ≤ Real.sqrt (((1800 + 145800 * K₁ ^ 2) / cv) * Q ^ 2) :=
        Real.sqrt_le_sqrt hratio
    _ = Real.sqrt ((1800 + 145800 * K₁ ^ 2) / cv) * Q := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hQ]

/-- **The gradient bound at one time slice** (deterministic form). -/
theorem sqrt_gradEnergy_openHeat_le {CB C₀ cv : ℝ} (hCB : 0 < CB) (hC₀ : 0 < C₀) (hcv : 0 < cv)
    {ω : Configuration 2} {K : OpenComponent ω} (hK : K.supp.Infinite) {y x : Vertex 2}
    (hx : x ∈ K.supp) {r t X : ℝ} (hr9 : 9 ≤ r) (hrt : 4 * r ^ 2 ≤ t)
    (hDt : latticeDist x y ≤ t) (hXr : X ≤ r)
    (hOZ : ∀ R', 2 * X ≤ R' → ∀ u : Vertex 2 → ℝ,
      (∀ z ∈ interiorOf (openGraph ω) (clusterBall K y R'),
        LatticeProb.Graph.laplacian (openGraph ω) u z = 0) →
      ∃ c : ℝ, ∀ ρ, X ≤ ρ → ρ ≤ R' / 2 →
        nL2 (clusterBall K y ρ) (fun z => u z - c) ≤ C₀ * (ρ / R') * nL2 (clusterBall K y R') u)
    (hB : ∀ w ∈ K.supp, ∀ τ, r ^ 2 ≤ τ → latticeDist w y ≤ τ + 1 → ∀ τ', τ / 4 ≤ τ' →
      ∀ z ∈ K.supp, openHeat ω τ' z w ≤ dgPhi CB τ' (latticeDist z w))
    (hvol : cv * r ^ 2 ≤ (clusterBall K y r).card) :
    Real.sqrt (gradEnergy ω (clusterBall K y r) (fun z => openHeat ω t x z) /
        (clusterBall K y r).card) ≤
      gradConst CB C₀ cv * t ^ (-(3 / 2 : ℝ)) *
        Real.exp (-(latticeDist x y ^ 2 / (gradConst CB C₀ cv * t))) := by
  obtain ⟨ht, h2r, h3t⟩ := slice_scales hr9 hrt
  have hr0 : 0 < r := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hdeg := openGraph_degree_le_four ω
  -- the bounds on `B_{3√t}(y)`
  have hE20 : Real.exp (-(latticeDist x y ^ 2 / (10 * CB * t))) ≤
      Real.exp (-(latticeDist x y ^ 2 / (20 * CB * t))) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith [mul_pos hCB ht])
  have hU : ∀ z ∈ clusterBall K y (3 * Real.sqrt t), |openHeat ω t x z| ≤
      8 * CB * Real.exp (36 / (10 * CB)) * t⁻¹ *
        Real.exp (-(latticeDist x y ^ 2 / (20 * CB * t))) := by
    intro z hz
    have hz' := mem_clusterBall.1 hz
    rw [abs_of_nonneg (openHeat_nonneg ω ht.le x z), openHeat_symm]
    exact (openHeat_slice_le hCB hx hr9 hrt hDt hB hz'.1 hz'.2 le_rfl (by linarith)).trans
      (mul_le_mul_of_nonneg_left hE20 (by positivity))
  have hF : ∀ z ∈ clusterBall K y (3 * Real.sqrt t),
      |LatticeProb.Graph.laplacian (openGraph ω) (fun z => openHeat ω t x z) z| ≤
        (2 * (8 * CB * Real.exp (36 / (10 * CB))) + 32 * CB) * (t ^ 2)⁻¹ *
          Real.exp (-(latticeDist x y ^ 2 / (20 * CB * t))) := fun z hz =>
    abs_laplacian_slice_le hCB hx hr9 hrt hDt hB (mem_clusterBall.1 hz).1 (mem_clusterBall.1 hz).2
  generalize hE : Real.exp (-(latticeDist x y ^ 2 / (20 * CB * t))) = E at hU hF
  generalize ha₀ : 8 * CB * Real.exp (36 / (10 * CB)) = a₀ at hU hF
  have hE0 : 0 < E := by rw [← hE]; exact Real.exp_pos _
  have ha₀0 : 0 < a₀ := by rw [← ha₀]; positivity
  have hU0 : 0 ≤ a₀ * t⁻¹ * E := by positivity
  have hF0 : 0 ≤ (2 * a₀ + 32 * CB) * (t ^ 2)⁻¹ * E := by positivity
  -- the elliptic oscillation estimate at the radius `3r`
  have hacc : ∀ ρ, LatticeProb.Network.BoundaryAccessible (openGraph ω)
      (interiorOf (openGraph ω) (clusterBall K y ρ)) :=
    fun ρ => boundaryAccessible_of_infinite hK fun v hv =>
      (mem_clusterBall.1 (interiorOf_subset _ hv)).1
  obtain ⟨c, hc⟩ := exists_nL2_sub_le_of_laplacian (G := openGraph ω) (D := 4) (by norm_num) hdeg
    (B := clusterBall K y) (fun ρ ρ' h => clusterBall_mono h) hacc hC₀.le hOZ
    (A := 50 * CB + 1) (ρ₀ := r) (by linarith) (exitHyp_clusterBall hCB (by linarith) hB)
    (r := 3 * r) (R := 3 * Real.sqrt t) (by linarith) (by positivity) (by linarith)
    (by linarith) hU0 hF0 (v := fun z => openHeat ω t x z) hU
    (fun z hz => hF z (interiorOf_subset _ hz))
  -- the Caccioppoli inequality at the radius `r`
  have hcac := pairEnergy_le_of_laplacian (G := openGraph ω) (D := 4) hdeg
    (δ := fun z => latticeDist z y) (fun a b hab => abs_latticeDist_sub_le_of_adj hab y)
    (P := fun z => z ∈ K.supp) (fun a b hab ha => K.mem_supp_of_adj_mem_supp ha hab)
    (B := clusterBall K y) (fun ρ z => mem_clusterBall) hr0 (fun z => openHeat ω t x z) c hF0
    (fun z hz => hF z (clusterBall_mono (by linarith) hz))
  -- the combination
  have hsub : clusterBall K y (2 * r + 2) ⊆ clusterBall K y (3 * r) := clusterBall_mono (by linarith)
  have hN3 : ((clusterBall K y (3 * r)).card : ℝ) ≤ 225 * r ^ 2 := by
    have := card_clusterBall_le K y (show 1 ≤ 3 * r by linarith)
    nlinarith
  have hNW : ((clusterBall K y (2 * r + 2)).card : ℝ) ≤ 225 * r ^ 2 :=
    (by exact_mod_cast Finset.card_le_card hsub : ((clusterBall K y (2 * r + 2)).card : ℝ) ≤
      (clusterBall K y (3 * r)).card).trans hN3
  have hSW : ∑ z ∈ clusterBall K y (2 * r + 2), (openHeat ω t x z - c) ^ 2 ≤
      (clusterBall K y (3 * r)).card *
        nL2 (clusterBall K y (3 * r)) (fun z => openHeat ω t x z - c) ^ 2 := by
    rw [← sum_sq_eq_card_mul_nL2_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  set Q := a₀ * t⁻¹ * E / (3 * Real.sqrt t) + 3 * Real.sqrt t * ((2 * a₀ + 32 * CB) * (t ^ 2)⁻¹ * E)
    with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hrF : r ^ 2 * ((2 * a₀ + 32 * CB) * (t ^ 2)⁻¹ * E) ^ 2 ≤ Q ^ 2 := by
    have h1 : r * ((2 * a₀ + 32 * CB) * (t ^ 2)⁻¹ * E) ≤ Q := by
      have h2 : r * ((2 * a₀ + 32 * CB) * (t ^ 2)⁻¹ * E) ≤
          3 * Real.sqrt t * ((2 * a₀ + 32 * CB) * (t ^ 2)⁻¹ * E) :=
        mul_le_mul_of_nonneg_right (by linarith) hF0
      have h3 : 0 ≤ a₀ * t⁻¹ * E / (3 * Real.sqrt t) := by positivity
      rw [hQ]
      linarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hgrad := gradEnergyOn_le (G := openGraph ω) (D := 4) hdeg (clusterBall K y r)
    (fun z => openHeat ω t x z)
  have h18 : (4 * ((4 : ℕ) : ℝ) + 2) = 18 := by norm_num
  rw [h18] at hcac
  have hmain := sqrt_div_le_of_energy (Γ := gradEnergy ω (clusterBall K y r)
      (fun z => openHeat ω t x z)) (K₁ := C₀ + (10 * C₀ + 32) * (50 * CB + 1)) hcv hr0 hQ0
    (by exact_mod_cast hgrad) hcac hNW (Nat.cast_nonneg _) hSW hN3 (nL2_nonneg _ _) hc hrF hvol
  -- the constant
  have hinv : (t ^ 2)⁻¹ * Real.sqrt t = (t * Real.sqrt t)⁻¹ := by
    have e : t ^ 2 = t * Real.sqrt t * Real.sqrt t := by
      rw [mul_assoc, Real.mul_self_sqrt ht.le, sq]
    rw [e, mul_inv, mul_assoc, inv_mul_cancel₀ hst.ne', mul_one]
  have hQeq : Q = (a₀ / 3 + 3 * (2 * a₀ + 32 * CB)) * (t * Real.sqrt t)⁻¹ * E := by
    rw [hQ, show 3 * Real.sqrt t * ((2 * a₀ + 32 * CB) * (t ^ 2)⁻¹ * E) =
      3 * (2 * a₀ + 32 * CB) * ((t ^ 2)⁻¹ * Real.sqrt t) * E by ring, hinv]
    simp only [mul_inv, div_eq_mul_inv]
    ring
  have hG1 : Real.sqrt ((1800 + 145800 * (C₀ + (10 * C₀ + 32) * (50 * CB + 1)) ^ 2) / cv) *
      (a₀ / 3 + 3 * (2 * a₀ + 32 * CB)) ≤ gradConst CB C₀ cv := by
    rw [gradConst, ← ha₀]
    exact le_max_left _ _
  have hG2 : 20 * CB ≤ gradConst CB C₀ cv := le_max_right _ _
  have hGpos := gradConst_pos (C₀ := C₀) (cv := cv) hCB
  have hEle : E ≤ Real.exp (-(latticeDist x y ^ 2 / (gradConst CB C₀ cv * t))) := by
    rw [← hE]
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_right hG2 ht.le)
  rw [rpow_neg_three_halves ht]
  refine hmain.trans ?_
  rw [hQeq]
  have hT0 : 0 ≤ (t * Real.sqrt t)⁻¹ := by positivity
  calc Real.sqrt ((1800 + 145800 * (C₀ + (10 * C₀ + 32) * (50 * CB + 1)) ^ 2) / cv) *
        ((a₀ / 3 + 3 * (2 * a₀ + 32 * CB)) * (t * Real.sqrt t)⁻¹ * E)
      = Real.sqrt ((1800 + 145800 * (C₀ + (10 * C₀ + 32) * (50 * CB + 1)) ^ 2) / cv) *
          (a₀ / 3 + 3 * (2 * a₀ + 32 * CB)) * (t * Real.sqrt t)⁻¹ * E := by ring
    _ ≤ gradConst CB C₀ cv * (t * Real.sqrt t)⁻¹ * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG1 hT0) hE0.le
    _ ≤ gradConst CB C₀ cv * (t * Real.sqrt t)⁻¹ *
        Real.exp (-(latticeDist x y ^ 2 / (gradConst CB C₀ cv * t))) :=
        mul_le_mul_of_nonneg_left hEle (by positivity)

/-! ### Theorem 3 -/

/-- **Dario–Gu, Theorem 3 (Remark 1.3) in dimension two, from Theorem 4**: the gradient bound
`DarioGuGradientBoundTwo` follows from the Gaussian upper bound of Barlow, with the order-zero
regularity of Armstrong and Dario and Proposition A.1, which are proved. -/
theorem darioGuGradientBoundTwo_of_barlow (hBar : BarlowGaussianUpperBoundTwo) :
    DarioGuGradientBoundTwo := by
  intro p hpc hp1
  -- Theorem 4 and the lattice supremum of `4 T_NA`
  obtain ⟨sB, CB, hsB, hCB, hB'⟩ := hBar p hpc hp1
  choose TB hTBm hTB0 hTBos hTBae using hB'
  have g4 := (goodTimes_of_isOsBond hsB hCB hTBm hTB0 hTBos).const_mul (c := 4) (by norm_num)
  obtain ⟨⟨hSm, hS0, CS, sS, hCS, hsS, hSt⟩, hbdd⟩ := goodTimes_latticeSup g4
  -- the order-zero estimate
  obtain ⟨sX, θX, C₀, hsX, hθX, hC₀, X, hXm, hX0, hXos, hXae⟩ := exists_orderZero_clusterBall hpc hp1
  -- Proposition A.1
  obtain ⟨sD, CD, cD, hsD, hCD, hcD, hD⟩ :=
    Rigidity.Proofs.S2.clusterDensityInputFaithful_of_concentration
      Rigidity.Proofs.S2.cluster_density_concentration 2 le_rfl p hpc hp1
  choose MD hMDm hMD0 hMDos hMDae using hD
  -- the constants
  set cv := cD * 100 ^ 2 with hcv
  have hcv0 : 0 < cv := by positivity
  set Cg := gradConst CB C₀ cv with hCg
  have hCg0 : 0 < Cg := gradConst_pos hCB
  set CX := max 2 (θX ^ sX) with hCX
  set CMD := max 2 (CD ^ sD) with hCMD
  set C1 := max (max CX CMD) CS with hC1
  have hC12 : 2 ≤ C1 := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hC10 : 0 < C1 := by linarith
  set s := min (min sX sD) (sS / (1 / 2)) with hs
  have hs0 : 0 < s := lt_min (lt_min hsX hsD) (by positivity)
  set Ctail := max (2 * (2 * C1)) (max 3 (Real.rpow 9 s)) with hCtail
  have hCtail0 : 0 < Ctail := lt_max_of_lt_left (by positivity)
  set Cout := max Cg Ctail with hCout
  have hCout0 : 0 < Cout := lt_max_of_lt_left hCg0
  refine ⟨s, Cout, hs0, hCout0, fun y => ?_⟩
  -- the minimal scale
  set S := fun ω => latticeSup (fun w ω => 4 * TB w ω) y ω with hSdef
  set M : Configuration 2 → ℝ := fun ω =>
    max (max (max (X y ω) (S ω ^ (1 / 2 : ℝ))) (MD y ω)) 9 with hM
  have hMm : Measurable M :=
    ((((hXm y).max ((hSm y).pow_const _)).max (hMDm y)).max measurable_const)
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => le_max_of_le_right (by norm_num)
  -- the tail of the minimal scale
  have hXt : HasTail p (X y) C1 s :=
    ((hasTail_of_isOsBond hsX hθX (hXos y)).mono (by positivity)
      ((le_max_left _ _).trans (le_max_left _ _))).mono_exponent hC12 hs0
      ((min_le_left _ _).trans (min_le_left _ _))
  have hSt' : HasTail p (fun ω => S ω ^ (1 / 2 : ℝ)) C1 s :=
    (((hSt y).rpow (by norm_num) (hS0 y)).mono (by linarith) (le_max_right _ _)).mono_exponent
      hC12 hs0 (min_le_right _ _)
  have hMDt : HasTail p (MD y) (2 * C1) s :=
    ((hasTail_of_isOsBond hsD hCD (hMDos y)).mono (by positivity)
      (((le_max_right _ _).trans (le_max_left _ _)).trans (by linarith))).mono_exponent
      (by linarith) hs0 ((min_le_left _ _).trans (min_le_right _ _))
  have hT1 := hXt.max hSt' hC10
  have hT2 := hT1.max hMDt (by positivity)
  have hT3 := hT2.max_const (a := 9) (by positivity) hs0
  have hMt : HasTail p M Cout s := hT3.mono hCtail0 (le_max_right _ _)
  refine ⟨M, hMm, hM0, hMt, ?_⟩
  -- the almost sure estimate
  filter_upwards [hXae, ae_all_iff.2 hTBae, hbdd y, hMDae y] with ω hXω hBω hbω hDω
  intro h r hr x hx t ht hdist
  set K := uniqueInfiniteComponent h with hK
  have hr9 : 9 ≤ r := (le_max_right _ _).trans hr
  have hXr : X y ω ≤ r :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hr
  have hSr' : S ω ^ (1 / 2 : ℝ) ≤ r :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hr
  have hMDr : MD y ω ≤ r := ((le_max_right _ _).trans (le_max_left _ _)).trans hr
  have hS0' : 0 ≤ S ω := hS0 y ω
  have hSr : S ω ≤ r ^ 2 := by
    have e : S ω = (S ω ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0']
      norm_num
    rw [e]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hS0' _) hSr' 2
  have hB : ∀ w ∈ K.supp, ∀ τ, r ^ 2 ≤ τ → latticeDist w y ≤ τ + 1 → ∀ τ', τ / 4 ≤ τ' →
      ∀ z ∈ K.supp, openHeat ω τ' z w ≤ dgPhi CB τ' (latticeDist z w) := by
    intro w hwK τ hτ hwτ τ' hτ' z hz
    have h4 : 4 * TB w ω ≤ τ :=
      le_of_latticeSup_le (T := fun w ω => 4 * TB w ω) hbω (hSr.trans hτ) hwτ
    have hτ'0 : 0 < τ' := by nlinarith
    exact hBω w h hwK τ' hτ'0 (by linarith) z hz
  have hvol : cv * r ^ 2 ≤ (clusterBall K y r).card := by
    have h1 := hDω h (100 * r) (by linarith) (latticeEuclideanEmbedding y) (by
      rw [dist_self]
      positivity)
    rw [show 100 * r / 100 = r by ring, ncard_eq_card_clusterBall] at h1
    calc cv * r ^ 2 = cD * (100 * r) ^ 2 := by rw [hcv]; ring
      _ ≤ _ := h1
  have key := sqrt_gradEnergy_openHeat_le hCB hC₀ hcv0 (uniqueInfiniteComponent_infinite h) hx
    hr9 ht hdist hXr (hXω h y) hB hvol
  refine key.trans ?_
  have ht0 : 0 < t := by nlinarith
  have hT : 0 ≤ t ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
  have hle : Cg ≤ Cout := le_max_left _ _
  apply mul_le_mul (mul_le_mul_of_nonneg_right hle hT) _ (Real.exp_pos _).le
    (mul_nonneg hCout0.le hT)
  apply Real.exp_le_exp.2
  rw [neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right hle ht0.le)

end Rigidity.Green

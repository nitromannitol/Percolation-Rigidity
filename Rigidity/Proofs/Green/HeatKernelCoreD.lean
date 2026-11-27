import Rigidity.Proofs.Green.PointwiseGaussianFactorD
import Rigidity.Proofs.Green.PointSourceDecayD
import Rigidity.Proofs.Green.ExitTimeD
import Rigidity.Proofs.Green.BondGaussianInputs
import Rigidity.Proofs.Green.BondCarneVaropoulos

/-!
# Theorem 1 of Dario–Gu on `ℤ^d` at one configuration

The deterministic steps of the proof of Theorem 1 of Dario–Gu along the passage from smooth
initial data to a point source, with every threshold of the inputs taken as a hypothesis:

* `cvBranches_sixteen`: the Carne–Varopoulos bound (`bondHeat_le_of_latticeDist_le`,
  `bondHeat_le_exp_of_le_latticeDist`) in the two-branch form `CVBranches` with constant `16 d`;
* `dgPhiDim_le_rpow`, `dgPhiDim_of_le`: `Φ_C(t, r) ≤ C t^{-d/2}`, and its Gaussian branch;
* `latticeDist_midLattice_le`: the lattice point `midLattice x y` is within `|x - y|/2 + d` of
  `y`;
* `exists_l2norm_pointSource_le_rpow`: `‖p_s(·, w) - G^w_s‖ ≤ C s^{3η - d/4 - 1/2}` above a
  deterministic time, from the order-zero estimate at `w`, the on-diagonal bound of the heat
  kernel near `w`, Proposition A.7 at `w` and the whole-cluster estimate at `w`
  (`l2norm_pointSource_le_of_time` with `eventually_psBound_le`);
* `exists_abs_vsrwHeat_sub_le_gaussian`: the error of Theorem 1 at a pair of points
  `|p_t(x, y) - θ^{-1} p̄(t, x - y)| ≤ C t^{-d/2 - (1/2 - 6η)} e^{-|x - y|²/(C t)}` for
  `|x - y| ≤ t` from the point source at both poles at time `t/2`, Proposition A.7 at `x`, `y`
  and `midLattice x y`, and the Gaussian upper bound at `y`
  (`abs_vsrwHeat_sub_le_rpow`, `abs_vsrwHeat_sub_le_gaussian`).
-/

open scoped Classical
open Filter LatticeProb.Percolation Rigidity.WeakPoincare

namespace Rigidity.Green

local notation "ldist" => Rigidity.WeakPoincare.latticeDist

variable {d : ℕ} [NeZero d]

/-- **The Carne–Varopoulos bound in two branches** with the constant `16 d`. -/
theorem cvBranches_sixteen (ω : Configuration d) {u : ℝ} (hu : 0 < u) (w : Vertex d) :
    CVBranches ω (16 * (d : ℝ)) u w := by
  intro x
  have hd1 := one_le_dim_real (d := d)
  have e : vsrwHeat (openGraph ω) (2 * d) u w x = bondHeat ω u w x := rfl
  rw [e]
  have hr' : ldist w x = ldist x w := WeakPoincare.latticeDist_comm w x
  have hr0 : 0 ≤ ldist x w := WeakPoincare.latticeDist_nonneg x w
  have hG : 0 ≤ 16 * (d : ℝ) * Real.exp (-(ldist x w ^ 2 / (16 * (d : ℝ) * u))) := by
    positivity
  rcases le_or_gt (ldist x w) u with h | h
  · have h1 := bondHeat_le_of_latticeDist_le ω hu (x := w) (y := x) (by rw [hr']; exact h)
    rw [hr'] at h1
    have hI : 0 ≤ (if u ≤ ldist x w then 16 * (d : ℝ) * Real.exp (-(ldist x w / (16 * d)))
        else 0) := by
      split_ifs <;> positivity
    have he := Real.exp_pos (-(ldist x w ^ 2 / (16 * (d : ℝ) * u)))
    calc bondHeat ω u w x ≤ 3 * Real.exp (-(ldist x w ^ 2 / (16 * d * u))) := h1
      _ ≤ 16 * (d : ℝ) * Real.exp (-(ldist x w ^ 2 / (16 * (d : ℝ) * u))) :=
          mul_le_mul_of_nonneg_right (by linarith) he.le
      _ ≤ _ := le_add_of_nonneg_right hI
  · have h1 := bondHeat_le_exp_of_le_latticeDist ω hu (x := w) (y := x) (by rw [hr']; exact h.le)
    rw [hr'] at h1
    rw [if_pos h.le]
    have hE : Real.exp (-(ldist x w / (8 * d))) ≤
        Real.exp (-(ldist x w / (16 * d))) := by
      apply Real.exp_le_exp.2
      rw [neg_le_neg_iff]
      exact div_le_div_of_nonneg_left hr0 (by linarith) (by linarith)
    have he := Real.exp_pos (-(ldist x w / (16 * (d : ℝ))))
    calc bondHeat ω u w x ≤ 3 * Real.exp (-(ldist x w / (8 * d))) := h1
      _ ≤ 16 * (d : ℝ) * Real.exp (-(ldist x w / (16 * d))) :=
          mul_le_mul (by linarith) hE (Real.exp_pos _).le (by positivity)
      _ ≤ _ := le_add_of_nonneg_left hG

omit [NeZero d] in
/-- `Φ_C(t, r) ≤ C t^{-d/2}`. -/
theorem dgPhiDim_le_rpow {C t r : ℝ} (hC : 0 < C) (ht : 0 < t) (hr : 0 ≤ r) :
    dgPhiDim d C t r ≤ C * t ^ (-((d : ℝ) / 2)) := by
  rw [dgPhiDim_eq_rpow d ht.le, dgExponent_eq]
  have h0 : 0 ≤ dgShape t r / C := div_nonneg (dgShape_nonneg ht hr) hC.le
  have h1 : Real.exp (-(dgShape t r / C)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : 0 ≤ C * t ^ (-((d : ℝ) / 2)) := by positivity
  calc C * t ^ (-((d : ℝ) / 2)) * Real.exp (-(dgShape t r / C))
      ≤ C * t ^ (-((d : ℝ) / 2)) * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := mul_one _

omit [NeZero d] in
/-- The Gaussian branch of `Φ_C`: `Φ_C(t, r) = C t^{-d/2} e^{-r²/(C t)}` for `r ≤ t`. -/
theorem dgPhiDim_of_le {C t r : ℝ} (ht : 0 < t) (hrt : r ≤ t) :
    dgPhiDim d C t r = C * t ^ (-((d : ℝ) / 2)) * Real.exp (-(r ^ 2 / (C * t))) := by
  rw [dgPhiDim_eq_rpow d ht.le, dgExponent, if_pos hrt]

omit [NeZero d] in
/-- The lattice point `midLattice x y` is within `|x - y|/2 + d` of `y`. -/
theorem latticeDist_midLattice_le (x y : Vertex d) :
    ldist (midLattice x y) y ≤ ldist x y / 2 + d := by
  have e : midPoint x y - latticeEuclideanEmbedding y =
      (1 / 2 : ℝ) • (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y) := by
    unfold midPoint
    module
  have h1 : ‖midPoint x y - latticeEuclideanEmbedding y‖ = ldist x y / 2 := by
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    unfold Rigidity.WeakPoincare.latticeDist
    ring
  calc ldist (midLattice x y) y
      = ‖(latticeEuclideanEmbedding (midLattice x y) - midPoint x y) +
          (midPoint x y - latticeEuclideanEmbedding y)‖ := by
        unfold Rigidity.WeakPoincare.latticeDist
        rw [sub_add_sub_cancel]
    _ ≤ ‖latticeEuclideanEmbedding (midLattice x y) - midPoint x y‖ +
          ‖midPoint x y - latticeEuclideanEmbedding y‖ := norm_add_le _ _
    _ ≤ d + ldist x y / 2 := by
        rw [h1, norm_sub_rev]
        linarith [norm_midPoint_sub_le x y]
    _ = _ := add_comm _ _

/-- `r^{-a} ≤ 4^a s^{-a}` for `r ≥ s/4 > 0` and `a ≥ 0`. -/
theorem rpow_neg_le_of_quarter_le {s r a : ℝ} (hs : 0 < s) (hr : s / 4 ≤ r) (ha : 0 ≤ a) :
    r ^ (-a) ≤ 4 ^ a * s ^ (-a) := by
  have h1 : r ^ (-a) ≤ (s / 4) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
  have h2 : (s / 4) ^ (-a) = 4 ^ a * s ^ (-a) := by
    rw [Real.div_rpow hs.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) a,
      div_inv_eq_mul, mul_comm]
  exact h1.trans h2.le

/-- `C (s^η)^{η - 1/2} ≤ θ/2` for large `s`. -/
theorem eventually_mul_rpow_rpow_le {CA θ η : ℝ} (hθ : 0 < θ) (hCA : 0 ≤ CA) (hη0 : 0 < η)
    (hη : η < 1 / 2) : ∀ᶠ s : ℝ in atTop, CA * (s ^ η) ^ (η - 1 / 2) ≤ θ / 2 := by
  have hexp : 0 < η * (1 / 2 - η) := mul_pos hη0 (by linarith)
  have hc : (0 : ℝ) < θ / (2 * (CA + 1)) := by positivity
  have hne : CA + 1 ≠ 0 := by positivity
  have hev := (tendsto_rpow_neg_atTop hexp).eventually (ge_mem_nhds hc)
  filter_upwards [hev, eventually_gt_atTop 0] with s hs hs0
  rw [← Real.rpow_mul hs0.le, show η * (η - 1 / 2) = -(η * (1 / 2 - η)) by ring]
  have h0 : 0 ≤ s ^ (-(η * (1 / 2 - η))) := by positivity
  calc CA * s ^ (-(η * (1 / 2 - η))) ≤ (CA + 1) * s ^ (-(η * (1 / 2 - η))) := by nlinarith
    _ ≤ (CA + 1) * (θ / (2 * (CA + 1))) := mul_le_mul_of_nonneg_left hs (by linarith)
    _ = θ / 2 := by field_simp

/-- `12 (s^γ)² s^η ≤ s` for large `s` when `2γ + η < 1`. -/
theorem eventually_twelve_mul_le {γ η : ℝ} (h : 2 * γ + η < 1) :
    ∀ᶠ s : ℝ in atTop, 12 * (s ^ γ) ^ 2 * s ^ η ≤ s := by
  have ha : 0 < 1 - (2 * γ + η) := by linarith
  filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop 12, eventually_gt_atTop 0]
    with s h1 h0
  have e : (s ^ γ) ^ 2 * s ^ η = s ^ (2 * γ + η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_add h0]
    congr 1
    push_cast
    ring
  have e2 : s ^ (1 - (2 * γ + η)) * s ^ (2 * γ + η) = s := by
    rw [← Real.rpow_add h0]
    norm_num
  calc 12 * (s ^ γ) ^ 2 * s ^ η = 12 * s ^ (2 * γ + η) := by rw [mul_assoc, e]
    _ ≤ s ^ (1 - (2 * γ + η)) * s ^ (2 * γ + η) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = s := e2

/-- **The point source above a deterministic time**, at one configuration: from the order-zero
estimate at the pole `w` above the scale `X`, the on-diagonal bound `p_τ(z, v) ≤ C_b τ^{-d/2}` in
the balls `V_ρ(w)`, `ρ ≥ ρ₀`, for `τ ≥ ρ²`, near `w` for `τ ≥ s/4` and at `w` for `τ ≥ s^η`,
Proposition A.7 at `w` on `[s^η, s]` and the whole-cluster estimate at `w` above `s^η`,
`‖p_s(·, w) - G^w_s‖ ≤ C s^{3η - d/4 - 1/2}`. -/
theorem exists_l2norm_pointSource_le_rpow {σ θ η C₀ Cb CA CG : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (hη0 : 0 < η) (hη : η ≤ 1 / 8) (hC₀ : 0 ≤ C₀) (hCb : 0 ≤ Cb) (hCA : 0 ≤ CA)
    (hCG : 0 ≤ CG) :
    ∃ C t₀ : ℝ, 0 < C ∧ 1 ≤ t₀ ∧ ∀ (ω : Configuration d) (K : OpenComponent ω),
      K.supp.Infinite → ∀ w ∈ K.supp, ∀ X ρ₀ s : ℝ, t₀ ≤ s → 1 ≤ ρ₀ → X ≤ s ^ (η / 2) →
      ρ₀ ≤ s ^ (η / 2) →
      (∀ R', 2 * X ≤ R' → ∀ u : Vertex d → ℝ,
        (∀ x ∈ interiorOf (openGraph ω) (clusterBall K w R'),
          LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
        ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
          nL2 (clusterBall K w r) (fun x => u x - c) ≤
            C₀ * (r / R') * nL2 (clusterBall K w R') u) →
      (∀ ρ, ρ₀ ≤ ρ → ∀ z ∈ clusterBall K w ρ, ∀ v ∈ clusterBall K w ρ, ∀ τ, ρ ^ 2 ≤ τ →
        vsrwHeat (openGraph ω) (2 * d) τ z v ≤ Cb * τ ^ (-((d : ℝ) / 2))) →
      (∀ z ∈ clusterBall K w (Real.sqrt s), ∀ r, s / 4 ≤ r →
        vsrwHeat (openGraph ω) (2 * d) r z z ≤ Cb * r ^ (-((d : ℝ) / 2))) →
      (∀ r, s ^ η ≤ r → vsrwHeat (openGraph ω) (2 * d) r w w ≤ Cb * r ^ (-((d : ℝ) / 2))) →
      (∀ u, s ^ η ≤ u → u ≤ s → |clusterGaussMass K σ u w - θ| ≤ CA * u ^ (η - 1 / 2)) →
      (∀ u, s ^ η ≤ u → 3 * u ≤ s → l2norm (fun x => heatFlowG (openGraph ω) (2 * d) (2 * u)
          (fun z => θ⁻¹ * clusterInd K σ u w z) x - θ⁻¹ * clusterInd K σ (3 * u) w x) ≤
        CG * u ^ (η - (d : ℝ) / 4 - 1 / 2)) →
      l2norm (fun x => vsrwHeat (openGraph ω) (2 * d) s x w - clusterGaussNorm K σ s w x) ≤
        C * s ^ (3 * η - (d : ℝ) / 4 - 1 / 2) := by
  have hd1 := one_le_dim_real (d := d)
  set CB := Cb * 4 ^ ((d : ℝ) / 2) with hCBdef
  have hCB : 0 ≤ CB := by positivity
  have h4 : (1 : ℝ) ≤ 4 ^ ((d : ℝ) / 2) := Real.one_le_rpow (by norm_num) (by positivity)
  have hA0 : 0 ≤ exitConstD d Cb := by unfold exitConstD; positivity
  have hCV : (0 : ℝ) < 16 * (d : ℝ) := by linarith
  obtain ⟨C, hC, hev⟩ := eventually_psBound_le (d := d) (CB := CB) hσ hθ hC₀ hA0 hCA hCG hCV hη0
  set γ := η / ((d : ℝ) + 2) with hγ
  have hγ0 : 0 < γ := div_pos hη0 (by positivity)
  have hγη : γ ≤ η / 3 := by
    rw [hγ]
    exact div_le_div_of_nonneg_left hη0.le (by norm_num) (by linarith)
  have hL : ∀ᶠ s : ℝ in atTop, 2 ≤ s ^ γ := (tendsto_rpow_atTop hγ0).eventually_ge_atTop 2
  have hbig := eventually_twelve_mul_le (γ := γ) (η := η) (by linarith)
  have hsm := eventually_mul_rpow_rpow_le hθ hCA hη0 (by linarith)
  obtain ⟨a, ha⟩ := eventually_atTop.1 (hev.and (hL.and (hbig.and hsm)))
  refine ⟨C, max a 1, hC, le_max_right _ _, ?_⟩
  intro ω K hK w hw X ρ₀ s hs hρ₁ hX hρ hOZ hBar hdiag hdiagw hA7 hGF
  obtain ⟨hps, hL2, hbig', hsm'⟩ := ha s ((le_max_left _ _).trans hs)
  have hs1 : 1 ≤ s := (le_max_right _ _).trans hs
  have hs0 : 0 < s := by linarith
  have hsη : 0 < s ^ η := by positivity
  have hP : s ^ (η / 2) ≤ s ^ (η / 2) * s ^ γ :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hP0 : 0 ≤ s ^ (η / 2) * s ^ γ := by positivity
  have hXl : X ≤ s ^ (η / 2) * s ^ γ := hX.trans hP
  have hρl : ρ₀ ≤ 2 * (s ^ (η / 2) * s ^ γ) := by linarith
  refine le_trans ?_ hps
  refine l2norm_pointSource_le_of_time hw
    (fun ρ => boundaryAccessible_of_infiniteD hK
      (fun v hv => (mem_clusterBall.1 (interiorOf_subset _ hv)).1))
    hC₀ hOZ hA0 (exitHyp_clusterBallD hCb hρ₁ hBar) hσ hθ hη0 hη hCB hCA hCG hCV
    (fun v _ u hu => cvBranches_sixteen ω (by linarith) v) hs1 hL2 hbig' hXl hρl ?_ ?_ hA7 hsm'
    hGF
  · intro z hz r hr _
    refine (hdiag z hz r hr).trans ?_
    rw [hCBdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_neg_le_of_quarter_le hs0 hr (by positivity)) hCb
  · intro u hu _
    have hu0 : 0 < u := lt_of_lt_of_le hsη hu
    refine (hdiagw (u + u) (by linarith)).trans ?_
    have h1 : (u + u) ^ (-((d : ℝ) / 2)) ≤ u ^ (-((d : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by
        have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
        linarith)
    have h2 : 0 ≤ u ^ (-((d : ℝ) / 2)) := by positivity
    rw [hCBdef]
    calc Cb * (u + u) ^ (-((d : ℝ) / 2)) ≤ Cb * u ^ (-((d : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left h1 hCb
      _ ≤ Cb * 4 ^ ((d : ℝ) / 2) * u ^ (-((d : ℝ) / 2)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left h2 h4) hCb

/-- **The error of Theorem 1 of Dario–Gu at a pair of points**, at one configuration, above a
deterministic time: from the point source at both poles at time `t/2`, the on-diagonal bound at
`y`, Proposition A.7 at `x`, `y` (time `t/2`) and `midLattice x y` (time `t/4`), and the Gaussian
upper bound `p_t(x, y) ≤ Φ_{C_b}(t, |x - y|)`, for `|x - y| ≤ t`. -/
theorem exists_abs_vsrwHeat_sub_le_gaussian {σ θ η E Cb CA : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (hη0 : 0 < η) (hη : η ≤ 1 / 12) (hE : 0 ≤ E) (hCb : 0 < Cb) (hCA : 0 ≤ CA) :
    ∃ C t₀ : ℝ, 0 < C ∧ 1 ≤ t₀ ∧ ∀ (ω : Configuration d) (K : OpenComponent ω) (x y : Vertex d)
      (t : ℝ), t₀ ≤ t → ldist x y ≤ t →
      l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) (t / 2) z x -
          clusterGaussNorm K σ (t / 2) x z) ≤ E * (t / 2) ^ (3 * η - (d : ℝ) / 4 - 1 / 2) →
      l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) (t / 2) z y -
          clusterGaussNorm K σ (t / 2) y z) ≤ E * (t / 2) ^ (3 * η - (d : ℝ) / 4 - 1 / 2) →
      vsrwHeat (openGraph ω) (2 * d) (t / 2 + t / 2) y y ≤
        Cb * (t / 2) ^ (-((d : ℝ) / 2)) →
      |clusterGaussMass K σ (t / 2) x - θ| ≤ CA * (t / 2) ^ (η - 1 / 2) →
      |clusterGaussMass K σ (t / 2) y - θ| ≤ CA * (t / 2) ^ (η - 1 / 2) →
      |clusterGaussMass K σ (t / 2 / 2) (midLattice x y) - θ| ≤
        CA * (t / 2 / 2) ^ (η - 1 / 2) →
      vsrwHeat (openGraph ω) (2 * d) t x y ≤ dgPhiDim d Cb t (ldist x y) →
      |vsrwHeat (openGraph ω) (2 * d) t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)| ≤
        C * t ^ (-((d : ℝ) / 2) - (1 / 2 - 6 * η)) *
          Real.exp (-(‖edzD x y‖ ^ 2 / (C * t))) := by
  have hsm2 : ∀ᶠ s : ℝ in atTop, CA * s ^ (η - 1 / 2) ≤ θ / 2 := by
    have hexp : 0 < 1 / 2 - η := by linarith
    have hc : (0 : ℝ) < θ / (2 * (CA + 1)) := by positivity
    have hne : CA + 1 ≠ 0 := by positivity
    have hev := (tendsto_rpow_neg_atTop hexp).eventually (ge_mem_nhds hc)
    filter_upwards [hev, eventually_gt_atTop 0] with s hs hs0
    rw [show η - 1 / 2 = -(1 / 2 - η) by ring]
    have h0 : 0 ≤ s ^ (-(1 / 2 - η)) := by positivity
    calc CA * s ^ (-(1 / 2 - η)) ≤ (CA + 1) * s ^ (-(1 / 2 - η)) := by nlinarith
      _ ≤ (CA + 1) * (θ / (2 * (CA + 1))) := mul_le_mul_of_nonneg_left hs (by linarith)
      _ = θ / 2 := by field_simp
  obtain ⟨a, ha⟩ := eventually_atTop.1 hsm2
  set C₁ := pwConst d σ θ E Cb CA with hC₁
  set C := gaussFactorConst d σ θ C₁ Cb Cb (6 * η) with hCdef
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁, pwConst]
    have := shiftConstD_nonneg (d := d) hσ d (Nat.cast_nonneg d)
    have := psGauss_nonneg d σ θ
    positivity
  have hC0 : 0 < C := by
    rw [hCdef, gaussFactorConst]
    exact lt_max_of_lt_right (div_pos (lt_max_of_lt_left hCb) (by positivity))
  refine ⟨C, max (2 * a) 4, hC0, by
    have := le_max_right (2 * a) 4
    linarith, ?_⟩
  intro ω K x y t ht hD hEx hEy hdiag hAx hAy hA' hBar
  have ht4 : 4 ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hs2 : 2 ≤ t / 2 := by linarith
  have hsm' : CA * (t / 2) ^ (η - 1 / 2) ≤ θ / 2 :=
    ha (t / 2) (by have := (le_max_left (2 * a) 4).trans ht; linarith)
  have h1 := abs_vsrwHeat_sub_le_rpow (K := K) hσ hθ hs2 hη0 (by linarith : η ≤ 3 * η)
    hCb.le hCA hEx hEy hdiag hAx hAy hA' hsm'
  rw [show 2 * (t / 2) = t by ring] at h1
  have hDn : ldist x y = ‖edzD x y‖ := latticeDist_eq_norm_edzD x y
  have hBar' : vsrwHeat (openGraph ω) (2 * d) t x y ≤
      Cb * t ^ (-((d : ℝ) / 2)) * Real.exp (-(‖edzD x y‖ ^ 2 / (Cb * t))) := by
    rw [← hDn, ← dgPhiDim_of_le (d := d) (C := Cb) ht0 hD]
    exact hBar
  have ha0 : 0 ≤ vsrwHeat (openGraph ω) (2 * d) t x y := bondHeat_nonneg ω ht0.le x y
  have hb0 : 0 ≤ gaussianHeatD d σ t (edzD x y) := gaussianHeatD_nonneg hσ ht0.le _
  exact abs_vsrwHeat_sub_le_gaussian (a := vsrwHeat (openGraph ω) (2 * d) t x y)
    (b := gaussianHeatD d σ t (edzD x y)) (D := ‖edzD x y‖) hσ hθ hC₁0 hCb.le hCb
    (by linarith : 0 < 6 * η) (by linarith) (by linarith) (by linarith) (by linarith) ha0
    le_rfl hb0 h1 hBar'

end Rigidity.Green

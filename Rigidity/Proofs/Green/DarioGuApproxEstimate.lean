import Rigidity.Proofs.Green.DarioGuApproxCore

/-!
# The deterministic estimate of Lemma 4.1 of Dario–Gu

`approx_estimate`: for `x, y` in a component `K`, `1 ≤ τ`, `3τ ≤ t` and `s = t - τ`, if

* `|θ^{-1} p̄(τ, z - y) - p(τ, z, y)| ≤ ε Φ_{C₀}(τ, z - y)` on `K` (Theorem 4 at time `τ` in the
  printed Lemma 4.1, the homogenization estimate (4.50) in the iteration of §4.3),
* `|Σ_{z ∈ K} p̄(τ, z - y) - θ| ≤ C_A τ^{-1/2 + α}` (Proposition A.7),
* the weak Poincaré inequality on the balls `K ∩ B_R(y)`, `R ≥ √τ`, with the gradient on
  `K ∩ B_{C_P R}(y)` (Proposition 2.7),
* the gradient bound on `p(s, x, ·)` on these balls (Theorem 3, Remark 1.3),
* `|K ∩ B_{√τ}(y)| ≥ c τ`,
* Theorem 4 at time `s` at the points `z` with `|z - y| ≤ s + 1`, and Proposition 2.15 at time `s`,

then `|q(t, x, τ, y) - p(t, x, y)| ≤ C (ε (τ/t)^{1/2} + τ^{-1/2 + α}) Φ_C(t, x - y)`.

The proof follows lines 1993-2148 of the source: Duhamel's formula (4.6), the subtraction of the
average `c₀` of `p(s, x, ·)` on `K ∩ B_{√τ}(y)` at the cost `|c₀| |Σ_K w|` ((4.7)), and the dyadic
annuli (4.8)-(4.17) (`sum_abs_mul_abs_sub_finAvg_le`, `approx_term_le`).
-/

open Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

theorem rpow_half_div_eq {τ t : ℝ} (hτ : 0 ≤ τ) : (τ / t) ^ (1 / 2 : ℝ) =
    Real.sqrt τ / Real.sqrt t := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div hτ]

/-- **The deterministic estimate of Lemma 4.1.** -/
theorem approx_estimate {σ θ C₀ CB Ccv CP CG cd CA α : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (hC₀ : 0 < C₀) (hCB : 0 < CB) (hCcv : 0 < Ccv) (hCP : 1 ≤ CP) (hCG : 0 < CG) (hcd : 0 < cd) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration 2) (K' : OpenComponent ω) (x y : Vertex 2)
      (t τ ε : ℝ), 1 ≤ τ → 3 * τ ≤ t → 0 ≤ ε → x ∈ K'.supp → y ∈ K'.supp →
      (∀ z ∈ K'.supp, |θ⁻¹ * latticeGaussian σ τ z y - openHeat ω τ z y| ≤
        ε * dgPhi C₀ τ (latticeDist z y)) →
      |∑' z : K'.supp, latticeGaussian σ τ z.val y - θ| ≤ CA * τ ^ (-(1 / 2 : ℝ) + α) →
      (∀ R : ℝ, Real.sqrt τ ≤ R → ∀ u : Vertex 2 → ℝ,
        Real.sqrt ((∑ z ∈ clusterBall K' y R, (u z - finAvg (clusterBall K' y R) u) ^ 2) /
            (clusterBall K' y R).card) ≤
          CP * R * Real.sqrt (gradEnergy ω (clusterBall K' y (CP * R)) u /
            (clusterBall K' y (CP * R)).card)) →
      (∀ R : ℝ, Real.sqrt τ ≤ R → 4 * R ^ 2 ≤ t - τ → latticeDist x y ≤ t - τ →
        Real.sqrt (gradEnergy ω (clusterBall K' y R) (fun z => openHeat ω (t - τ) x z) /
            (clusterBall K' y R).card) ≤
          CG * (t - τ) ^ (-(3 / 2 : ℝ)) * Real.exp (-(latticeDist x y ^ 2 / (CG * (t - τ))))) →
      cd * τ ≤ (clusterBall K' y (Real.sqrt τ)).card →
      (∀ z ∈ K'.supp, latticeDist z y ≤ (t - τ) + 1 →
        openHeat ω (t - τ) x z ≤ dgPhi CB (t - τ) (latticeDist x z)) →
      (∀ z ∈ K'.supp, (latticeDist x z ≤ t - τ → openHeat ω (t - τ) x z ≤
          Ccv * Real.exp (-(latticeDist x z ^ 2 / (Ccv * (t - τ))))) ∧
        (t - τ ≤ latticeDist x z → openHeat ω (t - τ) x z ≤
          Ccv * Real.exp (-(latticeDist x z / Ccv * (1 + Real.log (latticeDist x z / (t - τ))))))) →
      |dgQ ω σ θ t τ x y - openHeat ω t x y| ≤
        C * (ε * (τ / t) ^ (1 / 2 : ℝ) + τ ^ (-(1 / 2 : ℝ) + α)) * dgPhi C t (latticeDist x y) := by
  obtain ⟨Kc, C₈, hKc, hC₈, hconvs⟩ :=
    sum_openHeat_mul_dgPhi_le hCB hCcv (by positivity : (0 : ℝ) < 16 * C₀)
  obtain ⟨Kt, Cs, hKt, hCs, hterm⟩ := approx_term_le hC₀ hCP hCG hcd hKc hC₈
  set KB := Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) / 16 with hKB
  set e₀ := Real.exp (-((2 : ℝ) ^ 0 / (4 * C₀))) with he₀
  set K₀ := KB * e₀ * Kc / (C₀ * cd) with hK₀
  set Kann := Kt * (10080 * (4 * C₀) ^ 7) with hKann
  set Cf := max Cs C₈ with hCf
  have hCf0 : 0 < Cf := lt_max_of_lt_left hCs
  set C := max (max Kann (K₀ * (θ⁻¹ * CA))) Cf with hCdef
  have hC0 : 0 < C := lt_max_of_lt_right hCf0
  refine ⟨C, hC0, ?_⟩
  intro ω K' x y t τ ε hτ1 h3 hε hx hy hw hmassA hP hG hvol hB hcv
  have hτ0 : 0 < τ := by linarith
  set s := t - τ with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have ht0 : 0 < t := by linarith
  have hτs : 2 * τ ≤ s := by rw [hsdef]; linarith
  have hst : s ≤ t := by rw [hsdef]; linarith
  have h23 : 2 * t ≤ 3 * s := by rw [hsdef]; linarith
  have hsτ : 1 ≤ Real.sqrt τ := by rw [Real.one_le_sqrt]; exact hτ1
  have hstt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  set d := latticeDist x y with hd
  have hd0 : 0 ≤ d := latticeDist_nonneg x y
  -- the computation (4.15)
  have hconv : ∀ S : Finset (Vertex 2), ∑ z ∈ S, openHeat ω s x z * dgPhi (16 * C₀) τ
      (latticeDist z y) ≤ Kc * dgPhi C₈ t d := by
    intro S
    have h := hconvs ω K' x y s τ hτ1 (by linarith) hx hB hcv S
    rwa [show τ + s = t by rw [hsdef]; ring] at h
  have hvol0 : cd * τ ≤ (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card := by
    rw [pow_zero, one_mul]; exact hvol
  have hU0pos : (0 : ℝ) < (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card :=
    lt_of_lt_of_le (by positivity) hvol0
  have hU0ne : (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hU0pos
  -- the functions
  set g : Vertex 2 → ℝ := fun z => openHeat ω s x z with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => openHeat_nonneg' ω hs0.le x z
  have hg1 : ∀ z, g z ≤ 1 := fun z => openHeat_le_one ω hs0.le x z
  set w : Vertex 2 → ℝ := fun z => θ⁻¹ * latticeGaussian σ τ z y - openHeat ω τ z y with hwdef
  set wK : Vertex 2 → ℝ := K'.supp.indicator w with hwK
  set c₀ := finAvg (clusterBall K' y (2 ^ 0 * Real.sqrt τ)) g with hc₀
  have hlG : Summable fun z => latticeGaussian σ τ z y := summable_latticeGaussian hσ hτ1 y
  have hpτ : HasSum (fun z => openHeat ω τ z y) 1 := by
    have h := hasSum_openHeat ω hτ0.le y
    simpa only [openHeat_symm ω τ y] using h
  have hw_s : Summable w := (hlG.mul_left θ⁻¹).sub hpτ.summable
  have hwK_s : Summable wK := hw_s.indicator _
  -- Duhamel's formula (4.6)
  have hduh : dgQ ω σ θ t τ x y - openHeat ω t x y = ∑' z, g z * wK z := by
    have hq : dgQ ω σ θ t τ x y = ∑' z, g z * (θ⁻¹ * latticeGaussian σ τ z y) := rfl
    have hp : openHeat ω t x y = ∑' z, g z * openHeat ω τ z y := by
      have h := hasSum_openHeat_mul ω hs0.le hτ0.le x y
      rw [show s + τ = t by rw [hsdef]; ring] at h
      exact h.tsum_eq.symm
    have hs1 : Summable fun z => g z * (θ⁻¹ * latticeGaussian σ τ z y) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hg0 z)
          (mul_nonneg (inv_nonneg.2 hθ.le) (latticeGaussian_pos hσ hτ0 z y).le))
        (fun z => mul_le_of_le_one_left (mul_nonneg (inv_nonneg.2 hθ.le)
          (latticeGaussian_pos hσ hτ0 z y).le) (hg1 z)) (hlG.mul_left θ⁻¹)
    have hs2 : Summable fun z => g z * openHeat ω τ z y :=
      (hasSum_openHeat_mul ω hs0.le hτ0.le x y).summable
    rw [hq, hp, ← hs1.tsum_sub hs2]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ K'.supp
    · simp only [hwK, Set.indicator_of_mem hz, hwdef]
      ring
    · have h0 : g z = 0 := openHeat_eq_zero_of_mem_of_notMem hx hz s
      rw [h0]
      ring
  -- the mass of `w` (Proposition A.7)
  have hmassw : |∑' z, wK z| ≤ θ⁻¹ * (CA * τ ^ (-(1 / 2 : ℝ) + α)) := by
    have hsplit : ∑' z, wK z = θ⁻¹ * ∑' z : K'.supp, latticeGaussian σ τ z.val y - 1 := by
      have e1 : wK = fun z => K'.supp.indicator (fun z => θ⁻¹ * latticeGaussian σ τ z y) z -
          openHeat ω τ z y := by
        funext z
        by_cases hz : z ∈ K'.supp
        · simp only [hwK, Set.indicator_of_mem hz, hwdef]
        · have h0 : openHeat ω τ z y = 0 := by
            rw [openHeat_symm]; exact openHeat_eq_zero_of_mem_of_notMem hy hz τ
          simp only [hwK, Set.indicator_of_notMem hz, h0, sub_zero]
      rw [e1, ((hlG.mul_left θ⁻¹).indicator _).tsum_sub hpτ.summable, hpτ.tsum_eq,
        ← tsum_subtype K'.supp (fun z => θ⁻¹ * latticeGaussian σ τ z y), tsum_mul_left]
    rw [hsplit]
    have e : θ⁻¹ * ∑' z : K'.supp, latticeGaussian σ τ z.val y - 1 =
        θ⁻¹ * (∑' z : K'.supp, latticeGaussian σ τ z.val y - θ) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hθ)]
    exact mul_le_mul_of_nonneg_left hmassA (inv_pos.2 hθ).le
  -- the average `c₀`
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hc₀0 : 0 ≤ c₀ := div_nonneg (Finset.sum_nonneg fun z _ => hg0 z) (Nat.cast_nonneg _)
  have hc₀ : c₀ ≤ K₀ * dgPhi C₈ t d := by
    have hpt : ∀ z ∈ clusterBall K' y (2 ^ 0 * Real.sqrt τ),
        g z ≤ τ / C₀ * (KB * e₀) * (g z * dgPhi (16 * C₀) τ (latticeDist z y)) := by
      intro z hz
      have h := dgPhi_annulusInner_le_mul_dgPhi hC₀ hτ1 0 (latticeDist_nonneg z y)
        (mem_clusterBall.1 hz).2
      have h0 : annulusInner τ 0 = 0 := by simp [annulusInner]
      rw [h0, dgPhi_zero_eq hτ0, ← hKB, ← he₀] at h
      have h1 : 1 ≤ τ / C₀ * (KB * e₀ * dgPhi (16 * C₀) τ (latticeDist z y)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hC₀]
        have e : C₀ * τ⁻¹ * τ = C₀ := by field_simp
        have h2 := mul_le_mul_of_nonneg_right h hτ0.le
        rw [e] at h2
        linarith
      calc g z = g z * 1 := (mul_one _).symm
        _ ≤ g z * (τ / C₀ * (KB * e₀ * dgPhi (16 * C₀) τ (latticeDist z y))) :=
            mul_le_mul_of_nonneg_left h1 (hg0 z)
        _ = _ := by ring
    have hsum : ∑ z ∈ clusterBall K' y (2 ^ 0 * Real.sqrt τ), g z ≤
        τ / C₀ * (KB * e₀) * (Kc * dgPhi C₈ t d) := by
      calc ∑ z ∈ clusterBall K' y (2 ^ 0 * Real.sqrt τ), g z
          ≤ ∑ z ∈ clusterBall K' y (2 ^ 0 * Real.sqrt τ),
              τ / C₀ * (KB * e₀) * (g z * dgPhi (16 * C₀) τ (latticeDist z y)) :=
            Finset.sum_le_sum hpt
        _ = τ / C₀ * (KB * e₀) * ∑ z ∈ clusterBall K' y (2 ^ 0 * Real.sqrt τ),
              g z * dgPhi (16 * C₀) τ (latticeDist z y) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hconv _) (by positivity)
    rw [hc₀, finAvg, div_le_iff₀ hU0pos]
    refine hsum.trans ?_
    have hΦ := dgPhi_nonneg hC₈.le ht0.le d
    calc τ / C₀ * (KB * e₀) * (Kc * dgPhi C₈ t d) = K₀ * dgPhi C₈ t d * (cd * τ) := by
          rw [hK₀]; field_simp
      _ ≤ K₀ * dgPhi C₈ t d * (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card :=
          mul_le_mul_of_nonneg_left hvol0 (by rw [hK₀]; positivity)
  -- the annuli
  have hann : |∑' z, wK z * (g z - c₀)| ≤
      ε * Kann * (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t d := by
    set B := ε * Kann * (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t d with hBdef
    have hfin : ∀ S : Finset (Vertex 2), ∑ z ∈ S, |wK z * (g z - c₀)| ≤ B := by
      intro S
      classical
      have e : ∑ z ∈ S, |wK z * (g z - c₀)| =
          ∑ z ∈ S.filter (fun z => z ∈ K'.supp), |wK z| * |g z - c₀| := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun z _ => ?_
        split_ifs with hz
        · rw [abs_mul]
        · simp [hwK, Set.indicator_of_notMem hz]
      rw [e]
      refine sum_abs_mul_abs_sub_finAvg_le (U := fun n => clusterBall K' y (2 ^ n * Real.sqrt τ))
        (fun n m hnm => clusterBall_mono (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hnm) (Real.sqrt_nonneg _))) hU0ne wK g
        (fun n => ε * dgPhi C₀ τ (annulusInner τ n))
        (fun n => mul_nonneg hε (dgPhi_nonneg hC₀.le hτ0.le _)) ?_ ?_ _ ?_
      · intro n z hz hmin
        have hz' := mem_clusterBall.1 hz
        simp only [hwK, Set.indicator_of_mem hz'.1]
        refine (hw z hz'.1).trans (mul_le_mul_of_nonneg_left (dgPhi_anti hC₀ hτ0
          (annulusInner_nonneg τ n) ?_) hε)
        rcases n with _ | m
        · simp [annulusInner, latticeDist_nonneg]
        · have hnot := hmin m (Nat.lt_succ_self m)
          rw [mem_clusterBall] at hnot
          simp only [annulusInner, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
          by_contra hlt
          exact hnot ⟨hz'.1, not_le.1 hlt⟩
      · intro N
        calc ∑ n ∈ range N, ε * dgPhi C₀ τ (annulusInner τ n) *
              ((∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ),
                |g z - finAvg (clusterBall K' y (2 ^ n * Real.sqrt τ)) g|) *
              (1 + ((clusterBall K' y (2 ^ n * Real.sqrt τ)).card : ℝ) /
                (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card))
            ≤ ∑ n ∈ range N, ε * (Kt * ((64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀)))) *
                (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t d) := by
              refine Finset.sum_le_sum fun n _ => ?_
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (hterm ω K' x y s t τ hτ1 hτs hst h23 hP hG hvol0
                hconv n) hε
          _ = ε * Kt * (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t d *
                ∑ n ∈ range N, (64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun n _ => by ring
          _ ≤ ε * Kt * (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t d * (10080 * (4 * C₀) ^ 7) := by
              apply mul_le_mul_of_nonneg_left (sum_pow_mul_exp_neg_le hC₀ N)
              have := dgPhi_nonneg hCs.le ht0.le d
              positivity
          _ = B := by rw [hBdef, hKann]; ring
      · intro z hz
        have hzK := (Finset.mem_filter.1 hz).2
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (latticeDist z y) (by norm_num : (1 : ℝ) < 2)
        refine ⟨n, mem_clusterBall.2 ⟨hzK, ?_⟩⟩
        calc latticeDist z y < 2 ^ n := hn
          _ ≤ 2 ^ n * Real.sqrt τ := le_mul_of_one_le_right (by positivity) hsτ
    have hsumm : Summable fun z => |wK z * (g z - c₀)| :=
      summable_of_sum_le (fun z => abs_nonneg _) hfin
    exact (abs_tsum_le_tsum_abs hsumm).trans (hsumm.tsum_le_of_sum_le hfin)
  -- assembly
  have hsplitc : ∑' z, g z * wK z = ∑' z, wK z * (g z - c₀) + c₀ * ∑' z, wK z := by
    have hs1 : Summable fun z => wK z * (g z - c₀) := by
      refine (Summable.of_nonneg_of_le (fun z => abs_nonneg _) (fun z => ?_)
        (hwK_s.abs.mul_right (1 + c₀))).of_abs
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_le]
      constructor <;> linarith [hg0 z, hg1 z]
    rw [← tsum_mul_left, ← hs1.tsum_add (hwK_s.mul_left c₀)]
    exact tsum_congr fun z => by ring
  rw [hduh, hsplitc, rpow_half_div_eq hτ0.le]
  have hΦCs : dgPhi Cs t d ≤ dgPhi C t d :=
    dgPhi_mono hCs ((le_max_left _ _).trans (le_max_right _ _)) ht0 hd0
  have hΦC8 : dgPhi C₈ t d ≤ dgPhi C t d :=
    dgPhi_mono hC₈ ((le_max_right _ _).trans (le_max_right _ _)) ht0 hd0
  have hΦC0 := dgPhi_nonneg hC0.le ht0.le d
  have hpow0 : 0 ≤ τ ^ (-(1 / 2 : ℝ) + α) := Real.rpow_nonneg hτ0.le _
  have hfac0 : 0 ≤ Real.sqrt τ / Real.sqrt t := by positivity
  have hKannC : Kann ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hK₀C : K₀ * (θ⁻¹ * CA) ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  calc |∑' z, wK z * (g z - c₀) + c₀ * ∑' z, wK z|
      ≤ |∑' z, wK z * (g z - c₀)| + c₀ * |∑' z, wK z| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_of_nonneg hc₀0]
    _ ≤ ε * Kann * (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t d +
          K₀ * dgPhi C₈ t d * (θ⁻¹ * (CA * τ ^ (-(1 / 2 : ℝ) + α))) :=
        add_le_add hann (mul_le_mul hc₀ hmassw (abs_nonneg _)
          (mul_nonneg hK₀0 (dgPhi_nonneg hC₈.le ht0.le d)))
    _ ≤ ε * C * (Real.sqrt τ / Real.sqrt t) * dgPhi C t d +
          C * dgPhi C t d * τ ^ (-(1 / 2 : ℝ) + α) := by
        apply add_le_add
        · have hK0 : 0 ≤ Kann := by rw [hKann]; positivity
          have := dgPhi_nonneg hCs.le ht0.le d
          calc ε * Kann * (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t d
              ≤ ε * C * (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t d := by gcongr
            _ ≤ ε * C * (Real.sqrt τ / Real.sqrt t) * dgPhi C t d := by gcongr
        · have := dgPhi_nonneg hC₈.le ht0.le d
          calc K₀ * dgPhi C₈ t d * (θ⁻¹ * (CA * τ ^ (-(1 / 2 : ℝ) + α)))
              = K₀ * (θ⁻¹ * CA) * dgPhi C₈ t d * τ ^ (-(1 / 2 : ℝ) + α) := by ring
            _ ≤ C * dgPhi C₈ t d * τ ^ (-(1 / 2 : ℝ) + α) := by gcongr
            _ ≤ C * dgPhi C t d * τ ^ (-(1 / 2 : ℝ) + α) := by gcongr
    _ = C * (ε * (Real.sqrt τ / Real.sqrt t) + τ ^ (-(1 / 2 : ℝ) + α)) * dgPhi C t d := by ring

end Rigidity.Green

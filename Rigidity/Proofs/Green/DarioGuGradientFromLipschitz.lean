import Rigidity.Proofs.Green.DarioGuParabolicInputs
import Rigidity.Proofs.Green.DarioGuLevels
import Mathlib.Analysis.Calculus.Deriv.Shift
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHProb

/-!
# Theorem 3 of Dario–Gu from Proposition 3.9 and Barlow's bound, in dimension two

Dario–Gu prove Theorem 3 (lines 1865-1911 of the source) by applying Proposition 3.9 to the heat
kernel `u(τ, z) = p(t + 1 + τ, z, y)` on the cylinder of radius `R = √t / 2` and bounding the right
side by Barlow's Gaussian bound at the poles near the centre, after the minimal time `T'_NA` of
(3.52). This file carries out this argument for the form of Remark 1.3 (gradient in the second
variable, by the symmetry of the heat kernel), with Proposition 3.9 for `2r ≤ R`
(`DarioGuLipschitzTwo`): the cylinder has top time `T = t + r²/2` and radius
`R = (7t/8 + r²/2)^{1/2}`, so that `2r ≤ R` for `t ≥ 4r²`, the times of the cylinder lie in
`[t/8, 9t/8]` and `t` is the time `-r²/2 ∈ I_r` of the cylinder.

* `anchorDist w ω`: the distance from `w` to the anchor of its partition cube, with a stretched
  exponential tail from the tail of the scales of the partition cubes;
* `avgL2_subMean_le`: `‖f - (f)_U‖_{L̲²(U)} ≤ 2 sup_U |f|`;
* `dgPhi_shift_le`: `Φ_C(s, ρ) ≤ A t^{-1} exp(-d²/(10 C t))` for `s ∈ [t/8, 2t]`, `ρ ≥ d - 3√t`;
* `darioGuGradientBoundTwo_of_lipschitz`: Theorem 3 (Remark 1.3) from Proposition 3.9 and Theorem 4.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open scoped ENNReal

namespace Rigidity.Green

variable {p : unitInterval}

/-! ### Rounding and coarse vertices -/

theorem norm_latticeRound_sub_le (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖latticeEuclideanEmbedding (latticeRound ξ) - ξ‖ ≤ 1 := by
  have hc : ∀ i, |((latticeRound ξ i : ℤ) : ℝ) - ξ i| ≤ 1 / 2 := by
    intro i
    have h1 := Int.floor_le (ξ i + 1 / 2)
    have h2 := Int.lt_floor_add_one (ξ i + 1 / 2)
    simp only [latticeRound]
    rw [abs_le]
    constructor <;> linarith
  have e : ∀ i, ‖(latticeEuclideanEmbedding (latticeRound ξ) - ξ) i‖ ^ 2 =
      (((latticeRound ξ i : ℤ) : ℝ) - ξ i) ^ 2 := by
    intro i
    rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    rfl
  have hS : ∑ i, ‖(latticeEuclideanEmbedding (latticeRound ξ) - ξ) i‖ ^ 2 ≤ 1 := by
    rw [Fin.sum_univ_two, e 0, e 1]
    have h0 := hc 0
    have h1 := hc 1
    rw [abs_le] at h0 h1
    nlinarith
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖(latticeEuclideanEmbedding (latticeRound ξ) - ξ) i‖ ^ 2)
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hS
    _ = 1 := Real.sqrt_one

/-- The distance from `w` to the anchor of its partition cube (to `w` itself off the partition
event). -/
noncomputable def anchorDist (w : Vertex 2) (ω : Configuration 2) : ℝ :=
  latticeDist (Rigidity.Corrector.guardAnchor ω w) w

theorem latticeDist_self (x : Vertex 2) : latticeDist x x = 0 := by
  simp [latticeDist]

theorem coarseVertex_mem {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (x : Vertex 2) :
    coarseVertex ω (uniqueInfiniteComponent h) x ∈ (uniqueInfiniteComponent h).supp := by
  unfold coarseVertex
  split_ifs with hx
  · exact hx
  · exact (mem_uniqueInfiniteComponent_iff h _).2
      (Rigidity.Corrector.infinite_planarCoarseAnchor hP x)

theorem latticeDist_coarseVertex_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (K : OpenComponent ω) (x : Vertex 2) :
    latticeDist (coarseVertex ω K x) x ≤ anchorDist x ω := by
  unfold coarseVertex anchorDist
  split_ifs with hx
  · rw [latticeDist_self]
    exact latticeDist_nonneg _ _
  · rw [Rigidity.Corrector.guardAnchor_of_event hP]

/-- Two vertices of a triadic cube of scale `n` are at distance at most `2 · 3^n`. -/
theorem latticeDist_le_of_mem_vertices {Q : TriadicCube 2} {x z : Vertex 2}
    (hx : x ∈ Q.vertices) (hz : z ∈ Q.vertices) : latticeDist x z ≤ 2 * (3 : ℝ) ^ Q.scale := by
  have hside : ((Q.side : ℤ) : ℝ) = (3 : ℝ) ^ Q.scale := by
    simp [TriadicCube.side]
  have hi : ∀ i, |((x i : ℤ) : ℝ) - z i| ≤ (3 : ℝ) ^ Q.scale := by
    intro i
    have h1 := hx i
    have h2 := hz i
    have h3 : |x i - z i| < Q.side := by
      rw [abs_lt] at h1 h2 ⊢
      constructor <;> linarith
    have h4 : |((x i - z i : ℤ) : ℝ)| < ((Q.side : ℤ) : ℝ) := by exact_mod_cast h3
    rw [hside] at h4
    push_cast at h4
    exact h4.le
  have hsq := latticeDist_sq x z
  have h0 := latticeDist_nonneg x z
  have hS : (0 : ℝ) ≤ (3 : ℝ) ^ Q.scale := by positivity
  have ha := hi 0
  have hb := hi 1
  rw [abs_le] at ha hb
  have hd2 : latticeDist x z ^ 2 ≤ (2 * (3 : ℝ) ^ Q.scale) ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith

theorem anchorDist_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (w : Vertex 2) :
    anchorDist w ω ≤ 2 * (3 : ℝ) ^ (planarPartCube ω w).scale := by
  unfold anchorDist
  rw [Rigidity.Corrector.guardAnchor_of_event hP]
  exact latticeDist_le_of_mem_vertices (Rigidity.Corrector.planarCoarseAnchor_mem hP w)
    (planarPartCube_spec hP w).1

theorem measurable_anchorDist (w : Vertex 2) : Measurable (anchorDist w) :=
  (measurable_of_countable fun v : Vertex 2 => latticeDist v w).comp
    (Rigidity.Corrector.measurable_guardAnchor w)

/-- **The anchor distances form a good family**: they are measurable, nonnegative and have a
uniform exponential tail. -/
theorem goodTimes_anchorDist (hpc : criticalProbability 2 < (p : ℝ)) :
    GoodTimes p anchorDist := by
  obtain ⟨a, ha, hscale⟩ := Rigidity.Proofs.Cluster.exists_measure_planarPartCube_scale_ge_le (p := p) hpc
  have hPae : latticeBondLaw 2 p {ω | ¬ PlanarPartitionEvent ω} = 0 :=
    ae_iff.1 (ae_planarPartitionEvent hpc)
  set C : ℝ := max 4 (6 / a) with hCdef
  have hC4 : 4 ≤ C := le_max_left _ _
  have hCa : 6 / a ≤ C := le_max_right _ _
  refine ⟨measurable_anchorDist, fun w ω => latticeDist_nonneg _ _, C, 1, by linarith,
    one_pos, fun w => ?_⟩
  intro u hu
  rw [Real.rpow_eq_pow, Real.rpow_one]
  rcases lt_or_ge u 2 with hu2 | hu2
  · -- small `u`: the bound is at least one
    refine prob_le_one.trans (ENNReal.one_le_ofReal.2 ?_)
    have h1 := one_le_mul_exp_neg (C := C / 2) (v := u / 2) (by linarith) (by linarith)
    have e : -(u / 2) / (C / 2) = -u / C := by field_simp
    rw [e] at h1
    have h2 : 0 ≤ Real.exp (-u / C) := (Real.exp_pos _).le
    nlinarith
  · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ u / 2 by linarith)
      (show (1 : ℝ) < 3 by norm_num)
    have hsub : {ω | u ≤ anchorDist w ω} ⊆ {ω | ¬ PlanarPartitionEvent ω} ∪
        {ω | PlanarPartitionEvent ω ∧ n ≤ (planarPartCube ω w).scale + 2} := by
      intro ω hω
      by_cases hP : PlanarPartitionEvent ω
      · right
        refine ⟨hP, ?_⟩
        have h1 : u ≤ 2 * (3 : ℝ) ^ (planarPartCube ω w).scale := hω.trans (anchorDist_le hP w)
        have h2 : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (planarPartCube ω w).scale := by linarith
        have h3 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h2
        omega
      · exact Or.inl hP
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hPae, zero_add]
    refine (hscale n w).trans (ENNReal.ofReal_le_ofReal ?_)
    have h3n : u / 6 ≤ (3 : ℝ) ^ n := by
      rw [pow_succ] at hn2
      linarith
    have hexp : Real.exp (-a * (3 : ℝ) ^ n) ≤ Real.exp (-u / C) := by
      apply Real.exp_le_exp.2
      have hC0 : 0 < C := by linarith
      have hau : u / C ≤ a * (u / 6) := by
        rw [div_le_iff₀ hC0]
        have : 6 ≤ C * a := by
          have := (div_le_iff₀ ha).1 hCa
          linarith
        nlinarith
      have : a * (u / 6) ≤ a * (3 : ℝ) ^ n := mul_le_mul_of_nonneg_left h3n ha.le
      rw [neg_div, neg_mul]
      linarith
    have h2C : 2 ≤ C := by linarith
    nlinarith [Real.exp_pos (-u / C)]

/-! ### Averages on a cylinder -/

theorem volume_parabolicCylinderAt_lt_top (y : Vertex 2) (r : ℝ) :
    volume (parabolicCylinderAt y r) < ∞ := by
  unfold parabolicCylinderAt
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    measure_ball_lt_top

theorem abs_setAverage_le {U : Set (ℝ × EuclideanSpace ℝ (Fin 2))} (hU : volume U < ∞)
    {g : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ z ∈ U, |g z| ≤ K) : |⨍ z in U, g z| ≤ K := by
  rw [setAverage_eq, smul_eq_mul, abs_mul]
  have h1 : ‖∫ z in U, g z‖ ≤ K * volume.real U :=
    norm_setIntegral_le_of_norm_le_const hU fun z hz => by
      rw [Real.norm_eq_abs]
      exact hg z hz
  rw [Real.norm_eq_abs] at h1
  rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ volume.real U) with h0 | hpos
  · rw [← h0]
    simpa using hK
  · rw [abs_inv, abs_of_pos hpos]
    calc (volume.real U)⁻¹ * |∫ z in U, g z| ≤ (volume.real U)⁻¹ * (K * volume.real U) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
      _ = K := by field_simp

/-- `‖f - (f)_U‖_{L̲²(U)} ≤ 2 B` when `|f| ≤ B` on `U`. -/
theorem avgL2_subMean_le {U : Set (ℝ × EuclideanSpace ℝ (Fin 2))} (hU : volume U < ∞)
    {f : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ z ∈ U, |f z| ≤ B) :
    avgL2 (subMean f U) U ≤ 2 * B := by
  have hc : |⨍ z in U, f z| ≤ B := abs_setAverage_le hU hB hf
  have hg : ∀ z ∈ U, |subMean f U z ^ 2| ≤ (2 * B) ^ 2 := by
    intro z hz
    have h1 := hf z hz
    unfold subMean
    rw [abs_of_nonneg (sq_nonneg _)]
    have h2 : |f z - ⨍ z' in U, f z'| ≤ 2 * B := by
      rw [abs_le] at h1 hc ⊢
      constructor <;> linarith
    calc (f z - ⨍ z' in U, f z') ^ 2 = |f z - ⨍ z' in U, f z'| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h2 := abs_setAverage_le hU (sq_nonneg (2 * B)) hg
  unfold avgL2
  calc Real.sqrt (⨍ z in U, subMean f U z ^ 2) ≤ Real.sqrt ((2 * B) ^ 2) :=
        Real.sqrt_le_sqrt (le_of_abs_le h2)
    _ = 2 * B := Real.sqrt_sq (by linarith)

/-! ### The Gaussian factor at shifted points and times -/

/-- `Φ_C(s, ρ) ≤ 8 C e^{36/(10C)} t^{-1} exp(-d²/(10 C t))` for `s ∈ [t/8, 2t]`, `d ≤ t` and
`ρ ≥ d - 3√t`. -/
theorem dgPhi_shift_le {CB t s ρ d : ℝ} (hCB : 0 < CB) (ht : 0 < t) (hs1 : t / 8 ≤ s)
    (hs2 : s ≤ 2 * t) (hρ0 : 0 ≤ ρ) (hd0 : 0 ≤ d) (hdt : d ≤ t)
    (hρ : d - 3 * Real.sqrt t ≤ ρ) :
    dgPhi CB s ρ ≤
      8 * CB * Real.exp (36 / (10 * CB)) * t⁻¹ * Real.exp (-(d ^ 2 / (10 * CB * t))) := by
  have ht8 : 0 < t / 8 := by positivity
  have hs : 0 < s := ht8.trans_le hs1
  rw [dgPhi_eq]
  have hinv : s⁻¹ ≤ 8 * t⁻¹ := by
    have h := inv_anti₀ ht8 hs1
    rwa [inv_div, div_eq_mul_inv] at h
  have hexp : Real.exp (-(dgShape s ρ / CB)) ≤
      Real.exp (36 / (10 * CB)) * Real.exp (-(d ^ 2 / (10 * CB * t))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hsq := Real.sq_sqrt ht.le
    have hsqrt0 := Real.sqrt_nonneg t
    have h2 : 0 ≤ dgShape s ρ / CB := div_nonneg (dgShape_nonneg hs hρ0) hCB.le
    by_cases hd6 : d ≤ 6 * Real.sqrt t
    · have hd2 : d ^ 2 ≤ 36 * t := by nlinarith
      have h1 : d ^ 2 / (10 * CB * t) ≤ 36 / (10 * CB) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · push Not at hd6
      have hρd : d / 2 ≤ ρ := by linarith
      have hmin := min_le_dgShape hs hρ0
      have hA : d ^ 2 / (8 * t) ≤ ρ ^ 2 / s := by
        rw [div_le_div_iff₀ (by positivity) hs]
        have hρ2 : d ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
        nlinarith [sq_nonneg d]
      have hB : d ^ 2 / (8 * t) ≤ ρ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hg : d ^ 2 / (8 * t) ≤ dgShape s ρ := (le_min hA hB).trans hmin
      have h3 : d ^ 2 / (10 * CB * t) ≤ dgShape s ρ / CB := by
        have h4 : d ^ 2 / (10 * CB * t) ≤ d ^ 2 / (8 * t) / CB := by
          rw [div_div]
          exact div_le_div_of_nonneg_left (sq_nonneg d) (by positivity) (by nlinarith)
        exact h4.trans (div_le_div_of_nonneg_right hg hCB.le)
      have h4 : 0 ≤ 36 / (10 * CB) := by positivity
      linarith
  calc CB * s⁻¹ * Real.exp (-(dgShape s ρ / CB))
      ≤ CB * (8 * t⁻¹) * (Real.exp (36 / (10 * CB)) * Real.exp (-(d ^ 2 / (10 * CB * t)))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hinv hCB.le) hexp (Real.exp_pos _).le
          (by positivity)
    _ = 8 * CB * Real.exp (36 / (10 * CB)) * t⁻¹ * Real.exp (-(d ^ 2 / (10 * CB * t))) := by
        ring

theorem rpow_neg_three_halves_eq {t : ℝ} (ht : 0 < t) :
    t ^ (-(3 / 2 : ℝ)) = (Real.sqrt t)⁻¹ * t⁻¹ := by
  rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + -1 by norm_num, Real.rpow_add ht, Real.rpow_neg ht.le,
    Real.rpow_neg ht.le, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-! ### The heat kernel as a caloric function -/

theorem isClusterCaloric_openHeat (ω : Configuration 2) (V : Finset (Vertex 2)) (a b T : ℝ)
    (x : Vertex 2) :
    IsClusterCaloric ω V a b (fun τ z => openHeat ω (T + τ) z x) := by
  refine ⟨fun z _ => ?_, fun z _ _ s _ => ?_⟩
  · exact ((continuous_openHeat ω z x).comp (continuous_const.add continuous_id)).continuousOn
  · exact (hasDerivAt_openHeat ω (T + s) z x).comp_const_add T s

/-! ### Theorem 3 -/

/-- **The bound on the cylinder.** With `T - R² = t/8`, `T ≤ 2t`, `R ≤ √t`, `√t ≥ 16`, the poles near
`y` past their minimal times and the anchors near `y` within `R`, the coarsened heat kernel
`[p(T + ·, ·, x)]_𝒫` is at most `A t^{-1} exp(-|x - y|²/(10 C t))` on `(-R², 0] × B_R(y)`. -/
theorem abs_coarsenPar_openHeat_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) {TB : Vertex 2 → Configuration 2 → ℝ} {CB : ℝ}
    (hCB : 0 < CB)
    (hBω : ∀ w : Vertex 2, w ∈ (uniqueInfiniteComponent h).supp → ∀ s : ℝ, 0 < s →
      TB w ω ≤ s → ∀ x ∈ (uniqueInfiniteComponent h).supp,
        openHeat ω s x w ≤ dgPhi CB s (latticeDist x w))
    {y : Vertex 2}
    (hSb : BddAbove (Set.range fun w => if latticeDist w y ≤ TB w ω + 1 then TB w ω else 0))
    (hAb : BddAbove (Set.range fun w =>
      if latticeDist w y ≤ anchorDist w ω + 1 then anchorDist w ω else 0))
    {x : Vertex 2} (hx : x ∈ (uniqueInfiniteComponent h).supp) {t R T : ℝ} (ht0 : 0 < t)
    (hS : latticeSup TB y ω ≤ t / 32) (hA : latticeSup anchorDist y ω ≤ R)
    (hRt : R ≤ Real.sqrt t) (h16 : 16 ≤ Real.sqrt t) (hTR : T - R ^ 2 = t / 8) (hT : T ≤ 2 * t)
    (hdt : latticeDist x y ≤ t) :
    ∀ z ∈ parabolicCylinderAt y R,
      |coarsenPar ω (uniqueInfiniteComponent h) (fun τ z => openHeat ω (T + τ) z x) z| ≤
        8 * CB * Real.exp (36 / (10 * CB)) * t⁻¹ *
          Real.exp (-(latticeDist x y ^ 2 / (10 * CB * t))) := by
  rintro ⟨τ, ξ⟩ ⟨hτR, hξ⟩
  set K := uniqueInfiniteComponent h with hK
  set x' := latticeRound ξ with hx'
  set w := coarseVertex ω K x' with hw
  have hwK : w ∈ K.supp := coarseVertex_mem hP h x'
  have hτ1 := hτR.1
  have hτ2 := hτR.2
  have hs1 : t / 8 < T + τ := by linarith
  have hs2 : T + τ ≤ 2 * t := by linarith
  have hs0 : 0 < T + τ := by linarith
  have hsqt0 := Real.sqrt_nonneg t
  -- the vertex `x'` is close to `y`
  have hξy : ‖ξ - latticeEuclideanEmbedding y‖ < R := by
    rw [Metric.mem_ball, dist_eq_norm] at hξ
    exact hξ
  have hx'y : latticeDist x' y ≤ R + 1 := by
    have := norm_latticeRound_sub_le ξ
    unfold latticeDist
    calc ‖latticeEuclideanEmbedding x' - latticeEuclideanEmbedding y‖
        = ‖(latticeEuclideanEmbedding x' - ξ) + (ξ - latticeEuclideanEmbedding y)‖ := by
          congr 1
          abel
      _ ≤ ‖latticeEuclideanEmbedding x' - ξ‖ + ‖ξ - latticeEuclideanEmbedding y‖ :=
          norm_add_le _ _
      _ ≤ R + 1 := by linarith
  have hAx' : anchorDist x' ω ≤ R := le_of_latticeSup_le hAb hA hx'y
  have hwx' : latticeDist w x' ≤ R := (latticeDist_coarseVertex_le hP K x').trans hAx'
  have hwy : latticeDist w y ≤ 2 * R + 1 := by
    have h1 := latticeDist_triangle w x' y
    have h2 := latticeDist_comm x' w
    linarith
  -- Barlow's bound at the pole `w`
  have h2R : 2 * R ≤ t / 8 := by
    have h1 := mul_le_mul_of_nonneg_left h16 hsqt0
    have h2 := Real.mul_self_sqrt ht0.le
    linarith
  have hTw : TB w ω ≤ T + τ :=
    le_of_latticeSup_le hSb (by linarith) (by linarith)
  have hval : coarsenPar ω K (fun τ z => openHeat ω (T + τ) z x) (τ, ξ) =
      openHeat ω (T + τ) x w := by
    simp only [coarsenPar]
    rw [openHeat_symm]
  have hnn : 0 ≤ openHeat ω (T + τ) x w := openHeat_nonneg ω hs0.le x w
  rw [hval, abs_of_nonneg hnn]
  refine (hBω w hwK (T + τ) hs0 hTw x hx).trans ?_
  have hρ : latticeDist x y - 3 * Real.sqrt t ≤ latticeDist x w := by
    have h1 : latticeDist x y ≤ latticeDist w y + latticeDist w x := latticeDist_triangle x w y
    have h2 := latticeDist_comm w x
    linarith
  exact dgPhi_shift_le hCB ht0 hs1.le hs2 (latticeDist_nonneg _ _) (latticeDist_nonneg _ _) hdt hρ

/-- The final arithmetic: `(C_L/R) · 2 A t^{-1} e ≤ C t^{-3/2} e'` for `R ≥ √t/2`. -/
theorem final_gradient_arith {CL A CB Cf t R d G : ℝ} (hCL : 0 < CL) (hA0 : 0 < A)
    (hCB : 0 < CB) (ht0 : 0 < t) (hRt' : Real.sqrt t / 2 ≤ R) (hCfA : 4 * CL * A ≤ Cf)
    (hCfB : 10 * CB ≤ Cf) (hG0 : 0 ≤ G)
    (hG : G ≤ 2 * (A * t⁻¹ * Real.exp (-(d ^ 2 / (10 * CB * t))))) :
    CL / R * G ≤ Cf * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(d ^ 2 / (Cf * t))) := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hRpos : 0 < R := by linarith
  have hCLR : CL / R ≤ 2 * CL * (Real.sqrt t)⁻¹ := by
    rw [div_le_iff₀ hRpos]
    have h1 : 2 * CL * (Real.sqrt t)⁻¹ * (Real.sqrt t / 2) ≤ 2 * CL * (Real.sqrt t)⁻¹ * R :=
      mul_le_mul_of_nonneg_left hRt' (by positivity)
    have e : 2 * CL * (Real.sqrt t)⁻¹ * (Real.sqrt t / 2) = CL := by field_simp
    linarith
  have hexpC : Real.exp (-(d ^ 2 / (10 * CB * t))) ≤ Real.exp (-(d ^ 2 / (Cf * t))) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg d) (by positivity)
      (mul_le_mul_of_nonneg_right hCfB ht0.le)
  have hCf0 : 0 ≤ Cf := le_trans (by positivity) hCfA
  calc CL / R * G ≤ 2 * CL * (Real.sqrt t)⁻¹ * (2 * (A * t⁻¹ *
        Real.exp (-(d ^ 2 / (10 * CB * t))))) :=
        mul_le_mul hCLR hG hG0 (by positivity)
    _ = 4 * CL * A * ((Real.sqrt t)⁻¹ * t⁻¹) * Real.exp (-(d ^ 2 / (10 * CB * t))) := by ring
    _ ≤ Cf * ((Real.sqrt t)⁻¹ * t⁻¹) * Real.exp (-(d ^ 2 / (Cf * t))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hCfA (by positivity)) hexpC
          (Real.exp_pos _).le (by positivity)
    _ = Cf * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(d ^ 2 / (Cf * t))) := by
        rw [rpow_neg_three_halves_eq ht0]

/-- The radius and the times of the cylinder: for `r ≥ 16`, `t ≥ 4r²`, `T = t + r²/2` and
`R = (7t/8 + r²/2)^{1/2}`. -/
theorem cylinder_numbers {r t : ℝ} (hr : 16 ≤ r) (ht : 4 * r ^ 2 ≤ t) :
    0 < t ∧ 16 ≤ Real.sqrt t ∧ 2 * r ≤ Real.sqrt (7 * t / 8 + r ^ 2 / 2) ∧
      Real.sqrt (7 * t / 8 + r ^ 2 / 2) ≤ Real.sqrt t ∧
      Real.sqrt t / 2 ≤ Real.sqrt (7 * t / 8 + r ^ 2 / 2) ∧
      t + r ^ 2 / 2 - Real.sqrt (7 * t / 8 + r ^ 2 / 2) ^ 2 = t / 8 ∧
      t + r ^ 2 / 2 ≤ 2 * t := by
  have hr2 : (16 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num) hr 2
  have hr0 : 0 < r ^ 2 := by positivity
  have ht0 : 0 < t := by linarith
  have hX : 0 ≤ 7 * t / 8 + r ^ 2 / 2 := by positivity
  have hR2 := Real.sq_sqrt hX
  have hR0 := Real.sqrt_nonneg (7 * t / 8 + r ^ 2 / 2)
  have hsq := Real.sq_sqrt ht0.le
  have hst0 := Real.sqrt_nonneg t
  refine ⟨ht0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (16 : ℝ) = Real.sqrt (16 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [show 2 * r = Real.sqrt ((2 * r) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · exact Real.sqrt_le_sqrt (by linarith)
  · refine (pow_le_pow_iff_left₀ (by positivity) hR0 two_ne_zero).1 ?_
    rw [div_pow, hsq, hR2]
    norm_num
    linarith
  · rw [hR2]
    ring
  · linarith

/-- **Dario–Gu, Theorem 3** in the form of Remark 1.3, in dimension two, from Proposition 3.9
(`DarioGuLipschitzTwo`) and Theorem 4 (Barlow's Gaussian upper bound). -/
theorem darioGuGradientBoundTwo_of_lipschitz (hL : DarioGuLipschitzTwo)
    (hBar : BarlowGaussianUpperBoundTwo) : DarioGuGradientBoundTwo := by
  intro p hpc hp1
  obtain ⟨sL, CL, hsL, hCL, hL'⟩ := hL p hpc hp1
  choose ML hMLm hML0 hMLos hMLae using hL'
  obtain ⟨sB, CB, hsB, hCB, hB'⟩ := hBar p hpc hp1
  choose TB hTBm hTB0 hTBos hTBae using hB'
  -- the minimal times
  have gL : GoodTimes p ML := goodTimes_of_isOsBond hsL hCL hMLm hML0 hMLos
  have gB : GoodTimes p TB := goodTimes_of_isOsBond hsB hCB hTBm hTB0 hTBos
  obtain ⟨gS, hSbdd⟩ := goodTimes_latticeSup gB
  obtain ⟨gAS, hASbdd⟩ := goodTimes_latticeSup (goodTimes_anchorDist (p := p) hpc)
  have gM := (gL.max ((gS.const_mul (by norm_num : (0 : ℝ) < 8)).rpow
    (by norm_num : (0 : ℝ) < 1 / 2))).max (gAS.max_const (by norm_num : (0 : ℝ) ≤ 16))
  obtain ⟨hMm, hM0, CM, sM, hCM, hsM, hMt⟩ := gM
  -- the constants
  set A : ℝ := 8 * CB * Real.exp (36 / (10 * CB)) with hA
  have hA0 : 0 < A := by positivity
  set Cf : ℝ := max CM (max (4 * CL * A) (10 * CB)) with hCf
  have hCfM : CM ≤ Cf := le_max_left _ _
  have hCfA : 4 * CL * A ≤ Cf := (le_max_left _ _).trans (le_max_right _ _)
  have hCfB : 10 * CB ≤ Cf := (le_max_right _ _).trans (le_max_right _ _)
  have hCf0 : 0 < Cf := lt_of_lt_of_le (by linarith) hCfM
  refine ⟨sM, Cf, hsM, hCf0, fun y => ⟨_, hMm y, hM0 y, (hMt y).mono (by linarith) hCfM, ?_⟩⟩
  have hBall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ w : Vertex 2, ∀ h : HasUniqueInfiniteOpenComponent ω,
      w ∈ (uniqueInfiniteComponent h).supp → ∀ t : ℝ, 0 < t → TB w ω ≤ t →
        ∀ x ∈ (uniqueInfiniteComponent h).supp,
          openHeat ω t x w ≤ dgPhi CB t (latticeDist x w) :=
    ae_all_iff.2 hTBae
  filter_upwards [hMLae y, hBall, hSbdd y, hASbdd y, ae_planarPartitionEvent hpc]
    with ω hLω hBω hSb hAb hP
  intro h r hr x hx t ht hdt
  -- the minimal scale
  have hr1 : ML y ω ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hr2 : (8 * latticeSup TB y ω) ^ (1 / 2 : ℝ) ≤ r :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hr)
  have hr3 : latticeSup anchorDist y ω ≤ r :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have hr4 : (16 : ℝ) ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  have hS0 : 0 ≤ latticeSup TB y ω := latticeSup_nonneg hTB0 y ω
  have hT8 : 8 * latticeSup TB y ω ≤ r ^ 2 := by
    have h8 : 0 ≤ 8 * latticeSup TB y ω := by positivity
    have := Real.rpow_le_rpow (by positivity) hr2 (by norm_num : (0 : ℝ) ≤ 2)
    rwa [← Real.rpow_mul h8, show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one,
      Real.rpow_two] at this
  obtain ⟨ht0, h16, h2rR, hRt, hRt', hTR, hT2⟩ := cylinder_numbers hr4 ht
  -- Proposition 3.9 at time `t`
  have hτ : -r ^ 2 / 2 ∈ Set.Ioc (-r ^ 2) 0 := by
    have : 0 < r ^ 2 := by positivity
    constructor <;> linarith
  have hmain := hLω h r _ hr1 h2rR _
    (isClusterCaloric_openHeat ω _ _ _ (t + r ^ 2 / 2) x) (-r ^ 2 / 2) hτ
  have hut : (fun z => openHeat ω (t + r ^ 2 / 2 + -r ^ 2 / 2) z x) =
      fun z => openHeat ω t x z := by
    funext z
    rw [show t + r ^ 2 / 2 + -r ^ 2 / 2 = t by ring, openHeat_symm]
  rw [hut] at hmain
  refine hmain.trans (final_gradient_arith hCL hA0 hCB ht0 hRt' hCfA hCfB (Real.sqrt_nonneg _) ?_)
  refine avgL2_subMean_le (volume_parabolicCylinderAt_lt_top y _) (by positivity) ?_
  have hrt : r ^ 2 ≤ t / 4 := by linarith
  exact abs_coarsenPar_openHeat_le hP h hCB (hBω · h) hSb hAb hx ht0 (by linarith)
    (hr3.trans (by linarith)) hRt h16 hTR hT2 hdt

end Rigidity.Green

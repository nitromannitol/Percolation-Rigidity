import Rigidity.Proofs.Cluster.PlanarScaleStatements
import Rigidity.Proofs.Cluster.PlanarRHProb
import Rigidity.Proofs.Cluster.PlanarReachBounds
import Rigidity.Proofs.S2.ScaleInputsFaithful

/-!
# The minimal scales of Proposition 2.4 of Armstrong and Dario in dimension two

Proposition 2.4 of Armstrong and Dario (`exists_minimalScale_general`) applies to every local
family of good cubes with stretched-exponential failure probabilities ((2.1) and (2.2)). In
dimension two it applies to the reverse Hölder cubes `planarRHGood A₀` of Definition 3.7
(`planarRHFailureBound_holds`) and to the coarsely good cubes `planarCoarseGood`, whose partition
dominates the reach of the planar partition (`planarReach_le_stoppingSize`), which in turn dominates
the sides of the planar partition cubes (`three_pow_scale_le_planarReach`). The maximum of the two
minimal scales is a minimal scale `M ≤ O_r(θ)` for all the bounds of `PlanarMinimalScales`
(`planarMinimalScales_holds`, from `p > p_c(2)` alone).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

theorem mem_cube_zero_iff {d m : ℕ} {x : Vertex d} :
    x ∈ cube m (0 : Vertex d) ↔ x ∈ (originCube d m).vertices := by
  rw [← mem_triadicCube_idx_iff, idx_zero_vertex]
  rfl

theorem cube_zero_eq_vertices {d : ℕ} (m : ℕ) :
    cube m (0 : Vertex d) = (originCube d m).toIntegerCube.vertices :=
  Finset.ext fun x => by rw [TriadicCube.mem_toIntegerCube_vertices, mem_cube_zero_iff]

/-- The exponential moment of a scale with values in `[0, ∞]` is the bound `O_s` of its real
part. -/
theorem isOsBond_toReal_of_exp_moment {p : unitInterval} {M : Configuration 2 → ℝ≥0∞} {s θ : ℝ}
    (hθ : 0 < θ)
    (hint : Integrable (fun ω => Real.exp (((M ω).toReal / θ) ^ s)) (latticeBondLaw 2 p))
    (hle : (∫ ω, Real.exp (((M ω).toReal / θ) ^ s) ∂(latticeBondLaw 2 p)) ≤ 2) :
    IsOsBond 2 p (fun ω => (M ω).toReal) s θ := by
  have e : ∀ ω, Real.exp (Real.rpow (max ((M ω).toReal / θ) 0) s) =
      Real.exp (((M ω).toReal / θ) ^ s) := fun ω => by
    rw [max_eq_left (div_nonneg ENNReal.toReal_nonneg hθ.le)]
    rfl
  unfold IsOsBond
  simp only [e]
  exact ⟨hint, hle⟩

/-- **Proposition 2.4 of Armstrong and Dario for a local family, with a real minimal scale**
(dimension two): for every `τ ∈ ℕ` and `α > 0` there are `K`, `r, θ > 0` and `M ≤ O_r(θ)` such that
almost surely, whenever `M ≤ 3ᵐ`, `∑_{x ∈ □_m} size(x)^τ ≤ K |□_m|` and `size(x) ≤ 3^{α m}` on
`□_m`. -/
theorem exists_planar_minimalScale (p : unitInterval) (G : Configuration 2 → Set (TriadicCube 2))
    (hGm : ∀ T : TriadicCube 2, MeasurableSet {ω | T ∈ G ω})
    (hloc : ∀ T : TriadicCube 2,
      MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {C1 c s0 : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c) (hs0 : 0 < s0) (hs1 : s0 ≤ 1)
    (hq : ∀ T : TriadicCube 2, latticeBondLaw 2 p {ω | T ∉ G ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)))
    (τ : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ K r θ : ℝ, 0 ≤ K ∧ 0 < r ∧ 0 < θ ∧
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ m : ℕ, M ω ≤ 3 ^ m →
          ∑ x ∈ cube m (0 : Vertex 2), TriadicCube.stoppingSize (G ω) x ^ τ ≤
              K * (cube m (0 : Vertex 2)).card ∧
            ∀ x ∈ cube m (0 : Vertex 2), TriadicCube.stoppingSize (G ω) x ≤ ((3 : ℝ) ^ m) ^ α := by
  obtain ⟨C, r, hr, M₀, hM₀m, hfin, ⟨θ, hθ, hint, hle⟩, hprop⟩ :=
    exists_minimalScale_general (d := 2) (by norm_num) p G hGm hloc hC1 hc hs0 hs1 hq τ hα
  have hos := isOsBond_toReal_of_exp_moment (p := p) hθ hint hle
  refine ⟨max C 0, r, 3 * θ, le_max_right _ _, hr, by positivity,
    fun ω => 3 * (M₀ ω).toReal, (hM₀m.ennreal_toReal).const_mul 3,
    fun ω => by positivity, Rigidity.Proofs.S2.IsOsBond.const_mul (by norm_num) hos, ?_⟩
  filter_upwards [hfin, hprop] with ω hω hpr m hm
  have hlt : M₀ ω < 3 ^ m := by
    have h1 : (M₀ ω).toReal < (3 : ℝ) ^ m := by
      have := ENNReal.toReal_nonneg (a := M₀ ω)
      have h3 : (0 : ℝ) < 3 ^ m := by positivity
      linarith
    rw [← ENNReal.ofReal_toReal hω, show (3 : ℝ≥0∞) ^ m = ENNReal.ofReal ((3 : ℝ) ^ m) by
      rw [ENNReal.ofReal_pow (by norm_num)]; norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 h1
  obtain ⟨hsum, hsize⟩ := hpr m hlt
  refine ⟨?_, fun x hx => hsize x (mem_cube_zero_iff.1 hx)⟩
  rw [cube_zero_eq_vertices]
  refine hsum.trans ?_
  have hcard : (((originCube 2 m).toIntegerCube.vertices.card : ℕ) : ℝ) = (3 : ℝ) ^ (2 * m) := by
    rw [← cube_zero_eq_vertices, card_cube, ← pow_mul, mul_comm]
  rw [hcard]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Armstrong and Dario, Definition 3.7 with Propositions 2.1 and 2.4, in the form `O_s`**
(dimension two, from `p > p_c(2)` alone). -/
theorem planarMinimalScales_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarMinimalScales p := by
  obtain ⟨A₀, C1, c, s0, hC1, hc, hs0, hs1, hfail⟩ := planarRHFailureBound_holds hpc
  set μ := latticeBondLaw 2 p with hμ
  set G : Configuration 2 → Set (TriadicCube 2) := planarRHGood A₀ with hG
  have hGm : ∀ T : TriadicCube 2, MeasurableSet {ω | T ∈ G ω} := measurableSet_mem_planarRHGood A₀
  have hloc := measurableSet_not_mem_planarRHGood_local A₀
  obtain ⟨hae, -, -⟩ := partition_estimates_general (d := 2) (by norm_num) μ G hGm
    hC1 hc hs0 hfail
  obtain ⟨C₀, hC₀, c₀, hc₀, hq₀⟩ := exists_measure_not_mem_planarCoarseGood_le hpc
  have hH : ∀ᵐ ω ∂μ, ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω) :=
    TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched μ
      planarCoarseGood (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top 1 c₀ one_pos hc₀ fun R => by
        rw [← ENNReal.ofReal_mul hC₀]
        exact hq₀ R
  refine ⟨A₀, fun ω => stoppingScale (G ω), ?_, fun t ht α hα => ?_⟩
  · filter_upwards [hae] with ω hu
    exact ⟨fun x z hz => stoppingScale_eq_of_mem_cube hu hz,
      fun x y hxy => stoppingScale_le_of_supDist hu hxy,
      fun k y hk => mem_of_stoppingScale_le hu hk⟩
  set τ : ℕ := ⌈t⌉₊ with hτ
  have htτ : t ≤ τ := Nat.le_ceil t
  obtain ⟨K₁, r₁, θ₁, hK₁, hr₁, hθ₁, M₁, hM₁m, hM₁0, hM₁os, hM₁⟩ :=
    exists_planar_minimalScale p G hGm hloc hC1 hc hs0 hs1 hfail τ hα
  obtain ⟨K₂, r₂, θ₂, hK₂, hr₂, hθ₂, M₂, hM₂m, hM₂0, hM₂os, hM₂⟩ :=
    exists_planar_minimalScale p planarCoarseGood measurableSet_mem_planarCoarseGood
      measurableSet_not_mem_planarCoarseGood_localEdge hC₀ hc₀ one_pos le_rfl hq₀ τ hα
  set r : ℝ := min r₁ r₂ with hr
  have hr0 : 0 < r := lt_min hr₁ hr₂
  have h1 := Rigidity.Proofs.S2.IsOsBond.mono_exponent hr0 (min_le_left _ _) hM₁m hM₁os
  have h2 := Rigidity.Proofs.S2.IsOsBond.mono_exponent hr0 (min_le_right _ _) hM₂m hM₂os
  have h12 := Rigidity.Proofs.S2.IsOsBond.max hr0 (by positivity) (by positivity) hM₁m hM₂m h1 h2
  refine ⟨max K₁ K₂, r, _, le_max_of_le_left hK₁, hr0, by positivity,
    fun ω => max (M₁ ω) (M₂ ω), hM₁m.max hM₂m, fun ω => le_max_of_le_left (hM₁0 ω), h12, ?_⟩
  filter_upwards [hae, hH, hM₁, hM₂, ae_planarPartitionEvent hpc] with ω hu hH' hb₁ hb₂ hP m hm
  obtain ⟨hs₁, hz₁⟩ := hb₁ m ((le_max_left _ _).trans hm)
  obtain ⟨hs₂, hz₂⟩ := hb₂ m ((le_max_right _ _).trans hm)
  have hK : ∀ S : ℝ, S ≤ K₁ * (cube m (0 : Vertex 2)).card ∨ S ≤ K₂ * (cube m (0 : Vertex 2)).card →
      S ≤ max K₁ K₂ * (cube m (0 : Vertex 2)).card := by
    rintro S (h | h)
    · exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
    · exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))
  -- the sizes of the planar partition cubes and the reach are at most the coarse sizes
  set S₂ : Vertex 2 → ℝ := fun x => TriadicCube.stoppingSize (planarCoarseGood ω) x with hS₂
  have hS₂0 : ∀ x, 0 ≤ S₂ x := fun x => TriadicCube.stoppingSize_nonneg _ x
  have hreach : ∀ x, planarReach ω x ≤ ENNReal.ofReal (S₂ x) := planarReach_le_stoppingSize hH'
  have hpart : ∀ x, (3 : ℝ) ^ (planarPartCube ω x).scale ≤ S₂ x := by
    intro x
    have hx : x ∈ (planarPartCube ω x).ninefold.vertices :=
      TriadicCube.subset_ninefold_of_mem_planarSquares
        (planarPartCube ω x).toIntegerCube_mem_planarSquares
        (((planarPartCube ω x).mem_toIntegerCube_vertices x).2 (planarPartCube_spec hP x).1)
    have h := (three_pow_scale_le_planarReach hP hx).trans (hreach x)
    rw [← ENNReal.ofReal_toReal (a := (3 : ℝ≥0∞) ^ (planarPartCube ω x).scale)
      (ENNReal.pow_ne_top (by norm_num))] at h
    rw [ENNReal.ofReal_le_ofReal_iff (hS₂0 x)] at h
    simpa using h
  have hpow : ∀ {a : ℕ} {b : ℝ}, (3 : ℝ) ^ a ≤ b → ((3 : ℝ) ^ a) ^ t ≤ b ^ τ := by
    intro a b hab
    calc ((3 : ℝ) ^ a) ^ t ≤ ((3 : ℝ) ^ a) ^ (τ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) htτ
      _ = ((3 : ℝ) ^ a) ^ τ := Real.rpow_natCast _ τ
      _ ≤ b ^ τ := pow_le_pow_left₀ (by positivity) hab τ
  refine ⟨hK _ (Or.inl ((Finset.sum_le_sum fun x _ => hpow
      (stoppingSize_eq_stoppingScale hu x).ge).trans hs₁)),
    fun x hx => (stoppingSize_eq_stoppingScale hu x).symm.le.trans (hz₁ x hx),
    hK _ (Or.inr ((Finset.sum_le_sum fun x _ => hpow (hpart x)).trans hs₂)),
    fun x hx => (hpart x).trans (hz₂ x hx), ?_, fun x hx => (hreach x).trans
      (ENNReal.ofReal_le_ofReal (hz₂ x hx))⟩
  calc ∑ x ∈ cube m (0 : Vertex 2), planarReach ω x ^ ⌈t⌉₊
      ≤ ∑ x ∈ cube m (0 : Vertex 2), ENNReal.ofReal (S₂ x ^ τ) :=
        Finset.sum_le_sum fun x _ => by
          rw [ENNReal.ofReal_pow (hS₂0 x)]
          exact pow_le_pow_left₀ zero_le (hreach x) τ
    _ = ENNReal.ofReal (∑ x ∈ cube m (0 : Vertex 2), S₂ x ^ τ) :=
        (ENNReal.ofReal_sum_of_nonneg fun x _ => pow_nonneg (hS₂0 x) τ).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hK _ (Or.inr hs₂))

end Rigidity.Proofs.Cluster
